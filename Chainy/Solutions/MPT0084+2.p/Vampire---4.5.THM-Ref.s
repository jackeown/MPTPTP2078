%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0084+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:08 EST 2020

% Result     : Theorem 1.53s
% Output     : Refutation 1.53s
% Verified   : 
% Statistics : Number of formulae       :   35 (  52 expanded)
%              Number of leaves         :    8 (  15 expanded)
%              Depth                    :   11
%              Number of atoms          :   60 ( 106 expanded)
%              Number of equality atoms :    8 (  12 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f849,plain,(
    $false ),
    inference(subsumption_resolution,[],[f848,f812])).

fof(f812,plain,(
    r1_xboole_0(k3_xboole_0(sK0,sK1),sK0) ),
    inference(unit_resulting_resolution,[],[f740,f236])).

fof(f236,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f169])).

fof(f169,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f740,plain,(
    r1_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f733,f205])).

fof(f205,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f733,plain,(
    r1_xboole_0(sK0,k3_xboole_0(sK1,sK0)) ),
    inference(superposition,[],[f690,f429])).

fof(f429,plain,(
    sK0 = k3_xboole_0(sK0,sK2) ),
    inference(unit_resulting_resolution,[],[f186,f202])).

fof(f202,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f140])).

fof(f140,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f63])).

fof(f63,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f186,plain,(
    r1_tarski(sK0,sK2) ),
    inference(cnf_transformation,[],[f175])).

fof(f175,plain,
    ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    & r1_tarski(sK0,sK2)
    & ~ r1_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f130,f174])).

fof(f174,plain,
    ( ? [X0,X1,X2] :
        ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,X2)
        & ~ r1_xboole_0(X0,X1) )
   => ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
      & r1_tarski(sK0,sK2)
      & ~ r1_xboole_0(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f130,plain,(
    ? [X0,X1,X2] :
      ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
      & r1_tarski(X0,X2)
      & ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f122])).

fof(f122,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
          & r1_tarski(X0,X2)
          & ~ r1_xboole_0(X0,X1) ) ),
    inference(negated_conjecture,[],[f121])).

fof(f121,conjecture,(
    ! [X0,X1,X2] :
      ~ ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,X2)
        & ~ r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_xboole_1)).

fof(f690,plain,(
    ! [X0] : r1_xboole_0(sK0,k3_xboole_0(sK1,k3_xboole_0(X0,sK2))) ),
    inference(superposition,[],[f682,f205])).

fof(f682,plain,(
    ! [X0] : r1_xboole_0(sK0,k3_xboole_0(sK1,k3_xboole_0(sK2,X0))) ),
    inference(forward_demodulation,[],[f672,f200])).

fof(f200,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f672,plain,(
    ! [X0] : r1_xboole_0(sK0,k3_xboole_0(k3_xboole_0(sK1,sK2),X0)) ),
    inference(unit_resulting_resolution,[],[f187,f224])).

fof(f224,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X0,k3_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f157])).

fof(f157,plain,(
    ! [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X0,k3_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f118])).

fof(f118,axiom,(
    ! [X0,X1,X2] :
      ~ ( r1_xboole_0(X0,X1)
        & ~ r1_xboole_0(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_xboole_1)).

fof(f187,plain,(
    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f175])).

fof(f848,plain,(
    ~ r1_xboole_0(k3_xboole_0(sK0,sK1),sK0) ),
    inference(forward_demodulation,[],[f832,f205])).

fof(f832,plain,(
    ~ r1_xboole_0(k3_xboole_0(sK1,sK0),sK0) ),
    inference(unit_resulting_resolution,[],[f270,f233])).

fof(f233,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k3_xboole_0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f168])).

fof(f168,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k3_xboole_0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f119])).

fof(f119,axiom,(
    ! [X0,X1] :
      ~ ( r1_xboole_0(k3_xboole_0(X0,X1),X1)
        & ~ r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_xboole_1)).

fof(f270,plain,(
    ~ r1_xboole_0(sK1,sK0) ),
    inference(unit_resulting_resolution,[],[f185,f236])).

fof(f185,plain,(
    ~ r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f175])).
%------------------------------------------------------------------------------
