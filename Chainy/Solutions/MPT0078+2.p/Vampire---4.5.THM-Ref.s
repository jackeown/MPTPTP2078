%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0078+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:07 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   34 (  87 expanded)
%              Number of leaves         :    7 (  24 expanded)
%              Depth                    :   12
%              Number of atoms          :   61 ( 239 expanded)
%              Number of equality atoms :   40 ( 134 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f619,plain,(
    $false ),
    inference(subsumption_resolution,[],[f618,f256])).

fof(f256,plain,(
    sK0 != sK2 ),
    inference(cnf_transformation,[],[f199])).

fof(f199,plain,
    ( sK0 != sK2
    & r1_xboole_0(sK2,sK1)
    & r1_xboole_0(sK0,sK1)
    & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f127,f198])).

fof(f198,plain,
    ( ? [X0,X1,X2] :
        ( X0 != X2
        & r1_xboole_0(X2,X1)
        & r1_xboole_0(X0,X1)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) )
   => ( sK0 != sK2
      & r1_xboole_0(sK2,sK1)
      & r1_xboole_0(sK0,sK1)
      & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f127,plain,(
    ? [X0,X1,X2] :
      ( X0 != X2
      & r1_xboole_0(X2,X1)
      & r1_xboole_0(X0,X1)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) ) ),
    inference(flattening,[],[f126])).

fof(f126,plain,(
    ? [X0,X1,X2] :
      ( X0 != X2
      & r1_xboole_0(X2,X1)
      & r1_xboole_0(X0,X1)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) ) ),
    inference(ennf_transformation,[],[f116])).

fof(f116,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_xboole_0(X2,X1)
          & r1_xboole_0(X0,X1)
          & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) )
       => X0 = X2 ) ),
    inference(negated_conjecture,[],[f115])).

fof(f115,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X2,X1)
        & r1_xboole_0(X0,X1)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) )
     => X0 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_xboole_1)).

fof(f618,plain,(
    sK0 = sK2 ),
    inference(forward_demodulation,[],[f617,f554])).

fof(f554,plain,(
    sK0 = k2_xboole_0(k1_xboole_0,sK0) ),
    inference(backward_demodulation,[],[f529,f553])).

fof(f553,plain,(
    sK0 = k4_xboole_0(sK0,sK1) ),
    inference(forward_demodulation,[],[f530,f354])).

fof(f354,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f77])).

fof(f77,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f530,plain,(
    k4_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k1_xboole_0) ),
    inference(superposition,[],[f340,f426])).

fof(f426,plain,(
    k1_xboole_0 = k3_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f254,f268])).

fof(f268,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f200])).

fof(f200,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f254,plain,(
    r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f199])).

fof(f340,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f86])).

fof(f86,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f529,plain,(
    sK0 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f336,f426])).

fof(f336,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f92])).

fof(f92,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f617,plain,(
    sK2 = k2_xboole_0(k1_xboole_0,sK0) ),
    inference(forward_demodulation,[],[f590,f557])).

fof(f557,plain,(
    sK0 = k4_xboole_0(sK2,sK1) ),
    inference(backward_demodulation,[],[f492,f553])).

fof(f492,plain,(
    k4_xboole_0(sK2,sK1) = k4_xboole_0(sK0,sK1) ),
    inference(forward_demodulation,[],[f456,f339])).

fof(f339,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f79])).

fof(f79,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f456,plain,(
    k4_xboole_0(sK2,sK1) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK1) ),
    inference(superposition,[],[f339,f253])).

fof(f253,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f199])).

fof(f590,plain,(
    sK2 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK2,sK1)) ),
    inference(superposition,[],[f336,f434])).

fof(f434,plain,(
    k1_xboole_0 = k3_xboole_0(sK2,sK1) ),
    inference(resolution,[],[f255,f268])).

fof(f255,plain,(
    r1_xboole_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f199])).
%------------------------------------------------------------------------------
