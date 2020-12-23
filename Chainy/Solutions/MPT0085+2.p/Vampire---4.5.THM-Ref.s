%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0085+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:08 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   28 (  35 expanded)
%              Number of leaves         :    8 (  11 expanded)
%              Depth                    :    8
%              Number of atoms          :   52 (  66 expanded)
%              Number of equality atoms :   30 (  36 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f489,plain,(
    $false ),
    inference(subsumption_resolution,[],[f488,f255])).

fof(f255,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f53])).

fof(f53,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f488,plain,(
    k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,sK2)) != k2_xboole_0(k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,sK2)),k1_xboole_0) ),
    inference(backward_demodulation,[],[f327,f471])).

fof(f471,plain,(
    ! [X8] : k3_xboole_0(sK0,k2_xboole_0(sK1,X8)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X8)) ),
    inference(superposition,[],[f199,f277])).

fof(f277,plain,(
    k1_xboole_0 = k3_xboole_0(sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f187,f227])).

fof(f227,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f180])).

fof(f180,plain,(
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

fof(f187,plain,(
    r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f177])).

fof(f177,plain,
    ( k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k3_xboole_0(sK0,sK2)
    & r1_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f131,f176])).

fof(f176,plain,
    ( ? [X0,X1,X2] :
        ( k3_xboole_0(X0,k2_xboole_0(X1,X2)) != k3_xboole_0(X0,X2)
        & r1_xboole_0(X0,X1) )
   => ( k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k3_xboole_0(sK0,sK2)
      & r1_xboole_0(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f131,plain,(
    ? [X0,X1,X2] :
      ( k3_xboole_0(X0,k2_xboole_0(X1,X2)) != k3_xboole_0(X0,X2)
      & r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f123])).

fof(f123,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_xboole_0(X0,X1)
       => k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2) ) ),
    inference(negated_conjecture,[],[f122])).

fof(f122,conjecture,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_xboole_1)).

fof(f199,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_xboole_1)).

fof(f327,plain,(
    k2_xboole_0(k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k1_xboole_0) != k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,sK2)) ),
    inference(forward_demodulation,[],[f322,f212])).

fof(f212,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f322,plain,(
    k2_xboole_0(k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k1_xboole_0) != k2_xboole_0(k3_xboole_0(sK0,sK2),k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f232,f232,f188,f218])).

fof(f218,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) != k2_xboole_0(X2,X1)
      | ~ r1_xboole_0(X2,X1)
      | ~ r1_xboole_0(X0,X1)
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f149])).

fof(f149,plain,(
    ! [X0,X1,X2] :
      ( X0 = X2
      | ~ r1_xboole_0(X2,X1)
      | ~ r1_xboole_0(X0,X1)
      | k2_xboole_0(X0,X1) != k2_xboole_0(X2,X1) ) ),
    inference(flattening,[],[f148])).

fof(f148,plain,(
    ! [X0,X1,X2] :
      ( X0 = X2
      | ~ r1_xboole_0(X2,X1)
      | ~ r1_xboole_0(X0,X1)
      | k2_xboole_0(X0,X1) != k2_xboole_0(X2,X1) ) ),
    inference(ennf_transformation,[],[f115])).

fof(f115,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X2,X1)
        & r1_xboole_0(X0,X1)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) )
     => X0 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_xboole_1)).

fof(f188,plain,(
    k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k3_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f177])).

fof(f232,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f107])).

fof(f107,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
%------------------------------------------------------------------------------
