%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0778+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:48 EST 2020

% Result     : Theorem 2.04s
% Output     : Refutation 2.04s
% Verified   : 
% Statistics : Number of formulae       :   16 (  31 expanded)
%              Number of leaves         :    4 (   9 expanded)
%              Depth                    :    8
%              Number of atoms          :   26 (  58 expanded)
%              Number of equality atoms :   15 (  31 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2076,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2075,f1764])).

fof(f1764,plain,(
    ! [X0,X1] : k2_wellord1(k2_wellord1(sK2,X0),X1) = k2_wellord1(sK2,k3_xboole_0(X0,X1)) ),
    inference(unit_resulting_resolution,[],[f1436,f1440])).

fof(f1440,plain,(
    ! [X2,X0,X1] :
      ( k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f1173])).

fof(f1173,plain,(
    ! [X0,X1,X2] :
      ( k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f1160])).

fof(f1160,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_wellord1)).

fof(f1436,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f1361])).

fof(f1361,plain,
    ( k2_wellord1(k2_wellord1(sK2,sK0),sK1) != k2_wellord1(k2_wellord1(sK2,sK1),sK0)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f1170,f1360])).

fof(f1360,plain,
    ( ? [X0,X1,X2] :
        ( k2_wellord1(k2_wellord1(X2,X0),X1) != k2_wellord1(k2_wellord1(X2,X1),X0)
        & v1_relat_1(X2) )
   => ( k2_wellord1(k2_wellord1(sK2,sK0),sK1) != k2_wellord1(k2_wellord1(sK2,sK1),sK0)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f1170,plain,(
    ? [X0,X1,X2] :
      ( k2_wellord1(k2_wellord1(X2,X0),X1) != k2_wellord1(k2_wellord1(X2,X1),X0)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f1162])).

fof(f1162,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0) ) ),
    inference(negated_conjecture,[],[f1161])).

fof(f1161,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_wellord1)).

fof(f2075,plain,(
    k2_wellord1(k2_wellord1(sK2,sK0),sK1) != k2_wellord1(sK2,k3_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f2074,f1505])).

fof(f1505,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f2074,plain,(
    k2_wellord1(k2_wellord1(sK2,sK0),sK1) != k2_wellord1(sK2,k3_xboole_0(sK1,sK0)) ),
    inference(backward_demodulation,[],[f1437,f1764])).

fof(f1437,plain,(
    k2_wellord1(k2_wellord1(sK2,sK0),sK1) != k2_wellord1(k2_wellord1(sK2,sK1),sK0) ),
    inference(cnf_transformation,[],[f1361])).
%------------------------------------------------------------------------------
