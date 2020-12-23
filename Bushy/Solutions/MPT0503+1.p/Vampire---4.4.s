%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : relat_1__t101_relat_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:47 EDT 2019

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   15 (  18 expanded)
%              Number of leaves         :    3 (   4 expanded)
%              Depth                    :    7
%              Number of atoms          :   21 (  27 expanded)
%              Number of equality atoms :   13 (  16 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f23,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f22])).

fof(f22,plain,(
    k7_relat_1(sK1,sK0) != k7_relat_1(sK1,sK0) ),
    inference(forward_demodulation,[],[f20,f14])).

fof(f14,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/relat_1__t101_relat_1.p',idempotence_k3_xboole_0)).

fof(f20,plain,(
    k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k3_xboole_0(sK0,sK0)) ),
    inference(superposition,[],[f13,f18])).

fof(f18,plain,(
    ! [X0,X1] : k7_relat_1(k7_relat_1(sK1,X0),X1) = k7_relat_1(sK1,k3_xboole_0(X0,X1)) ),
    inference(resolution,[],[f17,f12])).

fof(f12,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( k7_relat_1(X1,X0) != k7_relat_1(k7_relat_1(X1,X0),X0)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => k7_relat_1(X1,X0) = k7_relat_1(k7_relat_1(X1,X0),X0) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k7_relat_1(k7_relat_1(X1,X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t101_relat_1.p',t101_relat_1)).

fof(f17,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t101_relat_1.p',t100_relat_1)).

fof(f13,plain,(
    k7_relat_1(sK1,sK0) != k7_relat_1(k7_relat_1(sK1,sK0),sK0) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
