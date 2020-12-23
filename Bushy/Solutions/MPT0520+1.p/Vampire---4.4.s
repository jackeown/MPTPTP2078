%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : relat_1__t120_relat_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:48 EDT 2019

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   20 (  28 expanded)
%              Number of leaves         :    4 (   6 expanded)
%              Depth                    :    8
%              Number of atoms          :   34 (  58 expanded)
%              Number of equality atoms :   17 (  25 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f49,plain,(
    $false ),
    inference(subsumption_resolution,[],[f44,f22])).

fof(f22,plain,(
    k2_relat_1(k8_relat_1(sK0,sK1)) != sK0 ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,X1)) != X0
      & r1_tarski(X0,k2_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,X1)) != X0
      & r1_tarski(X0,k2_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r1_tarski(X0,k2_relat_1(X1))
         => k2_relat_1(k8_relat_1(X0,X1)) = X0 ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k2_relat_1(k8_relat_1(X0,X1)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t120_relat_1.p',t120_relat_1)).

fof(f44,plain,(
    k2_relat_1(k8_relat_1(sK0,sK1)) = sK0 ),
    inference(superposition,[],[f36,f31])).

fof(f31,plain,(
    k3_xboole_0(sK0,k2_relat_1(sK1)) = sK0 ),
    inference(resolution,[],[f28,f21])).

fof(f21,plain,(
    r1_tarski(sK0,k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t120_relat_1.p',t28_xboole_1)).

fof(f36,plain,(
    ! [X1] : k2_relat_1(k8_relat_1(X1,sK1)) = k3_xboole_0(X1,k2_relat_1(sK1)) ),
    inference(superposition,[],[f33,f25])).

fof(f25,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t120_relat_1.p',commutativity_k3_xboole_0)).

fof(f33,plain,(
    ! [X0] : k2_relat_1(k8_relat_1(X0,sK1)) = k3_xboole_0(k2_relat_1(sK1),X0) ),
    inference(resolution,[],[f27,f20])).

fof(f20,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t120_relat_1.p',t119_relat_1)).
%------------------------------------------------------------------------------
