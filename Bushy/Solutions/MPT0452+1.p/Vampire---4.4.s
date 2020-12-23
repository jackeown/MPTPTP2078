%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : relat_1__t38_relat_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:02 EDT 2019

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   27 (  47 expanded)
%              Number of leaves         :    5 (  11 expanded)
%              Depth                    :    9
%              Number of atoms          :   43 (  82 expanded)
%              Number of equality atoms :   24 (  43 expanded)
%              Maximal formula depth    :    4 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f63,plain,(
    $false ),
    inference(subsumption_resolution,[],[f62,f20])).

fof(f20,plain,(
    k3_relat_1(sK0) != k3_relat_1(k4_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( k3_relat_1(X0) != k3_relat_1(k4_relat_1(X0))
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => k3_relat_1(X0) = k3_relat_1(k4_relat_1(X0)) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k3_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t38_relat_1.p',t38_relat_1)).

fof(f62,plain,(
    k3_relat_1(sK0) = k3_relat_1(k4_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f58,f35])).

fof(f35,plain,(
    k3_relat_1(sK0) = k2_xboole_0(k1_relat_1(sK0),k2_relat_1(sK0)) ),
    inference(resolution,[],[f23,f19])).

fof(f19,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f23,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t38_relat_1.p',d6_relat_1)).

fof(f58,plain,(
    k3_relat_1(k4_relat_1(sK0)) = k2_xboole_0(k1_relat_1(sK0),k2_relat_1(sK0)) ),
    inference(superposition,[],[f57,f27])).

fof(f27,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t38_relat_1.p',commutativity_k2_xboole_0)).

fof(f57,plain,(
    k3_relat_1(k4_relat_1(sK0)) = k2_xboole_0(k2_relat_1(sK0),k1_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f56,f31])).

fof(f31,plain,(
    k1_relat_1(k4_relat_1(sK0)) = k2_relat_1(sK0) ),
    inference(resolution,[],[f24,f19])).

fof(f24,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t38_relat_1.p',t37_relat_1)).

fof(f56,plain,(
    k3_relat_1(k4_relat_1(sK0)) = k2_xboole_0(k1_relat_1(k4_relat_1(sK0)),k1_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f54,f33])).

fof(f33,plain,(
    k1_relat_1(sK0) = k2_relat_1(k4_relat_1(sK0)) ),
    inference(resolution,[],[f25,f19])).

fof(f25,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f54,plain,(
    k3_relat_1(k4_relat_1(sK0)) = k2_xboole_0(k1_relat_1(k4_relat_1(sK0)),k2_relat_1(k4_relat_1(sK0))) ),
    inference(resolution,[],[f36,f19])).

fof(f36,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k3_relat_1(k4_relat_1(X0)) = k2_xboole_0(k1_relat_1(k4_relat_1(X0)),k2_relat_1(k4_relat_1(X0))) ) ),
    inference(resolution,[],[f23,f21])).

fof(f21,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t38_relat_1.p',dt_k4_relat_1)).
%------------------------------------------------------------------------------
