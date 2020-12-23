%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : relat_1__t33_relat_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:01 EDT 2019

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 147 expanded)
%              Number of leaves         :    8 (  37 expanded)
%              Depth                    :   14
%              Number of atoms          :   92 ( 262 expanded)
%              Number of equality atoms :   51 ( 131 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6296,plain,(
    $false ),
    inference(subsumption_resolution,[],[f6273,f22])).

fof(f22,plain,(
    k2_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1)) != k3_relat_1(k2_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_xboole_0(k3_relat_1(X0),k3_relat_1(X1)) != k3_relat_1(k2_xboole_0(X0,X1))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => k2_xboole_0(k3_relat_1(X0),k3_relat_1(X1)) = k3_relat_1(k2_xboole_0(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_xboole_0(k3_relat_1(X0),k3_relat_1(X1)) = k3_relat_1(k2_xboole_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t33_relat_1.p',t33_relat_1)).

fof(f6273,plain,(
    k2_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1)) = k3_relat_1(k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f6163,f942])).

fof(f942,plain,(
    ! [X78] : k2_xboole_0(X78,k3_relat_1(sK1)) = k2_xboole_0(k1_relat_1(sK1),k2_xboole_0(X78,k2_relat_1(sK1))) ),
    inference(superposition,[],[f66,f400])).

fof(f400,plain,(
    k2_xboole_0(k2_relat_1(sK1),k1_relat_1(sK1)) = k3_relat_1(sK1) ),
    inference(forward_demodulation,[],[f388,f134])).

fof(f134,plain,(
    k2_xboole_0(k3_relat_1(sK1),k1_relat_1(sK1)) = k3_relat_1(sK1) ),
    inference(superposition,[],[f122,f28])).

fof(f28,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t33_relat_1.p',commutativity_k2_xboole_0)).

fof(f122,plain,(
    k2_xboole_0(k1_relat_1(sK1),k3_relat_1(sK1)) = k3_relat_1(sK1) ),
    inference(forward_demodulation,[],[f117,f27])).

fof(f27,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/relat_1__t33_relat_1.p',idempotence_k2_xboole_0)).

fof(f117,plain,(
    k2_xboole_0(k3_relat_1(sK1),k3_relat_1(sK1)) = k2_xboole_0(k1_relat_1(sK1),k3_relat_1(sK1)) ),
    inference(superposition,[],[f94,f98])).

fof(f98,plain,(
    k2_xboole_0(k3_relat_1(sK1),k2_relat_1(sK1)) = k3_relat_1(sK1) ),
    inference(forward_demodulation,[],[f93,f35])).

fof(f35,plain,(
    k2_xboole_0(k1_relat_1(sK1),k2_relat_1(sK1)) = k3_relat_1(sK1) ),
    inference(resolution,[],[f24,f21])).

fof(f21,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f24,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t33_relat_1.p',d6_relat_1)).

fof(f93,plain,(
    k2_xboole_0(k3_relat_1(sK1),k2_relat_1(sK1)) = k2_xboole_0(k1_relat_1(sK1),k2_relat_1(sK1)) ),
    inference(superposition,[],[f62,f27])).

fof(f62,plain,(
    ! [X8] : k2_xboole_0(k3_relat_1(sK1),X8) = k2_xboole_0(k1_relat_1(sK1),k2_xboole_0(k2_relat_1(sK1),X8)) ),
    inference(superposition,[],[f30,f35])).

fof(f30,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t33_relat_1.p',t4_xboole_1)).

fof(f94,plain,(
    ! [X0] : k2_xboole_0(k3_relat_1(sK1),X0) = k2_xboole_0(k1_relat_1(sK1),k2_xboole_0(X0,k2_relat_1(sK1))) ),
    inference(superposition,[],[f62,f28])).

fof(f388,plain,(
    k2_xboole_0(k3_relat_1(sK1),k1_relat_1(sK1)) = k2_xboole_0(k2_relat_1(sK1),k1_relat_1(sK1)) ),
    inference(superposition,[],[f343,f27])).

fof(f343,plain,(
    ! [X42] : k2_xboole_0(k3_relat_1(sK1),X42) = k2_xboole_0(k2_relat_1(sK1),k2_xboole_0(k1_relat_1(sK1),X42)) ),
    inference(superposition,[],[f60,f35])).

fof(f60,plain,(
    ! [X4,X2,X3] : k2_xboole_0(X2,k2_xboole_0(X3,X4)) = k2_xboole_0(k2_xboole_0(X3,X2),X4) ),
    inference(superposition,[],[f30,f28])).

fof(f66,plain,(
    ! [X6,X7,X5] : k2_xboole_0(X5,k2_xboole_0(X6,X7)) = k2_xboole_0(X7,k2_xboole_0(X5,X6)) ),
    inference(superposition,[],[f30,f28])).

fof(f6163,plain,(
    k2_xboole_0(k1_relat_1(sK1),k2_xboole_0(k3_relat_1(sK0),k2_relat_1(sK1))) = k3_relat_1(k2_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f6112,f5246])).

fof(f5246,plain,(
    k2_xboole_0(k1_relat_1(k2_xboole_0(sK0,sK1)),k2_relat_1(k2_xboole_0(sK0,sK1))) = k3_relat_1(k2_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f2272,f23])).

fof(f23,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f2272,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k2_xboole_0(k1_relat_1(k2_xboole_0(X0,sK1)),k2_relat_1(k2_xboole_0(X0,sK1))) = k3_relat_1(k2_xboole_0(X0,sK1)) ) ),
    inference(resolution,[],[f37,f21])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k2_xboole_0(k1_relat_1(k2_xboole_0(X0,X1)),k2_relat_1(k2_xboole_0(X0,X1))) = k3_relat_1(k2_xboole_0(X0,X1)) ) ),
    inference(resolution,[],[f24,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_xboole_0(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_xboole_0(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_xboole_0(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k2_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t33_relat_1.p',fc3_relat_1)).

fof(f6112,plain,(
    k2_xboole_0(k1_relat_1(sK1),k2_xboole_0(k3_relat_1(sK0),k2_relat_1(sK1))) = k2_xboole_0(k1_relat_1(k2_xboole_0(sK0,sK1)),k2_relat_1(k2_xboole_0(sK0,sK1))) ),
    inference(superposition,[],[f149,f193])).

fof(f193,plain,(
    k2_xboole_0(k3_relat_1(sK0),k2_relat_1(sK1)) = k2_xboole_0(k1_relat_1(sK0),k2_relat_1(k2_xboole_0(sK0,sK1))) ),
    inference(superposition,[],[f63,f186])).

fof(f186,plain,(
    k2_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)) = k2_relat_1(k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f185,f28])).

fof(f185,plain,(
    k2_xboole_0(k2_relat_1(sK1),k2_relat_1(sK0)) = k2_relat_1(k2_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f182,f28])).

fof(f182,plain,(
    k2_xboole_0(k2_relat_1(sK1),k2_relat_1(sK0)) = k2_relat_1(k2_xboole_0(sK1,sK0)) ),
    inference(resolution,[],[f172,f23])).

fof(f172,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k2_xboole_0(k2_relat_1(sK1),k2_relat_1(X0)) = k2_relat_1(k2_xboole_0(sK1,X0)) ) ),
    inference(resolution,[],[f26,f21])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) = k2_relat_1(k2_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) = k2_relat_1(k2_xboole_0(X0,X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) = k2_relat_1(k2_xboole_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t33_relat_1.p',t26_relat_1)).

fof(f63,plain,(
    ! [X9] : k2_xboole_0(k3_relat_1(sK0),X9) = k2_xboole_0(k1_relat_1(sK0),k2_xboole_0(k2_relat_1(sK0),X9)) ),
    inference(superposition,[],[f30,f36])).

fof(f36,plain,(
    k2_xboole_0(k1_relat_1(sK0),k2_relat_1(sK0)) = k3_relat_1(sK0) ),
    inference(resolution,[],[f24,f23])).

fof(f149,plain,(
    ! [X0] : k2_xboole_0(k1_relat_1(k2_xboole_0(sK0,sK1)),X0) = k2_xboole_0(k1_relat_1(sK1),k2_xboole_0(k1_relat_1(sK0),X0)) ),
    inference(superposition,[],[f30,f146])).

fof(f146,plain,(
    k2_xboole_0(k1_relat_1(sK1),k1_relat_1(sK0)) = k1_relat_1(k2_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f143,f28])).

fof(f143,plain,(
    k2_xboole_0(k1_relat_1(sK1),k1_relat_1(sK0)) = k1_relat_1(k2_xboole_0(sK1,sK0)) ),
    inference(resolution,[],[f125,f23])).

fof(f125,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k2_xboole_0(k1_relat_1(sK1),k1_relat_1(X0)) = k1_relat_1(k2_xboole_0(sK1,X0)) ) ),
    inference(resolution,[],[f25,f21])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t33_relat_1.p',t13_relat_1)).
%------------------------------------------------------------------------------
