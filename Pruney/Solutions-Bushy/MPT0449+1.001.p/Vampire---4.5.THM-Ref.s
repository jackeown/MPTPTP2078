%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0449+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:00 EST 2020

% Result     : Theorem 2.21s
% Output     : Refutation 2.21s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 141 expanded)
%              Number of leaves         :    7 (  37 expanded)
%              Depth                    :   13
%              Number of atoms          :   88 ( 247 expanded)
%              Number of equality atoms :   47 ( 126 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5355,plain,(
    $false ),
    inference(subsumption_resolution,[],[f5345,f16])).

fof(f16,plain,(
    k3_relat_1(k2_xboole_0(sK0,sK1)) != k2_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k3_relat_1(k2_xboole_0(X0,X1)) != k2_xboole_0(k3_relat_1(X0),k3_relat_1(X1))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => k3_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k3_relat_1(X0),k3_relat_1(X1)) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k3_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k3_relat_1(X0),k3_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_relat_1)).

fof(f5345,plain,(
    k3_relat_1(k2_xboole_0(sK0,sK1)) = k2_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(superposition,[],[f1808,f4256])).

fof(f4256,plain,(
    k3_relat_1(k2_xboole_0(sK0,sK1)) = k2_xboole_0(k1_relat_1(k2_xboole_0(sK0,sK1)),k2_relat_1(k2_xboole_0(sK0,sK1))) ),
    inference(resolution,[],[f2414,f17])).

fof(f17,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f2414,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k3_relat_1(k2_xboole_0(X0,sK1)) = k2_xboole_0(k1_relat_1(k2_xboole_0(X0,sK1)),k2_relat_1(k2_xboole_0(X0,sK1))) ) ),
    inference(resolution,[],[f28,f15])).

fof(f15,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k3_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(k2_xboole_0(X0,X1)),k2_relat_1(k2_xboole_0(X0,X1))) ) ),
    inference(resolution,[],[f18,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_xboole_0(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_xboole_0(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_xboole_0(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k2_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_relat_1)).

fof(f18,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

fof(f1808,plain,(
    k2_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1)) = k2_xboole_0(k1_relat_1(k2_xboole_0(sK0,sK1)),k2_relat_1(k2_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f1807,f26])).

fof(f26,plain,(
    k3_relat_1(sK1) = k2_xboole_0(k1_relat_1(sK1),k2_relat_1(sK1)) ),
    inference(resolution,[],[f18,f15])).

fof(f1807,plain,(
    k2_xboole_0(k3_relat_1(sK0),k2_xboole_0(k1_relat_1(sK1),k2_relat_1(sK1))) = k2_xboole_0(k1_relat_1(k2_xboole_0(sK0,sK1)),k2_relat_1(k2_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f1806,f1255])).

fof(f1255,plain,(
    ! [X6,X7] : k2_xboole_0(k3_relat_1(sK0),k2_xboole_0(X6,X7)) = k2_xboole_0(k3_relat_1(sK0),k2_xboole_0(X7,X6)) ),
    inference(superposition,[],[f840,f21])).

fof(f21,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f840,plain,(
    ! [X6,X5] : k2_xboole_0(k2_xboole_0(X5,X6),k3_relat_1(sK0)) = k2_xboole_0(k3_relat_1(sK0),k2_xboole_0(X6,X5)) ),
    inference(forward_demodulation,[],[f817,f382])).

fof(f382,plain,(
    ! [X2,X3] : k2_xboole_0(k3_relat_1(sK0),k2_xboole_0(X2,X3)) = k2_xboole_0(k2_relat_1(sK0),k2_xboole_0(X3,k2_xboole_0(X2,k1_relat_1(sK0)))) ),
    inference(superposition,[],[f348,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X1,X0),X2) ),
    inference(superposition,[],[f23,f21])).

fof(f23,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f348,plain,(
    ! [X2] : k2_xboole_0(k3_relat_1(sK0),X2) = k2_xboole_0(k2_relat_1(sK0),k2_xboole_0(X2,k1_relat_1(sK0))) ),
    inference(superposition,[],[f267,f21])).

fof(f267,plain,(
    ! [X17] : k2_xboole_0(k2_relat_1(sK0),k2_xboole_0(k1_relat_1(sK0),X17)) = k2_xboole_0(k3_relat_1(sK0),X17) ),
    inference(superposition,[],[f44,f27])).

fof(f27,plain,(
    k3_relat_1(sK0) = k2_xboole_0(k1_relat_1(sK0),k2_relat_1(sK0)) ),
    inference(resolution,[],[f18,f17])).

fof(f817,plain,(
    ! [X6,X5] : k2_xboole_0(k2_xboole_0(X5,X6),k3_relat_1(sK0)) = k2_xboole_0(k2_relat_1(sK0),k2_xboole_0(X5,k2_xboole_0(X6,k1_relat_1(sK0)))) ),
    inference(superposition,[],[f653,f49])).

fof(f49,plain,(
    ! [X4,X5,X3] : k2_xboole_0(X3,k2_xboole_0(X4,X5)) = k2_xboole_0(X5,k2_xboole_0(X3,X4)) ),
    inference(superposition,[],[f23,f21])).

fof(f653,plain,(
    ! [X0] : k2_xboole_0(k2_relat_1(sK0),k2_xboole_0(k1_relat_1(sK0),X0)) = k2_xboole_0(X0,k3_relat_1(sK0)) ),
    inference(superposition,[],[f433,f21])).

fof(f433,plain,(
    ! [X25] : k2_xboole_0(k2_relat_1(sK0),k2_xboole_0(X25,k1_relat_1(sK0))) = k2_xboole_0(X25,k3_relat_1(sK0)) ),
    inference(superposition,[],[f49,f27])).

fof(f1806,plain,(
    k2_xboole_0(k3_relat_1(sK0),k2_xboole_0(k2_relat_1(sK1),k1_relat_1(sK1))) = k2_xboole_0(k1_relat_1(k2_xboole_0(sK0,sK1)),k2_relat_1(k2_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f1767,f49])).

fof(f1767,plain,(
    k2_xboole_0(k1_relat_1(sK1),k2_xboole_0(k3_relat_1(sK0),k2_relat_1(sK1))) = k2_xboole_0(k1_relat_1(k2_xboole_0(sK0,sK1)),k2_relat_1(k2_xboole_0(sK0,sK1))) ),
    inference(superposition,[],[f213,f162])).

fof(f162,plain,(
    k2_xboole_0(k3_relat_1(sK0),k2_relat_1(sK1)) = k2_xboole_0(k1_relat_1(sK0),k2_relat_1(k2_xboole_0(sK0,sK1))) ),
    inference(superposition,[],[f75,f147])).

fof(f147,plain,(
    k2_xboole_0(k2_relat_1(sK1),k2_relat_1(sK0)) = k2_relat_1(k2_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f145,f21])).

fof(f145,plain,(
    k2_relat_1(k2_xboole_0(sK1,sK0)) = k2_xboole_0(k2_relat_1(sK1),k2_relat_1(sK0)) ),
    inference(resolution,[],[f136,f17])).

fof(f136,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k2_relat_1(k2_xboole_0(sK1,X0)) = k2_xboole_0(k2_relat_1(sK1),k2_relat_1(X0)) ) ),
    inference(resolution,[],[f19,f15])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | k2_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_relat_1)).

fof(f75,plain,(
    ! [X0] : k2_xboole_0(k3_relat_1(sK0),X0) = k2_xboole_0(k1_relat_1(sK0),k2_xboole_0(X0,k2_relat_1(sK0))) ),
    inference(superposition,[],[f47,f21])).

fof(f47,plain,(
    ! [X7] : k2_xboole_0(k1_relat_1(sK0),k2_xboole_0(k2_relat_1(sK0),X7)) = k2_xboole_0(k3_relat_1(sK0),X7) ),
    inference(superposition,[],[f23,f27])).

fof(f213,plain,(
    ! [X0] : k2_xboole_0(k1_relat_1(sK1),k2_xboole_0(k1_relat_1(sK0),X0)) = k2_xboole_0(k1_relat_1(k2_xboole_0(sK0,sK1)),X0) ),
    inference(superposition,[],[f23,f207])).

fof(f207,plain,(
    k2_xboole_0(k1_relat_1(sK1),k1_relat_1(sK0)) = k1_relat_1(k2_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f205,f21])).

fof(f205,plain,(
    k1_relat_1(k2_xboole_0(sK1,sK0)) = k2_xboole_0(k1_relat_1(sK1),k1_relat_1(sK0)) ),
    inference(resolution,[],[f180,f17])).

fof(f180,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(k2_xboole_0(sK1,X0)) = k2_xboole_0(k1_relat_1(sK1),k1_relat_1(X0)) ) ),
    inference(resolution,[],[f20,f15])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_relat_1)).

%------------------------------------------------------------------------------
