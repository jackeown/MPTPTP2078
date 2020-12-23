%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:39 EST 2020

% Result     : Theorem 1.54s
% Output     : Refutation 1.69s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 126 expanded)
%              Number of leaves         :   16 (  33 expanded)
%              Depth                    :   13
%              Number of atoms          :  187 ( 425 expanded)
%              Number of equality atoms :   46 (  98 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f597,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f39,f457,f98])).

fof(f98,plain,(
    ! [X2] :
      ( ~ r1_tarski(X2,k10_relat_1(sK1,k9_relat_1(sK1,X2)))
      | k10_relat_1(sK1,k9_relat_1(sK1,X2)) = X2 ) ),
    inference(resolution,[],[f86,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f86,plain,(
    ! [X0] : r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0) ),
    inference(subsumption_resolution,[],[f85,f35])).

fof(f35,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( sK0 != k10_relat_1(sK1,k9_relat_1(sK1,sK0))
    & v2_funct_1(sK1)
    & r1_tarski(sK0,k1_relat_1(sK1))
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f31])).

fof(f31,plain,
    ( ? [X0,X1] :
        ( k10_relat_1(X1,k9_relat_1(X1,X0)) != X0
        & v2_funct_1(X1)
        & r1_tarski(X0,k1_relat_1(X1))
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( sK0 != k10_relat_1(sK1,k9_relat_1(sK1,sK0))
      & v2_funct_1(sK1)
      & r1_tarski(sK0,k1_relat_1(sK1))
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) != X0
      & v2_funct_1(X1)
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) != X0
      & v2_funct_1(X1)
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( ( v2_funct_1(X1)
            & r1_tarski(X0,k1_relat_1(X1)) )
         => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( v2_funct_1(X1)
          & r1_tarski(X0,k1_relat_1(X1)) )
       => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_1)).

fof(f85,plain,(
    ! [X0] :
      ( r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0)
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f84,f36])).

fof(f36,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f84,plain,(
    ! [X0] :
      ( r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0)
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f55,f38])).

fof(f38,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X1)
      | r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_funct_1)).

fof(f457,plain,(
    r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(superposition,[],[f181,f362])).

fof(f362,plain,(
    sK0 = k3_xboole_0(sK0,k1_relat_1(sK1)) ),
    inference(forward_demodulation,[],[f346,f40])).

fof(f40,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f346,plain,(
    k4_xboole_0(sK0,k1_xboole_0) = k3_xboole_0(sK0,k1_relat_1(sK1)) ),
    inference(superposition,[],[f52,f247])).

fof(f247,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k1_relat_1(sK1)) ),
    inference(resolution,[],[f94,f46])).

fof(f46,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

fof(f94,plain,(
    ! [X4,X3] : r1_xboole_0(k4_xboole_0(sK0,X3),k4_xboole_0(X4,k1_relat_1(sK1))) ),
    inference(resolution,[],[f91,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).

fof(f91,plain,(
    ! [X0] : r1_tarski(k4_xboole_0(sK0,X0),k1_relat_1(sK1)) ),
    inference(resolution,[],[f78,f49])).

fof(f49,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f78,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK0)
      | r1_tarski(X0,k1_relat_1(sK1)) ) ),
    inference(resolution,[],[f60,f37])).

fof(f37,plain,(
    r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f32])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f52,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f181,plain,(
    ! [X0] : r1_tarski(k3_xboole_0(X0,k1_relat_1(sK1)),k10_relat_1(sK1,k9_relat_1(sK1,X0))) ),
    inference(forward_demodulation,[],[f172,f69])).

fof(f69,plain,(
    sK1 = k5_relat_1(k6_relat_1(k1_relat_1(sK1)),sK1) ),
    inference(resolution,[],[f47,f35])).

fof(f47,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_relat_1)).

fof(f172,plain,(
    ! [X0] : r1_tarski(k3_xboole_0(X0,k1_relat_1(sK1)),k10_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(sK1)),sK1),k9_relat_1(sK1,X0))) ),
    inference(resolution,[],[f145,f62])).

fof(f62,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f145,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X1,k1_relat_1(sK1))
      | r1_tarski(k3_xboole_0(X2,X1),k10_relat_1(k5_relat_1(k6_relat_1(X1),sK1),k9_relat_1(sK1,X2))) ) ),
    inference(backward_demodulation,[],[f105,f143])).

fof(f143,plain,(
    ! [X2,X1] : k10_relat_1(k6_relat_1(X1),X2) = k3_xboole_0(X2,X1) ),
    inference(forward_demodulation,[],[f142,f43])).

fof(f43,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f142,plain,(
    ! [X2,X1] : k10_relat_1(k6_relat_1(X1),X2) = k1_relat_1(k6_relat_1(k3_xboole_0(X2,X1))) ),
    inference(forward_demodulation,[],[f141,f53])).

fof(f53,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

fof(f141,plain,(
    ! [X2,X1] : k10_relat_1(k6_relat_1(X1),X2) = k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) ),
    inference(resolution,[],[f83,f41])).

fof(f41,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f83,plain,(
    ! [X2,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k5_relat_1(X1,k6_relat_1(X2))) = k10_relat_1(X1,X2) ) ),
    inference(forward_demodulation,[],[f82,f43])).

fof(f82,plain,(
    ! [X2,X1] :
      ( k1_relat_1(k5_relat_1(X1,k6_relat_1(X2))) = k10_relat_1(X1,k1_relat_1(k6_relat_1(X2)))
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f48,f41])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

fof(f105,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X1,k1_relat_1(sK1))
      | r1_tarski(k10_relat_1(k6_relat_1(X1),X2),k10_relat_1(k5_relat_1(k6_relat_1(X1),sK1),k9_relat_1(sK1,X2))) ) ),
    inference(forward_demodulation,[],[f104,f44])).

fof(f44,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f104,plain,(
    ! [X2,X1] :
      ( r1_tarski(k10_relat_1(k6_relat_1(X1),X2),k10_relat_1(k5_relat_1(k6_relat_1(X1),sK1),k9_relat_1(sK1,X2)))
      | ~ r1_tarski(k2_relat_1(k6_relat_1(X1)),k1_relat_1(sK1)) ) ),
    inference(resolution,[],[f87,f41])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | r1_tarski(k10_relat_1(X0,X1),k10_relat_1(k5_relat_1(X0,sK1),k9_relat_1(sK1,X1)))
      | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(sK1)) ) ),
    inference(resolution,[],[f54,f35])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X2))
      | r1_tarski(k10_relat_1(X1,X0),k10_relat_1(k5_relat_1(X1,X2),k9_relat_1(X2,X0)))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k10_relat_1(X1,X0),k10_relat_1(k5_relat_1(X1,X2),k9_relat_1(X2,X0)))
          | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X2))
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k10_relat_1(X1,X0),k10_relat_1(k5_relat_1(X1,X2),k9_relat_1(X2,X0)))
          | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X2))
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(k2_relat_1(X1),k1_relat_1(X2))
           => r1_tarski(k10_relat_1(X1,X0),k10_relat_1(k5_relat_1(X1,X2),k9_relat_1(X2,X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_funct_1)).

fof(f39,plain,(
    sK0 != k10_relat_1(sK1,k9_relat_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_vampire %s %d
% 0.11/0.31  % Computer   : n012.cluster.edu
% 0.11/0.31  % Model      : x86_64 x86_64
% 0.11/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.31  % Memory     : 8042.1875MB
% 0.11/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.31  % CPULimit   : 60
% 0.11/0.31  % WCLimit    : 600
% 0.11/0.31  % DateTime   : Tue Dec  1 20:40:07 EST 2020
% 0.11/0.31  % CPUTime    : 
% 0.16/0.45  % (16215)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.16/0.46  % (16231)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.16/0.47  % (16216)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.16/0.47  % (16210)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.16/0.47  % (16223)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.16/0.47  % (16221)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.16/0.47  % (16207)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.16/0.47  % (16208)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.16/0.47  % (16206)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.16/0.48  % (16204)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.16/0.48  % (16214)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.16/0.48  % (16217)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.16/0.48  % (16212)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.16/0.49  % (16229)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.16/0.49  % (16224)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.16/0.49  % (16202)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.16/0.49  % (16225)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.16/0.49  % (16213)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.16/0.49  % (16228)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.16/0.49  % (16230)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.16/0.49  % (16203)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.16/0.50  % (16220)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.16/0.50  % (16205)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.16/0.50  % (16209)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.16/0.50  % (16226)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.16/0.50  % (16227)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.16/0.50  % (16218)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.16/0.50  % (16219)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.16/0.50  % (16211)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.16/0.51  % (16222)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.54/0.53  % (16209)Refutation found. Thanks to Tanya!
% 1.54/0.53  % SZS status Theorem for theBenchmark
% 1.69/0.55  % SZS output start Proof for theBenchmark
% 1.69/0.55  fof(f597,plain,(
% 1.69/0.55    $false),
% 1.69/0.55    inference(unit_resulting_resolution,[],[f39,f457,f98])).
% 1.69/0.55  fof(f98,plain,(
% 1.69/0.55    ( ! [X2] : (~r1_tarski(X2,k10_relat_1(sK1,k9_relat_1(sK1,X2))) | k10_relat_1(sK1,k9_relat_1(sK1,X2)) = X2) )),
% 1.69/0.55    inference(resolution,[],[f86,f58])).
% 1.69/0.55  fof(f58,plain,(
% 1.69/0.55    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.69/0.55    inference(cnf_transformation,[],[f34])).
% 1.69/0.55  fof(f34,plain,(
% 1.69/0.55    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.69/0.55    inference(flattening,[],[f33])).
% 1.69/0.55  fof(f33,plain,(
% 1.69/0.55    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.69/0.55    inference(nnf_transformation,[],[f1])).
% 1.69/0.55  fof(f1,axiom,(
% 1.69/0.55    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.69/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.69/0.56  fof(f86,plain,(
% 1.69/0.56    ( ! [X0] : (r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0)) )),
% 1.69/0.56    inference(subsumption_resolution,[],[f85,f35])).
% 1.69/0.56  fof(f35,plain,(
% 1.69/0.56    v1_relat_1(sK1)),
% 1.69/0.56    inference(cnf_transformation,[],[f32])).
% 1.69/0.56  fof(f32,plain,(
% 1.69/0.56    sK0 != k10_relat_1(sK1,k9_relat_1(sK1,sK0)) & v2_funct_1(sK1) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 1.69/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f31])).
% 1.69/0.56  fof(f31,plain,(
% 1.69/0.56    ? [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) != X0 & v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1)) => (sK0 != k10_relat_1(sK1,k9_relat_1(sK1,sK0)) & v2_funct_1(sK1) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 1.69/0.56    introduced(choice_axiom,[])).
% 1.69/0.56  fof(f20,plain,(
% 1.69/0.56    ? [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) != X0 & v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.69/0.56    inference(flattening,[],[f19])).
% 1.69/0.56  fof(f19,plain,(
% 1.69/0.56    ? [X0,X1] : ((k10_relat_1(X1,k9_relat_1(X1,X0)) != X0 & (v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1)))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 1.69/0.56    inference(ennf_transformation,[],[f18])).
% 1.69/0.56  fof(f18,negated_conjecture,(
% 1.69/0.56    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 1.69/0.56    inference(negated_conjecture,[],[f17])).
% 1.69/0.56  fof(f17,conjecture,(
% 1.69/0.56    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 1.69/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_1)).
% 1.69/0.56  fof(f85,plain,(
% 1.69/0.56    ( ! [X0] : (r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0) | ~v1_relat_1(sK1)) )),
% 1.69/0.56    inference(subsumption_resolution,[],[f84,f36])).
% 1.69/0.56  fof(f36,plain,(
% 1.69/0.56    v1_funct_1(sK1)),
% 1.69/0.56    inference(cnf_transformation,[],[f32])).
% 1.69/0.56  fof(f84,plain,(
% 1.69/0.56    ( ! [X0] : (r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) )),
% 1.69/0.56    inference(resolution,[],[f55,f38])).
% 1.69/0.56  fof(f38,plain,(
% 1.69/0.56    v2_funct_1(sK1)),
% 1.69/0.56    inference(cnf_transformation,[],[f32])).
% 1.69/0.56  fof(f55,plain,(
% 1.69/0.56    ( ! [X0,X1] : (~v2_funct_1(X1) | r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.69/0.56    inference(cnf_transformation,[],[f27])).
% 1.69/0.56  fof(f27,plain,(
% 1.69/0.56    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.69/0.56    inference(flattening,[],[f26])).
% 1.69/0.56  fof(f26,plain,(
% 1.69/0.56    ! [X0,X1] : ((r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.69/0.56    inference(ennf_transformation,[],[f14])).
% 1.69/0.56  fof(f14,axiom,(
% 1.69/0.56    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)))),
% 1.69/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_funct_1)).
% 1.69/0.56  fof(f457,plain,(
% 1.69/0.56    r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 1.69/0.56    inference(superposition,[],[f181,f362])).
% 1.69/0.56  fof(f362,plain,(
% 1.69/0.56    sK0 = k3_xboole_0(sK0,k1_relat_1(sK1))),
% 1.69/0.56    inference(forward_demodulation,[],[f346,f40])).
% 1.69/0.56  fof(f40,plain,(
% 1.69/0.56    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.69/0.56    inference(cnf_transformation,[],[f4])).
% 1.69/0.56  fof(f4,axiom,(
% 1.69/0.56    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.69/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 1.69/0.56  fof(f346,plain,(
% 1.69/0.56    k4_xboole_0(sK0,k1_xboole_0) = k3_xboole_0(sK0,k1_relat_1(sK1))),
% 1.69/0.56    inference(superposition,[],[f52,f247])).
% 1.69/0.56  fof(f247,plain,(
% 1.69/0.56    k1_xboole_0 = k4_xboole_0(sK0,k1_relat_1(sK1))),
% 1.69/0.56    inference(resolution,[],[f94,f46])).
% 1.69/0.56  fof(f46,plain,(
% 1.69/0.56    ( ! [X0] : (~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) )),
% 1.69/0.56    inference(cnf_transformation,[],[f21])).
% 1.69/0.56  fof(f21,plain,(
% 1.69/0.56    ! [X0] : ((~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) & (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)))),
% 1.69/0.56    inference(ennf_transformation,[],[f6])).
% 1.69/0.56  fof(f6,axiom,(
% 1.69/0.56    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 1.69/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).
% 1.69/0.56  fof(f94,plain,(
% 1.69/0.56    ( ! [X4,X3] : (r1_xboole_0(k4_xboole_0(sK0,X3),k4_xboole_0(X4,k1_relat_1(sK1)))) )),
% 1.69/0.56    inference(resolution,[],[f91,f59])).
% 1.69/0.56  fof(f59,plain,(
% 1.69/0.56    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_xboole_0(X0,k4_xboole_0(X2,X1))) )),
% 1.69/0.56    inference(cnf_transformation,[],[f28])).
% 1.69/0.56  fof(f28,plain,(
% 1.69/0.56    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 1.69/0.56    inference(ennf_transformation,[],[f7])).
% 1.69/0.56  fof(f7,axiom,(
% 1.69/0.56    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 1.69/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).
% 1.69/0.56  fof(f91,plain,(
% 1.69/0.56    ( ! [X0] : (r1_tarski(k4_xboole_0(sK0,X0),k1_relat_1(sK1))) )),
% 1.69/0.56    inference(resolution,[],[f78,f49])).
% 1.69/0.56  fof(f49,plain,(
% 1.69/0.56    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.69/0.56    inference(cnf_transformation,[],[f3])).
% 1.69/0.56  fof(f3,axiom,(
% 1.69/0.56    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.69/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.69/0.56  fof(f78,plain,(
% 1.69/0.56    ( ! [X0] : (~r1_tarski(X0,sK0) | r1_tarski(X0,k1_relat_1(sK1))) )),
% 1.69/0.56    inference(resolution,[],[f60,f37])).
% 1.69/0.56  fof(f37,plain,(
% 1.69/0.56    r1_tarski(sK0,k1_relat_1(sK1))),
% 1.69/0.56    inference(cnf_transformation,[],[f32])).
% 1.69/0.56  fof(f60,plain,(
% 1.69/0.56    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 1.69/0.56    inference(cnf_transformation,[],[f30])).
% 1.69/0.56  fof(f30,plain,(
% 1.69/0.56    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 1.69/0.56    inference(flattening,[],[f29])).
% 1.69/0.56  fof(f29,plain,(
% 1.69/0.56    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.69/0.56    inference(ennf_transformation,[],[f2])).
% 1.69/0.56  fof(f2,axiom,(
% 1.69/0.56    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 1.69/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 1.69/0.56  fof(f52,plain,(
% 1.69/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 1.69/0.56    inference(cnf_transformation,[],[f5])).
% 1.69/0.56  fof(f5,axiom,(
% 1.69/0.56    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 1.69/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.69/0.56  fof(f181,plain,(
% 1.69/0.56    ( ! [X0] : (r1_tarski(k3_xboole_0(X0,k1_relat_1(sK1)),k10_relat_1(sK1,k9_relat_1(sK1,X0)))) )),
% 1.69/0.56    inference(forward_demodulation,[],[f172,f69])).
% 1.69/0.56  fof(f69,plain,(
% 1.69/0.56    sK1 = k5_relat_1(k6_relat_1(k1_relat_1(sK1)),sK1)),
% 1.69/0.56    inference(resolution,[],[f47,f35])).
% 1.69/0.56  fof(f47,plain,(
% 1.69/0.56    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0) )),
% 1.69/0.56    inference(cnf_transformation,[],[f22])).
% 1.69/0.56  fof(f22,plain,(
% 1.69/0.56    ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0))),
% 1.69/0.56    inference(ennf_transformation,[],[f12])).
% 1.69/0.56  fof(f12,axiom,(
% 1.69/0.56    ! [X0] : (v1_relat_1(X0) => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0)),
% 1.69/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_relat_1)).
% 1.69/0.56  fof(f172,plain,(
% 1.69/0.56    ( ! [X0] : (r1_tarski(k3_xboole_0(X0,k1_relat_1(sK1)),k10_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(sK1)),sK1),k9_relat_1(sK1,X0)))) )),
% 1.69/0.56    inference(resolution,[],[f145,f62])).
% 1.69/0.56  fof(f62,plain,(
% 1.69/0.56    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.69/0.56    inference(equality_resolution,[],[f57])).
% 1.69/0.56  fof(f57,plain,(
% 1.69/0.56    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.69/0.56    inference(cnf_transformation,[],[f34])).
% 1.69/0.56  fof(f145,plain,(
% 1.69/0.56    ( ! [X2,X1] : (~r1_tarski(X1,k1_relat_1(sK1)) | r1_tarski(k3_xboole_0(X2,X1),k10_relat_1(k5_relat_1(k6_relat_1(X1),sK1),k9_relat_1(sK1,X2)))) )),
% 1.69/0.56    inference(backward_demodulation,[],[f105,f143])).
% 1.69/0.56  fof(f143,plain,(
% 1.69/0.56    ( ! [X2,X1] : (k10_relat_1(k6_relat_1(X1),X2) = k3_xboole_0(X2,X1)) )),
% 1.69/0.56    inference(forward_demodulation,[],[f142,f43])).
% 1.69/0.56  fof(f43,plain,(
% 1.69/0.56    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.69/0.56    inference(cnf_transformation,[],[f11])).
% 1.69/0.56  fof(f11,axiom,(
% 1.69/0.56    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.69/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 1.69/0.56  fof(f142,plain,(
% 1.69/0.56    ( ! [X2,X1] : (k10_relat_1(k6_relat_1(X1),X2) = k1_relat_1(k6_relat_1(k3_xboole_0(X2,X1)))) )),
% 1.69/0.56    inference(forward_demodulation,[],[f141,f53])).
% 1.69/0.56  fof(f53,plain,(
% 1.69/0.56    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))) )),
% 1.69/0.56    inference(cnf_transformation,[],[f16])).
% 1.69/0.56  fof(f16,axiom,(
% 1.69/0.56    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 1.69/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).
% 1.69/0.56  fof(f141,plain,(
% 1.69/0.56    ( ! [X2,X1] : (k10_relat_1(k6_relat_1(X1),X2) = k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))) )),
% 1.69/0.56    inference(resolution,[],[f83,f41])).
% 1.69/0.56  fof(f41,plain,(
% 1.69/0.56    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.69/0.56    inference(cnf_transformation,[],[f13])).
% 1.69/0.56  fof(f13,axiom,(
% 1.69/0.56    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.69/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 1.69/0.56  fof(f83,plain,(
% 1.69/0.56    ( ! [X2,X1] : (~v1_relat_1(X1) | k1_relat_1(k5_relat_1(X1,k6_relat_1(X2))) = k10_relat_1(X1,X2)) )),
% 1.69/0.56    inference(forward_demodulation,[],[f82,f43])).
% 1.69/0.56  fof(f82,plain,(
% 1.69/0.56    ( ! [X2,X1] : (k1_relat_1(k5_relat_1(X1,k6_relat_1(X2))) = k10_relat_1(X1,k1_relat_1(k6_relat_1(X2))) | ~v1_relat_1(X1)) )),
% 1.69/0.56    inference(resolution,[],[f48,f41])).
% 1.69/0.56  fof(f48,plain,(
% 1.69/0.56    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X0)) )),
% 1.69/0.56    inference(cnf_transformation,[],[f23])).
% 1.69/0.56  fof(f23,plain,(
% 1.69/0.56    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.69/0.56    inference(ennf_transformation,[],[f10])).
% 1.69/0.56  fof(f10,axiom,(
% 1.69/0.56    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 1.69/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).
% 1.69/0.56  fof(f105,plain,(
% 1.69/0.56    ( ! [X2,X1] : (~r1_tarski(X1,k1_relat_1(sK1)) | r1_tarski(k10_relat_1(k6_relat_1(X1),X2),k10_relat_1(k5_relat_1(k6_relat_1(X1),sK1),k9_relat_1(sK1,X2)))) )),
% 1.69/0.56    inference(forward_demodulation,[],[f104,f44])).
% 1.69/0.56  fof(f44,plain,(
% 1.69/0.56    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 1.69/0.56    inference(cnf_transformation,[],[f11])).
% 1.69/0.56  fof(f104,plain,(
% 1.69/0.56    ( ! [X2,X1] : (r1_tarski(k10_relat_1(k6_relat_1(X1),X2),k10_relat_1(k5_relat_1(k6_relat_1(X1),sK1),k9_relat_1(sK1,X2))) | ~r1_tarski(k2_relat_1(k6_relat_1(X1)),k1_relat_1(sK1))) )),
% 1.69/0.56    inference(resolution,[],[f87,f41])).
% 1.69/0.56  fof(f87,plain,(
% 1.69/0.56    ( ! [X0,X1] : (~v1_relat_1(X0) | r1_tarski(k10_relat_1(X0,X1),k10_relat_1(k5_relat_1(X0,sK1),k9_relat_1(sK1,X1))) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(sK1))) )),
% 1.69/0.56    inference(resolution,[],[f54,f35])).
% 1.69/0.56  fof(f54,plain,(
% 1.69/0.56    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_tarski(k2_relat_1(X1),k1_relat_1(X2)) | r1_tarski(k10_relat_1(X1,X0),k10_relat_1(k5_relat_1(X1,X2),k9_relat_1(X2,X0))) | ~v1_relat_1(X1)) )),
% 1.69/0.56    inference(cnf_transformation,[],[f25])).
% 1.69/0.56  fof(f25,plain,(
% 1.69/0.56    ! [X0,X1] : (! [X2] : (r1_tarski(k10_relat_1(X1,X0),k10_relat_1(k5_relat_1(X1,X2),k9_relat_1(X2,X0))) | ~r1_tarski(k2_relat_1(X1),k1_relat_1(X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 1.69/0.56    inference(flattening,[],[f24])).
% 1.69/0.56  fof(f24,plain,(
% 1.69/0.56    ! [X0,X1] : (! [X2] : ((r1_tarski(k10_relat_1(X1,X0),k10_relat_1(k5_relat_1(X1,X2),k9_relat_1(X2,X0))) | ~r1_tarski(k2_relat_1(X1),k1_relat_1(X2))) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 1.69/0.56    inference(ennf_transformation,[],[f15])).
% 1.69/0.56  fof(f15,axiom,(
% 1.69/0.56    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(k2_relat_1(X1),k1_relat_1(X2)) => r1_tarski(k10_relat_1(X1,X0),k10_relat_1(k5_relat_1(X1,X2),k9_relat_1(X2,X0))))))),
% 1.69/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_funct_1)).
% 1.69/0.56  fof(f39,plain,(
% 1.69/0.56    sK0 != k10_relat_1(sK1,k9_relat_1(sK1,sK0))),
% 1.69/0.56    inference(cnf_transformation,[],[f32])).
% 1.69/0.56  % SZS output end Proof for theBenchmark
% 1.69/0.56  % (16209)------------------------------
% 1.69/0.56  % (16209)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.69/0.56  % (16209)Termination reason: Refutation
% 1.69/0.56  
% 1.69/0.56  % (16209)Memory used [KB]: 2430
% 1.69/0.56  % (16209)Time elapsed: 0.168 s
% 1.69/0.56  % (16209)------------------------------
% 1.69/0.56  % (16209)------------------------------
% 1.69/0.56  % (16201)Success in time 0.232 s
%------------------------------------------------------------------------------
