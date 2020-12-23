%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:45 EST 2020

% Result     : Theorem 2.69s
% Output     : Refutation 2.69s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 342 expanded)
%              Number of leaves         :   17 (  92 expanded)
%              Depth                    :   19
%              Number of atoms          :  146 ( 756 expanded)
%              Number of equality atoms :   48 ( 140 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2625,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2619,f251])).

fof(f251,plain,(
    ~ r1_tarski(sK0,k1_relat_1(k7_relat_1(sK1,sK0))) ),
    inference(superposition,[],[f147,f83])).

fof(f83,plain,(
    ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k10_relat_1(k7_relat_1(sK1,X0),k9_relat_1(sK1,X0)) ),
    inference(forward_demodulation,[],[f79,f65])).

fof(f65,plain,(
    ! [X0] : k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0) ),
    inference(unit_resulting_resolution,[],[f36,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f36,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
    & r1_tarski(sK0,k1_relat_1(sK1))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f32])).

fof(f32,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
        & r1_tarski(X0,k1_relat_1(X1))
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
      & r1_tarski(sK0,k1_relat_1(sK1))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r1_tarski(X0,k1_relat_1(X1))
         => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

fof(f79,plain,(
    ! [X0] : k10_relat_1(k7_relat_1(sK1,X0),k2_relat_1(k7_relat_1(sK1,X0))) = k1_relat_1(k7_relat_1(sK1,X0)) ),
    inference(unit_resulting_resolution,[],[f66,f41])).

fof(f41,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

fof(f66,plain,(
    ! [X0] : v1_relat_1(k7_relat_1(sK1,X0)) ),
    inference(unit_resulting_resolution,[],[f36,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f147,plain,(
    ! [X0] : ~ r1_tarski(sK0,k10_relat_1(k7_relat_1(sK1,X0),k9_relat_1(sK1,sK0))) ),
    inference(forward_demodulation,[],[f145,f63])).

fof(f63,plain,(
    ! [X0,X1] : k10_relat_1(k7_relat_1(sK1,X0),X1) = k1_setfam_1(k2_tarski(X0,k10_relat_1(sK1,X1))) ),
    inference(unit_resulting_resolution,[],[f36,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k10_relat_1(k7_relat_1(X2,X0),X1) = k1_setfam_1(k2_tarski(X0,k10_relat_1(X2,X1))) ) ),
    inference(definition_unfolding,[],[f53,f44])).

fof(f44,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

fof(f145,plain,(
    ! [X0] : ~ r1_tarski(sK0,k1_setfam_1(k2_tarski(X0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))))) ),
    inference(superposition,[],[f91,f42])).

fof(f42,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f91,plain,(
    ! [X0] : ~ r1_tarski(sK0,k1_setfam_1(k2_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),X0))) ),
    inference(unit_resulting_resolution,[],[f38,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k1_setfam_1(k2_tarski(X1,X2)))
      | r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f54,f44])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_xboole_1)).

fof(f38,plain,(
    ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f33])).

fof(f2619,plain,(
    r1_tarski(sK0,k1_relat_1(k7_relat_1(sK1,sK0))) ),
    inference(superposition,[],[f289,f2382])).

fof(f2382,plain,(
    sK0 = k1_setfam_1(k2_tarski(sK0,k1_relat_1(sK1))) ),
    inference(forward_demodulation,[],[f2381,f40])).

fof(f40,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f2381,plain,(
    k1_setfam_1(k2_tarski(sK0,k1_relat_1(sK1))) = k4_xboole_0(sK0,k1_xboole_0) ),
    inference(superposition,[],[f58,f2085])).

fof(f2085,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k1_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f37,f1556])).

fof(f1556,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(forward_demodulation,[],[f1544,f1439])).

fof(f1439,plain,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(superposition,[],[f1351,f43])).

fof(f43,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f1351,plain,(
    ! [X1] : k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(backward_demodulation,[],[f1321,f1312])).

fof(f1312,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(unit_resulting_resolution,[],[f39,f1261,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f1261,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(k1_xboole_0,X0),X1) ),
    inference(unit_resulting_resolution,[],[f39,f186])).

fof(f186,plain,(
    ! [X6,X8,X7,X5] :
      ( ~ r1_tarski(X5,k2_xboole_0(X6,k10_relat_1(k7_relat_1(sK1,X7),X8)))
      | r1_tarski(k4_xboole_0(X5,X6),X7) ) ),
    inference(resolution,[],[f159,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f159,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,k10_relat_1(k7_relat_1(sK1,X0),X1))
      | r1_tarski(X2,X0) ) ),
    inference(superposition,[],[f60,f63])).

fof(f39,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f1321,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1) = X1 ),
    inference(unit_resulting_resolution,[],[f1261,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f1544,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,k2_xboole_0(X1,k1_xboole_0)) ) ),
    inference(resolution,[],[f1370,f55])).

fof(f1370,plain,(
    ! [X2] :
      ( ~ r1_tarski(X2,k1_xboole_0)
      | k1_xboole_0 = X2 ) ),
    inference(forward_demodulation,[],[f1369,f1312])).

fof(f1369,plain,(
    ! [X2,X3] :
      ( k1_xboole_0 = X2
      | ~ r1_tarski(X2,k4_xboole_0(k1_xboole_0,X3)) ) ),
    inference(forward_demodulation,[],[f1331,f1312])).

fof(f1331,plain,(
    ! [X2,X3] :
      ( k4_xboole_0(k1_xboole_0,X3) = X2
      | ~ r1_tarski(X2,k4_xboole_0(k1_xboole_0,X3)) ) ),
    inference(resolution,[],[f1261,f52])).

fof(f37,plain,(
    r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f33])).

fof(f58,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(definition_unfolding,[],[f45,f44])).

fof(f45,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f289,plain,(
    ! [X3] : r1_tarski(k1_setfam_1(k2_tarski(X3,k1_relat_1(sK1))),k1_relat_1(k7_relat_1(sK1,X3))) ),
    inference(superposition,[],[f85,f156])).

fof(f156,plain,(
    ! [X0] : k10_relat_1(k7_relat_1(sK1,X0),k2_relat_1(sK1)) = k1_setfam_1(k2_tarski(X0,k1_relat_1(sK1))) ),
    inference(superposition,[],[f63,f67])).

fof(f67,plain,(
    k1_relat_1(sK1) = k10_relat_1(sK1,k2_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f36,f41])).

fof(f85,plain,(
    ! [X0,X1] : r1_tarski(k10_relat_1(k7_relat_1(sK1,X0),X1),k1_relat_1(k7_relat_1(sK1,X0))) ),
    inference(forward_demodulation,[],[f84,f83])).

fof(f84,plain,(
    ! [X0,X1] : r1_tarski(k10_relat_1(k7_relat_1(sK1,X0),X1),k10_relat_1(k7_relat_1(sK1,X0),k9_relat_1(sK1,X0))) ),
    inference(forward_demodulation,[],[f76,f65])).

fof(f76,plain,(
    ! [X0,X1] : r1_tarski(k10_relat_1(k7_relat_1(sK1,X0),X1),k10_relat_1(k7_relat_1(sK1,X0),k2_relat_1(k7_relat_1(sK1,X0)))) ),
    inference(unit_resulting_resolution,[],[f66,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1)))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1)))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t170_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:48:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.51  % (32324)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.52  % (32331)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.52  % (32336)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.52  % (32325)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.53  % (32339)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.53  % (32346)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.53  % (32327)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.53  % (32329)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.53  % (32328)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.53  % (32338)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.53  % (32326)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.53  % (32352)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.54  % (32344)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.54  % (32352)Refutation not found, incomplete strategy% (32352)------------------------------
% 0.21/0.54  % (32352)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (32330)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (32353)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.54  % (32350)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (32352)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (32351)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.54  % (32352)Memory used [KB]: 10746
% 0.21/0.54  % (32352)Time elapsed: 0.128 s
% 0.21/0.54  % (32352)------------------------------
% 0.21/0.54  % (32352)------------------------------
% 0.21/0.54  % (32341)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.54  % (32332)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.55  % (32342)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.55  % (32345)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.55  % (32343)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.55  % (32333)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.55  % (32347)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.55  % (32334)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.55  % (32337)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.55  % (32340)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.55  % (32335)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.55  % (32349)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.56  % (32334)Refutation not found, incomplete strategy% (32334)------------------------------
% 0.21/0.56  % (32334)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (32334)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (32334)Memory used [KB]: 10746
% 0.21/0.56  % (32334)Time elapsed: 0.161 s
% 0.21/0.56  % (32334)------------------------------
% 0.21/0.56  % (32334)------------------------------
% 0.21/0.56  % (32340)Refutation not found, incomplete strategy% (32340)------------------------------
% 0.21/0.56  % (32340)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (32340)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (32340)Memory used [KB]: 10618
% 0.21/0.56  % (32340)Time elapsed: 0.155 s
% 0.21/0.56  % (32340)------------------------------
% 0.21/0.56  % (32340)------------------------------
% 0.21/0.56  % (32348)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 2.13/0.69  % (32356)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 2.13/0.70  % (32356)Refutation not found, incomplete strategy% (32356)------------------------------
% 2.13/0.70  % (32356)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.13/0.70  % (32356)Termination reason: Refutation not found, incomplete strategy
% 2.13/0.70  
% 2.13/0.70  % (32356)Memory used [KB]: 6140
% 2.13/0.70  % (32356)Time elapsed: 0.117 s
% 2.13/0.70  % (32356)------------------------------
% 2.13/0.70  % (32356)------------------------------
% 2.13/0.70  % (32327)Refutation not found, incomplete strategy% (32327)------------------------------
% 2.13/0.70  % (32327)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.13/0.70  % (32327)Termination reason: Refutation not found, incomplete strategy
% 2.13/0.70  
% 2.13/0.70  % (32327)Memory used [KB]: 6140
% 2.13/0.70  % (32327)Time elapsed: 0.296 s
% 2.13/0.70  % (32327)------------------------------
% 2.13/0.70  % (32327)------------------------------
% 2.69/0.71  % (32354)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.69/0.72  % (32335)Refutation found. Thanks to Tanya!
% 2.69/0.72  % SZS status Theorem for theBenchmark
% 2.69/0.72  % SZS output start Proof for theBenchmark
% 2.69/0.72  fof(f2625,plain,(
% 2.69/0.72    $false),
% 2.69/0.72    inference(subsumption_resolution,[],[f2619,f251])).
% 2.69/0.72  fof(f251,plain,(
% 2.69/0.72    ~r1_tarski(sK0,k1_relat_1(k7_relat_1(sK1,sK0)))),
% 2.69/0.72    inference(superposition,[],[f147,f83])).
% 2.69/0.72  fof(f83,plain,(
% 2.69/0.72    ( ! [X0] : (k1_relat_1(k7_relat_1(sK1,X0)) = k10_relat_1(k7_relat_1(sK1,X0),k9_relat_1(sK1,X0))) )),
% 2.69/0.72    inference(forward_demodulation,[],[f79,f65])).
% 2.69/0.72  fof(f65,plain,(
% 2.69/0.72    ( ! [X0] : (k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0)) )),
% 2.69/0.72    inference(unit_resulting_resolution,[],[f36,f47])).
% 2.69/0.72  fof(f47,plain,(
% 2.69/0.72    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 2.69/0.72    inference(cnf_transformation,[],[f24])).
% 2.69/0.72  fof(f24,plain,(
% 2.69/0.72    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.69/0.72    inference(ennf_transformation,[],[f14])).
% 2.69/0.72  fof(f14,axiom,(
% 2.69/0.72    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 2.69/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 2.69/0.72  fof(f36,plain,(
% 2.69/0.72    v1_relat_1(sK1)),
% 2.69/0.72    inference(cnf_transformation,[],[f33])).
% 2.69/0.72  fof(f33,plain,(
% 2.69/0.72    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1)),
% 2.69/0.72    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f32])).
% 2.69/0.72  fof(f32,plain,(
% 2.69/0.72    ? [X0,X1] : (~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1)) => (~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1))),
% 2.69/0.72    introduced(choice_axiom,[])).
% 2.69/0.72  fof(f21,plain,(
% 2.69/0.72    ? [X0,X1] : (~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1))),
% 2.69/0.72    inference(flattening,[],[f20])).
% 2.69/0.72  fof(f20,plain,(
% 2.69/0.72    ? [X0,X1] : ((~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1))) & v1_relat_1(X1))),
% 2.69/0.72    inference(ennf_transformation,[],[f19])).
% 2.69/0.72  fof(f19,negated_conjecture,(
% 2.69/0.72    ~! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 2.69/0.72    inference(negated_conjecture,[],[f18])).
% 2.69/0.72  fof(f18,conjecture,(
% 2.69/0.72    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 2.69/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).
% 2.69/0.72  fof(f79,plain,(
% 2.69/0.72    ( ! [X0] : (k10_relat_1(k7_relat_1(sK1,X0),k2_relat_1(k7_relat_1(sK1,X0))) = k1_relat_1(k7_relat_1(sK1,X0))) )),
% 2.69/0.72    inference(unit_resulting_resolution,[],[f66,f41])).
% 2.69/0.72  fof(f41,plain,(
% 2.69/0.72    ( ! [X0] : (~v1_relat_1(X0) | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)) )),
% 2.69/0.72    inference(cnf_transformation,[],[f22])).
% 2.69/0.72  fof(f22,plain,(
% 2.69/0.72    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 2.69/0.72    inference(ennf_transformation,[],[f15])).
% 2.69/0.72  fof(f15,axiom,(
% 2.69/0.72    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 2.69/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).
% 2.69/0.72  fof(f66,plain,(
% 2.69/0.72    ( ! [X0] : (v1_relat_1(k7_relat_1(sK1,X0))) )),
% 2.69/0.72    inference(unit_resulting_resolution,[],[f36,f46])).
% 2.69/0.72  fof(f46,plain,(
% 2.69/0.72    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 2.69/0.72    inference(cnf_transformation,[],[f23])).
% 2.69/0.72  fof(f23,plain,(
% 2.69/0.72    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 2.69/0.72    inference(ennf_transformation,[],[f13])).
% 2.69/0.72  fof(f13,axiom,(
% 2.69/0.72    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 2.69/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 2.69/0.72  fof(f147,plain,(
% 2.69/0.72    ( ! [X0] : (~r1_tarski(sK0,k10_relat_1(k7_relat_1(sK1,X0),k9_relat_1(sK1,sK0)))) )),
% 2.69/0.72    inference(forward_demodulation,[],[f145,f63])).
% 2.69/0.72  fof(f63,plain,(
% 2.69/0.72    ( ! [X0,X1] : (k10_relat_1(k7_relat_1(sK1,X0),X1) = k1_setfam_1(k2_tarski(X0,k10_relat_1(sK1,X1)))) )),
% 2.69/0.72    inference(unit_resulting_resolution,[],[f36,f59])).
% 2.69/0.72  fof(f59,plain,(
% 2.69/0.72    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k10_relat_1(k7_relat_1(X2,X0),X1) = k1_setfam_1(k2_tarski(X0,k10_relat_1(X2,X1)))) )),
% 2.69/0.72    inference(definition_unfolding,[],[f53,f44])).
% 2.69/0.72  fof(f44,plain,(
% 2.69/0.72    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.69/0.72    inference(cnf_transformation,[],[f12])).
% 2.69/0.72  fof(f12,axiom,(
% 2.69/0.72    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 2.69/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 2.69/0.72  fof(f53,plain,(
% 2.69/0.72    ( ! [X2,X0,X1] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 2.69/0.72    inference(cnf_transformation,[],[f27])).
% 2.69/0.72  fof(f27,plain,(
% 2.69/0.72    ! [X0,X1,X2] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 2.69/0.72    inference(ennf_transformation,[],[f17])).
% 2.69/0.72  fof(f17,axiom,(
% 2.69/0.72    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)))),
% 2.69/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).
% 2.69/0.73  fof(f145,plain,(
% 2.69/0.73    ( ! [X0] : (~r1_tarski(sK0,k1_setfam_1(k2_tarski(X0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))))) )),
% 2.69/0.73    inference(superposition,[],[f91,f42])).
% 2.69/0.73  fof(f42,plain,(
% 2.69/0.73    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 2.69/0.73    inference(cnf_transformation,[],[f11])).
% 2.69/0.73  fof(f11,axiom,(
% 2.69/0.73    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 2.69/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 2.69/0.73  fof(f91,plain,(
% 2.69/0.73    ( ! [X0] : (~r1_tarski(sK0,k1_setfam_1(k2_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),X0)))) )),
% 2.69/0.73    inference(unit_resulting_resolution,[],[f38,f60])).
% 2.69/0.73  fof(f60,plain,(
% 2.69/0.73    ( ! [X2,X0,X1] : (~r1_tarski(X0,k1_setfam_1(k2_tarski(X1,X2))) | r1_tarski(X0,X1)) )),
% 2.69/0.73    inference(definition_unfolding,[],[f54,f44])).
% 2.69/0.73  fof(f54,plain,(
% 2.69/0.73    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2))) )),
% 2.69/0.73    inference(cnf_transformation,[],[f28])).
% 2.69/0.73  fof(f28,plain,(
% 2.69/0.73    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 2.69/0.73    inference(ennf_transformation,[],[f5])).
% 2.69/0.73  fof(f5,axiom,(
% 2.69/0.73    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) => r1_tarski(X0,X1))),
% 2.69/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_xboole_1)).
% 2.69/0.73  fof(f38,plain,(
% 2.69/0.73    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 2.69/0.73    inference(cnf_transformation,[],[f33])).
% 2.69/0.73  fof(f2619,plain,(
% 2.69/0.73    r1_tarski(sK0,k1_relat_1(k7_relat_1(sK1,sK0)))),
% 2.69/0.73    inference(superposition,[],[f289,f2382])).
% 2.69/0.73  fof(f2382,plain,(
% 2.69/0.73    sK0 = k1_setfam_1(k2_tarski(sK0,k1_relat_1(sK1)))),
% 2.69/0.73    inference(forward_demodulation,[],[f2381,f40])).
% 2.69/0.73  fof(f40,plain,(
% 2.69/0.73    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.69/0.73    inference(cnf_transformation,[],[f7])).
% 2.69/0.73  fof(f7,axiom,(
% 2.69/0.73    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 2.69/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 2.69/0.73  fof(f2381,plain,(
% 2.69/0.73    k1_setfam_1(k2_tarski(sK0,k1_relat_1(sK1))) = k4_xboole_0(sK0,k1_xboole_0)),
% 2.69/0.73    inference(superposition,[],[f58,f2085])).
% 2.69/0.73  fof(f2085,plain,(
% 2.69/0.73    k1_xboole_0 = k4_xboole_0(sK0,k1_relat_1(sK1))),
% 2.69/0.73    inference(unit_resulting_resolution,[],[f37,f1556])).
% 2.69/0.73  fof(f1556,plain,(
% 2.69/0.73    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,X1)) )),
% 2.69/0.73    inference(forward_demodulation,[],[f1544,f1439])).
% 2.69/0.73  fof(f1439,plain,(
% 2.69/0.73    ( ! [X1] : (k2_xboole_0(X1,k1_xboole_0) = X1) )),
% 2.69/0.73    inference(superposition,[],[f1351,f43])).
% 2.69/0.73  fof(f43,plain,(
% 2.69/0.73    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 2.69/0.73    inference(cnf_transformation,[],[f1])).
% 2.69/0.73  fof(f1,axiom,(
% 2.69/0.73    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 2.69/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 2.69/0.73  fof(f1351,plain,(
% 2.69/0.73    ( ! [X1] : (k2_xboole_0(k1_xboole_0,X1) = X1) )),
% 2.69/0.73    inference(backward_demodulation,[],[f1321,f1312])).
% 2.69/0.73  fof(f1312,plain,(
% 2.69/0.73    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 2.69/0.73    inference(unit_resulting_resolution,[],[f39,f1261,f52])).
% 2.69/0.73  fof(f52,plain,(
% 2.69/0.73    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 2.69/0.73    inference(cnf_transformation,[],[f35])).
% 2.69/0.73  fof(f35,plain,(
% 2.69/0.73    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.69/0.73    inference(flattening,[],[f34])).
% 2.69/0.73  fof(f34,plain,(
% 2.69/0.73    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.69/0.73    inference(nnf_transformation,[],[f2])).
% 2.69/0.73  fof(f2,axiom,(
% 2.69/0.73    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.69/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.69/0.73  fof(f1261,plain,(
% 2.69/0.73    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(k1_xboole_0,X0),X1)) )),
% 2.69/0.73    inference(unit_resulting_resolution,[],[f39,f186])).
% 2.69/0.73  fof(f186,plain,(
% 2.69/0.73    ( ! [X6,X8,X7,X5] : (~r1_tarski(X5,k2_xboole_0(X6,k10_relat_1(k7_relat_1(sK1,X7),X8))) | r1_tarski(k4_xboole_0(X5,X6),X7)) )),
% 2.69/0.73    inference(resolution,[],[f159,f55])).
% 2.69/0.73  fof(f55,plain,(
% 2.69/0.73    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 2.69/0.73    inference(cnf_transformation,[],[f29])).
% 2.69/0.73  fof(f29,plain,(
% 2.69/0.73    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 2.69/0.73    inference(ennf_transformation,[],[f8])).
% 2.69/0.73  fof(f8,axiom,(
% 2.69/0.73    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 2.69/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).
% 2.69/0.73  fof(f159,plain,(
% 2.69/0.73    ( ! [X2,X0,X1] : (~r1_tarski(X2,k10_relat_1(k7_relat_1(sK1,X0),X1)) | r1_tarski(X2,X0)) )),
% 2.69/0.73    inference(superposition,[],[f60,f63])).
% 2.69/0.73  fof(f39,plain,(
% 2.69/0.73    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.69/0.73    inference(cnf_transformation,[],[f6])).
% 2.69/0.73  fof(f6,axiom,(
% 2.69/0.73    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.69/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 2.69/0.73  fof(f1321,plain,(
% 2.69/0.73    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1) = X1) )),
% 2.69/0.73    inference(unit_resulting_resolution,[],[f1261,f49])).
% 2.69/0.73  fof(f49,plain,(
% 2.69/0.73    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 2.69/0.73    inference(cnf_transformation,[],[f26])).
% 2.69/0.73  fof(f26,plain,(
% 2.69/0.73    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 2.69/0.73    inference(ennf_transformation,[],[f4])).
% 2.69/0.73  fof(f4,axiom,(
% 2.69/0.73    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 2.69/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 2.69/0.73  fof(f1544,plain,(
% 2.69/0.73    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,k2_xboole_0(X1,k1_xboole_0))) )),
% 2.69/0.73    inference(resolution,[],[f1370,f55])).
% 2.69/0.73  fof(f1370,plain,(
% 2.69/0.73    ( ! [X2] : (~r1_tarski(X2,k1_xboole_0) | k1_xboole_0 = X2) )),
% 2.69/0.73    inference(forward_demodulation,[],[f1369,f1312])).
% 2.69/0.73  fof(f1369,plain,(
% 2.69/0.73    ( ! [X2,X3] : (k1_xboole_0 = X2 | ~r1_tarski(X2,k4_xboole_0(k1_xboole_0,X3))) )),
% 2.69/0.73    inference(forward_demodulation,[],[f1331,f1312])).
% 2.69/0.73  fof(f1331,plain,(
% 2.69/0.73    ( ! [X2,X3] : (k4_xboole_0(k1_xboole_0,X3) = X2 | ~r1_tarski(X2,k4_xboole_0(k1_xboole_0,X3))) )),
% 2.69/0.73    inference(resolution,[],[f1261,f52])).
% 2.69/0.73  fof(f37,plain,(
% 2.69/0.73    r1_tarski(sK0,k1_relat_1(sK1))),
% 2.69/0.73    inference(cnf_transformation,[],[f33])).
% 2.69/0.73  fof(f58,plain,(
% 2.69/0.73    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.69/0.73    inference(definition_unfolding,[],[f45,f44])).
% 2.69/0.73  fof(f45,plain,(
% 2.69/0.73    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 2.69/0.73    inference(cnf_transformation,[],[f10])).
% 2.69/0.73  fof(f10,axiom,(
% 2.69/0.73    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 2.69/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.69/0.73  fof(f289,plain,(
% 2.69/0.73    ( ! [X3] : (r1_tarski(k1_setfam_1(k2_tarski(X3,k1_relat_1(sK1))),k1_relat_1(k7_relat_1(sK1,X3)))) )),
% 2.69/0.73    inference(superposition,[],[f85,f156])).
% 2.69/0.73  fof(f156,plain,(
% 2.69/0.73    ( ! [X0] : (k10_relat_1(k7_relat_1(sK1,X0),k2_relat_1(sK1)) = k1_setfam_1(k2_tarski(X0,k1_relat_1(sK1)))) )),
% 2.69/0.73    inference(superposition,[],[f63,f67])).
% 2.69/0.73  fof(f67,plain,(
% 2.69/0.73    k1_relat_1(sK1) = k10_relat_1(sK1,k2_relat_1(sK1))),
% 2.69/0.73    inference(unit_resulting_resolution,[],[f36,f41])).
% 2.69/0.73  fof(f85,plain,(
% 2.69/0.73    ( ! [X0,X1] : (r1_tarski(k10_relat_1(k7_relat_1(sK1,X0),X1),k1_relat_1(k7_relat_1(sK1,X0)))) )),
% 2.69/0.73    inference(forward_demodulation,[],[f84,f83])).
% 2.69/0.73  fof(f84,plain,(
% 2.69/0.73    ( ! [X0,X1] : (r1_tarski(k10_relat_1(k7_relat_1(sK1,X0),X1),k10_relat_1(k7_relat_1(sK1,X0),k9_relat_1(sK1,X0)))) )),
% 2.69/0.73    inference(forward_demodulation,[],[f76,f65])).
% 2.69/0.73  fof(f76,plain,(
% 2.69/0.73    ( ! [X0,X1] : (r1_tarski(k10_relat_1(k7_relat_1(sK1,X0),X1),k10_relat_1(k7_relat_1(sK1,X0),k2_relat_1(k7_relat_1(sK1,X0))))) )),
% 2.69/0.73    inference(unit_resulting_resolution,[],[f66,f48])).
% 2.69/0.73  fof(f48,plain,(
% 2.69/0.73    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1))) | ~v1_relat_1(X1)) )),
% 2.69/0.73    inference(cnf_transformation,[],[f25])).
% 2.69/0.73  fof(f25,plain,(
% 2.69/0.73    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1))) | ~v1_relat_1(X1))),
% 2.69/0.73    inference(ennf_transformation,[],[f16])).
% 2.69/0.73  fof(f16,axiom,(
% 2.69/0.73    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1))))),
% 2.69/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t170_relat_1)).
% 2.69/0.73  % SZS output end Proof for theBenchmark
% 2.69/0.73  % (32335)------------------------------
% 2.69/0.73  % (32335)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.69/0.73  % (32335)Termination reason: Refutation
% 2.69/0.73  
% 2.69/0.73  % (32335)Memory used [KB]: 8059
% 2.69/0.73  % (32335)Time elapsed: 0.323 s
% 2.69/0.73  % (32335)------------------------------
% 2.69/0.73  % (32335)------------------------------
% 2.69/0.73  % (32323)Success in time 0.367 s
%------------------------------------------------------------------------------
