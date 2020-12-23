%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:45 EST 2020

% Result     : Theorem 2.42s
% Output     : Refutation 2.42s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 280 expanded)
%              Number of leaves         :   17 (  81 expanded)
%              Depth                    :   14
%              Number of atoms          :  200 ( 512 expanded)
%              Number of equality atoms :   54 ( 148 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1370,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f43,f1368,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f1368,plain,(
    ~ v1_relat_1(k7_relat_1(sK2,sK1)) ),
    inference(subsumption_resolution,[],[f1363,f1335])).

fof(f1335,plain,(
    ! [X6,X7] : r1_tarski(k7_relat_1(k7_relat_1(sK2,X6),X7),k8_relat_1(k9_relat_1(sK2,X6),k7_relat_1(sK2,X7))) ),
    inference(superposition,[],[f1202,f1073])).

fof(f1073,plain,(
    ! [X0] : k7_relat_1(sK2,X0) = k7_relat_1(k8_relat_1(k9_relat_1(sK2,X0),sK2),X0) ),
    inference(subsumption_resolution,[],[f1051,f43])).

fof(f1051,plain,(
    ! [X0] :
      ( k7_relat_1(sK2,X0) = k7_relat_1(k8_relat_1(k9_relat_1(sK2,X0),sK2),X0)
      | ~ v1_relat_1(sK2) ) ),
    inference(superposition,[],[f1045,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f1045,plain,(
    ! [X53] : k7_relat_1(sK2,X53) = k7_relat_1(k8_relat_1(k2_relat_1(k7_relat_1(sK2,X53)),sK2),X53) ),
    inference(resolution,[],[f233,f43])).

fof(f233,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k7_relat_1(X0,X1) = k7_relat_1(k8_relat_1(k2_relat_1(k7_relat_1(X0,X1)),X0),X1) ) ),
    inference(resolution,[],[f89,f73])).

fof(f73,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f89,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_tarski(k2_relat_1(k7_relat_1(X4,X5)),X3)
      | ~ v1_relat_1(X4)
      | k7_relat_1(X4,X5) = k7_relat_1(k8_relat_1(X3,X4),X5) ) ),
    inference(subsumption_resolution,[],[f86,f52])).

fof(f86,plain,(
    ! [X4,X5,X3] :
      ( k7_relat_1(X4,X5) = k7_relat_1(k8_relat_1(X3,X4),X5)
      | ~ v1_relat_1(X4)
      | ~ r1_tarski(k2_relat_1(k7_relat_1(X4,X5)),X3)
      | ~ v1_relat_1(k7_relat_1(X4,X5)) ) ),
    inference(superposition,[],[f65,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k8_relat_1(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t140_relat_1)).

fof(f1202,plain,(
    ! [X80,X81,X79] : r1_tarski(k7_relat_1(k7_relat_1(k8_relat_1(X79,sK2),X81),X80),k8_relat_1(X79,k7_relat_1(sK2,X80))) ),
    inference(forward_demodulation,[],[f1198,f415])).

fof(f415,plain,(
    ! [X85,X83,X84] : k8_relat_1(X85,k7_relat_1(k7_relat_1(sK2,X84),X83)) = k7_relat_1(k7_relat_1(k8_relat_1(X85,sK2),X83),X84) ),
    inference(backward_demodulation,[],[f322,f414])).

fof(f414,plain,(
    ! [X47,X48,X49] : k7_relat_1(k7_relat_1(k8_relat_1(X47,sK2),X48),X49) = k7_relat_1(k8_relat_1(X47,sK2),k1_setfam_1(k2_enumset1(X48,X48,X48,X49))) ),
    inference(resolution,[],[f128,f43])).

fof(f128,plain,(
    ! [X14,X15,X13,X16] :
      ( ~ v1_relat_1(X14)
      | k7_relat_1(k7_relat_1(k8_relat_1(X13,X14),X15),X16) = k7_relat_1(k8_relat_1(X13,X14),k1_setfam_1(k2_enumset1(X15,X15,X15,X16))) ) ),
    inference(resolution,[],[f72,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relat_1)).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) ) ),
    inference(definition_unfolding,[],[f66,f68])).

fof(f68,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f50,f67])).

fof(f67,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f49,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f49,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f50,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

fof(f322,plain,(
    ! [X85,X83,X84] : k7_relat_1(k8_relat_1(X85,sK2),k1_setfam_1(k2_enumset1(X83,X83,X83,X84))) = k8_relat_1(X85,k7_relat_1(k7_relat_1(sK2,X84),X83)) ),
    inference(subsumption_resolution,[],[f315,f43])).

fof(f315,plain,(
    ! [X85,X83,X84] :
      ( k7_relat_1(k8_relat_1(X85,sK2),k1_setfam_1(k2_enumset1(X83,X83,X83,X84))) = k8_relat_1(X85,k7_relat_1(k7_relat_1(sK2,X84),X83))
      | ~ v1_relat_1(sK2) ) ),
    inference(superposition,[],[f65,f135])).

fof(f135,plain,(
    ! [X0,X1] : k7_relat_1(k7_relat_1(sK2,X0),X1) = k7_relat_1(sK2,k1_setfam_1(k2_enumset1(X1,X1,X1,X0))) ),
    inference(superposition,[],[f129,f70])).

fof(f70,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f48,f67,f67])).

fof(f48,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f129,plain,(
    ! [X17,X18] : k7_relat_1(k7_relat_1(sK2,X17),X18) = k7_relat_1(sK2,k1_setfam_1(k2_enumset1(X17,X17,X17,X18))) ),
    inference(resolution,[],[f72,f43])).

fof(f1198,plain,(
    ! [X80,X81,X79] : r1_tarski(k8_relat_1(X79,k7_relat_1(k7_relat_1(sK2,X80),X81)),k8_relat_1(X79,k7_relat_1(sK2,X80))) ),
    inference(resolution,[],[f265,f43])).

fof(f265,plain,(
    ! [X10,X8,X7,X9] :
      ( ~ v1_relat_1(X8)
      | r1_tarski(k8_relat_1(X7,k7_relat_1(k7_relat_1(X8,X9),X10)),k8_relat_1(X7,k7_relat_1(X8,X9))) ) ),
    inference(subsumption_resolution,[],[f264,f52])).

fof(f264,plain,(
    ! [X10,X8,X7,X9] :
      ( r1_tarski(k8_relat_1(X7,k7_relat_1(k7_relat_1(X8,X9),X10)),k8_relat_1(X7,k7_relat_1(X8,X9)))
      | ~ v1_relat_1(X8)
      | ~ v1_relat_1(k7_relat_1(X8,X9)) ) ),
    inference(subsumption_resolution,[],[f260,f52])).

fof(f260,plain,(
    ! [X10,X8,X7,X9] :
      ( r1_tarski(k8_relat_1(X7,k7_relat_1(k7_relat_1(X8,X9),X10)),k8_relat_1(X7,k7_relat_1(X8,X9)))
      | ~ v1_relat_1(k7_relat_1(k7_relat_1(X8,X9),X10))
      | ~ v1_relat_1(X8)
      | ~ v1_relat_1(k7_relat_1(X8,X9)) ) ),
    inference(resolution,[],[f92,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

fof(f92,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r1_tarski(X4,k7_relat_1(X5,X6))
      | r1_tarski(k8_relat_1(X7,X4),k8_relat_1(X7,k7_relat_1(X5,X6)))
      | ~ v1_relat_1(X4)
      | ~ v1_relat_1(X5) ) ),
    inference(resolution,[],[f57,f52])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_relat_1)).

fof(f1363,plain,
    ( ~ r1_tarski(k7_relat_1(k7_relat_1(sK2,sK0),sK1),k8_relat_1(k9_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)))
    | ~ v1_relat_1(k7_relat_1(sK2,sK1)) ),
    inference(resolution,[],[f1328,f51])).

fof(f1328,plain,
    ( ~ v1_relat_1(k8_relat_1(k9_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)))
    | ~ r1_tarski(k7_relat_1(k7_relat_1(sK2,sK0),sK1),k8_relat_1(k9_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))) ),
    inference(subsumption_resolution,[],[f1324,f148])).

fof(f148,plain,(
    ! [X8,X9] : v1_relat_1(k7_relat_1(k7_relat_1(sK2,X8),X9)) ),
    inference(subsumption_resolution,[],[f141,f43])).

fof(f141,plain,(
    ! [X8,X9] :
      ( v1_relat_1(k7_relat_1(k7_relat_1(sK2,X8),X9))
      | ~ v1_relat_1(sK2) ) ),
    inference(superposition,[],[f52,f129])).

fof(f1324,plain,
    ( ~ r1_tarski(k7_relat_1(k7_relat_1(sK2,sK0),sK1),k8_relat_1(k9_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)))
    | ~ v1_relat_1(k8_relat_1(k9_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)))
    | ~ v1_relat_1(k7_relat_1(k7_relat_1(sK2,sK0),sK1)) ),
    inference(resolution,[],[f1306,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

fof(f1306,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(sK2,sK0),sK1)),k2_relat_1(k8_relat_1(k9_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)))) ),
    inference(backward_demodulation,[],[f151,f1301])).

fof(f1301,plain,(
    ! [X66,X67] : k2_relat_1(k8_relat_1(X66,k7_relat_1(sK2,X67))) = k1_setfam_1(k2_enumset1(X66,X66,X66,k9_relat_1(sK2,X67))) ),
    inference(resolution,[],[f172,f43])).

fof(f172,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | k2_relat_1(k8_relat_1(X2,k7_relat_1(X0,X1))) = k1_setfam_1(k2_enumset1(X2,X2,X2,k9_relat_1(X0,X1))) ) ),
    inference(subsumption_resolution,[],[f166,f52])).

fof(f166,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(k8_relat_1(X2,k7_relat_1(X0,X1))) = k1_setfam_1(k2_enumset1(X2,X2,X2,k9_relat_1(X0,X1)))
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f117,f54])).

fof(f117,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k8_relat_1(X1,X0)) = k1_setfam_1(k2_enumset1(X1,X1,X1,k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f71,f70])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,X1)) = k1_setfam_1(k2_enumset1(k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f55,f68])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t119_relat_1)).

fof(f151,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(sK2,sK0),sK1)),k1_setfam_1(k2_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))) ),
    inference(backward_demodulation,[],[f69,f150])).

fof(f150,plain,(
    ! [X12,X13] : k9_relat_1(sK2,k1_setfam_1(k2_enumset1(X12,X12,X12,X13))) = k2_relat_1(k7_relat_1(k7_relat_1(sK2,X12),X13)) ),
    inference(subsumption_resolution,[],[f143,f43])).

fof(f143,plain,(
    ! [X12,X13] :
      ( k9_relat_1(sK2,k1_setfam_1(k2_enumset1(X12,X12,X12,X13))) = k2_relat_1(k7_relat_1(k7_relat_1(sK2,X12),X13))
      | ~ v1_relat_1(sK2) ) ),
    inference(superposition,[],[f54,f129])).

fof(f69,plain,(
    ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_setfam_1(k2_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))) ),
    inference(definition_unfolding,[],[f44,f68,f68])).

fof(f44,plain,(
    ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f38])).

fof(f38,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t154_relat_1)).

fof(f43,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f39])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:53:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.50  % (13435)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.51  % (13451)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.51  % (13443)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.51  % (13451)Refutation not found, incomplete strategy% (13451)------------------------------
% 0.21/0.51  % (13451)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (13451)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (13451)Memory used [KB]: 10746
% 0.21/0.51  % (13451)Time elapsed: 0.108 s
% 0.21/0.51  % (13451)------------------------------
% 0.21/0.51  % (13451)------------------------------
% 0.21/0.51  % (13450)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.51  % (13427)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.52  % (13445)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.52  % (13436)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.52  % (13431)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.52  % (13423)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.52  % (13426)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.52  % (13440)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.53  % (13439)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.53  % (13441)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.53  % (13424)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.53  % (13432)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.53  % (13434)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.53  % (13449)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.53  % (13442)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.53  % (13437)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.36/0.53  % (13444)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.36/0.53  % (13439)Refutation not found, incomplete strategy% (13439)------------------------------
% 1.36/0.53  % (13439)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.53  % (13428)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.36/0.54  % (13425)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.36/0.54  % (13447)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.36/0.54  % (13429)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.36/0.54  % (13438)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.36/0.54  % (13439)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.54  
% 1.36/0.54  % (13439)Memory used [KB]: 10618
% 1.36/0.54  % (13439)Time elapsed: 0.129 s
% 1.36/0.54  % (13439)------------------------------
% 1.36/0.54  % (13439)------------------------------
% 1.36/0.54  % (13446)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.36/0.54  % (13433)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.36/0.54  % (13433)Refutation not found, incomplete strategy% (13433)------------------------------
% 1.36/0.54  % (13433)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.55  % (13433)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.55  
% 1.45/0.55  % (13433)Memory used [KB]: 10746
% 1.45/0.55  % (13433)Time elapsed: 0.142 s
% 1.45/0.55  % (13433)------------------------------
% 1.45/0.55  % (13433)------------------------------
% 1.45/0.55  % (13430)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.45/0.55  % (13452)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.45/0.56  % (13448)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 2.04/0.64  % (13426)Refutation not found, incomplete strategy% (13426)------------------------------
% 2.04/0.64  % (13426)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.04/0.64  % (13426)Termination reason: Refutation not found, incomplete strategy
% 2.04/0.64  
% 2.04/0.64  % (13426)Memory used [KB]: 6140
% 2.04/0.64  % (13426)Time elapsed: 0.235 s
% 2.04/0.64  % (13426)------------------------------
% 2.04/0.64  % (13426)------------------------------
% 2.04/0.66  % (13453)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.42/0.69  % (13454)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.42/0.70  % (13455)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 2.42/0.70  % (13455)Refutation not found, incomplete strategy% (13455)------------------------------
% 2.42/0.70  % (13455)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.42/0.70  % (13455)Termination reason: Refutation not found, incomplete strategy
% 2.42/0.70  
% 2.42/0.70  % (13455)Memory used [KB]: 6140
% 2.42/0.70  % (13455)Time elapsed: 0.099 s
% 2.42/0.70  % (13455)------------------------------
% 2.42/0.70  % (13455)------------------------------
% 2.42/0.73  % (13445)Refutation found. Thanks to Tanya!
% 2.42/0.73  % SZS status Theorem for theBenchmark
% 2.42/0.73  % SZS output start Proof for theBenchmark
% 2.42/0.73  fof(f1370,plain,(
% 2.42/0.73    $false),
% 2.42/0.73    inference(unit_resulting_resolution,[],[f43,f1368,f52])).
% 2.42/0.73  fof(f52,plain,(
% 2.42/0.73    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 2.42/0.73    inference(cnf_transformation,[],[f26])).
% 2.42/0.73  fof(f26,plain,(
% 2.42/0.73    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 2.42/0.73    inference(ennf_transformation,[],[f8])).
% 2.42/0.73  fof(f8,axiom,(
% 2.42/0.73    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 2.42/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 2.42/0.73  fof(f1368,plain,(
% 2.42/0.73    ~v1_relat_1(k7_relat_1(sK2,sK1))),
% 2.42/0.73    inference(subsumption_resolution,[],[f1363,f1335])).
% 2.42/0.73  fof(f1335,plain,(
% 2.42/0.73    ( ! [X6,X7] : (r1_tarski(k7_relat_1(k7_relat_1(sK2,X6),X7),k8_relat_1(k9_relat_1(sK2,X6),k7_relat_1(sK2,X7)))) )),
% 2.42/0.73    inference(superposition,[],[f1202,f1073])).
% 2.42/0.74  fof(f1073,plain,(
% 2.42/0.74    ( ! [X0] : (k7_relat_1(sK2,X0) = k7_relat_1(k8_relat_1(k9_relat_1(sK2,X0),sK2),X0)) )),
% 2.42/0.74    inference(subsumption_resolution,[],[f1051,f43])).
% 2.42/0.74  fof(f1051,plain,(
% 2.42/0.74    ( ! [X0] : (k7_relat_1(sK2,X0) = k7_relat_1(k8_relat_1(k9_relat_1(sK2,X0),sK2),X0) | ~v1_relat_1(sK2)) )),
% 2.42/0.74    inference(superposition,[],[f1045,f54])).
% 2.42/0.74  fof(f54,plain,(
% 2.42/0.74    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.42/0.74    inference(cnf_transformation,[],[f28])).
% 2.42/0.74  fof(f28,plain,(
% 2.42/0.74    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.42/0.74    inference(ennf_transformation,[],[f16])).
% 2.42/0.74  fof(f16,axiom,(
% 2.42/0.74    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 2.42/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 2.42/0.74  fof(f1045,plain,(
% 2.42/0.74    ( ! [X53] : (k7_relat_1(sK2,X53) = k7_relat_1(k8_relat_1(k2_relat_1(k7_relat_1(sK2,X53)),sK2),X53)) )),
% 2.42/0.74    inference(resolution,[],[f233,f43])).
% 2.42/0.74  fof(f233,plain,(
% 2.42/0.74    ( ! [X0,X1] : (~v1_relat_1(X0) | k7_relat_1(X0,X1) = k7_relat_1(k8_relat_1(k2_relat_1(k7_relat_1(X0,X1)),X0),X1)) )),
% 2.42/0.74    inference(resolution,[],[f89,f73])).
% 2.42/0.74  fof(f73,plain,(
% 2.42/0.74    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.42/0.74    inference(equality_resolution,[],[f60])).
% 2.42/0.74  fof(f60,plain,(
% 2.42/0.74    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.42/0.74    inference(cnf_transformation,[],[f41])).
% 2.42/0.74  fof(f41,plain,(
% 2.42/0.74    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.42/0.74    inference(flattening,[],[f40])).
% 2.42/0.74  fof(f40,plain,(
% 2.42/0.74    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.42/0.74    inference(nnf_transformation,[],[f1])).
% 2.42/0.74  fof(f1,axiom,(
% 2.42/0.74    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.42/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.42/0.74  fof(f89,plain,(
% 2.42/0.74    ( ! [X4,X5,X3] : (~r1_tarski(k2_relat_1(k7_relat_1(X4,X5)),X3) | ~v1_relat_1(X4) | k7_relat_1(X4,X5) = k7_relat_1(k8_relat_1(X3,X4),X5)) )),
% 2.42/0.74    inference(subsumption_resolution,[],[f86,f52])).
% 2.42/0.74  fof(f86,plain,(
% 2.42/0.74    ( ! [X4,X5,X3] : (k7_relat_1(X4,X5) = k7_relat_1(k8_relat_1(X3,X4),X5) | ~v1_relat_1(X4) | ~r1_tarski(k2_relat_1(k7_relat_1(X4,X5)),X3) | ~v1_relat_1(k7_relat_1(X4,X5))) )),
% 2.42/0.74    inference(superposition,[],[f65,f56])).
% 2.42/0.74  fof(f56,plain,(
% 2.42/0.74    ( ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 2.42/0.74    inference(cnf_transformation,[],[f31])).
% 2.42/0.74  fof(f31,plain,(
% 2.42/0.74    ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 2.42/0.74    inference(flattening,[],[f30])).
% 2.42/0.74  fof(f30,plain,(
% 2.42/0.74    ! [X0,X1] : ((k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.42/0.74    inference(ennf_transformation,[],[f13])).
% 2.42/0.74  fof(f13,axiom,(
% 2.42/0.74    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k8_relat_1(X0,X1) = X1))),
% 2.42/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).
% 2.42/0.74  fof(f65,plain,(
% 2.42/0.74    ( ! [X2,X0,X1] : (k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 2.42/0.74    inference(cnf_transformation,[],[f36])).
% 2.42/0.74  fof(f36,plain,(
% 2.42/0.74    ! [X0,X1,X2] : (k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 2.42/0.74    inference(ennf_transformation,[],[f15])).
% 2.42/0.74  fof(f15,axiom,(
% 2.42/0.74    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1)))),
% 2.42/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t140_relat_1)).
% 2.42/0.74  fof(f1202,plain,(
% 2.42/0.74    ( ! [X80,X81,X79] : (r1_tarski(k7_relat_1(k7_relat_1(k8_relat_1(X79,sK2),X81),X80),k8_relat_1(X79,k7_relat_1(sK2,X80)))) )),
% 2.42/0.74    inference(forward_demodulation,[],[f1198,f415])).
% 2.42/0.74  fof(f415,plain,(
% 2.42/0.74    ( ! [X85,X83,X84] : (k8_relat_1(X85,k7_relat_1(k7_relat_1(sK2,X84),X83)) = k7_relat_1(k7_relat_1(k8_relat_1(X85,sK2),X83),X84)) )),
% 2.42/0.74    inference(backward_demodulation,[],[f322,f414])).
% 2.42/0.74  fof(f414,plain,(
% 2.42/0.74    ( ! [X47,X48,X49] : (k7_relat_1(k7_relat_1(k8_relat_1(X47,sK2),X48),X49) = k7_relat_1(k8_relat_1(X47,sK2),k1_setfam_1(k2_enumset1(X48,X48,X48,X49)))) )),
% 2.42/0.74    inference(resolution,[],[f128,f43])).
% 2.42/0.74  fof(f128,plain,(
% 2.42/0.74    ( ! [X14,X15,X13,X16] : (~v1_relat_1(X14) | k7_relat_1(k7_relat_1(k8_relat_1(X13,X14),X15),X16) = k7_relat_1(k8_relat_1(X13,X14),k1_setfam_1(k2_enumset1(X15,X15,X15,X16)))) )),
% 2.42/0.74    inference(resolution,[],[f72,f51])).
% 2.42/0.74  fof(f51,plain,(
% 2.42/0.74    ( ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1)) )),
% 2.42/0.74    inference(cnf_transformation,[],[f25])).
% 2.42/0.74  fof(f25,plain,(
% 2.42/0.74    ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1))),
% 2.42/0.74    inference(ennf_transformation,[],[f9])).
% 2.42/0.74  fof(f9,axiom,(
% 2.42/0.74    ! [X0,X1] : (v1_relat_1(X1) => v1_relat_1(k8_relat_1(X0,X1)))),
% 2.42/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relat_1)).
% 2.42/0.74  fof(f72,plain,(
% 2.42/0.74    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))) )),
% 2.42/0.74    inference(definition_unfolding,[],[f66,f68])).
% 2.42/0.74  fof(f68,plain,(
% 2.42/0.74    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 2.42/0.74    inference(definition_unfolding,[],[f50,f67])).
% 2.42/0.74  fof(f67,plain,(
% 2.42/0.74    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 2.42/0.74    inference(definition_unfolding,[],[f49,f64])).
% 2.42/0.74  fof(f64,plain,(
% 2.42/0.74    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 2.42/0.74    inference(cnf_transformation,[],[f4])).
% 2.42/0.74  fof(f4,axiom,(
% 2.42/0.74    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 2.42/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 2.42/0.74  fof(f49,plain,(
% 2.42/0.74    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.42/0.74    inference(cnf_transformation,[],[f3])).
% 2.42/0.74  fof(f3,axiom,(
% 2.42/0.74    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.42/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 2.42/0.74  fof(f50,plain,(
% 2.42/0.74    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 2.42/0.74    inference(cnf_transformation,[],[f5])).
% 2.42/0.74  fof(f5,axiom,(
% 2.42/0.74    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 2.42/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 2.42/0.74  fof(f66,plain,(
% 2.42/0.74    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2)) )),
% 2.42/0.74    inference(cnf_transformation,[],[f37])).
% 2.42/0.74  fof(f37,plain,(
% 2.42/0.74    ! [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 2.42/0.74    inference(ennf_transformation,[],[f10])).
% 2.42/0.74  fof(f10,axiom,(
% 2.42/0.74    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)))),
% 2.42/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).
% 2.42/0.74  fof(f322,plain,(
% 2.42/0.74    ( ! [X85,X83,X84] : (k7_relat_1(k8_relat_1(X85,sK2),k1_setfam_1(k2_enumset1(X83,X83,X83,X84))) = k8_relat_1(X85,k7_relat_1(k7_relat_1(sK2,X84),X83))) )),
% 2.42/0.74    inference(subsumption_resolution,[],[f315,f43])).
% 2.42/0.74  fof(f315,plain,(
% 2.42/0.74    ( ! [X85,X83,X84] : (k7_relat_1(k8_relat_1(X85,sK2),k1_setfam_1(k2_enumset1(X83,X83,X83,X84))) = k8_relat_1(X85,k7_relat_1(k7_relat_1(sK2,X84),X83)) | ~v1_relat_1(sK2)) )),
% 2.42/0.74    inference(superposition,[],[f65,f135])).
% 2.42/0.74  fof(f135,plain,(
% 2.42/0.74    ( ! [X0,X1] : (k7_relat_1(k7_relat_1(sK2,X0),X1) = k7_relat_1(sK2,k1_setfam_1(k2_enumset1(X1,X1,X1,X0)))) )),
% 2.42/0.74    inference(superposition,[],[f129,f70])).
% 2.42/0.74  fof(f70,plain,(
% 2.42/0.74    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0)) )),
% 2.42/0.74    inference(definition_unfolding,[],[f48,f67,f67])).
% 2.42/0.74  fof(f48,plain,(
% 2.42/0.74    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 2.42/0.74    inference(cnf_transformation,[],[f2])).
% 2.42/0.74  fof(f2,axiom,(
% 2.42/0.74    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 2.42/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 2.42/0.74  fof(f129,plain,(
% 2.42/0.74    ( ! [X17,X18] : (k7_relat_1(k7_relat_1(sK2,X17),X18) = k7_relat_1(sK2,k1_setfam_1(k2_enumset1(X17,X17,X17,X18)))) )),
% 2.42/0.74    inference(resolution,[],[f72,f43])).
% 2.42/0.74  fof(f1198,plain,(
% 2.42/0.74    ( ! [X80,X81,X79] : (r1_tarski(k8_relat_1(X79,k7_relat_1(k7_relat_1(sK2,X80),X81)),k8_relat_1(X79,k7_relat_1(sK2,X80)))) )),
% 2.42/0.74    inference(resolution,[],[f265,f43])).
% 2.42/0.74  fof(f265,plain,(
% 2.42/0.74    ( ! [X10,X8,X7,X9] : (~v1_relat_1(X8) | r1_tarski(k8_relat_1(X7,k7_relat_1(k7_relat_1(X8,X9),X10)),k8_relat_1(X7,k7_relat_1(X8,X9)))) )),
% 2.42/0.74    inference(subsumption_resolution,[],[f264,f52])).
% 2.42/0.74  fof(f264,plain,(
% 2.42/0.74    ( ! [X10,X8,X7,X9] : (r1_tarski(k8_relat_1(X7,k7_relat_1(k7_relat_1(X8,X9),X10)),k8_relat_1(X7,k7_relat_1(X8,X9))) | ~v1_relat_1(X8) | ~v1_relat_1(k7_relat_1(X8,X9))) )),
% 2.42/0.74    inference(subsumption_resolution,[],[f260,f52])).
% 2.42/0.74  fof(f260,plain,(
% 2.42/0.74    ( ! [X10,X8,X7,X9] : (r1_tarski(k8_relat_1(X7,k7_relat_1(k7_relat_1(X8,X9),X10)),k8_relat_1(X7,k7_relat_1(X8,X9))) | ~v1_relat_1(k7_relat_1(k7_relat_1(X8,X9),X10)) | ~v1_relat_1(X8) | ~v1_relat_1(k7_relat_1(X8,X9))) )),
% 2.42/0.74    inference(resolution,[],[f92,f53])).
% 2.42/0.74  fof(f53,plain,(
% 2.42/0.74    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1)) )),
% 2.42/0.74    inference(cnf_transformation,[],[f27])).
% 2.42/0.74  fof(f27,plain,(
% 2.42/0.74    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 2.42/0.74    inference(ennf_transformation,[],[f18])).
% 2.42/0.74  fof(f18,axiom,(
% 2.42/0.74    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 2.42/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).
% 2.42/0.74  fof(f92,plain,(
% 2.42/0.74    ( ! [X6,X4,X7,X5] : (~r1_tarski(X4,k7_relat_1(X5,X6)) | r1_tarski(k8_relat_1(X7,X4),k8_relat_1(X7,k7_relat_1(X5,X6))) | ~v1_relat_1(X4) | ~v1_relat_1(X5)) )),
% 2.42/0.74    inference(resolution,[],[f57,f52])).
% 2.42/0.74  fof(f57,plain,(
% 2.42/0.74    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_tarski(X1,X2) | r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2)) | ~v1_relat_1(X1)) )),
% 2.42/0.74    inference(cnf_transformation,[],[f33])).
% 2.42/0.74  fof(f33,plain,(
% 2.42/0.74    ! [X0,X1] : (! [X2] : (r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 2.42/0.74    inference(flattening,[],[f32])).
% 2.42/0.74  fof(f32,plain,(
% 2.42/0.74    ! [X0,X1] : (! [X2] : ((r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 2.42/0.74    inference(ennf_transformation,[],[f14])).
% 2.42/0.74  fof(f14,axiom,(
% 2.42/0.74    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X1,X2) => r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2)))))),
% 2.42/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_relat_1)).
% 2.42/0.74  fof(f1363,plain,(
% 2.42/0.74    ~r1_tarski(k7_relat_1(k7_relat_1(sK2,sK0),sK1),k8_relat_1(k9_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))) | ~v1_relat_1(k7_relat_1(sK2,sK1))),
% 2.42/0.74    inference(resolution,[],[f1328,f51])).
% 2.42/0.74  fof(f1328,plain,(
% 2.42/0.74    ~v1_relat_1(k8_relat_1(k9_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))) | ~r1_tarski(k7_relat_1(k7_relat_1(sK2,sK0),sK1),k8_relat_1(k9_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)))),
% 2.42/0.74    inference(subsumption_resolution,[],[f1324,f148])).
% 2.42/0.74  fof(f148,plain,(
% 2.42/0.74    ( ! [X8,X9] : (v1_relat_1(k7_relat_1(k7_relat_1(sK2,X8),X9))) )),
% 2.42/0.74    inference(subsumption_resolution,[],[f141,f43])).
% 2.42/0.74  fof(f141,plain,(
% 2.42/0.74    ( ! [X8,X9] : (v1_relat_1(k7_relat_1(k7_relat_1(sK2,X8),X9)) | ~v1_relat_1(sK2)) )),
% 2.42/0.74    inference(superposition,[],[f52,f129])).
% 2.42/0.74  fof(f1324,plain,(
% 2.42/0.74    ~r1_tarski(k7_relat_1(k7_relat_1(sK2,sK0),sK1),k8_relat_1(k9_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))) | ~v1_relat_1(k8_relat_1(k9_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))) | ~v1_relat_1(k7_relat_1(k7_relat_1(sK2,sK0),sK1))),
% 2.42/0.74    inference(resolution,[],[f1306,f46])).
% 2.42/0.74  fof(f46,plain,(
% 2.42/0.74    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.42/0.74    inference(cnf_transformation,[],[f23])).
% 2.42/0.74  fof(f23,plain,(
% 2.42/0.74    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.42/0.74    inference(flattening,[],[f22])).
% 2.42/0.74  fof(f22,plain,(
% 2.42/0.74    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.42/0.74    inference(ennf_transformation,[],[f17])).
% 2.42/0.74  fof(f17,axiom,(
% 2.42/0.74    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 2.42/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).
% 2.42/0.74  fof(f1306,plain,(
% 2.42/0.74    ~r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(sK2,sK0),sK1)),k2_relat_1(k8_relat_1(k9_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))))),
% 2.42/0.74    inference(backward_demodulation,[],[f151,f1301])).
% 2.42/0.74  fof(f1301,plain,(
% 2.42/0.74    ( ! [X66,X67] : (k2_relat_1(k8_relat_1(X66,k7_relat_1(sK2,X67))) = k1_setfam_1(k2_enumset1(X66,X66,X66,k9_relat_1(sK2,X67)))) )),
% 2.42/0.74    inference(resolution,[],[f172,f43])).
% 2.42/0.74  fof(f172,plain,(
% 2.42/0.74    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | k2_relat_1(k8_relat_1(X2,k7_relat_1(X0,X1))) = k1_setfam_1(k2_enumset1(X2,X2,X2,k9_relat_1(X0,X1)))) )),
% 2.42/0.74    inference(subsumption_resolution,[],[f166,f52])).
% 2.42/0.74  fof(f166,plain,(
% 2.42/0.74    ( ! [X2,X0,X1] : (k2_relat_1(k8_relat_1(X2,k7_relat_1(X0,X1))) = k1_setfam_1(k2_enumset1(X2,X2,X2,k9_relat_1(X0,X1))) | ~v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 2.42/0.74    inference(superposition,[],[f117,f54])).
% 2.42/0.74  fof(f117,plain,(
% 2.42/0.74    ( ! [X0,X1] : (k2_relat_1(k8_relat_1(X1,X0)) = k1_setfam_1(k2_enumset1(X1,X1,X1,k2_relat_1(X0))) | ~v1_relat_1(X0)) )),
% 2.42/0.74    inference(superposition,[],[f71,f70])).
% 2.42/0.74  fof(f71,plain,(
% 2.42/0.74    ( ! [X0,X1] : (k2_relat_1(k8_relat_1(X0,X1)) = k1_setfam_1(k2_enumset1(k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 2.42/0.74    inference(definition_unfolding,[],[f55,f68])).
% 2.42/0.74  fof(f55,plain,(
% 2.42/0.74    ( ! [X0,X1] : (k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 2.42/0.74    inference(cnf_transformation,[],[f29])).
% 2.42/0.74  fof(f29,plain,(
% 2.42/0.74    ! [X0,X1] : (k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 2.42/0.74    inference(ennf_transformation,[],[f12])).
% 2.42/0.74  fof(f12,axiom,(
% 2.42/0.74    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0))),
% 2.42/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t119_relat_1)).
% 2.42/0.74  fof(f151,plain,(
% 2.42/0.74    ~r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(sK2,sK0),sK1)),k1_setfam_1(k2_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))))),
% 2.42/0.74    inference(backward_demodulation,[],[f69,f150])).
% 2.42/0.74  fof(f150,plain,(
% 2.42/0.74    ( ! [X12,X13] : (k9_relat_1(sK2,k1_setfam_1(k2_enumset1(X12,X12,X12,X13))) = k2_relat_1(k7_relat_1(k7_relat_1(sK2,X12),X13))) )),
% 2.42/0.74    inference(subsumption_resolution,[],[f143,f43])).
% 2.42/0.74  fof(f143,plain,(
% 2.42/0.74    ( ! [X12,X13] : (k9_relat_1(sK2,k1_setfam_1(k2_enumset1(X12,X12,X12,X13))) = k2_relat_1(k7_relat_1(k7_relat_1(sK2,X12),X13)) | ~v1_relat_1(sK2)) )),
% 2.42/0.74    inference(superposition,[],[f54,f129])).
% 2.42/0.74  fof(f69,plain,(
% 2.42/0.74    ~r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_setfam_1(k2_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))))),
% 2.42/0.74    inference(definition_unfolding,[],[f44,f68,f68])).
% 2.42/0.74  fof(f44,plain,(
% 2.42/0.74    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))),
% 2.42/0.74    inference(cnf_transformation,[],[f39])).
% 2.42/0.74  fof(f39,plain,(
% 2.42/0.74    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))) & v1_relat_1(sK2)),
% 2.42/0.74    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f38])).
% 2.42/0.74  fof(f38,plain,(
% 2.42/0.74    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) & v1_relat_1(X2)) => (~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))) & v1_relat_1(sK2))),
% 2.42/0.74    introduced(choice_axiom,[])).
% 2.42/0.74  fof(f21,plain,(
% 2.42/0.74    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) & v1_relat_1(X2))),
% 2.42/0.74    inference(ennf_transformation,[],[f20])).
% 2.42/0.74  fof(f20,negated_conjecture,(
% 2.42/0.74    ~! [X0,X1,X2] : (v1_relat_1(X2) => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 2.42/0.74    inference(negated_conjecture,[],[f19])).
% 2.42/0.74  fof(f19,conjecture,(
% 2.42/0.74    ! [X0,X1,X2] : (v1_relat_1(X2) => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 2.42/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t154_relat_1)).
% 2.42/0.74  fof(f43,plain,(
% 2.42/0.74    v1_relat_1(sK2)),
% 2.42/0.74    inference(cnf_transformation,[],[f39])).
% 2.42/0.74  % SZS output end Proof for theBenchmark
% 2.42/0.74  % (13445)------------------------------
% 2.42/0.74  % (13445)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.42/0.74  % (13445)Termination reason: Refutation
% 2.42/0.74  
% 2.42/0.74  % (13445)Memory used [KB]: 8443
% 2.42/0.74  % (13445)Time elapsed: 0.298 s
% 2.42/0.74  % (13445)------------------------------
% 2.42/0.74  % (13445)------------------------------
% 2.42/0.74  % (13422)Success in time 0.374 s
%------------------------------------------------------------------------------
