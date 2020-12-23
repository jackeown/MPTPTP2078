%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:08 EST 2020

% Result     : Theorem 2.06s
% Output     : Refutation 2.06s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 287 expanded)
%              Number of leaves         :   14 (  87 expanded)
%              Depth                    :   16
%              Number of atoms          :  106 ( 374 expanded)
%              Number of equality atoms :   48 ( 244 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2694,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2693,f60])).

fof(f60,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f2693,plain,(
    ~ r1_tarski(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK2)) ),
    inference(forward_demodulation,[],[f2692,f2566])).

fof(f2566,plain,(
    ! [X2,X1] : k5_xboole_0(X2,k5_xboole_0(X1,X2)) = X1 ),
    inference(forward_demodulation,[],[f2553,f50])).

fof(f50,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f2553,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k1_xboole_0) = k5_xboole_0(X2,k5_xboole_0(X1,X2)) ),
    inference(superposition,[],[f141,f135])).

fof(f135,plain,(
    ! [X6,X5] : k1_xboole_0 = k5_xboole_0(X5,k5_xboole_0(X6,k5_xboole_0(X5,X6))) ),
    inference(superposition,[],[f37,f51])).

fof(f51,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f37,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f141,plain,(
    ! [X2,X3] : k5_xboole_0(X2,k5_xboole_0(X2,X3)) = X3 ),
    inference(forward_demodulation,[],[f131,f67])).

fof(f67,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(backward_demodulation,[],[f66,f52])).

fof(f52,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f66,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,k2_xboole_0(X0,X0)) = X0 ),
    inference(backward_demodulation,[],[f56,f51])).

fof(f56,plain,(
    ! [X0] : k5_xboole_0(k5_xboole_0(X0,X0),k2_xboole_0(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f41,f43])).

fof(f43,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f41,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f131,plain,(
    ! [X2,X3] : k5_xboole_0(X2,k5_xboole_0(X2,X3)) = k5_xboole_0(k1_xboole_0,X3) ),
    inference(superposition,[],[f37,f51])).

fof(f2692,plain,(
    ~ r1_tarski(k2_zfmisc_1(sK0,k5_xboole_0(sK3,k5_xboole_0(sK2,sK3))),k2_zfmisc_1(sK0,sK2)) ),
    inference(forward_demodulation,[],[f2691,f2598])).

fof(f2598,plain,(
    sK3 = k2_xboole_0(sK3,sK2) ),
    inference(unit_resulting_resolution,[],[f49,f2353,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f2353,plain,(
    r1_tarski(k2_xboole_0(sK3,sK2),sK3) ),
    inference(superposition,[],[f213,f141])).

fof(f213,plain,(
    ! [X0] : r1_tarski(k5_xboole_0(sK2,k5_xboole_0(X0,k2_xboole_0(sK3,X0))),sK3) ),
    inference(unit_resulting_resolution,[],[f35,f142,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k5_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k5_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k5_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k5_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t110_xboole_1)).

fof(f142,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X1,k2_xboole_0(X0,X1)),X0) ),
    inference(backward_demodulation,[],[f68,f141])).

fof(f68,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k2_xboole_0(X0,X1)))),X0) ),
    inference(forward_demodulation,[],[f59,f37])).

fof(f59,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),X0) ),
    inference(definition_unfolding,[],[f53,f54])).

fof(f54,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f44,f43])).

fof(f44,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f53,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f35,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ? [X0,X1,X2,X3] :
      ( k2_zfmisc_1(X0,X2) != k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2))
      & r1_tarski(X2,X3)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ? [X0,X1,X2,X3] :
      ( k2_zfmisc_1(X0,X2) != k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2))
      & r1_tarski(X2,X3)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_tarski(X2,X3)
          & r1_tarski(X0,X1) )
       => k2_zfmisc_1(X0,X2) = k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2)) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f23,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => k2_zfmisc_1(X0,X2) = k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t124_zfmisc_1)).

fof(f49,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f2691,plain,(
    ~ r1_tarski(k2_zfmisc_1(sK0,k5_xboole_0(sK3,k5_xboole_0(sK2,k2_xboole_0(sK3,sK2)))),k2_zfmisc_1(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f2690,f60])).

fof(f2690,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK2))
    | ~ r1_tarski(k2_zfmisc_1(sK0,k5_xboole_0(sK3,k5_xboole_0(sK2,k2_xboole_0(sK3,sK2)))),k2_zfmisc_1(sK0,sK2)) ),
    inference(forward_demodulation,[],[f2663,f2566])).

fof(f2663,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,k5_xboole_0(sK3,k5_xboole_0(sK2,sK3))))
    | ~ r1_tarski(k2_zfmisc_1(sK0,k5_xboole_0(sK3,k5_xboole_0(sK2,k2_xboole_0(sK3,sK2)))),k2_zfmisc_1(sK0,sK2)) ),
    inference(backward_demodulation,[],[f292,f2598])).

fof(f292,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,k5_xboole_0(sK3,k5_xboole_0(sK2,k2_xboole_0(sK3,sK2)))),k2_zfmisc_1(sK0,sK2))
    | ~ r1_tarski(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,k5_xboole_0(sK3,k5_xboole_0(sK2,k2_xboole_0(sK3,sK2))))) ),
    inference(forward_demodulation,[],[f291,f290])).

fof(f290,plain,(
    ! [X8,X7] : k5_xboole_0(k2_zfmisc_1(sK0,X7),k5_xboole_0(k2_zfmisc_1(sK1,X8),k2_xboole_0(k2_zfmisc_1(sK0,X7),k2_zfmisc_1(sK1,X8)))) = k2_zfmisc_1(sK0,k5_xboole_0(X7,k5_xboole_0(X8,k2_xboole_0(X7,X8)))) ),
    inference(forward_demodulation,[],[f289,f50])).

fof(f289,plain,(
    ! [X8,X7] : k5_xboole_0(k2_zfmisc_1(sK0,X7),k5_xboole_0(k2_zfmisc_1(sK1,X8),k2_xboole_0(k2_zfmisc_1(sK0,X7),k2_zfmisc_1(sK1,X8)))) = k2_zfmisc_1(k5_xboole_0(sK0,k1_xboole_0),k5_xboole_0(X7,k5_xboole_0(X8,k2_xboole_0(X7,X8)))) ),
    inference(forward_demodulation,[],[f272,f51])).

fof(f272,plain,(
    ! [X8,X7] : k5_xboole_0(k2_zfmisc_1(sK0,X7),k5_xboole_0(k2_zfmisc_1(sK1,X8),k2_xboole_0(k2_zfmisc_1(sK0,X7),k2_zfmisc_1(sK1,X8)))) = k2_zfmisc_1(k5_xboole_0(sK0,k5_xboole_0(sK1,sK1)),k5_xboole_0(X7,k5_xboole_0(X8,k2_xboole_0(X7,X8)))) ),
    inference(superposition,[],[f64,f70])).

fof(f70,plain,(
    sK1 = k2_xboole_0(sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f34,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f34,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k2_zfmisc_1(X0,X2),k5_xboole_0(k2_zfmisc_1(X1,X3),k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))) = k2_zfmisc_1(k5_xboole_0(X0,k5_xboole_0(X1,k2_xboole_0(X0,X1))),k5_xboole_0(X2,k5_xboole_0(X3,k2_xboole_0(X2,X3)))) ),
    inference(forward_demodulation,[],[f63,f37])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k2_zfmisc_1(X0,X2),k5_xboole_0(k2_zfmisc_1(X1,X3),k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))) = k2_zfmisc_1(k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)),k5_xboole_0(X2,k5_xboole_0(X3,k2_xboole_0(X2,X3)))) ),
    inference(forward_demodulation,[],[f62,f37])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)),k5_xboole_0(k5_xboole_0(X2,X3),k2_xboole_0(X2,X3))) = k5_xboole_0(k2_zfmisc_1(X0,X2),k5_xboole_0(k2_zfmisc_1(X1,X3),k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))) ),
    inference(forward_demodulation,[],[f57,f37])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)),k5_xboole_0(k5_xboole_0(X2,X3),k2_xboole_0(X2,X3))) = k5_xboole_0(k5_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)),k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) ),
    inference(definition_unfolding,[],[f42,f43,f43,f43])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).

fof(f291,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,k5_xboole_0(sK3,k5_xboole_0(sK2,k2_xboole_0(sK3,sK2)))))
    | ~ r1_tarski(k5_xboole_0(k2_zfmisc_1(sK0,sK3),k5_xboole_0(k2_zfmisc_1(sK1,sK2),k2_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2)))),k2_zfmisc_1(sK0,sK2)) ),
    inference(backward_demodulation,[],[f124,f290])).

fof(f124,plain,
    ( ~ r1_tarski(k5_xboole_0(k2_zfmisc_1(sK0,sK3),k5_xboole_0(k2_zfmisc_1(sK1,sK2),k2_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2)))),k2_zfmisc_1(sK0,sK2))
    | ~ r1_tarski(k2_zfmisc_1(sK0,sK2),k5_xboole_0(k2_zfmisc_1(sK0,sK3),k5_xboole_0(k2_zfmisc_1(sK1,sK2),k2_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2))))) ),
    inference(forward_demodulation,[],[f123,f37])).

fof(f123,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK2),k5_xboole_0(k2_zfmisc_1(sK0,sK3),k5_xboole_0(k2_zfmisc_1(sK1,sK2),k2_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2)))))
    | ~ r1_tarski(k5_xboole_0(k5_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2)),k2_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2))),k2_zfmisc_1(sK0,sK2)) ),
    inference(forward_demodulation,[],[f120,f37])).

fof(f120,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK2),k5_xboole_0(k5_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2)),k2_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2))))
    | ~ r1_tarski(k5_xboole_0(k5_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2)),k2_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2))),k2_zfmisc_1(sK0,sK2)) ),
    inference(extensionality_resolution,[],[f40,f55])).

fof(f55,plain,(
    k2_zfmisc_1(sK0,sK2) != k5_xboole_0(k5_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2)),k2_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2))) ),
    inference(definition_unfolding,[],[f36,f43])).

fof(f36,plain,(
    k2_zfmisc_1(sK0,sK2) != k3_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:28:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.23/0.52  % (6108)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.23/0.52  % (6101)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.23/0.53  % (6092)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.23/0.53  % (6090)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.23/0.54  % (6088)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.23/0.54  % (6087)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.23/0.54  % (6113)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.23/0.54  % (6091)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.23/0.54  % (6089)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.23/0.54  % (6086)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.23/0.55  % (6093)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.23/0.55  % (6114)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.23/0.55  % (6112)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.23/0.55  % (6111)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.23/0.55  % (6103)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.23/0.55  % (6102)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.23/0.55  % (6105)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.23/0.56  % (6107)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.23/0.56  % (6106)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.23/0.56  % (6104)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.23/0.56  % (6094)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.23/0.56  % (6085)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.23/0.56  % (6097)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.23/0.56  % (6098)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.23/0.56  % (6096)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.23/0.56  % (6095)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.23/0.56  % (6110)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.23/0.57  % (6100)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.23/0.57  % (6099)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.23/0.57  % (6109)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 2.06/0.71  % (6104)Refutation found. Thanks to Tanya!
% 2.06/0.71  % SZS status Theorem for theBenchmark
% 2.06/0.71  % SZS output start Proof for theBenchmark
% 2.06/0.71  fof(f2694,plain,(
% 2.06/0.71    $false),
% 2.06/0.71    inference(subsumption_resolution,[],[f2693,f60])).
% 2.06/0.71  fof(f60,plain,(
% 2.06/0.71    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.06/0.71    inference(equality_resolution,[],[f39])).
% 2.06/0.71  fof(f39,plain,(
% 2.06/0.71    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.06/0.71    inference(cnf_transformation,[],[f3])).
% 2.06/0.71  fof(f3,axiom,(
% 2.06/0.71    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.06/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.06/0.71  fof(f2693,plain,(
% 2.06/0.71    ~r1_tarski(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK2))),
% 2.06/0.71    inference(forward_demodulation,[],[f2692,f2566])).
% 2.06/0.71  fof(f2566,plain,(
% 2.06/0.71    ( ! [X2,X1] : (k5_xboole_0(X2,k5_xboole_0(X1,X2)) = X1) )),
% 2.06/0.71    inference(forward_demodulation,[],[f2553,f50])).
% 2.06/0.71  fof(f50,plain,(
% 2.06/0.71    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.06/0.71    inference(cnf_transformation,[],[f10])).
% 2.06/0.71  fof(f10,axiom,(
% 2.06/0.71    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 2.06/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 2.06/0.71  fof(f2553,plain,(
% 2.06/0.71    ( ! [X2,X1] : (k5_xboole_0(X1,k1_xboole_0) = k5_xboole_0(X2,k5_xboole_0(X1,X2))) )),
% 2.06/0.71    inference(superposition,[],[f141,f135])).
% 2.06/0.71  fof(f135,plain,(
% 2.06/0.71    ( ! [X6,X5] : (k1_xboole_0 = k5_xboole_0(X5,k5_xboole_0(X6,k5_xboole_0(X5,X6)))) )),
% 2.06/0.71    inference(superposition,[],[f37,f51])).
% 2.06/0.71  fof(f51,plain,(
% 2.06/0.71    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 2.06/0.71    inference(cnf_transformation,[],[f13])).
% 2.06/0.71  fof(f13,axiom,(
% 2.06/0.71    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 2.06/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 2.06/0.71  fof(f37,plain,(
% 2.06/0.71    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 2.06/0.71    inference(cnf_transformation,[],[f12])).
% 2.06/0.71  fof(f12,axiom,(
% 2.06/0.71    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 2.06/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 2.06/0.71  fof(f141,plain,(
% 2.06/0.71    ( ! [X2,X3] : (k5_xboole_0(X2,k5_xboole_0(X2,X3)) = X3) )),
% 2.06/0.71    inference(forward_demodulation,[],[f131,f67])).
% 2.06/0.71  fof(f67,plain,(
% 2.06/0.71    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 2.06/0.71    inference(backward_demodulation,[],[f66,f52])).
% 2.06/0.71  fof(f52,plain,(
% 2.06/0.71    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 2.06/0.71    inference(cnf_transformation,[],[f26])).
% 2.06/0.71  fof(f26,plain,(
% 2.06/0.71    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 2.06/0.71    inference(rectify,[],[f1])).
% 2.06/0.71  fof(f1,axiom,(
% 2.06/0.71    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 2.06/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 2.06/0.71  fof(f66,plain,(
% 2.06/0.71    ( ! [X0] : (k5_xboole_0(k1_xboole_0,k2_xboole_0(X0,X0)) = X0) )),
% 2.06/0.71    inference(backward_demodulation,[],[f56,f51])).
% 2.06/0.71  fof(f56,plain,(
% 2.06/0.71    ( ! [X0] : (k5_xboole_0(k5_xboole_0(X0,X0),k2_xboole_0(X0,X0)) = X0) )),
% 2.06/0.71    inference(definition_unfolding,[],[f41,f43])).
% 2.06/0.71  fof(f43,plain,(
% 2.06/0.71    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 2.06/0.71    inference(cnf_transformation,[],[f14])).
% 2.06/0.71  fof(f14,axiom,(
% 2.06/0.71    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 2.06/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).
% 2.06/0.71  fof(f41,plain,(
% 2.06/0.71    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 2.06/0.71    inference(cnf_transformation,[],[f25])).
% 2.06/0.71  fof(f25,plain,(
% 2.06/0.71    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 2.06/0.71    inference(rectify,[],[f2])).
% 2.06/0.71  fof(f2,axiom,(
% 2.06/0.71    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 2.06/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 2.06/0.71  fof(f131,plain,(
% 2.06/0.71    ( ! [X2,X3] : (k5_xboole_0(X2,k5_xboole_0(X2,X3)) = k5_xboole_0(k1_xboole_0,X3)) )),
% 2.06/0.71    inference(superposition,[],[f37,f51])).
% 2.06/0.71  fof(f2692,plain,(
% 2.06/0.71    ~r1_tarski(k2_zfmisc_1(sK0,k5_xboole_0(sK3,k5_xboole_0(sK2,sK3))),k2_zfmisc_1(sK0,sK2))),
% 2.06/0.71    inference(forward_demodulation,[],[f2691,f2598])).
% 2.06/0.71  fof(f2598,plain,(
% 2.06/0.71    sK3 = k2_xboole_0(sK3,sK2)),
% 2.06/0.71    inference(unit_resulting_resolution,[],[f49,f2353,f40])).
% 2.06/0.71  fof(f40,plain,(
% 2.06/0.71    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 2.06/0.71    inference(cnf_transformation,[],[f3])).
% 2.06/0.71  fof(f2353,plain,(
% 2.06/0.71    r1_tarski(k2_xboole_0(sK3,sK2),sK3)),
% 2.06/0.71    inference(superposition,[],[f213,f141])).
% 2.06/0.71  fof(f213,plain,(
% 2.06/0.71    ( ! [X0] : (r1_tarski(k5_xboole_0(sK2,k5_xboole_0(X0,k2_xboole_0(sK3,X0))),sK3)) )),
% 2.06/0.71    inference(unit_resulting_resolution,[],[f35,f142,f46])).
% 2.06/0.71  fof(f46,plain,(
% 2.06/0.71    ( ! [X2,X0,X1] : (r1_tarski(k5_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 2.06/0.71    inference(cnf_transformation,[],[f30])).
% 2.06/0.71  fof(f30,plain,(
% 2.06/0.71    ! [X0,X1,X2] : (r1_tarski(k5_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 2.06/0.71    inference(flattening,[],[f29])).
% 2.06/0.71  fof(f29,plain,(
% 2.06/0.71    ! [X0,X1,X2] : (r1_tarski(k5_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 2.06/0.71    inference(ennf_transformation,[],[f5])).
% 2.06/0.71  fof(f5,axiom,(
% 2.06/0.71    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k5_xboole_0(X0,X2),X1))),
% 2.06/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t110_xboole_1)).
% 2.06/0.71  fof(f142,plain,(
% 2.06/0.71    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X1,k2_xboole_0(X0,X1)),X0)) )),
% 2.06/0.71    inference(backward_demodulation,[],[f68,f141])).
% 2.06/0.71  fof(f68,plain,(
% 2.06/0.71    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k2_xboole_0(X0,X1)))),X0)) )),
% 2.06/0.71    inference(forward_demodulation,[],[f59,f37])).
% 2.06/0.71  fof(f59,plain,(
% 2.06/0.71    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),X0)) )),
% 2.06/0.71    inference(definition_unfolding,[],[f53,f54])).
% 2.06/0.71  fof(f54,plain,(
% 2.06/0.71    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)))) )),
% 2.06/0.71    inference(definition_unfolding,[],[f44,f43])).
% 2.06/0.71  fof(f44,plain,(
% 2.06/0.71    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.06/0.71    inference(cnf_transformation,[],[f4])).
% 2.06/0.71  fof(f4,axiom,(
% 2.06/0.71    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.06/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.06/0.71  fof(f53,plain,(
% 2.06/0.71    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 2.06/0.71    inference(cnf_transformation,[],[f9])).
% 2.06/0.71  fof(f9,axiom,(
% 2.06/0.71    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 2.06/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 2.06/0.71  fof(f35,plain,(
% 2.06/0.71    r1_tarski(sK2,sK3)),
% 2.06/0.71    inference(cnf_transformation,[],[f28])).
% 2.06/0.71  fof(f28,plain,(
% 2.06/0.71    ? [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X2) != k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2)) & r1_tarski(X2,X3) & r1_tarski(X0,X1))),
% 2.06/0.71    inference(flattening,[],[f27])).
% 2.06/0.71  fof(f27,plain,(
% 2.06/0.71    ? [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X2) != k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2)) & (r1_tarski(X2,X3) & r1_tarski(X0,X1)))),
% 2.06/0.71    inference(ennf_transformation,[],[f24])).
% 2.06/0.71  fof(f24,negated_conjecture,(
% 2.06/0.71    ~! [X0,X1,X2,X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => k2_zfmisc_1(X0,X2) = k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2)))),
% 2.06/0.71    inference(negated_conjecture,[],[f23])).
% 2.06/0.71  fof(f23,conjecture,(
% 2.06/0.71    ! [X0,X1,X2,X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => k2_zfmisc_1(X0,X2) = k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2)))),
% 2.06/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t124_zfmisc_1)).
% 2.06/0.71  fof(f49,plain,(
% 2.06/0.71    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 2.06/0.71    inference(cnf_transformation,[],[f11])).
% 2.06/0.71  fof(f11,axiom,(
% 2.06/0.71    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 2.06/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 2.06/0.71  fof(f2691,plain,(
% 2.06/0.71    ~r1_tarski(k2_zfmisc_1(sK0,k5_xboole_0(sK3,k5_xboole_0(sK2,k2_xboole_0(sK3,sK2)))),k2_zfmisc_1(sK0,sK2))),
% 2.06/0.71    inference(subsumption_resolution,[],[f2690,f60])).
% 2.06/0.71  fof(f2690,plain,(
% 2.06/0.71    ~r1_tarski(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK2)) | ~r1_tarski(k2_zfmisc_1(sK0,k5_xboole_0(sK3,k5_xboole_0(sK2,k2_xboole_0(sK3,sK2)))),k2_zfmisc_1(sK0,sK2))),
% 2.06/0.71    inference(forward_demodulation,[],[f2663,f2566])).
% 2.06/0.71  fof(f2663,plain,(
% 2.06/0.71    ~r1_tarski(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,k5_xboole_0(sK3,k5_xboole_0(sK2,sK3)))) | ~r1_tarski(k2_zfmisc_1(sK0,k5_xboole_0(sK3,k5_xboole_0(sK2,k2_xboole_0(sK3,sK2)))),k2_zfmisc_1(sK0,sK2))),
% 2.06/0.71    inference(backward_demodulation,[],[f292,f2598])).
% 2.06/0.71  fof(f292,plain,(
% 2.06/0.71    ~r1_tarski(k2_zfmisc_1(sK0,k5_xboole_0(sK3,k5_xboole_0(sK2,k2_xboole_0(sK3,sK2)))),k2_zfmisc_1(sK0,sK2)) | ~r1_tarski(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,k5_xboole_0(sK3,k5_xboole_0(sK2,k2_xboole_0(sK3,sK2)))))),
% 2.06/0.71    inference(forward_demodulation,[],[f291,f290])).
% 2.06/0.71  fof(f290,plain,(
% 2.06/0.71    ( ! [X8,X7] : (k5_xboole_0(k2_zfmisc_1(sK0,X7),k5_xboole_0(k2_zfmisc_1(sK1,X8),k2_xboole_0(k2_zfmisc_1(sK0,X7),k2_zfmisc_1(sK1,X8)))) = k2_zfmisc_1(sK0,k5_xboole_0(X7,k5_xboole_0(X8,k2_xboole_0(X7,X8))))) )),
% 2.06/0.71    inference(forward_demodulation,[],[f289,f50])).
% 2.06/0.71  fof(f289,plain,(
% 2.06/0.71    ( ! [X8,X7] : (k5_xboole_0(k2_zfmisc_1(sK0,X7),k5_xboole_0(k2_zfmisc_1(sK1,X8),k2_xboole_0(k2_zfmisc_1(sK0,X7),k2_zfmisc_1(sK1,X8)))) = k2_zfmisc_1(k5_xboole_0(sK0,k1_xboole_0),k5_xboole_0(X7,k5_xboole_0(X8,k2_xboole_0(X7,X8))))) )),
% 2.06/0.71    inference(forward_demodulation,[],[f272,f51])).
% 2.06/0.71  fof(f272,plain,(
% 2.06/0.71    ( ! [X8,X7] : (k5_xboole_0(k2_zfmisc_1(sK0,X7),k5_xboole_0(k2_zfmisc_1(sK1,X8),k2_xboole_0(k2_zfmisc_1(sK0,X7),k2_zfmisc_1(sK1,X8)))) = k2_zfmisc_1(k5_xboole_0(sK0,k5_xboole_0(sK1,sK1)),k5_xboole_0(X7,k5_xboole_0(X8,k2_xboole_0(X7,X8))))) )),
% 2.06/0.71    inference(superposition,[],[f64,f70])).
% 2.06/0.71  fof(f70,plain,(
% 2.06/0.71    sK1 = k2_xboole_0(sK0,sK1)),
% 2.06/0.71    inference(unit_resulting_resolution,[],[f34,f48])).
% 2.06/0.71  fof(f48,plain,(
% 2.06/0.71    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 2.06/0.71    inference(cnf_transformation,[],[f33])).
% 2.06/0.71  fof(f33,plain,(
% 2.06/0.71    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 2.06/0.71    inference(ennf_transformation,[],[f6])).
% 2.06/0.71  fof(f6,axiom,(
% 2.06/0.71    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 2.06/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 2.06/0.71  fof(f34,plain,(
% 2.06/0.71    r1_tarski(sK0,sK1)),
% 2.06/0.71    inference(cnf_transformation,[],[f28])).
% 2.06/0.71  fof(f64,plain,(
% 2.06/0.71    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k2_zfmisc_1(X0,X2),k5_xboole_0(k2_zfmisc_1(X1,X3),k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))) = k2_zfmisc_1(k5_xboole_0(X0,k5_xboole_0(X1,k2_xboole_0(X0,X1))),k5_xboole_0(X2,k5_xboole_0(X3,k2_xboole_0(X2,X3))))) )),
% 2.06/0.71    inference(forward_demodulation,[],[f63,f37])).
% 2.06/0.71  fof(f63,plain,(
% 2.06/0.71    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k2_zfmisc_1(X0,X2),k5_xboole_0(k2_zfmisc_1(X1,X3),k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))) = k2_zfmisc_1(k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)),k5_xboole_0(X2,k5_xboole_0(X3,k2_xboole_0(X2,X3))))) )),
% 2.06/0.71    inference(forward_demodulation,[],[f62,f37])).
% 2.06/0.71  fof(f62,plain,(
% 2.06/0.71    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)),k5_xboole_0(k5_xboole_0(X2,X3),k2_xboole_0(X2,X3))) = k5_xboole_0(k2_zfmisc_1(X0,X2),k5_xboole_0(k2_zfmisc_1(X1,X3),k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))))) )),
% 2.06/0.71    inference(forward_demodulation,[],[f57,f37])).
% 2.06/0.71  fof(f57,plain,(
% 2.06/0.71    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)),k5_xboole_0(k5_xboole_0(X2,X3),k2_xboole_0(X2,X3))) = k5_xboole_0(k5_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)),k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))) )),
% 2.06/0.71    inference(definition_unfolding,[],[f42,f43,f43,f43])).
% 2.06/0.71  fof(f42,plain,(
% 2.06/0.71    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) )),
% 2.06/0.71    inference(cnf_transformation,[],[f22])).
% 2.06/0.71  fof(f22,axiom,(
% 2.06/0.71    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))),
% 2.06/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).
% 2.06/0.71  fof(f291,plain,(
% 2.06/0.71    ~r1_tarski(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,k5_xboole_0(sK3,k5_xboole_0(sK2,k2_xboole_0(sK3,sK2))))) | ~r1_tarski(k5_xboole_0(k2_zfmisc_1(sK0,sK3),k5_xboole_0(k2_zfmisc_1(sK1,sK2),k2_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2)))),k2_zfmisc_1(sK0,sK2))),
% 2.06/0.71    inference(backward_demodulation,[],[f124,f290])).
% 2.06/0.71  fof(f124,plain,(
% 2.06/0.71    ~r1_tarski(k5_xboole_0(k2_zfmisc_1(sK0,sK3),k5_xboole_0(k2_zfmisc_1(sK1,sK2),k2_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2)))),k2_zfmisc_1(sK0,sK2)) | ~r1_tarski(k2_zfmisc_1(sK0,sK2),k5_xboole_0(k2_zfmisc_1(sK0,sK3),k5_xboole_0(k2_zfmisc_1(sK1,sK2),k2_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2)))))),
% 2.06/0.71    inference(forward_demodulation,[],[f123,f37])).
% 2.06/0.71  fof(f123,plain,(
% 2.06/0.71    ~r1_tarski(k2_zfmisc_1(sK0,sK2),k5_xboole_0(k2_zfmisc_1(sK0,sK3),k5_xboole_0(k2_zfmisc_1(sK1,sK2),k2_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2))))) | ~r1_tarski(k5_xboole_0(k5_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2)),k2_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2))),k2_zfmisc_1(sK0,sK2))),
% 2.06/0.71    inference(forward_demodulation,[],[f120,f37])).
% 2.06/0.71  fof(f120,plain,(
% 2.06/0.71    ~r1_tarski(k2_zfmisc_1(sK0,sK2),k5_xboole_0(k5_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2)),k2_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2)))) | ~r1_tarski(k5_xboole_0(k5_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2)),k2_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2))),k2_zfmisc_1(sK0,sK2))),
% 2.06/0.71    inference(extensionality_resolution,[],[f40,f55])).
% 2.06/0.71  fof(f55,plain,(
% 2.06/0.71    k2_zfmisc_1(sK0,sK2) != k5_xboole_0(k5_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2)),k2_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2)))),
% 2.06/0.71    inference(definition_unfolding,[],[f36,f43])).
% 2.06/0.71  fof(f36,plain,(
% 2.06/0.71    k2_zfmisc_1(sK0,sK2) != k3_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2))),
% 2.06/0.71    inference(cnf_transformation,[],[f28])).
% 2.06/0.71  % SZS output end Proof for theBenchmark
% 2.06/0.71  % (6104)------------------------------
% 2.06/0.71  % (6104)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.06/0.71  % (6104)Termination reason: Refutation
% 2.06/0.71  
% 2.06/0.71  % (6104)Memory used [KB]: 3070
% 2.06/0.71  % (6104)Time elapsed: 0.293 s
% 2.06/0.71  % (6104)------------------------------
% 2.06/0.71  % (6104)------------------------------
% 2.06/0.72  % (6084)Success in time 0.344 s
%------------------------------------------------------------------------------
