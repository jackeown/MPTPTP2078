%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:51 EST 2020

% Result     : Theorem 2.36s
% Output     : Refutation 2.36s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 323 expanded)
%              Number of leaves         :   15 (  92 expanded)
%              Depth                    :   21
%              Number of atoms          :  130 ( 486 expanded)
%              Number of equality atoms :   74 ( 276 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2013,plain,(
    $false ),
    inference(global_subsumption,[],[f28,f2012])).

fof(f2012,plain,(
    sK1 = sK2 ),
    inference(backward_demodulation,[],[f1264,f2010])).

fof(f2010,plain,(
    sK1 = k2_xboole_0(sK2,sK1) ),
    inference(backward_demodulation,[],[f1910,f1911])).

fof(f1911,plain,(
    sK2 = k4_xboole_0(sK2,sK0) ),
    inference(backward_demodulation,[],[f298,f1818])).

fof(f1818,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f1776,f151])).

fof(f151,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(unit_resulting_resolution,[],[f147,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f147,plain,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    inference(forward_demodulation,[],[f126,f56])).

fof(f56,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f31,f29])).

fof(f29,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f31,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f126,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X0),X1) ),
    inference(unit_resulting_resolution,[],[f30,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
      | r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f30,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f1776,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = k2_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f531,f56])).

fof(f531,plain,(
    ! [X4,X3] : k4_xboole_0(X3,k1_xboole_0) = k2_xboole_0(k4_xboole_0(X3,X4),X3) ),
    inference(forward_demodulation,[],[f491,f56])).

fof(f491,plain,(
    ! [X4,X3] : k2_xboole_0(k4_xboole_0(X3,X4),X3) = k4_xboole_0(X3,k4_xboole_0(X4,X4)) ),
    inference(superposition,[],[f51,f36])).

fof(f36,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f51,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) ),
    inference(definition_unfolding,[],[f42,f34])).

fof(f34,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f42,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).

fof(f298,plain,(
    k4_xboole_0(sK2,k1_xboole_0) = k4_xboole_0(sK2,sK0) ),
    inference(superposition,[],[f46,f158])).

fof(f158,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) ),
    inference(unit_resulting_resolution,[],[f26,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f39,f34])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f26,plain,(
    r1_xboole_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X3,X1)
          & r1_xboole_0(X2,X0)
          & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
       => X1 = X2 ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X3,X1)
        & r1_xboole_0(X2,X0)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_xboole_1)).

fof(f46,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f35,f34])).

fof(f35,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f1910,plain,(
    sK1 = k2_xboole_0(k4_xboole_0(sK2,sK0),sK1) ),
    inference(backward_demodulation,[],[f217,f1818])).

fof(f217,plain,(
    sK1 = k2_xboole_0(k4_xboole_0(k4_xboole_0(sK2,k1_xboole_0),sK0),sK1) ),
    inference(unit_resulting_resolution,[],[f188,f37])).

fof(f188,plain,(
    r1_tarski(k4_xboole_0(k4_xboole_0(sK2,k1_xboole_0),sK0),sK1) ),
    inference(unit_resulting_resolution,[],[f120,f43])).

fof(f120,plain,(
    r1_tarski(k4_xboole_0(sK2,k1_xboole_0),k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f105,f56])).

fof(f105,plain,(
    ! [X0] : r1_tarski(k4_xboole_0(sK2,k4_xboole_0(sK2,X0)),k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f49,f25])).

fof(f25,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f20])).

fof(f49,plain,(
    ! [X2,X0,X1] : r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k2_xboole_0(X0,X2)) ),
    inference(definition_unfolding,[],[f40,f34])).

fof(f40,plain,(
    ! [X2,X0,X1] : r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_xboole_1)).

fof(f1264,plain,(
    sK2 = k2_xboole_0(sK2,sK1) ),
    inference(forward_demodulation,[],[f1263,f151])).

fof(f1263,plain,(
    k2_xboole_0(sK2,sK1) = k2_xboole_0(k1_xboole_0,sK2) ),
    inference(forward_demodulation,[],[f1252,f33])).

fof(f33,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f1252,plain,(
    k2_xboole_0(sK2,sK1) = k2_xboole_0(sK2,k1_xboole_0) ),
    inference(superposition,[],[f36,f1196])).

fof(f1196,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,sK2) ),
    inference(unit_resulting_resolution,[],[f564,f54,f1173,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1)
      | ~ r1_xboole_0(X1,X2)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_xboole_1)).

fof(f1173,plain,(
    r1_xboole_0(k4_xboole_0(sK1,sK2),sK3) ),
    inference(trivial_inequality_removal,[],[f1168])).

fof(f1168,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(k4_xboole_0(sK1,sK2),sK3) ),
    inference(backward_demodulation,[],[f702,f1167])).

fof(f1167,plain,(
    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK1,sK2),k1_xboole_0) ),
    inference(forward_demodulation,[],[f1166,f1025])).

fof(f1025,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(unit_resulting_resolution,[],[f147,f76])).

fof(f76,plain,(
    ! [X8,X7] :
      ( k1_xboole_0 = k4_xboole_0(X7,X8)
      | ~ r1_tarski(X7,X8) ) ),
    inference(superposition,[],[f31,f37])).

fof(f1166,plain,(
    k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,sK3)) = k4_xboole_0(k4_xboole_0(sK1,sK2),k1_xboole_0) ),
    inference(forward_demodulation,[],[f1165,f45])).

fof(f45,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f32,f34,f34])).

fof(f32,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f1165,plain,(
    k4_xboole_0(sK3,k4_xboole_0(sK3,k1_xboole_0)) = k4_xboole_0(k4_xboole_0(sK1,sK2),k1_xboole_0) ),
    inference(backward_demodulation,[],[f709,f1025])).

fof(f709,plain,(
    k4_xboole_0(k4_xboole_0(sK1,sK2),k1_xboole_0) = k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(k1_xboole_0,sK2))) ),
    inference(forward_demodulation,[],[f698,f513])).

fof(f513,plain,(
    ! [X20] : k4_xboole_0(sK3,k4_xboole_0(sK1,X20)) = k4_xboole_0(sK3,k4_xboole_0(k1_xboole_0,X20)) ),
    inference(forward_demodulation,[],[f470,f51])).

fof(f470,plain,(
    ! [X20] : k4_xboole_0(sK3,k4_xboole_0(sK1,X20)) = k2_xboole_0(k4_xboole_0(sK3,k1_xboole_0),k4_xboole_0(sK3,k4_xboole_0(sK3,X20))) ),
    inference(superposition,[],[f51,f299])).

fof(f299,plain,(
    k4_xboole_0(sK3,sK1) = k4_xboole_0(sK3,k1_xboole_0) ),
    inference(superposition,[],[f46,f159])).

fof(f159,plain,(
    k1_xboole_0 = k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)) ),
    inference(unit_resulting_resolution,[],[f27,f47])).

fof(f27,plain,(
    r1_xboole_0(sK3,sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f698,plain,(
    k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(sK1,sK2))) = k4_xboole_0(k4_xboole_0(sK1,sK2),k1_xboole_0) ),
    inference(superposition,[],[f45,f623])).

fof(f623,plain,(
    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK1,sK2),sK3) ),
    inference(superposition,[],[f31,f591])).

fof(f591,plain,(
    sK3 = k2_xboole_0(k4_xboole_0(sK1,sK2),sK3) ),
    inference(unit_resulting_resolution,[],[f564,f37])).

fof(f702,plain,
    ( k1_xboole_0 != k4_xboole_0(k4_xboole_0(sK1,sK2),k1_xboole_0)
    | r1_xboole_0(k4_xboole_0(sK1,sK2),sK3) ),
    inference(superposition,[],[f48,f623])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f38,f34])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f54,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(superposition,[],[f30,f29])).

fof(f564,plain,(
    r1_tarski(k4_xboole_0(sK1,sK2),sK3) ),
    inference(unit_resulting_resolution,[],[f58,f140])).

fof(f140,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k2_xboole_0(sK0,sK1))
      | r1_tarski(k4_xboole_0(X0,sK2),sK3) ) ),
    inference(superposition,[],[f43,f25])).

fof(f58,plain,(
    ! [X4,X3] : r1_tarski(X3,k2_xboole_0(X4,X3)) ),
    inference(superposition,[],[f30,f33])).

fof(f28,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:03:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.49  % (1663)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.51  % (1669)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.51  % (1660)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (1656)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.52  % (1666)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.52  % (1666)Refutation not found, incomplete strategy% (1666)------------------------------
% 0.21/0.52  % (1666)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (1666)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (1666)Memory used [KB]: 10618
% 0.21/0.52  % (1666)Time elapsed: 0.096 s
% 0.21/0.52  % (1666)------------------------------
% 0.21/0.52  % (1666)------------------------------
% 0.21/0.52  % (1676)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.52  % (1661)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (1667)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.52  % (1655)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.52  % (1667)Refutation not found, incomplete strategy% (1667)------------------------------
% 0.21/0.52  % (1667)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (1674)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.53  % (1678)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.53  % (1665)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.53  % (1679)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.53  % (1658)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (1677)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.53  % (1659)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.53  % (1685)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.34/0.54  % (1664)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.34/0.54  % (1668)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.34/0.54  % (1684)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.34/0.54  % (1673)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.34/0.54  % (1673)Refutation not found, incomplete strategy% (1673)------------------------------
% 1.34/0.54  % (1673)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.54  % (1673)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.54  
% 1.34/0.54  % (1673)Memory used [KB]: 10618
% 1.34/0.54  % (1673)Time elapsed: 0.133 s
% 1.34/0.54  % (1673)------------------------------
% 1.34/0.54  % (1673)------------------------------
% 1.34/0.54  % (1657)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.34/0.54  % (1675)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.34/0.54  % (1671)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.34/0.54  % (1681)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.34/0.55  % (1672)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.34/0.55  % (1667)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.55  
% 1.34/0.55  % (1667)Memory used [KB]: 10618
% 1.34/0.55  % (1667)Time elapsed: 0.124 s
% 1.34/0.55  % (1667)------------------------------
% 1.34/0.55  % (1667)------------------------------
% 1.34/0.55  % (1670)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.34/0.55  % (1682)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.48/0.55  % (1680)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.48/0.55  % (1683)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 2.36/0.67  % (1686)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.36/0.69  % (1687)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.36/0.70  % (1680)Refutation found. Thanks to Tanya!
% 2.36/0.70  % SZS status Theorem for theBenchmark
% 2.36/0.70  % SZS output start Proof for theBenchmark
% 2.36/0.70  fof(f2013,plain,(
% 2.36/0.70    $false),
% 2.36/0.70    inference(global_subsumption,[],[f28,f2012])).
% 2.36/0.70  fof(f2012,plain,(
% 2.36/0.70    sK1 = sK2),
% 2.36/0.70    inference(backward_demodulation,[],[f1264,f2010])).
% 2.36/0.70  fof(f2010,plain,(
% 2.36/0.70    sK1 = k2_xboole_0(sK2,sK1)),
% 2.36/0.70    inference(backward_demodulation,[],[f1910,f1911])).
% 2.36/0.70  fof(f1911,plain,(
% 2.36/0.70    sK2 = k4_xboole_0(sK2,sK0)),
% 2.36/0.70    inference(backward_demodulation,[],[f298,f1818])).
% 2.36/0.70  fof(f1818,plain,(
% 2.36/0.70    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.36/0.70    inference(forward_demodulation,[],[f1776,f151])).
% 2.36/0.70  fof(f151,plain,(
% 2.36/0.70    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 2.36/0.70    inference(unit_resulting_resolution,[],[f147,f37])).
% 2.36/0.70  fof(f37,plain,(
% 2.36/0.70    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 2.36/0.70    inference(cnf_transformation,[],[f21])).
% 2.36/0.70  fof(f21,plain,(
% 2.36/0.70    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 2.36/0.70    inference(ennf_transformation,[],[f5])).
% 2.36/0.70  fof(f5,axiom,(
% 2.36/0.70    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 2.36/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 2.36/0.70  fof(f147,plain,(
% 2.36/0.70    ( ! [X1] : (r1_tarski(k1_xboole_0,X1)) )),
% 2.36/0.70    inference(forward_demodulation,[],[f126,f56])).
% 2.36/0.70  fof(f56,plain,(
% 2.36/0.70    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 2.36/0.70    inference(superposition,[],[f31,f29])).
% 2.36/0.70  fof(f29,plain,(
% 2.36/0.70    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 2.36/0.70    inference(cnf_transformation,[],[f18])).
% 2.36/0.70  fof(f18,plain,(
% 2.36/0.70    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 2.36/0.70    inference(rectify,[],[f4])).
% 2.36/0.70  fof(f4,axiom,(
% 2.36/0.70    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 2.36/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 2.36/0.70  fof(f31,plain,(
% 2.36/0.70    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 2.36/0.70    inference(cnf_transformation,[],[f10])).
% 2.36/0.70  fof(f10,axiom,(
% 2.36/0.70    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 2.36/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).
% 2.36/0.70  fof(f126,plain,(
% 2.36/0.70    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X0),X1)) )),
% 2.36/0.70    inference(unit_resulting_resolution,[],[f30,f43])).
% 2.36/0.70  fof(f43,plain,(
% 2.36/0.70    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_xboole_0(X1,X2)) | r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 2.36/0.70    inference(cnf_transformation,[],[f22])).
% 2.36/0.70  fof(f22,plain,(
% 2.36/0.70    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 2.36/0.70    inference(ennf_transformation,[],[f9])).
% 2.36/0.70  fof(f9,axiom,(
% 2.36/0.70    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 2.36/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).
% 2.36/0.70  fof(f30,plain,(
% 2.36/0.70    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 2.36/0.70    inference(cnf_transformation,[],[f15])).
% 2.36/0.70  fof(f15,axiom,(
% 2.36/0.70    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 2.36/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 2.36/0.70  fof(f1776,plain,(
% 2.36/0.70    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = k2_xboole_0(k1_xboole_0,X0)) )),
% 2.36/0.70    inference(superposition,[],[f531,f56])).
% 2.36/0.70  fof(f531,plain,(
% 2.36/0.70    ( ! [X4,X3] : (k4_xboole_0(X3,k1_xboole_0) = k2_xboole_0(k4_xboole_0(X3,X4),X3)) )),
% 2.36/0.70    inference(forward_demodulation,[],[f491,f56])).
% 2.36/0.70  fof(f491,plain,(
% 2.36/0.70    ( ! [X4,X3] : (k2_xboole_0(k4_xboole_0(X3,X4),X3) = k4_xboole_0(X3,k4_xboole_0(X4,X4))) )),
% 2.36/0.70    inference(superposition,[],[f51,f36])).
% 2.36/0.70  fof(f36,plain,(
% 2.36/0.70    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.36/0.70    inference(cnf_transformation,[],[f8])).
% 2.36/0.70  fof(f8,axiom,(
% 2.36/0.70    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.36/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 2.36/0.70  fof(f51,plain,(
% 2.36/0.70    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2)))) )),
% 2.36/0.70    inference(definition_unfolding,[],[f42,f34])).
% 2.36/0.70  fof(f34,plain,(
% 2.36/0.70    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.36/0.70    inference(cnf_transformation,[],[f12])).
% 2.36/0.70  fof(f12,axiom,(
% 2.36/0.70    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.36/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.36/0.70  fof(f42,plain,(
% 2.36/0.70    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 2.36/0.70    inference(cnf_transformation,[],[f13])).
% 2.36/0.70  fof(f13,axiom,(
% 2.36/0.70    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 2.36/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).
% 2.36/0.70  fof(f298,plain,(
% 2.36/0.70    k4_xboole_0(sK2,k1_xboole_0) = k4_xboole_0(sK2,sK0)),
% 2.36/0.70    inference(superposition,[],[f46,f158])).
% 2.36/0.70  fof(f158,plain,(
% 2.36/0.70    k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0))),
% 2.36/0.70    inference(unit_resulting_resolution,[],[f26,f47])).
% 2.36/0.70  fof(f47,plain,(
% 2.36/0.70    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 2.36/0.70    inference(definition_unfolding,[],[f39,f34])).
% 2.36/0.70  fof(f39,plain,(
% 2.36/0.70    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 2.36/0.70    inference(cnf_transformation,[],[f3])).
% 2.36/0.70  fof(f3,axiom,(
% 2.36/0.70    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 2.36/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 2.36/0.70  fof(f26,plain,(
% 2.36/0.70    r1_xboole_0(sK2,sK0)),
% 2.36/0.70    inference(cnf_transformation,[],[f20])).
% 2.36/0.70  fof(f20,plain,(
% 2.36/0.70    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3))),
% 2.36/0.70    inference(flattening,[],[f19])).
% 2.36/0.70  fof(f19,plain,(
% 2.36/0.70    ? [X0,X1,X2,X3] : (X1 != X2 & (r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)))),
% 2.36/0.70    inference(ennf_transformation,[],[f17])).
% 2.36/0.70  fof(f17,negated_conjecture,(
% 2.36/0.70    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 2.36/0.70    inference(negated_conjecture,[],[f16])).
% 2.36/0.70  fof(f16,conjecture,(
% 2.36/0.70    ! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 2.36/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_xboole_1)).
% 2.36/0.70  fof(f46,plain,(
% 2.36/0.70    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 2.36/0.70    inference(definition_unfolding,[],[f35,f34])).
% 2.36/0.70  fof(f35,plain,(
% 2.36/0.70    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.36/0.70    inference(cnf_transformation,[],[f11])).
% 2.36/0.70  fof(f11,axiom,(
% 2.36/0.70    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.36/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).
% 2.36/0.70  fof(f1910,plain,(
% 2.36/0.70    sK1 = k2_xboole_0(k4_xboole_0(sK2,sK0),sK1)),
% 2.36/0.70    inference(backward_demodulation,[],[f217,f1818])).
% 2.36/0.70  fof(f217,plain,(
% 2.36/0.70    sK1 = k2_xboole_0(k4_xboole_0(k4_xboole_0(sK2,k1_xboole_0),sK0),sK1)),
% 2.36/0.70    inference(unit_resulting_resolution,[],[f188,f37])).
% 2.36/0.70  fof(f188,plain,(
% 2.36/0.70    r1_tarski(k4_xboole_0(k4_xboole_0(sK2,k1_xboole_0),sK0),sK1)),
% 2.36/0.70    inference(unit_resulting_resolution,[],[f120,f43])).
% 2.36/0.70  fof(f120,plain,(
% 2.36/0.70    r1_tarski(k4_xboole_0(sK2,k1_xboole_0),k2_xboole_0(sK0,sK1))),
% 2.36/0.70    inference(superposition,[],[f105,f56])).
% 2.36/0.70  fof(f105,plain,(
% 2.36/0.70    ( ! [X0] : (r1_tarski(k4_xboole_0(sK2,k4_xboole_0(sK2,X0)),k2_xboole_0(sK0,sK1))) )),
% 2.36/0.70    inference(superposition,[],[f49,f25])).
% 2.36/0.70  fof(f25,plain,(
% 2.36/0.70    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)),
% 2.36/0.70    inference(cnf_transformation,[],[f20])).
% 2.36/0.70  fof(f49,plain,(
% 2.36/0.70    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k2_xboole_0(X0,X2))) )),
% 2.36/0.70    inference(definition_unfolding,[],[f40,f34])).
% 2.36/0.70  fof(f40,plain,(
% 2.36/0.70    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2))) )),
% 2.36/0.70    inference(cnf_transformation,[],[f6])).
% 2.36/0.70  fof(f6,axiom,(
% 2.36/0.70    ! [X0,X1,X2] : r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2))),
% 2.36/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_xboole_1)).
% 2.36/0.70  fof(f1264,plain,(
% 2.36/0.70    sK2 = k2_xboole_0(sK2,sK1)),
% 2.36/0.70    inference(forward_demodulation,[],[f1263,f151])).
% 2.36/0.70  fof(f1263,plain,(
% 2.36/0.70    k2_xboole_0(sK2,sK1) = k2_xboole_0(k1_xboole_0,sK2)),
% 2.36/0.70    inference(forward_demodulation,[],[f1252,f33])).
% 2.36/0.70  fof(f33,plain,(
% 2.36/0.70    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 2.36/0.70    inference(cnf_transformation,[],[f1])).
% 2.36/0.70  fof(f1,axiom,(
% 2.36/0.70    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 2.36/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 2.36/0.70  fof(f1252,plain,(
% 2.36/0.70    k2_xboole_0(sK2,sK1) = k2_xboole_0(sK2,k1_xboole_0)),
% 2.36/0.70    inference(superposition,[],[f36,f1196])).
% 2.36/0.70  fof(f1196,plain,(
% 2.36/0.70    k1_xboole_0 = k4_xboole_0(sK1,sK2)),
% 2.36/0.70    inference(unit_resulting_resolution,[],[f564,f54,f1173,f44])).
% 2.36/0.70  fof(f44,plain,(
% 2.36/0.70    ( ! [X2,X0,X1] : (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1) | ~r1_xboole_0(X1,X2) | k1_xboole_0 = X0) )),
% 2.36/0.70    inference(cnf_transformation,[],[f24])).
% 2.36/0.70  fof(f24,plain,(
% 2.36/0.70    ! [X0,X1,X2] : (k1_xboole_0 = X0 | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 2.36/0.70    inference(flattening,[],[f23])).
% 2.36/0.70  fof(f23,plain,(
% 2.36/0.70    ! [X0,X1,X2] : (k1_xboole_0 = X0 | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 2.36/0.70    inference(ennf_transformation,[],[f14])).
% 2.36/0.70  fof(f14,axiom,(
% 2.36/0.70    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X2) & r1_tarski(X0,X1)) => k1_xboole_0 = X0)),
% 2.36/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_xboole_1)).
% 2.36/0.70  fof(f1173,plain,(
% 2.36/0.70    r1_xboole_0(k4_xboole_0(sK1,sK2),sK3)),
% 2.36/0.70    inference(trivial_inequality_removal,[],[f1168])).
% 2.36/0.70  fof(f1168,plain,(
% 2.36/0.70    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k4_xboole_0(sK1,sK2),sK3)),
% 2.36/0.70    inference(backward_demodulation,[],[f702,f1167])).
% 2.36/0.70  fof(f1167,plain,(
% 2.36/0.70    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK1,sK2),k1_xboole_0)),
% 2.36/0.70    inference(forward_demodulation,[],[f1166,f1025])).
% 2.36/0.70  fof(f1025,plain,(
% 2.36/0.70    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 2.36/0.70    inference(unit_resulting_resolution,[],[f147,f76])).
% 2.36/0.70  fof(f76,plain,(
% 2.36/0.70    ( ! [X8,X7] : (k1_xboole_0 = k4_xboole_0(X7,X8) | ~r1_tarski(X7,X8)) )),
% 2.36/0.70    inference(superposition,[],[f31,f37])).
% 2.36/0.70  fof(f1166,plain,(
% 2.36/0.70    k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,sK3)) = k4_xboole_0(k4_xboole_0(sK1,sK2),k1_xboole_0)),
% 2.36/0.70    inference(forward_demodulation,[],[f1165,f45])).
% 2.36/0.70  fof(f45,plain,(
% 2.36/0.70    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 2.36/0.70    inference(definition_unfolding,[],[f32,f34,f34])).
% 2.36/0.70  fof(f32,plain,(
% 2.36/0.70    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.36/0.70    inference(cnf_transformation,[],[f2])).
% 2.36/0.70  fof(f2,axiom,(
% 2.36/0.70    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.36/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 2.36/0.70  fof(f1165,plain,(
% 2.36/0.70    k4_xboole_0(sK3,k4_xboole_0(sK3,k1_xboole_0)) = k4_xboole_0(k4_xboole_0(sK1,sK2),k1_xboole_0)),
% 2.36/0.70    inference(backward_demodulation,[],[f709,f1025])).
% 2.36/0.70  fof(f709,plain,(
% 2.36/0.70    k4_xboole_0(k4_xboole_0(sK1,sK2),k1_xboole_0) = k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(k1_xboole_0,sK2)))),
% 2.36/0.70    inference(forward_demodulation,[],[f698,f513])).
% 2.36/0.70  fof(f513,plain,(
% 2.36/0.70    ( ! [X20] : (k4_xboole_0(sK3,k4_xboole_0(sK1,X20)) = k4_xboole_0(sK3,k4_xboole_0(k1_xboole_0,X20))) )),
% 2.36/0.70    inference(forward_demodulation,[],[f470,f51])).
% 2.36/0.70  fof(f470,plain,(
% 2.36/0.70    ( ! [X20] : (k4_xboole_0(sK3,k4_xboole_0(sK1,X20)) = k2_xboole_0(k4_xboole_0(sK3,k1_xboole_0),k4_xboole_0(sK3,k4_xboole_0(sK3,X20)))) )),
% 2.36/0.70    inference(superposition,[],[f51,f299])).
% 2.36/0.70  fof(f299,plain,(
% 2.36/0.70    k4_xboole_0(sK3,sK1) = k4_xboole_0(sK3,k1_xboole_0)),
% 2.36/0.70    inference(superposition,[],[f46,f159])).
% 2.36/0.70  fof(f159,plain,(
% 2.36/0.70    k1_xboole_0 = k4_xboole_0(sK3,k4_xboole_0(sK3,sK1))),
% 2.36/0.70    inference(unit_resulting_resolution,[],[f27,f47])).
% 2.36/0.70  fof(f27,plain,(
% 2.36/0.70    r1_xboole_0(sK3,sK1)),
% 2.36/0.70    inference(cnf_transformation,[],[f20])).
% 2.36/0.70  fof(f698,plain,(
% 2.36/0.70    k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(sK1,sK2))) = k4_xboole_0(k4_xboole_0(sK1,sK2),k1_xboole_0)),
% 2.36/0.70    inference(superposition,[],[f45,f623])).
% 2.36/0.70  fof(f623,plain,(
% 2.36/0.70    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK1,sK2),sK3)),
% 2.36/0.70    inference(superposition,[],[f31,f591])).
% 2.36/0.70  fof(f591,plain,(
% 2.36/0.70    sK3 = k2_xboole_0(k4_xboole_0(sK1,sK2),sK3)),
% 2.36/0.70    inference(unit_resulting_resolution,[],[f564,f37])).
% 2.36/0.70  fof(f702,plain,(
% 2.36/0.70    k1_xboole_0 != k4_xboole_0(k4_xboole_0(sK1,sK2),k1_xboole_0) | r1_xboole_0(k4_xboole_0(sK1,sK2),sK3)),
% 2.36/0.70    inference(superposition,[],[f48,f623])).
% 2.36/0.70  fof(f48,plain,(
% 2.36/0.70    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 2.36/0.70    inference(definition_unfolding,[],[f38,f34])).
% 2.36/0.70  fof(f38,plain,(
% 2.36/0.70    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) )),
% 2.36/0.70    inference(cnf_transformation,[],[f3])).
% 2.36/0.70  fof(f54,plain,(
% 2.36/0.70    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 2.36/0.70    inference(superposition,[],[f30,f29])).
% 2.36/0.70  fof(f564,plain,(
% 2.36/0.70    r1_tarski(k4_xboole_0(sK1,sK2),sK3)),
% 2.36/0.70    inference(unit_resulting_resolution,[],[f58,f140])).
% 2.36/0.70  fof(f140,plain,(
% 2.36/0.70    ( ! [X0] : (~r1_tarski(X0,k2_xboole_0(sK0,sK1)) | r1_tarski(k4_xboole_0(X0,sK2),sK3)) )),
% 2.36/0.70    inference(superposition,[],[f43,f25])).
% 2.36/0.70  fof(f58,plain,(
% 2.36/0.70    ( ! [X4,X3] : (r1_tarski(X3,k2_xboole_0(X4,X3))) )),
% 2.36/0.70    inference(superposition,[],[f30,f33])).
% 2.36/0.70  fof(f28,plain,(
% 2.36/0.70    sK1 != sK2),
% 2.36/0.70    inference(cnf_transformation,[],[f20])).
% 2.36/0.70  % SZS output end Proof for theBenchmark
% 2.36/0.70  % (1680)------------------------------
% 2.36/0.70  % (1680)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.36/0.70  % (1680)Termination reason: Refutation
% 2.36/0.70  
% 2.36/0.70  % (1680)Memory used [KB]: 7931
% 2.36/0.70  % (1680)Time elapsed: 0.273 s
% 2.36/0.70  % (1680)------------------------------
% 2.36/0.70  % (1680)------------------------------
% 2.36/0.70  % (1654)Success in time 0.338 s
%------------------------------------------------------------------------------
