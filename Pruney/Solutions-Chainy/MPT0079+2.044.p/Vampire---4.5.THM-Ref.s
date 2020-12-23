%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:57 EST 2020

% Result     : Theorem 1.67s
% Output     : Refutation 1.67s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 392 expanded)
%              Number of leaves         :   13 ( 109 expanded)
%              Depth                    :   32
%              Number of atoms          :  128 ( 676 expanded)
%              Number of equality atoms :   76 ( 371 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1143,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1142,f27])).

fof(f27,plain,(
    sK1 != sK2 ),
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
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X3,X1)
          & r1_xboole_0(X2,X0)
          & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
       => X1 = X2 ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X3,X1)
        & r1_xboole_0(X2,X0)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_xboole_1)).

fof(f1142,plain,(
    sK1 = sK2 ),
    inference(forward_demodulation,[],[f1131,f812])).

fof(f812,plain,(
    sK1 = k2_xboole_0(sK1,sK2) ),
    inference(forward_demodulation,[],[f809,f30])).

fof(f30,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f809,plain,(
    k2_xboole_0(sK1,k1_xboole_0) = k2_xboole_0(sK1,sK2) ),
    inference(superposition,[],[f35,f789])).

fof(f789,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,sK1) ),
    inference(superposition,[],[f692,f294])).

fof(f294,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f143,f24])).

fof(f24,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f20])).

fof(f143,plain,(
    ! [X2,X3] : k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X2,X3)) ),
    inference(forward_demodulation,[],[f128,f74])).

fof(f74,plain,(
    ! [X8] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X8) ),
    inference(forward_demodulation,[],[f70,f47])).

fof(f47,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f43,f29])).

fof(f29,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f43,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f28,f34])).

fof(f34,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f28,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f70,plain,(
    ! [X8] : k4_xboole_0(k1_xboole_0,X8) = k4_xboole_0(X8,X8) ),
    inference(superposition,[],[f36,f52])).

fof(f52,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f33,f30])).

fof(f33,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f36,plain,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f128,plain,(
    ! [X2,X3] : k4_xboole_0(X2,k2_xboole_0(X2,X3)) = k4_xboole_0(k1_xboole_0,X3) ),
    inference(superposition,[],[f41,f47])).

fof(f41,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f692,plain,(
    ! [X0] : k4_xboole_0(sK2,k2_xboole_0(sK0,X0)) = k4_xboole_0(sK2,X0) ),
    inference(superposition,[],[f41,f669])).

fof(f669,plain,(
    sK2 = k4_xboole_0(sK2,sK0) ),
    inference(superposition,[],[f589,f52])).

fof(f589,plain,(
    sK2 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK2,sK0)) ),
    inference(superposition,[],[f44,f86])).

fof(f86,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) ),
    inference(resolution,[],[f84,f31])).

fof(f31,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f84,plain,(
    ! [X2] : ~ r2_hidden(X2,k4_xboole_0(sK2,k4_xboole_0(sK2,sK0))) ),
    inference(resolution,[],[f46,f25])).

fof(f25,plain,(
    r1_xboole_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(definition_unfolding,[],[f38,f34])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f44,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f37,f34])).

fof(f37,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f35,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f1131,plain,(
    sK2 = k2_xboole_0(sK1,sK2) ),
    inference(superposition,[],[f1130,f33])).

fof(f1130,plain,(
    sK2 = k2_xboole_0(sK2,sK1) ),
    inference(forward_demodulation,[],[f1126,f30])).

fof(f1126,plain,(
    k2_xboole_0(sK2,sK1) = k2_xboole_0(sK2,k1_xboole_0) ),
    inference(superposition,[],[f35,f1115])).

fof(f1115,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,sK2) ),
    inference(forward_demodulation,[],[f1103,f155])).

fof(f155,plain,(
    ! [X6,X5] : k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X6,X5)) ),
    inference(forward_demodulation,[],[f139,f35])).

fof(f139,plain,(
    ! [X6,X5] : k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X6,k4_xboole_0(X5,X6))) ),
    inference(superposition,[],[f41,f47])).

fof(f1103,plain,(
    k4_xboole_0(sK1,k2_xboole_0(sK0,sK1)) = k4_xboole_0(sK1,sK2) ),
    inference(superposition,[],[f781,f992])).

fof(f992,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK3,sK2) ),
    inference(forward_demodulation,[],[f991,f81])).

fof(f81,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f80,f24])).

fof(f80,plain,(
    k2_xboole_0(sK2,sK3) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f79,f33])).

fof(f79,plain,(
    k2_xboole_0(sK3,sK2) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f78,f35])).

fof(f78,plain,(
    k2_xboole_0(sK3,k2_xboole_0(sK0,sK1)) = k2_xboole_0(sK3,k4_xboole_0(sK2,sK3)) ),
    inference(superposition,[],[f35,f69])).

fof(f69,plain,(
    k4_xboole_0(sK2,sK3) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK3) ),
    inference(superposition,[],[f36,f24])).

fof(f991,plain,(
    k2_xboole_0(sK3,sK2) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f35,f970])).

fof(f970,plain,(
    sK2 = k4_xboole_0(k2_xboole_0(sK0,sK1),sK3) ),
    inference(backward_demodulation,[],[f69,f964])).

fof(f964,plain,(
    sK2 = k4_xboole_0(sK2,sK3) ),
    inference(superposition,[],[f955,f52])).

fof(f955,plain,(
    sK2 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK2,sK3)) ),
    inference(superposition,[],[f44,f951])).

fof(f951,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) ),
    inference(resolution,[],[f949,f31])).

fof(f949,plain,(
    ! [X0] : ~ r2_hidden(X0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) ),
    inference(resolution,[],[f946,f46])).

fof(f946,plain,(
    r1_xboole_0(sK2,sK3) ),
    inference(resolution,[],[f936,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f936,plain,(
    r1_xboole_0(sK3,sK2) ),
    inference(subsumption_resolution,[],[f935,f87])).

fof(f87,plain,(
    ! [X2] : ~ r2_hidden(X2,k1_xboole_0) ),
    inference(backward_demodulation,[],[f84,f86])).

fof(f935,plain,
    ( r2_hidden(sK5(sK3,sK2),k1_xboole_0)
    | r1_xboole_0(sK3,sK2) ),
    inference(forward_demodulation,[],[f911,f47])).

fof(f911,plain,
    ( r2_hidden(sK5(sK3,sK2),k4_xboole_0(sK3,sK3))
    | r1_xboole_0(sK3,sK2) ),
    inference(superposition,[],[f45,f875])).

fof(f875,plain,(
    sK3 = k4_xboole_0(sK3,sK2) ),
    inference(forward_demodulation,[],[f865,f694])).

fof(f694,plain,(
    sK3 = k4_xboole_0(sK3,sK1) ),
    inference(superposition,[],[f590,f52])).

fof(f590,plain,(
    sK3 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK3,sK1)) ),
    inference(superposition,[],[f44,f89])).

fof(f89,plain,(
    k1_xboole_0 = k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)) ),
    inference(resolution,[],[f85,f31])).

fof(f85,plain,(
    ! [X3] : ~ r2_hidden(X3,k4_xboole_0(sK3,k4_xboole_0(sK3,sK1))) ),
    inference(resolution,[],[f46,f26])).

fof(f26,plain,(
    r1_xboole_0(sK3,sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f865,plain,(
    k4_xboole_0(sK3,sK1) = k4_xboole_0(sK3,sK2) ),
    inference(superposition,[],[f723,f812])).

fof(f723,plain,(
    ! [X0] : k4_xboole_0(sK3,k2_xboole_0(sK1,X0)) = k4_xboole_0(sK3,X0) ),
    inference(superposition,[],[f41,f694])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f39,f34])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f781,plain,(
    ! [X0] : k4_xboole_0(sK1,k2_xboole_0(sK3,X0)) = k4_xboole_0(sK1,X0) ),
    inference(superposition,[],[f41,f750])).

fof(f750,plain,(
    sK1 = k4_xboole_0(sK1,sK3) ),
    inference(superposition,[],[f588,f52])).

fof(f588,plain,(
    sK1 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK3)) ),
    inference(superposition,[],[f44,f93])).

fof(f93,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) ),
    inference(resolution,[],[f83,f31])).

fof(f83,plain,(
    ! [X1] : ~ r2_hidden(X1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK3))) ),
    inference(resolution,[],[f46,f49])).

fof(f49,plain,(
    r1_xboole_0(sK1,sK3) ),
    inference(resolution,[],[f40,f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:31:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.51  % (27590)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.51  % (27576)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.51  % (27590)Refutation not found, incomplete strategy% (27590)------------------------------
% 0.21/0.51  % (27590)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (27579)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (27590)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (27590)Memory used [KB]: 6140
% 0.21/0.51  % (27590)Time elapsed: 0.003 s
% 0.21/0.51  % (27590)------------------------------
% 0.21/0.51  % (27590)------------------------------
% 0.21/0.51  % (27582)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.51  % (27580)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (27578)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.52  % (27581)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (27603)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.52  % (27589)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.52  % (27598)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.52  % (27577)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (27584)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.53  % (27593)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.53  % (27588)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.53  % (27597)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.53  % (27599)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.53  % (27604)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.53  % (27575)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (27595)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.53  % (27601)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.53  % (27596)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.54  % (27586)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (27600)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.54  % (27583)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.54  % (27602)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (27592)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.54  % (27592)Refutation not found, incomplete strategy% (27592)------------------------------
% 0.21/0.54  % (27592)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (27592)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (27592)Memory used [KB]: 10618
% 0.21/0.54  % (27592)Time elapsed: 0.131 s
% 0.21/0.54  % (27592)------------------------------
% 0.21/0.54  % (27592)------------------------------
% 0.21/0.55  % (27591)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.55  % (27594)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.55  % (27585)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.55  % (27587)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.67/0.59  % (27581)Refutation found. Thanks to Tanya!
% 1.67/0.59  % SZS status Theorem for theBenchmark
% 1.67/0.59  % SZS output start Proof for theBenchmark
% 1.67/0.59  fof(f1143,plain,(
% 1.67/0.59    $false),
% 1.67/0.59    inference(subsumption_resolution,[],[f1142,f27])).
% 1.67/0.59  fof(f27,plain,(
% 1.67/0.59    sK1 != sK2),
% 1.67/0.59    inference(cnf_transformation,[],[f20])).
% 1.67/0.59  fof(f20,plain,(
% 1.67/0.59    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3))),
% 1.67/0.59    inference(flattening,[],[f19])).
% 1.67/0.59  fof(f19,plain,(
% 1.67/0.59    ? [X0,X1,X2,X3] : (X1 != X2 & (r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)))),
% 1.67/0.59    inference(ennf_transformation,[],[f16])).
% 1.67/0.59  fof(f16,negated_conjecture,(
% 1.67/0.59    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 1.67/0.59    inference(negated_conjecture,[],[f15])).
% 1.67/0.59  fof(f15,conjecture,(
% 1.67/0.59    ! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 1.67/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_xboole_1)).
% 1.67/0.59  fof(f1142,plain,(
% 1.67/0.59    sK1 = sK2),
% 1.67/0.59    inference(forward_demodulation,[],[f1131,f812])).
% 1.67/0.59  fof(f812,plain,(
% 1.67/0.59    sK1 = k2_xboole_0(sK1,sK2)),
% 1.67/0.59    inference(forward_demodulation,[],[f809,f30])).
% 1.67/0.59  fof(f30,plain,(
% 1.67/0.59    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.67/0.59    inference(cnf_transformation,[],[f6])).
% 1.67/0.59  fof(f6,axiom,(
% 1.67/0.59    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 1.67/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 1.67/0.59  fof(f809,plain,(
% 1.67/0.59    k2_xboole_0(sK1,k1_xboole_0) = k2_xboole_0(sK1,sK2)),
% 1.67/0.59    inference(superposition,[],[f35,f789])).
% 1.67/0.59  fof(f789,plain,(
% 1.67/0.59    k1_xboole_0 = k4_xboole_0(sK2,sK1)),
% 1.67/0.59    inference(superposition,[],[f692,f294])).
% 1.67/0.59  fof(f294,plain,(
% 1.67/0.59    k1_xboole_0 = k4_xboole_0(sK2,k2_xboole_0(sK0,sK1))),
% 1.67/0.59    inference(superposition,[],[f143,f24])).
% 1.67/0.59  fof(f24,plain,(
% 1.67/0.59    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)),
% 1.67/0.59    inference(cnf_transformation,[],[f20])).
% 1.67/0.59  fof(f143,plain,(
% 1.67/0.59    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X2,X3))) )),
% 1.67/0.59    inference(forward_demodulation,[],[f128,f74])).
% 1.67/0.59  fof(f74,plain,(
% 1.67/0.59    ( ! [X8] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X8)) )),
% 1.67/0.59    inference(forward_demodulation,[],[f70,f47])).
% 1.67/0.59  fof(f47,plain,(
% 1.67/0.59    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 1.67/0.59    inference(backward_demodulation,[],[f43,f29])).
% 1.67/0.59  fof(f29,plain,(
% 1.67/0.59    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.67/0.59    inference(cnf_transformation,[],[f9])).
% 1.67/0.59  fof(f9,axiom,(
% 1.67/0.59    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.67/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 1.67/0.59  fof(f43,plain,(
% 1.67/0.59    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 1.67/0.59    inference(definition_unfolding,[],[f28,f34])).
% 1.67/0.59  fof(f34,plain,(
% 1.67/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.67/0.59    inference(cnf_transformation,[],[f12])).
% 1.67/0.59  fof(f12,axiom,(
% 1.67/0.59    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.67/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.67/0.59  fof(f28,plain,(
% 1.67/0.59    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.67/0.59    inference(cnf_transformation,[],[f7])).
% 1.67/0.59  fof(f7,axiom,(
% 1.67/0.59    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.67/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 1.67/0.59  fof(f70,plain,(
% 1.67/0.59    ( ! [X8] : (k4_xboole_0(k1_xboole_0,X8) = k4_xboole_0(X8,X8)) )),
% 1.67/0.59    inference(superposition,[],[f36,f52])).
% 1.67/0.59  fof(f52,plain,(
% 1.67/0.59    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 1.67/0.59    inference(superposition,[],[f33,f30])).
% 1.67/0.59  fof(f33,plain,(
% 1.67/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.67/0.59    inference(cnf_transformation,[],[f1])).
% 1.67/0.59  fof(f1,axiom,(
% 1.67/0.59    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.67/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.67/0.59  fof(f36,plain,(
% 1.67/0.59    ( ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1)) )),
% 1.67/0.59    inference(cnf_transformation,[],[f10])).
% 1.67/0.59  fof(f10,axiom,(
% 1.67/0.59    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1)),
% 1.67/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).
% 1.67/0.59  fof(f128,plain,(
% 1.67/0.59    ( ! [X2,X3] : (k4_xboole_0(X2,k2_xboole_0(X2,X3)) = k4_xboole_0(k1_xboole_0,X3)) )),
% 1.67/0.59    inference(superposition,[],[f41,f47])).
% 1.67/0.59  fof(f41,plain,(
% 1.67/0.59    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 1.67/0.59    inference(cnf_transformation,[],[f11])).
% 1.67/0.59  fof(f11,axiom,(
% 1.67/0.59    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 1.67/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 1.67/0.59  fof(f692,plain,(
% 1.67/0.59    ( ! [X0] : (k4_xboole_0(sK2,k2_xboole_0(sK0,X0)) = k4_xboole_0(sK2,X0)) )),
% 1.67/0.59    inference(superposition,[],[f41,f669])).
% 1.67/0.59  fof(f669,plain,(
% 1.67/0.59    sK2 = k4_xboole_0(sK2,sK0)),
% 1.67/0.59    inference(superposition,[],[f589,f52])).
% 1.67/0.59  fof(f589,plain,(
% 1.67/0.59    sK2 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK2,sK0))),
% 1.67/0.59    inference(superposition,[],[f44,f86])).
% 1.67/0.59  fof(f86,plain,(
% 1.67/0.59    k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0))),
% 1.67/0.59    inference(resolution,[],[f84,f31])).
% 1.67/0.59  fof(f31,plain,(
% 1.67/0.59    ( ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0) )),
% 1.67/0.59    inference(cnf_transformation,[],[f21])).
% 1.67/0.59  fof(f21,plain,(
% 1.67/0.59    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.67/0.59    inference(ennf_transformation,[],[f5])).
% 1.67/0.59  fof(f5,axiom,(
% 1.67/0.59    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.67/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 1.67/0.59  fof(f84,plain,(
% 1.67/0.59    ( ! [X2] : (~r2_hidden(X2,k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)))) )),
% 1.67/0.59    inference(resolution,[],[f46,f25])).
% 1.67/0.59  fof(f25,plain,(
% 1.67/0.59    r1_xboole_0(sK2,sK0)),
% 1.67/0.59    inference(cnf_transformation,[],[f20])).
% 1.67/0.59  fof(f46,plain,(
% 1.67/0.59    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.67/0.59    inference(definition_unfolding,[],[f38,f34])).
% 1.67/0.59  fof(f38,plain,(
% 1.67/0.59    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 1.67/0.59    inference(cnf_transformation,[],[f22])).
% 1.67/0.59  fof(f22,plain,(
% 1.67/0.59    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.67/0.59    inference(ennf_transformation,[],[f18])).
% 1.67/0.59  fof(f18,plain,(
% 1.67/0.59    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.67/0.59    inference(rectify,[],[f4])).
% 1.67/0.59  fof(f4,axiom,(
% 1.67/0.59    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.67/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.67/0.59  fof(f44,plain,(
% 1.67/0.59    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 1.67/0.59    inference(definition_unfolding,[],[f37,f34])).
% 1.67/0.59  fof(f37,plain,(
% 1.67/0.59    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 1.67/0.59    inference(cnf_transformation,[],[f14])).
% 1.67/0.59  fof(f14,axiom,(
% 1.67/0.59    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 1.67/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).
% 1.67/0.59  fof(f35,plain,(
% 1.67/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.67/0.59    inference(cnf_transformation,[],[f8])).
% 1.67/0.59  fof(f8,axiom,(
% 1.67/0.59    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.67/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 1.67/0.59  fof(f1131,plain,(
% 1.67/0.59    sK2 = k2_xboole_0(sK1,sK2)),
% 1.67/0.59    inference(superposition,[],[f1130,f33])).
% 1.67/0.59  fof(f1130,plain,(
% 1.67/0.59    sK2 = k2_xboole_0(sK2,sK1)),
% 1.67/0.59    inference(forward_demodulation,[],[f1126,f30])).
% 1.67/0.59  fof(f1126,plain,(
% 1.67/0.59    k2_xboole_0(sK2,sK1) = k2_xboole_0(sK2,k1_xboole_0)),
% 1.67/0.59    inference(superposition,[],[f35,f1115])).
% 1.67/0.59  fof(f1115,plain,(
% 1.67/0.59    k1_xboole_0 = k4_xboole_0(sK1,sK2)),
% 1.67/0.59    inference(forward_demodulation,[],[f1103,f155])).
% 1.67/0.59  fof(f155,plain,(
% 1.67/0.59    ( ! [X6,X5] : (k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X6,X5))) )),
% 1.67/0.59    inference(forward_demodulation,[],[f139,f35])).
% 1.67/0.59  fof(f139,plain,(
% 1.67/0.59    ( ! [X6,X5] : (k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X6,k4_xboole_0(X5,X6)))) )),
% 1.67/0.59    inference(superposition,[],[f41,f47])).
% 1.67/0.59  fof(f1103,plain,(
% 1.67/0.59    k4_xboole_0(sK1,k2_xboole_0(sK0,sK1)) = k4_xboole_0(sK1,sK2)),
% 1.67/0.59    inference(superposition,[],[f781,f992])).
% 1.67/0.59  fof(f992,plain,(
% 1.67/0.59    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK3,sK2)),
% 1.67/0.59    inference(forward_demodulation,[],[f991,f81])).
% 1.67/0.59  fof(f81,plain,(
% 1.67/0.59    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1))),
% 1.67/0.59    inference(forward_demodulation,[],[f80,f24])).
% 1.67/0.59  fof(f80,plain,(
% 1.67/0.59    k2_xboole_0(sK2,sK3) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1))),
% 1.67/0.59    inference(forward_demodulation,[],[f79,f33])).
% 1.67/0.59  fof(f79,plain,(
% 1.67/0.59    k2_xboole_0(sK3,sK2) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1))),
% 1.67/0.59    inference(forward_demodulation,[],[f78,f35])).
% 1.67/0.59  fof(f78,plain,(
% 1.67/0.59    k2_xboole_0(sK3,k2_xboole_0(sK0,sK1)) = k2_xboole_0(sK3,k4_xboole_0(sK2,sK3))),
% 1.67/0.59    inference(superposition,[],[f35,f69])).
% 1.67/0.59  fof(f69,plain,(
% 1.67/0.59    k4_xboole_0(sK2,sK3) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK3)),
% 1.67/0.59    inference(superposition,[],[f36,f24])).
% 1.67/0.59  fof(f991,plain,(
% 1.67/0.59    k2_xboole_0(sK3,sK2) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1))),
% 1.67/0.59    inference(superposition,[],[f35,f970])).
% 1.67/0.59  fof(f970,plain,(
% 1.67/0.59    sK2 = k4_xboole_0(k2_xboole_0(sK0,sK1),sK3)),
% 1.67/0.59    inference(backward_demodulation,[],[f69,f964])).
% 1.67/0.59  fof(f964,plain,(
% 1.67/0.59    sK2 = k4_xboole_0(sK2,sK3)),
% 1.67/0.59    inference(superposition,[],[f955,f52])).
% 1.67/0.59  fof(f955,plain,(
% 1.67/0.59    sK2 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK2,sK3))),
% 1.67/0.59    inference(superposition,[],[f44,f951])).
% 1.67/0.59  fof(f951,plain,(
% 1.67/0.59    k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),
% 1.67/0.59    inference(resolution,[],[f949,f31])).
% 1.67/0.59  fof(f949,plain,(
% 1.67/0.59    ( ! [X0] : (~r2_hidden(X0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))) )),
% 1.67/0.59    inference(resolution,[],[f946,f46])).
% 1.67/0.59  fof(f946,plain,(
% 1.67/0.59    r1_xboole_0(sK2,sK3)),
% 1.67/0.59    inference(resolution,[],[f936,f40])).
% 1.67/0.59  fof(f40,plain,(
% 1.67/0.59    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 1.67/0.59    inference(cnf_transformation,[],[f23])).
% 1.67/0.59  fof(f23,plain,(
% 1.67/0.59    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 1.67/0.59    inference(ennf_transformation,[],[f3])).
% 1.67/0.59  fof(f3,axiom,(
% 1.67/0.59    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 1.67/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 1.67/0.59  fof(f936,plain,(
% 1.67/0.59    r1_xboole_0(sK3,sK2)),
% 1.67/0.59    inference(subsumption_resolution,[],[f935,f87])).
% 1.67/0.59  fof(f87,plain,(
% 1.67/0.59    ( ! [X2] : (~r2_hidden(X2,k1_xboole_0)) )),
% 1.67/0.59    inference(backward_demodulation,[],[f84,f86])).
% 1.67/0.59  fof(f935,plain,(
% 1.67/0.59    r2_hidden(sK5(sK3,sK2),k1_xboole_0) | r1_xboole_0(sK3,sK2)),
% 1.67/0.59    inference(forward_demodulation,[],[f911,f47])).
% 1.67/0.59  fof(f911,plain,(
% 1.67/0.59    r2_hidden(sK5(sK3,sK2),k4_xboole_0(sK3,sK3)) | r1_xboole_0(sK3,sK2)),
% 1.67/0.59    inference(superposition,[],[f45,f875])).
% 1.67/0.59  fof(f875,plain,(
% 1.67/0.59    sK3 = k4_xboole_0(sK3,sK2)),
% 1.67/0.59    inference(forward_demodulation,[],[f865,f694])).
% 1.67/0.59  fof(f694,plain,(
% 1.67/0.59    sK3 = k4_xboole_0(sK3,sK1)),
% 1.67/0.59    inference(superposition,[],[f590,f52])).
% 1.67/0.59  fof(f590,plain,(
% 1.67/0.59    sK3 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK3,sK1))),
% 1.67/0.59    inference(superposition,[],[f44,f89])).
% 1.67/0.59  fof(f89,plain,(
% 1.67/0.59    k1_xboole_0 = k4_xboole_0(sK3,k4_xboole_0(sK3,sK1))),
% 1.67/0.59    inference(resolution,[],[f85,f31])).
% 1.67/0.59  fof(f85,plain,(
% 1.67/0.59    ( ! [X3] : (~r2_hidden(X3,k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)))) )),
% 1.67/0.59    inference(resolution,[],[f46,f26])).
% 1.67/0.59  fof(f26,plain,(
% 1.67/0.59    r1_xboole_0(sK3,sK1)),
% 1.67/0.59    inference(cnf_transformation,[],[f20])).
% 1.67/0.59  fof(f865,plain,(
% 1.67/0.59    k4_xboole_0(sK3,sK1) = k4_xboole_0(sK3,sK2)),
% 1.67/0.59    inference(superposition,[],[f723,f812])).
% 1.67/0.59  fof(f723,plain,(
% 1.67/0.59    ( ! [X0] : (k4_xboole_0(sK3,k2_xboole_0(sK1,X0)) = k4_xboole_0(sK3,X0)) )),
% 1.67/0.59    inference(superposition,[],[f41,f694])).
% 1.67/0.59  fof(f45,plain,(
% 1.67/0.59    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) | r1_xboole_0(X0,X1)) )),
% 1.67/0.59    inference(definition_unfolding,[],[f39,f34])).
% 1.67/0.59  fof(f39,plain,(
% 1.67/0.59    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1))) )),
% 1.67/0.59    inference(cnf_transformation,[],[f22])).
% 1.67/0.59  fof(f781,plain,(
% 1.67/0.59    ( ! [X0] : (k4_xboole_0(sK1,k2_xboole_0(sK3,X0)) = k4_xboole_0(sK1,X0)) )),
% 1.67/0.59    inference(superposition,[],[f41,f750])).
% 1.67/0.59  fof(f750,plain,(
% 1.67/0.59    sK1 = k4_xboole_0(sK1,sK3)),
% 1.67/0.59    inference(superposition,[],[f588,f52])).
% 1.67/0.59  fof(f588,plain,(
% 1.67/0.59    sK1 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK3))),
% 1.67/0.59    inference(superposition,[],[f44,f93])).
% 1.67/0.59  fof(f93,plain,(
% 1.67/0.59    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK3))),
% 1.67/0.59    inference(resolution,[],[f83,f31])).
% 1.67/0.59  fof(f83,plain,(
% 1.67/0.59    ( ! [X1] : (~r2_hidden(X1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)))) )),
% 1.67/0.59    inference(resolution,[],[f46,f49])).
% 1.67/0.59  fof(f49,plain,(
% 1.67/0.59    r1_xboole_0(sK1,sK3)),
% 1.67/0.59    inference(resolution,[],[f40,f26])).
% 1.67/0.59  % SZS output end Proof for theBenchmark
% 1.67/0.59  % (27581)------------------------------
% 1.67/0.59  % (27581)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.67/0.59  % (27581)Termination reason: Refutation
% 1.67/0.59  
% 1.67/0.59  % (27581)Memory used [KB]: 7036
% 1.67/0.59  % (27581)Time elapsed: 0.153 s
% 1.67/0.59  % (27581)------------------------------
% 1.67/0.59  % (27581)------------------------------
% 1.67/0.59  % (27574)Success in time 0.231 s
%------------------------------------------------------------------------------
