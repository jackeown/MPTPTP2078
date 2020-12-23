%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:13 EST 2020

% Result     : Theorem 1.31s
% Output     : Refutation 1.31s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 726 expanded)
%              Number of leaves         :   12 ( 260 expanded)
%              Depth                    :   18
%              Number of atoms          :   91 ( 749 expanded)
%              Number of equality atoms :   73 ( 721 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1875,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f1874])).

fof(f1874,plain,(
    k4_xboole_0(sK1,sK2) != k4_xboole_0(sK1,sK2) ),
    inference(superposition,[],[f1770,f1594])).

fof(f1594,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(backward_demodulation,[],[f1535,f1593])).

fof(f1593,plain,(
    ! [X18] : k2_xboole_0(k4_xboole_0(X18,k4_xboole_0(k1_xboole_0,X18)),k4_xboole_0(k1_xboole_0,X18)) = X18 ),
    inference(forward_demodulation,[],[f1592,f43])).

fof(f43,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f28,f27])).

fof(f27,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f28,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f1592,plain,(
    ! [X18] : k2_xboole_0(k4_xboole_0(X18,k4_xboole_0(k1_xboole_0,X18)),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X18)))) = X18 ),
    inference(forward_demodulation,[],[f1552,f53])).

fof(f53,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f42,f24])).

fof(f24,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f42,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f25,f27,f27])).

fof(f25,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

% (27586)Refutation not found, incomplete strategy% (27586)------------------------------
% (27586)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (27586)Termination reason: Refutation not found, incomplete strategy

% (27586)Memory used [KB]: 10618
% (27586)Time elapsed: 0.160 s
% (27586)------------------------------
% (27586)------------------------------
fof(f1552,plain,(
    ! [X18] : k2_xboole_0(k4_xboole_0(X18,k4_xboole_0(k1_xboole_0,X18)),k4_xboole_0(k4_xboole_0(k1_xboole_0,X18),k4_xboole_0(k1_xboole_0,X18))) = X18 ),
    inference(superposition,[],[f193,f1436])).

fof(f1436,plain,(
    ! [X6] : k4_xboole_0(k1_xboole_0,X6) = k4_xboole_0(k4_xboole_0(k1_xboole_0,X6),X6) ),
    inference(forward_demodulation,[],[f1435,f78])).

fof(f78,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) = X0 ),
    inference(superposition,[],[f65,f53])).

fof(f65,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(superposition,[],[f43,f24])).

fof(f1435,plain,(
    ! [X6] : k4_xboole_0(k4_xboole_0(k1_xboole_0,X6),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X6)))) = k4_xboole_0(k4_xboole_0(k1_xboole_0,X6),X6) ),
    inference(forward_demodulation,[],[f1434,f698])).

fof(f698,plain,(
    ! [X4,X2,X3] : k4_xboole_0(k4_xboole_0(X2,X3),X4) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(k4_xboole_0(X2,X3),X4))) ),
    inference(forward_demodulation,[],[f630,f71])).

fof(f71,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(superposition,[],[f43,f42])).

fof(f630,plain,(
    ! [X4,X2,X3] : k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(k4_xboole_0(X2,X3),X4))) = k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X3,X2))),X4) ),
    inference(superposition,[],[f45,f42])).

fof(f45,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f31,f27,f27])).

fof(f31,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f1434,plain,(
    ! [X6] : k4_xboole_0(k4_xboole_0(k1_xboole_0,X6),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X6)))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(k1_xboole_0,X6),X6))) ),
    inference(forward_demodulation,[],[f1333,f45])).

fof(f1333,plain,(
    ! [X6] : k4_xboole_0(k4_xboole_0(k1_xboole_0,X6),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X6)))) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X6))),X6) ),
    inference(superposition,[],[f629,f53])).

fof(f629,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,X1))) = k4_xboole_0(k4_xboole_0(X0,X0),X1) ),
    inference(superposition,[],[f45,f24])).

fof(f193,plain,(
    ! [X2,X1] : k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,k4_xboole_0(X2,X1))) = X1 ),
    inference(forward_demodulation,[],[f186,f71])).

fof(f186,plain,(
    ! [X2,X1] : k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1))),k4_xboole_0(X2,k4_xboole_0(X2,X1))) = X1 ),
    inference(superposition,[],[f44,f42])).

fof(f44,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f29,f27])).

fof(f29,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f1535,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)),k4_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[],[f40,f1436])).

fof(f40,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k4_xboole_0(X1,X0),X0)) ),
    inference(definition_unfolding,[],[f26,f30])).

fof(f30,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).

fof(f26,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f1770,plain,(
    k4_xboole_0(sK1,sK2) != k2_xboole_0(k4_xboole_0(sK1,sK2),k1_xboole_0) ),
    inference(backward_demodulation,[],[f48,f1734])).

fof(f1734,plain,(
    ! [X4,X3] : k1_xboole_0 = k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X4,X3))) ),
    inference(backward_demodulation,[],[f1126,f1711])).

fof(f1711,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f1632,f24])).

fof(f1632,plain,(
    ! [X0] : k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f53,f1626])).

fof(f1626,plain,(
    ! [X1] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[],[f1564,f1594])).

fof(f1564,plain,(
    ! [X10] : k1_xboole_0 = k2_xboole_0(k4_xboole_0(k1_xboole_0,X10),k1_xboole_0) ),
    inference(forward_demodulation,[],[f1560,f196])).

fof(f196,plain,(
    ! [X9] : k1_xboole_0 = k2_xboole_0(k4_xboole_0(k1_xboole_0,X9),k4_xboole_0(X9,X9)) ),
    inference(forward_demodulation,[],[f191,f73])).

fof(f73,plain,(
    ! [X6] : k4_xboole_0(k1_xboole_0,X6) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X6,X6)) ),
    inference(superposition,[],[f43,f53])).

fof(f191,plain,(
    ! [X9] : k1_xboole_0 = k2_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(X9,X9)),k4_xboole_0(X9,X9)) ),
    inference(superposition,[],[f44,f53])).

fof(f1560,plain,(
    ! [X10] : k2_xboole_0(k4_xboole_0(k1_xboole_0,X10),k1_xboole_0) = k2_xboole_0(k4_xboole_0(k1_xboole_0,X10),k4_xboole_0(X10,X10)) ),
    inference(backward_demodulation,[],[f1424,f1521])).

fof(f1521,plain,(
    ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k4_xboole_0(k4_xboole_0(k1_xboole_0,X1),k4_xboole_0(X1,X1)) ),
    inference(superposition,[],[f1436,f73])).

fof(f1424,plain,(
    ! [X10] : k2_xboole_0(k4_xboole_0(k1_xboole_0,X10),k1_xboole_0) = k2_xboole_0(k4_xboole_0(k4_xboole_0(k1_xboole_0,X10),k4_xboole_0(X10,X10)),k4_xboole_0(X10,X10)) ),
    inference(backward_demodulation,[],[f485,f1326])).

fof(f1326,plain,(
    ! [X0] : k4_xboole_0(X0,X0) = k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[],[f629,f78])).

fof(f485,plain,(
    ! [X10] : k2_xboole_0(k4_xboole_0(k1_xboole_0,X10),k1_xboole_0) = k2_xboole_0(k4_xboole_0(k4_xboole_0(k1_xboole_0,X10),k4_xboole_0(X10,X10)),k4_xboole_0(k4_xboole_0(X10,X10),k4_xboole_0(k1_xboole_0,X10))) ),
    inference(superposition,[],[f40,f53])).

% (27602)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% (27602)Refutation not found, incomplete strategy% (27602)------------------------------
% (27602)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (27602)Termination reason: Refutation not found, incomplete strategy

% (27602)Memory used [KB]: 1663
% (27602)Time elapsed: 0.164 s
% (27602)------------------------------
% (27602)------------------------------
% (27601)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
fof(f1126,plain,(
    ! [X4,X3] : k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X4,X3))) = k4_xboole_0(k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X4,X3))),k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X4,X3)))) ),
    inference(forward_demodulation,[],[f1090,f71])).

% (27605)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
fof(f1090,plain,(
    ! [X4,X3] : k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X4,k4_xboole_0(X3,k4_xboole_0(X3,X4))))) = k4_xboole_0(k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X4,k4_xboole_0(X3,k4_xboole_0(X3,X4))))),k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X4,k4_xboole_0(X3,k4_xboole_0(X3,X4)))))) ),
    inference(superposition,[],[f472,f45])).

fof(f472,plain,(
    ! [X0] : k4_xboole_0(X0,X0) = k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,X0)) ),
    inference(resolution,[],[f462,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X1,X0,X2)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f2,f13])).

fof(f13,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f462,plain,(
    ! [X0] : sP0(k4_xboole_0(X0,X0),k4_xboole_0(X0,X0),k4_xboole_0(X0,X0)) ),
    inference(superposition,[],[f119,f53])).

fof(f119,plain,(
    ! [X0] : sP0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0)) ),
    inference(forward_demodulation,[],[f108,f73])).

fof(f108,plain,(
    ! [X0] : sP0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X0))) ),
    inference(superposition,[],[f64,f53])).

fof(f64,plain,(
    ! [X2] : sP0(X2,X2,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X2))) ),
    inference(superposition,[],[f46,f53])).

fof(f46,plain,(
    ! [X0,X1] : sP0(X1,X0,k4_xboole_0(X0,X1)) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f48,plain,(
    k4_xboole_0(sK1,sK2) != k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK2,sK1)))) ),
    inference(backward_demodulation,[],[f47,f45])).

fof(f47,plain,(
    k4_xboole_0(sK1,sK2) != k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1)) ),
    inference(backward_demodulation,[],[f41,f43])).

fof(f41,plain,(
    k4_xboole_0(sK1,sK2) != k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1)) ),
    inference(definition_unfolding,[],[f23,f30,f27])).

fof(f23,plain,(
    k4_xboole_0(sK1,sK2) != k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    k4_xboole_0(sK1,sK2) != k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f12,f15])).

fof(f15,plain,
    ( ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1))
   => k4_xboole_0(sK1,sK2) != k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.15  % Command    : run_vampire %s %d
% 0.14/0.36  % Computer   : n007.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % WCLimit    : 600
% 0.14/0.36  % DateTime   : Tue Dec  1 13:09:06 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.22/0.52  % (27591)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  % (27599)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.52  % (27600)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.52  % (27599)Refutation not found, incomplete strategy% (27599)------------------------------
% 0.22/0.52  % (27599)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (27600)Refutation not found, incomplete strategy% (27600)------------------------------
% 0.22/0.53  % (27600)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (27600)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (27600)Memory used [KB]: 1663
% 0.22/0.53  % (27600)Time elapsed: 0.061 s
% 0.22/0.53  % (27600)------------------------------
% 0.22/0.53  % (27600)------------------------------
% 0.22/0.53  % (27599)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (27599)Memory used [KB]: 10618
% 0.22/0.53  % (27599)Time elapsed: 0.071 s
% 1.20/0.53  % (27599)------------------------------
% 1.20/0.53  % (27599)------------------------------
% 1.20/0.53  % (27578)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.20/0.53  % (27592)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.20/0.53  % (27587)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.20/0.53  % (27589)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.20/0.54  % (27583)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.31/0.55  % (27606)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.31/0.55  % (27578)Refutation not found, incomplete strategy% (27578)------------------------------
% 1.31/0.55  % (27578)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.55  % (27578)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.55  
% 1.31/0.55  % (27578)Memory used [KB]: 10618
% 1.31/0.55  % (27578)Time elapsed: 0.128 s
% 1.31/0.55  % (27578)------------------------------
% 1.31/0.55  % (27578)------------------------------
% 1.31/0.55  % (27604)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.31/0.55  % (27596)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.31/0.55  % (27579)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.31/0.55  % (27582)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.31/0.55  % (27580)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.31/0.55  % (27580)Refutation not found, incomplete strategy% (27580)------------------------------
% 1.31/0.55  % (27580)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.55  % (27580)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.55  
% 1.31/0.55  % (27580)Memory used [KB]: 6140
% 1.31/0.55  % (27580)Time elapsed: 0.126 s
% 1.31/0.55  % (27580)------------------------------
% 1.31/0.55  % (27580)------------------------------
% 1.31/0.55  % (27590)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.31/0.56  % (27587)Refutation not found, incomplete strategy% (27587)------------------------------
% 1.31/0.56  % (27587)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.56  % (27587)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.56  
% 1.31/0.56  % (27587)Memory used [KB]: 10618
% 1.31/0.56  % (27587)Time elapsed: 0.136 s
% 1.31/0.56  % (27587)------------------------------
% 1.31/0.56  % (27587)------------------------------
% 1.31/0.56  % (27589)Refutation not found, incomplete strategy% (27589)------------------------------
% 1.31/0.56  % (27589)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.56  % (27589)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.56  
% 1.31/0.56  % (27589)Memory used [KB]: 10618
% 1.31/0.56  % (27589)Time elapsed: 0.136 s
% 1.31/0.56  % (27589)------------------------------
% 1.31/0.56  % (27589)------------------------------
% 1.31/0.56  % (27607)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.31/0.56  % (27603)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.31/0.56  % (27597)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.31/0.56  % (27604)Refutation not found, incomplete strategy% (27604)------------------------------
% 1.31/0.56  % (27604)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.56  % (27604)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.56  
% 1.31/0.56  % (27604)Memory used [KB]: 6140
% 1.31/0.56  % (27604)Time elapsed: 0.141 s
% 1.31/0.56  % (27604)------------------------------
% 1.31/0.56  % (27604)------------------------------
% 1.31/0.56  % (27577)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.31/0.56  % (27596)Refutation not found, incomplete strategy% (27596)------------------------------
% 1.31/0.56  % (27596)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.56  % (27596)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.56  
% 1.31/0.56  % (27596)Memory used [KB]: 10618
% 1.31/0.56  % (27596)Time elapsed: 0.141 s
% 1.31/0.56  % (27596)------------------------------
% 1.31/0.56  % (27596)------------------------------
% 1.31/0.57  % (27595)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.31/0.57  % (27608)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.31/0.57  % (27598)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.31/0.57  % (27576)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.31/0.57  % (27576)Refutation not found, incomplete strategy% (27576)------------------------------
% 1.31/0.57  % (27576)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.57  % (27576)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.57  
% 1.31/0.57  % (27576)Memory used [KB]: 1663
% 1.31/0.57  % (27576)Time elapsed: 0.146 s
% 1.31/0.57  % (27576)------------------------------
% 1.31/0.57  % (27576)------------------------------
% 1.31/0.57  % (27594)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.31/0.57  % (27593)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.31/0.58  % (27586)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.31/0.58  % (27591)Refutation found. Thanks to Tanya!
% 1.31/0.58  % SZS status Theorem for theBenchmark
% 1.31/0.58  % SZS output start Proof for theBenchmark
% 1.31/0.58  fof(f1875,plain,(
% 1.31/0.58    $false),
% 1.31/0.58    inference(trivial_inequality_removal,[],[f1874])).
% 1.31/0.58  fof(f1874,plain,(
% 1.31/0.58    k4_xboole_0(sK1,sK2) != k4_xboole_0(sK1,sK2)),
% 1.31/0.58    inference(superposition,[],[f1770,f1594])).
% 1.31/0.58  fof(f1594,plain,(
% 1.31/0.58    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.31/0.58    inference(backward_demodulation,[],[f1535,f1593])).
% 1.31/0.58  fof(f1593,plain,(
% 1.31/0.58    ( ! [X18] : (k2_xboole_0(k4_xboole_0(X18,k4_xboole_0(k1_xboole_0,X18)),k4_xboole_0(k1_xboole_0,X18)) = X18) )),
% 1.31/0.58    inference(forward_demodulation,[],[f1592,f43])).
% 1.31/0.58  fof(f43,plain,(
% 1.31/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.31/0.58    inference(definition_unfolding,[],[f28,f27])).
% 1.31/0.58  fof(f27,plain,(
% 1.31/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.31/0.58    inference(cnf_transformation,[],[f6])).
% 1.31/0.58  fof(f6,axiom,(
% 1.31/0.58    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.31/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.31/0.58  fof(f28,plain,(
% 1.31/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.31/0.58    inference(cnf_transformation,[],[f5])).
% 1.31/0.58  fof(f5,axiom,(
% 1.31/0.58    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.31/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).
% 1.31/0.58  fof(f1592,plain,(
% 1.31/0.58    ( ! [X18] : (k2_xboole_0(k4_xboole_0(X18,k4_xboole_0(k1_xboole_0,X18)),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X18)))) = X18) )),
% 1.31/0.58    inference(forward_demodulation,[],[f1552,f53])).
% 1.31/0.58  fof(f53,plain,(
% 1.31/0.58    ( ! [X0] : (k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(X0,X0)) )),
% 1.31/0.58    inference(superposition,[],[f42,f24])).
% 1.31/0.58  fof(f24,plain,(
% 1.31/0.58    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.31/0.58    inference(cnf_transformation,[],[f4])).
% 1.31/0.58  fof(f4,axiom,(
% 1.31/0.58    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.31/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 1.31/0.58  fof(f42,plain,(
% 1.31/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 1.31/0.58    inference(definition_unfolding,[],[f25,f27,f27])).
% 1.31/0.58  fof(f25,plain,(
% 1.31/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.31/0.58    inference(cnf_transformation,[],[f1])).
% 1.31/0.58  fof(f1,axiom,(
% 1.31/0.58    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.31/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.31/0.58  % (27586)Refutation not found, incomplete strategy% (27586)------------------------------
% 1.31/0.58  % (27586)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.58  % (27586)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.58  
% 1.31/0.58  % (27586)Memory used [KB]: 10618
% 1.31/0.58  % (27586)Time elapsed: 0.160 s
% 1.31/0.58  % (27586)------------------------------
% 1.31/0.58  % (27586)------------------------------
% 1.31/0.58  fof(f1552,plain,(
% 1.31/0.58    ( ! [X18] : (k2_xboole_0(k4_xboole_0(X18,k4_xboole_0(k1_xboole_0,X18)),k4_xboole_0(k4_xboole_0(k1_xboole_0,X18),k4_xboole_0(k1_xboole_0,X18))) = X18) )),
% 1.31/0.58    inference(superposition,[],[f193,f1436])).
% 1.31/0.58  fof(f1436,plain,(
% 1.31/0.58    ( ! [X6] : (k4_xboole_0(k1_xboole_0,X6) = k4_xboole_0(k4_xboole_0(k1_xboole_0,X6),X6)) )),
% 1.31/0.58    inference(forward_demodulation,[],[f1435,f78])).
% 1.31/0.58  fof(f78,plain,(
% 1.31/0.58    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) = X0) )),
% 1.31/0.58    inference(superposition,[],[f65,f53])).
% 1.31/0.58  fof(f65,plain,(
% 1.31/0.58    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 1.31/0.58    inference(superposition,[],[f43,f24])).
% 1.31/0.58  fof(f1435,plain,(
% 1.31/0.58    ( ! [X6] : (k4_xboole_0(k4_xboole_0(k1_xboole_0,X6),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X6)))) = k4_xboole_0(k4_xboole_0(k1_xboole_0,X6),X6)) )),
% 1.31/0.58    inference(forward_demodulation,[],[f1434,f698])).
% 1.31/0.58  fof(f698,plain,(
% 1.31/0.58    ( ! [X4,X2,X3] : (k4_xboole_0(k4_xboole_0(X2,X3),X4) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(k4_xboole_0(X2,X3),X4)))) )),
% 1.31/0.58    inference(forward_demodulation,[],[f630,f71])).
% 1.31/0.58  fof(f71,plain,(
% 1.31/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) )),
% 1.31/0.58    inference(superposition,[],[f43,f42])).
% 1.31/0.58  fof(f630,plain,(
% 1.31/0.58    ( ! [X4,X2,X3] : (k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(k4_xboole_0(X2,X3),X4))) = k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X3,X2))),X4)) )),
% 1.31/0.58    inference(superposition,[],[f45,f42])).
% 1.31/0.58  fof(f45,plain,(
% 1.31/0.58    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 1.31/0.58    inference(definition_unfolding,[],[f31,f27,f27])).
% 1.31/0.58  fof(f31,plain,(
% 1.31/0.58    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 1.31/0.58    inference(cnf_transformation,[],[f7])).
% 1.31/0.58  fof(f7,axiom,(
% 1.31/0.58    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 1.31/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).
% 1.31/0.58  fof(f1434,plain,(
% 1.31/0.58    ( ! [X6] : (k4_xboole_0(k4_xboole_0(k1_xboole_0,X6),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X6)))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(k1_xboole_0,X6),X6)))) )),
% 1.31/0.58    inference(forward_demodulation,[],[f1333,f45])).
% 1.31/0.58  fof(f1333,plain,(
% 1.31/0.58    ( ! [X6] : (k4_xboole_0(k4_xboole_0(k1_xboole_0,X6),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X6)))) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X6))),X6)) )),
% 1.31/0.58    inference(superposition,[],[f629,f53])).
% 1.31/0.58  fof(f629,plain,(
% 1.31/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,X1))) = k4_xboole_0(k4_xboole_0(X0,X0),X1)) )),
% 1.31/0.58    inference(superposition,[],[f45,f24])).
% 1.31/0.58  fof(f193,plain,(
% 1.31/0.58    ( ! [X2,X1] : (k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,k4_xboole_0(X2,X1))) = X1) )),
% 1.31/0.58    inference(forward_demodulation,[],[f186,f71])).
% 1.31/0.58  fof(f186,plain,(
% 1.31/0.58    ( ! [X2,X1] : (k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1))),k4_xboole_0(X2,k4_xboole_0(X2,X1))) = X1) )),
% 1.31/0.58    inference(superposition,[],[f44,f42])).
% 1.31/0.58  fof(f44,plain,(
% 1.31/0.58    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 1.31/0.58    inference(definition_unfolding,[],[f29,f27])).
% 1.31/0.58  fof(f29,plain,(
% 1.31/0.58    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 1.31/0.58    inference(cnf_transformation,[],[f8])).
% 1.31/0.58  fof(f8,axiom,(
% 1.31/0.58    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 1.31/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).
% 1.31/0.58  fof(f1535,plain,(
% 1.31/0.58    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)),k4_xboole_0(k1_xboole_0,X0))) )),
% 1.31/0.58    inference(superposition,[],[f40,f1436])).
% 1.31/0.58  fof(f40,plain,(
% 1.31/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k4_xboole_0(X1,X0),X0))) )),
% 1.31/0.58    inference(definition_unfolding,[],[f26,f30])).
% 1.31/0.58  fof(f30,plain,(
% 1.31/0.58    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 1.31/0.58    inference(cnf_transformation,[],[f3])).
% 1.31/0.58  fof(f3,axiom,(
% 1.31/0.58    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 1.31/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).
% 1.31/0.58  fof(f26,plain,(
% 1.31/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.31/0.58    inference(cnf_transformation,[],[f9])).
% 1.31/0.58  fof(f9,axiom,(
% 1.31/0.58    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.31/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.31/0.58  fof(f1770,plain,(
% 1.31/0.58    k4_xboole_0(sK1,sK2) != k2_xboole_0(k4_xboole_0(sK1,sK2),k1_xboole_0)),
% 1.31/0.58    inference(backward_demodulation,[],[f48,f1734])).
% 1.31/0.58  fof(f1734,plain,(
% 1.31/0.58    ( ! [X4,X3] : (k1_xboole_0 = k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X4,X3)))) )),
% 1.31/0.58    inference(backward_demodulation,[],[f1126,f1711])).
% 1.31/0.58  fof(f1711,plain,(
% 1.31/0.58    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 1.31/0.58    inference(forward_demodulation,[],[f1632,f24])).
% 1.31/0.58  fof(f1632,plain,(
% 1.31/0.58    ( ! [X0] : (k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,k1_xboole_0)) )),
% 1.31/0.58    inference(backward_demodulation,[],[f53,f1626])).
% 1.31/0.58  fof(f1626,plain,(
% 1.31/0.58    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X1)) )),
% 1.31/0.58    inference(superposition,[],[f1564,f1594])).
% 1.31/0.58  fof(f1564,plain,(
% 1.31/0.58    ( ! [X10] : (k1_xboole_0 = k2_xboole_0(k4_xboole_0(k1_xboole_0,X10),k1_xboole_0)) )),
% 1.31/0.58    inference(forward_demodulation,[],[f1560,f196])).
% 1.31/0.58  fof(f196,plain,(
% 1.31/0.58    ( ! [X9] : (k1_xboole_0 = k2_xboole_0(k4_xboole_0(k1_xboole_0,X9),k4_xboole_0(X9,X9))) )),
% 1.31/0.58    inference(forward_demodulation,[],[f191,f73])).
% 1.31/0.58  fof(f73,plain,(
% 1.31/0.58    ( ! [X6] : (k4_xboole_0(k1_xboole_0,X6) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X6,X6))) )),
% 1.31/0.58    inference(superposition,[],[f43,f53])).
% 1.31/0.58  fof(f191,plain,(
% 1.31/0.58    ( ! [X9] : (k1_xboole_0 = k2_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(X9,X9)),k4_xboole_0(X9,X9))) )),
% 1.31/0.58    inference(superposition,[],[f44,f53])).
% 1.31/0.58  fof(f1560,plain,(
% 1.31/0.58    ( ! [X10] : (k2_xboole_0(k4_xboole_0(k1_xboole_0,X10),k1_xboole_0) = k2_xboole_0(k4_xboole_0(k1_xboole_0,X10),k4_xboole_0(X10,X10))) )),
% 1.31/0.58    inference(backward_demodulation,[],[f1424,f1521])).
% 1.31/0.58  fof(f1521,plain,(
% 1.31/0.58    ( ! [X1] : (k4_xboole_0(k1_xboole_0,X1) = k4_xboole_0(k4_xboole_0(k1_xboole_0,X1),k4_xboole_0(X1,X1))) )),
% 1.31/0.58    inference(superposition,[],[f1436,f73])).
% 1.31/0.58  fof(f1424,plain,(
% 1.31/0.58    ( ! [X10] : (k2_xboole_0(k4_xboole_0(k1_xboole_0,X10),k1_xboole_0) = k2_xboole_0(k4_xboole_0(k4_xboole_0(k1_xboole_0,X10),k4_xboole_0(X10,X10)),k4_xboole_0(X10,X10))) )),
% 1.31/0.58    inference(backward_demodulation,[],[f485,f1326])).
% 1.31/0.58  fof(f1326,plain,(
% 1.31/0.58    ( ! [X0] : (k4_xboole_0(X0,X0) = k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(k1_xboole_0,X0))) )),
% 1.31/0.58    inference(superposition,[],[f629,f78])).
% 1.31/0.58  fof(f485,plain,(
% 1.31/0.58    ( ! [X10] : (k2_xboole_0(k4_xboole_0(k1_xboole_0,X10),k1_xboole_0) = k2_xboole_0(k4_xboole_0(k4_xboole_0(k1_xboole_0,X10),k4_xboole_0(X10,X10)),k4_xboole_0(k4_xboole_0(X10,X10),k4_xboole_0(k1_xboole_0,X10)))) )),
% 1.31/0.58    inference(superposition,[],[f40,f53])).
% 1.31/0.58  % (27602)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.31/0.58  % (27602)Refutation not found, incomplete strategy% (27602)------------------------------
% 1.31/0.58  % (27602)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.58  % (27602)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.58  
% 1.31/0.58  % (27602)Memory used [KB]: 1663
% 1.31/0.58  % (27602)Time elapsed: 0.164 s
% 1.31/0.58  % (27602)------------------------------
% 1.31/0.58  % (27602)------------------------------
% 1.31/0.58  % (27601)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.31/0.59  fof(f1126,plain,(
% 1.31/0.59    ( ! [X4,X3] : (k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X4,X3))) = k4_xboole_0(k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X4,X3))),k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X4,X3))))) )),
% 1.31/0.59    inference(forward_demodulation,[],[f1090,f71])).
% 1.31/0.59  % (27605)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.31/0.59  fof(f1090,plain,(
% 1.31/0.59    ( ! [X4,X3] : (k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X4,k4_xboole_0(X3,k4_xboole_0(X3,X4))))) = k4_xboole_0(k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X4,k4_xboole_0(X3,k4_xboole_0(X3,X4))))),k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X4,k4_xboole_0(X3,k4_xboole_0(X3,X4))))))) )),
% 1.31/0.59    inference(superposition,[],[f472,f45])).
% 1.31/0.59  fof(f472,plain,(
% 1.31/0.59    ( ! [X0] : (k4_xboole_0(X0,X0) = k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,X0))) )),
% 1.31/0.59    inference(resolution,[],[f462,f39])).
% 1.31/0.59  fof(f39,plain,(
% 1.31/0.59    ( ! [X2,X0,X1] : (~sP0(X1,X0,X2) | k4_xboole_0(X0,X1) = X2) )),
% 1.31/0.59    inference(cnf_transformation,[],[f22])).
% 1.31/0.59  fof(f22,plain,(
% 1.31/0.59    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k4_xboole_0(X0,X1) != X2))),
% 1.31/0.59    inference(nnf_transformation,[],[f14])).
% 1.31/0.59  fof(f14,plain,(
% 1.31/0.59    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 1.31/0.59    inference(definition_folding,[],[f2,f13])).
% 1.31/0.59  fof(f13,plain,(
% 1.31/0.59    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.31/0.59    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.31/0.59  fof(f2,axiom,(
% 1.31/0.59    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.31/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.31/0.59  fof(f462,plain,(
% 1.31/0.59    ( ! [X0] : (sP0(k4_xboole_0(X0,X0),k4_xboole_0(X0,X0),k4_xboole_0(X0,X0))) )),
% 1.31/0.59    inference(superposition,[],[f119,f53])).
% 1.31/0.59  fof(f119,plain,(
% 1.31/0.59    ( ! [X0] : (sP0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0))) )),
% 1.31/0.59    inference(forward_demodulation,[],[f108,f73])).
% 1.31/0.59  fof(f108,plain,(
% 1.31/0.59    ( ! [X0] : (sP0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X0)))) )),
% 1.31/0.59    inference(superposition,[],[f64,f53])).
% 1.31/0.59  fof(f64,plain,(
% 1.31/0.59    ( ! [X2] : (sP0(X2,X2,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X2)))) )),
% 1.31/0.59    inference(superposition,[],[f46,f53])).
% 1.31/0.59  fof(f46,plain,(
% 1.31/0.59    ( ! [X0,X1] : (sP0(X1,X0,k4_xboole_0(X0,X1))) )),
% 1.31/0.59    inference(equality_resolution,[],[f38])).
% 1.31/0.59  fof(f38,plain,(
% 1.31/0.59    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.31/0.59    inference(cnf_transformation,[],[f22])).
% 1.31/0.59  fof(f48,plain,(
% 1.31/0.59    k4_xboole_0(sK1,sK2) != k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK2,sK1))))),
% 1.31/0.59    inference(backward_demodulation,[],[f47,f45])).
% 1.31/0.59  fof(f47,plain,(
% 1.31/0.59    k4_xboole_0(sK1,sK2) != k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),
% 1.31/0.59    inference(backward_demodulation,[],[f41,f43])).
% 1.31/0.59  fof(f41,plain,(
% 1.31/0.59    k4_xboole_0(sK1,sK2) != k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),
% 1.31/0.59    inference(definition_unfolding,[],[f23,f30,f27])).
% 1.31/0.59  fof(f23,plain,(
% 1.31/0.59    k4_xboole_0(sK1,sK2) != k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))),
% 1.31/0.59    inference(cnf_transformation,[],[f16])).
% 1.31/0.59  fof(f16,plain,(
% 1.31/0.59    k4_xboole_0(sK1,sK2) != k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))),
% 1.31/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f12,f15])).
% 1.31/0.59  fof(f15,plain,(
% 1.31/0.59    ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1)) => k4_xboole_0(sK1,sK2) != k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))),
% 1.31/0.59    introduced(choice_axiom,[])).
% 1.31/0.59  fof(f12,plain,(
% 1.31/0.59    ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.31/0.59    inference(ennf_transformation,[],[f11])).
% 1.31/0.59  fof(f11,negated_conjecture,(
% 1.31/0.59    ~! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.31/0.59    inference(negated_conjecture,[],[f10])).
% 1.31/0.59  fof(f10,conjecture,(
% 1.31/0.59    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.31/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.31/0.59  % SZS output end Proof for theBenchmark
% 1.31/0.59  % (27591)------------------------------
% 1.31/0.59  % (27591)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.59  % (27591)Termination reason: Refutation
% 1.31/0.59  
% 1.31/0.59  % (27591)Memory used [KB]: 7291
% 1.31/0.59  % (27591)Time elapsed: 0.126 s
% 1.31/0.59  % (27591)------------------------------
% 1.31/0.59  % (27591)------------------------------
% 1.31/0.59  % (27572)Success in time 0.208 s
%------------------------------------------------------------------------------
