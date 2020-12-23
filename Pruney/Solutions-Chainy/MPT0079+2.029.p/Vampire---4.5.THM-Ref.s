%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:55 EST 2020

% Result     : Theorem 2.99s
% Output     : Refutation 3.62s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 929 expanded)
%              Number of leaves         :   12 ( 263 expanded)
%              Depth                    :   25
%              Number of atoms          :  131 (1610 expanded)
%              Number of equality atoms :   93 ( 996 expanded)
%              Maximal formula depth    :    9 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4702,plain,(
    $false ),
    inference(subsumption_resolution,[],[f4701,f27])).

fof(f27,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_xboole_1)).

fof(f4701,plain,(
    sK1 = sK2 ),
    inference(forward_demodulation,[],[f4700,f2052])).

fof(f2052,plain,(
    sK1 = k2_xboole_0(sK1,sK2) ),
    inference(forward_demodulation,[],[f2046,f28])).

fof(f28,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f2046,plain,(
    k2_xboole_0(sK1,sK2) = k2_xboole_0(sK1,k1_xboole_0) ),
    inference(superposition,[],[f32,f2015])).

fof(f2015,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,sK1) ),
    inference(superposition,[],[f1263,f78])).

fof(f78,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f29,f24])).

fof(f24,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f18])).

fof(f29,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f1263,plain,(
    ! [X0] : k4_xboole_0(sK2,X0) = k4_xboole_0(sK2,k2_xboole_0(sK0,X0)) ),
    inference(superposition,[],[f40,f1210])).

fof(f1210,plain,(
    sK2 = k4_xboole_0(sK2,sK0) ),
    inference(backward_demodulation,[],[f654,f1209])).

fof(f1209,plain,(
    sK2 = k2_xboole_0(sK2,k4_xboole_0(sK2,sK0)) ),
    inference(forward_demodulation,[],[f1194,f236])).

fof(f236,plain,(
    sK2 = k2_xboole_0(sK2,sK2) ),
    inference(forward_demodulation,[],[f230,f28])).

fof(f230,plain,(
    k2_xboole_0(sK2,k1_xboole_0) = k2_xboole_0(sK2,sK2) ),
    inference(superposition,[],[f32,f209])).

fof(f209,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,sK2) ),
    inference(forward_demodulation,[],[f196,f191])).

fof(f191,plain,(
    sK2 = k4_xboole_0(sK2,k1_xboole_0) ),
    inference(superposition,[],[f93,f28])).

fof(f93,plain,(
    sK2 = k2_xboole_0(k4_xboole_0(sK2,k1_xboole_0),k1_xboole_0) ),
    inference(superposition,[],[f46,f53])).

fof(f53,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) ),
    inference(resolution,[],[f25,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f37,f31])).

fof(f31,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f37,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f25,plain,(
    r1_xboole_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f46,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f33,f31])).

fof(f33,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f196,plain,(
    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK2,k1_xboole_0),sK2) ),
    inference(superposition,[],[f29,f93])).

fof(f1194,plain,(
    k2_xboole_0(sK2,k4_xboole_0(sK2,sK0)) = k2_xboole_0(sK2,sK2) ),
    inference(superposition,[],[f212,f89])).

fof(f89,plain,(
    sK2 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK2,sK0)) ),
    inference(superposition,[],[f46,f53])).

fof(f212,plain,(
    ! [X0] : k2_xboole_0(sK2,X0) = k2_xboole_0(sK2,k2_xboole_0(k1_xboole_0,X0)) ),
    inference(forward_demodulation,[],[f200,f191])).

fof(f200,plain,(
    ! [X0] : k2_xboole_0(sK2,X0) = k2_xboole_0(k4_xboole_0(sK2,k1_xboole_0),k2_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[],[f41,f93])).

fof(f41,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f654,plain,(
    k4_xboole_0(sK2,sK0) = k2_xboole_0(sK2,k4_xboole_0(sK2,sK0)) ),
    inference(superposition,[],[f96,f30])).

fof(f30,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f96,plain,(
    k4_xboole_0(sK2,sK0) = k2_xboole_0(k4_xboole_0(sK2,sK0),sK2) ),
    inference(forward_demodulation,[],[f90,f28])).

fof(f90,plain,(
    k2_xboole_0(k4_xboole_0(sK2,sK0),sK2) = k2_xboole_0(k4_xboole_0(sK2,sK0),k1_xboole_0) ),
    inference(superposition,[],[f32,f53])).

fof(f40,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f32,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f4700,plain,(
    sK2 = k2_xboole_0(sK1,sK2) ),
    inference(forward_demodulation,[],[f4699,f28])).

fof(f4699,plain,(
    k2_xboole_0(sK1,sK2) = k2_xboole_0(sK2,k1_xboole_0) ),
    inference(forward_demodulation,[],[f4693,f30])).

fof(f4693,plain,(
    k2_xboole_0(sK2,k1_xboole_0) = k2_xboole_0(sK2,sK1) ),
    inference(superposition,[],[f32,f4683])).

fof(f4683,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,sK2) ),
    inference(forward_demodulation,[],[f4661,f1943])).

% (30377)Time limit reached!
% (30377)------------------------------
% (30377)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (30377)Termination reason: Time limit

% (30377)Memory used [KB]: 6396
% (30377)Time elapsed: 0.409 s
% (30377)------------------------------
% (30377)------------------------------
% (30400)Time limit reached!
% (30400)------------------------------
% (30400)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (30400)Termination reason: Time limit

% (30400)Memory used [KB]: 13560
% (30400)Time elapsed: 0.416 s
% (30400)------------------------------
% (30400)------------------------------
fof(f1943,plain,(
    ! [X1] : k1_xboole_0 = k4_xboole_0(sK1,k2_xboole_0(X1,sK1)) ),
    inference(backward_demodulation,[],[f1291,f1916])).

fof(f1916,plain,(
    sK1 = k4_xboole_0(sK1,sK3) ),
    inference(backward_demodulation,[],[f1129,f1915])).

fof(f1915,plain,(
    sK1 = k2_xboole_0(sK1,k4_xboole_0(sK1,sK3)) ),
    inference(forward_demodulation,[],[f1899,f625])).

fof(f625,plain,(
    sK1 = k2_xboole_0(sK1,sK1) ),
    inference(forward_demodulation,[],[f619,f28])).

fof(f619,plain,(
    k2_xboole_0(sK1,k1_xboole_0) = k2_xboole_0(sK1,sK1) ),
    inference(superposition,[],[f32,f586])).

fof(f586,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,sK1) ),
    inference(backward_demodulation,[],[f289,f571])).

fof(f571,plain,(
    sK1 = k4_xboole_0(sK1,k1_xboole_0) ),
    inference(superposition,[],[f138,f28])).

fof(f138,plain,(
    sK1 = k2_xboole_0(k4_xboole_0(sK1,k1_xboole_0),k1_xboole_0) ),
    inference(superposition,[],[f46,f75])).

fof(f75,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) ),
    inference(resolution,[],[f62,f47])).

fof(f62,plain,(
    r1_xboole_0(sK1,sK3) ),
    inference(resolution,[],[f26,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f26,plain,(
    r1_xboole_0(sK3,sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f289,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,k1_xboole_0)) ),
    inference(resolution,[],[f284,f47])).

fof(f284,plain,(
    r1_xboole_0(sK1,k1_xboole_0) ),
    inference(resolution,[],[f275,f62])).

fof(f275,plain,(
    ! [X1] :
      ( ~ r1_xboole_0(X1,sK3)
      | r1_xboole_0(X1,k1_xboole_0) ) ),
    inference(superposition,[],[f42,f99])).

fof(f99,plain,(
    sK3 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK3,sK1)) ),
    inference(superposition,[],[f46,f61])).

fof(f61,plain,(
    k1_xboole_0 = k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)) ),
    inference(resolution,[],[f26,f47])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X1)
      | ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

fof(f1899,plain,(
    k2_xboole_0(sK1,k4_xboole_0(sK1,sK3)) = k2_xboole_0(sK1,sK1) ),
    inference(superposition,[],[f595,f134])).

fof(f134,plain,(
    sK1 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK3)) ),
    inference(superposition,[],[f46,f75])).

fof(f595,plain,(
    ! [X0] : k2_xboole_0(sK1,X0) = k2_xboole_0(sK1,k2_xboole_0(k1_xboole_0,X0)) ),
    inference(forward_demodulation,[],[f580,f571])).

fof(f580,plain,(
    ! [X0] : k2_xboole_0(sK1,X0) = k2_xboole_0(k4_xboole_0(sK1,k1_xboole_0),k2_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[],[f41,f138])).

fof(f1129,plain,(
    k4_xboole_0(sK1,sK3) = k2_xboole_0(sK1,k4_xboole_0(sK1,sK3)) ),
    inference(superposition,[],[f141,f30])).

fof(f141,plain,(
    k4_xboole_0(sK1,sK3) = k2_xboole_0(k4_xboole_0(sK1,sK3),sK1) ),
    inference(forward_demodulation,[],[f135,f28])).

fof(f135,plain,(
    k2_xboole_0(k4_xboole_0(sK1,sK3),sK1) = k2_xboole_0(k4_xboole_0(sK1,sK3),k1_xboole_0) ),
    inference(superposition,[],[f32,f75])).

fof(f1291,plain,(
    ! [X1] : k1_xboole_0 = k4_xboole_0(sK1,k2_xboole_0(X1,k4_xboole_0(sK1,sK3))) ),
    inference(superposition,[],[f239,f30])).

fof(f239,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(sK1,k2_xboole_0(k4_xboole_0(sK1,sK3),X0)) ),
    inference(backward_demodulation,[],[f137,f237])).

fof(f237,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(forward_demodulation,[],[f232,f29])).

fof(f232,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(sK2,k2_xboole_0(sK2,X0)) ),
    inference(superposition,[],[f40,f209])).

fof(f137,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(sK1,k2_xboole_0(k4_xboole_0(sK1,sK3),X0)) ),
    inference(superposition,[],[f40,f75])).

fof(f4661,plain,(
    k4_xboole_0(sK1,sK2) = k4_xboole_0(sK1,k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f1966,f4645])).

fof(f4645,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK3,sK2) ),
    inference(forward_demodulation,[],[f4622,f2052])).

fof(f4622,plain,(
    k2_xboole_0(sK3,sK2) = k2_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(superposition,[],[f2594,f86])).

fof(f86,plain,(
    ! [X0] : k2_xboole_0(sK2,k2_xboole_0(sK3,X0)) = k2_xboole_0(sK0,k2_xboole_0(sK1,X0)) ),
    inference(forward_demodulation,[],[f80,f41])).

fof(f80,plain,(
    ! [X0] : k2_xboole_0(sK2,k2_xboole_0(sK3,X0)) = k2_xboole_0(k2_xboole_0(sK0,sK1),X0) ),
    inference(superposition,[],[f41,f24])).

fof(f2594,plain,(
    ! [X3] : k2_xboole_0(X3,sK2) = k2_xboole_0(sK2,k2_xboole_0(X3,sK2)) ),
    inference(superposition,[],[f1283,f30])).

fof(f1283,plain,(
    ! [X0] : k2_xboole_0(X0,sK2) = k2_xboole_0(k2_xboole_0(X0,sK2),sK2) ),
    inference(forward_demodulation,[],[f1277,f28])).

fof(f1277,plain,(
    ! [X0] : k2_xboole_0(k2_xboole_0(X0,sK2),sK2) = k2_xboole_0(k2_xboole_0(X0,sK2),k1_xboole_0) ),
    inference(superposition,[],[f32,f1239])).

fof(f1239,plain,(
    ! [X1] : k1_xboole_0 = k4_xboole_0(sK2,k2_xboole_0(X1,sK2)) ),
    inference(backward_demodulation,[],[f1062,f1210])).

fof(f1062,plain,(
    ! [X1] : k1_xboole_0 = k4_xboole_0(sK2,k2_xboole_0(X1,k4_xboole_0(sK2,sK0))) ),
    inference(superposition,[],[f243,f30])).

fof(f243,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK2,sK0),X0)) ),
    inference(backward_demodulation,[],[f92,f237])).

fof(f92,plain,(
    ! [X0] : k4_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK2,sK0),X0)) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f40,f53])).

fof(f1966,plain,(
    ! [X0] : k4_xboole_0(sK1,X0) = k4_xboole_0(sK1,k2_xboole_0(sK3,X0)) ),
    inference(superposition,[],[f40,f1916])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:52:34 EST 2020
% 0.21/0.35  % CPUTime    : 
% 0.22/0.53  % (30383)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.54  % (30386)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.54  % (30381)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.54  % (30382)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.54  % (30389)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.54  % (30390)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.54  % (30405)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.55  % (30391)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.55  % (30397)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.55  % (30400)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.55  % (30399)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.55  % (30394)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.55  % (30398)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.55  % (30402)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.56  % (30392)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.56  % (30392)Refutation not found, incomplete strategy% (30392)------------------------------
% 0.22/0.56  % (30392)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.57  % (30392)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.57  
% 1.50/0.57  % (30392)Memory used [KB]: 10618
% 1.50/0.57  % (30392)Time elapsed: 0.133 s
% 1.50/0.57  % (30392)------------------------------
% 1.50/0.57  % (30392)------------------------------
% 1.50/0.58  % (30395)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.67/0.58  % (30403)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.67/0.59  % (30378)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.67/0.59  % (30401)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.67/0.59  % (30387)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.67/0.59  % (30379)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.67/0.60  % (30376)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.67/0.60  % (30380)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.67/0.61  % (30393)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.67/0.61  % (30388)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.67/0.62  % (30404)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.67/0.62  % (30385)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.67/0.62  % (30377)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.67/0.62  % (30396)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.67/0.62  % (30375)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 2.20/0.69  % (30413)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.99/0.83  % (30393)Refutation found. Thanks to Tanya!
% 2.99/0.83  % SZS status Theorem for theBenchmark
% 2.99/0.83  % SZS output start Proof for theBenchmark
% 2.99/0.83  fof(f4702,plain,(
% 2.99/0.83    $false),
% 2.99/0.83    inference(subsumption_resolution,[],[f4701,f27])).
% 2.99/0.83  fof(f27,plain,(
% 2.99/0.83    sK1 != sK2),
% 2.99/0.83    inference(cnf_transformation,[],[f18])).
% 2.99/0.83  fof(f18,plain,(
% 2.99/0.83    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3))),
% 2.99/0.83    inference(flattening,[],[f17])).
% 2.99/0.83  fof(f17,plain,(
% 2.99/0.83    ? [X0,X1,X2,X3] : (X1 != X2 & (r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)))),
% 2.99/0.83    inference(ennf_transformation,[],[f16])).
% 2.99/0.83  fof(f16,negated_conjecture,(
% 2.99/0.83    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 2.99/0.83    inference(negated_conjecture,[],[f15])).
% 2.99/0.83  fof(f15,conjecture,(
% 2.99/0.83    ! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 2.99/0.83    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_xboole_1)).
% 2.99/0.83  fof(f4701,plain,(
% 2.99/0.83    sK1 = sK2),
% 2.99/0.83    inference(forward_demodulation,[],[f4700,f2052])).
% 2.99/0.83  fof(f2052,plain,(
% 2.99/0.83    sK1 = k2_xboole_0(sK1,sK2)),
% 2.99/0.83    inference(forward_demodulation,[],[f2046,f28])).
% 2.99/0.83  fof(f28,plain,(
% 2.99/0.83    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.99/0.83    inference(cnf_transformation,[],[f6])).
% 2.99/0.83  fof(f6,axiom,(
% 2.99/0.83    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 2.99/0.83    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 2.99/0.83  fof(f2046,plain,(
% 2.99/0.83    k2_xboole_0(sK1,sK2) = k2_xboole_0(sK1,k1_xboole_0)),
% 2.99/0.83    inference(superposition,[],[f32,f2015])).
% 2.99/0.83  fof(f2015,plain,(
% 2.99/0.83    k1_xboole_0 = k4_xboole_0(sK2,sK1)),
% 2.99/0.83    inference(superposition,[],[f1263,f78])).
% 2.99/0.83  fof(f78,plain,(
% 2.99/0.83    k1_xboole_0 = k4_xboole_0(sK2,k2_xboole_0(sK0,sK1))),
% 2.99/0.83    inference(superposition,[],[f29,f24])).
% 2.99/0.83  fof(f24,plain,(
% 2.99/0.83    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)),
% 2.99/0.83    inference(cnf_transformation,[],[f18])).
% 2.99/0.83  fof(f29,plain,(
% 2.99/0.83    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 2.99/0.83    inference(cnf_transformation,[],[f9])).
% 2.99/0.83  fof(f9,axiom,(
% 2.99/0.83    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 2.99/0.83    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
% 2.99/0.83  fof(f1263,plain,(
% 2.99/0.83    ( ! [X0] : (k4_xboole_0(sK2,X0) = k4_xboole_0(sK2,k2_xboole_0(sK0,X0))) )),
% 2.99/0.83    inference(superposition,[],[f40,f1210])).
% 2.99/0.83  fof(f1210,plain,(
% 2.99/0.83    sK2 = k4_xboole_0(sK2,sK0)),
% 2.99/0.83    inference(backward_demodulation,[],[f654,f1209])).
% 2.99/0.83  fof(f1209,plain,(
% 2.99/0.83    sK2 = k2_xboole_0(sK2,k4_xboole_0(sK2,sK0))),
% 2.99/0.83    inference(forward_demodulation,[],[f1194,f236])).
% 2.99/0.83  fof(f236,plain,(
% 2.99/0.83    sK2 = k2_xboole_0(sK2,sK2)),
% 2.99/0.83    inference(forward_demodulation,[],[f230,f28])).
% 2.99/0.83  fof(f230,plain,(
% 2.99/0.83    k2_xboole_0(sK2,k1_xboole_0) = k2_xboole_0(sK2,sK2)),
% 2.99/0.83    inference(superposition,[],[f32,f209])).
% 2.99/0.83  fof(f209,plain,(
% 2.99/0.83    k1_xboole_0 = k4_xboole_0(sK2,sK2)),
% 2.99/0.83    inference(forward_demodulation,[],[f196,f191])).
% 2.99/0.83  fof(f191,plain,(
% 2.99/0.83    sK2 = k4_xboole_0(sK2,k1_xboole_0)),
% 2.99/0.83    inference(superposition,[],[f93,f28])).
% 2.99/0.83  fof(f93,plain,(
% 2.99/0.83    sK2 = k2_xboole_0(k4_xboole_0(sK2,k1_xboole_0),k1_xboole_0)),
% 2.99/0.83    inference(superposition,[],[f46,f53])).
% 2.99/0.83  fof(f53,plain,(
% 2.99/0.83    k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0))),
% 2.99/0.83    inference(resolution,[],[f25,f47])).
% 2.99/0.83  fof(f47,plain,(
% 2.99/0.83    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 2.99/0.83    inference(definition_unfolding,[],[f37,f31])).
% 2.99/0.83  fof(f31,plain,(
% 2.99/0.83    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.99/0.83    inference(cnf_transformation,[],[f10])).
% 2.99/0.83  fof(f10,axiom,(
% 2.99/0.83    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.99/0.83    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.99/0.83  fof(f37,plain,(
% 2.99/0.83    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 2.99/0.83    inference(cnf_transformation,[],[f2])).
% 2.99/0.83  fof(f2,axiom,(
% 2.99/0.83    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 2.99/0.83    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 2.99/0.83  fof(f25,plain,(
% 2.99/0.83    r1_xboole_0(sK2,sK0)),
% 2.99/0.83    inference(cnf_transformation,[],[f18])).
% 2.99/0.83  fof(f46,plain,(
% 2.99/0.83    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 2.99/0.83    inference(definition_unfolding,[],[f33,f31])).
% 2.99/0.83  fof(f33,plain,(
% 2.99/0.83    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 2.99/0.83    inference(cnf_transformation,[],[f12])).
% 2.99/0.83  fof(f12,axiom,(
% 2.99/0.83    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 2.99/0.83    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).
% 2.99/0.83  fof(f196,plain,(
% 2.99/0.83    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK2,k1_xboole_0),sK2)),
% 2.99/0.83    inference(superposition,[],[f29,f93])).
% 2.99/0.83  fof(f1194,plain,(
% 2.99/0.83    k2_xboole_0(sK2,k4_xboole_0(sK2,sK0)) = k2_xboole_0(sK2,sK2)),
% 2.99/0.83    inference(superposition,[],[f212,f89])).
% 2.99/0.83  fof(f89,plain,(
% 2.99/0.83    sK2 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK2,sK0))),
% 2.99/0.83    inference(superposition,[],[f46,f53])).
% 2.99/0.83  fof(f212,plain,(
% 2.99/0.83    ( ! [X0] : (k2_xboole_0(sK2,X0) = k2_xboole_0(sK2,k2_xboole_0(k1_xboole_0,X0))) )),
% 2.99/0.83    inference(forward_demodulation,[],[f200,f191])).
% 2.99/0.83  fof(f200,plain,(
% 2.99/0.83    ( ! [X0] : (k2_xboole_0(sK2,X0) = k2_xboole_0(k4_xboole_0(sK2,k1_xboole_0),k2_xboole_0(k1_xboole_0,X0))) )),
% 2.99/0.83    inference(superposition,[],[f41,f93])).
% 2.99/0.83  fof(f41,plain,(
% 2.99/0.83    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 2.99/0.83    inference(cnf_transformation,[],[f11])).
% 2.99/0.83  fof(f11,axiom,(
% 2.99/0.83    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 2.99/0.83    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).
% 2.99/0.83  fof(f654,plain,(
% 2.99/0.83    k4_xboole_0(sK2,sK0) = k2_xboole_0(sK2,k4_xboole_0(sK2,sK0))),
% 2.99/0.83    inference(superposition,[],[f96,f30])).
% 2.99/0.83  fof(f30,plain,(
% 2.99/0.83    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 2.99/0.83    inference(cnf_transformation,[],[f1])).
% 2.99/0.83  fof(f1,axiom,(
% 2.99/0.83    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 2.99/0.83    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 2.99/0.83  fof(f96,plain,(
% 2.99/0.83    k4_xboole_0(sK2,sK0) = k2_xboole_0(k4_xboole_0(sK2,sK0),sK2)),
% 2.99/0.83    inference(forward_demodulation,[],[f90,f28])).
% 2.99/0.83  fof(f90,plain,(
% 2.99/0.83    k2_xboole_0(k4_xboole_0(sK2,sK0),sK2) = k2_xboole_0(k4_xboole_0(sK2,sK0),k1_xboole_0)),
% 2.99/0.83    inference(superposition,[],[f32,f53])).
% 2.99/0.83  fof(f40,plain,(
% 2.99/0.83    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 2.99/0.83    inference(cnf_transformation,[],[f8])).
% 2.99/0.83  fof(f8,axiom,(
% 2.99/0.83    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 2.99/0.83    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 2.99/0.83  fof(f32,plain,(
% 2.99/0.83    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.99/0.83    inference(cnf_transformation,[],[f7])).
% 2.99/0.83  fof(f7,axiom,(
% 2.99/0.83    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.99/0.83    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 2.99/0.83  fof(f4700,plain,(
% 2.99/0.83    sK2 = k2_xboole_0(sK1,sK2)),
% 2.99/0.83    inference(forward_demodulation,[],[f4699,f28])).
% 2.99/0.83  fof(f4699,plain,(
% 2.99/0.83    k2_xboole_0(sK1,sK2) = k2_xboole_0(sK2,k1_xboole_0)),
% 2.99/0.83    inference(forward_demodulation,[],[f4693,f30])).
% 2.99/0.83  fof(f4693,plain,(
% 2.99/0.83    k2_xboole_0(sK2,k1_xboole_0) = k2_xboole_0(sK2,sK1)),
% 2.99/0.83    inference(superposition,[],[f32,f4683])).
% 2.99/0.83  fof(f4683,plain,(
% 2.99/0.83    k1_xboole_0 = k4_xboole_0(sK1,sK2)),
% 2.99/0.83    inference(forward_demodulation,[],[f4661,f1943])).
% 2.99/0.84  % (30377)Time limit reached!
% 2.99/0.84  % (30377)------------------------------
% 2.99/0.84  % (30377)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.99/0.84  % (30377)Termination reason: Time limit
% 2.99/0.84  
% 2.99/0.84  % (30377)Memory used [KB]: 6396
% 2.99/0.84  % (30377)Time elapsed: 0.409 s
% 2.99/0.84  % (30377)------------------------------
% 2.99/0.84  % (30377)------------------------------
% 3.62/0.85  % (30400)Time limit reached!
% 3.62/0.85  % (30400)------------------------------
% 3.62/0.85  % (30400)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.62/0.85  % (30400)Termination reason: Time limit
% 3.62/0.85  
% 3.62/0.85  % (30400)Memory used [KB]: 13560
% 3.62/0.85  % (30400)Time elapsed: 0.416 s
% 3.62/0.85  % (30400)------------------------------
% 3.62/0.85  % (30400)------------------------------
% 3.62/0.85  fof(f1943,plain,(
% 3.62/0.85    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(sK1,k2_xboole_0(X1,sK1))) )),
% 3.62/0.85    inference(backward_demodulation,[],[f1291,f1916])).
% 3.62/0.85  fof(f1916,plain,(
% 3.62/0.85    sK1 = k4_xboole_0(sK1,sK3)),
% 3.62/0.85    inference(backward_demodulation,[],[f1129,f1915])).
% 3.62/0.85  fof(f1915,plain,(
% 3.62/0.85    sK1 = k2_xboole_0(sK1,k4_xboole_0(sK1,sK3))),
% 3.62/0.85    inference(forward_demodulation,[],[f1899,f625])).
% 3.62/0.85  fof(f625,plain,(
% 3.62/0.85    sK1 = k2_xboole_0(sK1,sK1)),
% 3.62/0.85    inference(forward_demodulation,[],[f619,f28])).
% 3.62/0.85  fof(f619,plain,(
% 3.62/0.85    k2_xboole_0(sK1,k1_xboole_0) = k2_xboole_0(sK1,sK1)),
% 3.62/0.85    inference(superposition,[],[f32,f586])).
% 3.62/0.85  fof(f586,plain,(
% 3.62/0.85    k1_xboole_0 = k4_xboole_0(sK1,sK1)),
% 3.62/0.85    inference(backward_demodulation,[],[f289,f571])).
% 3.62/0.85  fof(f571,plain,(
% 3.62/0.85    sK1 = k4_xboole_0(sK1,k1_xboole_0)),
% 3.62/0.85    inference(superposition,[],[f138,f28])).
% 3.62/0.85  fof(f138,plain,(
% 3.62/0.85    sK1 = k2_xboole_0(k4_xboole_0(sK1,k1_xboole_0),k1_xboole_0)),
% 3.62/0.85    inference(superposition,[],[f46,f75])).
% 3.62/0.85  fof(f75,plain,(
% 3.62/0.85    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK3))),
% 3.62/0.85    inference(resolution,[],[f62,f47])).
% 3.62/0.85  fof(f62,plain,(
% 3.62/0.85    r1_xboole_0(sK1,sK3)),
% 3.62/0.85    inference(resolution,[],[f26,f35])).
% 3.62/0.85  fof(f35,plain,(
% 3.62/0.85    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 3.62/0.85    inference(cnf_transformation,[],[f20])).
% 3.62/0.85  fof(f20,plain,(
% 3.62/0.85    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 3.62/0.85    inference(ennf_transformation,[],[f3])).
% 3.62/0.85  fof(f3,axiom,(
% 3.62/0.85    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 3.62/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 3.62/0.85  fof(f26,plain,(
% 3.62/0.85    r1_xboole_0(sK3,sK1)),
% 3.62/0.85    inference(cnf_transformation,[],[f18])).
% 3.62/0.85  fof(f289,plain,(
% 3.62/0.85    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,k1_xboole_0))),
% 3.62/0.85    inference(resolution,[],[f284,f47])).
% 3.62/0.85  fof(f284,plain,(
% 3.62/0.85    r1_xboole_0(sK1,k1_xboole_0)),
% 3.62/0.85    inference(resolution,[],[f275,f62])).
% 3.62/0.85  fof(f275,plain,(
% 3.62/0.85    ( ! [X1] : (~r1_xboole_0(X1,sK3) | r1_xboole_0(X1,k1_xboole_0)) )),
% 3.62/0.85    inference(superposition,[],[f42,f99])).
% 3.62/0.85  fof(f99,plain,(
% 3.62/0.85    sK3 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK3,sK1))),
% 3.62/0.85    inference(superposition,[],[f46,f61])).
% 3.62/0.85  fof(f61,plain,(
% 3.62/0.85    k1_xboole_0 = k4_xboole_0(sK3,k4_xboole_0(sK3,sK1))),
% 3.62/0.85    inference(resolution,[],[f26,f47])).
% 3.62/0.85  fof(f42,plain,(
% 3.62/0.85    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X1) | ~r1_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 3.62/0.85    inference(cnf_transformation,[],[f21])).
% 3.62/0.85  fof(f21,plain,(
% 3.62/0.85    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 3.62/0.85    inference(ennf_transformation,[],[f13])).
% 3.62/0.85  fof(f13,axiom,(
% 3.62/0.85    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 3.62/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).
% 3.62/0.85  fof(f1899,plain,(
% 3.62/0.85    k2_xboole_0(sK1,k4_xboole_0(sK1,sK3)) = k2_xboole_0(sK1,sK1)),
% 3.62/0.85    inference(superposition,[],[f595,f134])).
% 3.62/0.85  fof(f134,plain,(
% 3.62/0.85    sK1 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK3))),
% 3.62/0.85    inference(superposition,[],[f46,f75])).
% 3.62/0.85  fof(f595,plain,(
% 3.62/0.85    ( ! [X0] : (k2_xboole_0(sK1,X0) = k2_xboole_0(sK1,k2_xboole_0(k1_xboole_0,X0))) )),
% 3.62/0.85    inference(forward_demodulation,[],[f580,f571])).
% 3.62/0.85  fof(f580,plain,(
% 3.62/0.85    ( ! [X0] : (k2_xboole_0(sK1,X0) = k2_xboole_0(k4_xboole_0(sK1,k1_xboole_0),k2_xboole_0(k1_xboole_0,X0))) )),
% 3.62/0.85    inference(superposition,[],[f41,f138])).
% 3.62/0.85  fof(f1129,plain,(
% 3.62/0.85    k4_xboole_0(sK1,sK3) = k2_xboole_0(sK1,k4_xboole_0(sK1,sK3))),
% 3.62/0.85    inference(superposition,[],[f141,f30])).
% 3.62/0.85  fof(f141,plain,(
% 3.62/0.85    k4_xboole_0(sK1,sK3) = k2_xboole_0(k4_xboole_0(sK1,sK3),sK1)),
% 3.62/0.85    inference(forward_demodulation,[],[f135,f28])).
% 3.62/0.85  fof(f135,plain,(
% 3.62/0.85    k2_xboole_0(k4_xboole_0(sK1,sK3),sK1) = k2_xboole_0(k4_xboole_0(sK1,sK3),k1_xboole_0)),
% 3.62/0.85    inference(superposition,[],[f32,f75])).
% 3.62/0.85  fof(f1291,plain,(
% 3.62/0.85    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(sK1,k2_xboole_0(X1,k4_xboole_0(sK1,sK3)))) )),
% 3.62/0.85    inference(superposition,[],[f239,f30])).
% 3.62/0.85  fof(f239,plain,(
% 3.62/0.85    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(sK1,k2_xboole_0(k4_xboole_0(sK1,sK3),X0))) )),
% 3.62/0.85    inference(backward_demodulation,[],[f137,f237])).
% 3.62/0.85  fof(f237,plain,(
% 3.62/0.85    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 3.62/0.85    inference(forward_demodulation,[],[f232,f29])).
% 3.62/0.85  fof(f232,plain,(
% 3.62/0.85    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(sK2,k2_xboole_0(sK2,X0))) )),
% 3.62/0.85    inference(superposition,[],[f40,f209])).
% 3.62/0.85  fof(f137,plain,(
% 3.62/0.85    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(sK1,k2_xboole_0(k4_xboole_0(sK1,sK3),X0))) )),
% 3.62/0.85    inference(superposition,[],[f40,f75])).
% 3.62/0.85  fof(f4661,plain,(
% 3.62/0.85    k4_xboole_0(sK1,sK2) = k4_xboole_0(sK1,k2_xboole_0(sK0,sK1))),
% 3.62/0.85    inference(superposition,[],[f1966,f4645])).
% 3.62/0.85  fof(f4645,plain,(
% 3.62/0.85    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK3,sK2)),
% 3.62/0.85    inference(forward_demodulation,[],[f4622,f2052])).
% 3.62/0.85  fof(f4622,plain,(
% 3.62/0.85    k2_xboole_0(sK3,sK2) = k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),
% 3.62/0.85    inference(superposition,[],[f2594,f86])).
% 3.62/0.85  fof(f86,plain,(
% 3.62/0.85    ( ! [X0] : (k2_xboole_0(sK2,k2_xboole_0(sK3,X0)) = k2_xboole_0(sK0,k2_xboole_0(sK1,X0))) )),
% 3.62/0.85    inference(forward_demodulation,[],[f80,f41])).
% 3.62/0.85  fof(f80,plain,(
% 3.62/0.85    ( ! [X0] : (k2_xboole_0(sK2,k2_xboole_0(sK3,X0)) = k2_xboole_0(k2_xboole_0(sK0,sK1),X0)) )),
% 3.62/0.85    inference(superposition,[],[f41,f24])).
% 3.62/0.86  fof(f2594,plain,(
% 3.62/0.86    ( ! [X3] : (k2_xboole_0(X3,sK2) = k2_xboole_0(sK2,k2_xboole_0(X3,sK2))) )),
% 3.62/0.86    inference(superposition,[],[f1283,f30])).
% 3.62/0.86  fof(f1283,plain,(
% 3.62/0.86    ( ! [X0] : (k2_xboole_0(X0,sK2) = k2_xboole_0(k2_xboole_0(X0,sK2),sK2)) )),
% 3.62/0.86    inference(forward_demodulation,[],[f1277,f28])).
% 3.62/0.86  fof(f1277,plain,(
% 3.62/0.86    ( ! [X0] : (k2_xboole_0(k2_xboole_0(X0,sK2),sK2) = k2_xboole_0(k2_xboole_0(X0,sK2),k1_xboole_0)) )),
% 3.62/0.86    inference(superposition,[],[f32,f1239])).
% 3.62/0.86  fof(f1239,plain,(
% 3.62/0.86    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(sK2,k2_xboole_0(X1,sK2))) )),
% 3.62/0.86    inference(backward_demodulation,[],[f1062,f1210])).
% 3.62/0.86  fof(f1062,plain,(
% 3.62/0.86    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(sK2,k2_xboole_0(X1,k4_xboole_0(sK2,sK0)))) )),
% 3.62/0.86    inference(superposition,[],[f243,f30])).
% 3.62/0.86  fof(f243,plain,(
% 3.62/0.86    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK2,sK0),X0))) )),
% 3.62/0.86    inference(backward_demodulation,[],[f92,f237])).
% 3.62/0.86  fof(f92,plain,(
% 3.62/0.86    ( ! [X0] : (k4_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK2,sK0),X0)) = k4_xboole_0(k1_xboole_0,X0)) )),
% 3.62/0.86    inference(superposition,[],[f40,f53])).
% 3.62/0.86  fof(f1966,plain,(
% 3.62/0.86    ( ! [X0] : (k4_xboole_0(sK1,X0) = k4_xboole_0(sK1,k2_xboole_0(sK3,X0))) )),
% 3.62/0.86    inference(superposition,[],[f40,f1916])).
% 3.62/0.86  % SZS output end Proof for theBenchmark
% 3.62/0.86  % (30393)------------------------------
% 3.62/0.86  % (30393)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.62/0.86  % (30393)Termination reason: Refutation
% 3.62/0.86  
% 3.62/0.86  % (30393)Memory used [KB]: 3326
% 3.62/0.86  % (30393)Time elapsed: 0.380 s
% 3.62/0.86  % (30393)------------------------------
% 3.62/0.86  % (30393)------------------------------
% 3.62/0.86  % (30374)Success in time 0.496 s
%------------------------------------------------------------------------------
