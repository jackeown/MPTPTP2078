%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:39:05 EST 2020

% Result     : Theorem 1.50s
% Output     : Refutation 1.50s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 152 expanded)
%              Number of leaves         :   17 (  45 expanded)
%              Depth                    :   21
%              Number of atoms          :  122 ( 257 expanded)
%              Number of equality atoms :   39 (  79 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f303,plain,(
    $false ),
    inference(subsumption_resolution,[],[f299,f28])).

fof(f28,plain,(
    ~ r2_hidden(sK0,sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ~ r2_hidden(sK0,sK2)
    & r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f23])).

fof(f23,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_hidden(X0,X2)
        & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) )
   => ( ~ r2_hidden(sK0,sK2)
      & r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)
       => r2_hidden(X0,X2) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)
     => r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_zfmisc_1)).

fof(f299,plain,(
    r2_hidden(sK0,sK2) ),
    inference(superposition,[],[f49,f293])).

fof(f293,plain,(
    sK2 = k2_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(subsumption_resolution,[],[f290,f30])).

% (13238)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
fof(f30,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f290,plain,
    ( ~ r1_tarski(sK2,k2_xboole_0(sK2,k2_tarski(sK0,sK1)))
    | sK2 = k2_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(backward_demodulation,[],[f119,f288])).

fof(f288,plain,(
    ! [X2,X3] : k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2) ),
    inference(superposition,[],[f229,f31])).

fof(f31,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f229,plain,(
    ! [X2,X1] : k2_xboole_0(X1,X2) = k3_tarski(k2_tarski(X2,X1)) ),
    inference(superposition,[],[f31,f228])).

fof(f228,plain,(
    ! [X4,X5] : k2_tarski(X4,X5) = k2_tarski(X5,X4) ),
    inference(subsumption_resolution,[],[f227,f184])).

fof(f184,plain,(
    ! [X0,X1] : r2_hidden(X1,k2_tarski(X0,X1)) ),
    inference(superposition,[],[f183,f32])).

fof(f32,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f183,plain,(
    ! [X12,X13,X11] : r2_hidden(X11,k1_enumset1(X13,X12,X11)) ),
    inference(superposition,[],[f161,f98])).

fof(f98,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X2,X1,X0,X0) ),
    inference(superposition,[],[f40,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f40,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_enumset1)).

fof(f161,plain,(
    ! [X6,X4,X7,X5] : r2_hidden(X4,k2_enumset1(X4,X5,X6,X7)) ),
    inference(resolution,[],[f158,f37])).

% (13245)Refutation not found, incomplete strategy% (13245)------------------------------
% (13245)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (13245)Termination reason: Refutation not found, incomplete strategy

% (13245)Memory used [KB]: 1663
% (13245)Time elapsed: 0.146 s
% (13245)------------------------------
% (13245)------------------------------
fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_tarski(X0,X1),X2)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f158,plain,(
    ! [X2,X0,X3,X1] : r1_tarski(k2_tarski(X0,X1),k2_enumset1(X0,X1,X2,X3)) ),
    inference(forward_demodulation,[],[f154,f41])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f154,plain,(
    ! [X2,X0,X3,X1] : r1_tarski(k2_tarski(X0,X1),k3_enumset1(X0,X0,X1,X2,X3)) ),
    inference(superposition,[],[f151,f32])).

fof(f151,plain,(
    ! [X4,X2,X0,X3,X1] : r1_tarski(k1_enumset1(X0,X1,X2),k3_enumset1(X0,X1,X2,X3,X4)) ),
    inference(forward_demodulation,[],[f146,f42])).

fof(f42,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f146,plain,(
    ! [X4,X2,X0,X3,X1] : r1_tarski(k1_enumset1(X0,X1,X2),k4_enumset1(X0,X0,X1,X2,X3,X4)) ),
    inference(superposition,[],[f143,f36])).

fof(f143,plain,(
    ! [X4,X2,X0,X5,X3,X1] : r1_tarski(k2_enumset1(X0,X1,X2,X3),k4_enumset1(X0,X1,X2,X3,X4,X5)) ),
    inference(forward_demodulation,[],[f141,f43])).

fof(f43,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f141,plain,(
    ! [X4,X2,X0,X5,X3,X1] : r1_tarski(k2_enumset1(X0,X1,X2,X3),k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) ),
    inference(superposition,[],[f138,f41])).

fof(f138,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : r1_tarski(k3_enumset1(X0,X1,X2,X3,X4),k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) ),
    inference(forward_demodulation,[],[f136,f44])).

fof(f44,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

% (13243)Refutation not found, incomplete strategy% (13243)------------------------------
% (13243)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (13243)Termination reason: Refutation not found, incomplete strategy

% (13243)Memory used [KB]: 1791
% (13243)Time elapsed: 0.148 s
% (13243)------------------------------
% (13243)------------------------------
fof(f136,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : r1_tarski(k3_enumset1(X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) ),
    inference(superposition,[],[f133,f42])).

fof(f133,plain,(
    ! [X23,X21,X19,X17,X22,X20,X18,X16] : r1_tarski(k4_enumset1(X16,X17,X18,X19,X20,X21),k6_enumset1(X16,X17,X18,X19,X20,X21,X22,X23)) ),
    inference(superposition,[],[f30,f45])).

fof(f45,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_enumset1)).

fof(f227,plain,(
    ! [X4,X5] :
      ( k2_tarski(X4,X5) = k2_tarski(X5,X4)
      | ~ r2_hidden(X4,k2_tarski(X5,X4)) ) ),
    inference(subsumption_resolution,[],[f223,f65])).

fof(f65,plain,(
    ! [X0,X1] : r2_hidden(X0,k2_tarski(X0,X1)) ),
    inference(superposition,[],[f52,f33])).

fof(f33,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

fof(f52,plain,(
    ! [X0,X1] : r2_hidden(X0,k2_xboole_0(k1_tarski(X0),X1)) ),
    inference(superposition,[],[f49,f29])).

fof(f29,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f223,plain,(
    ! [X4,X5] :
      ( k2_tarski(X4,X5) = k2_tarski(X5,X4)
      | ~ r2_hidden(X5,k2_tarski(X5,X4))
      | ~ r2_hidden(X4,k2_tarski(X5,X4)) ) ),
    inference(resolution,[],[f216,f120])).

fof(f120,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,k2_tarski(X0,X2))
      | k2_tarski(X0,X2) = X1
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f93,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( r2_xboole_0(X1,X0)
        & r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_xboole_1)).

fof(f93,plain,(
    ! [X6,X8,X7] :
      ( r2_xboole_0(k2_tarski(X8,X6),X7)
      | ~ r2_hidden(X8,X7)
      | k2_tarski(X8,X6) = X7
      | ~ r2_hidden(X6,X7) ) ),
    inference(resolution,[],[f39,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( X0 != X1
        & r1_tarski(X0,X1) )
     => r2_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f216,plain,(
    ! [X0,X1] : r1_tarski(k2_tarski(X1,X0),k2_tarski(X0,X1)) ),
    inference(superposition,[],[f167,f32])).

fof(f167,plain,(
    ! [X12,X13,X11] : r1_tarski(k2_tarski(X11,X12),k1_enumset1(X13,X12,X11)) ),
    inference(superposition,[],[f158,f98])).

fof(f119,plain,
    ( ~ r1_tarski(sK2,k2_xboole_0(k2_tarski(sK0,sK1),sK2))
    | sK2 = k2_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(resolution,[],[f76,f35])).

fof(f76,plain,
    ( r2_xboole_0(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2)
    | sK2 = k2_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(resolution,[],[f34,f27])).

fof(f27,plain,(
    r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f49,plain,(
    ! [X2,X0,X1] : r2_hidden(X0,k2_xboole_0(k2_tarski(X0,X1),X2)) ),
    inference(resolution,[],[f37,f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:18:01 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.50  % (13230)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.50  % (13230)Refutation not found, incomplete strategy% (13230)------------------------------
% 0.21/0.50  % (13230)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (13248)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.51  % (13240)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.51  % (13230)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (13230)Memory used [KB]: 10746
% 0.21/0.51  % (13230)Time elapsed: 0.096 s
% 0.21/0.51  % (13230)------------------------------
% 0.21/0.51  % (13230)------------------------------
% 0.21/0.51  % (13226)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (13226)Refutation not found, incomplete strategy% (13226)------------------------------
% 0.21/0.51  % (13226)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (13226)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (13226)Memory used [KB]: 6140
% 0.21/0.51  % (13226)Time elapsed: 0.106 s
% 0.21/0.51  % (13226)------------------------------
% 0.21/0.51  % (13226)------------------------------
% 0.21/0.52  % (13248)Refutation not found, incomplete strategy% (13248)------------------------------
% 0.21/0.52  % (13248)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (13222)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.52  % (13248)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (13248)Memory used [KB]: 10746
% 0.21/0.52  % (13248)Time elapsed: 0.107 s
% 0.21/0.52  % (13248)------------------------------
% 0.21/0.52  % (13248)------------------------------
% 0.21/0.52  % (13222)Refutation not found, incomplete strategy% (13222)------------------------------
% 0.21/0.52  % (13222)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (13222)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (13222)Memory used [KB]: 1663
% 0.21/0.52  % (13222)Time elapsed: 0.082 s
% 0.21/0.52  % (13222)------------------------------
% 0.21/0.52  % (13222)------------------------------
% 0.21/0.52  % (13229)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.52  % (13244)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (13244)Refutation not found, incomplete strategy% (13244)------------------------------
% 0.21/0.52  % (13244)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (13244)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (13244)Memory used [KB]: 10746
% 0.21/0.52  % (13244)Time elapsed: 0.080 s
% 0.21/0.52  % (13244)------------------------------
% 0.21/0.52  % (13244)------------------------------
% 0.21/0.52  % (13223)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (13236)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.53  % (13245)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.53  % (13227)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.54  % (13250)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.54  % (13228)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.54  % (13249)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (13224)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (13246)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.54  % (13224)Refutation not found, incomplete strategy% (13224)------------------------------
% 0.21/0.54  % (13224)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (13224)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (13224)Memory used [KB]: 10746
% 0.21/0.54  % (13224)Time elapsed: 0.133 s
% 0.21/0.54  % (13224)------------------------------
% 0.21/0.54  % (13224)------------------------------
% 0.21/0.54  % (13242)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.54  % (13225)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (13242)Refutation not found, incomplete strategy% (13242)------------------------------
% 0.21/0.54  % (13242)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (13242)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (13242)Memory used [KB]: 10746
% 0.21/0.54  % (13242)Time elapsed: 0.139 s
% 0.21/0.54  % (13242)------------------------------
% 0.21/0.54  % (13242)------------------------------
% 1.50/0.54  % (13241)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.50/0.54  % (13237)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.50/0.54  % (13234)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.50/0.54  % (13237)Refutation not found, incomplete strategy% (13237)------------------------------
% 1.50/0.54  % (13237)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.54  % (13237)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.54  
% 1.50/0.54  % (13237)Memory used [KB]: 6140
% 1.50/0.54  % (13237)Time elapsed: 0.137 s
% 1.50/0.54  % (13237)------------------------------
% 1.50/0.54  % (13237)------------------------------
% 1.50/0.54  % (13251)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.50/0.55  % (13233)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.50/0.55  % (13239)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.50/0.55  % (13231)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.50/0.55  % (13233)Refutation not found, incomplete strategy% (13233)------------------------------
% 1.50/0.55  % (13233)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.55  % (13233)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.55  
% 1.50/0.55  % (13233)Memory used [KB]: 10618
% 1.50/0.55  % (13233)Time elapsed: 0.146 s
% 1.50/0.55  % (13233)------------------------------
% 1.50/0.55  % (13233)------------------------------
% 1.50/0.55  % (13231)Refutation not found, incomplete strategy% (13231)------------------------------
% 1.50/0.55  % (13231)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.55  % (13231)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.55  
% 1.50/0.55  % (13231)Memory used [KB]: 10618
% 1.50/0.55  % (13231)Time elapsed: 0.147 s
% 1.50/0.55  % (13231)------------------------------
% 1.50/0.55  % (13231)------------------------------
% 1.50/0.55  % (13243)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.50/0.55  % (13229)Refutation found. Thanks to Tanya!
% 1.50/0.55  % SZS status Theorem for theBenchmark
% 1.50/0.55  % SZS output start Proof for theBenchmark
% 1.50/0.55  fof(f303,plain,(
% 1.50/0.55    $false),
% 1.50/0.55    inference(subsumption_resolution,[],[f299,f28])).
% 1.50/0.55  fof(f28,plain,(
% 1.50/0.55    ~r2_hidden(sK0,sK2)),
% 1.50/0.55    inference(cnf_transformation,[],[f24])).
% 1.50/0.55  fof(f24,plain,(
% 1.50/0.55    ~r2_hidden(sK0,sK2) & r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2)),
% 1.50/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f23])).
% 1.50/0.55  fof(f23,plain,(
% 1.50/0.55    ? [X0,X1,X2] : (~r2_hidden(X0,X2) & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)) => (~r2_hidden(sK0,sK2) & r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2))),
% 1.50/0.55    introduced(choice_axiom,[])).
% 1.50/0.55  fof(f19,plain,(
% 1.50/0.55    ? [X0,X1,X2] : (~r2_hidden(X0,X2) & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2))),
% 1.50/0.55    inference(ennf_transformation,[],[f17])).
% 1.50/0.55  fof(f17,negated_conjecture,(
% 1.50/0.55    ~! [X0,X1,X2] : (r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) => r2_hidden(X0,X2))),
% 1.50/0.55    inference(negated_conjecture,[],[f16])).
% 1.50/0.55  fof(f16,conjecture,(
% 1.50/0.55    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) => r2_hidden(X0,X2))),
% 1.50/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_zfmisc_1)).
% 1.50/0.55  fof(f299,plain,(
% 1.50/0.55    r2_hidden(sK0,sK2)),
% 1.50/0.55    inference(superposition,[],[f49,f293])).
% 1.50/0.55  fof(f293,plain,(
% 1.50/0.55    sK2 = k2_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 1.50/0.55    inference(subsumption_resolution,[],[f290,f30])).
% 1.50/0.55  % (13238)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.50/0.55  fof(f30,plain,(
% 1.50/0.55    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.50/0.55    inference(cnf_transformation,[],[f3])).
% 1.50/0.55  fof(f3,axiom,(
% 1.50/0.55    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.50/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.50/0.55  fof(f290,plain,(
% 1.50/0.55    ~r1_tarski(sK2,k2_xboole_0(sK2,k2_tarski(sK0,sK1))) | sK2 = k2_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 1.50/0.55    inference(backward_demodulation,[],[f119,f288])).
% 1.50/0.55  fof(f288,plain,(
% 1.50/0.55    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2)) )),
% 1.50/0.55    inference(superposition,[],[f229,f31])).
% 1.50/0.55  fof(f31,plain,(
% 1.50/0.55    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.50/0.55    inference(cnf_transformation,[],[f14])).
% 1.50/0.55  fof(f14,axiom,(
% 1.50/0.55    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.50/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.50/0.55  fof(f229,plain,(
% 1.50/0.55    ( ! [X2,X1] : (k2_xboole_0(X1,X2) = k3_tarski(k2_tarski(X2,X1))) )),
% 1.50/0.55    inference(superposition,[],[f31,f228])).
% 1.50/0.55  fof(f228,plain,(
% 1.50/0.55    ( ! [X4,X5] : (k2_tarski(X4,X5) = k2_tarski(X5,X4)) )),
% 1.50/0.55    inference(subsumption_resolution,[],[f227,f184])).
% 1.50/0.55  fof(f184,plain,(
% 1.50/0.55    ( ! [X0,X1] : (r2_hidden(X1,k2_tarski(X0,X1))) )),
% 1.50/0.55    inference(superposition,[],[f183,f32])).
% 1.50/0.55  fof(f32,plain,(
% 1.50/0.55    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.50/0.55    inference(cnf_transformation,[],[f8])).
% 1.50/0.55  fof(f8,axiom,(
% 1.50/0.55    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.50/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.50/0.55  fof(f183,plain,(
% 1.50/0.55    ( ! [X12,X13,X11] : (r2_hidden(X11,k1_enumset1(X13,X12,X11))) )),
% 1.50/0.55    inference(superposition,[],[f161,f98])).
% 1.50/0.55  fof(f98,plain,(
% 1.50/0.55    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X2,X1,X0,X0)) )),
% 1.50/0.55    inference(superposition,[],[f40,f36])).
% 1.50/0.55  fof(f36,plain,(
% 1.50/0.55    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.50/0.55    inference(cnf_transformation,[],[f9])).
% 1.50/0.55  fof(f9,axiom,(
% 1.50/0.55    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.50/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.50/0.55  fof(f40,plain,(
% 1.50/0.55    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0)) )),
% 1.50/0.55    inference(cnf_transformation,[],[f4])).
% 1.50/0.55  fof(f4,axiom,(
% 1.50/0.55    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0)),
% 1.50/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_enumset1)).
% 1.50/0.55  fof(f161,plain,(
% 1.50/0.55    ( ! [X6,X4,X7,X5] : (r2_hidden(X4,k2_enumset1(X4,X5,X6,X7))) )),
% 1.50/0.55    inference(resolution,[],[f158,f37])).
% 1.50/0.55  % (13245)Refutation not found, incomplete strategy% (13245)------------------------------
% 1.50/0.55  % (13245)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.55  % (13245)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.55  
% 1.50/0.55  % (13245)Memory used [KB]: 1663
% 1.50/0.55  % (13245)Time elapsed: 0.146 s
% 1.50/0.55  % (13245)------------------------------
% 1.50/0.55  % (13245)------------------------------
% 1.50/0.55  fof(f37,plain,(
% 1.50/0.55    ( ! [X2,X0,X1] : (~r1_tarski(k2_tarski(X0,X1),X2) | r2_hidden(X0,X2)) )),
% 1.50/0.55    inference(cnf_transformation,[],[f26])).
% 1.50/0.55  fof(f26,plain,(
% 1.50/0.55    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 1.50/0.55    inference(flattening,[],[f25])).
% 1.50/0.55  fof(f25,plain,(
% 1.50/0.55    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 1.50/0.55    inference(nnf_transformation,[],[f15])).
% 1.50/0.55  fof(f15,axiom,(
% 1.50/0.55    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 1.50/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 1.50/0.55  fof(f158,plain,(
% 1.50/0.55    ( ! [X2,X0,X3,X1] : (r1_tarski(k2_tarski(X0,X1),k2_enumset1(X0,X1,X2,X3))) )),
% 1.50/0.55    inference(forward_demodulation,[],[f154,f41])).
% 1.50/0.55  fof(f41,plain,(
% 1.50/0.55    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 1.50/0.55    inference(cnf_transformation,[],[f10])).
% 1.50/0.55  fof(f10,axiom,(
% 1.50/0.55    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 1.50/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.50/0.55  fof(f154,plain,(
% 1.50/0.55    ( ! [X2,X0,X3,X1] : (r1_tarski(k2_tarski(X0,X1),k3_enumset1(X0,X0,X1,X2,X3))) )),
% 1.50/0.55    inference(superposition,[],[f151,f32])).
% 1.50/0.55  fof(f151,plain,(
% 1.50/0.55    ( ! [X4,X2,X0,X3,X1] : (r1_tarski(k1_enumset1(X0,X1,X2),k3_enumset1(X0,X1,X2,X3,X4))) )),
% 1.50/0.55    inference(forward_demodulation,[],[f146,f42])).
% 1.50/0.55  fof(f42,plain,(
% 1.50/0.55    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.50/0.55    inference(cnf_transformation,[],[f11])).
% 1.50/0.55  fof(f11,axiom,(
% 1.50/0.55    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.50/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 1.50/0.55  fof(f146,plain,(
% 1.50/0.55    ( ! [X4,X2,X0,X3,X1] : (r1_tarski(k1_enumset1(X0,X1,X2),k4_enumset1(X0,X0,X1,X2,X3,X4))) )),
% 1.50/0.55    inference(superposition,[],[f143,f36])).
% 1.50/0.55  fof(f143,plain,(
% 1.50/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (r1_tarski(k2_enumset1(X0,X1,X2,X3),k4_enumset1(X0,X1,X2,X3,X4,X5))) )),
% 1.50/0.55    inference(forward_demodulation,[],[f141,f43])).
% 1.50/0.55  fof(f43,plain,(
% 1.50/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 1.50/0.55    inference(cnf_transformation,[],[f12])).
% 1.50/0.55  fof(f12,axiom,(
% 1.50/0.55    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 1.50/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 1.50/0.55  fof(f141,plain,(
% 1.50/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (r1_tarski(k2_enumset1(X0,X1,X2,X3),k5_enumset1(X0,X0,X1,X2,X3,X4,X5))) )),
% 1.50/0.55    inference(superposition,[],[f138,f41])).
% 1.50/0.55  fof(f138,plain,(
% 1.50/0.55    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tarski(k3_enumset1(X0,X1,X2,X3,X4),k5_enumset1(X0,X1,X2,X3,X4,X5,X6))) )),
% 1.50/0.55    inference(forward_demodulation,[],[f136,f44])).
% 1.50/0.55  fof(f44,plain,(
% 1.50/0.55    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.50/0.55    inference(cnf_transformation,[],[f13])).
% 1.50/0.55  fof(f13,axiom,(
% 1.50/0.55    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 1.50/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 1.50/0.55  % (13243)Refutation not found, incomplete strategy% (13243)------------------------------
% 1.50/0.55  % (13243)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.55  % (13243)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.55  
% 1.50/0.55  % (13243)Memory used [KB]: 1791
% 1.50/0.55  % (13243)Time elapsed: 0.148 s
% 1.50/0.55  % (13243)------------------------------
% 1.50/0.55  % (13243)------------------------------
% 1.50/0.55  fof(f136,plain,(
% 1.50/0.55    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tarski(k3_enumset1(X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6))) )),
% 1.50/0.55    inference(superposition,[],[f133,f42])).
% 1.50/0.55  fof(f133,plain,(
% 1.50/0.55    ( ! [X23,X21,X19,X17,X22,X20,X18,X16] : (r1_tarski(k4_enumset1(X16,X17,X18,X19,X20,X21),k6_enumset1(X16,X17,X18,X19,X20,X21,X22,X23))) )),
% 1.50/0.55    inference(superposition,[],[f30,f45])).
% 1.50/0.55  fof(f45,plain,(
% 1.50/0.55    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7))) )),
% 1.50/0.55    inference(cnf_transformation,[],[f6])).
% 1.50/0.55  fof(f6,axiom,(
% 1.50/0.55    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7))),
% 1.50/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_enumset1)).
% 1.50/0.55  fof(f227,plain,(
% 1.50/0.55    ( ! [X4,X5] : (k2_tarski(X4,X5) = k2_tarski(X5,X4) | ~r2_hidden(X4,k2_tarski(X5,X4))) )),
% 1.50/0.55    inference(subsumption_resolution,[],[f223,f65])).
% 1.50/0.55  fof(f65,plain,(
% 1.50/0.55    ( ! [X0,X1] : (r2_hidden(X0,k2_tarski(X0,X1))) )),
% 1.50/0.55    inference(superposition,[],[f52,f33])).
% 1.50/0.55  fof(f33,plain,(
% 1.50/0.55    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 1.50/0.55    inference(cnf_transformation,[],[f5])).
% 1.50/0.55  fof(f5,axiom,(
% 1.50/0.55    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 1.50/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).
% 1.50/0.55  fof(f52,plain,(
% 1.50/0.55    ( ! [X0,X1] : (r2_hidden(X0,k2_xboole_0(k1_tarski(X0),X1))) )),
% 1.50/0.55    inference(superposition,[],[f49,f29])).
% 1.50/0.55  fof(f29,plain,(
% 1.50/0.55    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.50/0.55    inference(cnf_transformation,[],[f7])).
% 1.50/0.55  fof(f7,axiom,(
% 1.50/0.55    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.50/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.50/0.55  fof(f223,plain,(
% 1.50/0.55    ( ! [X4,X5] : (k2_tarski(X4,X5) = k2_tarski(X5,X4) | ~r2_hidden(X5,k2_tarski(X5,X4)) | ~r2_hidden(X4,k2_tarski(X5,X4))) )),
% 1.50/0.55    inference(resolution,[],[f216,f120])).
% 1.50/0.55  fof(f120,plain,(
% 1.50/0.55    ( ! [X2,X0,X1] : (~r1_tarski(X1,k2_tarski(X0,X2)) | k2_tarski(X0,X2) = X1 | ~r2_hidden(X2,X1) | ~r2_hidden(X0,X1)) )),
% 1.50/0.55    inference(resolution,[],[f93,f35])).
% 1.50/0.55  fof(f35,plain,(
% 1.50/0.55    ( ! [X0,X1] : (~r2_xboole_0(X1,X0) | ~r1_tarski(X0,X1)) )),
% 1.50/0.55    inference(cnf_transformation,[],[f22])).
% 1.50/0.55  fof(f22,plain,(
% 1.50/0.55    ! [X0,X1] : (~r2_xboole_0(X1,X0) | ~r1_tarski(X0,X1))),
% 1.50/0.55    inference(ennf_transformation,[],[f2])).
% 1.50/0.55  fof(f2,axiom,(
% 1.50/0.55    ! [X0,X1] : ~(r2_xboole_0(X1,X0) & r1_tarski(X0,X1))),
% 1.50/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_xboole_1)).
% 1.50/0.55  fof(f93,plain,(
% 1.50/0.55    ( ! [X6,X8,X7] : (r2_xboole_0(k2_tarski(X8,X6),X7) | ~r2_hidden(X8,X7) | k2_tarski(X8,X6) = X7 | ~r2_hidden(X6,X7)) )),
% 1.50/0.55    inference(resolution,[],[f39,f34])).
% 1.50/0.55  fof(f34,plain,(
% 1.50/0.55    ( ! [X0,X1] : (~r1_tarski(X0,X1) | X0 = X1 | r2_xboole_0(X0,X1)) )),
% 1.50/0.55    inference(cnf_transformation,[],[f21])).
% 1.50/0.55  fof(f21,plain,(
% 1.50/0.55    ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1))),
% 1.50/0.55    inference(flattening,[],[f20])).
% 1.50/0.55  fof(f20,plain,(
% 1.50/0.55    ! [X0,X1] : (r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1)))),
% 1.50/0.55    inference(ennf_transformation,[],[f18])).
% 1.50/0.55  fof(f18,plain,(
% 1.50/0.55    ! [X0,X1] : ((X0 != X1 & r1_tarski(X0,X1)) => r2_xboole_0(X0,X1))),
% 1.50/0.55    inference(unused_predicate_definition_removal,[],[f1])).
% 1.50/0.55  fof(f1,axiom,(
% 1.50/0.55    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 1.50/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).
% 1.50/0.55  fof(f39,plain,(
% 1.50/0.55    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 1.50/0.55    inference(cnf_transformation,[],[f26])).
% 1.50/0.55  fof(f216,plain,(
% 1.50/0.55    ( ! [X0,X1] : (r1_tarski(k2_tarski(X1,X0),k2_tarski(X0,X1))) )),
% 1.50/0.55    inference(superposition,[],[f167,f32])).
% 1.50/0.55  fof(f167,plain,(
% 1.50/0.55    ( ! [X12,X13,X11] : (r1_tarski(k2_tarski(X11,X12),k1_enumset1(X13,X12,X11))) )),
% 1.50/0.55    inference(superposition,[],[f158,f98])).
% 1.50/0.55  fof(f119,plain,(
% 1.50/0.55    ~r1_tarski(sK2,k2_xboole_0(k2_tarski(sK0,sK1),sK2)) | sK2 = k2_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 1.50/0.55    inference(resolution,[],[f76,f35])).
% 1.50/0.55  fof(f76,plain,(
% 1.50/0.55    r2_xboole_0(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2) | sK2 = k2_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 1.50/0.55    inference(resolution,[],[f34,f27])).
% 1.50/0.55  fof(f27,plain,(
% 1.50/0.55    r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2)),
% 1.50/0.55    inference(cnf_transformation,[],[f24])).
% 1.50/0.55  fof(f49,plain,(
% 1.50/0.55    ( ! [X2,X0,X1] : (r2_hidden(X0,k2_xboole_0(k2_tarski(X0,X1),X2))) )),
% 1.50/0.55    inference(resolution,[],[f37,f30])).
% 1.50/0.55  % SZS output end Proof for theBenchmark
% 1.50/0.55  % (13229)------------------------------
% 1.50/0.55  % (13229)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.55  % (13229)Termination reason: Refutation
% 1.50/0.55  
% 1.50/0.55  % (13229)Memory used [KB]: 6396
% 1.50/0.55  % (13229)Time elapsed: 0.143 s
% 1.50/0.55  % (13229)------------------------------
% 1.50/0.55  % (13229)------------------------------
% 1.50/0.56  % (13221)Success in time 0.19 s
%------------------------------------------------------------------------------
