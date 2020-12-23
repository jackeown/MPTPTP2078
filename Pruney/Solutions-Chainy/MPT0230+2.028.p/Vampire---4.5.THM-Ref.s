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
% DateTime   : Thu Dec  3 12:36:38 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 1.52s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 271 expanded)
%              Number of leaves         :   16 (  85 expanded)
%              Depth                    :   20
%              Number of atoms          :  115 ( 377 expanded)
%              Number of equality atoms :   88 ( 300 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f413,plain,(
    $false ),
    inference(subsumption_resolution,[],[f412,f28])).

fof(f28,plain,(
    sK0 != sK2 ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( X0 != X2
      & X0 != X1
      & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( X0 != X2
          & X0 != X1
          & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1,X2] :
      ~ ( X0 != X2
        & X0 != X1
        & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_zfmisc_1)).

fof(f412,plain,(
    sK0 = sK2 ),
    inference(subsumption_resolution,[],[f405,f27])).

fof(f27,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f23])).

fof(f405,plain,
    ( sK0 = sK1
    | sK0 = sK2 ),
    inference(resolution,[],[f339,f99])).

fof(f99,plain,(
    ! [X4,X2,X1] : r2_hidden(X4,k3_enumset1(X4,X4,X4,X1,X2)) ),
    inference(equality_resolution,[],[f98])).

fof(f98,plain,(
    ! [X4,X2,X3,X1] :
      ( r2_hidden(X4,X3)
      | k3_enumset1(X4,X4,X4,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X0 != X4
      | r2_hidden(X4,X3)
      | k3_enumset1(X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f58,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f44,f51])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f44,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f58,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X0 != X4
      | r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(f339,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,k3_enumset1(sK0,sK0,sK0,sK1,sK2))
      | sK1 = X5
      | sK2 = X5 ) ),
    inference(duplicate_literal_removal,[],[f332])).

fof(f332,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,k3_enumset1(sK0,sK0,sK0,sK1,sK2))
      | sK1 = X5
      | sK1 = X5
      | sK2 = X5 ) ),
    inference(superposition,[],[f100,f229])).

fof(f229,plain,(
    k3_enumset1(sK1,sK1,sK1,sK1,sK2) = k3_enumset1(sK0,sK0,sK0,sK1,sK2) ),
    inference(forward_demodulation,[],[f228,f71])).

% (3646)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% (3645)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% (3629)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% (3648)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% (3639)Refutation not found, incomplete strategy% (3639)------------------------------
% (3639)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (3639)Termination reason: Refutation not found, incomplete strategy

% (3633)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% (3639)Memory used [KB]: 10618
% (3639)Time elapsed: 0.152 s
% (3639)------------------------------
% (3639)------------------------------
% (3637)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% (3649)Refutation not found, incomplete strategy% (3649)------------------------------
% (3649)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (3649)Termination reason: Refutation not found, incomplete strategy

% (3649)Memory used [KB]: 6268
% (3649)Time elapsed: 0.190 s
% (3649)------------------------------
% (3649)------------------------------
fof(f71,plain,(
    ! [X2,X0,X1] : k3_enumset1(X0,X0,X0,X1,X2) = k3_enumset1(X1,X1,X1,X2,X0) ),
    inference(definition_unfolding,[],[f41,f61,f61])).

fof(f41,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_enumset1)).

fof(f228,plain,(
    k3_enumset1(sK1,sK1,sK1,sK1,sK2) = k3_enumset1(sK1,sK1,sK1,sK2,sK0) ),
    inference(forward_demodulation,[],[f222,f29])).

fof(f29,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f222,plain,(
    k3_enumset1(sK1,sK1,sK1,sK2,sK0) = k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK2),k1_xboole_0) ),
    inference(superposition,[],[f80,f170])).

fof(f170,plain,(
    k1_xboole_0 = k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK2)) ),
    inference(backward_demodulation,[],[f133,f169])).

fof(f169,plain,(
    k1_xboole_0 = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    inference(backward_demodulation,[],[f164,f168])).

fof(f168,plain,(
    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0) ),
    inference(superposition,[],[f66,f154])).

fof(f154,plain,(
    k1_xboole_0 = k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    inference(forward_demodulation,[],[f139,f101])).

fof(f101,plain,(
    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK2))) ),
    inference(resolution,[],[f65,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f38,f37])).

fof(f37,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f65,plain,(
    r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK2)) ),
    inference(definition_unfolding,[],[f26,f63,f62])).

fof(f62,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f34,f61])).

fof(f34,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f63,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f30,f62])).

fof(f30,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f26,plain,(
    r1_tarski(k1_tarski(sK0),k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f23])).

fof(f139,plain,(
    k1_xboole_0 = k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK2)))) ),
    inference(resolution,[],[f134,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f40,f37])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f134,plain,(
    r1_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK2))) ),
    inference(superposition,[],[f32,f101])).

fof(f32,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f66,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f31,f37])).

fof(f31,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f164,plain,(
    k1_xboole_0 = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0)) ),
    inference(superposition,[],[f64,f154])).

fof(f64,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f36,f37])).

fof(f36,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f133,plain,(
    k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK2)) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    inference(superposition,[],[f64,f101])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k5_xboole_0(k3_enumset1(X0,X0,X0,X1,X2),k4_xboole_0(k3_enumset1(X3,X3,X3,X3,X3),k3_enumset1(X0,X0,X0,X1,X2))) ),
    inference(definition_unfolding,[],[f52,f51,f35,f61,f63])).

fof(f35,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f52,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

fof(f100,plain,(
    ! [X4,X2,X0,X1] :
      ( X0 = X4
      | X1 = X4
      | X2 = X4
      | ~ r2_hidden(X4,k3_enumset1(X0,X0,X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f84])).

fof(f84,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X0 = X4
      | X1 = X4
      | X2 = X4
      | ~ r2_hidden(X4,X3)
      | k3_enumset1(X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f57,f61])).

fof(f57,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X0 = X4
      | X1 = X4
      | X2 = X4
      | ~ r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:52:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (3625)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.49  % (3641)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.49  % (3641)Refutation not found, incomplete strategy% (3641)------------------------------
% 0.22/0.49  % (3641)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (3641)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (3641)Memory used [KB]: 1791
% 0.22/0.49  % (3641)Time elapsed: 0.074 s
% 0.22/0.49  % (3641)------------------------------
% 0.22/0.49  % (3641)------------------------------
% 0.22/0.55  % (3628)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.56  % (3624)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.56  % (3623)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.57  % (3623)Refutation not found, incomplete strategy% (3623)------------------------------
% 0.22/0.57  % (3623)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (3623)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.57  
% 0.22/0.57  % (3623)Memory used [KB]: 1663
% 0.22/0.57  % (3623)Time elapsed: 0.119 s
% 0.22/0.57  % (3623)------------------------------
% 0.22/0.57  % (3623)------------------------------
% 0.22/0.57  % (3632)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.57  % (3649)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.57  % (3639)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.58  % (3635)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.58  % (3635)Refutation not found, incomplete strategy% (3635)------------------------------
% 0.22/0.58  % (3635)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.58  % (3635)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.58  
% 0.22/0.58  % (3635)Memory used [KB]: 10618
% 0.22/0.58  % (3635)Time elapsed: 0.155 s
% 0.22/0.58  % (3635)------------------------------
% 0.22/0.58  % (3635)------------------------------
% 0.22/0.58  % (3636)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.58  % (3640)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.58  % (3631)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.58  % (3653)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.58  % (3640)Refutation found. Thanks to Tanya!
% 0.22/0.58  % SZS status Theorem for theBenchmark
% 0.22/0.58  % SZS output start Proof for theBenchmark
% 0.22/0.58  fof(f413,plain,(
% 0.22/0.58    $false),
% 0.22/0.58    inference(subsumption_resolution,[],[f412,f28])).
% 0.22/0.58  fof(f28,plain,(
% 0.22/0.58    sK0 != sK2),
% 0.22/0.58    inference(cnf_transformation,[],[f23])).
% 0.22/0.58  fof(f23,plain,(
% 0.22/0.58    ? [X0,X1,X2] : (X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 0.22/0.58    inference(ennf_transformation,[],[f21])).
% 0.22/0.58  fof(f21,negated_conjecture,(
% 0.22/0.58    ~! [X0,X1,X2] : ~(X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 0.22/0.58    inference(negated_conjecture,[],[f20])).
% 0.22/0.58  fof(f20,conjecture,(
% 0.22/0.58    ! [X0,X1,X2] : ~(X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_zfmisc_1)).
% 0.22/0.58  fof(f412,plain,(
% 0.22/0.58    sK0 = sK2),
% 0.22/0.58    inference(subsumption_resolution,[],[f405,f27])).
% 0.22/0.58  fof(f27,plain,(
% 0.22/0.58    sK0 != sK1),
% 0.22/0.58    inference(cnf_transformation,[],[f23])).
% 0.22/0.58  fof(f405,plain,(
% 0.22/0.58    sK0 = sK1 | sK0 = sK2),
% 0.22/0.58    inference(resolution,[],[f339,f99])).
% 0.22/0.58  fof(f99,plain,(
% 0.22/0.58    ( ! [X4,X2,X1] : (r2_hidden(X4,k3_enumset1(X4,X4,X4,X1,X2))) )),
% 0.22/0.58    inference(equality_resolution,[],[f98])).
% 0.22/0.58  fof(f98,plain,(
% 0.22/0.58    ( ! [X4,X2,X3,X1] : (r2_hidden(X4,X3) | k3_enumset1(X4,X4,X4,X1,X2) != X3) )),
% 0.22/0.58    inference(equality_resolution,[],[f83])).
% 0.22/0.58  fof(f83,plain,(
% 0.22/0.58    ( ! [X4,X2,X0,X3,X1] : (X0 != X4 | r2_hidden(X4,X3) | k3_enumset1(X0,X0,X0,X1,X2) != X3) )),
% 0.22/0.58    inference(definition_unfolding,[],[f58,f61])).
% 0.22/0.58  fof(f61,plain,(
% 0.22/0.58    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 0.22/0.58    inference(definition_unfolding,[],[f44,f51])).
% 0.22/0.58  fof(f51,plain,(
% 0.22/0.58    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f18])).
% 0.22/0.58  fof(f18,axiom,(
% 0.22/0.58    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.22/0.58  fof(f44,plain,(
% 0.22/0.58    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f17])).
% 0.22/0.58  fof(f17,axiom,(
% 0.22/0.58    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.22/0.58  fof(f58,plain,(
% 0.22/0.58    ( ! [X4,X2,X0,X3,X1] : (X0 != X4 | r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 0.22/0.58    inference(cnf_transformation,[],[f25])).
% 0.22/0.58  fof(f25,plain,(
% 0.22/0.58    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 0.22/0.58    inference(ennf_transformation,[],[f10])).
% 0.22/0.58  fof(f10,axiom,(
% 0.22/0.58    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 0.22/0.58  fof(f339,plain,(
% 0.22/0.58    ( ! [X5] : (~r2_hidden(X5,k3_enumset1(sK0,sK0,sK0,sK1,sK2)) | sK1 = X5 | sK2 = X5) )),
% 0.22/0.58    inference(duplicate_literal_removal,[],[f332])).
% 0.22/0.58  fof(f332,plain,(
% 0.22/0.58    ( ! [X5] : (~r2_hidden(X5,k3_enumset1(sK0,sK0,sK0,sK1,sK2)) | sK1 = X5 | sK1 = X5 | sK2 = X5) )),
% 0.22/0.58    inference(superposition,[],[f100,f229])).
% 0.22/0.58  fof(f229,plain,(
% 0.22/0.58    k3_enumset1(sK1,sK1,sK1,sK1,sK2) = k3_enumset1(sK0,sK0,sK0,sK1,sK2)),
% 0.22/0.58    inference(forward_demodulation,[],[f228,f71])).
% 0.22/0.59  % (3646)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.59  % (3645)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.59  % (3629)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.59  % (3648)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.52/0.60  % (3639)Refutation not found, incomplete strategy% (3639)------------------------------
% 1.52/0.60  % (3639)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.52/0.60  % (3639)Termination reason: Refutation not found, incomplete strategy
% 1.52/0.60  
% 1.52/0.60  % (3633)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.52/0.60  % (3639)Memory used [KB]: 10618
% 1.52/0.60  % (3639)Time elapsed: 0.152 s
% 1.52/0.60  % (3639)------------------------------
% 1.52/0.60  % (3639)------------------------------
% 1.52/0.60  % (3637)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.52/0.60  % (3649)Refutation not found, incomplete strategy% (3649)------------------------------
% 1.52/0.60  % (3649)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.52/0.60  % (3649)Termination reason: Refutation not found, incomplete strategy
% 1.52/0.60  
% 1.52/0.60  % (3649)Memory used [KB]: 6268
% 1.52/0.60  % (3649)Time elapsed: 0.190 s
% 1.52/0.60  % (3649)------------------------------
% 1.52/0.60  % (3649)------------------------------
% 1.52/0.60  fof(f71,plain,(
% 1.52/0.60    ( ! [X2,X0,X1] : (k3_enumset1(X0,X0,X0,X1,X2) = k3_enumset1(X1,X1,X1,X2,X0)) )),
% 1.52/0.60    inference(definition_unfolding,[],[f41,f61,f61])).
% 1.52/0.60  fof(f41,plain,(
% 1.52/0.60    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0)) )),
% 1.52/0.60    inference(cnf_transformation,[],[f12])).
% 1.52/0.60  fof(f12,axiom,(
% 1.52/0.60    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0)),
% 1.52/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_enumset1)).
% 1.52/0.60  fof(f228,plain,(
% 1.52/0.60    k3_enumset1(sK1,sK1,sK1,sK1,sK2) = k3_enumset1(sK1,sK1,sK1,sK2,sK0)),
% 1.52/0.60    inference(forward_demodulation,[],[f222,f29])).
% 1.52/0.60  fof(f29,plain,(
% 1.52/0.60    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.52/0.60    inference(cnf_transformation,[],[f7])).
% 1.52/0.60  fof(f7,axiom,(
% 1.52/0.60    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.52/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 1.52/0.60  fof(f222,plain,(
% 1.52/0.60    k3_enumset1(sK1,sK1,sK1,sK2,sK0) = k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK2),k1_xboole_0)),
% 1.52/0.60    inference(superposition,[],[f80,f170])).
% 1.52/0.60  fof(f170,plain,(
% 1.52/0.60    k1_xboole_0 = k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK2))),
% 1.52/0.60    inference(backward_demodulation,[],[f133,f169])).
% 1.52/0.60  fof(f169,plain,(
% 1.52/0.60    k1_xboole_0 = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0))),
% 1.52/0.60    inference(backward_demodulation,[],[f164,f168])).
% 1.52/0.60  fof(f168,plain,(
% 1.52/0.60    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0)),
% 1.52/0.60    inference(superposition,[],[f66,f154])).
% 1.52/0.60  fof(f154,plain,(
% 1.52/0.60    k1_xboole_0 = k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0))),
% 1.52/0.60    inference(forward_demodulation,[],[f139,f101])).
% 1.52/0.60  fof(f101,plain,(
% 1.52/0.60    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK2)))),
% 1.52/0.60    inference(resolution,[],[f65,f68])).
% 1.52/0.60  fof(f68,plain,(
% 1.52/0.60    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0) )),
% 1.52/0.60    inference(definition_unfolding,[],[f38,f37])).
% 1.52/0.60  fof(f37,plain,(
% 1.52/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.52/0.60    inference(cnf_transformation,[],[f6])).
% 1.52/0.60  fof(f6,axiom,(
% 1.52/0.60    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.52/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.52/0.60  fof(f38,plain,(
% 1.52/0.60    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.52/0.60    inference(cnf_transformation,[],[f24])).
% 1.52/0.60  fof(f24,plain,(
% 1.52/0.60    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.52/0.60    inference(ennf_transformation,[],[f5])).
% 1.52/0.60  fof(f5,axiom,(
% 1.52/0.60    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.52/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.52/0.60  fof(f65,plain,(
% 1.52/0.60    r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK2))),
% 1.52/0.60    inference(definition_unfolding,[],[f26,f63,f62])).
% 1.52/0.60  fof(f62,plain,(
% 1.52/0.60    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 1.52/0.60    inference(definition_unfolding,[],[f34,f61])).
% 1.52/0.60  fof(f34,plain,(
% 1.52/0.60    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.52/0.60    inference(cnf_transformation,[],[f16])).
% 1.52/0.60  fof(f16,axiom,(
% 1.52/0.60    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.52/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.52/0.60  fof(f63,plain,(
% 1.52/0.60    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 1.52/0.60    inference(definition_unfolding,[],[f30,f62])).
% 1.52/0.60  fof(f30,plain,(
% 1.52/0.60    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.52/0.60    inference(cnf_transformation,[],[f15])).
% 1.52/0.60  fof(f15,axiom,(
% 1.52/0.60    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.52/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.52/0.60  fof(f26,plain,(
% 1.52/0.60    r1_tarski(k1_tarski(sK0),k2_tarski(sK1,sK2))),
% 1.52/0.60    inference(cnf_transformation,[],[f23])).
% 1.52/0.60  fof(f139,plain,(
% 1.52/0.60    k1_xboole_0 = k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK2))))),
% 1.52/0.60    inference(resolution,[],[f134,f69])).
% 1.52/0.60  fof(f69,plain,(
% 1.52/0.60    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 1.52/0.60    inference(definition_unfolding,[],[f40,f37])).
% 1.52/0.60  fof(f40,plain,(
% 1.52/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 1.52/0.60    inference(cnf_transformation,[],[f2])).
% 1.52/0.60  fof(f2,axiom,(
% 1.52/0.60    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.52/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.52/0.60  fof(f134,plain,(
% 1.52/0.60    r1_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK2)))),
% 1.52/0.60    inference(superposition,[],[f32,f101])).
% 1.52/0.60  fof(f32,plain,(
% 1.52/0.60    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 1.52/0.60    inference(cnf_transformation,[],[f8])).
% 1.52/0.60  fof(f8,axiom,(
% 1.52/0.60    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 1.52/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).
% 1.52/0.60  fof(f66,plain,(
% 1.52/0.60    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 1.52/0.60    inference(definition_unfolding,[],[f31,f37])).
% 1.52/0.60  fof(f31,plain,(
% 1.52/0.60    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.52/0.60    inference(cnf_transformation,[],[f22])).
% 1.52/0.60  fof(f22,plain,(
% 1.52/0.60    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 1.52/0.60    inference(rectify,[],[f3])).
% 1.52/0.60  fof(f3,axiom,(
% 1.52/0.60    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 1.52/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 1.52/0.60  fof(f164,plain,(
% 1.52/0.60    k1_xboole_0 = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0))),
% 1.52/0.60    inference(superposition,[],[f64,f154])).
% 1.52/0.60  fof(f64,plain,(
% 1.52/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.52/0.60    inference(definition_unfolding,[],[f36,f37])).
% 1.52/0.60  fof(f36,plain,(
% 1.52/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.52/0.60    inference(cnf_transformation,[],[f4])).
% 1.52/0.60  fof(f4,axiom,(
% 1.52/0.60    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.52/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.52/0.60  fof(f133,plain,(
% 1.52/0.60    k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK2)) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0))),
% 1.52/0.60    inference(superposition,[],[f64,f101])).
% 1.52/0.60  fof(f80,plain,(
% 1.52/0.60    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k5_xboole_0(k3_enumset1(X0,X0,X0,X1,X2),k4_xboole_0(k3_enumset1(X3,X3,X3,X3,X3),k3_enumset1(X0,X0,X0,X1,X2)))) )),
% 1.52/0.60    inference(definition_unfolding,[],[f52,f51,f35,f61,f63])).
% 1.52/0.60  fof(f35,plain,(
% 1.52/0.60    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.52/0.60    inference(cnf_transformation,[],[f9])).
% 1.52/0.60  fof(f9,axiom,(
% 1.52/0.60    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.52/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.52/0.60  fof(f52,plain,(
% 1.52/0.60    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) )),
% 1.52/0.60    inference(cnf_transformation,[],[f14])).
% 1.52/0.60  fof(f14,axiom,(
% 1.52/0.60    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))),
% 1.52/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).
% 1.52/0.60  fof(f100,plain,(
% 1.52/0.60    ( ! [X4,X2,X0,X1] : (X0 = X4 | X1 = X4 | X2 = X4 | ~r2_hidden(X4,k3_enumset1(X0,X0,X0,X1,X2))) )),
% 1.52/0.60    inference(equality_resolution,[],[f84])).
% 1.52/0.60  fof(f84,plain,(
% 1.52/0.60    ( ! [X4,X2,X0,X3,X1] : (X0 = X4 | X1 = X4 | X2 = X4 | ~r2_hidden(X4,X3) | k3_enumset1(X0,X0,X0,X1,X2) != X3) )),
% 1.52/0.60    inference(definition_unfolding,[],[f57,f61])).
% 1.52/0.60  fof(f57,plain,(
% 1.52/0.60    ( ! [X4,X2,X0,X3,X1] : (X0 = X4 | X1 = X4 | X2 = X4 | ~r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 1.52/0.60    inference(cnf_transformation,[],[f25])).
% 1.52/0.60  % SZS output end Proof for theBenchmark
% 1.52/0.60  % (3640)------------------------------
% 1.52/0.60  % (3640)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.52/0.60  % (3640)Termination reason: Refutation
% 1.52/0.60  
% 1.52/0.60  % (3640)Memory used [KB]: 1918
% 1.52/0.60  % (3640)Time elapsed: 0.177 s
% 1.52/0.60  % (3640)------------------------------
% 1.52/0.60  % (3640)------------------------------
% 1.52/0.60  % (3622)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.52/0.60  % (3619)Success in time 0.232 s
%------------------------------------------------------------------------------
