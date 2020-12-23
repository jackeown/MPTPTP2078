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
% DateTime   : Thu Dec  3 12:35:43 EST 2020

% Result     : Theorem 1.59s
% Output     : Refutation 1.59s
% Verified   : 
% Statistics : Number of formulae       :   41 (  48 expanded)
%              Number of leaves         :   11 (  14 expanded)
%              Depth                    :   10
%              Number of atoms          :   60 (  72 expanded)
%              Number of equality atoms :   41 (  49 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f223,plain,(
    $false ),
    inference(subsumption_resolution,[],[f33,f222])).

fof(f222,plain,(
    ! [X2,X3] : k2_tarski(X2,X3) = k2_xboole_0(k1_tarski(X2),k2_tarski(X2,X3)) ),
    inference(forward_demodulation,[],[f221,f72])).

fof(f72,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(superposition,[],[f70,f38])).

fof(f38,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f70,plain,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(forward_demodulation,[],[f68,f36])).

fof(f36,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f68,plain,(
    ! [X1] : k2_xboole_0(X1,X1) = k5_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[],[f41,f63])).

fof(f63,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(resolution,[],[f50,f58])).

fof(f58,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f41,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f221,plain,(
    ! [X2,X3] : k5_xboole_0(k1_xboole_0,k2_tarski(X2,X3)) = k2_xboole_0(k1_tarski(X2),k2_tarski(X2,X3)) ),
    inference(forward_demodulation,[],[f206,f38])).

fof(f206,plain,(
    ! [X2,X3] : k5_xboole_0(k2_tarski(X2,X3),k1_xboole_0) = k2_xboole_0(k1_tarski(X2),k2_tarski(X2,X3)) ),
    inference(superposition,[],[f202,f65])).

fof(f65,plain,(
    ! [X4,X3] : k1_xboole_0 = k4_xboole_0(k1_tarski(X3),k2_tarski(X3,X4)) ),
    inference(resolution,[],[f50,f37])).

fof(f37,plain,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).

fof(f202,plain,(
    ! [X4,X3] : k2_xboole_0(X4,X3) = k5_xboole_0(X3,k4_xboole_0(X4,X3)) ),
    inference(forward_demodulation,[],[f190,f40])).

fof(f40,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f190,plain,(
    ! [X4,X3] : k5_xboole_0(X3,k5_xboole_0(X4,k3_xboole_0(X4,X3))) = k2_xboole_0(X4,X3) ),
    inference(superposition,[],[f94,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f94,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X1,X0),k3_xboole_0(X0,X1)) ),
    inference(superposition,[],[f42,f38])).

fof(f42,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

fof(f33,plain,(
    k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f23])).

fof(f23,plain,
    ( ? [X0,X1] : k2_tarski(X0,X1) != k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))
   => k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1] : k2_tarski(X0,X1) != k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:59:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.51  % (4126)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.51  % (4126)Refutation not found, incomplete strategy% (4126)------------------------------
% 0.21/0.51  % (4126)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (4132)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (4126)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (4126)Memory used [KB]: 1663
% 0.21/0.52  % (4126)Time elapsed: 0.089 s
% 0.21/0.52  % (4126)------------------------------
% 0.21/0.52  % (4126)------------------------------
% 0.21/0.52  % (4128)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (4140)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.52  % (4154)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.52  % (4138)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (4129)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.52  % (4148)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (4148)Refutation not found, incomplete strategy% (4148)------------------------------
% 0.21/0.52  % (4148)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (4148)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (4148)Memory used [KB]: 10746
% 0.21/0.52  % (4148)Time elapsed: 0.075 s
% 0.21/0.52  % (4148)------------------------------
% 0.21/0.52  % (4148)------------------------------
% 0.21/0.53  % (4147)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.53  % (4147)Refutation not found, incomplete strategy% (4147)------------------------------
% 0.21/0.53  % (4147)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (4147)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (4147)Memory used [KB]: 1663
% 0.21/0.53  % (4147)Time elapsed: 0.113 s
% 0.21/0.53  % (4147)------------------------------
% 0.21/0.53  % (4147)------------------------------
% 0.21/0.53  % (4131)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (4136)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.53  % (4146)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.53  % (4155)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.53  % (4143)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.54  % (4146)Refutation not found, incomplete strategy% (4146)------------------------------
% 0.21/0.54  % (4146)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (4134)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.54  % (4135)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.54  % (4146)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (4146)Memory used [KB]: 10618
% 0.21/0.54  % (4146)Time elapsed: 0.124 s
% 0.21/0.54  % (4146)------------------------------
% 0.21/0.54  % (4146)------------------------------
% 0.21/0.54  % (4135)Refutation not found, incomplete strategy% (4135)------------------------------
% 0.21/0.54  % (4135)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (4135)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (4135)Memory used [KB]: 10618
% 0.21/0.54  % (4135)Time elapsed: 0.131 s
% 0.21/0.54  % (4135)------------------------------
% 0.21/0.54  % (4135)------------------------------
% 0.21/0.54  % (4152)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.54  % (4127)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (4128)Refutation not found, incomplete strategy% (4128)------------------------------
% 0.21/0.54  % (4128)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (4128)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (4128)Memory used [KB]: 10618
% 0.21/0.54  % (4128)Time elapsed: 0.126 s
% 0.21/0.54  % (4128)------------------------------
% 0.21/0.54  % (4128)------------------------------
% 0.21/0.54  % (4144)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.54  % (4134)Refutation not found, incomplete strategy% (4134)------------------------------
% 0.21/0.54  % (4134)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (4134)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (4134)Memory used [KB]: 10618
% 0.21/0.54  % (4134)Time elapsed: 0.122 s
% 0.21/0.54  % (4134)------------------------------
% 0.21/0.54  % (4134)------------------------------
% 1.40/0.54  % (4137)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.40/0.55  % (4151)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.40/0.55  % (4142)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.40/0.55  % (4141)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.40/0.55  % (4139)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.40/0.55  % (4151)Refutation not found, incomplete strategy% (4151)------------------------------
% 1.40/0.55  % (4151)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.55  % (4143)Refutation not found, incomplete strategy% (4143)------------------------------
% 1.40/0.55  % (4143)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.55  % (4143)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.55  
% 1.40/0.55  % (4143)Memory used [KB]: 10618
% 1.40/0.55  % (4143)Time elapsed: 0.139 s
% 1.40/0.55  % (4143)------------------------------
% 1.40/0.55  % (4143)------------------------------
% 1.40/0.55  % (4153)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.40/0.55  % (4151)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.55  
% 1.40/0.55  % (4151)Memory used [KB]: 6140
% 1.40/0.55  % (4151)Time elapsed: 0.136 s
% 1.40/0.55  % (4151)------------------------------
% 1.40/0.55  % (4151)------------------------------
% 1.40/0.55  % (4130)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.40/0.55  % (4136)Refutation not found, incomplete strategy% (4136)------------------------------
% 1.40/0.55  % (4136)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.55  % (4136)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.55  
% 1.40/0.55  % (4136)Memory used [KB]: 10618
% 1.40/0.55  % (4136)Time elapsed: 0.137 s
% 1.40/0.55  % (4136)------------------------------
% 1.40/0.55  % (4136)------------------------------
% 1.40/0.55  % (4130)Refutation not found, incomplete strategy% (4130)------------------------------
% 1.40/0.55  % (4130)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.55  % (4130)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.55  
% 1.40/0.55  % (4130)Memory used [KB]: 6140
% 1.40/0.55  % (4130)Time elapsed: 0.131 s
% 1.40/0.55  % (4130)------------------------------
% 1.40/0.55  % (4130)------------------------------
% 1.40/0.56  % (4133)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.40/0.56  % (4145)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.59/0.56  % (4150)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.59/0.56  % (4149)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.59/0.56  % (4137)Refutation not found, incomplete strategy% (4137)------------------------------
% 1.59/0.56  % (4137)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.56  % (4137)Termination reason: Refutation not found, incomplete strategy
% 1.59/0.56  
% 1.59/0.56  % (4137)Memory used [KB]: 10618
% 1.59/0.56  % (4137)Time elapsed: 0.149 s
% 1.59/0.56  % (4137)------------------------------
% 1.59/0.56  % (4137)------------------------------
% 1.59/0.57  % (4149)Refutation not found, incomplete strategy% (4149)------------------------------
% 1.59/0.57  % (4149)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.57  % (4149)Termination reason: Refutation not found, incomplete strategy
% 1.59/0.57  
% 1.59/0.57  % (4149)Memory used [KB]: 1663
% 1.59/0.57  % (4149)Time elapsed: 0.158 s
% 1.59/0.57  % (4149)------------------------------
% 1.59/0.57  % (4149)------------------------------
% 1.59/0.58  % (4133)Refutation found. Thanks to Tanya!
% 1.59/0.58  % SZS status Theorem for theBenchmark
% 1.59/0.58  % SZS output start Proof for theBenchmark
% 1.59/0.58  fof(f223,plain,(
% 1.59/0.58    $false),
% 1.59/0.58    inference(subsumption_resolution,[],[f33,f222])).
% 1.59/0.58  fof(f222,plain,(
% 1.59/0.58    ( ! [X2,X3] : (k2_tarski(X2,X3) = k2_xboole_0(k1_tarski(X2),k2_tarski(X2,X3))) )),
% 1.59/0.58    inference(forward_demodulation,[],[f221,f72])).
% 1.59/0.58  fof(f72,plain,(
% 1.59/0.58    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = X1) )),
% 1.59/0.58    inference(superposition,[],[f70,f38])).
% 1.59/0.58  fof(f38,plain,(
% 1.59/0.58    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 1.59/0.58    inference(cnf_transformation,[],[f1])).
% 1.59/0.58  fof(f1,axiom,(
% 1.59/0.58    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 1.59/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 1.59/0.58  fof(f70,plain,(
% 1.59/0.58    ( ! [X1] : (k5_xboole_0(X1,k1_xboole_0) = X1) )),
% 1.59/0.58    inference(forward_demodulation,[],[f68,f36])).
% 1.59/0.58  fof(f36,plain,(
% 1.59/0.58    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 1.59/0.58    inference(cnf_transformation,[],[f19])).
% 1.59/0.58  fof(f19,plain,(
% 1.59/0.58    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 1.59/0.58    inference(rectify,[],[f3])).
% 1.59/0.58  fof(f3,axiom,(
% 1.59/0.58    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 1.59/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 1.59/0.58  fof(f68,plain,(
% 1.59/0.58    ( ! [X1] : (k2_xboole_0(X1,X1) = k5_xboole_0(X1,k1_xboole_0)) )),
% 1.59/0.58    inference(superposition,[],[f41,f63])).
% 1.59/0.58  fof(f63,plain,(
% 1.59/0.58    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 1.59/0.58    inference(resolution,[],[f50,f58])).
% 1.59/0.58  fof(f58,plain,(
% 1.59/0.58    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.59/0.58    inference(equality_resolution,[],[f44])).
% 1.59/0.58  fof(f44,plain,(
% 1.59/0.58    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.59/0.58    inference(cnf_transformation,[],[f26])).
% 1.59/0.58  fof(f26,plain,(
% 1.59/0.58    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.59/0.58    inference(flattening,[],[f25])).
% 1.59/0.58  fof(f25,plain,(
% 1.59/0.58    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.59/0.58    inference(nnf_transformation,[],[f5])).
% 1.59/0.58  fof(f5,axiom,(
% 1.59/0.58    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.59/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.59/0.58  fof(f50,plain,(
% 1.59/0.58    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 1.59/0.58    inference(cnf_transformation,[],[f31])).
% 1.59/0.58  fof(f31,plain,(
% 1.59/0.58    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 1.59/0.58    inference(nnf_transformation,[],[f6])).
% 1.59/0.58  fof(f6,axiom,(
% 1.59/0.58    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.59/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.59/0.58  fof(f41,plain,(
% 1.59/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.59/0.58    inference(cnf_transformation,[],[f11])).
% 1.59/0.58  fof(f11,axiom,(
% 1.59/0.58    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.59/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.59/0.58  fof(f221,plain,(
% 1.59/0.58    ( ! [X2,X3] : (k5_xboole_0(k1_xboole_0,k2_tarski(X2,X3)) = k2_xboole_0(k1_tarski(X2),k2_tarski(X2,X3))) )),
% 1.59/0.58    inference(forward_demodulation,[],[f206,f38])).
% 1.59/0.58  fof(f206,plain,(
% 1.59/0.58    ( ! [X2,X3] : (k5_xboole_0(k2_tarski(X2,X3),k1_xboole_0) = k2_xboole_0(k1_tarski(X2),k2_tarski(X2,X3))) )),
% 1.59/0.58    inference(superposition,[],[f202,f65])).
% 1.59/0.58  fof(f65,plain,(
% 1.59/0.58    ( ! [X4,X3] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X3),k2_tarski(X3,X4))) )),
% 1.59/0.58    inference(resolution,[],[f50,f37])).
% 1.59/0.58  fof(f37,plain,(
% 1.59/0.58    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))) )),
% 1.59/0.58    inference(cnf_transformation,[],[f16])).
% 1.59/0.58  fof(f16,axiom,(
% 1.59/0.58    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))),
% 1.59/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).
% 1.59/0.58  fof(f202,plain,(
% 1.59/0.58    ( ! [X4,X3] : (k2_xboole_0(X4,X3) = k5_xboole_0(X3,k4_xboole_0(X4,X3))) )),
% 1.59/0.58    inference(forward_demodulation,[],[f190,f40])).
% 1.59/0.58  fof(f40,plain,(
% 1.59/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.59/0.58    inference(cnf_transformation,[],[f7])).
% 1.59/0.58  fof(f7,axiom,(
% 1.59/0.58    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.59/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.59/0.58  fof(f190,plain,(
% 1.59/0.58    ( ! [X4,X3] : (k5_xboole_0(X3,k5_xboole_0(X4,k3_xboole_0(X4,X3))) = k2_xboole_0(X4,X3)) )),
% 1.59/0.58    inference(superposition,[],[f94,f52])).
% 1.59/0.58  fof(f52,plain,(
% 1.59/0.58    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 1.59/0.58    inference(cnf_transformation,[],[f9])).
% 1.59/0.58  fof(f9,axiom,(
% 1.59/0.58    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 1.59/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 1.59/0.58  fof(f94,plain,(
% 1.59/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X1,X0),k3_xboole_0(X0,X1))) )),
% 1.59/0.58    inference(superposition,[],[f42,f38])).
% 1.59/0.58  fof(f42,plain,(
% 1.59/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 1.59/0.58    inference(cnf_transformation,[],[f10])).
% 1.59/0.58  fof(f10,axiom,(
% 1.59/0.58    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 1.59/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).
% 1.59/0.58  fof(f33,plain,(
% 1.59/0.58    k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1))),
% 1.59/0.58    inference(cnf_transformation,[],[f24])).
% 1.59/0.58  fof(f24,plain,(
% 1.59/0.58    k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1))),
% 1.59/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f23])).
% 1.59/0.58  fof(f23,plain,(
% 1.59/0.58    ? [X0,X1] : k2_tarski(X0,X1) != k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) => k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1))),
% 1.59/0.58    introduced(choice_axiom,[])).
% 1.59/0.58  fof(f20,plain,(
% 1.59/0.58    ? [X0,X1] : k2_tarski(X0,X1) != k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))),
% 1.59/0.58    inference(ennf_transformation,[],[f18])).
% 1.59/0.58  fof(f18,negated_conjecture,(
% 1.59/0.58    ~! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))),
% 1.59/0.58    inference(negated_conjecture,[],[f17])).
% 1.59/0.58  fof(f17,conjecture,(
% 1.59/0.58    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))),
% 1.59/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_zfmisc_1)).
% 1.59/0.58  % SZS output end Proof for theBenchmark
% 1.59/0.58  % (4133)------------------------------
% 1.59/0.58  % (4133)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.58  % (4133)Termination reason: Refutation
% 1.59/0.58  
% 1.59/0.58  % (4133)Memory used [KB]: 6396
% 1.59/0.58  % (4133)Time elapsed: 0.167 s
% 1.59/0.58  % (4133)------------------------------
% 1.59/0.58  % (4133)------------------------------
% 1.59/0.58  % (4125)Success in time 0.209 s
%------------------------------------------------------------------------------
