%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:13 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 267 expanded)
%              Number of leaves         :    8 (  88 expanded)
%              Depth                    :   18
%              Number of atoms          :   68 ( 372 expanded)
%              Number of equality atoms :   46 ( 224 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f557,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f556])).

fof(f556,plain,(
    k4_xboole_0(sK0,sK1) != k4_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f420,f509])).

fof(f509,plain,(
    ! [X2] : k2_xboole_0(X2,k1_xboole_0) = X2 ),
    inference(forward_demodulation,[],[f508,f13])).

fof(f13,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f508,plain,(
    ! [X2] : k2_xboole_0(X2,k1_xboole_0) = k4_xboole_0(X2,k1_xboole_0) ),
    inference(forward_demodulation,[],[f507,f250])).

fof(f250,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f226,f13])).

fof(f226,plain,(
    ! [X0] : k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f67,f222])).

fof(f222,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(unit_resulting_resolution,[],[f211,f214,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( sP3(sK2(X0,X1,X2),X1,X0)
      | r2_hidden(sK2(X0,X1,X2),X2)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f214,plain,(
    ! [X0,X1] : ~ sP3(X0,X1,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f211,f21])).

fof(f21,plain,(
    ! [X0,X3,X1] :
      ( ~ sP3(X3,X1,X0)
      | r2_hidden(X3,X0) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f211,plain,(
    ! [X6] : ~ r2_hidden(X6,k1_xboole_0) ),
    inference(duplicate_literal_removal,[],[f209])).

fof(f209,plain,(
    ! [X6] :
      ( ~ r2_hidden(X6,k1_xboole_0)
      | ~ r2_hidden(X6,k1_xboole_0) ) ),
    inference(superposition,[],[f156,f13])).

fof(f156,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k4_xboole_0(X1,X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f120,f22])).

fof(f22,plain,(
    ! [X0,X3,X1] :
      ( ~ sP3(X3,X1,X0)
      | ~ r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f120,plain,(
    ! [X10,X11] :
      ( sP3(X11,k4_xboole_0(X10,X10),X10)
      | ~ r2_hidden(X11,X10) ) ),
    inference(superposition,[],[f31,f89])).

fof(f89,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(superposition,[],[f30,f13])).

fof(f30,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f17,f16])).

fof(f16,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f17,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f31,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k4_xboole_0(X0,X1))
      | sP3(X3,X1,X0) ) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] :
      ( sP3(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f67,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f29,f13])).

fof(f29,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f14,f16,f16])).

fof(f14,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f507,plain,(
    ! [X2] : k2_xboole_0(X2,k1_xboole_0) = k4_xboole_0(X2,k4_xboole_0(X2,X2)) ),
    inference(forward_demodulation,[],[f506,f13])).

fof(f506,plain,(
    ! [X2] : k4_xboole_0(X2,k4_xboole_0(X2,X2)) = k4_xboole_0(k2_xboole_0(X2,k1_xboole_0),k1_xboole_0) ),
    inference(forward_demodulation,[],[f494,f45])).

fof(f45,plain,(
    ! [X4,X3] : k4_xboole_0(X3,X4) = k4_xboole_0(X3,k2_xboole_0(X4,k1_xboole_0)) ),
    inference(superposition,[],[f19,f13])).

fof(f19,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f494,plain,(
    ! [X2] : k4_xboole_0(k2_xboole_0(X2,k1_xboole_0),k1_xboole_0) = k4_xboole_0(X2,k4_xboole_0(X2,k2_xboole_0(X2,k1_xboole_0))) ),
    inference(superposition,[],[f29,f275])).

fof(f275,plain,(
    ! [X2] : k1_xboole_0 = k4_xboole_0(k2_xboole_0(X2,k1_xboole_0),X2) ),
    inference(forward_demodulation,[],[f237,f13])).

fof(f237,plain,(
    ! [X2] : k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k2_xboole_0(X2,k1_xboole_0),X2) ),
    inference(backward_demodulation,[],[f150,f222])).

fof(f150,plain,(
    ! [X2] : k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X2)) = k4_xboole_0(k2_xboole_0(X2,k1_xboole_0),X2) ),
    inference(forward_demodulation,[],[f129,f45])).

fof(f129,plain,(
    ! [X2] : k4_xboole_0(k2_xboole_0(X2,k1_xboole_0),X2) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k2_xboole_0(X2,k1_xboole_0))) ),
    inference(superposition,[],[f67,f45])).

fof(f420,plain,(
    k4_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0) ),
    inference(backward_demodulation,[],[f35,f419])).

fof(f419,plain,(
    ! [X4,X3] : k1_xboole_0 = k4_xboole_0(X3,k2_xboole_0(X4,X3)) ),
    inference(forward_demodulation,[],[f418,f250])).

fof(f418,plain,(
    ! [X4,X3] : k4_xboole_0(k4_xboole_0(X3,X4),k4_xboole_0(X3,X4)) = k4_xboole_0(X3,k2_xboole_0(X4,X3)) ),
    inference(forward_demodulation,[],[f417,f19])).

fof(f417,plain,(
    ! [X4,X3] : k4_xboole_0(k4_xboole_0(X3,X4),k4_xboole_0(X3,X4)) = k4_xboole_0(k4_xboole_0(X3,X4),X3) ),
    inference(forward_demodulation,[],[f392,f96])).

fof(f96,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(superposition,[],[f30,f29])).

fof(f392,plain,(
    ! [X4,X3] : k4_xboole_0(k4_xboole_0(X3,X4),X3) = k4_xboole_0(k4_xboole_0(X3,X4),k4_xboole_0(X3,k4_xboole_0(X4,k4_xboole_0(X4,X3)))) ),
    inference(superposition,[],[f96,f29])).

fof(f35,plain,(
    k4_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),sK0))) ),
    inference(backward_demodulation,[],[f33,f19])).

fof(f33,plain,(
    k4_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0)) ),
    inference(backward_demodulation,[],[f28,f30])).

fof(f28,plain,(
    k4_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0)) ),
    inference(definition_unfolding,[],[f12,f18,f16])).

fof(f18,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

fof(f12,plain,(
    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 19:48:52 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.50  % (14251)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.19/0.51  % (14251)Refutation not found, incomplete strategy% (14251)------------------------------
% 0.19/0.51  % (14251)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.51  % (14256)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.19/0.51  % (14251)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.51  
% 0.19/0.51  % (14251)Memory used [KB]: 10618
% 0.19/0.51  % (14251)Time elapsed: 0.114 s
% 0.19/0.51  % (14251)------------------------------
% 0.19/0.51  % (14251)------------------------------
% 0.19/0.52  % (14265)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.19/0.53  % (14264)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.19/0.53  % (14273)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.19/0.54  % (14259)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.19/0.54  % (14250)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.19/0.54  % (14272)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.19/0.54  % (14272)Refutation not found, incomplete strategy% (14272)------------------------------
% 0.19/0.54  % (14272)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.54  % (14272)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.54  
% 0.19/0.54  % (14272)Memory used [KB]: 1663
% 0.19/0.54  % (14272)Time elapsed: 0.135 s
% 0.19/0.54  % (14272)------------------------------
% 0.19/0.54  % (14272)------------------------------
% 0.19/0.54  % (14259)Refutation not found, incomplete strategy% (14259)------------------------------
% 0.19/0.54  % (14259)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.54  % (14259)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.54  
% 0.19/0.54  % (14259)Memory used [KB]: 10618
% 0.19/0.54  % (14259)Time elapsed: 0.143 s
% 0.19/0.54  % (14259)------------------------------
% 0.19/0.54  % (14259)------------------------------
% 0.19/0.55  % (14258)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.19/0.55  % (14275)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.19/0.55  % (14249)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.19/0.56  % (14252)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.19/0.57  % (14249)Refutation not found, incomplete strategy% (14249)------------------------------
% 0.19/0.57  % (14249)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.57  % (14263)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.19/0.58  % (14249)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.58  
% 0.19/0.58  % (14249)Memory used [KB]: 1663
% 0.19/0.58  % (14249)Time elapsed: 0.162 s
% 0.19/0.58  % (14249)------------------------------
% 0.19/0.58  % (14249)------------------------------
% 0.19/0.58  % (14254)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.19/0.58  % (14253)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.19/0.58  % (14273)Refutation found. Thanks to Tanya!
% 0.19/0.58  % SZS status Theorem for theBenchmark
% 0.19/0.58  % (14253)Refutation not found, incomplete strategy% (14253)------------------------------
% 0.19/0.58  % (14253)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.58  % (14253)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.58  
% 0.19/0.58  % (14253)Memory used [KB]: 6140
% 0.19/0.58  % (14253)Time elapsed: 0.157 s
% 0.19/0.58  % (14253)------------------------------
% 0.19/0.58  % (14253)------------------------------
% 0.19/0.58  % SZS output start Proof for theBenchmark
% 0.19/0.58  fof(f557,plain,(
% 0.19/0.58    $false),
% 0.19/0.58    inference(trivial_inequality_removal,[],[f556])).
% 0.19/0.58  fof(f556,plain,(
% 0.19/0.58    k4_xboole_0(sK0,sK1) != k4_xboole_0(sK0,sK1)),
% 0.19/0.58    inference(superposition,[],[f420,f509])).
% 0.19/0.58  fof(f509,plain,(
% 0.19/0.58    ( ! [X2] : (k2_xboole_0(X2,k1_xboole_0) = X2) )),
% 0.19/0.58    inference(forward_demodulation,[],[f508,f13])).
% 0.19/0.58  fof(f13,plain,(
% 0.19/0.58    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.19/0.58    inference(cnf_transformation,[],[f4])).
% 0.19/0.58  fof(f4,axiom,(
% 0.19/0.58    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.19/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.19/0.58  fof(f508,plain,(
% 0.19/0.58    ( ! [X2] : (k2_xboole_0(X2,k1_xboole_0) = k4_xboole_0(X2,k1_xboole_0)) )),
% 0.19/0.58    inference(forward_demodulation,[],[f507,f250])).
% 0.19/0.58  fof(f250,plain,(
% 0.19/0.58    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.19/0.58    inference(forward_demodulation,[],[f226,f13])).
% 0.19/0.58  fof(f226,plain,(
% 0.19/0.58    ( ! [X0] : (k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,k1_xboole_0)) )),
% 0.19/0.58    inference(backward_demodulation,[],[f67,f222])).
% 0.19/0.58  fof(f222,plain,(
% 0.19/0.58    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.19/0.58    inference(unit_resulting_resolution,[],[f211,f214,f25])).
% 0.19/0.58  fof(f25,plain,(
% 0.19/0.58    ( ! [X2,X0,X1] : (sP3(sK2(X0,X1,X2),X1,X0) | r2_hidden(sK2(X0,X1,X2),X2) | k4_xboole_0(X0,X1) = X2) )),
% 0.19/0.58    inference(cnf_transformation,[],[f2])).
% 0.19/0.58  fof(f2,axiom,(
% 0.19/0.58    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.19/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.19/0.58  fof(f214,plain,(
% 0.19/0.58    ( ! [X0,X1] : (~sP3(X0,X1,k1_xboole_0)) )),
% 0.19/0.58    inference(unit_resulting_resolution,[],[f211,f21])).
% 0.19/0.58  fof(f21,plain,(
% 0.19/0.58    ( ! [X0,X3,X1] : (~sP3(X3,X1,X0) | r2_hidden(X3,X0)) )),
% 0.19/0.58    inference(cnf_transformation,[],[f2])).
% 0.19/0.58  fof(f211,plain,(
% 0.19/0.58    ( ! [X6] : (~r2_hidden(X6,k1_xboole_0)) )),
% 0.19/0.58    inference(duplicate_literal_removal,[],[f209])).
% 0.19/0.58  fof(f209,plain,(
% 0.19/0.58    ( ! [X6] : (~r2_hidden(X6,k1_xboole_0) | ~r2_hidden(X6,k1_xboole_0)) )),
% 0.19/0.58    inference(superposition,[],[f156,f13])).
% 0.19/0.58  fof(f156,plain,(
% 0.19/0.58    ( ! [X0,X1] : (~r2_hidden(X0,k4_xboole_0(X1,X1)) | ~r2_hidden(X0,X1)) )),
% 0.19/0.58    inference(resolution,[],[f120,f22])).
% 0.19/0.58  fof(f22,plain,(
% 0.19/0.58    ( ! [X0,X3,X1] : (~sP3(X3,X1,X0) | ~r2_hidden(X3,X1)) )),
% 0.19/0.58    inference(cnf_transformation,[],[f2])).
% 0.19/0.58  fof(f120,plain,(
% 0.19/0.58    ( ! [X10,X11] : (sP3(X11,k4_xboole_0(X10,X10),X10) | ~r2_hidden(X11,X10)) )),
% 0.19/0.58    inference(superposition,[],[f31,f89])).
% 0.19/0.58  fof(f89,plain,(
% 0.19/0.58    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 0.19/0.58    inference(superposition,[],[f30,f13])).
% 0.19/0.58  fof(f30,plain,(
% 0.19/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.19/0.58    inference(definition_unfolding,[],[f17,f16])).
% 0.19/0.58  fof(f16,plain,(
% 0.19/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.19/0.58    inference(cnf_transformation,[],[f7])).
% 0.19/0.58  fof(f7,axiom,(
% 0.19/0.58    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.19/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.19/0.58  fof(f17,plain,(
% 0.19/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.19/0.58    inference(cnf_transformation,[],[f6])).
% 0.19/0.58  fof(f6,axiom,(
% 0.19/0.58    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.19/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 0.19/0.58  fof(f31,plain,(
% 0.19/0.58    ( ! [X0,X3,X1] : (~r2_hidden(X3,k4_xboole_0(X0,X1)) | sP3(X3,X1,X0)) )),
% 0.19/0.58    inference(equality_resolution,[],[f24])).
% 0.19/0.58  fof(f24,plain,(
% 0.19/0.58    ( ! [X2,X0,X3,X1] : (sP3(X3,X1,X0) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.19/0.58    inference(cnf_transformation,[],[f2])).
% 0.19/0.58  fof(f67,plain,(
% 0.19/0.58    ( ! [X0] : (k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(X0,X0)) )),
% 0.19/0.58    inference(superposition,[],[f29,f13])).
% 0.19/0.58  fof(f29,plain,(
% 0.19/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 0.19/0.58    inference(definition_unfolding,[],[f14,f16,f16])).
% 0.19/0.58  fof(f14,plain,(
% 0.19/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.19/0.58    inference(cnf_transformation,[],[f1])).
% 0.19/0.58  fof(f1,axiom,(
% 0.19/0.58    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.19/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.19/0.58  fof(f507,plain,(
% 0.19/0.58    ( ! [X2] : (k2_xboole_0(X2,k1_xboole_0) = k4_xboole_0(X2,k4_xboole_0(X2,X2))) )),
% 0.19/0.58    inference(forward_demodulation,[],[f506,f13])).
% 0.19/0.58  fof(f506,plain,(
% 0.19/0.58    ( ! [X2] : (k4_xboole_0(X2,k4_xboole_0(X2,X2)) = k4_xboole_0(k2_xboole_0(X2,k1_xboole_0),k1_xboole_0)) )),
% 0.19/0.58    inference(forward_demodulation,[],[f494,f45])).
% 0.19/0.58  fof(f45,plain,(
% 0.19/0.58    ( ! [X4,X3] : (k4_xboole_0(X3,X4) = k4_xboole_0(X3,k2_xboole_0(X4,k1_xboole_0))) )),
% 0.19/0.58    inference(superposition,[],[f19,f13])).
% 0.19/0.58  fof(f19,plain,(
% 0.19/0.58    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.19/0.58    inference(cnf_transformation,[],[f5])).
% 0.19/0.58  fof(f5,axiom,(
% 0.19/0.58    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.19/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.19/0.58  fof(f494,plain,(
% 0.19/0.58    ( ! [X2] : (k4_xboole_0(k2_xboole_0(X2,k1_xboole_0),k1_xboole_0) = k4_xboole_0(X2,k4_xboole_0(X2,k2_xboole_0(X2,k1_xboole_0)))) )),
% 0.19/0.58    inference(superposition,[],[f29,f275])).
% 0.19/0.58  fof(f275,plain,(
% 0.19/0.58    ( ! [X2] : (k1_xboole_0 = k4_xboole_0(k2_xboole_0(X2,k1_xboole_0),X2)) )),
% 0.19/0.58    inference(forward_demodulation,[],[f237,f13])).
% 0.19/0.58  fof(f237,plain,(
% 0.19/0.58    ( ! [X2] : (k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k2_xboole_0(X2,k1_xboole_0),X2)) )),
% 0.19/0.58    inference(backward_demodulation,[],[f150,f222])).
% 0.19/0.58  fof(f150,plain,(
% 0.19/0.58    ( ! [X2] : (k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X2)) = k4_xboole_0(k2_xboole_0(X2,k1_xboole_0),X2)) )),
% 0.19/0.58    inference(forward_demodulation,[],[f129,f45])).
% 0.19/0.58  fof(f129,plain,(
% 0.19/0.58    ( ! [X2] : (k4_xboole_0(k2_xboole_0(X2,k1_xboole_0),X2) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k2_xboole_0(X2,k1_xboole_0)))) )),
% 0.19/0.58    inference(superposition,[],[f67,f45])).
% 0.19/0.58  fof(f420,plain,(
% 0.19/0.58    k4_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0)),
% 0.19/0.58    inference(backward_demodulation,[],[f35,f419])).
% 0.19/0.58  fof(f419,plain,(
% 0.19/0.58    ( ! [X4,X3] : (k1_xboole_0 = k4_xboole_0(X3,k2_xboole_0(X4,X3))) )),
% 0.19/0.58    inference(forward_demodulation,[],[f418,f250])).
% 0.19/0.58  fof(f418,plain,(
% 0.19/0.58    ( ! [X4,X3] : (k4_xboole_0(k4_xboole_0(X3,X4),k4_xboole_0(X3,X4)) = k4_xboole_0(X3,k2_xboole_0(X4,X3))) )),
% 0.19/0.58    inference(forward_demodulation,[],[f417,f19])).
% 0.19/0.58  fof(f417,plain,(
% 0.19/0.58    ( ! [X4,X3] : (k4_xboole_0(k4_xboole_0(X3,X4),k4_xboole_0(X3,X4)) = k4_xboole_0(k4_xboole_0(X3,X4),X3)) )),
% 0.19/0.58    inference(forward_demodulation,[],[f392,f96])).
% 0.19/0.58  fof(f96,plain,(
% 0.19/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) )),
% 0.19/0.58    inference(superposition,[],[f30,f29])).
% 0.19/0.58  fof(f392,plain,(
% 0.19/0.58    ( ! [X4,X3] : (k4_xboole_0(k4_xboole_0(X3,X4),X3) = k4_xboole_0(k4_xboole_0(X3,X4),k4_xboole_0(X3,k4_xboole_0(X4,k4_xboole_0(X4,X3))))) )),
% 0.19/0.58    inference(superposition,[],[f96,f29])).
% 0.19/0.58  fof(f35,plain,(
% 0.19/0.58    k4_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),sK0)))),
% 0.19/0.58    inference(backward_demodulation,[],[f33,f19])).
% 0.19/0.58  fof(f33,plain,(
% 0.19/0.58    k4_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0))),
% 0.19/0.58    inference(backward_demodulation,[],[f28,f30])).
% 0.19/0.58  fof(f28,plain,(
% 0.19/0.58    k4_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0))),
% 0.19/0.58    inference(definition_unfolding,[],[f12,f18,f16])).
% 0.19/0.58  fof(f18,plain,(
% 0.19/0.58    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 0.19/0.58    inference(cnf_transformation,[],[f3])).
% 0.19/0.58  fof(f3,axiom,(
% 0.19/0.58    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 0.19/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).
% 0.19/0.58  fof(f12,plain,(
% 0.19/0.58    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 0.19/0.58    inference(cnf_transformation,[],[f11])).
% 0.19/0.58  fof(f11,plain,(
% 0.19/0.58    ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.19/0.58    inference(ennf_transformation,[],[f10])).
% 0.19/0.58  fof(f10,negated_conjecture,(
% 0.19/0.58    ~! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.19/0.58    inference(negated_conjecture,[],[f9])).
% 0.19/0.58  fof(f9,conjecture,(
% 0.19/0.58    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.19/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.19/0.58  % SZS output end Proof for theBenchmark
% 0.19/0.58  % (14273)------------------------------
% 0.19/0.58  % (14273)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.58  % (14273)Termination reason: Refutation
% 0.19/0.58  
% 0.19/0.58  % (14273)Memory used [KB]: 6652
% 0.19/0.58  % (14273)Time elapsed: 0.172 s
% 0.19/0.58  % (14273)------------------------------
% 0.19/0.58  % (14273)------------------------------
% 0.19/0.59  % (14248)Success in time 0.237 s
%------------------------------------------------------------------------------
