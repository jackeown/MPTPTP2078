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
% DateTime   : Thu Dec  3 12:30:48 EST 2020

% Result     : Theorem 1.98s
% Output     : Refutation 1.98s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 111 expanded)
%              Number of leaves         :   12 (  34 expanded)
%              Depth                    :   17
%              Number of atoms          :   96 ( 239 expanded)
%              Number of equality atoms :   49 ( 122 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f857,plain,(
    $false ),
    inference(subsumption_resolution,[],[f856,f32])).

fof(f32,plain,(
    sK0 != sK2 ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( sK0 != sK2
    & r1_xboole_0(sK2,sK1)
    & r1_xboole_0(sK0,sK1)
    & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f23])).

fof(f23,plain,
    ( ? [X0,X1,X2] :
        ( X0 != X2
        & r1_xboole_0(X2,X1)
        & r1_xboole_0(X0,X1)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) )
   => ( sK0 != sK2
      & r1_xboole_0(sK2,sK1)
      & r1_xboole_0(sK0,sK1)
      & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( X0 != X2
      & r1_xboole_0(X2,X1)
      & r1_xboole_0(X0,X1)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( X0 != X2
      & r1_xboole_0(X2,X1)
      & r1_xboole_0(X0,X1)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_xboole_0(X2,X1)
          & r1_xboole_0(X0,X1)
          & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) )
       => X0 = X2 ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X2,X1)
        & r1_xboole_0(X0,X1)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) )
     => X0 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_xboole_1)).

fof(f856,plain,(
    sK0 = sK2 ),
    inference(forward_demodulation,[],[f855,f35])).

fof(f35,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f855,plain,(
    sK2 = k2_xboole_0(sK0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f843,f56])).

fof(f56,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f38,f35])).

fof(f38,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f843,plain,(
    sK2 = k2_xboole_0(sK0,k4_xboole_0(sK1,sK1)) ),
    inference(superposition,[],[f790,f631])).

fof(f631,plain,(
    ! [X21] : k4_xboole_0(k2_xboole_0(sK0,X21),sK1) = k2_xboole_0(sK0,k4_xboole_0(X21,sK1)) ),
    inference(superposition,[],[f47,f418])).

fof(f418,plain,(
    sK0 = k4_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f375,f58])).

fof(f58,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f40,f35])).

fof(f40,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f375,plain,(
    sK0 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f50,f190])).

fof(f190,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f188,f36])).

fof(f36,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f20,f25])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f188,plain,(
    ! [X0] : ~ r2_hidden(X0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(resolution,[],[f51,f30])).

fof(f30,plain,(
    r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(definition_unfolding,[],[f45,f41])).

fof(f41,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f21,f27])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f50,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f43,f41])).

% (11714)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
fof(f43,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f47,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_xboole_1)).

fof(f790,plain,(
    sK2 = k4_xboole_0(k2_xboole_0(sK0,sK1),sK1) ),
    inference(forward_demodulation,[],[f789,f35])).

fof(f789,plain,(
    k2_xboole_0(sK2,k1_xboole_0) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK1) ),
    inference(forward_demodulation,[],[f771,f56])).

fof(f771,plain,(
    k4_xboole_0(k2_xboole_0(sK0,sK1),sK1) = k2_xboole_0(sK2,k4_xboole_0(sK1,sK1)) ),
    inference(superposition,[],[f634,f29])).

fof(f29,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f634,plain,(
    ! [X24] : k4_xboole_0(k2_xboole_0(sK2,X24),sK1) = k2_xboole_0(sK2,k4_xboole_0(X24,sK1)) ),
    inference(superposition,[],[f47,f442])).

fof(f442,plain,(
    sK2 = k4_xboole_0(sK2,sK1) ),
    inference(superposition,[],[f377,f58])).

fof(f377,plain,(
    sK2 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK2,sK1)) ),
    inference(superposition,[],[f50,f191])).

fof(f191,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)) ),
    inference(resolution,[],[f189,f36])).

fof(f189,plain,(
    ! [X1] : ~ r2_hidden(X1,k4_xboole_0(sK2,k4_xboole_0(sK2,sK1))) ),
    inference(resolution,[],[f51,f31])).

fof(f31,plain,(
    r1_xboole_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:50:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.52  % (11718)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.52  % (11715)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.54  % (11739)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.54  % (11733)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.54  % (11730)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.55  % (11709)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.55  % (11723)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.56  % (11728)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.57  % (11736)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.58  % (11713)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.58  % (11732)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.58  % (11711)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.58  % (11725)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.59  % (11725)Refutation not found, incomplete strategy% (11725)------------------------------
% 0.22/0.59  % (11725)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.59  % (11725)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.59  
% 0.22/0.59  % (11725)Memory used [KB]: 6140
% 0.22/0.59  % (11725)Time elapsed: 0.002 s
% 0.22/0.59  % (11725)------------------------------
% 0.22/0.59  % (11725)------------------------------
% 0.22/0.59  % (11721)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.59  % (11721)Refutation not found, incomplete strategy% (11721)------------------------------
% 0.22/0.59  % (11721)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.59  % (11721)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.59  
% 0.22/0.59  % (11721)Memory used [KB]: 10618
% 0.22/0.59  % (11721)Time elapsed: 0.141 s
% 0.22/0.59  % (11721)------------------------------
% 0.22/0.59  % (11721)------------------------------
% 0.22/0.59  % (11717)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.59  % (11727)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.59  % (11735)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.59  % (11727)Refutation not found, incomplete strategy% (11727)------------------------------
% 0.22/0.59  % (11727)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.59  % (11727)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.59  
% 0.22/0.59  % (11727)Memory used [KB]: 10618
% 0.22/0.59  % (11727)Time elapsed: 0.149 s
% 0.22/0.59  % (11727)------------------------------
% 0.22/0.59  % (11727)------------------------------
% 0.22/0.59  % (11720)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.59  % (11720)Refutation not found, incomplete strategy% (11720)------------------------------
% 0.22/0.59  % (11720)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.59  % (11720)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.59  
% 0.22/0.59  % (11720)Memory used [KB]: 10618
% 0.22/0.59  % (11720)Time elapsed: 0.152 s
% 0.22/0.59  % (11720)------------------------------
% 0.22/0.59  % (11720)------------------------------
% 1.98/0.62  % (11713)Refutation found. Thanks to Tanya!
% 1.98/0.62  % SZS status Theorem for theBenchmark
% 1.98/0.62  % SZS output start Proof for theBenchmark
% 1.98/0.62  fof(f857,plain,(
% 1.98/0.62    $false),
% 1.98/0.62    inference(subsumption_resolution,[],[f856,f32])).
% 1.98/0.62  fof(f32,plain,(
% 1.98/0.62    sK0 != sK2),
% 1.98/0.62    inference(cnf_transformation,[],[f24])).
% 1.98/0.62  fof(f24,plain,(
% 1.98/0.62    sK0 != sK2 & r1_xboole_0(sK2,sK1) & r1_xboole_0(sK0,sK1) & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK1)),
% 1.98/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f23])).
% 1.98/0.62  fof(f23,plain,(
% 1.98/0.62    ? [X0,X1,X2] : (X0 != X2 & r1_xboole_0(X2,X1) & r1_xboole_0(X0,X1) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1)) => (sK0 != sK2 & r1_xboole_0(sK2,sK1) & r1_xboole_0(sK0,sK1) & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK1))),
% 1.98/0.62    introduced(choice_axiom,[])).
% 1.98/0.62  fof(f19,plain,(
% 1.98/0.62    ? [X0,X1,X2] : (X0 != X2 & r1_xboole_0(X2,X1) & r1_xboole_0(X0,X1) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1))),
% 1.98/0.62    inference(flattening,[],[f18])).
% 1.98/0.62  fof(f18,plain,(
% 1.98/0.62    ? [X0,X1,X2] : (X0 != X2 & (r1_xboole_0(X2,X1) & r1_xboole_0(X0,X1) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1)))),
% 1.98/0.62    inference(ennf_transformation,[],[f16])).
% 1.98/0.62  fof(f16,negated_conjecture,(
% 1.98/0.62    ~! [X0,X1,X2] : ((r1_xboole_0(X2,X1) & r1_xboole_0(X0,X1) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1)) => X0 = X2)),
% 1.98/0.62    inference(negated_conjecture,[],[f15])).
% 1.98/0.62  fof(f15,conjecture,(
% 1.98/0.62    ! [X0,X1,X2] : ((r1_xboole_0(X2,X1) & r1_xboole_0(X0,X1) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1)) => X0 = X2)),
% 1.98/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_xboole_1)).
% 1.98/0.62  fof(f856,plain,(
% 1.98/0.62    sK0 = sK2),
% 1.98/0.62    inference(forward_demodulation,[],[f855,f35])).
% 1.98/0.62  fof(f35,plain,(
% 1.98/0.62    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.98/0.62    inference(cnf_transformation,[],[f6])).
% 1.98/0.62  fof(f6,axiom,(
% 1.98/0.62    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 1.98/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 1.98/0.62  fof(f855,plain,(
% 1.98/0.62    sK2 = k2_xboole_0(sK0,k1_xboole_0)),
% 1.98/0.62    inference(forward_demodulation,[],[f843,f56])).
% 1.98/0.62  fof(f56,plain,(
% 1.98/0.62    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 1.98/0.62    inference(superposition,[],[f38,f35])).
% 1.98/0.62  fof(f38,plain,(
% 1.98/0.62    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 1.98/0.62    inference(cnf_transformation,[],[f11])).
% 1.98/0.62  fof(f11,axiom,(
% 1.98/0.62    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 1.98/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
% 1.98/0.62  fof(f843,plain,(
% 1.98/0.62    sK2 = k2_xboole_0(sK0,k4_xboole_0(sK1,sK1))),
% 1.98/0.62    inference(superposition,[],[f790,f631])).
% 1.98/0.62  fof(f631,plain,(
% 1.98/0.62    ( ! [X21] : (k4_xboole_0(k2_xboole_0(sK0,X21),sK1) = k2_xboole_0(sK0,k4_xboole_0(X21,sK1))) )),
% 1.98/0.62    inference(superposition,[],[f47,f418])).
% 1.98/0.62  fof(f418,plain,(
% 1.98/0.62    sK0 = k4_xboole_0(sK0,sK1)),
% 1.98/0.62    inference(superposition,[],[f375,f58])).
% 1.98/0.62  fof(f58,plain,(
% 1.98/0.62    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 1.98/0.62    inference(superposition,[],[f40,f35])).
% 1.98/0.62  fof(f40,plain,(
% 1.98/0.62    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.98/0.62    inference(cnf_transformation,[],[f1])).
% 1.98/0.62  fof(f1,axiom,(
% 1.98/0.62    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.98/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.98/0.62  fof(f375,plain,(
% 1.98/0.62    sK0 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK1))),
% 1.98/0.62    inference(superposition,[],[f50,f190])).
% 1.98/0.62  fof(f190,plain,(
% 1.98/0.62    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 1.98/0.62    inference(resolution,[],[f188,f36])).
% 1.98/0.62  fof(f36,plain,(
% 1.98/0.62    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 1.98/0.62    inference(cnf_transformation,[],[f26])).
% 1.98/0.62  fof(f26,plain,(
% 1.98/0.62    ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0)),
% 1.98/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f20,f25])).
% 1.98/0.62  fof(f25,plain,(
% 1.98/0.62    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 1.98/0.62    introduced(choice_axiom,[])).
% 1.98/0.62  fof(f20,plain,(
% 1.98/0.62    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.98/0.62    inference(ennf_transformation,[],[f4])).
% 1.98/0.62  fof(f4,axiom,(
% 1.98/0.62    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.98/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 1.98/0.62  fof(f188,plain,(
% 1.98/0.62    ( ! [X0] : (~r2_hidden(X0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) )),
% 1.98/0.62    inference(resolution,[],[f51,f30])).
% 1.98/0.62  fof(f30,plain,(
% 1.98/0.62    r1_xboole_0(sK0,sK1)),
% 1.98/0.62    inference(cnf_transformation,[],[f24])).
% 1.98/0.62  fof(f51,plain,(
% 1.98/0.62    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.98/0.62    inference(definition_unfolding,[],[f45,f41])).
% 1.98/0.62  fof(f41,plain,(
% 1.98/0.62    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.98/0.62    inference(cnf_transformation,[],[f12])).
% 1.98/0.62  fof(f12,axiom,(
% 1.98/0.62    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.98/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.98/0.62  fof(f45,plain,(
% 1.98/0.62    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 1.98/0.62    inference(cnf_transformation,[],[f28])).
% 1.98/0.62  fof(f28,plain,(
% 1.98/0.62    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.98/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f21,f27])).
% 1.98/0.62  fof(f27,plain,(
% 1.98/0.62    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)))),
% 1.98/0.62    introduced(choice_axiom,[])).
% 1.98/0.62  fof(f21,plain,(
% 1.98/0.62    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.98/0.62    inference(ennf_transformation,[],[f17])).
% 1.98/0.62  fof(f17,plain,(
% 1.98/0.62    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.98/0.62    inference(rectify,[],[f3])).
% 1.98/0.62  fof(f3,axiom,(
% 1.98/0.62    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.98/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.98/0.62  fof(f50,plain,(
% 1.98/0.62    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 1.98/0.62    inference(definition_unfolding,[],[f43,f41])).
% 1.98/0.62  % (11714)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.98/0.62  fof(f43,plain,(
% 1.98/0.62    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 1.98/0.62    inference(cnf_transformation,[],[f13])).
% 1.98/0.62  fof(f13,axiom,(
% 1.98/0.62    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 1.98/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).
% 1.98/0.62  fof(f47,plain,(
% 1.98/0.62    ( ! [X2,X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))) )),
% 1.98/0.62    inference(cnf_transformation,[],[f10])).
% 1.98/0.62  fof(f10,axiom,(
% 1.98/0.62    ! [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))),
% 1.98/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_xboole_1)).
% 1.98/0.62  fof(f790,plain,(
% 1.98/0.62    sK2 = k4_xboole_0(k2_xboole_0(sK0,sK1),sK1)),
% 1.98/0.62    inference(forward_demodulation,[],[f789,f35])).
% 1.98/0.62  fof(f789,plain,(
% 1.98/0.62    k2_xboole_0(sK2,k1_xboole_0) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK1)),
% 1.98/0.62    inference(forward_demodulation,[],[f771,f56])).
% 1.98/0.62  fof(f771,plain,(
% 1.98/0.62    k4_xboole_0(k2_xboole_0(sK0,sK1),sK1) = k2_xboole_0(sK2,k4_xboole_0(sK1,sK1))),
% 1.98/0.62    inference(superposition,[],[f634,f29])).
% 1.98/0.62  fof(f29,plain,(
% 1.98/0.62    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK1)),
% 1.98/0.62    inference(cnf_transformation,[],[f24])).
% 1.98/0.62  fof(f634,plain,(
% 1.98/0.62    ( ! [X24] : (k4_xboole_0(k2_xboole_0(sK2,X24),sK1) = k2_xboole_0(sK2,k4_xboole_0(X24,sK1))) )),
% 1.98/0.62    inference(superposition,[],[f47,f442])).
% 1.98/0.62  fof(f442,plain,(
% 1.98/0.62    sK2 = k4_xboole_0(sK2,sK1)),
% 1.98/0.62    inference(superposition,[],[f377,f58])).
% 1.98/0.62  fof(f377,plain,(
% 1.98/0.62    sK2 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK2,sK1))),
% 1.98/0.62    inference(superposition,[],[f50,f191])).
% 1.98/0.62  fof(f191,plain,(
% 1.98/0.62    k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK1))),
% 1.98/0.62    inference(resolution,[],[f189,f36])).
% 1.98/0.62  fof(f189,plain,(
% 1.98/0.62    ( ! [X1] : (~r2_hidden(X1,k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)))) )),
% 1.98/0.62    inference(resolution,[],[f51,f31])).
% 1.98/0.62  fof(f31,plain,(
% 1.98/0.62    r1_xboole_0(sK2,sK1)),
% 1.98/0.62    inference(cnf_transformation,[],[f24])).
% 1.98/0.62  % SZS output end Proof for theBenchmark
% 1.98/0.62  % (11713)------------------------------
% 1.98/0.62  % (11713)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.98/0.62  % (11713)Termination reason: Refutation
% 1.98/0.62  
% 1.98/0.62  % (11713)Memory used [KB]: 11129
% 1.98/0.62  % (11713)Time elapsed: 0.178 s
% 1.98/0.62  % (11713)------------------------------
% 1.98/0.62  % (11713)------------------------------
% 1.98/0.63  % (11701)Success in time 0.257 s
%------------------------------------------------------------------------------
