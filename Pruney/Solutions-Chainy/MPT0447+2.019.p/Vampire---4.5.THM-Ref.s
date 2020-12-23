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
% DateTime   : Thu Dec  3 12:47:11 EST 2020

% Result     : Theorem 1.51s
% Output     : Refutation 2.11s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 189 expanded)
%              Number of leaves         :    9 (  40 expanded)
%              Depth                    :   21
%              Number of atoms          :  156 ( 537 expanded)
%              Number of equality atoms :   10 (  38 expanded)
%              Maximal formula depth    :    7 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f255,plain,(
    $false ),
    inference(subsumption_resolution,[],[f252,f178])).

fof(f178,plain,(
    ~ r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f177,f31])).

fof(f31,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( r1_tarski(X0,X1)
             => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relat_1)).

fof(f177,plain,
    ( ~ r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1))
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f176,f29])).

fof(f29,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f176,plain,
    ( ~ r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1))
    | ~ r1_tarski(sK0,sK1)
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f174,f28])).

fof(f28,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f174,plain,
    ( ~ r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | ~ r1_tarski(sK0,sK1)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f173,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

fof(f173,plain,
    ( ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1))
    | ~ r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f170,f30])).

fof(f30,plain,(
    ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f170,plain,
    ( r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))
    | ~ r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1))
    | ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1)) ),
    inference(resolution,[],[f113,f100])).

fof(f100,plain,(
    ! [X1] :
      ( r1_tarski(X1,k3_relat_1(sK1))
      | ~ r1_tarski(X1,k2_relat_1(sK1)) ) ),
    inference(superposition,[],[f58,f68])).

fof(f68,plain,(
    k3_relat_1(sK1) = k3_tarski(k2_tarski(k1_relat_1(sK1),k2_relat_1(sK1))) ),
    inference(resolution,[],[f28,f57])).

fof(f57,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k3_relat_1(X0) = k3_tarski(k2_tarski(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    inference(definition_unfolding,[],[f32,f36])).

fof(f36,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f32,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_tarski(k2_tarski(X2,X1)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f49,f36])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f113,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(sK0),X0)
      | r1_tarski(k3_relat_1(sK0),X0)
      | ~ r1_tarski(k1_relat_1(sK0),X0) ) ),
    inference(superposition,[],[f59,f72])).

fof(f72,plain,(
    k3_relat_1(sK0) = k3_tarski(k2_tarski(k1_relat_1(sK0),k2_relat_1(sK0))) ),
    inference(resolution,[],[f31,f57])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_tarski(k2_tarski(X0,X2)),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f50,f36])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X2,X1)
      | r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

fof(f252,plain,(
    r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(resolution,[],[f251,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f251,plain,(
    r2_hidden(sK2(k1_relat_1(sK0),k3_relat_1(sK1)),k3_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f250,f29])).

fof(f250,plain,
    ( ~ r1_tarski(sK0,sK1)
    | r2_hidden(sK2(k1_relat_1(sK0),k3_relat_1(sK1)),k3_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f244,f28])).

fof(f244,plain,
    ( ~ v1_relat_1(sK1)
    | ~ r1_tarski(sK0,sK1)
    | r2_hidden(sK2(k1_relat_1(sK0),k3_relat_1(sK1)),k3_relat_1(sK1)) ),
    inference(resolution,[],[f202,f92])).

fof(f92,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k1_relat_1(sK1))
      | r2_hidden(X1,k3_relat_1(sK1)) ) ),
    inference(resolution,[],[f65,f60])).

fof(f60,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X2,sK4(X0,X2)),X0)
      | ~ r2_hidden(X2,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X2,sK4(X0,X2)),X0)
      | ~ r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),sK1)
      | r2_hidden(X0,k3_relat_1(sK1)) ) ),
    inference(resolution,[],[f28,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | r2_hidden(X0,k3_relat_1(X2)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k3_relat_1(X2))
          & r2_hidden(X0,k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_relat_1)).

fof(f202,plain,(
    ! [X0] :
      ( r2_hidden(sK2(k1_relat_1(sK0),k3_relat_1(sK1)),k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | ~ r1_tarski(sK0,X0) ) ),
    inference(subsumption_resolution,[],[f197,f31])).

fof(f197,plain,(
    ! [X0] :
      ( r2_hidden(sK2(k1_relat_1(sK0),k3_relat_1(sK1)),k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | ~ r1_tarski(sK0,X0)
      | ~ v1_relat_1(sK0) ) ),
    inference(resolution,[],[f184,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f184,plain,(
    ! [X1] :
      ( ~ r1_tarski(k1_relat_1(sK0),X1)
      | r2_hidden(sK2(k1_relat_1(sK0),k3_relat_1(sK1)),X1) ) ),
    inference(resolution,[],[f180,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f180,plain,(
    r2_hidden(sK2(k1_relat_1(sK0),k3_relat_1(sK1)),k1_relat_1(sK0)) ),
    inference(resolution,[],[f178,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.15/0.36  % Computer   : n007.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % WCLimit    : 600
% 0.15/0.36  % DateTime   : Tue Dec  1 13:40:21 EST 2020
% 0.15/0.36  % CPUTime    : 
% 1.24/0.57  % (23570)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.24/0.57  % (23569)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.24/0.58  % (23569)Refutation not found, incomplete strategy% (23569)------------------------------
% 1.24/0.58  % (23569)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.58  % (23569)Termination reason: Refutation not found, incomplete strategy
% 1.24/0.58  
% 1.24/0.58  % (23569)Memory used [KB]: 10618
% 1.24/0.58  % (23569)Time elapsed: 0.124 s
% 1.51/0.58  % (23569)------------------------------
% 1.51/0.58  % (23569)------------------------------
% 1.51/0.58  % (23577)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.51/0.58  % (23585)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.51/0.58  % (23586)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.51/0.58  % (23578)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.51/0.61  % (23562)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.51/0.61  % (23561)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.51/0.62  % (23560)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.51/0.62  % (23575)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.51/0.62  % (23575)Refutation not found, incomplete strategy% (23575)------------------------------
% 1.51/0.62  % (23575)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.62  % (23575)Termination reason: Refutation not found, incomplete strategy
% 1.51/0.62  
% 1.51/0.62  % (23575)Memory used [KB]: 10618
% 1.51/0.62  % (23575)Time elapsed: 0.178 s
% 1.51/0.62  % (23575)------------------------------
% 1.51/0.62  % (23575)------------------------------
% 1.51/0.62  % (23584)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.51/0.62  % (23573)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.51/0.62  % (23574)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.51/0.63  % (23571)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.51/0.63  % (23576)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.51/0.63  % (23583)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.51/0.63  % (23568)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.51/0.63  % (23568)Refutation not found, incomplete strategy% (23568)------------------------------
% 1.51/0.63  % (23568)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.63  % (23558)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.51/0.63  % (23568)Termination reason: Refutation not found, incomplete strategy
% 1.51/0.63  
% 1.51/0.63  % (23568)Memory used [KB]: 10618
% 1.51/0.63  % (23568)Time elapsed: 0.181 s
% 1.51/0.63  % (23568)------------------------------
% 1.51/0.63  % (23568)------------------------------
% 1.51/0.63  % (23558)Refutation not found, incomplete strategy% (23558)------------------------------
% 1.51/0.63  % (23558)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.63  % (23558)Termination reason: Refutation not found, incomplete strategy
% 1.51/0.63  
% 1.51/0.63  % (23558)Memory used [KB]: 1663
% 1.51/0.63  % (23558)Time elapsed: 0.175 s
% 1.51/0.63  % (23558)------------------------------
% 1.51/0.63  % (23558)------------------------------
% 1.51/0.63  % (23565)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.51/0.63  % (23563)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.51/0.63  % (23566)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.51/0.63  % (23567)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.51/0.63  % (23567)Refutation not found, incomplete strategy% (23567)------------------------------
% 1.51/0.63  % (23567)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.63  % (23567)Termination reason: Refutation not found, incomplete strategy
% 1.51/0.63  
% 1.51/0.63  % (23567)Memory used [KB]: 10618
% 1.51/0.63  % (23567)Time elapsed: 0.191 s
% 1.51/0.63  % (23567)------------------------------
% 1.51/0.63  % (23567)------------------------------
% 1.51/0.63  % (23564)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.51/0.64  % (23559)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.51/0.64  % (23587)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.51/0.64  % (23582)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.51/0.64  % (23580)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.51/0.64  % (23572)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.51/0.64  % (23581)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.51/0.64  % (23579)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.51/0.65  % (23579)Refutation found. Thanks to Tanya!
% 1.51/0.65  % SZS status Theorem for theBenchmark
% 2.11/0.67  % (23580)Refutation not found, incomplete strategy% (23580)------------------------------
% 2.11/0.67  % (23580)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.11/0.67  % (23580)Termination reason: Refutation not found, incomplete strategy
% 2.11/0.67  
% 2.11/0.67  % (23580)Memory used [KB]: 10746
% 2.11/0.67  % (23580)Time elapsed: 0.218 s
% 2.11/0.67  % (23580)------------------------------
% 2.11/0.67  % (23580)------------------------------
% 2.11/0.67  % SZS output start Proof for theBenchmark
% 2.11/0.67  fof(f255,plain,(
% 2.11/0.67    $false),
% 2.11/0.67    inference(subsumption_resolution,[],[f252,f178])).
% 2.11/0.67  fof(f178,plain,(
% 2.11/0.67    ~r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1))),
% 2.11/0.67    inference(subsumption_resolution,[],[f177,f31])).
% 2.11/0.67  fof(f31,plain,(
% 2.11/0.67    v1_relat_1(sK0)),
% 2.11/0.67    inference(cnf_transformation,[],[f16])).
% 2.11/0.67  fof(f16,plain,(
% 2.11/0.67    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 2.11/0.67    inference(flattening,[],[f15])).
% 2.11/0.67  fof(f15,plain,(
% 2.11/0.67    ? [X0] : (? [X1] : ((~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 2.11/0.67    inference(ennf_transformation,[],[f14])).
% 2.11/0.67  fof(f14,negated_conjecture,(
% 2.11/0.67    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 2.11/0.67    inference(negated_conjecture,[],[f13])).
% 2.11/0.67  fof(f13,conjecture,(
% 2.11/0.67    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 2.11/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relat_1)).
% 2.11/0.67  fof(f177,plain,(
% 2.11/0.67    ~r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1)) | ~v1_relat_1(sK0)),
% 2.11/0.67    inference(subsumption_resolution,[],[f176,f29])).
% 2.11/0.67  fof(f29,plain,(
% 2.11/0.67    r1_tarski(sK0,sK1)),
% 2.11/0.67    inference(cnf_transformation,[],[f16])).
% 2.11/0.67  fof(f176,plain,(
% 2.11/0.67    ~r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1)) | ~r1_tarski(sK0,sK1) | ~v1_relat_1(sK0)),
% 2.11/0.67    inference(subsumption_resolution,[],[f174,f28])).
% 2.11/0.67  fof(f28,plain,(
% 2.11/0.67    v1_relat_1(sK1)),
% 2.11/0.67    inference(cnf_transformation,[],[f16])).
% 2.11/0.67  fof(f174,plain,(
% 2.11/0.67    ~r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1)) | ~v1_relat_1(sK1) | ~r1_tarski(sK0,sK1) | ~v1_relat_1(sK0)),
% 2.11/0.67    inference(resolution,[],[f173,f34])).
% 2.11/0.67  fof(f34,plain,(
% 2.11/0.67    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~r1_tarski(X0,X1) | ~v1_relat_1(X0)) )),
% 2.11/0.67    inference(cnf_transformation,[],[f19])).
% 2.11/0.67  fof(f19,plain,(
% 2.11/0.67    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.11/0.67    inference(flattening,[],[f18])).
% 2.11/0.67  fof(f18,plain,(
% 2.11/0.67    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.11/0.67    inference(ennf_transformation,[],[f11])).
% 2.11/0.67  fof(f11,axiom,(
% 2.11/0.67    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 2.11/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).
% 2.11/0.67  fof(f173,plain,(
% 2.11/0.67    ~r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1)) | ~r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1))),
% 2.11/0.67    inference(subsumption_resolution,[],[f170,f30])).
% 2.11/0.67  fof(f30,plain,(
% 2.11/0.67    ~r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))),
% 2.11/0.67    inference(cnf_transformation,[],[f16])).
% 2.11/0.67  fof(f170,plain,(
% 2.11/0.67    r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) | ~r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1)) | ~r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1))),
% 2.11/0.67    inference(resolution,[],[f113,f100])).
% 2.11/0.67  fof(f100,plain,(
% 2.11/0.67    ( ! [X1] : (r1_tarski(X1,k3_relat_1(sK1)) | ~r1_tarski(X1,k2_relat_1(sK1))) )),
% 2.11/0.67    inference(superposition,[],[f58,f68])).
% 2.11/0.67  fof(f68,plain,(
% 2.11/0.67    k3_relat_1(sK1) = k3_tarski(k2_tarski(k1_relat_1(sK1),k2_relat_1(sK1)))),
% 2.11/0.67    inference(resolution,[],[f28,f57])).
% 2.11/0.67  fof(f57,plain,(
% 2.11/0.67    ( ! [X0] : (~v1_relat_1(X0) | k3_relat_1(X0) = k3_tarski(k2_tarski(k1_relat_1(X0),k2_relat_1(X0)))) )),
% 2.11/0.67    inference(definition_unfolding,[],[f32,f36])).
% 2.11/0.67  fof(f36,plain,(
% 2.11/0.67    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 2.11/0.67    inference(cnf_transformation,[],[f6])).
% 2.11/0.67  fof(f6,axiom,(
% 2.11/0.67    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 2.11/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 2.11/0.67  fof(f32,plain,(
% 2.11/0.67    ( ! [X0] : (~v1_relat_1(X0) | k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))) )),
% 2.11/0.67    inference(cnf_transformation,[],[f17])).
% 2.11/0.67  fof(f17,plain,(
% 2.11/0.67    ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 2.11/0.67    inference(ennf_transformation,[],[f10])).
% 2.11/0.67  fof(f10,axiom,(
% 2.11/0.67    ! [X0] : (v1_relat_1(X0) => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)))),
% 2.11/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).
% 2.11/0.67  fof(f58,plain,(
% 2.11/0.67    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_tarski(k2_tarski(X2,X1))) | ~r1_tarski(X0,X1)) )),
% 2.11/0.67    inference(definition_unfolding,[],[f49,f36])).
% 2.11/0.67  fof(f49,plain,(
% 2.11/0.67    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(X0,k2_xboole_0(X2,X1))) )),
% 2.11/0.67    inference(cnf_transformation,[],[f25])).
% 2.11/0.67  fof(f25,plain,(
% 2.11/0.67    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 2.11/0.67    inference(ennf_transformation,[],[f3])).
% 2.11/0.67  fof(f3,axiom,(
% 2.11/0.67    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 2.11/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).
% 2.11/0.67  fof(f113,plain,(
% 2.11/0.67    ( ! [X0] : (~r1_tarski(k2_relat_1(sK0),X0) | r1_tarski(k3_relat_1(sK0),X0) | ~r1_tarski(k1_relat_1(sK0),X0)) )),
% 2.11/0.67    inference(superposition,[],[f59,f72])).
% 2.11/0.67  fof(f72,plain,(
% 2.11/0.67    k3_relat_1(sK0) = k3_tarski(k2_tarski(k1_relat_1(sK0),k2_relat_1(sK0)))),
% 2.11/0.67    inference(resolution,[],[f31,f57])).
% 2.11/0.67  fof(f59,plain,(
% 2.11/0.67    ( ! [X2,X0,X1] : (r1_tarski(k3_tarski(k2_tarski(X0,X2)),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 2.11/0.67    inference(definition_unfolding,[],[f50,f36])).
% 2.11/0.67  fof(f50,plain,(
% 2.11/0.67    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X2,X1) | r1_tarski(k2_xboole_0(X0,X2),X1)) )),
% 2.11/0.67    inference(cnf_transformation,[],[f27])).
% 2.11/0.67  fof(f27,plain,(
% 2.11/0.67    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 2.11/0.67    inference(flattening,[],[f26])).
% 2.11/0.67  fof(f26,plain,(
% 2.11/0.67    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 2.11/0.67    inference(ennf_transformation,[],[f5])).
% 2.11/0.67  fof(f5,axiom,(
% 2.11/0.67    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 2.11/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).
% 2.11/0.67  fof(f252,plain,(
% 2.11/0.67    r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1))),
% 2.11/0.67    inference(resolution,[],[f251,f40])).
% 2.11/0.67  fof(f40,plain,(
% 2.11/0.67    ( ! [X0,X1] : (~r2_hidden(sK2(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 2.11/0.67    inference(cnf_transformation,[],[f22])).
% 2.11/0.67  fof(f22,plain,(
% 2.11/0.67    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.11/0.67    inference(ennf_transformation,[],[f1])).
% 2.11/0.67  fof(f1,axiom,(
% 2.11/0.67    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.11/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 2.11/0.67  fof(f251,plain,(
% 2.11/0.67    r2_hidden(sK2(k1_relat_1(sK0),k3_relat_1(sK1)),k3_relat_1(sK1))),
% 2.11/0.67    inference(subsumption_resolution,[],[f250,f29])).
% 2.11/0.67  fof(f250,plain,(
% 2.11/0.67    ~r1_tarski(sK0,sK1) | r2_hidden(sK2(k1_relat_1(sK0),k3_relat_1(sK1)),k3_relat_1(sK1))),
% 2.11/0.67    inference(subsumption_resolution,[],[f244,f28])).
% 2.11/0.67  fof(f244,plain,(
% 2.11/0.67    ~v1_relat_1(sK1) | ~r1_tarski(sK0,sK1) | r2_hidden(sK2(k1_relat_1(sK0),k3_relat_1(sK1)),k3_relat_1(sK1))),
% 2.11/0.67    inference(resolution,[],[f202,f92])).
% 2.11/0.67  fof(f92,plain,(
% 2.11/0.67    ( ! [X1] : (~r2_hidden(X1,k1_relat_1(sK1)) | r2_hidden(X1,k3_relat_1(sK1))) )),
% 2.11/0.67    inference(resolution,[],[f65,f60])).
% 2.11/0.67  fof(f60,plain,(
% 2.11/0.67    ( ! [X2,X0] : (r2_hidden(k4_tarski(X2,sK4(X0,X2)),X0) | ~r2_hidden(X2,k1_relat_1(X0))) )),
% 2.11/0.67    inference(equality_resolution,[],[f42])).
% 2.11/0.67  fof(f42,plain,(
% 2.11/0.67    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X2,sK4(X0,X2)),X0) | ~r2_hidden(X2,X1) | k1_relat_1(X0) != X1) )),
% 2.11/0.67    inference(cnf_transformation,[],[f9])).
% 2.11/0.67  fof(f9,axiom,(
% 2.11/0.67    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 2.11/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).
% 2.11/0.67  fof(f65,plain,(
% 2.11/0.67    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK1) | r2_hidden(X0,k3_relat_1(sK1))) )),
% 2.11/0.67    inference(resolution,[],[f28,f47])).
% 2.11/0.67  fof(f47,plain,(
% 2.11/0.67    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(k4_tarski(X0,X1),X2) | r2_hidden(X0,k3_relat_1(X2))) )),
% 2.11/0.67    inference(cnf_transformation,[],[f24])).
% 2.11/0.67  fof(f24,plain,(
% 2.11/0.67    ! [X0,X1,X2] : ((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2))),
% 2.11/0.67    inference(flattening,[],[f23])).
% 2.11/0.67  fof(f23,plain,(
% 2.11/0.67    ! [X0,X1,X2] : (((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2)) | ~v1_relat_1(X2))),
% 2.11/0.67    inference(ennf_transformation,[],[f12])).
% 2.11/0.67  fof(f12,axiom,(
% 2.11/0.67    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)))))),
% 2.11/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_relat_1)).
% 2.11/0.67  fof(f202,plain,(
% 2.11/0.67    ( ! [X0] : (r2_hidden(sK2(k1_relat_1(sK0),k3_relat_1(sK1)),k1_relat_1(X0)) | ~v1_relat_1(X0) | ~r1_tarski(sK0,X0)) )),
% 2.11/0.67    inference(subsumption_resolution,[],[f197,f31])).
% 2.11/0.67  fof(f197,plain,(
% 2.11/0.67    ( ! [X0] : (r2_hidden(sK2(k1_relat_1(sK0),k3_relat_1(sK1)),k1_relat_1(X0)) | ~v1_relat_1(X0) | ~r1_tarski(sK0,X0) | ~v1_relat_1(sK0)) )),
% 2.11/0.67    inference(resolution,[],[f184,f33])).
% 2.11/0.67  fof(f33,plain,(
% 2.11/0.67    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~r1_tarski(X0,X1) | ~v1_relat_1(X0)) )),
% 2.11/0.67    inference(cnf_transformation,[],[f19])).
% 2.11/0.67  fof(f184,plain,(
% 2.11/0.67    ( ! [X1] : (~r1_tarski(k1_relat_1(sK0),X1) | r2_hidden(sK2(k1_relat_1(sK0),k3_relat_1(sK1)),X1)) )),
% 2.11/0.67    inference(resolution,[],[f180,f38])).
% 2.11/0.67  fof(f38,plain,(
% 2.11/0.67    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 2.11/0.67    inference(cnf_transformation,[],[f22])).
% 2.11/0.67  fof(f180,plain,(
% 2.11/0.67    r2_hidden(sK2(k1_relat_1(sK0),k3_relat_1(sK1)),k1_relat_1(sK0))),
% 2.11/0.67    inference(resolution,[],[f178,f39])).
% 2.11/0.67  fof(f39,plain,(
% 2.11/0.67    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK2(X0,X1),X0)) )),
% 2.11/0.67    inference(cnf_transformation,[],[f22])).
% 2.11/0.67  % SZS output end Proof for theBenchmark
% 2.11/0.67  % (23579)------------------------------
% 2.11/0.67  % (23579)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.11/0.67  % (23579)Termination reason: Refutation
% 2.11/0.67  
% 2.11/0.67  % (23579)Memory used [KB]: 1791
% 2.11/0.67  % (23579)Time elapsed: 0.158 s
% 2.11/0.67  % (23579)------------------------------
% 2.11/0.67  % (23579)------------------------------
% 2.11/0.67  % (23557)Success in time 0.286 s
%------------------------------------------------------------------------------
