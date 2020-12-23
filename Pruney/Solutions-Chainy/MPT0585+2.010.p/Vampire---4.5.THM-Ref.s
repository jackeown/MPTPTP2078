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
% DateTime   : Thu Dec  3 12:50:53 EST 2020

% Result     : Theorem 1.43s
% Output     : Refutation 1.61s
% Verified   : 
% Statistics : Number of formulae       :   39 ( 115 expanded)
%              Number of leaves         :    7 (  26 expanded)
%              Depth                    :   12
%              Number of atoms          :   79 ( 254 expanded)
%              Number of equality atoms :   21 (  82 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f427,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f380,f425,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK2(X0,X1),X0) ) ),
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f425,plain,(
    ! [X0] : ~ r2_hidden(sK2(k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(sK0)),k3_xboole_0(k1_relat_1(sK0),X0)) ),
    inference(forward_demodulation,[],[f393,f51])).

fof(f51,plain,(
    ! [X0] : k1_relat_1(k7_relat_1(sK0,X0)) = k3_xboole_0(k1_relat_1(sK0),X0) ),
    inference(unit_resulting_resolution,[],[f25,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

fof(f25,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k7_relat_1(X0,k1_relat_1(X1)) != k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0))))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0)))) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t189_relat_1)).

fof(f393,plain,(
    ! [X0] : ~ r2_hidden(sK2(k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(sK0)),k1_relat_1(k7_relat_1(sK0,X0))) ),
    inference(unit_resulting_resolution,[],[f25,f390,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

% (7779)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_relat_1)).

fof(f390,plain,(
    ~ r2_hidden(sK2(k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(sK0)),k1_relat_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f380,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f380,plain,(
    ~ r1_tarski(k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f46,f126])).

fof(f126,plain,(
    ! [X17,X16] :
      ( ~ r1_tarski(k3_xboole_0(k1_relat_1(sK0),X16),X17)
      | k7_relat_1(sK0,X16) = k7_relat_1(sK0,k3_xboole_0(X16,X17)) ) ),
    inference(forward_demodulation,[],[f125,f50])).

fof(f50,plain,(
    ! [X0,X1] : k7_relat_1(k7_relat_1(sK0,X0),X1) = k7_relat_1(sK0,k3_xboole_0(X0,X1)) ),
    inference(unit_resulting_resolution,[],[f25,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

fof(f125,plain,(
    ! [X17,X16] :
      ( ~ r1_tarski(k3_xboole_0(k1_relat_1(sK0),X16),X17)
      | k7_relat_1(sK0,X16) = k7_relat_1(k7_relat_1(sK0,X16),X17) ) ),
    inference(forward_demodulation,[],[f104,f51])).

fof(f104,plain,(
    ! [X17,X16] :
      ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK0,X16)),X17)
      | k7_relat_1(sK0,X16) = k7_relat_1(k7_relat_1(sK0,X16),X17) ) ),
    inference(resolution,[],[f52,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | k7_relat_1(X1,X0) = X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

fof(f52,plain,(
    ! [X0] : v1_relat_1(k7_relat_1(sK0,X0)) ),
    inference(unit_resulting_resolution,[],[f25,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k7_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f46,plain,(
    k7_relat_1(sK0,k1_relat_1(sK1)) != k7_relat_1(sK0,k3_xboole_0(k1_relat_1(sK1),k1_relat_1(sK0))) ),
    inference(backward_demodulation,[],[f24,f37])).

fof(f37,plain,(
    ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k3_xboole_0(k1_relat_1(sK1),X0) ),
    inference(unit_resulting_resolution,[],[f23,f27])).

fof(f23,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f24,plain,(
    k7_relat_1(sK0,k1_relat_1(sK1)) != k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0)))) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:26:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.52  % (7770)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.52  % (7750)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.52  % (7778)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.53  % (7762)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (7754)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (7777)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (7753)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (7755)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.54  % (7760)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.54  % (7759)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.43/0.55  % (7756)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.43/0.55  % (7766)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.43/0.55  % (7769)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.43/0.55  % (7776)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.43/0.55  % (7775)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.43/0.56  % (7758)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.43/0.56  % (7751)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.43/0.56  % (7764)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.43/0.56  % (7772)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.43/0.56  % (7761)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.43/0.56  % (7772)Refutation not found, incomplete strategy% (7772)------------------------------
% 1.43/0.56  % (7772)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.56  % (7772)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.56  
% 1.43/0.56  % (7772)Memory used [KB]: 10746
% 1.43/0.56  % (7772)Time elapsed: 0.160 s
% 1.43/0.56  % (7772)------------------------------
% 1.43/0.56  % (7772)------------------------------
% 1.43/0.56  % (7767)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.43/0.56  % (7768)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.43/0.56  % (7752)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.43/0.56  % (7754)Refutation found. Thanks to Tanya!
% 1.43/0.56  % SZS status Theorem for theBenchmark
% 1.61/0.57  % (7773)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.61/0.57  % (7767)Refutation not found, incomplete strategy% (7767)------------------------------
% 1.61/0.57  % (7767)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.61/0.57  % (7767)Termination reason: Refutation not found, incomplete strategy
% 1.61/0.57  
% 1.61/0.57  % (7767)Memory used [KB]: 10618
% 1.61/0.57  % (7767)Time elapsed: 0.169 s
% 1.61/0.57  % (7767)------------------------------
% 1.61/0.57  % (7767)------------------------------
% 1.61/0.58  % (7765)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.61/0.58  % SZS output start Proof for theBenchmark
% 1.61/0.58  fof(f427,plain,(
% 1.61/0.58    $false),
% 1.61/0.58    inference(unit_resulting_resolution,[],[f380,f425,f34])).
% 1.61/0.59  fof(f34,plain,(
% 1.61/0.59    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK2(X0,X1),X0)) )),
% 1.61/0.59    inference(cnf_transformation,[],[f22])).
% 1.61/0.59  fof(f22,plain,(
% 1.61/0.59    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.61/0.59    inference(ennf_transformation,[],[f1])).
% 1.61/0.59  fof(f1,axiom,(
% 1.61/0.59    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.61/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.61/0.59  fof(f425,plain,(
% 1.61/0.59    ( ! [X0] : (~r2_hidden(sK2(k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(sK0)),k3_xboole_0(k1_relat_1(sK0),X0))) )),
% 1.61/0.59    inference(forward_demodulation,[],[f393,f51])).
% 1.61/0.59  fof(f51,plain,(
% 1.61/0.59    ( ! [X0] : (k1_relat_1(k7_relat_1(sK0,X0)) = k3_xboole_0(k1_relat_1(sK0),X0)) )),
% 1.61/0.59    inference(unit_resulting_resolution,[],[f25,f27])).
% 1.61/0.59  fof(f27,plain,(
% 1.61/0.59    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)) )),
% 1.61/0.59    inference(cnf_transformation,[],[f17])).
% 1.61/0.59  fof(f17,plain,(
% 1.61/0.59    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.61/0.59    inference(ennf_transformation,[],[f11])).
% 1.61/0.59  fof(f11,axiom,(
% 1.61/0.59    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 1.61/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).
% 1.61/0.59  fof(f25,plain,(
% 1.61/0.59    v1_relat_1(sK0)),
% 1.61/0.59    inference(cnf_transformation,[],[f15])).
% 1.61/0.59  fof(f15,plain,(
% 1.61/0.59    ? [X0] : (? [X1] : (k7_relat_1(X0,k1_relat_1(X1)) != k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0)))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 1.61/0.59    inference(ennf_transformation,[],[f14])).
% 1.61/0.59  fof(f14,negated_conjecture,(
% 1.61/0.59    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0))))))),
% 1.61/0.59    inference(negated_conjecture,[],[f13])).
% 1.61/0.59  fof(f13,conjecture,(
% 1.61/0.59    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0))))))),
% 1.61/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t189_relat_1)).
% 1.61/0.59  fof(f393,plain,(
% 1.61/0.59    ( ! [X0] : (~r2_hidden(sK2(k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(sK0)),k1_relat_1(k7_relat_1(sK0,X0)))) )),
% 1.61/0.59    inference(unit_resulting_resolution,[],[f25,f390,f30])).
% 1.61/0.59  fof(f30,plain,(
% 1.61/0.59    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))) )),
% 1.61/0.59    inference(cnf_transformation,[],[f19])).
% 1.61/0.59  % (7779)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.61/0.59  fof(f19,plain,(
% 1.61/0.59    ! [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))) | ~v1_relat_1(X2))),
% 1.61/0.59    inference(ennf_transformation,[],[f10])).
% 1.61/0.59  fof(f10,axiom,(
% 1.61/0.59    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))))),
% 1.61/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_relat_1)).
% 1.61/0.59  fof(f390,plain,(
% 1.61/0.59    ~r2_hidden(sK2(k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(sK0)),k1_relat_1(sK0))),
% 1.61/0.59    inference(unit_resulting_resolution,[],[f380,f35])).
% 1.61/0.59  fof(f35,plain,(
% 1.61/0.59    ( ! [X0,X1] : (~r2_hidden(sK2(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.61/0.59    inference(cnf_transformation,[],[f22])).
% 1.61/0.59  fof(f380,plain,(
% 1.61/0.59    ~r1_tarski(k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(sK0))),
% 1.61/0.59    inference(unit_resulting_resolution,[],[f46,f126])).
% 1.61/0.59  fof(f126,plain,(
% 1.61/0.59    ( ! [X17,X16] : (~r1_tarski(k3_xboole_0(k1_relat_1(sK0),X16),X17) | k7_relat_1(sK0,X16) = k7_relat_1(sK0,k3_xboole_0(X16,X17))) )),
% 1.61/0.59    inference(forward_demodulation,[],[f125,f50])).
% 1.61/0.59  fof(f50,plain,(
% 1.61/0.59    ( ! [X0,X1] : (k7_relat_1(k7_relat_1(sK0,X0),X1) = k7_relat_1(sK0,k3_xboole_0(X0,X1))) )),
% 1.61/0.59    inference(unit_resulting_resolution,[],[f25,f26])).
% 1.61/0.59  fof(f26,plain,(
% 1.61/0.59    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))) )),
% 1.61/0.59    inference(cnf_transformation,[],[f16])).
% 1.61/0.59  fof(f16,plain,(
% 1.61/0.59    ! [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 1.61/0.59    inference(ennf_transformation,[],[f9])).
% 1.61/0.59  fof(f9,axiom,(
% 1.61/0.59    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)))),
% 1.61/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).
% 1.61/0.59  fof(f125,plain,(
% 1.61/0.59    ( ! [X17,X16] : (~r1_tarski(k3_xboole_0(k1_relat_1(sK0),X16),X17) | k7_relat_1(sK0,X16) = k7_relat_1(k7_relat_1(sK0,X16),X17)) )),
% 1.61/0.59    inference(forward_demodulation,[],[f104,f51])).
% 1.61/0.59  fof(f104,plain,(
% 1.61/0.59    ( ! [X17,X16] : (~r1_tarski(k1_relat_1(k7_relat_1(sK0,X16)),X17) | k7_relat_1(sK0,X16) = k7_relat_1(k7_relat_1(sK0,X16),X17)) )),
% 1.61/0.59    inference(resolution,[],[f52,f32])).
% 1.61/0.59  fof(f32,plain,(
% 1.61/0.59    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k1_relat_1(X1),X0) | k7_relat_1(X1,X0) = X1) )),
% 1.61/0.59    inference(cnf_transformation,[],[f21])).
% 1.61/0.59  fof(f21,plain,(
% 1.61/0.59    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.61/0.59    inference(flattening,[],[f20])).
% 1.61/0.59  fof(f20,plain,(
% 1.61/0.59    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.61/0.59    inference(ennf_transformation,[],[f12])).
% 1.61/0.59  fof(f12,axiom,(
% 1.61/0.59    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 1.61/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).
% 1.61/0.59  fof(f52,plain,(
% 1.61/0.59    ( ! [X0] : (v1_relat_1(k7_relat_1(sK0,X0))) )),
% 1.61/0.59    inference(unit_resulting_resolution,[],[f25,f28])).
% 1.61/0.59  fof(f28,plain,(
% 1.61/0.59    ( ! [X0,X1] : (~v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1))) )),
% 1.61/0.59    inference(cnf_transformation,[],[f18])).
% 1.61/0.59  fof(f18,plain,(
% 1.61/0.59    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 1.61/0.59    inference(ennf_transformation,[],[f8])).
% 1.61/0.59  fof(f8,axiom,(
% 1.61/0.59    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 1.61/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 1.61/0.59  fof(f46,plain,(
% 1.61/0.59    k7_relat_1(sK0,k1_relat_1(sK1)) != k7_relat_1(sK0,k3_xboole_0(k1_relat_1(sK1),k1_relat_1(sK0)))),
% 1.61/0.59    inference(backward_demodulation,[],[f24,f37])).
% 1.61/0.59  fof(f37,plain,(
% 1.61/0.59    ( ! [X0] : (k1_relat_1(k7_relat_1(sK1,X0)) = k3_xboole_0(k1_relat_1(sK1),X0)) )),
% 1.61/0.59    inference(unit_resulting_resolution,[],[f23,f27])).
% 1.61/0.59  fof(f23,plain,(
% 1.61/0.59    v1_relat_1(sK1)),
% 1.61/0.59    inference(cnf_transformation,[],[f15])).
% 1.61/0.59  fof(f24,plain,(
% 1.61/0.59    k7_relat_1(sK0,k1_relat_1(sK1)) != k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0))))),
% 1.61/0.59    inference(cnf_transformation,[],[f15])).
% 1.61/0.59  % SZS output end Proof for theBenchmark
% 1.61/0.59  % (7754)------------------------------
% 1.61/0.59  % (7754)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.61/0.59  % (7754)Termination reason: Refutation
% 1.61/0.59  
% 1.61/0.59  % (7754)Memory used [KB]: 6524
% 1.61/0.59  % (7754)Time elapsed: 0.146 s
% 1.61/0.59  % (7754)------------------------------
% 1.61/0.59  % (7754)------------------------------
% 1.61/0.59  % (7749)Success in time 0.225 s
%------------------------------------------------------------------------------
