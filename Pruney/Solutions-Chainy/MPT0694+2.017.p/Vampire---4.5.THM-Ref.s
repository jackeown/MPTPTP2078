%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:02 EST 2020

% Result     : Theorem 1.97s
% Output     : Refutation 1.97s
% Verified   : 
% Statistics : Number of formulae       :   41 (  77 expanded)
%              Number of leaves         :    8 (  19 expanded)
%              Depth                    :   10
%              Number of atoms          :   84 ( 170 expanded)
%              Number of equality atoms :    7 (  12 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1145,plain,(
    $false ),
    inference(resolution,[],[f1068,f145])).

fof(f145,plain,(
    ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),sK1) ),
    inference(unit_resulting_resolution,[],[f40,f135,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

fof(f135,plain,(
    ! [X0,X1] : r1_tarski(k9_relat_1(sK2,k3_xboole_0(X0,X1)),k9_relat_1(sK2,X0)) ),
    inference(unit_resulting_resolution,[],[f26,f35,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t156_relat_1)).

fof(f35,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f26,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_funct_1)).

fof(f40,plain,(
    ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(sK1,k9_relat_1(sK2,sK0))) ),
    inference(backward_demodulation,[],[f28,f37])).

fof(f37,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f28,plain,(
    ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f1068,plain,(
    ! [X0,X1] : r1_tarski(k9_relat_1(sK2,k3_xboole_0(X1,k10_relat_1(sK2,X0))),X0) ),
    inference(superposition,[],[f1023,f37])).

fof(f1023,plain,(
    ! [X2,X3] : r1_tarski(k9_relat_1(sK2,k3_xboole_0(k10_relat_1(sK2,X2),X3)),X2) ),
    inference(superposition,[],[f164,f291])).

fof(f291,plain,(
    ! [X0,X1] : k9_relat_1(sK2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(sK2,k3_xboole_0(X0,X1)),k9_relat_1(sK2,X0)) ),
    inference(unit_resulting_resolution,[],[f135,f38,f35,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k3_xboole_0(X2,X1),X0)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1)
      | k3_xboole_0(X2,X1) = X0 ) ),
    inference(resolution,[],[f29,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f38,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f164,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X1,k9_relat_1(sK2,k10_relat_1(sK2,X0))),X0) ),
    inference(superposition,[],[f129,f37])).

fof(f129,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(k9_relat_1(sK2,k10_relat_1(sK2,X0)),X1),X0) ),
    inference(unit_resulting_resolution,[],[f123,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k3_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_xboole_1)).

fof(f123,plain,(
    ! [X0] : r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X0)),X0) ),
    inference(unit_resulting_resolution,[],[f27,f26,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

fof(f27,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n015.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:38:38 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (2381)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.50  % (2373)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.51  % (2365)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.16/0.51  % (2360)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.16/0.52  % (2364)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.16/0.52  % (2370)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.27/0.53  % (2384)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.27/0.53  % (2377)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.27/0.53  % (2358)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.27/0.53  % (2368)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.27/0.53  % (2361)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.27/0.54  % (2375)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.27/0.54  % (2378)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.27/0.54  % (2372)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.27/0.54  % (2376)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.27/0.54  % (2385)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.27/0.54  % (2362)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.27/0.54  % (2385)Refutation not found, incomplete strategy% (2385)------------------------------
% 1.27/0.54  % (2385)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.54  % (2385)Termination reason: Refutation not found, incomplete strategy
% 1.27/0.54  
% 1.27/0.54  % (2385)Memory used [KB]: 6140
% 1.27/0.54  % (2385)Time elapsed: 0.132 s
% 1.27/0.54  % (2385)------------------------------
% 1.27/0.54  % (2385)------------------------------
% 1.27/0.54  % (2369)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.27/0.54  % (2382)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.27/0.54  % (2382)Refutation not found, incomplete strategy% (2382)------------------------------
% 1.27/0.54  % (2382)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.54  % (2382)Termination reason: Refutation not found, incomplete strategy
% 1.27/0.54  
% 1.27/0.54  % (2382)Memory used [KB]: 10618
% 1.27/0.54  % (2382)Time elapsed: 0.142 s
% 1.27/0.54  % (2382)------------------------------
% 1.27/0.54  % (2382)------------------------------
% 1.27/0.54  % (2386)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.27/0.55  % (2363)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.27/0.55  % (2374)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.27/0.55  % (2359)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.27/0.55  % (2374)Refutation not found, incomplete strategy% (2374)------------------------------
% 1.27/0.55  % (2374)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.55  % (2374)Termination reason: Refutation not found, incomplete strategy
% 1.27/0.55  
% 1.27/0.55  % (2374)Memory used [KB]: 10618
% 1.27/0.55  % (2374)Time elapsed: 0.141 s
% 1.27/0.55  % (2374)------------------------------
% 1.27/0.55  % (2374)------------------------------
% 1.27/0.55  % (2383)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.27/0.55  % (2387)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.27/0.55  % (2387)Refutation not found, incomplete strategy% (2387)------------------------------
% 1.27/0.55  % (2387)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.55  % (2387)Termination reason: Refutation not found, incomplete strategy
% 1.27/0.55  
% 1.27/0.55  % (2387)Memory used [KB]: 1663
% 1.27/0.55  % (2387)Time elapsed: 0.140 s
% 1.27/0.55  % (2387)------------------------------
% 1.27/0.55  % (2387)------------------------------
% 1.27/0.55  % (2366)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.27/0.55  % (2379)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.27/0.55  % (2367)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.27/0.55  % (2368)Refutation not found, incomplete strategy% (2368)------------------------------
% 1.27/0.55  % (2368)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.55  % (2368)Termination reason: Refutation not found, incomplete strategy
% 1.27/0.55  
% 1.27/0.55  % (2368)Memory used [KB]: 10746
% 1.27/0.55  % (2368)Time elapsed: 0.155 s
% 1.27/0.55  % (2368)------------------------------
% 1.27/0.55  % (2368)------------------------------
% 1.27/0.56  % (2386)Refutation not found, incomplete strategy% (2386)------------------------------
% 1.27/0.56  % (2386)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.56  % (2386)Termination reason: Refutation not found, incomplete strategy
% 1.27/0.56  
% 1.27/0.56  % (2386)Memory used [KB]: 10746
% 1.27/0.56  % (2386)Time elapsed: 0.149 s
% 1.27/0.56  % (2386)------------------------------
% 1.27/0.56  % (2386)------------------------------
% 1.27/0.57  % (2371)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.27/0.57  % (2380)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.97/0.66  % (2377)Refutation found. Thanks to Tanya!
% 1.97/0.66  % SZS status Theorem for theBenchmark
% 1.97/0.66  % SZS output start Proof for theBenchmark
% 1.97/0.66  fof(f1145,plain,(
% 1.97/0.66    $false),
% 1.97/0.66    inference(resolution,[],[f1068,f145])).
% 1.97/0.66  fof(f145,plain,(
% 1.97/0.66    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),sK1)),
% 1.97/0.66    inference(unit_resulting_resolution,[],[f40,f135,f29])).
% 1.97/0.66  fof(f29,plain,(
% 1.97/0.66    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 1.97/0.66    inference(cnf_transformation,[],[f20])).
% 1.97/0.66  fof(f20,plain,(
% 1.97/0.66    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 1.97/0.66    inference(flattening,[],[f19])).
% 1.97/0.66  fof(f19,plain,(
% 1.97/0.66    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 1.97/0.66    inference(ennf_transformation,[],[f5])).
% 1.97/0.66  fof(f5,axiom,(
% 1.97/0.66    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 1.97/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).
% 1.97/0.66  fof(f135,plain,(
% 1.97/0.66    ( ! [X0,X1] : (r1_tarski(k9_relat_1(sK2,k3_xboole_0(X0,X1)),k9_relat_1(sK2,X0))) )),
% 1.97/0.66    inference(unit_resulting_resolution,[],[f26,f35,f31])).
% 1.97/0.66  fof(f31,plain,(
% 1.97/0.66    ( ! [X2,X0,X1] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 1.97/0.66    inference(cnf_transformation,[],[f23])).
% 1.97/0.66  fof(f23,plain,(
% 1.97/0.66    ! [X0,X1,X2] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 1.97/0.66    inference(flattening,[],[f22])).
% 1.97/0.66  fof(f22,plain,(
% 1.97/0.66    ! [X0,X1,X2] : ((r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 1.97/0.66    inference(ennf_transformation,[],[f13])).
% 1.97/0.66  fof(f13,axiom,(
% 1.97/0.66    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 1.97/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t156_relat_1)).
% 1.97/0.66  fof(f35,plain,(
% 1.97/0.66    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.97/0.66    inference(cnf_transformation,[],[f4])).
% 1.97/0.66  fof(f4,axiom,(
% 1.97/0.66    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.97/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.97/0.66  fof(f26,plain,(
% 1.97/0.66    v1_relat_1(sK2)),
% 1.97/0.66    inference(cnf_transformation,[],[f18])).
% 1.97/0.66  fof(f18,plain,(
% 1.97/0.66    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 1.97/0.66    inference(flattening,[],[f17])).
% 1.97/0.66  fof(f17,plain,(
% 1.97/0.66    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 1.97/0.66    inference(ennf_transformation,[],[f16])).
% 1.97/0.66  fof(f16,negated_conjecture,(
% 1.97/0.66    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)))),
% 1.97/0.66    inference(negated_conjecture,[],[f15])).
% 1.97/0.66  fof(f15,conjecture,(
% 1.97/0.66    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)))),
% 1.97/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_funct_1)).
% 1.97/0.66  fof(f40,plain,(
% 1.97/0.66    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(sK1,k9_relat_1(sK2,sK0)))),
% 1.97/0.66    inference(backward_demodulation,[],[f28,f37])).
% 1.97/0.66  fof(f37,plain,(
% 1.97/0.66    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.97/0.66    inference(cnf_transformation,[],[f1])).
% 1.97/0.66  fof(f1,axiom,(
% 1.97/0.66    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.97/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.97/0.66  fof(f28,plain,(
% 1.97/0.66    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1))),
% 1.97/0.66    inference(cnf_transformation,[],[f18])).
% 1.97/0.66  fof(f1068,plain,(
% 1.97/0.66    ( ! [X0,X1] : (r1_tarski(k9_relat_1(sK2,k3_xboole_0(X1,k10_relat_1(sK2,X0))),X0)) )),
% 1.97/0.66    inference(superposition,[],[f1023,f37])).
% 1.97/0.66  fof(f1023,plain,(
% 1.97/0.66    ( ! [X2,X3] : (r1_tarski(k9_relat_1(sK2,k3_xboole_0(k10_relat_1(sK2,X2),X3)),X2)) )),
% 1.97/0.66    inference(superposition,[],[f164,f291])).
% 1.97/0.66  fof(f291,plain,(
% 1.97/0.66    ( ! [X0,X1] : (k9_relat_1(sK2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(sK2,k3_xboole_0(X0,X1)),k9_relat_1(sK2,X0))) )),
% 1.97/0.66    inference(unit_resulting_resolution,[],[f135,f38,f35,f78])).
% 1.97/0.66  fof(f78,plain,(
% 1.97/0.66    ( ! [X2,X0,X1] : (~r1_tarski(k3_xboole_0(X2,X1),X0) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1) | k3_xboole_0(X2,X1) = X0) )),
% 1.97/0.66    inference(resolution,[],[f29,f34])).
% 1.97/0.66  fof(f34,plain,(
% 1.97/0.66    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 1.97/0.66    inference(cnf_transformation,[],[f2])).
% 1.97/0.66  fof(f2,axiom,(
% 1.97/0.66    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.97/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.97/0.66  fof(f38,plain,(
% 1.97/0.66    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.97/0.66    inference(equality_resolution,[],[f33])).
% 1.97/0.66  fof(f33,plain,(
% 1.97/0.66    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.97/0.66    inference(cnf_transformation,[],[f2])).
% 1.97/0.66  fof(f164,plain,(
% 1.97/0.66    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X1,k9_relat_1(sK2,k10_relat_1(sK2,X0))),X0)) )),
% 1.97/0.66    inference(superposition,[],[f129,f37])).
% 1.97/0.66  fof(f129,plain,(
% 1.97/0.66    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(k9_relat_1(sK2,k10_relat_1(sK2,X0)),X1),X0)) )),
% 1.97/0.66    inference(unit_resulting_resolution,[],[f123,f30])).
% 1.97/0.66  fof(f30,plain,(
% 1.97/0.66    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1)) )),
% 1.97/0.66    inference(cnf_transformation,[],[f21])).
% 1.97/0.66  fof(f21,plain,(
% 1.97/0.66    ! [X0,X1,X2] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1))),
% 1.97/0.66    inference(ennf_transformation,[],[f3])).
% 1.97/0.66  fof(f3,axiom,(
% 1.97/0.66    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k3_xboole_0(X0,X2),X1))),
% 1.97/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_xboole_1)).
% 1.97/0.66  fof(f123,plain,(
% 1.97/0.66    ( ! [X0] : (r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X0)),X0)) )),
% 1.97/0.66    inference(unit_resulting_resolution,[],[f27,f26,f36])).
% 1.97/0.66  fof(f36,plain,(
% 1.97/0.66    ( ! [X0,X1] : (~v1_funct_1(X1) | ~v1_relat_1(X1) | r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)) )),
% 1.97/0.66    inference(cnf_transformation,[],[f25])).
% 1.97/0.66  fof(f25,plain,(
% 1.97/0.66    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.97/0.66    inference(flattening,[],[f24])).
% 1.97/0.66  fof(f24,plain,(
% 1.97/0.66    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.97/0.66    inference(ennf_transformation,[],[f14])).
% 1.97/0.66  fof(f14,axiom,(
% 1.97/0.66    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 1.97/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).
% 1.97/0.66  fof(f27,plain,(
% 1.97/0.66    v1_funct_1(sK2)),
% 1.97/0.66    inference(cnf_transformation,[],[f18])).
% 1.97/0.66  % SZS output end Proof for theBenchmark
% 1.97/0.66  % (2377)------------------------------
% 1.97/0.66  % (2377)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.97/0.66  % (2377)Termination reason: Refutation
% 1.97/0.66  
% 1.97/0.66  % (2377)Memory used [KB]: 2430
% 1.97/0.66  % (2377)Time elapsed: 0.238 s
% 1.97/0.66  % (2377)------------------------------
% 1.97/0.66  % (2377)------------------------------
% 1.97/0.66  % (2357)Success in time 0.291 s
%------------------------------------------------------------------------------
