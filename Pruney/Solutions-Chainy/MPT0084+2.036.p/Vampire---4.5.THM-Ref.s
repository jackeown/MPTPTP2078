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
% DateTime   : Thu Dec  3 12:31:19 EST 2020

% Result     : Theorem 2.26s
% Output     : Refutation 2.26s
% Verified   : 
% Statistics : Number of formulae       :   61 (  79 expanded)
%              Number of leaves         :   14 (  21 expanded)
%              Depth                    :   10
%              Number of atoms          :  127 ( 190 expanded)
%              Number of equality atoms :   18 (  26 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6292,plain,(
    $false ),
    inference(subsumption_resolution,[],[f6272,f3911])).

fof(f3911,plain,(
    ~ r1_tarski(k3_xboole_0(k3_xboole_0(sK1,sK0),sK0),k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f78,f1308,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_xboole_0(X1,X2)
      | r2_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( r2_xboole_0(X0,X2)
      | ~ r2_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( r2_xboole_0(X0,X2)
      | ~ r2_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( r2_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r2_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_xboole_1)).

fof(f1308,plain,(
    r2_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(sK1,sK0),sK0)) ),
    inference(unit_resulting_resolution,[],[f52,f211,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f211,plain,(
    k1_xboole_0 != k3_xboole_0(k3_xboole_0(sK1,sK0),sK0) ),
    inference(unit_resulting_resolution,[],[f95,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f95,plain,(
    ~ r1_xboole_0(k3_xboole_0(sK1,sK0),sK0) ),
    inference(unit_resulting_resolution,[],[f81,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k3_xboole_0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k3_xboole_0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ~ ( r1_xboole_0(k3_xboole_0(X0,X1),X1)
        & ~ r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_xboole_1)).

fof(f81,plain,(
    ~ r1_xboole_0(sK1,sK0) ),
    inference(unit_resulting_resolution,[],[f48,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f48,plain,(
    ~ r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,
    ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    & r1_tarski(sK0,sK2)
    & ~ r1_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f39])).

fof(f39,plain,
    ( ? [X0,X1,X2] :
        ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,X2)
        & ~ r1_xboole_0(X0,X1) )
   => ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
      & r1_tarski(sK0,sK2)
      & ~ r1_xboole_0(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
      & r1_tarski(X0,X2)
      & ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
          & r1_tarski(X0,X2)
          & ~ r1_xboole_0(X0,X1) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1,X2] :
      ~ ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,X2)
        & ~ r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_xboole_1)).

fof(f52,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f78,plain,(
    ! [X1] : ~ r2_xboole_0(X1,X1) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f6272,plain,(
    r1_tarski(k3_xboole_0(k3_xboole_0(sK1,sK0),sK0),k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f853,f648])).

fof(f648,plain,(
    ! [X4] :
      ( r1_tarski(k3_xboole_0(X4,sK0),k1_xboole_0)
      | ~ r1_tarski(X4,k3_xboole_0(sK1,sK2)) ) ),
    inference(superposition,[],[f72,f203])).

fof(f203,plain,(
    k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK1,sK2),sK0) ),
    inference(unit_resulting_resolution,[],[f103,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f103,plain,(
    r1_xboole_0(k3_xboole_0(sK1,sK2),sK0) ),
    inference(unit_resulting_resolution,[],[f50,f61])).

fof(f50,plain,(
    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f40])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_xboole_1)).

fof(f853,plain,(
    ! [X0] : r1_tarski(k3_xboole_0(X0,sK0),k3_xboole_0(X0,sK2)) ),
    inference(unit_resulting_resolution,[],[f55,f814,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

fof(f814,plain,(
    ! [X0] : r1_tarski(k3_xboole_0(X0,sK0),sK2) ),
    inference(unit_resulting_resolution,[],[f156,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f156,plain,(
    ! [X1] : r1_tarski(k2_xboole_0(k3_xboole_0(X1,sK0),k3_xboole_0(X1,sK2)),sK2) ),
    inference(superposition,[],[f71,f85])).

fof(f85,plain,(
    sK2 = k2_xboole_0(sK0,sK2) ),
    inference(unit_resulting_resolution,[],[f49,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f49,plain,(
    r1_tarski(sK0,sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f71,plain,(
    ! [X2,X0,X1] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_xboole_1)).

fof(f55,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:09:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.43  % (30298)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.46  % (30291)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.47  % (30295)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.47  % (30289)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.48  % (30281)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.49  % (30288)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.49  % (30283)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.49  % (30296)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.49  % (30294)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.49  % (30285)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.50  % (30292)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.50  % (30286)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.50  % (30287)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.50  % (30300)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.50  % (30284)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.50  % (30282)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (30299)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.50  % (30282)Refutation not found, incomplete strategy% (30282)------------------------------
% 0.21/0.50  % (30282)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (30282)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (30282)Memory used [KB]: 10618
% 0.21/0.50  % (30282)Time elapsed: 0.093 s
% 0.21/0.50  % (30282)------------------------------
% 0.21/0.50  % (30282)------------------------------
% 0.21/0.50  % (30301)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.51  % (30301)Refutation not found, incomplete strategy% (30301)------------------------------
% 0.21/0.51  % (30301)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (30301)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (30301)Memory used [KB]: 10618
% 0.21/0.51  % (30301)Time elapsed: 0.098 s
% 0.21/0.51  % (30301)------------------------------
% 0.21/0.51  % (30301)------------------------------
% 0.21/0.51  % (30297)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.51  % (30293)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (30290)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 2.26/0.69  % (30296)Refutation found. Thanks to Tanya!
% 2.26/0.69  % SZS status Theorem for theBenchmark
% 2.26/0.69  % SZS output start Proof for theBenchmark
% 2.26/0.69  fof(f6292,plain,(
% 2.26/0.69    $false),
% 2.26/0.69    inference(subsumption_resolution,[],[f6272,f3911])).
% 2.26/0.69  fof(f3911,plain,(
% 2.26/0.69    ~r1_tarski(k3_xboole_0(k3_xboole_0(sK1,sK0),sK0),k1_xboole_0)),
% 2.26/0.69    inference(unit_resulting_resolution,[],[f78,f1308,f74])).
% 2.26/0.69  fof(f74,plain,(
% 2.26/0.69    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r2_xboole_0(X1,X2) | r2_xboole_0(X0,X2)) )),
% 2.26/0.69    inference(cnf_transformation,[],[f35])).
% 2.26/0.69  fof(f35,plain,(
% 2.26/0.69    ! [X0,X1,X2] : (r2_xboole_0(X0,X2) | ~r2_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 2.26/0.69    inference(flattening,[],[f34])).
% 2.26/0.69  fof(f34,plain,(
% 2.26/0.69    ! [X0,X1,X2] : (r2_xboole_0(X0,X2) | (~r2_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 2.26/0.69    inference(ennf_transformation,[],[f15])).
% 2.26/0.69  fof(f15,axiom,(
% 2.26/0.69    ! [X0,X1,X2] : ((r2_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r2_xboole_0(X0,X2))),
% 2.26/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_xboole_1)).
% 2.26/0.69  fof(f1308,plain,(
% 2.26/0.69    r2_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(sK1,sK0),sK0))),
% 2.26/0.69    inference(unit_resulting_resolution,[],[f52,f211,f66])).
% 2.26/0.69  fof(f66,plain,(
% 2.26/0.69    ( ! [X0,X1] : (~r1_tarski(X0,X1) | X0 = X1 | r2_xboole_0(X0,X1)) )),
% 2.26/0.69    inference(cnf_transformation,[],[f46])).
% 2.26/0.69  fof(f46,plain,(
% 2.26/0.69    ! [X0,X1] : ((r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 2.26/0.69    inference(flattening,[],[f45])).
% 2.26/0.69  fof(f45,plain,(
% 2.26/0.69    ! [X0,X1] : ((r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1))) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 2.26/0.69    inference(nnf_transformation,[],[f2])).
% 2.26/0.69  fof(f2,axiom,(
% 2.26/0.69    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 2.26/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).
% 2.26/0.69  fof(f211,plain,(
% 2.26/0.69    k1_xboole_0 != k3_xboole_0(k3_xboole_0(sK1,sK0),sK0)),
% 2.26/0.69    inference(unit_resulting_resolution,[],[f95,f68])).
% 2.26/0.69  fof(f68,plain,(
% 2.26/0.69    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) )),
% 2.26/0.69    inference(cnf_transformation,[],[f47])).
% 2.26/0.69  fof(f47,plain,(
% 2.26/0.69    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 2.26/0.69    inference(nnf_transformation,[],[f1])).
% 2.26/0.69  fof(f1,axiom,(
% 2.26/0.69    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 2.26/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 2.26/0.69  fof(f95,plain,(
% 2.26/0.69    ~r1_xboole_0(k3_xboole_0(sK1,sK0),sK0)),
% 2.26/0.69    inference(unit_resulting_resolution,[],[f81,f69])).
% 2.26/0.69  fof(f69,plain,(
% 2.26/0.69    ( ! [X0,X1] : (~r1_xboole_0(k3_xboole_0(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 2.26/0.69    inference(cnf_transformation,[],[f31])).
% 2.26/0.69  fof(f31,plain,(
% 2.26/0.69    ! [X0,X1] : (~r1_xboole_0(k3_xboole_0(X0,X1),X1) | r1_xboole_0(X0,X1))),
% 2.26/0.69    inference(ennf_transformation,[],[f19])).
% 2.26/0.69  fof(f19,axiom,(
% 2.26/0.69    ! [X0,X1] : ~(r1_xboole_0(k3_xboole_0(X0,X1),X1) & ~r1_xboole_0(X0,X1))),
% 2.26/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_xboole_1)).
% 2.26/0.69  fof(f81,plain,(
% 2.26/0.69    ~r1_xboole_0(sK1,sK0)),
% 2.26/0.69    inference(unit_resulting_resolution,[],[f48,f61])).
% 2.26/0.69  fof(f61,plain,(
% 2.26/0.69    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 2.26/0.69    inference(cnf_transformation,[],[f28])).
% 2.26/0.69  fof(f28,plain,(
% 2.26/0.69    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 2.26/0.69    inference(ennf_transformation,[],[f3])).
% 2.26/0.69  fof(f3,axiom,(
% 2.26/0.69    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 2.26/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 2.26/0.69  fof(f48,plain,(
% 2.26/0.69    ~r1_xboole_0(sK0,sK1)),
% 2.26/0.69    inference(cnf_transformation,[],[f40])).
% 2.26/0.69  fof(f40,plain,(
% 2.26/0.69    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) & r1_tarski(sK0,sK2) & ~r1_xboole_0(sK0,sK1)),
% 2.26/0.69    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f39])).
% 2.26/0.69  fof(f39,plain,(
% 2.26/0.69    ? [X0,X1,X2] : (r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1)) => (r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) & r1_tarski(sK0,sK2) & ~r1_xboole_0(sK0,sK1))),
% 2.26/0.69    introduced(choice_axiom,[])).
% 2.26/0.69  fof(f24,plain,(
% 2.26/0.69    ? [X0,X1,X2] : (r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 2.26/0.69    inference(ennf_transformation,[],[f21])).
% 2.26/0.69  fof(f21,negated_conjecture,(
% 2.26/0.69    ~! [X0,X1,X2] : ~(r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 2.26/0.69    inference(negated_conjecture,[],[f20])).
% 2.26/0.69  fof(f20,conjecture,(
% 2.26/0.69    ! [X0,X1,X2] : ~(r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 2.26/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_xboole_1)).
% 2.26/0.69  fof(f52,plain,(
% 2.26/0.69    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.26/0.69    inference(cnf_transformation,[],[f13])).
% 2.26/0.69  fof(f13,axiom,(
% 2.26/0.69    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.26/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 2.26/0.69  fof(f78,plain,(
% 2.26/0.69    ( ! [X1] : (~r2_xboole_0(X1,X1)) )),
% 2.26/0.69    inference(equality_resolution,[],[f65])).
% 2.26/0.69  fof(f65,plain,(
% 2.26/0.69    ( ! [X0,X1] : (X0 != X1 | ~r2_xboole_0(X0,X1)) )),
% 2.26/0.69    inference(cnf_transformation,[],[f46])).
% 2.26/0.69  fof(f6272,plain,(
% 2.26/0.69    r1_tarski(k3_xboole_0(k3_xboole_0(sK1,sK0),sK0),k1_xboole_0)),
% 2.26/0.69    inference(unit_resulting_resolution,[],[f853,f648])).
% 2.26/0.69  fof(f648,plain,(
% 2.26/0.69    ( ! [X4] : (r1_tarski(k3_xboole_0(X4,sK0),k1_xboole_0) | ~r1_tarski(X4,k3_xboole_0(sK1,sK2))) )),
% 2.26/0.69    inference(superposition,[],[f72,f203])).
% 2.26/0.69  fof(f203,plain,(
% 2.26/0.69    k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK1,sK2),sK0)),
% 2.26/0.69    inference(unit_resulting_resolution,[],[f103,f67])).
% 2.26/0.69  fof(f67,plain,(
% 2.26/0.69    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 2.26/0.69    inference(cnf_transformation,[],[f47])).
% 2.26/0.69  fof(f103,plain,(
% 2.26/0.69    r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)),
% 2.26/0.69    inference(unit_resulting_resolution,[],[f50,f61])).
% 2.26/0.69  fof(f50,plain,(
% 2.26/0.69    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))),
% 2.26/0.69    inference(cnf_transformation,[],[f40])).
% 2.26/0.69  fof(f72,plain,(
% 2.26/0.69    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X1)) )),
% 2.26/0.69    inference(cnf_transformation,[],[f32])).
% 2.26/0.69  fof(f32,plain,(
% 2.26/0.69    ! [X0,X1,X2] : (r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X1))),
% 2.26/0.69    inference(ennf_transformation,[],[f10])).
% 2.26/0.69  fof(f10,axiom,(
% 2.26/0.69    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2)))),
% 2.26/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_xboole_1)).
% 2.26/0.69  fof(f853,plain,(
% 2.26/0.69    ( ! [X0] : (r1_tarski(k3_xboole_0(X0,sK0),k3_xboole_0(X0,sK2))) )),
% 2.26/0.69    inference(unit_resulting_resolution,[],[f55,f814,f75])).
% 2.26/0.69  fof(f75,plain,(
% 2.26/0.69    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 2.26/0.69    inference(cnf_transformation,[],[f37])).
% 2.26/0.69  fof(f37,plain,(
% 2.26/0.69    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 2.26/0.69    inference(flattening,[],[f36])).
% 2.26/0.69  fof(f36,plain,(
% 2.26/0.69    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 2.26/0.69    inference(ennf_transformation,[],[f9])).
% 2.26/0.69  fof(f9,axiom,(
% 2.26/0.69    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 2.26/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).
% 2.26/0.69  fof(f814,plain,(
% 2.26/0.69    ( ! [X0] : (r1_tarski(k3_xboole_0(X0,sK0),sK2)) )),
% 2.26/0.69    inference(unit_resulting_resolution,[],[f156,f73])).
% 2.26/0.69  fof(f73,plain,(
% 2.26/0.69    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 2.26/0.69    inference(cnf_transformation,[],[f33])).
% 2.26/0.69  fof(f33,plain,(
% 2.26/0.69    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 2.26/0.69    inference(ennf_transformation,[],[f6])).
% 2.26/0.69  fof(f6,axiom,(
% 2.26/0.69    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 2.26/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).
% 2.26/0.69  fof(f156,plain,(
% 2.26/0.69    ( ! [X1] : (r1_tarski(k2_xboole_0(k3_xboole_0(X1,sK0),k3_xboole_0(X1,sK2)),sK2)) )),
% 2.26/0.69    inference(superposition,[],[f71,f85])).
% 2.26/0.69  fof(f85,plain,(
% 2.26/0.69    sK2 = k2_xboole_0(sK0,sK2)),
% 2.26/0.69    inference(unit_resulting_resolution,[],[f49,f62])).
% 2.26/0.69  fof(f62,plain,(
% 2.26/0.69    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 2.26/0.69    inference(cnf_transformation,[],[f29])).
% 2.26/0.69  fof(f29,plain,(
% 2.26/0.69    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 2.26/0.69    inference(ennf_transformation,[],[f7])).
% 2.26/0.69  fof(f7,axiom,(
% 2.26/0.69    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 2.26/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 2.26/0.69  fof(f49,plain,(
% 2.26/0.69    r1_tarski(sK0,sK2)),
% 2.26/0.69    inference(cnf_transformation,[],[f40])).
% 2.26/0.69  fof(f71,plain,(
% 2.26/0.69    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))) )),
% 2.26/0.69    inference(cnf_transformation,[],[f14])).
% 2.26/0.69  fof(f14,axiom,(
% 2.26/0.69    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))),
% 2.26/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_xboole_1)).
% 2.26/0.69  fof(f55,plain,(
% 2.26/0.69    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 2.26/0.69    inference(cnf_transformation,[],[f8])).
% 2.26/0.69  fof(f8,axiom,(
% 2.26/0.69    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 2.26/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 2.26/0.69  % SZS output end Proof for theBenchmark
% 2.26/0.69  % (30296)------------------------------
% 2.26/0.69  % (30296)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.26/0.69  % (30296)Termination reason: Refutation
% 2.26/0.69  
% 2.26/0.69  % (30296)Memory used [KB]: 10362
% 2.26/0.69  % (30296)Time elapsed: 0.254 s
% 2.26/0.69  % (30296)------------------------------
% 2.26/0.69  % (30296)------------------------------
% 2.26/0.69  % (30280)Success in time 0.329 s
%------------------------------------------------------------------------------
