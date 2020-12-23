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
% DateTime   : Thu Dec  3 12:47:11 EST 2020

% Result     : Theorem 44.57s
% Output     : Refutation 44.57s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 200 expanded)
%              Number of leaves         :    9 (  44 expanded)
%              Depth                    :   13
%              Number of atoms          :  132 ( 520 expanded)
%              Number of equality atoms :   13 (  44 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f91963,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f170,f91738,f91739,f1635])).

fof(f1635,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,k1_relat_1(sK0))
      | r2_hidden(X2,X3)
      | ~ r1_tarski(k1_relat_1(sK1),X3) ) ),
    inference(resolution,[],[f702,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
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

fof(f702,plain,(
    ! [X3] :
      ( r2_hidden(X3,k1_relat_1(sK1))
      | ~ r2_hidden(X3,k1_relat_1(sK0)) ) ),
    inference(resolution,[],[f122,f88])).

fof(f88,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X2,sK8(X0,X2)),X0)
      | ~ r2_hidden(X2,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X2,sK8(X0,X2)),X0)
      | ~ r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(f122,plain,(
    ! [X15,X16] :
      ( ~ r2_hidden(k4_tarski(X15,X16),sK0)
      | r2_hidden(X15,k1_relat_1(sK1)) ) ),
    inference(resolution,[],[f103,f89])).

fof(f89,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),X0)
      | r2_hidden(X2,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X2,X3),X0)
      | r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f103,plain,(
    ! [X0] :
      ( r2_hidden(X0,sK1)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f34,f40])).

fof(f34,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( r1_tarski(X0,X1)
             => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_relat_1)).

fof(f91739,plain,(
    ~ r2_hidden(sK2(k1_relat_1(sK0),k3_relat_1(sK1)),k3_relat_1(sK1)) ),
    inference(resolution,[],[f91699,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f91699,plain,(
    ~ r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(resolution,[],[f91697,f1551])).

fof(f1551,plain,
    ( ~ r1_tarski(k2_relat_1(sK0),k3_relat_1(sK1))
    | ~ r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(resolution,[],[f216,f35])).

fof(f35,plain,(
    ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f24])).

fof(f216,plain,(
    ! [X1] :
      ( r1_tarski(k3_relat_1(sK0),X1)
      | ~ r1_tarski(k1_relat_1(sK0),X1)
      | ~ r1_tarski(k2_relat_1(sK0),X1) ) ),
    inference(superposition,[],[f38,f99])).

fof(f99,plain,(
    k3_relat_1(sK0) = k2_xboole_0(k1_relat_1(sK0),k2_relat_1(sK0)) ),
    inference(resolution,[],[f36,f37])).

fof(f37,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

fof(f36,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f38,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

fof(f91697,plain,(
    r1_tarski(k2_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(duplicate_literal_removal,[],[f91679])).

fof(f91679,plain,
    ( r1_tarski(k2_relat_1(sK0),k3_relat_1(sK1))
    | r1_tarski(k2_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(resolution,[],[f7887,f11238])).

fof(f11238,plain,(
    ! [X0] :
      ( r2_hidden(sK2(k4_xboole_0(X0,k1_relat_1(sK1)),k2_relat_1(sK1)),X0)
      | r1_tarski(X0,k3_relat_1(sK1)) ) ),
    inference(resolution,[],[f1120,f92])).

fof(f92,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f1120,plain,(
    ! [X0] :
      ( r2_hidden(sK2(k4_xboole_0(X0,k1_relat_1(sK1)),k2_relat_1(sK1)),k4_xboole_0(X0,k1_relat_1(sK1)))
      | r1_tarski(X0,k3_relat_1(sK1)) ) ),
    inference(resolution,[],[f172,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f172,plain,(
    ! [X0] :
      ( ~ r1_tarski(k4_xboole_0(X0,k1_relat_1(sK1)),k2_relat_1(sK1))
      | r1_tarski(X0,k3_relat_1(sK1)) ) ),
    inference(superposition,[],[f39,f98])).

fof(f98,plain,(
    k3_relat_1(sK1) = k2_xboole_0(k1_relat_1(sK1),k2_relat_1(sK1)) ),
    inference(resolution,[],[f33,f37])).

fof(f33,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k4_xboole_0(X0,X1),X2)
      | r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f7887,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK2(k4_xboole_0(X0,k1_relat_1(sK1)),k2_relat_1(sK1)),k2_relat_1(sK0))
      | r1_tarski(X0,k3_relat_1(sK1)) ) ),
    inference(resolution,[],[f1121,f760])).

fof(f760,plain,(
    ! [X1] :
      ( r2_hidden(X1,k2_relat_1(sK1))
      | ~ r2_hidden(X1,k2_relat_1(sK0)) ) ),
    inference(resolution,[],[f123,f86])).

fof(f86,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(sK5(X0,X2),X2),X0)
      | ~ r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK5(X0,X2),X2),X0)
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(f123,plain,(
    ! [X17,X18] :
      ( ~ r2_hidden(k4_tarski(X17,X18),sK0)
      | r2_hidden(X18,k2_relat_1(sK1)) ) ),
    inference(resolution,[],[f103,f87])).

fof(f87,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(k4_tarski(X3,X2),X0)
      | r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X3,X2),X0)
      | r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f1121,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK2(k4_xboole_0(X1,k1_relat_1(sK1)),k2_relat_1(sK1)),k2_relat_1(sK1))
      | r1_tarski(X1,k3_relat_1(sK1)) ) ),
    inference(resolution,[],[f172,f42])).

fof(f91738,plain,(
    r2_hidden(sK2(k1_relat_1(sK0),k3_relat_1(sK1)),k1_relat_1(sK0)) ),
    inference(resolution,[],[f91699,f41])).

fof(f170,plain,(
    r1_tarski(k1_relat_1(sK1),k3_relat_1(sK1)) ),
    inference(superposition,[],[f48,f98])).

fof(f48,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:44:01 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.48  % (13148)dis+1004_1_aac=none:acc=on:afp=40000:afq=1.2:anc=none:cond=on:fde=unused:gs=on:gsem=off:irw=on:nm=32:nwc=2:sd=1:ss=axioms:sos=theory:sp=reverse_arity:urr=ec_only_17 on theBenchmark
% 0.22/0.48  % (13148)Refutation not found, incomplete strategy% (13148)------------------------------
% 0.22/0.48  % (13148)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (13148)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (13148)Memory used [KB]: 10746
% 0.22/0.48  % (13148)Time elapsed: 0.066 s
% 0.22/0.48  % (13148)------------------------------
% 0.22/0.48  % (13148)------------------------------
% 0.22/0.48  % (13164)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_157 on theBenchmark
% 0.22/0.48  % (13156)dis+1002_5_av=off:cond=on:gs=on:lma=on:nm=2:nwc=1:sd=3:ss=axioms:st=1.5:sos=on:updr=off_4 on theBenchmark
% 0.22/0.49  % (13156)Refutation not found, incomplete strategy% (13156)------------------------------
% 0.22/0.49  % (13156)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (13156)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (13156)Memory used [KB]: 6268
% 0.22/0.49  % (13156)Time elapsed: 0.076 s
% 0.22/0.49  % (13156)------------------------------
% 0.22/0.49  % (13156)------------------------------
% 0.22/0.51  % (13157)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.52  % (13149)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_6 on theBenchmark
% 0.22/0.53  % (13165)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.54  % (13146)dis+4_8:1_add=large:afp=100000:afq=1.4:ep=RST:fde=unused:gsp=input_only:lcm=predicate:nwc=1:sos=all:sp=occurrence:updr=off:uhcvi=on_33 on theBenchmark
% 0.22/0.54  % (13144)lrs+1002_8:1_av=off:cond=on:gsp=input_only:gs=on:irw=on:lma=on:nm=0:nwc=1.7:stl=30:sd=2:ss=axioms:sos=on:sp=occurrence:urr=on_41 on theBenchmark
% 1.40/0.54  % (13147)lrs+11_4_av=off:gsp=input_only:irw=on:lma=on:nm=0:nwc=1.2:stl=30:sd=2:ss=axioms:sp=reverse_arity:urr=on:updr=off_8 on theBenchmark
% 1.40/0.55  % (13168)dis+11_2_add=large:afr=on:anc=none:gs=on:gsem=on:lwlo=on:nm=16:nwc=1:sd=1:ss=axioms:st=3.0:sos=on_4 on theBenchmark
% 1.40/0.55  % (13167)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_88 on theBenchmark
% 1.40/0.55  % (13169)ott+11_8:1_av=off:bs=on:bce=on:fde=none:gsp=input_only:gs=on:gsem=on:irw=on:lcm=predicate:nm=6:nwc=1.5:sd=2:ss=axioms:st=1.2:sos=theory:urr=on:updr=off_49 on theBenchmark
% 1.40/0.55  % (13163)ott+11_4:1_awrs=converge:awrsf=16:acc=model:add=large:afr=on:afp=4000:afq=1.4:amm=off:br=off:cond=fast:fde=none:gsp=input_only:nm=64:nwc=2:nicw=on:sd=3:ss=axioms:s2a=on:sac=on:sp=frequency:urr=on:updr=off_70 on theBenchmark
% 1.40/0.55  % (13143)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_21 on theBenchmark
% 1.40/0.55  % (13145)lrs+2_5:4_av=off:bce=on:cond=fast:ep=R:fde=none:gs=on:lcm=reverse:lwlo=on:nwc=1:stl=30:sd=1:ss=axioms:sos=all:sp=occurrence_8 on theBenchmark
% 1.40/0.55  % (13145)Refutation not found, incomplete strategy% (13145)------------------------------
% 1.40/0.55  % (13145)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.55  % (13145)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.55  
% 1.40/0.55  % (13145)Memory used [KB]: 6140
% 1.40/0.55  % (13145)Time elapsed: 0.001 s
% 1.40/0.55  % (13145)------------------------------
% 1.40/0.55  % (13145)------------------------------
% 1.40/0.56  % (13150)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_11 on theBenchmark
% 1.40/0.56  % (13150)Refutation not found, incomplete strategy% (13150)------------------------------
% 1.40/0.56  % (13150)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.56  % (13162)lrs+1010_4:1_aac=none:add=off:afp=40000:afq=2.0:amm=sco:anc=none:gs=on:gsem=off:lma=on:lwlo=on:nm=4:nwc=10:stl=30:sd=3:ss=axioms:sos=all:sac=on_49 on theBenchmark
% 1.40/0.56  % (13160)lrs+1_2:3_aac=none:afr=on:afp=100000:afq=1.0:amm=sco:bd=off:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off:uhcvi=on_11 on theBenchmark
% 1.40/0.56  % (13153)dis+1010_2:3_afr=on:afp=40000:afq=1.4:amm=off:anc=none:lma=on:nm=16:nwc=1:sp=occurrence:updr=off:uhcvi=on_34 on theBenchmark
% 1.40/0.56  % (13171)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_48 on theBenchmark
% 1.40/0.56  % (13152)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_3 on theBenchmark
% 1.40/0.56  % (13161)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_6 on theBenchmark
% 1.40/0.56  % (13142)lrs-11_3_av=off:bs=unit_only:bsr=on:cond=on:gsp=input_only:gs=on:gsem=on:lma=on:nm=2:nwc=1:stl=30:sd=3:ss=axioms:st=1.2:sos=all:sp=reverse_arity:urr=on:updr=off_11 on theBenchmark
% 1.40/0.56  % (13151)ott+11_2:1_add=large:afp=40000:afq=2.0:amm=sco:anc=none:br=off:cond=on:irw=on:nwc=1:sd=2:ss=axioms:st=2.0:sos=all:urr=on:updr=off_6 on theBenchmark
% 1.54/0.56  % (13150)Termination reason: Refutation not found, incomplete strategy
% 1.54/0.56  
% 1.54/0.56  % (13150)Memory used [KB]: 6140
% 1.54/0.56  % (13150)Time elapsed: 0.132 s
% 1.54/0.56  % (13150)------------------------------
% 1.54/0.56  % (13150)------------------------------
% 1.54/0.57  % (13155)dis+4_2_av=off:bs=on:fsr=off:gsp=input_only:newcnf=on:nwc=1:sd=3:ss=axioms:st=3.0:sos=all:sp=reverse_arity:urr=ec_only:updr=off_127 on theBenchmark
% 1.54/0.57  % (13161)Refutation not found, incomplete strategy% (13161)------------------------------
% 1.54/0.57  % (13161)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.57  % (13159)lrs-2_3:2_av=off:bce=on:cond=on:gsp=input_only:gs=on:gsem=on:lcm=predicate:lma=on:newcnf=on:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:updr=off:uhcvi=on_62 on theBenchmark
% 1.54/0.57  % (13166)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.54/0.57  % (13161)Termination reason: Refutation not found, incomplete strategy
% 1.54/0.57  
% 1.54/0.57  % (13161)Memory used [KB]: 1791
% 1.54/0.57  % (13161)Time elapsed: 0.146 s
% 1.54/0.57  % (13161)------------------------------
% 1.54/0.57  % (13161)------------------------------
% 1.54/0.57  % (13166)Refutation not found, incomplete strategy% (13166)------------------------------
% 1.54/0.57  % (13166)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.57  % (13166)Termination reason: Refutation not found, incomplete strategy
% 1.54/0.57  
% 1.54/0.57  % (13166)Memory used [KB]: 10746
% 1.54/0.57  % (13166)Time elapsed: 0.156 s
% 1.54/0.57  % (13166)------------------------------
% 1.54/0.57  % (13166)------------------------------
% 1.54/0.57  % (13170)lrs+1011_10_av=off:bce=on:cond=on:fsr=off:fde=unused:gs=on:nm=2:nwc=1.1:stl=30:sd=4:ss=axioms:s2a=on:st=1.5:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_4 on theBenchmark
% 1.54/0.57  % (13159)Refutation not found, incomplete strategy% (13159)------------------------------
% 1.54/0.57  % (13159)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.57  % (13159)Termination reason: Refutation not found, incomplete strategy
% 1.54/0.57  
% 1.54/0.57  % (13159)Memory used [KB]: 6396
% 1.54/0.57  % (13159)Time elapsed: 0.157 s
% 1.54/0.57  % (13159)------------------------------
% 1.54/0.57  % (13159)------------------------------
% 1.54/0.58  % (13158)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_23 on theBenchmark
% 1.54/0.58  % (13154)dis+10_5:4_add=off:afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sd=3:ss=axioms:st=3.0:sos=all:sp=occurrence:urr=on:updr=off_15 on theBenchmark
% 1.54/0.58  % (13204)dis+1011_8:1_aac=none:acc=on:afp=1000:afq=1.4:amm=off:anc=all:bs=unit_only:bce=on:ccuc=small_ones:fsr=off:fde=unused:gsp=input_only:gs=on:gsem=off:lma=on:nm=16:nwc=2.5:sd=4:ss=axioms:st=1.5:sos=all:uhcvi=on_65 on theBenchmark
% 1.54/0.58  % (13168)Refutation not found, incomplete strategy% (13168)------------------------------
% 1.54/0.58  % (13168)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.58  % (13168)Termination reason: Refutation not found, incomplete strategy
% 1.54/0.58  
% 1.54/0.58  % (13168)Memory used [KB]: 10746
% 1.54/0.58  % (13168)Time elapsed: 0.167 s
% 1.54/0.58  % (13168)------------------------------
% 1.54/0.58  % (13168)------------------------------
% 1.54/0.61  % (13211)ott+1_5:1_acc=on:add=off:afr=on:afp=100000:afq=1.1:amm=sco:anc=none:lcm=predicate:nm=16:nwc=1.1:sd=1:ss=axioms:st=3.0:sos=on:sac=on:updr=off_18 on theBenchmark
% 2.19/0.66  % (13149)Refutation not found, incomplete strategy% (13149)------------------------------
% 2.19/0.66  % (13149)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.19/0.67  % (13235)lrs+1002_1_add=large:afp=100000:afq=1.0:amm=off:anc=none:cond=fast:fde=none:gs=on:gsem=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence_8 on theBenchmark
% 2.19/0.68  % (13149)Termination reason: Refutation not found, incomplete strategy
% 2.19/0.68  
% 2.19/0.68  % (13149)Memory used [KB]: 6268
% 2.19/0.68  % (13149)Time elapsed: 0.216 s
% 2.19/0.68  % (13149)------------------------------
% 2.19/0.68  % (13149)------------------------------
% 2.19/0.68  % (13235)Refutation not found, incomplete strategy% (13235)------------------------------
% 2.19/0.68  % (13235)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.19/0.69  % (13235)Termination reason: Refutation not found, incomplete strategy
% 2.19/0.69  
% 2.19/0.69  % (13235)Memory used [KB]: 10618
% 2.19/0.69  % (13235)Time elapsed: 0.090 s
% 2.19/0.69  % (13235)------------------------------
% 2.19/0.69  % (13235)------------------------------
% 2.19/0.71  % (13253)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_243 on theBenchmark
% 2.19/0.71  % (13242)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_4 on theBenchmark
% 2.19/0.71  % (13248)lrs+1002_3:1_av=off:bd=off:cond=fast:fde=none:gsp=input_only:lcm=predicate:lma=on:lwlo=on:nm=4:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_134 on theBenchmark
% 2.19/0.72  % (13261)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_254 on theBenchmark
% 2.19/0.73  % (13251)dis+10_5_av=off:bce=on:cond=on:gsp=input_only:gs=on:lcm=predicate:lma=on:nm=6:nwc=1:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_6 on theBenchmark
% 2.19/0.73  % (13251)Refutation not found, incomplete strategy% (13251)------------------------------
% 2.19/0.73  % (13251)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.19/0.73  % (13251)Termination reason: Refutation not found, incomplete strategy
% 2.19/0.73  
% 2.19/0.73  % (13251)Memory used [KB]: 6268
% 2.19/0.73  % (13251)Time elapsed: 0.124 s
% 2.19/0.73  % (13251)------------------------------
% 2.19/0.73  % (13251)------------------------------
% 2.93/0.80  % (13324)ins+11_64_av=off:cond=fast:fde=none:gs=on:gsem=on:igbrr=0.7:igrr=1/2:igrp=4000:igrpq=1.2:igwr=on:lcm=predicate:lma=on:nwc=1.1:sd=2:ss=axioms:st=3.0:sos=on:sp=occurrence_38 on theBenchmark
% 2.93/0.82  % (13321)ins+10_1_av=off:fde=none:gsp=input_only:irw=on:igbrr=0.7:igpr=on:igrr=16/1:igrp=400:igrpq=2.0:igs=1003:igwr=on:lcm=predicate:lma=on:nm=64:newcnf=on:nwc=3:sp=occurrence:uhcvi=on_62 on theBenchmark
% 3.52/0.87  % (13339)lrs+10_2:3_afp=1000:afq=1.1:amm=sco:anc=none:er=known:lcm=reverse:lwlo=on:nm=64:newcnf=on:nwc=2:stl=30:sd=5:ss=axioms:sos=theory:sac=on:sp=occurrence_78 on theBenchmark
% 4.06/1.03  % (13152)Time limit reached!
% 4.06/1.03  % (13152)------------------------------
% 4.06/1.03  % (13152)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.51/1.05  % (13152)Termination reason: Time limit
% 4.51/1.05  % (13152)Termination phase: Saturation
% 4.51/1.05  
% 4.51/1.05  % (13152)Memory used [KB]: 11513
% 4.51/1.05  % (13152)Time elapsed: 0.600 s
% 4.51/1.05  % (13152)------------------------------
% 4.51/1.05  % (13152)------------------------------
% 6.29/1.19  % (13413)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_27 on theBenchmark
% 6.74/1.25  % (13170)Time limit reached!
% 6.74/1.25  % (13170)------------------------------
% 6.74/1.25  % (13170)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.74/1.25  % (13170)Termination reason: Time limit
% 6.74/1.25  
% 6.74/1.25  % (13170)Memory used [KB]: 13176
% 6.74/1.25  % (13170)Time elapsed: 0.818 s
% 6.74/1.25  % (13170)------------------------------
% 6.74/1.25  % (13170)------------------------------
% 7.81/1.39  % (13414)lrs-2_3:1_add=off:afr=on:afp=1000:afq=1.2:amm=sco:anc=all_dependent:bd=off:bs=unit_only:bsr=on:cond=on:fde=unused:gs=on:gsem=on:irw=on:lcm=reverse:nm=32:nwc=1.7:sas=z3:stl=30:sos=all:sac=on_28 on theBenchmark
% 7.81/1.42  % (13242)Time limit reached!
% 7.81/1.42  % (13242)------------------------------
% 7.81/1.42  % (13242)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.81/1.43  % (13242)Termination reason: Time limit
% 7.81/1.43  
% 7.81/1.43  % (13242)Memory used [KB]: 20340
% 7.81/1.43  % (13242)Time elapsed: 0.822 s
% 7.81/1.43  % (13242)------------------------------
% 7.81/1.43  % (13242)------------------------------
% 8.40/1.44  % (13151)Time limit reached!
% 8.40/1.44  % (13151)------------------------------
% 8.40/1.44  % (13151)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.40/1.44  % (13151)Termination reason: Time limit
% 8.40/1.44  % (13151)Termination phase: Saturation
% 8.40/1.44  
% 8.40/1.44  % (13151)Memory used [KB]: 14711
% 8.40/1.44  % (13151)Time elapsed: 1.027 s
% 8.40/1.44  % (13151)------------------------------
% 8.40/1.44  % (13151)------------------------------
% 9.23/1.57  % (13416)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_4 on theBenchmark
% 9.23/1.57  % (13415)lrs+1002_2:1_acc=on:add=large:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:bd=off:ccuc=first:fsr=off:gs=on:irw=on:nm=32:newcnf=on:nwc=1:stl=30:sd=2:ss=axioms:sos=on:sp=reverse_arity_3 on theBenchmark
% 9.23/1.57  % (13415)Refutation not found, incomplete strategy% (13415)------------------------------
% 9.23/1.57  % (13415)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.23/1.57  % (13415)Termination reason: Refutation not found, incomplete strategy
% 9.23/1.57  
% 9.23/1.57  % (13415)Memory used [KB]: 10618
% 9.23/1.57  % (13415)Time elapsed: 0.116 s
% 9.23/1.57  % (13415)------------------------------
% 9.23/1.57  % (13415)------------------------------
% 9.23/1.58  % (13157)Time limit reached!
% 9.23/1.58  % (13157)------------------------------
% 9.23/1.58  % (13157)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.23/1.58  % (13157)Termination reason: Time limit
% 9.23/1.58  
% 9.23/1.58  % (13157)Memory used [KB]: 11641
% 9.23/1.58  % (13157)Time elapsed: 1.111 s
% 9.23/1.58  % (13157)------------------------------
% 9.23/1.58  % (13157)------------------------------
% 10.00/1.64  % (13147)Time limit reached!
% 10.00/1.64  % (13147)------------------------------
% 10.00/1.64  % (13147)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.00/1.64  % (13147)Termination reason: Time limit
% 10.00/1.64  % (13147)Termination phase: Saturation
% 10.00/1.64  
% 10.00/1.64  % (13147)Memory used [KB]: 12281
% 10.00/1.64  % (13147)Time elapsed: 1.200 s
% 10.00/1.64  % (13147)------------------------------
% 10.00/1.64  % (13147)------------------------------
% 10.35/1.71  % (13417)ott-11_3_av=off:bsr=on:cond=fast:fde=unused:lcm=predicate:lma=on:nm=6:nwc=1:sos=on:updr=off_546 on theBenchmark
% 10.35/1.72  % (13418)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_138 on theBenchmark
% 11.09/1.78  % (13419)lrs+11_8:1_av=off:bd=preordered:br=off:cond=on:gs=on:gsem=on:lcm=reverse:lma=on:nm=0:nwc=1:stl=60:urr=on_362 on theBenchmark
% 11.09/1.79  % (13165)Time limit reached!
% 11.09/1.79  % (13165)------------------------------
% 11.09/1.79  % (13165)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.09/1.79  % (13165)Termination reason: Time limit
% 11.09/1.79  
% 11.09/1.79  % (13165)Memory used [KB]: 17014
% 11.09/1.79  % (13165)Time elapsed: 1.313 s
% 11.09/1.79  % (13165)------------------------------
% 11.09/1.79  % (13165)------------------------------
% 11.66/1.92  % (13420)ott+1004_12_awrs=converge:awrsf=64:aac=none:afr=on:afp=4000:afq=1.4:amm=sco:anc=none:bs=on:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=on:lma=on:nwc=5:nicw=on:sas=z3:sos=all:sac=on:sp=occurrence:urr=ec_only_113 on theBenchmark
% 12.60/2.05  % (13160)Time limit reached!
% 12.60/2.05  % (13160)------------------------------
% 12.60/2.05  % (13160)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.60/2.05  % (13160)Termination reason: Time limit
% 12.60/2.05  
% 12.60/2.05  % (13160)Memory used [KB]: 29423
% 12.60/2.05  % (13160)Time elapsed: 1.630 s
% 12.60/2.05  % (13160)------------------------------
% 12.60/2.05  % (13160)------------------------------
% 13.18/2.06  % (13142)Time limit reached!
% 13.18/2.06  % (13142)------------------------------
% 13.18/2.06  % (13142)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 13.18/2.06  % (13142)Termination reason: Time limit
% 13.18/2.06  
% 13.18/2.06  % (13142)Memory used [KB]: 21236
% 13.18/2.06  % (13142)Time elapsed: 1.614 s
% 13.18/2.06  % (13142)------------------------------
% 13.18/2.06  % (13142)------------------------------
% 14.18/2.20  % (13422)dis+1010_128_afr=on:afp=10000:afq=1.1:anc=none:bsr=on:br=off:bce=on:cond=on:fsr=off:gsp=input_only:irw=on:nm=6:newcnf=on:nwc=1.5:sos=all:sac=on:sp=occurrence:urr=on:updr=off_107 on theBenchmark
% 14.18/2.21  % (13421)lrs+1010_2:3_afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:gs=on:gsem=off:nm=16:nwc=1:nicw=on:sas=z3:stl=30:sd=2:ss=axioms:st=1.5:updr=off_41 on theBenchmark
% 14.77/2.27  % (13416)Time limit reached!
% 14.77/2.27  % (13416)------------------------------
% 14.77/2.27  % (13416)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.77/2.27  % (13416)Termination reason: Time limit
% 14.77/2.27  
% 14.77/2.27  % (13416)Memory used [KB]: 15223
% 14.77/2.27  % (13416)Time elapsed: 0.808 s
% 14.77/2.27  % (13416)------------------------------
% 14.77/2.27  % (13416)------------------------------
% 16.15/2.41  % (13423)lrs+1002_8:1_add=large:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:bd=off:bsr=on:er=known:lwlo=on:nm=0:nwc=1.2:stl=30:sd=1:ss=axioms:sp=occurrence:updr=off_51 on theBenchmark
% 16.15/2.43  % (13423)Refutation not found, incomplete strategy% (13423)------------------------------
% 16.15/2.43  % (13423)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 16.15/2.43  % (13423)Termination reason: Refutation not found, incomplete strategy
% 16.15/2.43  
% 16.15/2.43  % (13423)Memory used [KB]: 6140
% 16.15/2.43  % (13423)Time elapsed: 0.140 s
% 16.15/2.43  % (13423)------------------------------
% 16.15/2.43  % (13423)------------------------------
% 17.12/2.55  % (13154)Time limit reached!
% 17.12/2.55  % (13154)------------------------------
% 17.12/2.55  % (13154)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 17.12/2.55  % (13154)Termination reason: Time limit
% 17.12/2.55  
% 17.12/2.55  % (13154)Memory used [KB]: 10490
% 17.12/2.55  % (13154)Time elapsed: 2.125 s
% 17.12/2.55  % (13154)------------------------------
% 17.12/2.55  % (13154)------------------------------
% 21.26/3.08  % (13211)Time limit reached!
% 21.26/3.08  % (13211)------------------------------
% 21.26/3.08  % (13211)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 21.26/3.08  % (13211)Termination reason: Time limit
% 21.26/3.08  % (13211)Termination phase: Saturation
% 21.26/3.08  
% 21.26/3.08  % (13211)Memory used [KB]: 37483
% 21.26/3.08  % (13211)Time elapsed: 2.500 s
% 21.26/3.08  % (13211)------------------------------
% 21.26/3.08  % (13211)------------------------------
% 23.76/3.39  % (13143)Time limit reached!
% 23.76/3.39  % (13143)------------------------------
% 23.76/3.39  % (13143)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 23.76/3.39  % (13143)Termination reason: Time limit
% 23.76/3.39  
% 23.76/3.39  % (13143)Memory used [KB]: 36076
% 23.76/3.39  % (13143)Time elapsed: 2.936 s
% 23.76/3.39  % (13143)------------------------------
% 23.76/3.39  % (13143)------------------------------
% 25.12/3.55  % (13158)Time limit reached!
% 25.12/3.55  % (13158)------------------------------
% 25.12/3.55  % (13158)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 25.12/3.55  % (13158)Termination reason: Time limit
% 25.12/3.55  % (13158)Termination phase: Saturation
% 25.12/3.55  
% 25.12/3.55  % (13158)Memory used [KB]: 13816
% 25.12/3.55  % (13158)Time elapsed: 3.100 s
% 25.12/3.55  % (13158)------------------------------
% 25.12/3.55  % (13158)------------------------------
% 35.05/4.82  % (13413)Time limit reached!
% 35.05/4.82  % (13413)------------------------------
% 35.05/4.82  % (13413)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 35.49/4.83  % (13413)Termination reason: Time limit
% 35.49/4.83  
% 35.49/4.83  % (13413)Memory used [KB]: 28656
% 35.49/4.83  % (13413)Time elapsed: 3.722 s
% 35.49/4.83  % (13413)------------------------------
% 35.49/4.83  % (13413)------------------------------
% 35.49/4.84  % (13146)Time limit reached!
% 35.49/4.84  % (13146)------------------------------
% 35.49/4.84  % (13146)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 35.49/4.84  % (13146)Termination reason: Time limit
% 35.49/4.84  % (13146)Termination phase: Saturation
% 35.49/4.84  
% 35.49/4.84  % (13146)Memory used [KB]: 41577
% 35.49/4.84  % (13146)Time elapsed: 4.400 s
% 35.49/4.84  % (13146)------------------------------
% 35.49/4.84  % (13146)------------------------------
% 36.64/5.01  % (13153)Time limit reached!
% 36.64/5.01  % (13153)------------------------------
% 36.64/5.01  % (13153)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 36.64/5.03  % (13153)Termination reason: Time limit
% 36.64/5.03  % (13153)Termination phase: Saturation
% 36.64/5.03  
% 36.64/5.03  % (13153)Memory used [KB]: 31214
% 36.64/5.03  % (13153)Time elapsed: 4.600 s
% 36.64/5.03  % (13153)------------------------------
% 36.64/5.03  % (13153)------------------------------
% 37.44/5.12  % (13414)Time limit reached!
% 37.44/5.12  % (13414)------------------------------
% 37.44/5.12  % (13414)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 37.44/5.12  % (13414)Termination reason: Time limit
% 37.44/5.12  
% 37.44/5.12  % (13414)Memory used [KB]: 18038
% 37.44/5.12  % (13414)Time elapsed: 3.841 s
% 37.44/5.12  % (13414)------------------------------
% 37.44/5.12  % (13414)------------------------------
% 44.57/5.97  % (13155)Refutation found. Thanks to Tanya!
% 44.57/5.97  % SZS status Theorem for theBenchmark
% 44.57/5.97  % SZS output start Proof for theBenchmark
% 44.57/5.97  fof(f91963,plain,(
% 44.57/5.97    $false),
% 44.57/5.97    inference(unit_resulting_resolution,[],[f170,f91738,f91739,f1635])).
% 44.57/5.97  fof(f1635,plain,(
% 44.57/5.97    ( ! [X2,X3] : (~r2_hidden(X2,k1_relat_1(sK0)) | r2_hidden(X2,X3) | ~r1_tarski(k1_relat_1(sK1),X3)) )),
% 44.57/5.97    inference(resolution,[],[f702,f40])).
% 44.57/5.97  fof(f40,plain,(
% 44.57/5.97    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 44.57/5.97    inference(cnf_transformation,[],[f29])).
% 44.57/5.97  fof(f29,plain,(
% 44.57/5.97    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 44.57/5.97    inference(ennf_transformation,[],[f1])).
% 44.57/5.97  fof(f1,axiom,(
% 44.57/5.97    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 44.57/5.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 44.57/5.97  fof(f702,plain,(
% 44.57/5.97    ( ! [X3] : (r2_hidden(X3,k1_relat_1(sK1)) | ~r2_hidden(X3,k1_relat_1(sK0))) )),
% 44.57/5.97    inference(resolution,[],[f122,f88])).
% 44.57/5.97  fof(f88,plain,(
% 44.57/5.97    ( ! [X2,X0] : (r2_hidden(k4_tarski(X2,sK8(X0,X2)),X0) | ~r2_hidden(X2,k1_relat_1(X0))) )),
% 44.57/5.97    inference(equality_resolution,[],[f56])).
% 44.57/5.97  fof(f56,plain,(
% 44.57/5.97    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X2,sK8(X0,X2)),X0) | ~r2_hidden(X2,X1) | k1_relat_1(X0) != X1) )),
% 44.57/5.97    inference(cnf_transformation,[],[f18])).
% 44.57/5.97  fof(f18,axiom,(
% 44.57/5.97    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 44.57/5.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).
% 44.57/5.97  fof(f122,plain,(
% 44.57/5.97    ( ! [X15,X16] : (~r2_hidden(k4_tarski(X15,X16),sK0) | r2_hidden(X15,k1_relat_1(sK1))) )),
% 44.57/5.97    inference(resolution,[],[f103,f89])).
% 44.57/5.97  fof(f89,plain,(
% 44.57/5.97    ( ! [X2,X0,X3] : (~r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,k1_relat_1(X0))) )),
% 44.57/5.97    inference(equality_resolution,[],[f55])).
% 44.57/5.97  fof(f55,plain,(
% 44.57/5.97    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1) | k1_relat_1(X0) != X1) )),
% 44.57/5.97    inference(cnf_transformation,[],[f18])).
% 44.57/5.97  fof(f103,plain,(
% 44.57/5.97    ( ! [X0] : (r2_hidden(X0,sK1) | ~r2_hidden(X0,sK0)) )),
% 44.57/5.97    inference(resolution,[],[f34,f40])).
% 44.57/5.97  fof(f34,plain,(
% 44.57/5.97    r1_tarski(sK0,sK1)),
% 44.57/5.97    inference(cnf_transformation,[],[f24])).
% 44.57/5.97  fof(f24,plain,(
% 44.57/5.97    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 44.57/5.97    inference(flattening,[],[f23])).
% 44.57/5.97  fof(f23,plain,(
% 44.57/5.97    ? [X0] : (? [X1] : ((~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 44.57/5.97    inference(ennf_transformation,[],[f22])).
% 44.57/5.97  fof(f22,negated_conjecture,(
% 44.57/5.97    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 44.57/5.97    inference(negated_conjecture,[],[f21])).
% 44.57/5.97  fof(f21,conjecture,(
% 44.57/5.97    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 44.57/5.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_relat_1)).
% 44.57/5.97  fof(f91739,plain,(
% 44.57/5.97    ~r2_hidden(sK2(k1_relat_1(sK0),k3_relat_1(sK1)),k3_relat_1(sK1))),
% 44.57/5.97    inference(resolution,[],[f91699,f42])).
% 44.57/5.97  fof(f42,plain,(
% 44.57/5.97    ( ! [X0,X1] : (~r2_hidden(sK2(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 44.57/5.97    inference(cnf_transformation,[],[f29])).
% 44.57/5.97  fof(f91699,plain,(
% 44.57/5.97    ~r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1))),
% 44.57/5.97    inference(resolution,[],[f91697,f1551])).
% 44.57/5.97  fof(f1551,plain,(
% 44.57/5.97    ~r1_tarski(k2_relat_1(sK0),k3_relat_1(sK1)) | ~r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1))),
% 44.57/5.97    inference(resolution,[],[f216,f35])).
% 44.57/5.97  fof(f35,plain,(
% 44.57/5.97    ~r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))),
% 44.57/5.97    inference(cnf_transformation,[],[f24])).
% 44.57/5.97  fof(f216,plain,(
% 44.57/5.97    ( ! [X1] : (r1_tarski(k3_relat_1(sK0),X1) | ~r1_tarski(k1_relat_1(sK0),X1) | ~r1_tarski(k2_relat_1(sK0),X1)) )),
% 44.57/5.97    inference(superposition,[],[f38,f99])).
% 44.57/5.97  fof(f99,plain,(
% 44.57/5.97    k3_relat_1(sK0) = k2_xboole_0(k1_relat_1(sK0),k2_relat_1(sK0))),
% 44.57/5.97    inference(resolution,[],[f36,f37])).
% 44.57/5.97  fof(f37,plain,(
% 44.57/5.97    ( ! [X0] : (~v1_relat_1(X0) | k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))) )),
% 44.57/5.97    inference(cnf_transformation,[],[f25])).
% 44.57/5.97  fof(f25,plain,(
% 44.57/5.97    ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 44.57/5.97    inference(ennf_transformation,[],[f20])).
% 44.57/5.97  fof(f20,axiom,(
% 44.57/5.97    ! [X0] : (v1_relat_1(X0) => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)))),
% 44.57/5.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).
% 44.57/5.97  fof(f36,plain,(
% 44.57/5.97    v1_relat_1(sK0)),
% 44.57/5.97    inference(cnf_transformation,[],[f24])).
% 44.57/5.97  fof(f38,plain,(
% 44.57/5.97    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X2,X1) | r1_tarski(k2_xboole_0(X0,X2),X1)) )),
% 44.57/5.97    inference(cnf_transformation,[],[f27])).
% 44.57/5.97  fof(f27,plain,(
% 44.57/5.97    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 44.57/5.97    inference(flattening,[],[f26])).
% 44.57/5.97  fof(f26,plain,(
% 44.57/5.97    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 44.57/5.97    inference(ennf_transformation,[],[f12])).
% 44.57/5.97  fof(f12,axiom,(
% 44.57/5.97    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 44.57/5.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).
% 44.57/5.97  fof(f91697,plain,(
% 44.57/5.97    r1_tarski(k2_relat_1(sK0),k3_relat_1(sK1))),
% 44.57/5.97    inference(duplicate_literal_removal,[],[f91679])).
% 44.57/5.97  fof(f91679,plain,(
% 44.57/5.97    r1_tarski(k2_relat_1(sK0),k3_relat_1(sK1)) | r1_tarski(k2_relat_1(sK0),k3_relat_1(sK1))),
% 44.57/5.97    inference(resolution,[],[f7887,f11238])).
% 44.57/5.97  fof(f11238,plain,(
% 44.57/5.97    ( ! [X0] : (r2_hidden(sK2(k4_xboole_0(X0,k1_relat_1(sK1)),k2_relat_1(sK1)),X0) | r1_tarski(X0,k3_relat_1(sK1))) )),
% 44.57/5.97    inference(resolution,[],[f1120,f92])).
% 44.57/5.97  fof(f92,plain,(
% 44.57/5.97    ( ! [X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,k4_xboole_0(X0,X1))) )),
% 44.57/5.97    inference(equality_resolution,[],[f62])).
% 44.57/5.97  fof(f62,plain,(
% 44.57/5.97    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 44.57/5.97    inference(cnf_transformation,[],[f3])).
% 44.57/5.97  fof(f3,axiom,(
% 44.57/5.97    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 44.57/5.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 44.57/5.97  fof(f1120,plain,(
% 44.57/5.97    ( ! [X0] : (r2_hidden(sK2(k4_xboole_0(X0,k1_relat_1(sK1)),k2_relat_1(sK1)),k4_xboole_0(X0,k1_relat_1(sK1))) | r1_tarski(X0,k3_relat_1(sK1))) )),
% 44.57/5.97    inference(resolution,[],[f172,f41])).
% 44.57/5.97  fof(f41,plain,(
% 44.57/5.97    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 44.57/5.97    inference(cnf_transformation,[],[f29])).
% 44.57/5.97  fof(f172,plain,(
% 44.57/5.97    ( ! [X0] : (~r1_tarski(k4_xboole_0(X0,k1_relat_1(sK1)),k2_relat_1(sK1)) | r1_tarski(X0,k3_relat_1(sK1))) )),
% 44.57/5.97    inference(superposition,[],[f39,f98])).
% 44.57/5.97  fof(f98,plain,(
% 44.57/5.97    k3_relat_1(sK1) = k2_xboole_0(k1_relat_1(sK1),k2_relat_1(sK1))),
% 44.57/5.97    inference(resolution,[],[f33,f37])).
% 44.57/5.97  fof(f33,plain,(
% 44.57/5.97    v1_relat_1(sK1)),
% 44.57/5.97    inference(cnf_transformation,[],[f24])).
% 44.57/5.97  fof(f39,plain,(
% 44.57/5.97    ( ! [X2,X0,X1] : (~r1_tarski(k4_xboole_0(X0,X1),X2) | r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 44.57/5.97    inference(cnf_transformation,[],[f28])).
% 44.57/5.97  fof(f28,plain,(
% 44.57/5.97    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 44.57/5.97    inference(ennf_transformation,[],[f10])).
% 44.57/5.97  fof(f10,axiom,(
% 44.57/5.97    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 44.57/5.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).
% 44.57/5.97  fof(f7887,plain,(
% 44.57/5.97    ( ! [X0] : (~r2_hidden(sK2(k4_xboole_0(X0,k1_relat_1(sK1)),k2_relat_1(sK1)),k2_relat_1(sK0)) | r1_tarski(X0,k3_relat_1(sK1))) )),
% 44.57/5.97    inference(resolution,[],[f1121,f760])).
% 44.57/5.97  fof(f760,plain,(
% 44.57/5.97    ( ! [X1] : (r2_hidden(X1,k2_relat_1(sK1)) | ~r2_hidden(X1,k2_relat_1(sK0))) )),
% 44.57/5.97    inference(resolution,[],[f123,f86])).
% 44.57/5.97  fof(f86,plain,(
% 44.57/5.97    ( ! [X2,X0] : (r2_hidden(k4_tarski(sK5(X0,X2),X2),X0) | ~r2_hidden(X2,k2_relat_1(X0))) )),
% 44.57/5.97    inference(equality_resolution,[],[f52])).
% 44.57/5.97  fof(f52,plain,(
% 44.57/5.97    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK5(X0,X2),X2),X0) | ~r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 44.57/5.97    inference(cnf_transformation,[],[f19])).
% 44.57/5.97  fof(f19,axiom,(
% 44.57/5.97    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 44.57/5.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).
% 44.57/5.97  fof(f123,plain,(
% 44.57/5.97    ( ! [X17,X18] : (~r2_hidden(k4_tarski(X17,X18),sK0) | r2_hidden(X18,k2_relat_1(sK1))) )),
% 44.57/5.97    inference(resolution,[],[f103,f87])).
% 44.57/5.97  fof(f87,plain,(
% 44.57/5.97    ( ! [X2,X0,X3] : (~r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,k2_relat_1(X0))) )),
% 44.57/5.97    inference(equality_resolution,[],[f51])).
% 44.57/5.97  fof(f51,plain,(
% 44.57/5.97    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 44.57/5.97    inference(cnf_transformation,[],[f19])).
% 44.57/5.97  fof(f1121,plain,(
% 44.57/5.97    ( ! [X1] : (~r2_hidden(sK2(k4_xboole_0(X1,k1_relat_1(sK1)),k2_relat_1(sK1)),k2_relat_1(sK1)) | r1_tarski(X1,k3_relat_1(sK1))) )),
% 44.57/5.97    inference(resolution,[],[f172,f42])).
% 44.57/5.97  fof(f91738,plain,(
% 44.57/5.97    r2_hidden(sK2(k1_relat_1(sK0),k3_relat_1(sK1)),k1_relat_1(sK0))),
% 44.57/5.97    inference(resolution,[],[f91699,f41])).
% 44.57/5.97  fof(f170,plain,(
% 44.57/5.97    r1_tarski(k1_relat_1(sK1),k3_relat_1(sK1))),
% 44.57/5.97    inference(superposition,[],[f48,f98])).
% 44.57/5.97  fof(f48,plain,(
% 44.57/5.97    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 44.57/5.97    inference(cnf_transformation,[],[f11])).
% 44.57/5.97  fof(f11,axiom,(
% 44.57/5.97    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 44.57/5.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 44.57/5.97  % SZS output end Proof for theBenchmark
% 44.57/5.97  % (13155)------------------------------
% 44.57/5.97  % (13155)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 44.57/5.97  % (13155)Termination reason: Refutation
% 44.57/5.97  
% 44.57/5.97  % (13155)Memory used [KB]: 49125
% 44.57/5.97  % (13155)Time elapsed: 5.545 s
% 44.57/5.97  % (13155)------------------------------
% 44.57/5.97  % (13155)------------------------------
% 44.57/5.98  % (13141)Success in time 5.615 s
%------------------------------------------------------------------------------
