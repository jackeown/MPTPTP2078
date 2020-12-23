%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:06 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   61 (1714 expanded)
%              Number of leaves         :    9 ( 455 expanded)
%              Depth                    :   17
%              Number of atoms          :  141 (5620 expanded)
%              Number of equality atoms :   65 (2784 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f588,plain,(
    $false ),
    inference(global_subsumption,[],[f122,f587])).

fof(f587,plain,(
    k1_xboole_0 = sK0 ),
    inference(forward_demodulation,[],[f584,f585])).

fof(f585,plain,(
    k1_xboole_0 = k1_relat_1(sK0) ),
    inference(unit_resulting_resolution,[],[f534,f553,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( sP7(sK6(X0,X1),X0)
      | r2_hidden(sK6(X0,X1),X1)
      | k1_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(f553,plain,(
    ! [X0] : ~ sP7(X0,sK0) ),
    inference(unit_resulting_resolution,[],[f532,f42])).

fof(f42,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X2,sK8(X0,X2)),X0)
      | ~ sP7(X2,X0) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f532,plain,(
    ! [X0] : ~ r2_hidden(X0,sK0) ),
    inference(backward_demodulation,[],[f276,f522])).

fof(f522,plain,(
    ! [X0] : sK4(k1_tarski(X0),sK0) = X0 ),
    inference(unit_resulting_resolution,[],[f277,f52])).

fof(f52,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_tarski(X0))
      | X0 = X2 ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f277,plain,(
    ! [X0] : r2_hidden(sK4(k1_tarski(X0),sK0),k1_tarski(X0)) ),
    inference(unit_resulting_resolution,[],[f268,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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

fof(f268,plain,(
    ! [X0] : ~ r1_tarski(k1_tarski(X0),sK0) ),
    inference(forward_demodulation,[],[f262,f179])).

fof(f179,plain,(
    ! [X0] : k1_tarski(X0) = k2_relat_1(sK2(sK1,X0)) ),
    inference(unit_resulting_resolution,[],[f118,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k2_relat_1(sK2(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
        ? [X2] :
          ( k2_relat_1(X2) = k1_tarski(X1)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( k1_xboole_0 != X0
     => ! [X1] :
        ? [X2] :
          ( k2_relat_1(X2) = k1_tarski(X1)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_funct_1)).

fof(f118,plain,(
    k1_xboole_0 != sK1 ),
    inference(unit_resulting_resolution,[],[f116,f24,f117,f60])).

fof(f60,plain,
    ( k1_xboole_0 != sK1
    | ~ r1_tarski(k1_xboole_0,sK0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(forward_demodulation,[],[f58,f23])).

fof(f23,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f58,plain,
    ( k1_xboole_0 != sK1
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ r1_tarski(k2_relat_1(k1_xboole_0),sK0) ),
    inference(superposition,[],[f20,f22])).

fof(f22,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f20,plain,(
    ! [X2] :
      ( k1_relat_1(X2) != sK1
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ r1_tarski(k2_relat_1(X2),sK0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),X0)
          | k1_relat_1(X2) != X1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 != X0 ) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),X0)
          | k1_relat_1(X2) != X1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 != X0 ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ~ ( r1_tarski(k2_relat_1(X2),X0)
                  & k1_relat_1(X2) = X1 ) )
          & ~ ( k1_xboole_0 != X1
              & k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ~ ( r1_tarski(k2_relat_1(X2),X0)
                & k1_relat_1(X2) = X1 ) )
        & ~ ( k1_xboole_0 != X1
            & k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_1)).

fof(f117,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f32,f107])).

fof(f107,plain,(
    k1_xboole_0 = sK3(k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f32,f34,f25])).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

fof(f34,plain,(
    ! [X0] : k1_relat_1(sK3(X0)) = X0 ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( k1_xboole_0 = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => k1_xboole_0 = k1_funct_1(X1,X2) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).

fof(f32,plain,(
    ! [X0] : v1_relat_1(sK3(X0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f24,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f116,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(superposition,[],[f33,f107])).

fof(f33,plain,(
    ! [X0] : v1_funct_1(sK3(X0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f262,plain,(
    ! [X0] : ~ r1_tarski(k2_relat_1(sK2(sK1,X0)),sK0) ),
    inference(unit_resulting_resolution,[],[f123,f124,f131,f20])).

fof(f131,plain,(
    ! [X0] : sK1 = k1_relat_1(sK2(sK1,X0)) ),
    inference(unit_resulting_resolution,[],[f118,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k1_relat_1(sK2(X0,X1)) = X0
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f124,plain,(
    ! [X0] : v1_relat_1(sK2(sK1,X0)) ),
    inference(unit_resulting_resolution,[],[f118,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( v1_relat_1(sK2(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f123,plain,(
    ! [X0] : v1_funct_1(sK2(sK1,X0)) ),
    inference(unit_resulting_resolution,[],[f118,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( v1_funct_1(sK2(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f276,plain,(
    ! [X0] : ~ r2_hidden(sK4(k1_tarski(X0),sK0),sK0) ),
    inference(unit_resulting_resolution,[],[f268,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f534,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f283,f522])).

fof(f283,plain,(
    ! [X0] : ~ r2_hidden(sK4(k1_tarski(X0),sK0),k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f24,f276,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f584,plain,(
    sK0 = k1_relat_1(sK0) ),
    inference(unit_resulting_resolution,[],[f532,f553,f46])).

fof(f122,plain,(
    k1_xboole_0 != sK0 ),
    inference(unit_resulting_resolution,[],[f118,f21])).

fof(f21,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 = sK1 ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:53:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.51  % (14241)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.51  % (14222)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.51  % (14222)Refutation not found, incomplete strategy% (14222)------------------------------
% 0.21/0.51  % (14222)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (14222)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (14222)Memory used [KB]: 10618
% 0.21/0.51  % (14222)Time elapsed: 0.102 s
% 0.21/0.51  % (14222)------------------------------
% 0.21/0.51  % (14222)------------------------------
% 0.21/0.51  % (14227)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.51  % (14214)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.51  % (14217)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (14228)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.52  % (14238)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.52  % (14236)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.52  % (14221)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.52  % (14220)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.52  % (14237)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.52  % (14225)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (14229)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.53  % (14235)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.53  % (14230)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.53  % (14239)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.53  % (14230)Refutation not found, incomplete strategy% (14230)------------------------------
% 0.21/0.53  % (14230)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (14219)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (14230)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (14230)Memory used [KB]: 10618
% 0.21/0.53  % (14230)Time elapsed: 0.116 s
% 0.21/0.53  % (14230)------------------------------
% 0.21/0.53  % (14230)------------------------------
% 0.21/0.53  % (14218)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (14223)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.53  % (14223)Refutation not found, incomplete strategy% (14223)------------------------------
% 0.21/0.53  % (14223)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (14223)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (14223)Memory used [KB]: 10618
% 0.21/0.53  % (14223)Time elapsed: 0.095 s
% 0.21/0.53  % (14223)------------------------------
% 0.21/0.53  % (14223)------------------------------
% 0.21/0.54  % (14224)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (14234)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.54  % (14231)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.54  % (14233)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.54  % (14221)Refutation not found, incomplete strategy% (14221)------------------------------
% 0.21/0.54  % (14221)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (14221)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (14221)Memory used [KB]: 10746
% 0.21/0.54  % (14221)Time elapsed: 0.143 s
% 0.21/0.54  % (14221)------------------------------
% 0.21/0.54  % (14221)------------------------------
% 0.21/0.54  % (14232)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.54  % (14226)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.55  % (14215)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.55  % (14216)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.55  % (14213)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.55  % (14213)Refutation not found, incomplete strategy% (14213)------------------------------
% 0.21/0.55  % (14213)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (14213)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (14213)Memory used [KB]: 1663
% 0.21/0.55  % (14235)Refutation not found, incomplete strategy% (14235)------------------------------
% 0.21/0.55  % (14235)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (14235)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (14235)Memory used [KB]: 10746
% 0.21/0.55  % (14235)Time elapsed: 0.119 s
% 0.21/0.55  % (14235)------------------------------
% 0.21/0.55  % (14235)------------------------------
% 0.21/0.55  % (14213)Time elapsed: 0.145 s
% 0.21/0.55  % (14213)------------------------------
% 0.21/0.55  % (14213)------------------------------
% 0.21/0.55  % (14240)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.55  % (14242)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.55  % (14215)Refutation not found, incomplete strategy% (14215)------------------------------
% 0.21/0.55  % (14215)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (14215)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (14215)Memory used [KB]: 10746
% 0.21/0.55  % (14215)Time elapsed: 0.120 s
% 0.21/0.55  % (14215)------------------------------
% 0.21/0.55  % (14215)------------------------------
% 0.21/0.56  % (14237)Refutation found. Thanks to Tanya!
% 0.21/0.56  % SZS status Theorem for theBenchmark
% 0.21/0.56  % SZS output start Proof for theBenchmark
% 0.21/0.56  fof(f588,plain,(
% 0.21/0.56    $false),
% 0.21/0.56    inference(global_subsumption,[],[f122,f587])).
% 0.21/0.56  fof(f587,plain,(
% 0.21/0.56    k1_xboole_0 = sK0),
% 0.21/0.56    inference(forward_demodulation,[],[f584,f585])).
% 0.21/0.56  fof(f585,plain,(
% 0.21/0.56    k1_xboole_0 = k1_relat_1(sK0)),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f534,f553,f46])).
% 0.21/0.56  fof(f46,plain,(
% 0.21/0.56    ( ! [X0,X1] : (sP7(sK6(X0,X1),X0) | r2_hidden(sK6(X0,X1),X1) | k1_relat_1(X0) = X1) )),
% 0.21/0.56    inference(cnf_transformation,[],[f4])).
% 0.21/0.56  fof(f4,axiom,(
% 0.21/0.56    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).
% 0.21/0.56  fof(f553,plain,(
% 0.21/0.56    ( ! [X0] : (~sP7(X0,sK0)) )),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f532,f42])).
% 0.21/0.56  fof(f42,plain,(
% 0.21/0.56    ( ! [X2,X0] : (r2_hidden(k4_tarski(X2,sK8(X0,X2)),X0) | ~sP7(X2,X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f4])).
% 0.21/0.56  fof(f532,plain,(
% 0.21/0.56    ( ! [X0] : (~r2_hidden(X0,sK0)) )),
% 0.21/0.56    inference(backward_demodulation,[],[f276,f522])).
% 0.21/0.56  fof(f522,plain,(
% 0.21/0.56    ( ! [X0] : (sK4(k1_tarski(X0),sK0) = X0) )),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f277,f52])).
% 0.21/0.56  fof(f52,plain,(
% 0.21/0.56    ( ! [X2,X0] : (~r2_hidden(X2,k1_tarski(X0)) | X0 = X2) )),
% 0.21/0.56    inference(equality_resolution,[],[f39])).
% 0.21/0.56  fof(f39,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 0.21/0.56    inference(cnf_transformation,[],[f3])).
% 0.21/0.56  fof(f3,axiom,(
% 0.21/0.56    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 0.21/0.56  fof(f277,plain,(
% 0.21/0.56    ( ! [X0] : (r2_hidden(sK4(k1_tarski(X0),sK0),k1_tarski(X0))) )),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f268,f36])).
% 0.21/0.56  fof(f36,plain,(
% 0.21/0.56    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f18])).
% 0.21/0.56  fof(f18,plain,(
% 0.21/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.56    inference(ennf_transformation,[],[f1])).
% 0.21/0.56  fof(f1,axiom,(
% 0.21/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.56  fof(f268,plain,(
% 0.21/0.56    ( ! [X0] : (~r1_tarski(k1_tarski(X0),sK0)) )),
% 0.21/0.56    inference(forward_demodulation,[],[f262,f179])).
% 0.21/0.56  fof(f179,plain,(
% 0.21/0.56    ( ! [X0] : (k1_tarski(X0) = k2_relat_1(sK2(sK1,X0))) )),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f118,f30])).
% 0.21/0.56  fof(f30,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k1_tarski(X1) = k2_relat_1(sK2(X0,X1)) | k1_xboole_0 = X0) )),
% 0.21/0.56    inference(cnf_transformation,[],[f16])).
% 0.21/0.56  fof(f16,plain,(
% 0.21/0.56    ! [X0] : (! [X1] : ? [X2] : (k2_relat_1(X2) = k1_tarski(X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) | k1_xboole_0 = X0)),
% 0.21/0.56    inference(ennf_transformation,[],[f9])).
% 0.21/0.56  fof(f9,axiom,(
% 0.21/0.56    ! [X0] : (k1_xboole_0 != X0 => ! [X1] : ? [X2] : (k2_relat_1(X2) = k1_tarski(X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_funct_1)).
% 0.21/0.56  fof(f118,plain,(
% 0.21/0.56    k1_xboole_0 != sK1),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f116,f24,f117,f60])).
% 0.21/0.56  fof(f60,plain,(
% 0.21/0.56    k1_xboole_0 != sK1 | ~r1_tarski(k1_xboole_0,sK0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)),
% 0.21/0.56    inference(forward_demodulation,[],[f58,f23])).
% 0.21/0.56  fof(f23,plain,(
% 0.21/0.56    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.21/0.56    inference(cnf_transformation,[],[f5])).
% 0.21/0.56  fof(f5,axiom,(
% 0.21/0.56    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.21/0.56  fof(f58,plain,(
% 0.21/0.56    k1_xboole_0 != sK1 | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~r1_tarski(k2_relat_1(k1_xboole_0),sK0)),
% 0.21/0.56    inference(superposition,[],[f20,f22])).
% 0.21/0.56  fof(f22,plain,(
% 0.21/0.56    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.56    inference(cnf_transformation,[],[f5])).
% 0.21/0.56  fof(f20,plain,(
% 0.21/0.56    ( ! [X2] : (k1_relat_1(X2) != sK1 | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~r1_tarski(k2_relat_1(X2),sK0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f13])).
% 0.21/0.56  fof(f13,plain,(
% 0.21/0.56    ? [X0,X1] : (! [X2] : (~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = X1 | k1_xboole_0 != X0))),
% 0.21/0.56    inference(flattening,[],[f12])).
% 0.21/0.56  fof(f12,plain,(
% 0.21/0.56    ? [X0,X1] : (! [X2] : ((~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) & (k1_xboole_0 = X1 | k1_xboole_0 != X0))),
% 0.21/0.56    inference(ennf_transformation,[],[f11])).
% 0.21/0.56  fof(f11,negated_conjecture,(
% 0.21/0.56    ~! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 0.21/0.56    inference(negated_conjecture,[],[f10])).
% 0.21/0.56  fof(f10,conjecture,(
% 0.21/0.56    ! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_1)).
% 0.21/0.56  fof(f117,plain,(
% 0.21/0.56    v1_relat_1(k1_xboole_0)),
% 0.21/0.56    inference(superposition,[],[f32,f107])).
% 0.21/0.56  fof(f107,plain,(
% 0.21/0.56    k1_xboole_0 = sK3(k1_xboole_0)),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f32,f34,f25])).
% 0.21/0.56  fof(f25,plain,(
% 0.21/0.56    ( ! [X0] : (k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0) | k1_xboole_0 = X0) )),
% 0.21/0.56    inference(cnf_transformation,[],[f15])).
% 0.21/0.56  fof(f15,plain,(
% 0.21/0.56    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.56    inference(flattening,[],[f14])).
% 0.21/0.56  fof(f14,plain,(
% 0.21/0.56    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.56    inference(ennf_transformation,[],[f6])).
% 0.21/0.56  fof(f6,axiom,(
% 0.21/0.56    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).
% 0.21/0.56  fof(f34,plain,(
% 0.21/0.56    ( ! [X0] : (k1_relat_1(sK3(X0)) = X0) )),
% 0.21/0.56    inference(cnf_transformation,[],[f17])).
% 0.21/0.56  fof(f17,plain,(
% 0.21/0.56    ! [X0] : ? [X1] : (! [X2] : (k1_xboole_0 = k1_funct_1(X1,X2) | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.21/0.56    inference(ennf_transformation,[],[f8])).
% 0.21/0.56  fof(f8,axiom,(
% 0.21/0.56    ! [X0] : ? [X1] : (! [X2] : (r2_hidden(X2,X0) => k1_xboole_0 = k1_funct_1(X1,X2)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).
% 0.21/0.56  fof(f32,plain,(
% 0.21/0.56    ( ! [X0] : (v1_relat_1(sK3(X0))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f17])).
% 0.21/0.56  fof(f24,plain,(
% 0.21/0.56    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f2])).
% 0.21/0.56  fof(f2,axiom,(
% 0.21/0.56    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.56  fof(f116,plain,(
% 0.21/0.56    v1_funct_1(k1_xboole_0)),
% 0.21/0.56    inference(superposition,[],[f33,f107])).
% 0.21/0.56  fof(f33,plain,(
% 0.21/0.56    ( ! [X0] : (v1_funct_1(sK3(X0))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f17])).
% 0.21/0.56  fof(f262,plain,(
% 0.21/0.56    ( ! [X0] : (~r1_tarski(k2_relat_1(sK2(sK1,X0)),sK0)) )),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f123,f124,f131,f20])).
% 0.21/0.56  fof(f131,plain,(
% 0.21/0.56    ( ! [X0] : (sK1 = k1_relat_1(sK2(sK1,X0))) )),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f118,f29])).
% 0.21/0.56  fof(f29,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k1_relat_1(sK2(X0,X1)) = X0 | k1_xboole_0 = X0) )),
% 0.21/0.56    inference(cnf_transformation,[],[f16])).
% 0.21/0.56  fof(f124,plain,(
% 0.21/0.56    ( ! [X0] : (v1_relat_1(sK2(sK1,X0))) )),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f118,f27])).
% 0.21/0.56  fof(f27,plain,(
% 0.21/0.56    ( ! [X0,X1] : (v1_relat_1(sK2(X0,X1)) | k1_xboole_0 = X0) )),
% 0.21/0.56    inference(cnf_transformation,[],[f16])).
% 0.21/0.56  fof(f123,plain,(
% 0.21/0.56    ( ! [X0] : (v1_funct_1(sK2(sK1,X0))) )),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f118,f28])).
% 0.21/0.56  fof(f28,plain,(
% 0.21/0.56    ( ! [X0,X1] : (v1_funct_1(sK2(X0,X1)) | k1_xboole_0 = X0) )),
% 0.21/0.56    inference(cnf_transformation,[],[f16])).
% 0.21/0.56  fof(f276,plain,(
% 0.21/0.56    ( ! [X0] : (~r2_hidden(sK4(k1_tarski(X0),sK0),sK0)) )),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f268,f37])).
% 0.21/0.56  fof(f37,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f18])).
% 0.21/0.56  fof(f534,plain,(
% 0.21/0.56    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.21/0.56    inference(backward_demodulation,[],[f283,f522])).
% 0.21/0.56  fof(f283,plain,(
% 0.21/0.56    ( ! [X0] : (~r2_hidden(sK4(k1_tarski(X0),sK0),k1_xboole_0)) )),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f24,f276,f35])).
% 0.21/0.56  fof(f35,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f18])).
% 0.21/0.56  fof(f584,plain,(
% 0.21/0.56    sK0 = k1_relat_1(sK0)),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f532,f553,f46])).
% 0.21/0.56  fof(f122,plain,(
% 0.21/0.56    k1_xboole_0 != sK0),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f118,f21])).
% 0.21/0.56  fof(f21,plain,(
% 0.21/0.56    k1_xboole_0 != sK0 | k1_xboole_0 = sK1),
% 0.21/0.56    inference(cnf_transformation,[],[f13])).
% 0.21/0.56  % SZS output end Proof for theBenchmark
% 0.21/0.56  % (14237)------------------------------
% 0.21/0.56  % (14237)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (14237)Termination reason: Refutation
% 0.21/0.56  
% 0.21/0.56  % (14237)Memory used [KB]: 6780
% 0.21/0.56  % (14237)Time elapsed: 0.130 s
% 0.21/0.56  % (14237)------------------------------
% 0.21/0.56  % (14237)------------------------------
% 0.21/0.56  % (14211)Success in time 0.192 s
%------------------------------------------------------------------------------
