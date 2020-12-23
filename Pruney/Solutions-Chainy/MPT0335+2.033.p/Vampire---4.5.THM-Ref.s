%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:19 EST 2020

% Result     : Theorem 1.30s
% Output     : Refutation 1.30s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 208 expanded)
%              Number of leaves         :   12 (  59 expanded)
%              Depth                    :   14
%              Number of atoms          :   94 ( 354 expanded)
%              Number of equality atoms :   57 ( 226 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f482,plain,(
    $false ),
    inference(resolution,[],[f474,f119])).

fof(f119,plain,(
    ~ r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK2)) ),
    inference(forward_demodulation,[],[f117,f42])).

fof(f42,plain,(
    k3_xboole_0(sK1,sK2) = k2_enumset1(sK3,sK3,sK3,sK3) ),
    inference(definition_unfolding,[],[f20,f40])).

fof(f40,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f30,f39])).

fof(f39,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f37,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f37,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f30,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f20,plain,(
    k3_xboole_0(sK1,sK2) = k1_tarski(sK3) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_tarski(X3) != k3_xboole_0(X0,X2)
      & r2_hidden(X3,X0)
      & k3_xboole_0(X1,X2) = k1_tarski(X3)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_tarski(X3) != k3_xboole_0(X0,X2)
      & r2_hidden(X3,X0)
      & k3_xboole_0(X1,X2) = k1_tarski(X3)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r2_hidden(X3,X0)
          & k3_xboole_0(X1,X2) = k1_tarski(X3)
          & r1_tarski(X0,X1) )
       => k1_tarski(X3) = k3_xboole_0(X0,X2) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(X3,X0)
        & k3_xboole_0(X1,X2) = k1_tarski(X3)
        & r1_tarski(X0,X1) )
     => k1_tarski(X3) = k3_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_zfmisc_1)).

fof(f117,plain,(
    ~ r1_tarski(k3_xboole_0(sK0,sK2),k2_enumset1(sK3,sK3,sK3,sK3)) ),
    inference(unit_resulting_resolution,[],[f41,f111,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))
      | k2_enumset1(X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f27,f40,f40])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | k1_tarski(X1) = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f111,plain,(
    k1_xboole_0 != k3_xboole_0(sK0,sK2) ),
    inference(superposition,[],[f61,f55])).

fof(f55,plain,(
    ! [X0] : k3_xboole_0(sK0,k3_xboole_0(sK1,X0)) = k3_xboole_0(sK0,X0) ),
    inference(superposition,[],[f25,f50])).

fof(f50,plain,(
    sK0 = k3_xboole_0(sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f19,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f19,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f17])).

% (20768)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
fof(f25,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f61,plain,(
    k1_xboole_0 != k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f60,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f60,plain,(
    ~ r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f53,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f53,plain,(
    sK0 != k4_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    inference(forward_demodulation,[],[f52,f42])).

fof(f52,plain,(
    sK0 != k4_xboole_0(sK0,k2_enumset1(sK3,sK3,sK3,sK3)) ),
    inference(unit_resulting_resolution,[],[f21,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) != X0
      | ~ r2_hidden(X1,X0) ) ),
    inference(definition_unfolding,[],[f24,f40])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f21,plain,(
    r2_hidden(sK3,sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f41,plain,(
    k3_xboole_0(sK0,sK2) != k2_enumset1(sK3,sK3,sK3,sK3) ),
    inference(definition_unfolding,[],[f22,f40])).

fof(f22,plain,(
    k1_tarski(sK3) != k3_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f474,plain,(
    r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK2)) ),
    inference(superposition,[],[f464,f204])).

fof(f204,plain,(
    ! [X0] : k3_xboole_0(sK0,X0) = k3_xboole_0(sK1,k3_xboole_0(sK0,X0)) ),
    inference(superposition,[],[f25,f185])).

fof(f185,plain,(
    sK0 = k3_xboole_0(sK1,sK0) ),
    inference(forward_demodulation,[],[f179,f56])).

fof(f56,plain,(
    sK0 = k3_xboole_0(sK0,sK0) ),
    inference(unit_resulting_resolution,[],[f54,f31])).

fof(f54,plain,(
    r1_tarski(sK0,sK0) ),
    inference(superposition,[],[f32,f50])).

fof(f32,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f179,plain,(
    k3_xboole_0(sK1,sK0) = k3_xboole_0(sK0,sK0) ),
    inference(superposition,[],[f141,f55])).

fof(f141,plain,(
    ! [X3] : k3_xboole_0(X3,sK0) = k3_xboole_0(sK0,k3_xboole_0(X3,sK0)) ),
    inference(superposition,[],[f59,f26])).

fof(f26,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f59,plain,(
    ! [X0] : k3_xboole_0(sK0,X0) = k3_xboole_0(sK0,k3_xboole_0(sK0,X0)) ),
    inference(superposition,[],[f25,f56])).

fof(f464,plain,(
    ! [X0] : r1_tarski(k3_xboole_0(sK1,k3_xboole_0(X0,sK2)),k3_xboole_0(sK1,sK2)) ),
    inference(superposition,[],[f435,f26])).

fof(f435,plain,(
    ! [X2] : r1_tarski(k3_xboole_0(sK1,k3_xboole_0(sK2,X2)),k3_xboole_0(sK1,sK2)) ),
    inference(superposition,[],[f32,f124])).

fof(f124,plain,(
    ! [X0] : k3_xboole_0(sK1,k3_xboole_0(sK2,X0)) = k3_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK1,k3_xboole_0(sK2,X0))) ),
    inference(forward_demodulation,[],[f123,f25])).

fof(f123,plain,(
    ! [X0] : k3_xboole_0(k3_xboole_0(sK1,sK2),X0) = k3_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(k3_xboole_0(sK1,sK2),X0)) ),
    inference(superposition,[],[f25,f72])).

fof(f72,plain,(
    k3_xboole_0(sK1,sK2) = k3_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f68,f31])).

fof(f68,plain,(
    r1_tarski(k3_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2)) ),
    inference(superposition,[],[f48,f42])).

fof(f48,plain,(
    ! [X1] : r1_tarski(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1)) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k2_enumset1(X1,X1,X1,X1) != X0
      | r1_tarski(X0,k2_enumset1(X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f29,f40,f40])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) != X0
      | r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n014.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:40:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.49  % (20757)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.51  % (20765)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.51  % (20755)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.18/0.51  % (20751)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.18/0.52  % (20777)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.18/0.52  % (20774)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.18/0.52  % (20779)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.18/0.52  % (20763)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.18/0.53  % (20753)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.18/0.53  % (20771)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.30/0.53  % (20755)Refutation found. Thanks to Tanya!
% 1.30/0.53  % SZS status Theorem for theBenchmark
% 1.30/0.53  % (20775)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.30/0.53  % (20759)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.30/0.54  % (20767)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.30/0.54  % (20767)Refutation not found, incomplete strategy% (20767)------------------------------
% 1.30/0.54  % (20767)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.54  % (20767)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.54  
% 1.30/0.54  % (20767)Memory used [KB]: 6140
% 1.30/0.54  % (20767)Time elapsed: 0.088 s
% 1.30/0.54  % (20767)------------------------------
% 1.30/0.54  % (20767)------------------------------
% 1.30/0.54  % (20766)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.30/0.54  % (20778)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.30/0.54  % (20776)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.30/0.54  % (20781)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.30/0.54  % (20756)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.30/0.54  % (20769)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.30/0.54  % (20754)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.30/0.54  % (20769)Refutation not found, incomplete strategy% (20769)------------------------------
% 1.30/0.54  % (20769)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.54  % (20769)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.54  
% 1.30/0.54  % (20769)Memory used [KB]: 10618
% 1.30/0.54  % (20769)Time elapsed: 0.138 s
% 1.30/0.54  % (20769)------------------------------
% 1.30/0.54  % (20769)------------------------------
% 1.30/0.55  % (20758)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.30/0.55  % SZS output start Proof for theBenchmark
% 1.30/0.55  fof(f482,plain,(
% 1.30/0.55    $false),
% 1.30/0.55    inference(resolution,[],[f474,f119])).
% 1.30/0.55  fof(f119,plain,(
% 1.30/0.55    ~r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK2))),
% 1.30/0.55    inference(forward_demodulation,[],[f117,f42])).
% 1.30/0.55  fof(f42,plain,(
% 1.30/0.55    k3_xboole_0(sK1,sK2) = k2_enumset1(sK3,sK3,sK3,sK3)),
% 1.30/0.55    inference(definition_unfolding,[],[f20,f40])).
% 1.30/0.55  fof(f40,plain,(
% 1.30/0.55    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.30/0.55    inference(definition_unfolding,[],[f30,f39])).
% 1.30/0.55  fof(f39,plain,(
% 1.30/0.55    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.30/0.55    inference(definition_unfolding,[],[f37,f38])).
% 1.30/0.55  fof(f38,plain,(
% 1.30/0.55    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.30/0.55    inference(cnf_transformation,[],[f10])).
% 1.30/0.55  fof(f10,axiom,(
% 1.30/0.55    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.30/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.30/0.55  fof(f37,plain,(
% 1.30/0.55    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.30/0.55    inference(cnf_transformation,[],[f9])).
% 1.30/0.55  fof(f9,axiom,(
% 1.30/0.55    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.30/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.30/0.55  fof(f30,plain,(
% 1.30/0.55    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.30/0.55    inference(cnf_transformation,[],[f8])).
% 1.30/0.55  fof(f8,axiom,(
% 1.30/0.55    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.30/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.30/0.55  fof(f20,plain,(
% 1.30/0.55    k3_xboole_0(sK1,sK2) = k1_tarski(sK3)),
% 1.30/0.55    inference(cnf_transformation,[],[f17])).
% 1.30/0.55  fof(f17,plain,(
% 1.30/0.55    ? [X0,X1,X2,X3] : (k1_tarski(X3) != k3_xboole_0(X0,X2) & r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1))),
% 1.30/0.55    inference(flattening,[],[f16])).
% 1.30/0.55  fof(f16,plain,(
% 1.30/0.55    ? [X0,X1,X2,X3] : (k1_tarski(X3) != k3_xboole_0(X0,X2) & (r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)))),
% 1.30/0.55    inference(ennf_transformation,[],[f15])).
% 1.30/0.55  fof(f15,negated_conjecture,(
% 1.30/0.55    ~! [X0,X1,X2,X3] : ((r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => k1_tarski(X3) = k3_xboole_0(X0,X2))),
% 1.30/0.55    inference(negated_conjecture,[],[f14])).
% 1.30/0.55  fof(f14,conjecture,(
% 1.30/0.55    ! [X0,X1,X2,X3] : ((r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => k1_tarski(X3) = k3_xboole_0(X0,X2))),
% 1.30/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_zfmisc_1)).
% 1.30/0.55  fof(f117,plain,(
% 1.30/0.55    ~r1_tarski(k3_xboole_0(sK0,sK2),k2_enumset1(sK3,sK3,sK3,sK3))),
% 1.30/0.55    inference(unit_resulting_resolution,[],[f41,f111,f47])).
% 1.30/0.55  fof(f47,plain,(
% 1.30/0.55    ( ! [X0,X1] : (~r1_tarski(X0,k2_enumset1(X1,X1,X1,X1)) | k2_enumset1(X1,X1,X1,X1) = X0 | k1_xboole_0 = X0) )),
% 1.30/0.55    inference(definition_unfolding,[],[f27,f40,f40])).
% 1.30/0.55  fof(f27,plain,(
% 1.30/0.55    ( ! [X0,X1] : (k1_xboole_0 = X0 | k1_tarski(X1) = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 1.30/0.55    inference(cnf_transformation,[],[f12])).
% 1.30/0.55  fof(f12,axiom,(
% 1.30/0.55    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.30/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 1.30/0.55  fof(f111,plain,(
% 1.30/0.55    k1_xboole_0 != k3_xboole_0(sK0,sK2)),
% 1.30/0.55    inference(superposition,[],[f61,f55])).
% 1.30/0.55  fof(f55,plain,(
% 1.30/0.55    ( ! [X0] : (k3_xboole_0(sK0,k3_xboole_0(sK1,X0)) = k3_xboole_0(sK0,X0)) )),
% 1.30/0.55    inference(superposition,[],[f25,f50])).
% 1.30/0.55  fof(f50,plain,(
% 1.30/0.55    sK0 = k3_xboole_0(sK0,sK1)),
% 1.30/0.55    inference(unit_resulting_resolution,[],[f19,f31])).
% 1.30/0.55  fof(f31,plain,(
% 1.30/0.55    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.30/0.55    inference(cnf_transformation,[],[f18])).
% 1.30/0.55  fof(f18,plain,(
% 1.30/0.55    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.30/0.55    inference(ennf_transformation,[],[f6])).
% 1.30/0.55  fof(f6,axiom,(
% 1.30/0.55    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.30/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.30/0.55  fof(f19,plain,(
% 1.30/0.55    r1_tarski(sK0,sK1)),
% 1.30/0.55    inference(cnf_transformation,[],[f17])).
% 1.30/0.55  % (20768)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.30/0.55  fof(f25,plain,(
% 1.30/0.55    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 1.30/0.55    inference(cnf_transformation,[],[f4])).
% 1.30/0.55  fof(f4,axiom,(
% 1.30/0.55    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 1.30/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).
% 1.30/0.55  fof(f61,plain,(
% 1.30/0.55    k1_xboole_0 != k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),
% 1.30/0.55    inference(unit_resulting_resolution,[],[f60,f35])).
% 1.30/0.55  fof(f35,plain,(
% 1.30/0.55    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 1.30/0.55    inference(cnf_transformation,[],[f2])).
% 1.30/0.55  fof(f2,axiom,(
% 1.30/0.55    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.30/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.30/0.55  fof(f60,plain,(
% 1.30/0.55    ~r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))),
% 1.30/0.55    inference(unit_resulting_resolution,[],[f53,f34])).
% 1.30/0.55  fof(f34,plain,(
% 1.30/0.55    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 1.30/0.55    inference(cnf_transformation,[],[f7])).
% 1.30/0.55  fof(f7,axiom,(
% 1.30/0.55    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 1.30/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 1.30/0.55  fof(f53,plain,(
% 1.30/0.55    sK0 != k4_xboole_0(sK0,k3_xboole_0(sK1,sK2))),
% 1.30/0.55    inference(forward_demodulation,[],[f52,f42])).
% 1.30/0.55  fof(f52,plain,(
% 1.30/0.55    sK0 != k4_xboole_0(sK0,k2_enumset1(sK3,sK3,sK3,sK3))),
% 1.30/0.55    inference(unit_resulting_resolution,[],[f21,f43])).
% 1.30/0.55  fof(f43,plain,(
% 1.30/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) != X0 | ~r2_hidden(X1,X0)) )),
% 1.30/0.55    inference(definition_unfolding,[],[f24,f40])).
% 1.30/0.55  fof(f24,plain,(
% 1.30/0.55    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) )),
% 1.30/0.55    inference(cnf_transformation,[],[f13])).
% 1.30/0.55  fof(f13,axiom,(
% 1.30/0.55    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 1.30/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 1.30/0.55  fof(f21,plain,(
% 1.30/0.55    r2_hidden(sK3,sK0)),
% 1.30/0.55    inference(cnf_transformation,[],[f17])).
% 1.30/0.55  fof(f41,plain,(
% 1.30/0.55    k3_xboole_0(sK0,sK2) != k2_enumset1(sK3,sK3,sK3,sK3)),
% 1.30/0.55    inference(definition_unfolding,[],[f22,f40])).
% 1.30/0.55  fof(f22,plain,(
% 1.30/0.55    k1_tarski(sK3) != k3_xboole_0(sK0,sK2)),
% 1.30/0.55    inference(cnf_transformation,[],[f17])).
% 1.30/0.55  fof(f474,plain,(
% 1.30/0.55    r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK2))),
% 1.30/0.55    inference(superposition,[],[f464,f204])).
% 1.30/0.55  fof(f204,plain,(
% 1.30/0.55    ( ! [X0] : (k3_xboole_0(sK0,X0) = k3_xboole_0(sK1,k3_xboole_0(sK0,X0))) )),
% 1.30/0.55    inference(superposition,[],[f25,f185])).
% 1.30/0.55  fof(f185,plain,(
% 1.30/0.55    sK0 = k3_xboole_0(sK1,sK0)),
% 1.30/0.55    inference(forward_demodulation,[],[f179,f56])).
% 1.30/0.55  fof(f56,plain,(
% 1.30/0.55    sK0 = k3_xboole_0(sK0,sK0)),
% 1.30/0.55    inference(unit_resulting_resolution,[],[f54,f31])).
% 1.30/0.55  fof(f54,plain,(
% 1.30/0.55    r1_tarski(sK0,sK0)),
% 1.30/0.55    inference(superposition,[],[f32,f50])).
% 1.30/0.55  fof(f32,plain,(
% 1.30/0.55    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.30/0.55    inference(cnf_transformation,[],[f5])).
% 1.30/0.55  fof(f5,axiom,(
% 1.30/0.55    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.30/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.30/0.55  fof(f179,plain,(
% 1.30/0.55    k3_xboole_0(sK1,sK0) = k3_xboole_0(sK0,sK0)),
% 1.30/0.55    inference(superposition,[],[f141,f55])).
% 1.30/0.55  fof(f141,plain,(
% 1.30/0.55    ( ! [X3] : (k3_xboole_0(X3,sK0) = k3_xboole_0(sK0,k3_xboole_0(X3,sK0))) )),
% 1.30/0.55    inference(superposition,[],[f59,f26])).
% 1.30/0.55  fof(f26,plain,(
% 1.30/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.30/0.55    inference(cnf_transformation,[],[f1])).
% 1.30/0.55  fof(f1,axiom,(
% 1.30/0.55    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.30/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.30/0.55  fof(f59,plain,(
% 1.30/0.55    ( ! [X0] : (k3_xboole_0(sK0,X0) = k3_xboole_0(sK0,k3_xboole_0(sK0,X0))) )),
% 1.30/0.55    inference(superposition,[],[f25,f56])).
% 1.30/0.55  fof(f464,plain,(
% 1.30/0.55    ( ! [X0] : (r1_tarski(k3_xboole_0(sK1,k3_xboole_0(X0,sK2)),k3_xboole_0(sK1,sK2))) )),
% 1.30/0.55    inference(superposition,[],[f435,f26])).
% 1.30/0.55  fof(f435,plain,(
% 1.30/0.55    ( ! [X2] : (r1_tarski(k3_xboole_0(sK1,k3_xboole_0(sK2,X2)),k3_xboole_0(sK1,sK2))) )),
% 1.30/0.55    inference(superposition,[],[f32,f124])).
% 1.30/0.55  fof(f124,plain,(
% 1.30/0.55    ( ! [X0] : (k3_xboole_0(sK1,k3_xboole_0(sK2,X0)) = k3_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK1,k3_xboole_0(sK2,X0)))) )),
% 1.30/0.55    inference(forward_demodulation,[],[f123,f25])).
% 1.30/0.55  fof(f123,plain,(
% 1.30/0.55    ( ! [X0] : (k3_xboole_0(k3_xboole_0(sK1,sK2),X0) = k3_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(k3_xboole_0(sK1,sK2),X0))) )),
% 1.30/0.55    inference(superposition,[],[f25,f72])).
% 1.30/0.55  fof(f72,plain,(
% 1.30/0.55    k3_xboole_0(sK1,sK2) = k3_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2))),
% 1.30/0.55    inference(unit_resulting_resolution,[],[f68,f31])).
% 1.30/0.55  fof(f68,plain,(
% 1.30/0.55    r1_tarski(k3_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2))),
% 1.30/0.55    inference(superposition,[],[f48,f42])).
% 1.30/0.55  fof(f48,plain,(
% 1.30/0.55    ( ! [X1] : (r1_tarski(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1))) )),
% 1.30/0.55    inference(equality_resolution,[],[f45])).
% 1.30/0.55  fof(f45,plain,(
% 1.30/0.55    ( ! [X0,X1] : (k2_enumset1(X1,X1,X1,X1) != X0 | r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))) )),
% 1.30/0.55    inference(definition_unfolding,[],[f29,f40,f40])).
% 1.30/0.55  fof(f29,plain,(
% 1.30/0.55    ( ! [X0,X1] : (k1_tarski(X1) != X0 | r1_tarski(X0,k1_tarski(X1))) )),
% 1.30/0.55    inference(cnf_transformation,[],[f12])).
% 1.30/0.55  % SZS output end Proof for theBenchmark
% 1.30/0.55  % (20755)------------------------------
% 1.30/0.55  % (20755)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.55  % (20755)Termination reason: Refutation
% 1.30/0.55  
% 1.30/0.55  % (20755)Memory used [KB]: 6396
% 1.30/0.55  % (20755)Time elapsed: 0.123 s
% 1.30/0.55  % (20755)------------------------------
% 1.30/0.55  % (20755)------------------------------
% 1.30/0.55  % (20750)Success in time 0.183 s
%------------------------------------------------------------------------------
