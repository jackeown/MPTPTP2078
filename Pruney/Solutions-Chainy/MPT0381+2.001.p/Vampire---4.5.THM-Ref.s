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
% DateTime   : Thu Dec  3 12:45:35 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   44 ( 160 expanded)
%              Number of leaves         :   11 (  44 expanded)
%              Depth                    :   10
%              Number of atoms          :   85 ( 285 expanded)
%              Number of equality atoms :   21 (  73 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f171,plain,(
    $false ),
    inference(resolution,[],[f141,f79])).

fof(f79,plain,(
    r2_hidden(sK0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f25,f78])).

fof(f78,plain,(
    k1_xboole_0 = sK1 ),
    inference(unit_resulting_resolution,[],[f57,f73,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_enumset1(X1,X1,X1,X1),k1_zfmisc_1(X0))
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X1,X0) ) ),
    inference(definition_unfolding,[],[f27,f56])).

fof(f56,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f32,f55])).

fof(f55,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f43,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f43,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f32,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | k1_xboole_0 = X0
      | m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X1,X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
     => ( k1_xboole_0 != X0
       => m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_subset_1)).

fof(f73,plain,(
    m1_subset_1(sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f25,f65,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ r2_hidden(X1,X0)
      | m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f65,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(unit_resulting_resolution,[],[f25,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f57,plain,(
    ~ m1_subset_1(k2_enumset1(sK0,sK0,sK0,sK0),k1_zfmisc_1(sK1)) ),
    inference(definition_unfolding,[],[f26,f56])).

fof(f26,plain,(
    ~ m1_subset_1(k1_tarski(sK0),k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0,X1] :
      ( ~ m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

fof(f25,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f141,plain,(
    ~ r2_hidden(sK0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f130,f59])).

fof(f59,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f40,f45])).

fof(f45,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

% (20214)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% (20218)Refutation not found, incomplete strategy% (20218)------------------------------
% (20218)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (20218)Termination reason: Refutation not found, incomplete strategy

% (20218)Memory used [KB]: 10746
% (20218)Time elapsed: 0.109 s
% (20218)------------------------------
% (20218)------------------------------
% (20224)Refutation not found, incomplete strategy% (20224)------------------------------
% (20224)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (20232)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% (20225)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% (20230)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% (20222)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% (20223)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% (20210)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% (20228)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% (20222)Refutation not found, incomplete strategy% (20222)------------------------------
% (20222)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (20208)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% (20224)Termination reason: Refutation not found, incomplete strategy

% (20224)Memory used [KB]: 10618
% (20224)Time elapsed: 0.112 s
% (20224)------------------------------
% (20224)------------------------------
% (20222)Termination reason: Refutation not found, incomplete strategy

% (20222)Memory used [KB]: 1663
% (20222)Time elapsed: 0.109 s
% (20222)------------------------------
% (20222)------------------------------
% (20221)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% (20229)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% (20209)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% (20220)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% (20209)Refutation not found, incomplete strategy% (20209)------------------------------
% (20209)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (20209)Termination reason: Refutation not found, incomplete strategy

% (20209)Memory used [KB]: 1663
% (20209)Time elapsed: 0.123 s
% (20209)------------------------------
% (20209)------------------------------
% (20220)Refutation not found, incomplete strategy% (20220)------------------------------
% (20220)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (20220)Termination reason: Refutation not found, incomplete strategy

% (20220)Memory used [KB]: 10618
% (20220)Time elapsed: 0.091 s
% (20220)------------------------------
% (20220)------------------------------
fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f40,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f130,plain,(
    ~ r2_hidden(sK0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0))) ),
    inference(unit_resulting_resolution,[],[f79,f83,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k5_xboole_0(X1,X2))
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

fof(f83,plain,(
    r2_hidden(sK0,k3_xboole_0(k1_xboole_0,k1_xboole_0)) ),
    inference(backward_demodulation,[],[f69,f78])).

fof(f69,plain,(
    r2_hidden(sK0,k3_xboole_0(sK1,sK1)) ),
    inference(unit_resulting_resolution,[],[f25,f25,f60])).

fof(f60,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:28:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.37  ipcrm: permission denied for id (1234862081)
% 0.13/0.37  ipcrm: permission denied for id (1234894850)
% 0.21/0.37  ipcrm: permission denied for id (1234960388)
% 0.21/0.38  ipcrm: permission denied for id (1234993157)
% 0.21/0.38  ipcrm: permission denied for id (1235025926)
% 0.21/0.38  ipcrm: permission denied for id (1235058695)
% 0.21/0.38  ipcrm: permission denied for id (1235124232)
% 0.21/0.39  ipcrm: permission denied for id (1235353616)
% 0.21/0.40  ipcrm: permission denied for id (1235550237)
% 0.21/0.41  ipcrm: permission denied for id (1235615775)
% 0.21/0.41  ipcrm: permission denied for id (1235681314)
% 0.21/0.41  ipcrm: permission denied for id (1235714083)
% 0.21/0.42  ipcrm: permission denied for id (1235845160)
% 0.21/0.42  ipcrm: permission denied for id (1235877929)
% 0.21/0.42  ipcrm: permission denied for id (1235910698)
% 0.21/0.42  ipcrm: permission denied for id (1236009005)
% 0.21/0.43  ipcrm: permission denied for id (1236140082)
% 0.21/0.43  ipcrm: permission denied for id (1236172851)
% 0.21/0.44  ipcrm: permission denied for id (1236336700)
% 0.21/0.44  ipcrm: permission denied for id (1236435007)
% 0.21/0.45  ipcrm: permission denied for id (1236500545)
% 0.21/0.45  ipcrm: permission denied for id (1236533314)
% 0.21/0.45  ipcrm: permission denied for id (1236566083)
% 0.21/0.45  ipcrm: permission denied for id (1236598852)
% 0.21/0.46  ipcrm: permission denied for id (1236762696)
% 0.21/0.46  ipcrm: permission denied for id (1236992080)
% 0.21/0.47  ipcrm: permission denied for id (1237057618)
% 0.21/0.47  ipcrm: permission denied for id (1237221464)
% 0.21/0.48  ipcrm: permission denied for id (1237254233)
% 0.21/0.48  ipcrm: permission denied for id (1237418078)
% 0.21/0.48  ipcrm: permission denied for id (1237450847)
% 0.21/0.49  ipcrm: permission denied for id (1237581924)
% 0.21/0.49  ipcrm: permission denied for id (1237614695)
% 0.21/0.49  ipcrm: permission denied for id (1237647464)
% 0.21/0.50  ipcrm: permission denied for id (1237844078)
% 0.21/0.51  ipcrm: permission denied for id (1237975156)
% 0.21/0.51  ipcrm: permission denied for id (1238007925)
% 0.21/0.51  ipcrm: permission denied for id (1238040695)
% 0.21/0.51  ipcrm: permission denied for id (1238073465)
% 0.21/0.52  ipcrm: permission denied for id (1238171772)
% 0.21/0.52  ipcrm: permission denied for id (1238270079)
% 0.37/0.68  % (20213)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.37/0.68  % (20216)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.37/0.68  % (20224)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.37/0.69  % (20233)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.37/0.69  % (20218)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.37/0.69  % (20233)Refutation found. Thanks to Tanya!
% 0.37/0.69  % SZS status Theorem for theBenchmark
% 0.37/0.69  % SZS output start Proof for theBenchmark
% 0.37/0.69  fof(f171,plain,(
% 0.37/0.69    $false),
% 0.37/0.69    inference(resolution,[],[f141,f79])).
% 0.37/0.69  fof(f79,plain,(
% 0.37/0.69    r2_hidden(sK0,k1_xboole_0)),
% 0.37/0.69    inference(backward_demodulation,[],[f25,f78])).
% 0.37/0.69  fof(f78,plain,(
% 0.37/0.69    k1_xboole_0 = sK1),
% 0.37/0.69    inference(unit_resulting_resolution,[],[f57,f73,f58])).
% 0.37/0.69  fof(f58,plain,(
% 0.37/0.69    ( ! [X0,X1] : (m1_subset_1(k2_enumset1(X1,X1,X1,X1),k1_zfmisc_1(X0)) | k1_xboole_0 = X0 | ~m1_subset_1(X1,X0)) )),
% 0.37/0.69    inference(definition_unfolding,[],[f27,f56])).
% 0.37/0.69  fof(f56,plain,(
% 0.37/0.69    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.37/0.69    inference(definition_unfolding,[],[f32,f55])).
% 0.37/0.69  fof(f55,plain,(
% 0.37/0.69    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.37/0.69    inference(definition_unfolding,[],[f43,f47])).
% 0.37/0.69  fof(f47,plain,(
% 0.37/0.69    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.37/0.69    inference(cnf_transformation,[],[f12])).
% 0.37/0.69  fof(f12,axiom,(
% 0.37/0.69    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.37/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.37/0.69  fof(f43,plain,(
% 0.37/0.69    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.37/0.69    inference(cnf_transformation,[],[f11])).
% 0.37/0.69  fof(f11,axiom,(
% 0.37/0.69    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.37/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.37/0.69  fof(f32,plain,(
% 0.37/0.69    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.37/0.69    inference(cnf_transformation,[],[f10])).
% 0.37/0.69  fof(f10,axiom,(
% 0.37/0.69    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.37/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.37/0.69  fof(f27,plain,(
% 0.37/0.69    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | k1_xboole_0 = X0 | m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))) )),
% 0.37/0.69    inference(cnf_transformation,[],[f20])).
% 0.37/0.69  fof(f20,plain,(
% 0.37/0.69    ! [X0,X1] : (m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) | k1_xboole_0 = X0 | ~m1_subset_1(X1,X0))),
% 0.37/0.69    inference(flattening,[],[f19])).
% 0.37/0.69  fof(f19,plain,(
% 0.37/0.69    ! [X0,X1] : ((m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) | k1_xboole_0 = X0) | ~m1_subset_1(X1,X0))),
% 0.37/0.69    inference(ennf_transformation,[],[f15])).
% 0.37/0.69  fof(f15,axiom,(
% 0.37/0.69    ! [X0,X1] : (m1_subset_1(X1,X0) => (k1_xboole_0 != X0 => m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))))),
% 0.37/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_subset_1)).
% 0.37/0.69  fof(f73,plain,(
% 0.37/0.69    m1_subset_1(sK0,sK1)),
% 0.37/0.69    inference(unit_resulting_resolution,[],[f25,f65,f30])).
% 0.37/0.69  fof(f30,plain,(
% 0.37/0.69    ( ! [X0,X1] : (v1_xboole_0(X0) | ~r2_hidden(X1,X0) | m1_subset_1(X1,X0)) )),
% 0.37/0.69    inference(cnf_transformation,[],[f21])).
% 0.37/0.69  fof(f21,plain,(
% 0.37/0.69    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.37/0.69    inference(ennf_transformation,[],[f14])).
% 0.37/0.69  fof(f14,axiom,(
% 0.37/0.69    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.37/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 0.37/0.69  fof(f65,plain,(
% 0.37/0.69    ~v1_xboole_0(sK1)),
% 0.37/0.69    inference(unit_resulting_resolution,[],[f25,f42])).
% 0.37/0.69  fof(f42,plain,(
% 0.37/0.69    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~r2_hidden(X1,X0)) )),
% 0.37/0.69    inference(cnf_transformation,[],[f2])).
% 0.37/0.69  fof(f2,axiom,(
% 0.37/0.69    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.37/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.37/0.69  fof(f57,plain,(
% 0.37/0.69    ~m1_subset_1(k2_enumset1(sK0,sK0,sK0,sK0),k1_zfmisc_1(sK1))),
% 0.37/0.69    inference(definition_unfolding,[],[f26,f56])).
% 0.37/0.69  fof(f26,plain,(
% 0.37/0.69    ~m1_subset_1(k1_tarski(sK0),k1_zfmisc_1(sK1))),
% 0.37/0.69    inference(cnf_transformation,[],[f18])).
% 0.37/0.69  fof(f18,plain,(
% 0.37/0.69    ? [X0,X1] : (~m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) & r2_hidden(X0,X1))),
% 0.37/0.69    inference(ennf_transformation,[],[f17])).
% 0.37/0.69  fof(f17,negated_conjecture,(
% 0.37/0.69    ~! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 0.37/0.69    inference(negated_conjecture,[],[f16])).
% 0.37/0.69  fof(f16,conjecture,(
% 0.37/0.69    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 0.37/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).
% 0.37/0.69  fof(f25,plain,(
% 0.37/0.69    r2_hidden(sK0,sK1)),
% 0.37/0.69    inference(cnf_transformation,[],[f18])).
% 0.37/0.69  fof(f141,plain,(
% 0.37/0.69    ~r2_hidden(sK0,k1_xboole_0)),
% 0.37/0.69    inference(forward_demodulation,[],[f130,f59])).
% 0.37/0.69  fof(f59,plain,(
% 0.37/0.69    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0) )),
% 0.37/0.69    inference(definition_unfolding,[],[f40,f45])).
% 0.37/0.69  fof(f45,plain,(
% 0.37/0.69    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.37/0.69    inference(cnf_transformation,[],[f7])).
% 0.37/0.69  % (20214)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.37/0.69  % (20218)Refutation not found, incomplete strategy% (20218)------------------------------
% 0.37/0.69  % (20218)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.37/0.69  % (20218)Termination reason: Refutation not found, incomplete strategy
% 0.37/0.69  
% 0.37/0.69  % (20218)Memory used [KB]: 10746
% 0.37/0.69  % (20218)Time elapsed: 0.109 s
% 0.37/0.69  % (20218)------------------------------
% 0.37/0.69  % (20218)------------------------------
% 0.37/0.69  % (20224)Refutation not found, incomplete strategy% (20224)------------------------------
% 0.37/0.69  % (20224)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.37/0.69  % (20232)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.37/0.70  % (20225)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.37/0.70  % (20230)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.37/0.70  % (20222)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.37/0.70  % (20223)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.37/0.70  % (20210)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.37/0.70  % (20228)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.37/0.70  % (20222)Refutation not found, incomplete strategy% (20222)------------------------------
% 0.37/0.70  % (20222)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.37/0.70  % (20208)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.37/0.70  % (20224)Termination reason: Refutation not found, incomplete strategy
% 0.37/0.70  
% 0.37/0.70  % (20224)Memory used [KB]: 10618
% 0.37/0.70  % (20224)Time elapsed: 0.112 s
% 0.37/0.70  % (20224)------------------------------
% 0.37/0.70  % (20224)------------------------------
% 0.37/0.70  % (20222)Termination reason: Refutation not found, incomplete strategy
% 0.37/0.70  
% 0.37/0.70  % (20222)Memory used [KB]: 1663
% 0.37/0.70  % (20222)Time elapsed: 0.109 s
% 0.37/0.70  % (20222)------------------------------
% 0.37/0.70  % (20222)------------------------------
% 0.37/0.70  % (20221)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.37/0.70  % (20229)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.37/0.71  % (20209)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.37/0.71  % (20220)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.37/0.71  % (20209)Refutation not found, incomplete strategy% (20209)------------------------------
% 0.37/0.71  % (20209)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.37/0.71  % (20209)Termination reason: Refutation not found, incomplete strategy
% 0.37/0.71  
% 0.37/0.71  % (20209)Memory used [KB]: 1663
% 0.37/0.71  % (20209)Time elapsed: 0.123 s
% 0.37/0.71  % (20209)------------------------------
% 0.37/0.71  % (20209)------------------------------
% 0.37/0.71  % (20220)Refutation not found, incomplete strategy% (20220)------------------------------
% 0.37/0.71  % (20220)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.37/0.71  % (20220)Termination reason: Refutation not found, incomplete strategy
% 0.37/0.71  
% 0.37/0.71  % (20220)Memory used [KB]: 10618
% 0.37/0.71  % (20220)Time elapsed: 0.091 s
% 0.37/0.71  % (20220)------------------------------
% 0.37/0.71  % (20220)------------------------------
% 0.37/0.71  fof(f7,axiom,(
% 0.37/0.71    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.37/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.37/0.71  fof(f40,plain,(
% 0.37/0.71    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.37/0.71    inference(cnf_transformation,[],[f9])).
% 0.37/0.71  fof(f9,axiom,(
% 0.37/0.71    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.37/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.37/0.71  fof(f130,plain,(
% 0.37/0.71    ~r2_hidden(sK0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0)))),
% 0.37/0.71    inference(unit_resulting_resolution,[],[f79,f83,f52])).
% 0.37/0.71  fof(f52,plain,(
% 0.37/0.71    ( ! [X2,X0,X1] : (~r2_hidden(X0,k5_xboole_0(X1,X2)) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) )),
% 0.37/0.71    inference(cnf_transformation,[],[f24])).
% 0.37/0.71  fof(f24,plain,(
% 0.37/0.71    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 0.37/0.71    inference(ennf_transformation,[],[f4])).
% 0.37/0.71  fof(f4,axiom,(
% 0.37/0.71    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 0.37/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).
% 0.37/0.71  fof(f83,plain,(
% 0.37/0.71    r2_hidden(sK0,k3_xboole_0(k1_xboole_0,k1_xboole_0))),
% 0.37/0.71    inference(backward_demodulation,[],[f69,f78])).
% 0.37/0.71  fof(f69,plain,(
% 0.37/0.71    r2_hidden(sK0,k3_xboole_0(sK1,sK1))),
% 0.37/0.71    inference(unit_resulting_resolution,[],[f25,f25,f60])).
% 0.37/0.71  fof(f60,plain,(
% 0.37/0.71    ( ! [X0,X3,X1] : (r2_hidden(X3,k3_xboole_0(X0,X1)) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) )),
% 0.37/0.71    inference(equality_resolution,[],[f38])).
% 0.37/0.71  fof(f38,plain,(
% 0.37/0.71    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | r2_hidden(X3,X2) | k3_xboole_0(X0,X1) != X2) )),
% 0.37/0.71    inference(cnf_transformation,[],[f3])).
% 0.37/0.71  fof(f3,axiom,(
% 0.37/0.71    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.37/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 0.37/0.71  % SZS output end Proof for theBenchmark
% 0.37/0.71  % (20233)------------------------------
% 0.37/0.71  % (20233)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.37/0.71  % (20233)Termination reason: Refutation
% 0.37/0.71  
% 0.37/0.71  % (20233)Memory used [KB]: 6268
% 0.37/0.71  % (20233)Time elapsed: 0.119 s
% 0.37/0.71  % (20233)------------------------------
% 0.37/0.71  % (20233)------------------------------
% 0.37/0.71  % (20215)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.37/0.71  % (20074)Success in time 0.344 s
%------------------------------------------------------------------------------
