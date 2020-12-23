%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:43 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 488 expanded)
%              Number of leaves         :   10 ( 104 expanded)
%              Depth                    :   26
%              Number of atoms          :  166 (1500 expanded)
%              Number of equality atoms :   40 ( 330 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f224,plain,(
    $false ),
    inference(subsumption_resolution,[],[f223,f20])).

fof(f20,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r2_hidden(X2,X1)
          | ~ m1_subset_1(X2,X0) )
      & k1_xboole_0 != X1
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r2_hidden(X2,X1)
          | ~ m1_subset_1(X2,X0) )
      & k1_xboole_0 != X1
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ~ ( ! [X2] :
                ( m1_subset_1(X2,X0)
               => ~ r2_hidden(X2,X1) )
            & k1_xboole_0 != X1 ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ~ ( ! [X2] :
              ( m1_subset_1(X2,X0)
             => ~ r2_hidden(X2,X1) )
          & k1_xboole_0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_subset_1)).

fof(f223,plain,(
    k1_xboole_0 = sK1 ),
    inference(resolution,[],[f219,f22])).

fof(f22,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

fof(f219,plain,(
    v1_xboole_0(sK1) ),
    inference(resolution,[],[f201,f151])).

fof(f151,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_xboole_0)
      | v1_xboole_0(X0) ) ),
    inference(backward_demodulation,[],[f124,f126])).

fof(f126,plain,(
    k1_xboole_0 = sK0 ),
    inference(resolution,[],[f123,f22])).

fof(f123,plain,(
    v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f122,f20])).

fof(f122,plain,
    ( v1_xboole_0(sK0)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f117,f22])).

fof(f117,plain,
    ( v1_xboole_0(sK1)
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f96,f19])).

% (31737)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
fof(f19,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f96,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | v1_xboole_0(X0)
      | v1_xboole_0(sK0) ) ),
    inference(resolution,[],[f94,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f94,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK0))
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f93,f58])).

fof(f58,plain,
    ( ~ r2_hidden(sK2(sK1),sK0)
    | v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f57,f20])).

fof(f57,plain,
    ( v1_xboole_0(sK0)
    | ~ r2_hidden(sK2(sK1),sK0)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f56,f24])).

fof(f24,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f56,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | v1_xboole_0(sK0)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f27,f18])).

% (31757)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
fof(f18,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,sK0)
      | ~ r2_hidden(X2,sK1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f93,plain,
    ( r2_hidden(sK2(sK1),sK0)
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f92,f20])).

fof(f92,plain,
    ( r2_hidden(sK2(sK1),sK0)
    | v1_xboole_0(k1_zfmisc_1(sK0))
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f91,f24])).

fof(f91,plain,(
    ! [X8] :
      ( ~ r2_hidden(X8,sK1)
      | r2_hidden(X8,sK0)
      | v1_xboole_0(k1_zfmisc_1(sK0)) ) ),
    inference(forward_demodulation,[],[f89,f21])).

fof(f21,plain,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).

fof(f89,plain,(
    ! [X8] :
      ( ~ r2_hidden(X8,sK1)
      | r2_hidden(X8,k3_tarski(k1_zfmisc_1(sK0)))
      | v1_xboole_0(k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f48,f59])).

fof(f59,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f28,f19])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f48,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(X3,X0)
      | ~ r2_hidden(X2,X3)
      | r2_hidden(X2,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X2,X3)
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X2,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( r2_hidden(X3,X0)
              & r2_hidden(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).

fof(f124,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X0,sK0) ) ),
    inference(resolution,[],[f123,f26])).

fof(f201,plain,(
    m1_subset_1(sK1,k1_xboole_0) ),
    inference(backward_demodulation,[],[f128,f200])).

fof(f200,plain,(
    k1_xboole_0 = k1_zfmisc_1(k1_xboole_0) ),
    inference(resolution,[],[f197,f22])).

fof(f197,plain,(
    v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f195,f20])).

fof(f195,plain,
    ( v1_xboole_0(k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f165,f83])).

fof(f83,plain,(
    ! [X0] :
      ( ~ r2_xboole_0(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(duplicate_literal_removal,[],[f80])).

fof(f80,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r2_xboole_0(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f77,f23])).

fof(f23,plain,(
    ! [X0] :
      ( r2_xboole_0(k1_xboole_0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( r2_xboole_0(k1_xboole_0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( k1_xboole_0 != X0
     => r2_xboole_0(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_xboole_1)).

fof(f77,plain,(
    ! [X2,X1] :
      ( ~ r2_xboole_0(X2,X1)
      | X1 = X2
      | ~ r2_xboole_0(X1,X2) ) ),
    inference(resolution,[],[f64,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f64,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X1,X2)
      | X1 = X2
      | ~ r2_xboole_0(X2,X1) ) ),
    inference(resolution,[],[f31,f32])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f165,plain,
    ( r2_xboole_0(sK1,k1_xboole_0)
    | v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f164,f20])).

fof(f164,plain,
    ( k1_xboole_0 = sK1
    | r2_xboole_0(sK1,k1_xboole_0)
    | v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f163,f126])).

fof(f163,plain,
    ( r2_xboole_0(sK1,k1_xboole_0)
    | v1_xboole_0(k1_zfmisc_1(k1_xboole_0))
    | sK0 = sK1 ),
    inference(forward_demodulation,[],[f135,f126])).

fof(f135,plain,
    ( v1_xboole_0(k1_zfmisc_1(k1_xboole_0))
    | r2_xboole_0(sK1,sK0)
    | sK0 = sK1 ),
    inference(backward_demodulation,[],[f69,f126])).

fof(f69,plain,
    ( r2_xboole_0(sK1,sK0)
    | sK0 = sK1
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f34,f62])).

fof(f62,plain,
    ( r1_tarski(sK1,sK0)
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f59,f51])).

fof(f51,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_zfmisc_1(X0))
      | r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f128,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(backward_demodulation,[],[f19,f126])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n018.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 17:52:57 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.48  % (31740)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.49  % (31744)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.49  % (31741)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.50  % (31755)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.50  % (31747)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.50  % (31741)Refutation not found, incomplete strategy% (31741)------------------------------
% 0.22/0.50  % (31741)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (31741)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (31741)Memory used [KB]: 6140
% 0.22/0.50  % (31741)Time elapsed: 0.097 s
% 0.22/0.50  % (31741)------------------------------
% 0.22/0.50  % (31741)------------------------------
% 0.22/0.51  % (31739)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.51  % (31755)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % (31748)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f224,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(subsumption_resolution,[],[f223,f20])).
% 0.22/0.51  fof(f20,plain,(
% 0.22/0.51    k1_xboole_0 != sK1),
% 0.22/0.51    inference(cnf_transformation,[],[f13])).
% 0.22/0.51  fof(f13,plain,(
% 0.22/0.51    ? [X0,X1] : (! [X2] : (~r2_hidden(X2,X1) | ~m1_subset_1(X2,X0)) & k1_xboole_0 != X1 & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.51    inference(flattening,[],[f12])).
% 0.22/0.51  fof(f12,plain,(
% 0.22/0.51    ? [X0,X1] : ((! [X2] : (~r2_hidden(X2,X1) | ~m1_subset_1(X2,X0)) & k1_xboole_0 != X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f11])).
% 0.22/0.51  fof(f11,negated_conjecture,(
% 0.22/0.51    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ~(! [X2] : (m1_subset_1(X2,X0) => ~r2_hidden(X2,X1)) & k1_xboole_0 != X1))),
% 0.22/0.51    inference(negated_conjecture,[],[f10])).
% 0.22/0.51  fof(f10,conjecture,(
% 0.22/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ~(! [X2] : (m1_subset_1(X2,X0) => ~r2_hidden(X2,X1)) & k1_xboole_0 != X1))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_subset_1)).
% 0.22/0.51  fof(f223,plain,(
% 0.22/0.51    k1_xboole_0 = sK1),
% 0.22/0.51    inference(resolution,[],[f219,f22])).
% 0.22/0.51  fof(f22,plain,(
% 0.22/0.51    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.22/0.51    inference(cnf_transformation,[],[f14])).
% 0.22/0.51  fof(f14,plain,(
% 0.22/0.51    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f5])).
% 0.22/0.51  fof(f5,axiom,(
% 0.22/0.51    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).
% 0.22/0.51  fof(f219,plain,(
% 0.22/0.51    v1_xboole_0(sK1)),
% 0.22/0.51    inference(resolution,[],[f201,f151])).
% 0.22/0.51  fof(f151,plain,(
% 0.22/0.51    ( ! [X0] : (~m1_subset_1(X0,k1_xboole_0) | v1_xboole_0(X0)) )),
% 0.22/0.51    inference(backward_demodulation,[],[f124,f126])).
% 0.22/0.51  fof(f126,plain,(
% 0.22/0.51    k1_xboole_0 = sK0),
% 0.22/0.51    inference(resolution,[],[f123,f22])).
% 0.22/0.51  fof(f123,plain,(
% 0.22/0.51    v1_xboole_0(sK0)),
% 0.22/0.51    inference(subsumption_resolution,[],[f122,f20])).
% 0.22/0.51  fof(f122,plain,(
% 0.22/0.51    v1_xboole_0(sK0) | k1_xboole_0 = sK1),
% 0.22/0.51    inference(resolution,[],[f117,f22])).
% 0.22/0.51  fof(f117,plain,(
% 0.22/0.51    v1_xboole_0(sK1) | v1_xboole_0(sK0)),
% 0.22/0.51    inference(resolution,[],[f96,f19])).
% 0.22/0.51  % (31737)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.51  fof(f19,plain,(
% 0.22/0.51    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.22/0.51    inference(cnf_transformation,[],[f13])).
% 0.22/0.51  fof(f96,plain,(
% 0.22/0.51    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK0)) | v1_xboole_0(X0) | v1_xboole_0(sK0)) )),
% 0.22/0.51    inference(resolution,[],[f94,f26])).
% 0.22/0.51  fof(f26,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~v1_xboole_0(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f17])).
% 0.22/0.51  fof(f17,plain,(
% 0.22/0.51    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f9])).
% 0.22/0.51  fof(f9,axiom,(
% 0.22/0.51    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 0.22/0.51  fof(f94,plain,(
% 0.22/0.51    v1_xboole_0(k1_zfmisc_1(sK0)) | v1_xboole_0(sK0)),
% 0.22/0.51    inference(resolution,[],[f93,f58])).
% 0.22/0.51  fof(f58,plain,(
% 0.22/0.51    ~r2_hidden(sK2(sK1),sK0) | v1_xboole_0(sK0)),
% 0.22/0.51    inference(subsumption_resolution,[],[f57,f20])).
% 0.22/0.51  fof(f57,plain,(
% 0.22/0.51    v1_xboole_0(sK0) | ~r2_hidden(sK2(sK1),sK0) | k1_xboole_0 = sK1),
% 0.22/0.51    inference(resolution,[],[f56,f24])).
% 0.22/0.51  fof(f24,plain,(
% 0.22/0.51    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 0.22/0.51    inference(cnf_transformation,[],[f16])).
% 0.22/0.51  fof(f16,plain,(
% 0.22/0.51    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.22/0.51    inference(ennf_transformation,[],[f2])).
% 0.22/0.51  fof(f2,axiom,(
% 0.22/0.51    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.22/0.51  fof(f56,plain,(
% 0.22/0.51    ( ! [X0] : (~r2_hidden(X0,sK1) | v1_xboole_0(sK0) | ~r2_hidden(X0,sK0)) )),
% 0.22/0.51    inference(resolution,[],[f27,f18])).
% 0.22/0.51  % (31757)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.51  fof(f18,plain,(
% 0.22/0.51    ( ! [X2] : (~m1_subset_1(X2,sK0) | ~r2_hidden(X2,sK1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f13])).
% 0.22/0.51  fof(f27,plain,(
% 0.22/0.51    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f17])).
% 0.22/0.51  fof(f93,plain,(
% 0.22/0.51    r2_hidden(sK2(sK1),sK0) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 0.22/0.51    inference(subsumption_resolution,[],[f92,f20])).
% 0.22/0.51  fof(f92,plain,(
% 0.22/0.51    r2_hidden(sK2(sK1),sK0) | v1_xboole_0(k1_zfmisc_1(sK0)) | k1_xboole_0 = sK1),
% 0.22/0.51    inference(resolution,[],[f91,f24])).
% 0.22/0.51  fof(f91,plain,(
% 0.22/0.51    ( ! [X8] : (~r2_hidden(X8,sK1) | r2_hidden(X8,sK0) | v1_xboole_0(k1_zfmisc_1(sK0))) )),
% 0.22/0.51    inference(forward_demodulation,[],[f89,f21])).
% 0.22/0.51  fof(f21,plain,(
% 0.22/0.51    ( ! [X0] : (k3_tarski(k1_zfmisc_1(X0)) = X0) )),
% 0.22/0.51    inference(cnf_transformation,[],[f8])).
% 0.22/0.51  fof(f8,axiom,(
% 0.22/0.51    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).
% 0.22/0.51  fof(f89,plain,(
% 0.22/0.51    ( ! [X8] : (~r2_hidden(X8,sK1) | r2_hidden(X8,k3_tarski(k1_zfmisc_1(sK0))) | v1_xboole_0(k1_zfmisc_1(sK0))) )),
% 0.22/0.51    inference(resolution,[],[f48,f59])).
% 0.22/0.51  fof(f59,plain,(
% 0.22/0.51    r2_hidden(sK1,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 0.22/0.51    inference(resolution,[],[f28,f19])).
% 0.22/0.51  fof(f28,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f17])).
% 0.22/0.51  fof(f48,plain,(
% 0.22/0.51    ( ! [X2,X0,X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3) | r2_hidden(X2,k3_tarski(X0))) )),
% 0.22/0.51    inference(equality_resolution,[],[f40])).
% 0.22/0.51  fof(f40,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (~r2_hidden(X2,X3) | ~r2_hidden(X3,X0) | r2_hidden(X2,X1) | k3_tarski(X0) != X1) )),
% 0.22/0.51    inference(cnf_transformation,[],[f7])).
% 0.22/0.51  fof(f7,axiom,(
% 0.22/0.51    ! [X0,X1] : (k3_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).
% 0.22/0.51  fof(f124,plain,(
% 0.22/0.51    ( ! [X0] : (v1_xboole_0(X0) | ~m1_subset_1(X0,sK0)) )),
% 0.22/0.51    inference(resolution,[],[f123,f26])).
% 0.22/0.51  fof(f201,plain,(
% 0.22/0.51    m1_subset_1(sK1,k1_xboole_0)),
% 0.22/0.51    inference(backward_demodulation,[],[f128,f200])).
% 0.22/0.51  fof(f200,plain,(
% 0.22/0.51    k1_xboole_0 = k1_zfmisc_1(k1_xboole_0)),
% 0.22/0.51    inference(resolution,[],[f197,f22])).
% 0.22/0.51  fof(f197,plain,(
% 0.22/0.51    v1_xboole_0(k1_zfmisc_1(k1_xboole_0))),
% 0.22/0.51    inference(subsumption_resolution,[],[f195,f20])).
% 0.22/0.51  fof(f195,plain,(
% 0.22/0.51    v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = sK1),
% 0.22/0.51    inference(resolution,[],[f165,f83])).
% 0.22/0.51  fof(f83,plain,(
% 0.22/0.51    ( ! [X0] : (~r2_xboole_0(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.22/0.51    inference(duplicate_literal_removal,[],[f80])).
% 0.22/0.51  fof(f80,plain,(
% 0.22/0.51    ( ! [X0] : (k1_xboole_0 = X0 | ~r2_xboole_0(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.22/0.51    inference(resolution,[],[f77,f23])).
% 0.22/0.51  fof(f23,plain,(
% 0.22/0.51    ( ! [X0] : (r2_xboole_0(k1_xboole_0,X0) | k1_xboole_0 = X0) )),
% 0.22/0.51    inference(cnf_transformation,[],[f15])).
% 0.22/0.51  fof(f15,plain,(
% 0.22/0.51    ! [X0] : (r2_xboole_0(k1_xboole_0,X0) | k1_xboole_0 = X0)),
% 0.22/0.51    inference(ennf_transformation,[],[f4])).
% 0.22/0.51  fof(f4,axiom,(
% 0.22/0.51    ! [X0] : (k1_xboole_0 != X0 => r2_xboole_0(k1_xboole_0,X0))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_xboole_1)).
% 0.22/0.51  fof(f77,plain,(
% 0.22/0.51    ( ! [X2,X1] : (~r2_xboole_0(X2,X1) | X1 = X2 | ~r2_xboole_0(X1,X2)) )),
% 0.22/0.51    inference(resolution,[],[f64,f32])).
% 0.22/0.51  fof(f32,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_xboole_0(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f1])).
% 0.22/0.51  fof(f1,axiom,(
% 0.22/0.51    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).
% 0.22/0.51  fof(f64,plain,(
% 0.22/0.51    ( ! [X2,X1] : (~r1_tarski(X1,X2) | X1 = X2 | ~r2_xboole_0(X2,X1)) )),
% 0.22/0.51    inference(resolution,[],[f31,f32])).
% 0.22/0.51  fof(f31,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 0.22/0.51    inference(cnf_transformation,[],[f3])).
% 0.22/0.51  fof(f3,axiom,(
% 0.22/0.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.51  fof(f165,plain,(
% 0.22/0.51    r2_xboole_0(sK1,k1_xboole_0) | v1_xboole_0(k1_zfmisc_1(k1_xboole_0))),
% 0.22/0.51    inference(subsumption_resolution,[],[f164,f20])).
% 0.22/0.51  fof(f164,plain,(
% 0.22/0.51    k1_xboole_0 = sK1 | r2_xboole_0(sK1,k1_xboole_0) | v1_xboole_0(k1_zfmisc_1(k1_xboole_0))),
% 0.22/0.51    inference(forward_demodulation,[],[f163,f126])).
% 0.22/0.51  fof(f163,plain,(
% 0.22/0.51    r2_xboole_0(sK1,k1_xboole_0) | v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) | sK0 = sK1),
% 0.22/0.51    inference(forward_demodulation,[],[f135,f126])).
% 0.22/0.51  fof(f135,plain,(
% 0.22/0.51    v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) | r2_xboole_0(sK1,sK0) | sK0 = sK1),
% 0.22/0.51    inference(backward_demodulation,[],[f69,f126])).
% 0.22/0.51  fof(f69,plain,(
% 0.22/0.51    r2_xboole_0(sK1,sK0) | sK0 = sK1 | v1_xboole_0(k1_zfmisc_1(sK0))),
% 0.22/0.51    inference(resolution,[],[f34,f62])).
% 0.22/0.51  fof(f62,plain,(
% 0.22/0.51    r1_tarski(sK1,sK0) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 0.22/0.51    inference(resolution,[],[f59,f51])).
% 0.22/0.51  fof(f51,plain,(
% 0.22/0.51    ( ! [X2,X0] : (~r2_hidden(X2,k1_zfmisc_1(X0)) | r1_tarski(X2,X0)) )),
% 0.22/0.51    inference(equality_resolution,[],[f42])).
% 0.22/0.51  fof(f42,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.22/0.51    inference(cnf_transformation,[],[f6])).
% 0.22/0.51  fof(f6,axiom,(
% 0.22/0.51    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.22/0.51  fof(f34,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r1_tarski(X0,X1) | X0 = X1 | r2_xboole_0(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f1])).
% 0.22/0.51  fof(f128,plain,(
% 0.22/0.51    m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0))),
% 0.22/0.51    inference(backward_demodulation,[],[f19,f126])).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (31755)------------------------------
% 0.22/0.51  % (31755)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (31755)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (31755)Memory used [KB]: 1663
% 0.22/0.51  % (31755)Time elapsed: 0.110 s
% 0.22/0.51  % (31755)------------------------------
% 0.22/0.51  % (31755)------------------------------
% 0.22/0.51  % (31737)Refutation not found, incomplete strategy% (31737)------------------------------
% 0.22/0.51  % (31737)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (31737)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (31737)Memory used [KB]: 10618
% 0.22/0.51  % (31737)Time elapsed: 0.112 s
% 0.22/0.51  % (31737)------------------------------
% 0.22/0.51  % (31737)------------------------------
% 0.22/0.51  % (31735)Success in time 0.15 s
%------------------------------------------------------------------------------
