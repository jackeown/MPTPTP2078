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
% DateTime   : Thu Dec  3 12:42:43 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   45 (  91 expanded)
%              Number of leaves         :    7 (  25 expanded)
%              Depth                    :    9
%              Number of atoms          :  100 ( 239 expanded)
%              Number of equality atoms :   12 (  34 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f450,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f60,f294,f449])).

fof(f449,plain,(
    spl12_2 ),
    inference(avatar_contradiction_clause,[],[f440])).

fof(f440,plain,
    ( $false
    | spl12_2 ),
    inference(unit_resulting_resolution,[],[f75,f296,f339,f29])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f339,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(sK5(sK0,sK2),X0),k2_zfmisc_1(sK0,sK1))
    | spl12_2 ),
    inference(unit_resulting_resolution,[],[f19,f327,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
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

fof(f327,plain,
    ( ! [X0,X1] : ~ r2_hidden(k4_tarski(sK5(sK0,sK2),X0),k2_zfmisc_1(sK2,X1))
    | spl12_2 ),
    inference(unit_resulting_resolution,[],[f297,f27])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f297,plain,
    ( ~ r2_hidden(sK5(sK0,sK2),sK2)
    | spl12_2 ),
    inference(unit_resulting_resolution,[],[f59,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f59,plain,
    ( ~ r1_tarski(sK0,sK2)
    | spl12_2 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl12_2
  <=> r1_tarski(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).

fof(f19,plain,(
    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X1,X3)
        | ~ r1_tarski(X0,X2) )
      & k1_xboole_0 != k2_zfmisc_1(X0,X1)
      & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X1,X3)
        | ~ r1_tarski(X0,X2) )
      & k1_xboole_0 != k2_zfmisc_1(X0,X1)
      & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
       => ( ( r1_tarski(X1,X3)
            & r1_tarski(X0,X2) )
          | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
     => ( ( r1_tarski(X1,X3)
          & r1_tarski(X0,X2) )
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_zfmisc_1)).

fof(f296,plain,
    ( r2_hidden(sK5(sK0,sK2),sK0)
    | spl12_2 ),
    inference(unit_resulting_resolution,[],[f59,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK5(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f75,plain,(
    r2_hidden(sK8(sK0,sK1,sK4(k2_zfmisc_1(sK0,sK1))),sK1) ),
    inference(unit_resulting_resolution,[],[f51,f49])).

fof(f49,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(sK8(X0,X1,X3),X1)
      | ~ r2_hidden(X3,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK8(X0,X1,X3),X1)
      | ~ r2_hidden(X3,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(f51,plain,(
    r2_hidden(sK4(k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f20,f21])).

fof(f21,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f20,plain,(
    k1_xboole_0 != k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f294,plain,(
    spl12_1 ),
    inference(avatar_contradiction_clause,[],[f284])).

fof(f284,plain,
    ( $false
    | spl12_1 ),
    inference(unit_resulting_resolution,[],[f74,f61,f116,f29])).

fof(f116,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(X0,sK5(sK1,sK3)),k2_zfmisc_1(sK0,sK1))
    | spl12_1 ),
    inference(unit_resulting_resolution,[],[f19,f69,f24])).

fof(f69,plain,
    ( ! [X0,X1] : ~ r2_hidden(k4_tarski(X0,sK5(sK1,sK3)),k2_zfmisc_1(X1,sK3))
    | spl12_1 ),
    inference(unit_resulting_resolution,[],[f62,f28])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f62,plain,
    ( ~ r2_hidden(sK5(sK1,sK3),sK3)
    | spl12_1 ),
    inference(unit_resulting_resolution,[],[f55,f26])).

fof(f55,plain,
    ( ~ r1_tarski(sK1,sK3)
    | spl12_1 ),
    inference(avatar_component_clause,[],[f53])).

fof(f53,plain,
    ( spl12_1
  <=> r1_tarski(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).

fof(f61,plain,
    ( r2_hidden(sK5(sK1,sK3),sK1)
    | spl12_1 ),
    inference(unit_resulting_resolution,[],[f55,f25])).

fof(f74,plain,(
    r2_hidden(sK7(sK0,sK1,sK4(k2_zfmisc_1(sK0,sK1))),sK0) ),
    inference(unit_resulting_resolution,[],[f51,f50])).

fof(f50,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(sK7(X0,X1,X3),X0)
      | ~ r2_hidden(X3,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK7(X0,X1,X3),X0)
      | ~ r2_hidden(X3,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f60,plain,
    ( ~ spl12_1
    | ~ spl12_2 ),
    inference(avatar_split_clause,[],[f18,f57,f53])).

fof(f18,plain,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_tarski(sK1,sK3) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:52:36 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.22/0.51  % (10771)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.52  % (10766)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.52  % (10769)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.52  % (10787)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.53  % (10774)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.53  % (10779)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.54  % (10782)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.54  % (10788)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.54  % (10787)Refutation not found, incomplete strategy% (10787)------------------------------
% 0.22/0.54  % (10787)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (10780)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.54  % (10782)Refutation not found, incomplete strategy% (10782)------------------------------
% 0.22/0.54  % (10782)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (10765)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.54  % (10782)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (10782)Memory used [KB]: 10618
% 0.22/0.54  % (10782)Time elapsed: 0.128 s
% 0.22/0.54  % (10782)------------------------------
% 0.22/0.54  % (10782)------------------------------
% 0.22/0.54  % (10767)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.54  % (10770)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.54  % (10777)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.54  % (10767)Refutation not found, incomplete strategy% (10767)------------------------------
% 0.22/0.54  % (10767)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (10767)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (10767)Memory used [KB]: 10618
% 0.22/0.54  % (10767)Time elapsed: 0.126 s
% 0.22/0.54  % (10767)------------------------------
% 0.22/0.54  % (10767)------------------------------
% 0.22/0.54  % (10768)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.55  % (10783)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.55  % (10787)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (10787)Memory used [KB]: 10746
% 0.22/0.55  % (10787)Time elapsed: 0.127 s
% 0.22/0.55  % (10787)------------------------------
% 0.22/0.55  % (10787)------------------------------
% 0.22/0.55  % (10769)Refutation found. Thanks to Tanya!
% 0.22/0.55  % SZS status Theorem for theBenchmark
% 0.22/0.55  % SZS output start Proof for theBenchmark
% 0.22/0.55  fof(f450,plain,(
% 0.22/0.55    $false),
% 0.22/0.55    inference(avatar_sat_refutation,[],[f60,f294,f449])).
% 0.22/0.55  fof(f449,plain,(
% 0.22/0.55    spl12_2),
% 0.22/0.55    inference(avatar_contradiction_clause,[],[f440])).
% 0.22/0.55  fof(f440,plain,(
% 0.22/0.55    $false | spl12_2),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f75,f296,f339,f29])).
% 0.22/0.55  fof(f29,plain,(
% 0.22/0.55    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f9])).
% 0.22/0.55  fof(f9,axiom,(
% 0.22/0.55    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 0.22/0.55  fof(f339,plain,(
% 0.22/0.55    ( ! [X0] : (~r2_hidden(k4_tarski(sK5(sK0,sK2),X0),k2_zfmisc_1(sK0,sK1))) ) | spl12_2),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f19,f327,f24])).
% 0.22/0.55  fof(f24,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(X0,X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f16])).
% 0.22/0.55  fof(f16,plain,(
% 0.22/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.22/0.55    inference(ennf_transformation,[],[f1])).
% 0.22/0.55  fof(f1,axiom,(
% 0.22/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.55  fof(f327,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~r2_hidden(k4_tarski(sK5(sK0,sK2),X0),k2_zfmisc_1(sK2,X1))) ) | spl12_2),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f297,f27])).
% 0.22/0.55  fof(f27,plain,(
% 0.22/0.55    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f9])).
% 0.22/0.55  fof(f297,plain,(
% 0.22/0.55    ~r2_hidden(sK5(sK0,sK2),sK2) | spl12_2),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f59,f26])).
% 0.22/0.55  fof(f26,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f16])).
% 0.22/0.55  fof(f59,plain,(
% 0.22/0.55    ~r1_tarski(sK0,sK2) | spl12_2),
% 0.22/0.55    inference(avatar_component_clause,[],[f57])).
% 0.22/0.55  fof(f57,plain,(
% 0.22/0.55    spl12_2 <=> r1_tarski(sK0,sK2)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).
% 0.22/0.55  fof(f19,plain,(
% 0.22/0.55    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 0.22/0.55    inference(cnf_transformation,[],[f14])).
% 0.22/0.55  fof(f14,plain,(
% 0.22/0.55    ? [X0,X1,X2,X3] : ((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 0.22/0.55    inference(flattening,[],[f13])).
% 0.22/0.55  fof(f13,plain,(
% 0.22/0.55    ? [X0,X1,X2,X3] : (((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1)) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 0.22/0.55    inference(ennf_transformation,[],[f11])).
% 0.22/0.55  fof(f11,negated_conjecture,(
% 0.22/0.55    ~! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 0.22/0.55    inference(negated_conjecture,[],[f10])).
% 0.22/0.55  fof(f10,conjecture,(
% 0.22/0.55    ! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_zfmisc_1)).
% 0.22/0.55  fof(f296,plain,(
% 0.22/0.55    r2_hidden(sK5(sK0,sK2),sK0) | spl12_2),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f59,f25])).
% 0.22/0.55  fof(f25,plain,(
% 0.22/0.55    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK5(X0,X1),X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f16])).
% 0.22/0.55  fof(f75,plain,(
% 0.22/0.55    r2_hidden(sK8(sK0,sK1,sK4(k2_zfmisc_1(sK0,sK1))),sK1)),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f51,f49])).
% 0.22/0.55  fof(f49,plain,(
% 0.22/0.55    ( ! [X0,X3,X1] : (r2_hidden(sK8(X0,X1,X3),X1) | ~r2_hidden(X3,k2_zfmisc_1(X0,X1))) )),
% 0.22/0.55    inference(equality_resolution,[],[f35])).
% 0.22/0.55  fof(f35,plain,(
% 0.22/0.55    ( ! [X2,X0,X3,X1] : (r2_hidden(sK8(X0,X1,X3),X1) | ~r2_hidden(X3,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 0.22/0.55    inference(cnf_transformation,[],[f8])).
% 0.22/0.55  fof(f8,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).
% 0.22/0.55  fof(f51,plain,(
% 0.22/0.55    r2_hidden(sK4(k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f20,f21])).
% 0.22/0.55  fof(f21,plain,(
% 0.22/0.55    ( ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0) )),
% 0.22/0.55    inference(cnf_transformation,[],[f15])).
% 0.22/0.55  fof(f15,plain,(
% 0.22/0.55    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.22/0.55    inference(ennf_transformation,[],[f3])).
% 0.22/0.55  fof(f3,axiom,(
% 0.22/0.55    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.22/0.55  fof(f20,plain,(
% 0.22/0.55    k1_xboole_0 != k2_zfmisc_1(sK0,sK1)),
% 0.22/0.55    inference(cnf_transformation,[],[f14])).
% 0.22/0.55  fof(f294,plain,(
% 0.22/0.55    spl12_1),
% 0.22/0.55    inference(avatar_contradiction_clause,[],[f284])).
% 0.22/0.55  fof(f284,plain,(
% 0.22/0.55    $false | spl12_1),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f74,f61,f116,f29])).
% 0.22/0.55  fof(f116,plain,(
% 0.22/0.55    ( ! [X0] : (~r2_hidden(k4_tarski(X0,sK5(sK1,sK3)),k2_zfmisc_1(sK0,sK1))) ) | spl12_1),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f19,f69,f24])).
% 0.22/0.55  fof(f69,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,sK5(sK1,sK3)),k2_zfmisc_1(X1,sK3))) ) | spl12_1),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f62,f28])).
% 0.22/0.55  fof(f28,plain,(
% 0.22/0.55    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,X3) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f9])).
% 0.22/0.55  fof(f62,plain,(
% 0.22/0.55    ~r2_hidden(sK5(sK1,sK3),sK3) | spl12_1),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f55,f26])).
% 0.22/0.55  fof(f55,plain,(
% 0.22/0.55    ~r1_tarski(sK1,sK3) | spl12_1),
% 0.22/0.55    inference(avatar_component_clause,[],[f53])).
% 0.22/0.55  fof(f53,plain,(
% 0.22/0.55    spl12_1 <=> r1_tarski(sK1,sK3)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).
% 0.22/0.55  fof(f61,plain,(
% 0.22/0.55    r2_hidden(sK5(sK1,sK3),sK1) | spl12_1),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f55,f25])).
% 0.22/0.55  fof(f74,plain,(
% 0.22/0.55    r2_hidden(sK7(sK0,sK1,sK4(k2_zfmisc_1(sK0,sK1))),sK0)),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f51,f50])).
% 0.22/0.55  fof(f50,plain,(
% 0.22/0.55    ( ! [X0,X3,X1] : (r2_hidden(sK7(X0,X1,X3),X0) | ~r2_hidden(X3,k2_zfmisc_1(X0,X1))) )),
% 0.22/0.55    inference(equality_resolution,[],[f34])).
% 0.22/0.55  fof(f34,plain,(
% 0.22/0.55    ( ! [X2,X0,X3,X1] : (r2_hidden(sK7(X0,X1,X3),X0) | ~r2_hidden(X3,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 0.22/0.55    inference(cnf_transformation,[],[f8])).
% 0.22/0.55  fof(f60,plain,(
% 0.22/0.55    ~spl12_1 | ~spl12_2),
% 0.22/0.55    inference(avatar_split_clause,[],[f18,f57,f53])).
% 0.22/0.55  fof(f18,plain,(
% 0.22/0.55    ~r1_tarski(sK0,sK2) | ~r1_tarski(sK1,sK3)),
% 0.22/0.55    inference(cnf_transformation,[],[f14])).
% 0.22/0.55  % SZS output end Proof for theBenchmark
% 0.22/0.55  % (10769)------------------------------
% 0.22/0.55  % (10769)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (10769)Termination reason: Refutation
% 0.22/0.55  
% 0.22/0.55  % (10769)Memory used [KB]: 6396
% 0.22/0.55  % (10769)Time elapsed: 0.140 s
% 0.22/0.55  % (10769)------------------------------
% 0.22/0.55  % (10769)------------------------------
% 0.22/0.55  % (10764)Success in time 0.177 s
%------------------------------------------------------------------------------
