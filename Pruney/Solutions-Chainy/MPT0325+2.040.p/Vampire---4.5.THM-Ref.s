%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:43 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 1.57s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 102 expanded)
%              Number of leaves         :    8 (  29 expanded)
%              Depth                    :   10
%              Number of atoms          :  113 ( 263 expanded)
%              Number of equality atoms :   13 (  38 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f498,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f75,f303,f497])).

fof(f497,plain,(
    spl13_2 ),
    inference(avatar_contradiction_clause,[],[f482])).

fof(f482,plain,
    ( $false
    | spl13_2 ),
    inference(unit_resulting_resolution,[],[f90,f305,f314,f112])).

fof(f112,plain,(
    ! [X8,X9] :
      ( r2_hidden(k4_tarski(X8,X9),k2_zfmisc_1(sK2,sK3))
      | ~ r2_hidden(X8,sK0)
      | ~ r2_hidden(X9,sK1) ) ),
    inference(resolution,[],[f78,f39])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X1,X3)
      | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f78,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(sK0,sK1))
      | r2_hidden(X0,k2_zfmisc_1(sK2,sK3)) ) ),
    inference(resolution,[],[f18,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
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

fof(f18,plain,(
    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f13])).

% (12469)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% (12487)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% (12465)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% (12495)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% (12481)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% (12474)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% (12494)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% (12490)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% (12472)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% (12492)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% (12488)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% (12488)Refutation not found, incomplete strategy% (12488)------------------------------
% (12488)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (12488)Termination reason: Refutation not found, incomplete strategy

% (12488)Memory used [KB]: 10746
% (12488)Time elapsed: 0.159 s
% (12488)------------------------------
% (12488)------------------------------
fof(f13,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X1,X3)
        | ~ r1_tarski(X0,X2) )
      & k1_xboole_0 != k2_zfmisc_1(X0,X1)
      & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X1,X3)
        | ~ r1_tarski(X0,X2) )
      & k1_xboole_0 != k2_zfmisc_1(X0,X1)
      & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
       => ( ( r1_tarski(X1,X3)
            & r1_tarski(X0,X2) )
          | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
     => ( ( r1_tarski(X1,X3)
          & r1_tarski(X0,X2) )
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_zfmisc_1)).

fof(f314,plain,
    ( ! [X0,X1] : ~ r2_hidden(k4_tarski(sK6(sK0,sK2),X0),k2_zfmisc_1(sK2,X1))
    | spl13_2 ),
    inference(resolution,[],[f306,f37])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f306,plain,
    ( ~ r2_hidden(sK6(sK0,sK2),sK2)
    | spl13_2 ),
    inference(resolution,[],[f74,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK6(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f74,plain,
    ( ~ r1_tarski(sK0,sK2)
    | spl13_2 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl13_2
  <=> r1_tarski(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_2])])).

fof(f305,plain,
    ( r2_hidden(sK6(sK0,sK2),sK0)
    | spl13_2 ),
    inference(resolution,[],[f74,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f90,plain,(
    r2_hidden(sK9(sK0,sK1,sK4(k2_zfmisc_1(sK0,sK1))),sK1) ),
    inference(resolution,[],[f58,f43])).

fof(f43,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(sK9(X0,X1,X3),X1)
      | ~ r2_hidden(X3,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK9(X0,X1,X3),X1)
      | ~ r2_hidden(X3,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(f58,plain,(
    r2_hidden(sK4(k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f47,f49])).

fof(f49,plain,(
    ! [X0] :
      ( sQ12_eqProxy(k1_xboole_0,X0)
      | r2_hidden(sK4(X0),X0) ) ),
    inference(equality_proxy_replacement,[],[f22,f45])).

fof(f45,plain,(
    ! [X1,X0] :
      ( sQ12_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ12_eqProxy])])).

fof(f22,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | r2_hidden(sK4(X0),X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f47,plain,(
    ~ sQ12_eqProxy(k1_xboole_0,k2_zfmisc_1(sK0,sK1)) ),
    inference(equality_proxy_replacement,[],[f19,f45])).

fof(f19,plain,(
    k1_xboole_0 != k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f303,plain,(
    spl13_1 ),
    inference(avatar_contradiction_clause,[],[f285])).

fof(f285,plain,
    ( $false
    | spl13_1 ),
    inference(unit_resulting_resolution,[],[f58,f281,f44])).

fof(f44,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(sK8(X0,X1,X3),X0)
      | ~ r2_hidden(X3,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK8(X0,X1,X3),X0)
      | ~ r2_hidden(X3,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f281,plain,
    ( ! [X10] : ~ r2_hidden(X10,sK0)
    | spl13_1 ),
    inference(subsumption_resolution,[],[f273,f87])).

fof(f87,plain,
    ( ! [X2,X3] : ~ r2_hidden(k4_tarski(X2,sK6(sK1,sK3)),k2_zfmisc_1(X3,sK3))
    | spl13_1 ),
    inference(resolution,[],[f77,f38])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f77,plain,
    ( ~ r2_hidden(sK6(sK1,sK3),sK3)
    | spl13_1 ),
    inference(resolution,[],[f70,f28])).

fof(f70,plain,
    ( ~ r1_tarski(sK1,sK3)
    | spl13_1 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl13_1
  <=> r1_tarski(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1])])).

fof(f273,plain,
    ( ! [X10] :
        ( ~ r2_hidden(X10,sK0)
        | r2_hidden(k4_tarski(X10,sK6(sK1,sK3)),k2_zfmisc_1(sK2,sK3)) )
    | spl13_1 ),
    inference(resolution,[],[f81,f78])).

fof(f81,plain,
    ( ! [X4,X3] :
        ( r2_hidden(k4_tarski(X3,sK6(sK1,sK3)),k2_zfmisc_1(X4,sK1))
        | ~ r2_hidden(X3,X4) )
    | spl13_1 ),
    inference(resolution,[],[f76,f39])).

fof(f76,plain,
    ( r2_hidden(sK6(sK1,sK3),sK1)
    | spl13_1 ),
    inference(resolution,[],[f70,f27])).

fof(f75,plain,
    ( ~ spl13_1
    | ~ spl13_2 ),
    inference(avatar_split_clause,[],[f17,f72,f68])).

fof(f17,plain,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_tarski(sK1,sK3) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:53:11 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.52  % (12470)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.53  % (12467)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.53  % (12478)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.53  % (12466)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.53  % (12466)Refutation not found, incomplete strategy% (12466)------------------------------
% 0.22/0.53  % (12466)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (12466)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (12466)Memory used [KB]: 10618
% 0.22/0.53  % (12466)Time elapsed: 0.108 s
% 0.22/0.53  % (12466)------------------------------
% 0.22/0.53  % (12466)------------------------------
% 0.22/0.54  % (12473)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.54  % (12489)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.54  % (12477)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.54  % (12484)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.54  % (12478)Refutation found. Thanks to Tanya!
% 0.22/0.54  % SZS status Theorem for theBenchmark
% 0.22/0.54  % SZS output start Proof for theBenchmark
% 0.22/0.54  fof(f498,plain,(
% 0.22/0.54    $false),
% 0.22/0.54    inference(avatar_sat_refutation,[],[f75,f303,f497])).
% 0.22/0.54  fof(f497,plain,(
% 0.22/0.54    spl13_2),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f482])).
% 0.22/0.54  fof(f482,plain,(
% 0.22/0.54    $false | spl13_2),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f90,f305,f314,f112])).
% 0.22/0.54  fof(f112,plain,(
% 0.22/0.54    ( ! [X8,X9] : (r2_hidden(k4_tarski(X8,X9),k2_zfmisc_1(sK2,sK3)) | ~r2_hidden(X8,sK0) | ~r2_hidden(X9,sK1)) )),
% 0.22/0.54    inference(resolution,[],[f78,f39])).
% 0.22/0.54  fof(f39,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (~r2_hidden(X0,X2) | ~r2_hidden(X1,X3) | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f8])).
% 0.22/0.54  fof(f8,axiom,(
% 0.22/0.54    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 0.22/0.54  fof(f78,plain,(
% 0.22/0.54    ( ! [X0] : (~r2_hidden(X0,k2_zfmisc_1(sK0,sK1)) | r2_hidden(X0,k2_zfmisc_1(sK2,sK3))) )),
% 0.22/0.54    inference(resolution,[],[f18,f26])).
% 0.22/0.54  fof(f26,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f16])).
% 0.22/0.54  fof(f16,plain,(
% 0.22/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f1])).
% 0.22/0.54  fof(f1,axiom,(
% 0.22/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.54  fof(f18,plain,(
% 0.22/0.54    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 0.22/0.54    inference(cnf_transformation,[],[f13])).
% 0.22/0.55  % (12469)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.55  % (12487)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.55  % (12465)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.55  % (12495)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.56  % (12481)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.56  % (12474)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.56  % (12494)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.56  % (12490)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.56  % (12472)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.57  % (12492)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.57/0.57  % (12488)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.57/0.57  % (12488)Refutation not found, incomplete strategy% (12488)------------------------------
% 1.57/0.57  % (12488)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.57  % (12488)Termination reason: Refutation not found, incomplete strategy
% 1.57/0.57  
% 1.57/0.57  % (12488)Memory used [KB]: 10746
% 1.57/0.57  % (12488)Time elapsed: 0.159 s
% 1.57/0.57  % (12488)------------------------------
% 1.57/0.57  % (12488)------------------------------
% 1.57/0.57  fof(f13,plain,(
% 1.57/0.57    ? [X0,X1,X2,X3] : ((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 1.57/0.57    inference(flattening,[],[f12])).
% 1.57/0.57  fof(f12,plain,(
% 1.57/0.57    ? [X0,X1,X2,X3] : (((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1)) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 1.57/0.57    inference(ennf_transformation,[],[f10])).
% 1.57/0.57  fof(f10,negated_conjecture,(
% 1.57/0.57    ~! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 1.57/0.57    inference(negated_conjecture,[],[f9])).
% 1.57/0.57  fof(f9,conjecture,(
% 1.57/0.57    ! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 1.57/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_zfmisc_1)).
% 1.57/0.57  fof(f314,plain,(
% 1.57/0.57    ( ! [X0,X1] : (~r2_hidden(k4_tarski(sK6(sK0,sK2),X0),k2_zfmisc_1(sK2,X1))) ) | spl13_2),
% 1.57/0.57    inference(resolution,[],[f306,f37])).
% 1.57/0.57  fof(f37,plain,(
% 1.57/0.57    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 1.57/0.57    inference(cnf_transformation,[],[f8])).
% 1.57/0.57  fof(f306,plain,(
% 1.57/0.57    ~r2_hidden(sK6(sK0,sK2),sK2) | spl13_2),
% 1.57/0.57    inference(resolution,[],[f74,f28])).
% 1.57/0.57  fof(f28,plain,(
% 1.57/0.57    ( ! [X0,X1] : (~r2_hidden(sK6(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.57/0.57    inference(cnf_transformation,[],[f16])).
% 1.57/0.57  fof(f74,plain,(
% 1.57/0.57    ~r1_tarski(sK0,sK2) | spl13_2),
% 1.57/0.57    inference(avatar_component_clause,[],[f72])).
% 1.57/0.57  fof(f72,plain,(
% 1.57/0.57    spl13_2 <=> r1_tarski(sK0,sK2)),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl13_2])])).
% 1.57/0.57  fof(f305,plain,(
% 1.57/0.57    r2_hidden(sK6(sK0,sK2),sK0) | spl13_2),
% 1.57/0.57    inference(resolution,[],[f74,f27])).
% 1.57/0.57  fof(f27,plain,(
% 1.57/0.57    ( ! [X0,X1] : (r2_hidden(sK6(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.57/0.57    inference(cnf_transformation,[],[f16])).
% 1.57/0.57  fof(f90,plain,(
% 1.57/0.57    r2_hidden(sK9(sK0,sK1,sK4(k2_zfmisc_1(sK0,sK1))),sK1)),
% 1.57/0.57    inference(resolution,[],[f58,f43])).
% 1.57/0.57  fof(f43,plain,(
% 1.57/0.57    ( ! [X0,X3,X1] : (r2_hidden(sK9(X0,X1,X3),X1) | ~r2_hidden(X3,k2_zfmisc_1(X0,X1))) )),
% 1.57/0.57    inference(equality_resolution,[],[f34])).
% 1.57/0.57  fof(f34,plain,(
% 1.57/0.57    ( ! [X2,X0,X3,X1] : (r2_hidden(sK9(X0,X1,X3),X1) | ~r2_hidden(X3,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 1.57/0.57    inference(cnf_transformation,[],[f7])).
% 1.57/0.57  fof(f7,axiom,(
% 1.57/0.57    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 1.57/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).
% 1.57/0.57  fof(f58,plain,(
% 1.57/0.57    r2_hidden(sK4(k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))),
% 1.57/0.57    inference(resolution,[],[f47,f49])).
% 1.57/0.57  fof(f49,plain,(
% 1.57/0.57    ( ! [X0] : (sQ12_eqProxy(k1_xboole_0,X0) | r2_hidden(sK4(X0),X0)) )),
% 1.57/0.57    inference(equality_proxy_replacement,[],[f22,f45])).
% 1.57/0.57  fof(f45,plain,(
% 1.57/0.57    ! [X1,X0] : (sQ12_eqProxy(X0,X1) <=> X0 = X1)),
% 1.57/0.57    introduced(equality_proxy_definition,[new_symbols(naming,[sQ12_eqProxy])])).
% 1.57/0.57  fof(f22,plain,(
% 1.57/0.57    ( ! [X0] : (k1_xboole_0 = X0 | r2_hidden(sK4(X0),X0)) )),
% 1.57/0.57    inference(cnf_transformation,[],[f14])).
% 1.57/0.57  fof(f14,plain,(
% 1.57/0.57    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.57/0.57    inference(ennf_transformation,[],[f3])).
% 1.57/0.57  fof(f3,axiom,(
% 1.57/0.57    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.57/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 1.57/0.57  fof(f47,plain,(
% 1.57/0.57    ~sQ12_eqProxy(k1_xboole_0,k2_zfmisc_1(sK0,sK1))),
% 1.57/0.57    inference(equality_proxy_replacement,[],[f19,f45])).
% 1.57/0.57  fof(f19,plain,(
% 1.57/0.57    k1_xboole_0 != k2_zfmisc_1(sK0,sK1)),
% 1.57/0.57    inference(cnf_transformation,[],[f13])).
% 1.57/0.57  fof(f303,plain,(
% 1.57/0.57    spl13_1),
% 1.57/0.57    inference(avatar_contradiction_clause,[],[f285])).
% 1.57/0.57  fof(f285,plain,(
% 1.57/0.57    $false | spl13_1),
% 1.57/0.57    inference(unit_resulting_resolution,[],[f58,f281,f44])).
% 1.57/0.57  fof(f44,plain,(
% 1.57/0.57    ( ! [X0,X3,X1] : (r2_hidden(sK8(X0,X1,X3),X0) | ~r2_hidden(X3,k2_zfmisc_1(X0,X1))) )),
% 1.57/0.57    inference(equality_resolution,[],[f33])).
% 1.57/0.57  fof(f33,plain,(
% 1.57/0.57    ( ! [X2,X0,X3,X1] : (r2_hidden(sK8(X0,X1,X3),X0) | ~r2_hidden(X3,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 1.57/0.57    inference(cnf_transformation,[],[f7])).
% 1.57/0.57  fof(f281,plain,(
% 1.57/0.57    ( ! [X10] : (~r2_hidden(X10,sK0)) ) | spl13_1),
% 1.57/0.57    inference(subsumption_resolution,[],[f273,f87])).
% 1.57/0.57  fof(f87,plain,(
% 1.57/0.57    ( ! [X2,X3] : (~r2_hidden(k4_tarski(X2,sK6(sK1,sK3)),k2_zfmisc_1(X3,sK3))) ) | spl13_1),
% 1.57/0.57    inference(resolution,[],[f77,f38])).
% 1.57/0.57  fof(f38,plain,(
% 1.57/0.57    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,X3) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 1.57/0.57    inference(cnf_transformation,[],[f8])).
% 1.57/0.57  fof(f77,plain,(
% 1.57/0.57    ~r2_hidden(sK6(sK1,sK3),sK3) | spl13_1),
% 1.57/0.57    inference(resolution,[],[f70,f28])).
% 1.57/0.57  fof(f70,plain,(
% 1.57/0.57    ~r1_tarski(sK1,sK3) | spl13_1),
% 1.57/0.57    inference(avatar_component_clause,[],[f68])).
% 1.57/0.57  fof(f68,plain,(
% 1.57/0.57    spl13_1 <=> r1_tarski(sK1,sK3)),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl13_1])])).
% 1.57/0.57  fof(f273,plain,(
% 1.57/0.57    ( ! [X10] : (~r2_hidden(X10,sK0) | r2_hidden(k4_tarski(X10,sK6(sK1,sK3)),k2_zfmisc_1(sK2,sK3))) ) | spl13_1),
% 1.57/0.57    inference(resolution,[],[f81,f78])).
% 1.57/0.57  fof(f81,plain,(
% 1.57/0.57    ( ! [X4,X3] : (r2_hidden(k4_tarski(X3,sK6(sK1,sK3)),k2_zfmisc_1(X4,sK1)) | ~r2_hidden(X3,X4)) ) | spl13_1),
% 1.57/0.57    inference(resolution,[],[f76,f39])).
% 1.57/0.57  fof(f76,plain,(
% 1.57/0.57    r2_hidden(sK6(sK1,sK3),sK1) | spl13_1),
% 1.57/0.57    inference(resolution,[],[f70,f27])).
% 1.57/0.57  fof(f75,plain,(
% 1.57/0.57    ~spl13_1 | ~spl13_2),
% 1.57/0.57    inference(avatar_split_clause,[],[f17,f72,f68])).
% 1.57/0.57  fof(f17,plain,(
% 1.57/0.57    ~r1_tarski(sK0,sK2) | ~r1_tarski(sK1,sK3)),
% 1.57/0.57    inference(cnf_transformation,[],[f13])).
% 1.57/0.57  % SZS output end Proof for theBenchmark
% 1.57/0.57  % (12478)------------------------------
% 1.57/0.57  % (12478)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.57  % (12478)Termination reason: Refutation
% 1.57/0.57  
% 1.57/0.57  % (12478)Memory used [KB]: 6524
% 1.57/0.57  % (12478)Time elapsed: 0.102 s
% 1.57/0.57  % (12478)------------------------------
% 1.57/0.57  % (12478)------------------------------
% 1.57/0.57  % (12457)Success in time 0.21 s
%------------------------------------------------------------------------------
