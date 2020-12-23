%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:05 EST 2020

% Result     : Theorem 1.50s
% Output     : Refutation 1.50s
% Verified   : 
% Statistics : Number of formulae       :   34 (  85 expanded)
%              Number of leaves         :    3 (  20 expanded)
%              Depth                    :   11
%              Number of atoms          :   68 ( 217 expanded)
%              Number of equality atoms :    7 (  23 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f130,plain,(
    $false ),
    inference(global_subsumption,[],[f52,f129])).

% (31096)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
fof(f129,plain,(
    sP6(sK4(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)),sK3,sK1) ),
    inference(backward_demodulation,[],[f110,f124])).

fof(f124,plain,(
    sK4(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)) = k4_tarski(sK7(sK0,sK2,sK4(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))),sK8(sK0,sK2,sK4(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))) ),
    inference(unit_resulting_resolution,[],[f34,f17])).

fof(f17,plain,(
    ! [X0,X3,X1] :
      ( k4_tarski(sK7(X0,X1,X3),sK8(X0,X1,X3)) = X3
      | ~ sP6(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(f34,plain,(
    sP6(sK4(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)),sK2,sK0) ),
    inference(unit_resulting_resolution,[],[f25,f22])).

fof(f22,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k2_zfmisc_1(X0,X1))
      | sP6(X3,X1,X0) ) ),
    inference(equality_resolution,[],[f19])).

fof(f19,plain,(
    ! [X2,X0,X3,X1] :
      ( sP6(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f25,plain,(
    r2_hidden(sK4(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)),k2_zfmisc_1(sK0,sK2)) ),
    inference(unit_resulting_resolution,[],[f10,f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
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

fof(f10,plain,(
    ~ r1_tarski(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      & r1_tarski(X2,X3)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      & r1_tarski(X2,X3)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_tarski(X2,X3)
          & r1_tarski(X0,X1) )
       => r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    inference(negated_conjecture,[],[f3])).

% (31107)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
fof(f3,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t119_zfmisc_1)).

fof(f110,plain,(
    sP6(k4_tarski(sK7(sK0,sK2,sK4(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))),sK8(sK0,sK2,sK4(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),sK3,sK1) ),
    inference(unit_resulting_resolution,[],[f67,f79,f24])).

fof(f24,plain,(
    ! [X4,X0,X5,X1] :
      ( sP6(k4_tarski(X4,X5),X1,X0)
      | ~ r2_hidden(X5,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f14])).

fof(f14,plain,(
    ! [X4,X0,X5,X3,X1] :
      ( ~ r2_hidden(X4,X0)
      | ~ r2_hidden(X5,X1)
      | k4_tarski(X4,X5) != X3
      | sP6(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f79,plain,(
    r2_hidden(sK8(sK0,sK2,sK4(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))),sK3) ),
    inference(unit_resulting_resolution,[],[f9,f76,f11])).

fof(f11,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f76,plain,(
    r2_hidden(sK8(sK0,sK2,sK4(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))),sK2) ),
    inference(unit_resulting_resolution,[],[f34,f16])).

fof(f16,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(sK8(X0,X1,X3),X1)
      | ~ sP6(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f9,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f6])).

fof(f67,plain,(
    r2_hidden(sK7(sK0,sK2,sK4(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))),sK1) ),
    inference(unit_resulting_resolution,[],[f8,f64,f11])).

fof(f64,plain,(
    r2_hidden(sK7(sK0,sK2,sK4(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))),sK0) ),
    inference(unit_resulting_resolution,[],[f34,f15])).

fof(f15,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(sK7(X0,X1,X3),X0)
      | ~ sP6(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f8,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f6])).

fof(f52,plain,(
    ~ sP6(sK4(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)),sK3,sK1) ),
    inference(unit_resulting_resolution,[],[f26,f23])).

fof(f23,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k2_zfmisc_1(X0,X1))
      | ~ sP6(X3,X1,X0) ) ),
    inference(equality_resolution,[],[f18])).

fof(f18,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP6(X3,X1,X0)
      | r2_hidden(X3,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f26,plain,(
    ~ r2_hidden(sK4(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)),k2_zfmisc_1(sK1,sK3)) ),
    inference(unit_resulting_resolution,[],[f10,f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:40:09 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.49  % (31086)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.52  % (31101)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.53  % (31093)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.53  % (31094)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.38/0.53  % (31110)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.38/0.54  % (31090)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.38/0.54  % (31094)Refutation not found, incomplete strategy% (31094)------------------------------
% 1.38/0.54  % (31094)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.54  % (31094)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.54  
% 1.38/0.54  % (31094)Memory used [KB]: 10618
% 1.38/0.54  % (31094)Time elapsed: 0.113 s
% 1.38/0.54  % (31094)------------------------------
% 1.38/0.54  % (31094)------------------------------
% 1.38/0.54  % (31087)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.38/0.54  % (31102)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.38/0.54  % (31100)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.38/0.54  % (31114)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.38/0.54  % (31088)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.38/0.54  % (31099)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.38/0.54  % (31088)Refutation not found, incomplete strategy% (31088)------------------------------
% 1.38/0.54  % (31088)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.54  % (31088)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.54  
% 1.38/0.54  % (31088)Memory used [KB]: 10618
% 1.38/0.54  % (31088)Time elapsed: 0.129 s
% 1.38/0.54  % (31088)------------------------------
% 1.38/0.54  % (31088)------------------------------
% 1.38/0.54  % (31104)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.50/0.55  % (31110)Refutation found. Thanks to Tanya!
% 1.50/0.55  % SZS status Theorem for theBenchmark
% 1.50/0.55  % SZS output start Proof for theBenchmark
% 1.50/0.55  fof(f130,plain,(
% 1.50/0.55    $false),
% 1.50/0.55    inference(global_subsumption,[],[f52,f129])).
% 1.50/0.55  % (31096)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.50/0.55  fof(f129,plain,(
% 1.50/0.55    sP6(sK4(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)),sK3,sK1)),
% 1.50/0.55    inference(backward_demodulation,[],[f110,f124])).
% 1.50/0.55  fof(f124,plain,(
% 1.50/0.55    sK4(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)) = k4_tarski(sK7(sK0,sK2,sK4(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))),sK8(sK0,sK2,sK4(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))))),
% 1.50/0.55    inference(unit_resulting_resolution,[],[f34,f17])).
% 1.50/0.55  fof(f17,plain,(
% 1.50/0.55    ( ! [X0,X3,X1] : (k4_tarski(sK7(X0,X1,X3),sK8(X0,X1,X3)) = X3 | ~sP6(X3,X1,X0)) )),
% 1.50/0.55    inference(cnf_transformation,[],[f2])).
% 1.50/0.55  fof(f2,axiom,(
% 1.50/0.55    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 1.50/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).
% 1.50/0.55  fof(f34,plain,(
% 1.50/0.55    sP6(sK4(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)),sK2,sK0)),
% 1.50/0.55    inference(unit_resulting_resolution,[],[f25,f22])).
% 1.50/0.55  fof(f22,plain,(
% 1.50/0.55    ( ! [X0,X3,X1] : (~r2_hidden(X3,k2_zfmisc_1(X0,X1)) | sP6(X3,X1,X0)) )),
% 1.50/0.55    inference(equality_resolution,[],[f19])).
% 1.50/0.55  fof(f19,plain,(
% 1.50/0.55    ( ! [X2,X0,X3,X1] : (sP6(X3,X1,X0) | ~r2_hidden(X3,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 1.50/0.55    inference(cnf_transformation,[],[f2])).
% 1.50/0.55  fof(f25,plain,(
% 1.50/0.55    r2_hidden(sK4(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)),k2_zfmisc_1(sK0,sK2))),
% 1.50/0.55    inference(unit_resulting_resolution,[],[f10,f12])).
% 1.50/0.55  fof(f12,plain,(
% 1.50/0.55    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.50/0.55    inference(cnf_transformation,[],[f7])).
% 1.50/0.55  fof(f7,plain,(
% 1.50/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.50/0.55    inference(ennf_transformation,[],[f1])).
% 1.50/0.55  fof(f1,axiom,(
% 1.50/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.50/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.50/0.55  fof(f10,plain,(
% 1.50/0.55    ~r1_tarski(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))),
% 1.50/0.55    inference(cnf_transformation,[],[f6])).
% 1.50/0.55  fof(f6,plain,(
% 1.50/0.55    ? [X0,X1,X2,X3] : (~r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) & r1_tarski(X2,X3) & r1_tarski(X0,X1))),
% 1.50/0.55    inference(flattening,[],[f5])).
% 1.50/0.55  fof(f5,plain,(
% 1.50/0.55    ? [X0,X1,X2,X3] : (~r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) & (r1_tarski(X2,X3) & r1_tarski(X0,X1)))),
% 1.50/0.55    inference(ennf_transformation,[],[f4])).
% 1.50/0.55  fof(f4,negated_conjecture,(
% 1.50/0.55    ~! [X0,X1,X2,X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))),
% 1.50/0.55    inference(negated_conjecture,[],[f3])).
% 1.50/0.55  % (31107)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.50/0.55  fof(f3,conjecture,(
% 1.50/0.55    ! [X0,X1,X2,X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))),
% 1.50/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t119_zfmisc_1)).
% 1.50/0.55  fof(f110,plain,(
% 1.50/0.55    sP6(k4_tarski(sK7(sK0,sK2,sK4(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))),sK8(sK0,sK2,sK4(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),sK3,sK1)),
% 1.50/0.55    inference(unit_resulting_resolution,[],[f67,f79,f24])).
% 1.50/0.55  fof(f24,plain,(
% 1.50/0.55    ( ! [X4,X0,X5,X1] : (sP6(k4_tarski(X4,X5),X1,X0) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) )),
% 1.50/0.55    inference(equality_resolution,[],[f14])).
% 1.50/0.55  fof(f14,plain,(
% 1.50/0.55    ( ! [X4,X0,X5,X3,X1] : (~r2_hidden(X4,X0) | ~r2_hidden(X5,X1) | k4_tarski(X4,X5) != X3 | sP6(X3,X1,X0)) )),
% 1.50/0.55    inference(cnf_transformation,[],[f2])).
% 1.50/0.55  fof(f79,plain,(
% 1.50/0.55    r2_hidden(sK8(sK0,sK2,sK4(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))),sK3)),
% 1.50/0.55    inference(unit_resulting_resolution,[],[f9,f76,f11])).
% 1.50/0.55  fof(f11,plain,(
% 1.50/0.55    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 1.50/0.55    inference(cnf_transformation,[],[f7])).
% 1.50/0.55  fof(f76,plain,(
% 1.50/0.55    r2_hidden(sK8(sK0,sK2,sK4(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))),sK2)),
% 1.50/0.55    inference(unit_resulting_resolution,[],[f34,f16])).
% 1.50/0.55  fof(f16,plain,(
% 1.50/0.55    ( ! [X0,X3,X1] : (r2_hidden(sK8(X0,X1,X3),X1) | ~sP6(X3,X1,X0)) )),
% 1.50/0.55    inference(cnf_transformation,[],[f2])).
% 1.50/0.55  fof(f9,plain,(
% 1.50/0.55    r1_tarski(sK2,sK3)),
% 1.50/0.55    inference(cnf_transformation,[],[f6])).
% 1.50/0.55  fof(f67,plain,(
% 1.50/0.55    r2_hidden(sK7(sK0,sK2,sK4(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))),sK1)),
% 1.50/0.55    inference(unit_resulting_resolution,[],[f8,f64,f11])).
% 1.50/0.55  fof(f64,plain,(
% 1.50/0.55    r2_hidden(sK7(sK0,sK2,sK4(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))),sK0)),
% 1.50/0.55    inference(unit_resulting_resolution,[],[f34,f15])).
% 1.50/0.55  fof(f15,plain,(
% 1.50/0.55    ( ! [X0,X3,X1] : (r2_hidden(sK7(X0,X1,X3),X0) | ~sP6(X3,X1,X0)) )),
% 1.50/0.55    inference(cnf_transformation,[],[f2])).
% 1.50/0.55  fof(f8,plain,(
% 1.50/0.55    r1_tarski(sK0,sK1)),
% 1.50/0.55    inference(cnf_transformation,[],[f6])).
% 1.50/0.55  fof(f52,plain,(
% 1.50/0.55    ~sP6(sK4(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)),sK3,sK1)),
% 1.50/0.55    inference(unit_resulting_resolution,[],[f26,f23])).
% 1.50/0.55  fof(f23,plain,(
% 1.50/0.55    ( ! [X0,X3,X1] : (r2_hidden(X3,k2_zfmisc_1(X0,X1)) | ~sP6(X3,X1,X0)) )),
% 1.50/0.55    inference(equality_resolution,[],[f18])).
% 1.50/0.55  fof(f18,plain,(
% 1.50/0.55    ( ! [X2,X0,X3,X1] : (~sP6(X3,X1,X0) | r2_hidden(X3,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 1.50/0.55    inference(cnf_transformation,[],[f2])).
% 1.50/0.55  fof(f26,plain,(
% 1.50/0.55    ~r2_hidden(sK4(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)),k2_zfmisc_1(sK1,sK3))),
% 1.50/0.55    inference(unit_resulting_resolution,[],[f10,f13])).
% 1.50/0.55  fof(f13,plain,(
% 1.50/0.55    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.50/0.55    inference(cnf_transformation,[],[f7])).
% 1.50/0.55  % SZS output end Proof for theBenchmark
% 1.50/0.55  % (31110)------------------------------
% 1.50/0.55  % (31110)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.55  % (31110)Termination reason: Refutation
% 1.50/0.55  
% 1.50/0.55  % (31110)Memory used [KB]: 6396
% 1.50/0.55  % (31110)Time elapsed: 0.129 s
% 1.50/0.55  % (31110)------------------------------
% 1.50/0.55  % (31110)------------------------------
% 1.50/0.55  % (31108)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.50/0.55  % (31095)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.50/0.55  % (31085)Success in time 0.19 s
%------------------------------------------------------------------------------
