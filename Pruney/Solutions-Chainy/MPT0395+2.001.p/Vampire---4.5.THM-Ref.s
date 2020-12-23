%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:03 EST 2020

% Result     : Theorem 1.45s
% Output     : Refutation 1.45s
% Verified   : 
% Statistics : Number of formulae       :   46 ( 124 expanded)
%              Number of leaves         :    7 (  32 expanded)
%              Depth                    :   10
%              Number of atoms          :   92 ( 252 expanded)
%              Number of equality atoms :   13 (  33 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f812,plain,(
    $false ),
    inference(subsumption_resolution,[],[f768,f333])).

fof(f333,plain,(
    ! [X19,X18] : ~ r2_hidden(X19,k4_xboole_0(X18,X18)) ),
    inference(subsumption_resolution,[],[f309,f308])).

fof(f308,plain,(
    ! [X14,X15,X16] :
      ( ~ r2_hidden(X16,k4_xboole_0(X15,X15))
      | ~ r2_hidden(X16,X14) ) ),
    inference(superposition,[],[f41,f140])).

fof(f140,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X0) = k4_xboole_0(X1,X1) ),
    inference(unit_resulting_resolution,[],[f129,f129,f26])).

fof(f26,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f129,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X0),X1) ),
    inference(unit_resulting_resolution,[],[f51,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f51,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(unit_resulting_resolution,[],[f38,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f38,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f41,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f309,plain,(
    ! [X19,X17,X18] :
      ( ~ r2_hidden(X19,k4_xboole_0(X18,X18))
      | r2_hidden(X19,X17) ) ),
    inference(superposition,[],[f42,f140])).

fof(f42,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k4_xboole_0(X0,X1))
      | r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f768,plain,(
    ! [X0] : r2_hidden(sK2(sK0,sK1),k4_xboole_0(X0,X0)) ),
    inference(superposition,[],[f216,f150])).

fof(f150,plain,(
    ! [X0] : k4_xboole_0(sK0,sK1) = k4_xboole_0(X0,X0) ),
    inference(unit_resulting_resolution,[],[f129,f126,f26])).

fof(f126,plain,(
    ! [X0] : r1_tarski(k4_xboole_0(sK0,sK1),X0) ),
    inference(unit_resulting_resolution,[],[f76,f29])).

fof(f76,plain,(
    ! [X0] : r1_tarski(sK0,k2_xboole_0(sK1,X0)) ),
    inference(unit_resulting_resolution,[],[f51,f56])).

fof(f56,plain,(
    ! [X11] :
      ( ~ r1_tarski(sK1,X11)
      | r1_tarski(sK0,X11) ) ),
    inference(superposition,[],[f31,f43])).

fof(f43,plain,(
    sK1 = k2_xboole_0(sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f19,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f19,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ~ r1_setfam_1(X0,X1)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(X0,X1)
       => r1_setfam_1(X0,X1) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_setfam_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_setfam_1)).

fof(f216,plain,(
    r2_hidden(sK2(sK0,sK1),k4_xboole_0(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f50,f201,f40])).

fof(f40,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k4_xboole_0(X0,X1))
      | r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f201,plain,(
    ~ r2_hidden(sK2(sK0,sK1),sK1) ),
    inference(unit_resulting_resolution,[],[f20,f38,f27])).

fof(f27,plain,(
    ! [X0,X3,X1] :
      ( ~ r1_tarski(sK2(X0,X1),X3)
      | ~ r2_hidden(X3,X1)
      | r1_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
      | ? [X2] :
          ( ! [X3] :
              ( ~ r1_tarski(X2,X3)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ~ ( ! [X3] :
                ~ ( r1_tarski(X2,X3)
                  & r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) )
     => r1_setfam_1(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
    <=> ! [X2] :
          ~ ( ! [X3] :
                ~ ( r1_tarski(X2,X3)
                  & r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_setfam_1)).

fof(f20,plain,(
    ~ r1_setfam_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f50,plain,(
    r2_hidden(sK2(sK0,sK1),sK0) ),
    inference(unit_resulting_resolution,[],[f20,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:38:29 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.23/0.48  % (8449)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.23/0.50  % (8457)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.23/0.50  % (8460)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.23/0.50  % (8466)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.23/0.51  % (8468)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.23/0.51  % (8448)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.23/0.51  % (8464)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.23/0.51  % (8465)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.23/0.51  % (8452)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.23/0.51  % (8451)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.23/0.51  % (8452)Refutation not found, incomplete strategy% (8452)------------------------------
% 0.23/0.51  % (8452)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.51  % (8452)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.51  
% 0.23/0.51  % (8452)Memory used [KB]: 10490
% 0.23/0.51  % (8452)Time elapsed: 0.097 s
% 0.23/0.51  % (8452)------------------------------
% 0.23/0.51  % (8452)------------------------------
% 0.23/0.51  % (8461)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.23/0.52  % (8446)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.23/0.52  % (8469)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.23/0.52  % (8450)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.23/0.52  % (8456)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.23/0.52  % (8447)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.23/0.52  % (8453)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.23/0.53  % (8462)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.23/0.53  % (8472)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.23/0.53  % (8467)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.23/0.53  % (8454)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.23/0.53  % (8459)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.23/0.54  % (8455)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.23/0.54  % (8471)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.23/0.54  % (8470)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.23/0.56  % (8463)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.45/0.57  % (8453)Refutation found. Thanks to Tanya!
% 1.45/0.57  % SZS status Theorem for theBenchmark
% 1.45/0.57  % SZS output start Proof for theBenchmark
% 1.45/0.57  fof(f812,plain,(
% 1.45/0.57    $false),
% 1.45/0.57    inference(subsumption_resolution,[],[f768,f333])).
% 1.45/0.57  fof(f333,plain,(
% 1.45/0.57    ( ! [X19,X18] : (~r2_hidden(X19,k4_xboole_0(X18,X18))) )),
% 1.45/0.57    inference(subsumption_resolution,[],[f309,f308])).
% 1.45/0.57  fof(f308,plain,(
% 1.45/0.57    ( ! [X14,X15,X16] : (~r2_hidden(X16,k4_xboole_0(X15,X15)) | ~r2_hidden(X16,X14)) )),
% 1.45/0.57    inference(superposition,[],[f41,f140])).
% 1.45/0.57  fof(f140,plain,(
% 1.45/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X0) = k4_xboole_0(X1,X1)) )),
% 1.45/0.57    inference(unit_resulting_resolution,[],[f129,f129,f26])).
% 1.45/0.57  fof(f26,plain,(
% 1.45/0.57    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 1.45/0.57    inference(cnf_transformation,[],[f3])).
% 1.45/0.57  fof(f3,axiom,(
% 1.45/0.57    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.45/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.45/0.57  fof(f129,plain,(
% 1.45/0.57    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X0),X1)) )),
% 1.45/0.57    inference(unit_resulting_resolution,[],[f51,f29])).
% 1.45/0.57  fof(f29,plain,(
% 1.45/0.57    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 1.45/0.57    inference(cnf_transformation,[],[f16])).
% 1.45/0.57  fof(f16,plain,(
% 1.45/0.57    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 1.45/0.57    inference(ennf_transformation,[],[f7])).
% 1.45/0.57  fof(f7,axiom,(
% 1.45/0.57    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 1.45/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).
% 1.45/0.57  fof(f51,plain,(
% 1.45/0.57    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.45/0.57    inference(unit_resulting_resolution,[],[f38,f31])).
% 1.45/0.57  fof(f31,plain,(
% 1.45/0.57    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 1.45/0.57    inference(cnf_transformation,[],[f18])).
% 1.45/0.57  fof(f18,plain,(
% 1.45/0.57    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 1.45/0.57    inference(ennf_transformation,[],[f4])).
% 1.45/0.57  fof(f4,axiom,(
% 1.45/0.57    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 1.45/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).
% 1.45/0.57  fof(f38,plain,(
% 1.45/0.57    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.45/0.57    inference(equality_resolution,[],[f25])).
% 1.45/0.57  fof(f25,plain,(
% 1.45/0.57    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.45/0.57    inference(cnf_transformation,[],[f3])).
% 1.45/0.57  fof(f41,plain,(
% 1.45/0.57    ( ! [X0,X3,X1] : (~r2_hidden(X3,k4_xboole_0(X0,X1)) | ~r2_hidden(X3,X1)) )),
% 1.45/0.57    inference(equality_resolution,[],[f36])).
% 1.45/0.57  fof(f36,plain,(
% 1.45/0.57    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.45/0.57    inference(cnf_transformation,[],[f2])).
% 1.45/0.57  fof(f2,axiom,(
% 1.45/0.57    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.45/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.45/0.57  fof(f309,plain,(
% 1.45/0.57    ( ! [X19,X17,X18] : (~r2_hidden(X19,k4_xboole_0(X18,X18)) | r2_hidden(X19,X17)) )),
% 1.45/0.57    inference(superposition,[],[f42,f140])).
% 1.45/0.57  fof(f42,plain,(
% 1.45/0.57    ( ! [X0,X3,X1] : (~r2_hidden(X3,k4_xboole_0(X0,X1)) | r2_hidden(X3,X0)) )),
% 1.45/0.57    inference(equality_resolution,[],[f35])).
% 1.45/0.57  fof(f35,plain,(
% 1.45/0.57    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.45/0.57    inference(cnf_transformation,[],[f2])).
% 1.45/0.57  fof(f768,plain,(
% 1.45/0.57    ( ! [X0] : (r2_hidden(sK2(sK0,sK1),k4_xboole_0(X0,X0))) )),
% 1.45/0.57    inference(superposition,[],[f216,f150])).
% 1.45/0.57  fof(f150,plain,(
% 1.45/0.57    ( ! [X0] : (k4_xboole_0(sK0,sK1) = k4_xboole_0(X0,X0)) )),
% 1.45/0.57    inference(unit_resulting_resolution,[],[f129,f126,f26])).
% 1.45/0.57  fof(f126,plain,(
% 1.45/0.57    ( ! [X0] : (r1_tarski(k4_xboole_0(sK0,sK1),X0)) )),
% 1.45/0.57    inference(unit_resulting_resolution,[],[f76,f29])).
% 1.45/0.57  fof(f76,plain,(
% 1.45/0.57    ( ! [X0] : (r1_tarski(sK0,k2_xboole_0(sK1,X0))) )),
% 1.45/0.57    inference(unit_resulting_resolution,[],[f51,f56])).
% 1.45/0.57  fof(f56,plain,(
% 1.45/0.57    ( ! [X11] : (~r1_tarski(sK1,X11) | r1_tarski(sK0,X11)) )),
% 1.45/0.57    inference(superposition,[],[f31,f43])).
% 1.45/0.57  fof(f43,plain,(
% 1.45/0.57    sK1 = k2_xboole_0(sK0,sK1)),
% 1.45/0.57    inference(unit_resulting_resolution,[],[f19,f23])).
% 1.45/0.57  fof(f23,plain,(
% 1.45/0.57    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 1.45/0.57    inference(cnf_transformation,[],[f14])).
% 1.45/0.57  fof(f14,plain,(
% 1.45/0.57    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.45/0.57    inference(ennf_transformation,[],[f5])).
% 1.45/0.57  fof(f5,axiom,(
% 1.45/0.57    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.45/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.45/0.57  fof(f19,plain,(
% 1.45/0.57    r1_tarski(sK0,sK1)),
% 1.45/0.57    inference(cnf_transformation,[],[f13])).
% 1.45/0.57  fof(f13,plain,(
% 1.45/0.57    ? [X0,X1] : (~r1_setfam_1(X0,X1) & r1_tarski(X0,X1))),
% 1.45/0.57    inference(ennf_transformation,[],[f11])).
% 1.45/0.57  fof(f11,negated_conjecture,(
% 1.45/0.57    ~! [X0,X1] : (r1_tarski(X0,X1) => r1_setfam_1(X0,X1))),
% 1.45/0.57    inference(negated_conjecture,[],[f10])).
% 1.45/0.57  fof(f10,conjecture,(
% 1.45/0.57    ! [X0,X1] : (r1_tarski(X0,X1) => r1_setfam_1(X0,X1))),
% 1.45/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_setfam_1)).
% 1.45/0.57  fof(f216,plain,(
% 1.45/0.57    r2_hidden(sK2(sK0,sK1),k4_xboole_0(sK0,sK1))),
% 1.45/0.57    inference(unit_resulting_resolution,[],[f50,f201,f40])).
% 1.45/0.57  fof(f40,plain,(
% 1.45/0.57    ( ! [X0,X3,X1] : (r2_hidden(X3,k4_xboole_0(X0,X1)) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) )),
% 1.45/0.57    inference(equality_resolution,[],[f37])).
% 1.45/0.57  fof(f37,plain,(
% 1.45/0.57    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.45/0.57    inference(cnf_transformation,[],[f2])).
% 1.45/0.57  fof(f201,plain,(
% 1.45/0.57    ~r2_hidden(sK2(sK0,sK1),sK1)),
% 1.45/0.57    inference(unit_resulting_resolution,[],[f20,f38,f27])).
% 1.45/0.57  fof(f27,plain,(
% 1.45/0.57    ( ! [X0,X3,X1] : (~r1_tarski(sK2(X0,X1),X3) | ~r2_hidden(X3,X1) | r1_setfam_1(X0,X1)) )),
% 1.45/0.57    inference(cnf_transformation,[],[f15])).
% 1.45/0.57  fof(f15,plain,(
% 1.45/0.57    ! [X0,X1] : (r1_setfam_1(X0,X1) | ? [X2] : (! [X3] : (~r1_tarski(X2,X3) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X0)))),
% 1.45/0.57    inference(ennf_transformation,[],[f12])).
% 1.45/0.57  fof(f12,plain,(
% 1.45/0.57    ! [X0,X1] : (! [X2] : ~(! [X3] : ~(r1_tarski(X2,X3) & r2_hidden(X3,X1)) & r2_hidden(X2,X0)) => r1_setfam_1(X0,X1))),
% 1.45/0.57    inference(unused_predicate_definition_removal,[],[f9])).
% 1.45/0.57  fof(f9,axiom,(
% 1.45/0.57    ! [X0,X1] : (r1_setfam_1(X0,X1) <=> ! [X2] : ~(! [X3] : ~(r1_tarski(X2,X3) & r2_hidden(X3,X1)) & r2_hidden(X2,X0)))),
% 1.45/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_setfam_1)).
% 1.45/0.57  fof(f20,plain,(
% 1.45/0.57    ~r1_setfam_1(sK0,sK1)),
% 1.45/0.57    inference(cnf_transformation,[],[f13])).
% 1.45/0.57  fof(f50,plain,(
% 1.45/0.57    r2_hidden(sK2(sK0,sK1),sK0)),
% 1.45/0.57    inference(unit_resulting_resolution,[],[f20,f28])).
% 1.45/0.57  fof(f28,plain,(
% 1.45/0.57    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_setfam_1(X0,X1)) )),
% 1.45/0.57    inference(cnf_transformation,[],[f15])).
% 1.45/0.57  % SZS output end Proof for theBenchmark
% 1.45/0.57  % (8453)------------------------------
% 1.45/0.57  % (8453)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.57  % (8453)Termination reason: Refutation
% 1.45/0.57  
% 1.45/0.57  % (8453)Memory used [KB]: 2046
% 1.45/0.57  % (8453)Time elapsed: 0.117 s
% 1.45/0.57  % (8453)------------------------------
% 1.45/0.57  % (8453)------------------------------
% 1.45/0.57  % (8445)Success in time 0.204 s
%------------------------------------------------------------------------------
