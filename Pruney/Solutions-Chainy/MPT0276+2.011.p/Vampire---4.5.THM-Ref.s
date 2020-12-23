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
% DateTime   : Thu Dec  3 12:41:30 EST 2020

% Result     : Theorem 2.15s
% Output     : Refutation 2.15s
% Verified   : 
% Statistics : Number of formulae       :   46 ( 160 expanded)
%              Number of leaves         :    6 (  44 expanded)
%              Depth                    :   13
%              Number of atoms          :   93 ( 409 expanded)
%              Number of equality atoms :   54 ( 305 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1702,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1638,f540])).

fof(f540,plain,(
    ! [X0] : ~ r2_hidden(sK1,k4_xboole_0(X0,sK2)) ),
    inference(unit_resulting_resolution,[],[f506,f44])).

fof(f44,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k4_xboole_0(X0,X1))
      | sP7(X3,X1,X0) ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( sP7(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f506,plain,(
    ! [X0] : ~ sP7(sK1,sK2,X0) ),
    inference(unit_resulting_resolution,[],[f489,f31])).

fof(f31,plain,(
    ! [X0,X3,X1] :
      ( ~ sP7(X3,X1,X0)
      | ~ r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f489,plain,(
    r2_hidden(sK1,sK2) ),
    inference(unit_resulting_resolution,[],[f15,f437,f21])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | r2_hidden(X1,X2)
      | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_zfmisc_1)).

fof(f437,plain,(
    ~ r2_hidden(sK0,sK2) ),
    inference(backward_demodulation,[],[f368,f411])).

fof(f411,plain,(
    sK0 = sK3(k4_xboole_0(k2_tarski(sK0,sK1),sK2),sK1) ),
    inference(unit_resulting_resolution,[],[f106,f369,f91])).

fof(f91,plain,(
    ! [X6,X4,X5] :
      ( ~ r2_hidden(X5,k2_tarski(X6,X4))
      | X5 = X6
      | X4 = X5 ) ),
    inference(resolution,[],[f24,f40])).

fof(f40,plain,(
    ! [X0,X3,X1] :
      ( sP5(X3,X1,X0)
      | ~ r2_hidden(X3,k2_tarski(X0,X1)) ) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] :
      ( sP5(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f24,plain,(
    ! [X0,X3,X1] :
      ( ~ sP5(X3,X1,X0)
      | X1 = X3
      | X0 = X3 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f369,plain,(
    r2_hidden(sK3(k4_xboole_0(k2_tarski(sK0,sK1),sK2),sK1),k2_tarski(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f216,f30])).

fof(f30,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ sP7(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f216,plain,(
    sP7(sK3(k4_xboole_0(k2_tarski(sK0,sK1),sK2),sK1),sK2,k2_tarski(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f116,f44])).

fof(f116,plain,(
    r2_hidden(sK3(k4_xboole_0(k2_tarski(sK0,sK1),sK2),sK1),k4_xboole_0(k2_tarski(sK0,sK1),sK2)) ),
    inference(unit_resulting_resolution,[],[f12,f36,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | k1_xboole_0 = X0
      | k2_tarski(X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f16,f18])).

fof(f18,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f16,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( X1 != X2
              & r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_zfmisc_1)).

fof(f36,plain,(
    k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k2_tarski(sK1,sK1) ),
    inference(definition_unfolding,[],[f14,f18])).

fof(f14,plain,(
    k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)
      & k1_tarski(X1) != k4_xboole_0(k2_tarski(X0,X1),X2)
      & k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2)
      & k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)
          & k1_tarski(X1) != k4_xboole_0(k2_tarski(X0,X1),X2)
          & k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2)
          & k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ~ ( k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)
        & k1_tarski(X1) != k4_xboole_0(k2_tarski(X0,X1),X2)
        & k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2)
        & k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_zfmisc_1)).

% (11352)Refutation not found, incomplete strategy% (11352)------------------------------
% (11352)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (11352)Termination reason: Refutation not found, incomplete strategy

% (11352)Memory used [KB]: 6140
% (11352)Time elapsed: 0.255 s
% (11352)------------------------------
% (11352)------------------------------
fof(f12,plain,(
    k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f106,plain,(
    sK1 != sK3(k4_xboole_0(k2_tarski(sK0,sK1),sK2),sK1) ),
    inference(unit_resulting_resolution,[],[f12,f36,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( sK3(X0,X1) != X1
      | k1_xboole_0 = X0
      | k2_tarski(X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f17,f18])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | sK3(X0,X1) != X1 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f368,plain,(
    ~ r2_hidden(sK3(k4_xboole_0(k2_tarski(sK0,sK1),sK2),sK1),sK2) ),
    inference(unit_resulting_resolution,[],[f216,f31])).

fof(f15,plain,(
    k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f1638,plain,(
    r2_hidden(sK1,k4_xboole_0(k2_tarski(sK0,sK1),sK2)) ),
    inference(backward_demodulation,[],[f117,f1627])).

fof(f1627,plain,(
    sK1 = sK3(k4_xboole_0(k2_tarski(sK0,sK1),sK2),sK0) ),
    inference(unit_resulting_resolution,[],[f107,f232,f330])).

fof(f330,plain,(
    ! [X17,X15,X18,X16] :
      ( ~ sP7(X15,X18,k2_tarski(X16,X17))
      | X15 = X17
      | X15 = X16 ) ),
    inference(resolution,[],[f91,f30])).

fof(f232,plain,(
    sP7(sK3(k4_xboole_0(k2_tarski(sK0,sK1),sK2),sK0),sK2,k2_tarski(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f117,f44])).

fof(f107,plain,(
    sK0 != sK3(k4_xboole_0(k2_tarski(sK0,sK1),sK2),sK0) ),
    inference(unit_resulting_resolution,[],[f12,f37,f38])).

fof(f37,plain,(
    k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k2_tarski(sK0,sK0) ),
    inference(definition_unfolding,[],[f13,f18])).

fof(f13,plain,(
    k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f117,plain,(
    r2_hidden(sK3(k4_xboole_0(k2_tarski(sK0,sK1),sK2),sK0),k4_xboole_0(k2_tarski(sK0,sK1),sK2)) ),
    inference(unit_resulting_resolution,[],[f12,f37,f39])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:24:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.52  % (11375)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.52  % (11367)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.52  % (11359)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.53  % (11361)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.53  % (11362)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.53  % (11367)Refutation not found, incomplete strategy% (11367)------------------------------
% 0.21/0.53  % (11367)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (11349)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.53  % (11355)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (11367)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (11367)Memory used [KB]: 1663
% 0.21/0.53  % (11367)Time elapsed: 0.107 s
% 0.21/0.53  % (11367)------------------------------
% 0.21/0.53  % (11367)------------------------------
% 0.21/0.53  % (11375)Refutation not found, incomplete strategy% (11375)------------------------------
% 0.21/0.53  % (11375)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (11375)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (11375)Memory used [KB]: 6140
% 0.21/0.53  % (11375)Time elapsed: 0.114 s
% 0.21/0.53  % (11375)------------------------------
% 0.21/0.53  % (11375)------------------------------
% 0.21/0.54  % (11356)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.54  % (11364)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.54  % (11354)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.54  % (11373)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.54  % (11353)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.55  % (11350)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.55  % (11351)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.55  % (11371)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.55  % (11374)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.55  % (11350)Refutation not found, incomplete strategy% (11350)------------------------------
% 0.21/0.55  % (11350)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (11350)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (11350)Memory used [KB]: 1663
% 0.21/0.55  % (11350)Time elapsed: 0.124 s
% 0.21/0.55  % (11350)------------------------------
% 0.21/0.55  % (11350)------------------------------
% 0.21/0.55  % (11372)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.55  % (11368)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.55  % (11357)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.55  % (11369)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.45/0.56  % (11370)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.45/0.56  % (11366)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.45/0.56  % (11366)Refutation not found, incomplete strategy% (11366)------------------------------
% 1.45/0.56  % (11366)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.56  % (11366)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.56  
% 1.45/0.56  % (11366)Memory used [KB]: 1663
% 1.45/0.56  % (11366)Time elapsed: 0.136 s
% 1.45/0.56  % (11366)------------------------------
% 1.45/0.56  % (11366)------------------------------
% 1.45/0.56  % (11365)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.45/0.56  % (11378)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.45/0.56  % (11377)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.45/0.56  % (11358)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.45/0.56  % (11363)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.45/0.56  % (11363)Refutation not found, incomplete strategy% (11363)------------------------------
% 1.45/0.56  % (11363)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.56  % (11363)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.56  
% 1.45/0.56  % (11363)Memory used [KB]: 1663
% 1.45/0.56  % (11363)Time elapsed: 0.150 s
% 1.45/0.56  % (11363)------------------------------
% 1.45/0.56  % (11363)------------------------------
% 1.45/0.57  % (11373)Refutation not found, incomplete strategy% (11373)------------------------------
% 1.45/0.57  % (11373)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.57  % (11373)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.57  
% 1.45/0.57  % (11373)Memory used [KB]: 10618
% 1.45/0.57  % (11373)Time elapsed: 0.148 s
% 1.45/0.57  % (11373)------------------------------
% 1.45/0.57  % (11373)------------------------------
% 1.45/0.57  % (11352)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.45/0.57  % (11365)Refutation not found, incomplete strategy% (11365)------------------------------
% 1.45/0.57  % (11365)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.57  % (11365)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.57  
% 1.45/0.57  % (11365)Memory used [KB]: 10618
% 1.45/0.57  % (11365)Time elapsed: 0.145 s
% 1.45/0.57  % (11365)------------------------------
% 1.45/0.57  % (11365)------------------------------
% 1.63/0.58  % (11376)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.63/0.59  % (11360)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.63/0.59  % (11376)Refutation not found, incomplete strategy% (11376)------------------------------
% 1.63/0.59  % (11376)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.63/0.59  % (11376)Termination reason: Refutation not found, incomplete strategy
% 1.63/0.59  
% 1.63/0.59  % (11376)Memory used [KB]: 6140
% 1.63/0.59  % (11376)Time elapsed: 0.140 s
% 1.63/0.59  % (11376)------------------------------
% 1.63/0.59  % (11376)------------------------------
% 2.15/0.70  % (11383)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.15/0.70  % (11368)Refutation found. Thanks to Tanya!
% 2.15/0.70  % SZS status Theorem for theBenchmark
% 2.15/0.70  % SZS output start Proof for theBenchmark
% 2.15/0.70  fof(f1702,plain,(
% 2.15/0.70    $false),
% 2.15/0.70    inference(subsumption_resolution,[],[f1638,f540])).
% 2.15/0.70  fof(f540,plain,(
% 2.15/0.70    ( ! [X0] : (~r2_hidden(sK1,k4_xboole_0(X0,sK2))) )),
% 2.15/0.70    inference(unit_resulting_resolution,[],[f506,f44])).
% 2.15/0.70  fof(f44,plain,(
% 2.15/0.70    ( ! [X0,X3,X1] : (~r2_hidden(X3,k4_xboole_0(X0,X1)) | sP7(X3,X1,X0)) )),
% 2.15/0.70    inference(equality_resolution,[],[f33])).
% 2.15/0.70  fof(f33,plain,(
% 2.15/0.70    ( ! [X2,X0,X3,X1] : (sP7(X3,X1,X0) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.15/0.70    inference(cnf_transformation,[],[f1])).
% 2.15/0.70  fof(f1,axiom,(
% 2.15/0.70    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.15/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 2.15/0.70  fof(f506,plain,(
% 2.15/0.70    ( ! [X0] : (~sP7(sK1,sK2,X0)) )),
% 2.15/0.70    inference(unit_resulting_resolution,[],[f489,f31])).
% 2.15/0.70  fof(f31,plain,(
% 2.15/0.70    ( ! [X0,X3,X1] : (~sP7(X3,X1,X0) | ~r2_hidden(X3,X1)) )),
% 2.15/0.70    inference(cnf_transformation,[],[f1])).
% 2.15/0.70  fof(f489,plain,(
% 2.15/0.70    r2_hidden(sK1,sK2)),
% 2.15/0.70    inference(unit_resulting_resolution,[],[f15,f437,f21])).
% 2.15/0.70  fof(f21,plain,(
% 2.15/0.70    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | r2_hidden(X1,X2) | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)) )),
% 2.15/0.70    inference(cnf_transformation,[],[f7])).
% 2.15/0.70  fof(f7,axiom,(
% 2.15/0.70    ! [X0,X1,X2] : (k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 2.15/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_zfmisc_1)).
% 2.15/0.70  fof(f437,plain,(
% 2.15/0.70    ~r2_hidden(sK0,sK2)),
% 2.15/0.70    inference(backward_demodulation,[],[f368,f411])).
% 2.15/0.70  fof(f411,plain,(
% 2.15/0.70    sK0 = sK3(k4_xboole_0(k2_tarski(sK0,sK1),sK2),sK1)),
% 2.15/0.70    inference(unit_resulting_resolution,[],[f106,f369,f91])).
% 2.15/0.70  fof(f91,plain,(
% 2.15/0.70    ( ! [X6,X4,X5] : (~r2_hidden(X5,k2_tarski(X6,X4)) | X5 = X6 | X4 = X5) )),
% 2.15/0.70    inference(resolution,[],[f24,f40])).
% 2.15/0.70  fof(f40,plain,(
% 2.15/0.70    ( ! [X0,X3,X1] : (sP5(X3,X1,X0) | ~r2_hidden(X3,k2_tarski(X0,X1))) )),
% 2.15/0.70    inference(equality_resolution,[],[f26])).
% 2.15/0.70  fof(f26,plain,(
% 2.15/0.70    ( ! [X2,X0,X3,X1] : (sP5(X3,X1,X0) | ~r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 2.15/0.70    inference(cnf_transformation,[],[f3])).
% 2.15/0.70  fof(f3,axiom,(
% 2.15/0.70    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 2.15/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 2.15/0.70  fof(f24,plain,(
% 2.15/0.70    ( ! [X0,X3,X1] : (~sP5(X3,X1,X0) | X1 = X3 | X0 = X3) )),
% 2.15/0.70    inference(cnf_transformation,[],[f3])).
% 2.15/0.70  fof(f369,plain,(
% 2.15/0.70    r2_hidden(sK3(k4_xboole_0(k2_tarski(sK0,sK1),sK2),sK1),k2_tarski(sK0,sK1))),
% 2.15/0.70    inference(unit_resulting_resolution,[],[f216,f30])).
% 2.15/0.70  fof(f30,plain,(
% 2.15/0.70    ( ! [X0,X3,X1] : (r2_hidden(X3,X0) | ~sP7(X3,X1,X0)) )),
% 2.15/0.70    inference(cnf_transformation,[],[f1])).
% 2.15/0.70  fof(f216,plain,(
% 2.15/0.70    sP7(sK3(k4_xboole_0(k2_tarski(sK0,sK1),sK2),sK1),sK2,k2_tarski(sK0,sK1))),
% 2.15/0.70    inference(unit_resulting_resolution,[],[f116,f44])).
% 2.15/0.70  fof(f116,plain,(
% 2.15/0.70    r2_hidden(sK3(k4_xboole_0(k2_tarski(sK0,sK1),sK2),sK1),k4_xboole_0(k2_tarski(sK0,sK1),sK2))),
% 2.15/0.70    inference(unit_resulting_resolution,[],[f12,f36,f39])).
% 2.15/0.70  fof(f39,plain,(
% 2.15/0.70    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | k1_xboole_0 = X0 | k2_tarski(X1,X1) = X0) )),
% 2.15/0.70    inference(definition_unfolding,[],[f16,f18])).
% 2.15/0.70  fof(f18,plain,(
% 2.15/0.70    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.15/0.70    inference(cnf_transformation,[],[f4])).
% 2.15/0.70  fof(f4,axiom,(
% 2.15/0.70    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.15/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 2.15/0.70  fof(f16,plain,(
% 2.15/0.70    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | r2_hidden(sK3(X0,X1),X0)) )),
% 2.15/0.70    inference(cnf_transformation,[],[f11])).
% 2.15/0.70  fof(f11,plain,(
% 2.15/0.70    ! [X0,X1] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 2.15/0.70    inference(ennf_transformation,[],[f6])).
% 2.15/0.70  fof(f6,axiom,(
% 2.15/0.70    ! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 2.15/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_zfmisc_1)).
% 2.15/0.70  fof(f36,plain,(
% 2.15/0.70    k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k2_tarski(sK1,sK1)),
% 2.15/0.70    inference(definition_unfolding,[],[f14,f18])).
% 2.15/0.70  fof(f14,plain,(
% 2.15/0.70    k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK1)),
% 2.15/0.70    inference(cnf_transformation,[],[f10])).
% 2.15/0.70  fof(f10,plain,(
% 2.15/0.70    ? [X0,X1,X2] : (k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) & k1_tarski(X1) != k4_xboole_0(k2_tarski(X0,X1),X2) & k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2) & k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2))),
% 2.15/0.70    inference(ennf_transformation,[],[f9])).
% 2.15/0.70  fof(f9,negated_conjecture,(
% 2.15/0.70    ~! [X0,X1,X2] : ~(k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) & k1_tarski(X1) != k4_xboole_0(k2_tarski(X0,X1),X2) & k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2) & k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2))),
% 2.15/0.70    inference(negated_conjecture,[],[f8])).
% 2.15/0.70  fof(f8,conjecture,(
% 2.15/0.70    ! [X0,X1,X2] : ~(k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) & k1_tarski(X1) != k4_xboole_0(k2_tarski(X0,X1),X2) & k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2) & k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2))),
% 2.15/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_zfmisc_1)).
% 2.15/0.70  % (11352)Refutation not found, incomplete strategy% (11352)------------------------------
% 2.15/0.70  % (11352)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.15/0.70  % (11352)Termination reason: Refutation not found, incomplete strategy
% 2.15/0.70  
% 2.15/0.70  % (11352)Memory used [KB]: 6140
% 2.15/0.70  % (11352)Time elapsed: 0.255 s
% 2.15/0.70  % (11352)------------------------------
% 2.15/0.70  % (11352)------------------------------
% 2.15/0.71  fof(f12,plain,(
% 2.15/0.71    k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 2.15/0.71    inference(cnf_transformation,[],[f10])).
% 2.15/0.71  fof(f106,plain,(
% 2.15/0.71    sK1 != sK3(k4_xboole_0(k2_tarski(sK0,sK1),sK2),sK1)),
% 2.15/0.71    inference(unit_resulting_resolution,[],[f12,f36,f38])).
% 2.15/0.71  fof(f38,plain,(
% 2.15/0.71    ( ! [X0,X1] : (sK3(X0,X1) != X1 | k1_xboole_0 = X0 | k2_tarski(X1,X1) = X0) )),
% 2.15/0.71    inference(definition_unfolding,[],[f17,f18])).
% 2.15/0.71  fof(f17,plain,(
% 2.15/0.71    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | sK3(X0,X1) != X1) )),
% 2.15/0.71    inference(cnf_transformation,[],[f11])).
% 2.15/0.71  fof(f368,plain,(
% 2.15/0.71    ~r2_hidden(sK3(k4_xboole_0(k2_tarski(sK0,sK1),sK2),sK1),sK2)),
% 2.15/0.71    inference(unit_resulting_resolution,[],[f216,f31])).
% 2.15/0.71  fof(f15,plain,(
% 2.15/0.71    k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 2.15/0.71    inference(cnf_transformation,[],[f10])).
% 2.15/0.71  fof(f1638,plain,(
% 2.15/0.71    r2_hidden(sK1,k4_xboole_0(k2_tarski(sK0,sK1),sK2))),
% 2.15/0.71    inference(backward_demodulation,[],[f117,f1627])).
% 2.15/0.71  fof(f1627,plain,(
% 2.15/0.71    sK1 = sK3(k4_xboole_0(k2_tarski(sK0,sK1),sK2),sK0)),
% 2.15/0.71    inference(unit_resulting_resolution,[],[f107,f232,f330])).
% 2.15/0.71  fof(f330,plain,(
% 2.15/0.71    ( ! [X17,X15,X18,X16] : (~sP7(X15,X18,k2_tarski(X16,X17)) | X15 = X17 | X15 = X16) )),
% 2.15/0.71    inference(resolution,[],[f91,f30])).
% 2.15/0.71  fof(f232,plain,(
% 2.15/0.71    sP7(sK3(k4_xboole_0(k2_tarski(sK0,sK1),sK2),sK0),sK2,k2_tarski(sK0,sK1))),
% 2.15/0.71    inference(unit_resulting_resolution,[],[f117,f44])).
% 2.15/0.71  fof(f107,plain,(
% 2.15/0.71    sK0 != sK3(k4_xboole_0(k2_tarski(sK0,sK1),sK2),sK0)),
% 2.15/0.71    inference(unit_resulting_resolution,[],[f12,f37,f38])).
% 2.15/0.71  fof(f37,plain,(
% 2.15/0.71    k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k2_tarski(sK0,sK0)),
% 2.15/0.71    inference(definition_unfolding,[],[f13,f18])).
% 2.15/0.71  fof(f13,plain,(
% 2.15/0.71    k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK0)),
% 2.15/0.71    inference(cnf_transformation,[],[f10])).
% 2.15/0.71  fof(f117,plain,(
% 2.15/0.71    r2_hidden(sK3(k4_xboole_0(k2_tarski(sK0,sK1),sK2),sK0),k4_xboole_0(k2_tarski(sK0,sK1),sK2))),
% 2.15/0.71    inference(unit_resulting_resolution,[],[f12,f37,f39])).
% 2.15/0.71  % SZS output end Proof for theBenchmark
% 2.15/0.71  % (11368)------------------------------
% 2.15/0.71  % (11368)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.15/0.71  % (11368)Termination reason: Refutation
% 2.15/0.71  
% 2.15/0.71  % (11368)Memory used [KB]: 2686
% 2.15/0.71  % (11368)Time elapsed: 0.277 s
% 2.15/0.71  % (11368)------------------------------
% 2.15/0.71  % (11368)------------------------------
% 2.15/0.71  % (11348)Success in time 0.334 s
%------------------------------------------------------------------------------
