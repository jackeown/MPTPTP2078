%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:38 EST 2020

% Result     : Theorem 1.61s
% Output     : Refutation 1.61s
% Verified   : 
% Statistics : Number of formulae       :   34 ( 103 expanded)
%              Number of leaves         :    4 (  26 expanded)
%              Depth                    :   10
%              Number of atoms          :   70 ( 244 expanded)
%              Number of equality atoms :   37 ( 135 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f191,plain,(
    $false ),
    inference(subsumption_resolution,[],[f189,f131])).

fof(f131,plain,(
    k4_tarski(sK0,sK1) != sK6(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1))) ),
    inference(unit_resulting_resolution,[],[f8,f116,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK6(X0,X1),X1)
      | sK6(X0,X1) != X0
      | k1_tarski(X0) = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f116,plain,(
    r2_hidden(sK6(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1))),k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1))) ),
    inference(unit_resulting_resolution,[],[f25,f8,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1),X1)
      | k1_tarski(X0) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(trivial_inequality_removal,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | X0 != X0
      | k1_tarski(X0) = X1
      | r2_hidden(sK6(X0,X1),X1) ) ),
    inference(duplicate_literal_removal,[],[f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | X0 != X0
      | k1_tarski(X0) = X1
      | r2_hidden(sK6(X0,X1),X1)
      | k1_tarski(X0) = X1 ) ),
    inference(superposition,[],[f23,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( sK6(X0,X1) = X0
      | r2_hidden(sK6(X0,X1),X1)
      | k1_tarski(X0) = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f25,plain,(
    ! [X2,X3] : r2_hidden(k4_tarski(X2,X3),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X2,X3,X1] :
      ( X1 != X3
      | r2_hidden(k4_tarski(X2,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) ) ),
    inference(equality_resolution,[],[f11])).

fof(f11,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 != X2
      | X1 != X3
      | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))
    <=> ( X1 = X3
        & X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_zfmisc_1)).

fof(f8,plain,(
    k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1)) != k1_tarski(k4_tarski(sK0,sK1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0,X1] : k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(k4_tarski(X0,X1)) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] : k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(k4_tarski(X0,X1)) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] : k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(k4_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_zfmisc_1)).

fof(f189,plain,(
    k4_tarski(sK0,sK1) = sK6(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1))) ),
    inference(backward_demodulation,[],[f188,f179])).

fof(f179,plain,(
    sK1 = sK5(k1_tarski(sK0),k1_tarski(sK1),sK6(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1)))) ),
    inference(unit_resulting_resolution,[],[f132,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( sK5(X2,k1_tarski(X1),X0) = X1
      | ~ sP3(X0,k1_tarski(X1),X2) ) ),
    inference(resolution,[],[f14,f29])).

fof(f29,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_tarski(X0))
      | X0 = X2 ) ),
    inference(equality_resolution,[],[f21])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f14,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(sK5(X0,X1,X3),X1)
      | ~ sP3(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(f132,plain,(
    sP3(sK6(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK1),k1_tarski(sK0)) ),
    inference(unit_resulting_resolution,[],[f116,f26])).

fof(f26,plain,(
    ! [X0,X3,X1] :
      ( sP3(X3,X1,X0)
      | ~ r2_hidden(X3,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f17])).

fof(f17,plain,(
    ! [X2,X0,X3,X1] :
      ( sP3(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f188,plain,(
    sK6(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1))) = k4_tarski(sK0,sK5(k1_tarski(sK0),k1_tarski(sK1),sK6(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1))))) ),
    inference(backward_demodulation,[],[f164,f180])).

fof(f180,plain,(
    sK0 = sK4(k1_tarski(sK0),k1_tarski(sK1),sK6(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1)))) ),
    inference(unit_resulting_resolution,[],[f132,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( sK4(k1_tarski(X2),X1,X0) = X2
      | ~ sP3(X0,X1,k1_tarski(X2)) ) ),
    inference(resolution,[],[f13,f29])).

fof(f13,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(sK4(X0,X1,X3),X0)
      | ~ sP3(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f164,plain,(
    sK6(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1))) = k4_tarski(sK4(k1_tarski(sK0),k1_tarski(sK1),sK6(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1)))),sK5(k1_tarski(sK0),k1_tarski(sK1),sK6(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1))))) ),
    inference(unit_resulting_resolution,[],[f116,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k2_zfmisc_1(X0,X1))
      | k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)) = X2 ) ),
    inference(resolution,[],[f15,f26])).

fof(f15,plain,(
    ! [X0,X3,X1] :
      ( ~ sP3(X3,X1,X0)
      | k4_tarski(sK4(X0,X1,X3),sK5(X0,X1,X3)) = X3 ) ),
    inference(cnf_transformation,[],[f3])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:52:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 1.27/0.56  % (4975)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.27/0.57  % (4996)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.61/0.57  % (4988)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.61/0.58  % (4980)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.61/0.59  % (5000)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.61/0.59  % (5000)Refutation not found, incomplete strategy% (5000)------------------------------
% 1.61/0.59  % (5000)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.61/0.59  % (4983)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.61/0.59  % (5000)Termination reason: Refutation not found, incomplete strategy
% 1.61/0.59  
% 1.61/0.59  % (5000)Memory used [KB]: 6140
% 1.61/0.59  % (5000)Time elapsed: 0.151 s
% 1.61/0.59  % (5000)------------------------------
% 1.61/0.59  % (5000)------------------------------
% 1.61/0.59  % (4976)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.61/0.59  % (4977)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.61/0.60  % (4987)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.61/0.60  % (4987)Refutation not found, incomplete strategy% (4987)------------------------------
% 1.61/0.60  % (4987)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.61/0.60  % (4987)Termination reason: Refutation not found, incomplete strategy
% 1.61/0.60  
% 1.61/0.60  % (4987)Memory used [KB]: 1663
% 1.61/0.60  % (4987)Time elapsed: 0.167 s
% 1.61/0.60  % (4987)------------------------------
% 1.61/0.60  % (4987)------------------------------
% 1.61/0.61  % (4974)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.61/0.61  % (4978)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.61/0.61  % (4974)Refutation not found, incomplete strategy% (4974)------------------------------
% 1.61/0.61  % (4974)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.61/0.61  % (4974)Termination reason: Refutation not found, incomplete strategy
% 1.61/0.61  
% 1.61/0.61  % (4974)Memory used [KB]: 1663
% 1.61/0.61  % (4974)Time elapsed: 0.174 s
% 1.61/0.61  % (4974)------------------------------
% 1.61/0.61  % (4974)------------------------------
% 1.61/0.61  % (4973)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.61/0.62  % (4979)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.61/0.62  % (4992)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.61/0.63  % (5001)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.61/0.63  % (4986)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.61/0.63  % (5002)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.61/0.63  % (4993)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.61/0.63  % (4999)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.61/0.64  % (4994)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.61/0.64  % (4991)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.61/0.64  % (4984)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.61/0.64  % (4991)Refutation not found, incomplete strategy% (4991)------------------------------
% 1.61/0.64  % (4991)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.61/0.64  % (4991)Termination reason: Refutation not found, incomplete strategy
% 1.61/0.64  
% 1.61/0.64  % (4991)Memory used [KB]: 1663
% 1.61/0.64  % (4991)Time elapsed: 0.203 s
% 1.61/0.64  % (4991)------------------------------
% 1.61/0.64  % (4991)------------------------------
% 1.61/0.64  % (4995)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.61/0.64  % (4984)Refutation not found, incomplete strategy% (4984)------------------------------
% 1.61/0.64  % (4984)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.61/0.64  % (4984)Termination reason: Refutation not found, incomplete strategy
% 1.61/0.64  
% 1.61/0.64  % (4984)Memory used [KB]: 6268
% 1.61/0.64  % (4984)Time elapsed: 0.205 s
% 1.61/0.64  % (4984)------------------------------
% 1.61/0.64  % (4984)------------------------------
% 1.61/0.64  % (4982)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.61/0.64  % (4985)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.61/0.64  % (4997)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.61/0.65  % (4997)Refutation not found, incomplete strategy% (4997)------------------------------
% 1.61/0.65  % (4997)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.61/0.65  % (4990)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.61/0.65  % (4989)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.61/0.65  % (4990)Refutation not found, incomplete strategy% (4990)------------------------------
% 1.61/0.65  % (4990)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.61/0.65  % (4990)Termination reason: Refutation not found, incomplete strategy
% 1.61/0.65  
% 1.61/0.65  % (4990)Memory used [KB]: 1663
% 1.61/0.65  % (4990)Time elapsed: 0.211 s
% 1.61/0.65  % (4990)------------------------------
% 1.61/0.65  % (4990)------------------------------
% 1.61/0.65  % (4989)Refutation not found, incomplete strategy% (4989)------------------------------
% 1.61/0.65  % (4989)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.61/0.65  % (4989)Termination reason: Refutation not found, incomplete strategy
% 1.61/0.65  
% 1.61/0.65  % (4989)Memory used [KB]: 10618
% 1.61/0.65  % (4989)Time elapsed: 0.212 s
% 1.61/0.65  % (4989)------------------------------
% 1.61/0.65  % (4989)------------------------------
% 1.61/0.65  % (4992)Refutation found. Thanks to Tanya!
% 1.61/0.65  % SZS status Theorem for theBenchmark
% 1.61/0.65  % SZS output start Proof for theBenchmark
% 1.61/0.65  fof(f191,plain,(
% 1.61/0.65    $false),
% 1.61/0.65    inference(subsumption_resolution,[],[f189,f131])).
% 1.61/0.65  fof(f131,plain,(
% 1.61/0.65    k4_tarski(sK0,sK1) != sK6(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1)))),
% 1.61/0.65    inference(unit_resulting_resolution,[],[f8,f116,f23])).
% 1.61/0.65  fof(f23,plain,(
% 1.61/0.65    ( ! [X0,X1] : (~r2_hidden(sK6(X0,X1),X1) | sK6(X0,X1) != X0 | k1_tarski(X0) = X1) )),
% 1.61/0.65    inference(cnf_transformation,[],[f1])).
% 1.61/0.65  fof(f1,axiom,(
% 1.61/0.65    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.61/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 1.61/0.65  fof(f116,plain,(
% 1.61/0.65    r2_hidden(sK6(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1))),k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1)))),
% 1.61/0.65    inference(unit_resulting_resolution,[],[f25,f8,f70])).
% 1.61/0.65  fof(f70,plain,(
% 1.61/0.65    ( ! [X0,X1] : (r2_hidden(sK6(X0,X1),X1) | k1_tarski(X0) = X1 | ~r2_hidden(X0,X1)) )),
% 1.61/0.65    inference(trivial_inequality_removal,[],[f69])).
% 1.61/0.65  fof(f69,plain,(
% 1.61/0.65    ( ! [X0,X1] : (~r2_hidden(X0,X1) | X0 != X0 | k1_tarski(X0) = X1 | r2_hidden(sK6(X0,X1),X1)) )),
% 1.61/0.65    inference(duplicate_literal_removal,[],[f68])).
% 1.61/0.65  fof(f68,plain,(
% 1.61/0.65    ( ! [X0,X1] : (~r2_hidden(X0,X1) | X0 != X0 | k1_tarski(X0) = X1 | r2_hidden(sK6(X0,X1),X1) | k1_tarski(X0) = X1) )),
% 1.61/0.65    inference(superposition,[],[f23,f22])).
% 1.61/0.65  fof(f22,plain,(
% 1.61/0.65    ( ! [X0,X1] : (sK6(X0,X1) = X0 | r2_hidden(sK6(X0,X1),X1) | k1_tarski(X0) = X1) )),
% 1.61/0.65    inference(cnf_transformation,[],[f1])).
% 1.61/0.65  fof(f25,plain,(
% 1.61/0.65    ( ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))) )),
% 1.61/0.65    inference(equality_resolution,[],[f24])).
% 1.61/0.65  fof(f24,plain,(
% 1.61/0.65    ( ! [X2,X3,X1] : (X1 != X3 | r2_hidden(k4_tarski(X2,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))) )),
% 1.61/0.65    inference(equality_resolution,[],[f11])).
% 1.61/0.65  fof(f11,plain,(
% 1.61/0.65    ( ! [X2,X0,X3,X1] : (X0 != X2 | X1 != X3 | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))) )),
% 1.61/0.65    inference(cnf_transformation,[],[f4])).
% 1.61/0.65  fof(f4,axiom,(
% 1.61/0.65    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) <=> (X1 = X3 & X0 = X2))),
% 1.61/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_zfmisc_1)).
% 1.61/0.65  fof(f8,plain,(
% 1.61/0.65    k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1)) != k1_tarski(k4_tarski(sK0,sK1))),
% 1.61/0.65    inference(cnf_transformation,[],[f7])).
% 1.61/0.65  fof(f7,plain,(
% 1.61/0.65    ? [X0,X1] : k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(k4_tarski(X0,X1))),
% 1.61/0.65    inference(ennf_transformation,[],[f6])).
% 1.61/0.65  fof(f6,negated_conjecture,(
% 1.61/0.65    ~! [X0,X1] : k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(k4_tarski(X0,X1))),
% 1.61/0.65    inference(negated_conjecture,[],[f5])).
% 1.61/0.65  fof(f5,conjecture,(
% 1.61/0.65    ! [X0,X1] : k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(k4_tarski(X0,X1))),
% 1.61/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_zfmisc_1)).
% 1.61/0.65  fof(f189,plain,(
% 1.61/0.65    k4_tarski(sK0,sK1) = sK6(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1)))),
% 1.61/0.65    inference(backward_demodulation,[],[f188,f179])).
% 1.61/0.65  fof(f179,plain,(
% 1.61/0.65    sK1 = sK5(k1_tarski(sK0),k1_tarski(sK1),sK6(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1))))),
% 1.61/0.65    inference(unit_resulting_resolution,[],[f132,f41])).
% 1.61/0.65  fof(f41,plain,(
% 1.61/0.65    ( ! [X2,X0,X1] : (sK5(X2,k1_tarski(X1),X0) = X1 | ~sP3(X0,k1_tarski(X1),X2)) )),
% 1.61/0.65    inference(resolution,[],[f14,f29])).
% 1.61/0.65  fof(f29,plain,(
% 1.61/0.65    ( ! [X2,X0] : (~r2_hidden(X2,k1_tarski(X0)) | X0 = X2) )),
% 1.61/0.65    inference(equality_resolution,[],[f21])).
% 1.61/0.65  fof(f21,plain,(
% 1.61/0.65    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 1.61/0.65    inference(cnf_transformation,[],[f1])).
% 1.61/0.65  fof(f14,plain,(
% 1.61/0.65    ( ! [X0,X3,X1] : (r2_hidden(sK5(X0,X1,X3),X1) | ~sP3(X3,X1,X0)) )),
% 1.61/0.65    inference(cnf_transformation,[],[f3])).
% 1.61/0.65  fof(f3,axiom,(
% 1.61/0.65    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 1.61/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).
% 1.61/0.65  fof(f132,plain,(
% 1.61/0.65    sP3(sK6(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK1),k1_tarski(sK0))),
% 1.61/0.65    inference(unit_resulting_resolution,[],[f116,f26])).
% 1.61/0.65  fof(f26,plain,(
% 1.61/0.65    ( ! [X0,X3,X1] : (sP3(X3,X1,X0) | ~r2_hidden(X3,k2_zfmisc_1(X0,X1))) )),
% 1.61/0.65    inference(equality_resolution,[],[f17])).
% 1.61/0.65  fof(f17,plain,(
% 1.61/0.65    ( ! [X2,X0,X3,X1] : (sP3(X3,X1,X0) | ~r2_hidden(X3,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 1.61/0.65    inference(cnf_transformation,[],[f3])).
% 1.61/0.65  fof(f188,plain,(
% 1.61/0.65    sK6(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1))) = k4_tarski(sK0,sK5(k1_tarski(sK0),k1_tarski(sK1),sK6(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1)))))),
% 1.61/0.65    inference(backward_demodulation,[],[f164,f180])).
% 1.61/0.65  fof(f180,plain,(
% 1.61/0.65    sK0 = sK4(k1_tarski(sK0),k1_tarski(sK1),sK6(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1))))),
% 1.61/0.65    inference(unit_resulting_resolution,[],[f132,f39])).
% 1.61/0.65  fof(f39,plain,(
% 1.61/0.65    ( ! [X2,X0,X1] : (sK4(k1_tarski(X2),X1,X0) = X2 | ~sP3(X0,X1,k1_tarski(X2))) )),
% 1.61/0.65    inference(resolution,[],[f13,f29])).
% 1.61/0.65  fof(f13,plain,(
% 1.61/0.65    ( ! [X0,X3,X1] : (r2_hidden(sK4(X0,X1,X3),X0) | ~sP3(X3,X1,X0)) )),
% 1.61/0.65    inference(cnf_transformation,[],[f3])).
% 1.61/0.65  fof(f164,plain,(
% 1.61/0.65    sK6(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1))) = k4_tarski(sK4(k1_tarski(sK0),k1_tarski(sK1),sK6(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1)))),sK5(k1_tarski(sK0),k1_tarski(sK1),sK6(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1)))))),
% 1.61/0.65    inference(unit_resulting_resolution,[],[f116,f72])).
% 1.61/0.65  fof(f72,plain,(
% 1.61/0.65    ( ! [X2,X0,X1] : (~r2_hidden(X2,k2_zfmisc_1(X0,X1)) | k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)) = X2) )),
% 1.61/0.65    inference(resolution,[],[f15,f26])).
% 1.61/0.65  fof(f15,plain,(
% 1.61/0.65    ( ! [X0,X3,X1] : (~sP3(X3,X1,X0) | k4_tarski(sK4(X0,X1,X3),sK5(X0,X1,X3)) = X3) )),
% 1.61/0.65    inference(cnf_transformation,[],[f3])).
% 1.61/0.65  % SZS output end Proof for theBenchmark
% 1.61/0.65  % (4992)------------------------------
% 1.61/0.65  % (4992)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.61/0.65  % (4992)Termination reason: Refutation
% 1.61/0.65  
% 1.61/0.65  % (4992)Memory used [KB]: 1918
% 1.61/0.65  % (4992)Time elapsed: 0.218 s
% 1.61/0.65  % (4992)------------------------------
% 1.61/0.65  % (4992)------------------------------
% 1.61/0.65  % (4981)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.61/0.65  % (4972)Success in time 0.286 s
%------------------------------------------------------------------------------
