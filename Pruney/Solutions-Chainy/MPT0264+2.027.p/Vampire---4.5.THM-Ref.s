%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:40:24 EST 2020

% Result     : Theorem 4.26s
% Output     : Refutation 4.26s
% Verified   : 
% Statistics : Number of formulae       :   45 (  81 expanded)
%              Number of leaves         :   11 (  24 expanded)
%              Depth                    :    8
%              Number of atoms          :   87 ( 145 expanded)
%              Number of equality atoms :   47 (  89 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5432,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f152,f135,f130,f366])).

fof(f366,plain,(
    ! [X1] :
      ( r2_hidden(X1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
      | r2_hidden(X1,k5_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)))
      | ~ r2_hidden(X1,k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2)) ) ),
    inference(superposition,[],[f46,f123])).

fof(f123,plain,(
    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k5_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)),k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2)) ),
    inference(forward_demodulation,[],[f85,f68])).

fof(f68,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f85,plain,(
    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2),k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f37,f84,f58,f83])).

fof(f83,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f62,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f78,f79])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f78,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f62,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f58,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f84,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f63,f83])).

fof(f63,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f37,plain,(
    k1_tarski(sK0) = k3_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ? [X0,X1,X2] :
      ( X0 != X1
      & r2_hidden(X1,X2)
      & k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( X0 != X1
          & r2_hidden(X1,X2)
          & k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(negated_conjecture,[],[f30])).

fof(f30,conjecture,(
    ! [X0,X1,X2] :
      ~ ( X0 != X1
        & r2_hidden(X1,X2)
        & k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_zfmisc_1)).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

fof(f130,plain,(
    ! [X0,X1] : ~ r2_hidden(sK1,k5_xboole_0(sK2,k3_enumset1(X0,X0,X0,X1,sK1))) ),
    inference(unit_resulting_resolution,[],[f117,f38,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k5_xboole_0(X1,X2))
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f38,plain,(
    r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f117,plain,(
    ! [X4,X0,X1] : r2_hidden(X4,k3_enumset1(X0,X0,X0,X1,X4)) ),
    inference(equality_resolution,[],[f116])).

fof(f116,plain,(
    ! [X4,X0,X3,X1] :
      ( r2_hidden(X4,X3)
      | k3_enumset1(X0,X0,X0,X1,X4) != X3 ) ),
    inference(equality_resolution,[],[f99])).

fof(f99,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X2 != X4
      | r2_hidden(X4,X3)
      | k3_enumset1(X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f77,f82])).

fof(f77,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X2 != X4
      | r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(f135,plain,(
    ! [X0] : r2_hidden(sK1,k2_xboole_0(X0,sK2)) ),
    inference(unit_resulting_resolution,[],[f38,f109])).

fof(f109,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f152,plain,(
    ~ r2_hidden(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    inference(unit_resulting_resolution,[],[f39,f112])).

fof(f112,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k3_enumset1(X0,X0,X0,X0,X0))
      | X0 = X2 ) ),
    inference(equality_resolution,[],[f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k3_enumset1(X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f55,f84])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f39,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 21:01:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.49  % (16081)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.50  % (16076)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.50  % (16073)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.51  % (16074)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.51  % (16101)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.51  % (16084)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.52  % (16100)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.52  % (16072)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.52  % (16082)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.53  % (16090)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.53  % (16075)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.53  % (16096)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.53  % (16091)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.53  % (16078)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.53  % (16087)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.53  % (16077)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.54  % (16092)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.54  % (16079)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.54  % (16095)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.43/0.54  % (16102)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.43/0.54  % (16080)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.43/0.54  % (16093)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.43/0.54  % (16102)Refutation not found, incomplete strategy% (16102)------------------------------
% 1.43/0.54  % (16102)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.54  % (16102)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.54  
% 1.43/0.54  % (16102)Memory used [KB]: 1663
% 1.43/0.54  % (16102)Time elapsed: 0.137 s
% 1.43/0.54  % (16102)------------------------------
% 1.43/0.54  % (16102)------------------------------
% 1.43/0.54  % (16097)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.43/0.54  % (16094)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.43/0.55  % (16083)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.43/0.55  % (16085)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.43/0.55  % (16086)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.43/0.56  % (16099)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.43/0.56  % (16098)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.57/0.57  % (16088)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.57/0.57  % (16088)Refutation not found, incomplete strategy% (16088)------------------------------
% 1.57/0.57  % (16088)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.57  % (16088)Termination reason: Refutation not found, incomplete strategy
% 1.57/0.57  
% 1.57/0.57  % (16088)Memory used [KB]: 10746
% 1.57/0.57  % (16088)Time elapsed: 0.160 s
% 1.57/0.57  % (16088)------------------------------
% 1.57/0.57  % (16088)------------------------------
% 2.03/0.65  % (16206)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.34/0.72  % (16216)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 3.05/0.82  % (16074)Time limit reached!
% 3.05/0.82  % (16074)------------------------------
% 3.05/0.82  % (16074)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.05/0.82  % (16074)Termination reason: Time limit
% 3.05/0.82  
% 3.05/0.82  % (16074)Memory used [KB]: 6908
% 3.05/0.82  % (16074)Time elapsed: 0.419 s
% 3.05/0.82  % (16074)------------------------------
% 3.05/0.82  % (16074)------------------------------
% 3.56/0.84  % (16097)Time limit reached!
% 3.56/0.84  % (16097)------------------------------
% 3.56/0.84  % (16097)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.56/0.84  % (16097)Termination reason: Time limit
% 3.56/0.84  
% 3.56/0.84  % (16097)Memory used [KB]: 13048
% 3.56/0.84  % (16097)Time elapsed: 0.429 s
% 3.56/0.84  % (16097)------------------------------
% 3.56/0.84  % (16097)------------------------------
% 3.75/0.91  % (16086)Time limit reached!
% 3.75/0.91  % (16086)------------------------------
% 3.75/0.91  % (16086)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.75/0.91  % (16086)Termination reason: Time limit
% 3.75/0.91  
% 3.75/0.91  % (16086)Memory used [KB]: 4733
% 3.75/0.91  % (16086)Time elapsed: 0.510 s
% 3.75/0.91  % (16086)------------------------------
% 3.75/0.91  % (16086)------------------------------
% 3.75/0.92  % (16078)Time limit reached!
% 3.75/0.92  % (16078)------------------------------
% 3.75/0.92  % (16078)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.75/0.92  % (16078)Termination reason: Time limit
% 3.75/0.92  % (16078)Termination phase: Saturation
% 3.75/0.92  
% 3.75/0.92  % (16078)Memory used [KB]: 15863
% 3.75/0.92  % (16078)Time elapsed: 0.500 s
% 3.75/0.92  % (16078)------------------------------
% 3.75/0.92  % (16078)------------------------------
% 4.26/0.93  % (16098)Refutation found. Thanks to Tanya!
% 4.26/0.93  % SZS status Theorem for theBenchmark
% 4.26/0.95  % SZS output start Proof for theBenchmark
% 4.26/0.95  fof(f5432,plain,(
% 4.26/0.95    $false),
% 4.26/0.95    inference(unit_resulting_resolution,[],[f152,f135,f130,f366])).
% 4.26/0.95  fof(f366,plain,(
% 4.26/0.95    ( ! [X1] : (r2_hidden(X1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | r2_hidden(X1,k5_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1))) | ~r2_hidden(X1,k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2))) )),
% 4.26/0.95    inference(superposition,[],[f46,f123])).
% 4.26/0.95  fof(f123,plain,(
% 4.26/0.95    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k5_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)),k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2))),
% 4.26/0.95    inference(forward_demodulation,[],[f85,f68])).
% 4.26/0.95  fof(f68,plain,(
% 4.26/0.95    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 4.26/0.95    inference(cnf_transformation,[],[f1])).
% 4.26/0.95  fof(f1,axiom,(
% 4.26/0.95    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 4.26/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 4.26/0.95  fof(f85,plain,(
% 4.26/0.95    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2),k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2))),
% 4.26/0.95    inference(definition_unfolding,[],[f37,f84,f58,f83])).
% 4.26/0.95  fof(f83,plain,(
% 4.26/0.95    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 4.26/0.95    inference(definition_unfolding,[],[f62,f82])).
% 4.26/0.95  fof(f82,plain,(
% 4.26/0.95    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 4.26/0.95    inference(definition_unfolding,[],[f78,f79])).
% 4.26/0.95  fof(f79,plain,(
% 4.26/0.95    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 4.26/0.95    inference(cnf_transformation,[],[f22])).
% 4.26/0.95  fof(f22,axiom,(
% 4.26/0.95    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 4.26/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 4.26/0.95  fof(f78,plain,(
% 4.26/0.95    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 4.26/0.95    inference(cnf_transformation,[],[f21])).
% 4.26/0.95  fof(f21,axiom,(
% 4.26/0.95    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 4.26/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 4.26/0.95  fof(f62,plain,(
% 4.26/0.95    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 4.26/0.95    inference(cnf_transformation,[],[f20])).
% 4.26/0.95  fof(f20,axiom,(
% 4.26/0.95    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 4.26/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 4.26/0.95  fof(f58,plain,(
% 4.26/0.95    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 4.26/0.95    inference(cnf_transformation,[],[f13])).
% 4.26/0.95  fof(f13,axiom,(
% 4.26/0.95    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 4.26/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).
% 4.26/0.95  fof(f84,plain,(
% 4.26/0.95    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 4.26/0.95    inference(definition_unfolding,[],[f63,f83])).
% 4.26/0.95  fof(f63,plain,(
% 4.26/0.95    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 4.26/0.95    inference(cnf_transformation,[],[f19])).
% 4.26/0.95  fof(f19,axiom,(
% 4.26/0.95    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 4.26/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 4.26/0.95  fof(f37,plain,(
% 4.26/0.95    k1_tarski(sK0) = k3_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 4.26/0.95    inference(cnf_transformation,[],[f34])).
% 4.26/0.95  fof(f34,plain,(
% 4.26/0.95    ? [X0,X1,X2] : (X0 != X1 & r2_hidden(X1,X2) & k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X1),X2))),
% 4.26/0.95    inference(ennf_transformation,[],[f31])).
% 4.26/0.95  fof(f31,negated_conjecture,(
% 4.26/0.95    ~! [X0,X1,X2] : ~(X0 != X1 & r2_hidden(X1,X2) & k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X1),X2))),
% 4.26/0.95    inference(negated_conjecture,[],[f30])).
% 4.26/0.95  fof(f30,conjecture,(
% 4.26/0.95    ! [X0,X1,X2] : ~(X0 != X1 & r2_hidden(X1,X2) & k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X1),X2))),
% 4.26/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_zfmisc_1)).
% 4.26/0.95  fof(f46,plain,(
% 4.26/0.95    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) )),
% 4.26/0.95    inference(cnf_transformation,[],[f35])).
% 4.26/0.95  fof(f35,plain,(
% 4.26/0.95    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 4.26/0.95    inference(ennf_transformation,[],[f5])).
% 4.26/0.95  fof(f5,axiom,(
% 4.26/0.95    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 4.26/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).
% 4.26/0.95  fof(f130,plain,(
% 4.26/0.95    ( ! [X0,X1] : (~r2_hidden(sK1,k5_xboole_0(sK2,k3_enumset1(X0,X0,X0,X1,sK1)))) )),
% 4.26/0.95    inference(unit_resulting_resolution,[],[f117,f38,f45])).
% 4.26/0.95  fof(f45,plain,(
% 4.26/0.95    ( ! [X2,X0,X1] : (~r2_hidden(X0,k5_xboole_0(X1,X2)) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) )),
% 4.26/0.95    inference(cnf_transformation,[],[f35])).
% 4.26/0.95  fof(f38,plain,(
% 4.26/0.95    r2_hidden(sK1,sK2)),
% 4.26/0.95    inference(cnf_transformation,[],[f34])).
% 4.26/0.95  fof(f117,plain,(
% 4.26/0.95    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_enumset1(X0,X0,X0,X1,X4))) )),
% 4.26/0.95    inference(equality_resolution,[],[f116])).
% 4.26/0.95  fof(f116,plain,(
% 4.26/0.95    ( ! [X4,X0,X3,X1] : (r2_hidden(X4,X3) | k3_enumset1(X0,X0,X0,X1,X4) != X3) )),
% 4.26/0.95    inference(equality_resolution,[],[f99])).
% 4.26/0.95  fof(f99,plain,(
% 4.26/0.95    ( ! [X4,X2,X0,X3,X1] : (X2 != X4 | r2_hidden(X4,X3) | k3_enumset1(X0,X0,X0,X1,X2) != X3) )),
% 4.26/0.95    inference(definition_unfolding,[],[f77,f82])).
% 4.26/0.95  fof(f77,plain,(
% 4.26/0.95    ( ! [X4,X2,X0,X3,X1] : (X2 != X4 | r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 4.26/0.95    inference(cnf_transformation,[],[f36])).
% 4.26/0.95  fof(f36,plain,(
% 4.26/0.95    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 4.26/0.95    inference(ennf_transformation,[],[f14])).
% 4.26/0.95  fof(f14,axiom,(
% 4.26/0.95    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 4.26/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 4.26/0.95  fof(f135,plain,(
% 4.26/0.95    ( ! [X0] : (r2_hidden(sK1,k2_xboole_0(X0,sK2))) )),
% 4.26/0.95    inference(unit_resulting_resolution,[],[f38,f109])).
% 4.26/0.95  fof(f109,plain,(
% 4.26/0.95    ( ! [X0,X3,X1] : (r2_hidden(X3,k2_xboole_0(X0,X1)) | ~r2_hidden(X3,X1)) )),
% 4.26/0.95    inference(equality_resolution,[],[f53])).
% 4.26/0.95  fof(f53,plain,(
% 4.26/0.95    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | r2_hidden(X3,X2) | k2_xboole_0(X0,X1) != X2) )),
% 4.26/0.95    inference(cnf_transformation,[],[f2])).
% 4.26/0.95  fof(f2,axiom,(
% 4.26/0.95    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 4.26/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).
% 4.26/0.95  fof(f152,plain,(
% 4.26/0.95    ~r2_hidden(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),
% 4.26/0.95    inference(unit_resulting_resolution,[],[f39,f112])).
% 4.26/0.95  fof(f112,plain,(
% 4.26/0.95    ( ! [X2,X0] : (~r2_hidden(X2,k3_enumset1(X0,X0,X0,X0,X0)) | X0 = X2) )),
% 4.26/0.95    inference(equality_resolution,[],[f92])).
% 4.26/0.95  fof(f92,plain,(
% 4.26/0.95    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k3_enumset1(X0,X0,X0,X0,X0) != X1) )),
% 4.26/0.95    inference(definition_unfolding,[],[f55,f84])).
% 4.26/0.95  fof(f55,plain,(
% 4.26/0.95    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 4.26/0.95    inference(cnf_transformation,[],[f15])).
% 4.26/0.95  fof(f15,axiom,(
% 4.26/0.95    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 4.26/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 4.26/0.95  fof(f39,plain,(
% 4.26/0.95    sK0 != sK1),
% 4.26/0.95    inference(cnf_transformation,[],[f34])).
% 4.26/0.95  % SZS output end Proof for theBenchmark
% 4.26/0.95  % (16098)------------------------------
% 4.26/0.95  % (16098)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.26/0.95  % (16098)Termination reason: Refutation
% 4.26/0.95  
% 4.26/0.95  % (16098)Memory used [KB]: 11513
% 4.26/0.95  % (16098)Time elapsed: 0.493 s
% 4.26/0.95  % (16098)------------------------------
% 4.26/0.95  % (16098)------------------------------
% 4.26/0.95  % (16070)Success in time 0.587 s
%------------------------------------------------------------------------------
