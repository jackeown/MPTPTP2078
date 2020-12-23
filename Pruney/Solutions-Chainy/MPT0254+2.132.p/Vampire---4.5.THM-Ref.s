%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:39:30 EST 2020

% Result     : Theorem 1.31s
% Output     : Refutation 1.31s
% Verified   : 
% Statistics : Number of formulae       :   44 ( 102 expanded)
%              Number of leaves         :   11 (  28 expanded)
%              Depth                    :   14
%              Number of atoms          :  106 ( 261 expanded)
%              Number of equality atoms :   32 (  61 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f133,plain,(
    $false ),
    inference(subsumption_resolution,[],[f130,f46])).

fof(f46,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(f130,plain,(
    k1_xboole_0 != k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f76,f105])).

fof(f105,plain,(
    k1_xboole_0 = k1_tarski(sK0) ),
    inference(subsumption_resolution,[],[f104,f103])).

fof(f103,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK2(k1_tarski(sK0)),X1)
      | k1_xboole_0 = k1_tarski(sK0) ) ),
    inference(duplicate_literal_removal,[],[f102])).

fof(f102,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK2(k1_tarski(sK0)),X1)
      | k1_xboole_0 = k1_tarski(sK0)
      | ~ r2_hidden(sK2(k1_tarski(sK0)),X1) ) ),
    inference(forward_demodulation,[],[f97,f48])).

fof(f48,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f97,plain,(
    ! [X1] :
      ( k1_xboole_0 = k1_tarski(sK0)
      | ~ r2_hidden(sK2(k1_tarski(sK0)),X1)
      | ~ r2_hidden(sK2(k1_tarski(sK0)),k5_xboole_0(X1,k1_xboole_0)) ) ),
    inference(resolution,[],[f81,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k5_xboole_0(X1,X2))
        | ( ( r2_hidden(X0,X1)
            | ~ r2_hidden(X0,X2) )
          & ( r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) ) ) )
      & ( ( ( ~ r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) )
          & ( r2_hidden(X0,X2)
            | r2_hidden(X0,X1) ) )
        | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
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

fof(f81,plain,
    ( r2_hidden(sK2(k1_tarski(sK0)),k1_xboole_0)
    | k1_xboole_0 = k1_tarski(sK0) ),
    inference(resolution,[],[f79,f50])).

fof(f50,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f31,f36])).

fof(f36,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f79,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_tarski(sK0))
      | r2_hidden(X0,k1_xboole_0) ) ),
    inference(resolution,[],[f78,f58])).

fof(f58,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f39,f40])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
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

fof(f78,plain,(
    r1_tarski(k1_tarski(sK0),k1_xboole_0) ),
    inference(superposition,[],[f53,f44])).

fof(f44,plain,(
    k1_xboole_0 = k2_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    k1_xboole_0 = k2_xboole_0(k1_tarski(sK0),sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f30,f34])).

fof(f34,plain,
    ( ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1)
   => k1_xboole_0 = k2_xboole_0(k1_tarski(sK0),sK1) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,negated_conjecture,(
    ~ ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(negated_conjecture,[],[f26])).

fof(f26,conjecture,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f53,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f104,plain,(
    ! [X2] :
      ( k1_xboole_0 = k1_tarski(sK0)
      | r2_hidden(sK2(k1_tarski(sK0)),X2) ) ),
    inference(subsumption_resolution,[],[f98,f103])).

fof(f98,plain,(
    ! [X2] :
      ( k1_xboole_0 = k1_tarski(sK0)
      | r2_hidden(sK2(k1_tarski(sK0)),k5_xboole_0(k1_xboole_0,X2))
      | r2_hidden(sK2(k1_tarski(sK0)),X2) ) ),
    inference(resolution,[],[f81,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f76,plain,(
    ! [X1] : k1_tarski(X1) != k4_xboole_0(k1_tarski(X1),k1_tarski(X1)) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
        | X0 = X1 )
      & ( X0 != X1
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:28:16 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.51  % (7797)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.51  % (7789)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.51  % (7797)Refutation not found, incomplete strategy% (7797)------------------------------
% 0.22/0.51  % (7797)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (7797)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (7797)Memory used [KB]: 1791
% 0.22/0.51  % (7797)Time elapsed: 0.066 s
% 0.22/0.51  % (7797)------------------------------
% 0.22/0.51  % (7797)------------------------------
% 0.22/0.51  % (7787)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.52  % (7786)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.52  % (7803)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.52  % (7786)Refutation not found, incomplete strategy% (7786)------------------------------
% 0.22/0.52  % (7786)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (7786)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (7786)Memory used [KB]: 10618
% 0.22/0.52  % (7786)Time elapsed: 0.100 s
% 0.22/0.52  % (7786)------------------------------
% 0.22/0.52  % (7786)------------------------------
% 0.22/0.52  % (7778)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.52  % (7802)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.53  % (7780)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.53  % (7780)Refutation not found, incomplete strategy% (7780)------------------------------
% 0.22/0.53  % (7780)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (7780)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (7780)Memory used [KB]: 6268
% 0.22/0.53  % (7780)Time elapsed: 0.104 s
% 0.22/0.53  % (7780)------------------------------
% 0.22/0.53  % (7780)------------------------------
% 0.22/0.53  % (7785)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.53  % (7794)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.53  % (7800)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.53  % (7801)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.53  % (7784)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.53  % (7788)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (7798)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.53  % (7787)Refutation not found, incomplete strategy% (7787)------------------------------
% 0.22/0.53  % (7787)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (7787)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (7787)Memory used [KB]: 10618
% 0.22/0.53  % (7787)Time elapsed: 0.114 s
% 0.22/0.53  % (7787)------------------------------
% 0.22/0.53  % (7787)------------------------------
% 0.22/0.54  % (7802)Refutation not found, incomplete strategy% (7802)------------------------------
% 0.22/0.54  % (7802)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (7784)Refutation not found, incomplete strategy% (7784)------------------------------
% 0.22/0.54  % (7784)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (7784)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (7784)Memory used [KB]: 10746
% 0.22/0.54  % (7784)Time elapsed: 0.112 s
% 0.22/0.54  % (7784)------------------------------
% 0.22/0.54  % (7784)------------------------------
% 0.22/0.54  % (7795)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.54  % (7783)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.54  % (7792)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.54  % (7779)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.54  % (7778)Refutation not found, incomplete strategy% (7778)------------------------------
% 0.22/0.54  % (7778)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (7778)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (7778)Memory used [KB]: 10746
% 0.22/0.54  % (7778)Time elapsed: 0.125 s
% 0.22/0.54  % (7778)------------------------------
% 0.22/0.54  % (7778)------------------------------
% 0.22/0.54  % (7790)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.31/0.54  % (7802)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.54  
% 1.31/0.54  % (7802)Memory used [KB]: 10746
% 1.31/0.54  % (7802)Time elapsed: 0.117 s
% 1.31/0.54  % (7802)------------------------------
% 1.31/0.54  % (7802)------------------------------
% 1.31/0.54  % (7777)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.31/0.54  % (7782)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.31/0.54  % (7781)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.31/0.55  % (7796)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.31/0.55  % (7805)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.31/0.55  % (7791)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.31/0.55  % (7798)Refutation not found, incomplete strategy% (7798)------------------------------
% 1.31/0.55  % (7798)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.55  % (7798)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.55  
% 1.31/0.55  % (7798)Memory used [KB]: 10874
% 1.31/0.55  % (7798)Time elapsed: 0.130 s
% 1.31/0.55  % (7798)------------------------------
% 1.31/0.55  % (7798)------------------------------
% 1.31/0.55  % (7791)Refutation not found, incomplete strategy% (7791)------------------------------
% 1.31/0.55  % (7791)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.55  % (7793)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.31/0.55  % (7776)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.31/0.55  % (7799)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.31/0.55  % (7793)Refutation not found, incomplete strategy% (7793)------------------------------
% 1.31/0.55  % (7793)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.55  % (7785)Refutation not found, incomplete strategy% (7785)------------------------------
% 1.31/0.55  % (7785)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.55  % (7785)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.55  
% 1.31/0.55  % (7785)Memory used [KB]: 10618
% 1.31/0.55  % (7785)Time elapsed: 0.131 s
% 1.31/0.55  % (7785)------------------------------
% 1.31/0.55  % (7785)------------------------------
% 1.31/0.55  % (7799)Refutation found. Thanks to Tanya!
% 1.31/0.55  % SZS status Theorem for theBenchmark
% 1.31/0.55  % (7801)Refutation not found, incomplete strategy% (7801)------------------------------
% 1.31/0.55  % (7801)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.55  % (7801)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.55  
% 1.31/0.55  % (7801)Memory used [KB]: 6268
% 1.31/0.55  % (7801)Time elapsed: 0.141 s
% 1.31/0.55  % (7801)------------------------------
% 1.31/0.55  % (7801)------------------------------
% 1.31/0.55  % (7804)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.31/0.55  % (7776)Refutation not found, incomplete strategy% (7776)------------------------------
% 1.31/0.55  % (7776)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.56  % SZS output start Proof for theBenchmark
% 1.31/0.56  fof(f133,plain,(
% 1.31/0.56    $false),
% 1.31/0.56    inference(subsumption_resolution,[],[f130,f46])).
% 1.31/0.56  fof(f46,plain,(
% 1.31/0.56    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 1.31/0.56    inference(cnf_transformation,[],[f8])).
% 1.31/0.56  fof(f8,axiom,(
% 1.31/0.56    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 1.31/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).
% 1.31/0.56  fof(f130,plain,(
% 1.31/0.56    k1_xboole_0 != k4_xboole_0(k1_xboole_0,k1_xboole_0)),
% 1.31/0.56    inference(superposition,[],[f76,f105])).
% 1.31/0.56  fof(f105,plain,(
% 1.31/0.56    k1_xboole_0 = k1_tarski(sK0)),
% 1.31/0.56    inference(subsumption_resolution,[],[f104,f103])).
% 1.31/0.56  fof(f103,plain,(
% 1.31/0.56    ( ! [X1] : (~r2_hidden(sK2(k1_tarski(sK0)),X1) | k1_xboole_0 = k1_tarski(sK0)) )),
% 1.31/0.56    inference(duplicate_literal_removal,[],[f102])).
% 1.31/0.56  fof(f102,plain,(
% 1.31/0.56    ( ! [X1] : (~r2_hidden(sK2(k1_tarski(sK0)),X1) | k1_xboole_0 = k1_tarski(sK0) | ~r2_hidden(sK2(k1_tarski(sK0)),X1)) )),
% 1.31/0.56    inference(forward_demodulation,[],[f97,f48])).
% 1.31/0.56  fof(f48,plain,(
% 1.31/0.56    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.31/0.56    inference(cnf_transformation,[],[f9])).
% 1.31/0.56  fof(f9,axiom,(
% 1.31/0.56    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.31/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 1.31/0.56  fof(f97,plain,(
% 1.31/0.56    ( ! [X1] : (k1_xboole_0 = k1_tarski(sK0) | ~r2_hidden(sK2(k1_tarski(sK0)),X1) | ~r2_hidden(sK2(k1_tarski(sK0)),k5_xboole_0(X1,k1_xboole_0))) )),
% 1.31/0.56    inference(resolution,[],[f81,f67])).
% 1.31/0.56  fof(f67,plain,(
% 1.31/0.56    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,k5_xboole_0(X1,X2))) )),
% 1.31/0.56    inference(cnf_transformation,[],[f43])).
% 1.31/0.56  fof(f43,plain,(
% 1.31/0.56    ! [X0,X1,X2] : ((r2_hidden(X0,k5_xboole_0(X1,X2)) | ((r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) & (r2_hidden(X0,X2) | ~r2_hidden(X0,X1)))) & (((~r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X2) | r2_hidden(X0,X1))) | ~r2_hidden(X0,k5_xboole_0(X1,X2))))),
% 1.31/0.56    inference(nnf_transformation,[],[f33])).
% 1.31/0.56  fof(f33,plain,(
% 1.31/0.56    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 1.31/0.56    inference(ennf_transformation,[],[f4])).
% 1.31/0.56  fof(f4,axiom,(
% 1.31/0.56    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 1.31/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).
% 1.31/0.56  fof(f81,plain,(
% 1.31/0.56    r2_hidden(sK2(k1_tarski(sK0)),k1_xboole_0) | k1_xboole_0 = k1_tarski(sK0)),
% 1.31/0.56    inference(resolution,[],[f79,f50])).
% 1.31/0.56  fof(f50,plain,(
% 1.31/0.56    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 1.31/0.56    inference(cnf_transformation,[],[f37])).
% 1.31/0.56  fof(f37,plain,(
% 1.31/0.56    ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0)),
% 1.31/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f31,f36])).
% 1.31/0.56  fof(f36,plain,(
% 1.31/0.56    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 1.31/0.56    introduced(choice_axiom,[])).
% 1.31/0.56  fof(f31,plain,(
% 1.31/0.56    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.31/0.56    inference(ennf_transformation,[],[f5])).
% 1.31/0.56  fof(f5,axiom,(
% 1.31/0.56    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.31/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 1.31/0.56  fof(f79,plain,(
% 1.31/0.56    ( ! [X0] : (~r2_hidden(X0,k1_tarski(sK0)) | r2_hidden(X0,k1_xboole_0)) )),
% 1.31/0.56    inference(resolution,[],[f78,f58])).
% 1.31/0.56  fof(f58,plain,(
% 1.31/0.56    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 1.31/0.56    inference(cnf_transformation,[],[f41])).
% 1.31/0.56  fof(f41,plain,(
% 1.31/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.31/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f39,f40])).
% 1.31/0.56  fof(f40,plain,(
% 1.31/0.56    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 1.31/0.56    introduced(choice_axiom,[])).
% 1.31/0.56  fof(f39,plain,(
% 1.31/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.31/0.56    inference(rectify,[],[f38])).
% 1.31/0.56  fof(f38,plain,(
% 1.31/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.31/0.56    inference(nnf_transformation,[],[f32])).
% 1.31/0.56  fof(f32,plain,(
% 1.31/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.31/0.56    inference(ennf_transformation,[],[f1])).
% 1.31/0.56  fof(f1,axiom,(
% 1.31/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.31/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.31/0.56  fof(f78,plain,(
% 1.31/0.56    r1_tarski(k1_tarski(sK0),k1_xboole_0)),
% 1.31/0.56    inference(superposition,[],[f53,f44])).
% 1.31/0.56  fof(f44,plain,(
% 1.31/0.56    k1_xboole_0 = k2_xboole_0(k1_tarski(sK0),sK1)),
% 1.31/0.56    inference(cnf_transformation,[],[f35])).
% 1.31/0.56  fof(f35,plain,(
% 1.31/0.56    k1_xboole_0 = k2_xboole_0(k1_tarski(sK0),sK1)),
% 1.31/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f30,f34])).
% 1.31/0.56  fof(f34,plain,(
% 1.31/0.56    ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1) => k1_xboole_0 = k2_xboole_0(k1_tarski(sK0),sK1)),
% 1.31/0.56    introduced(choice_axiom,[])).
% 1.31/0.56  fof(f30,plain,(
% 1.31/0.56    ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1)),
% 1.31/0.56    inference(ennf_transformation,[],[f27])).
% 1.31/0.56  fof(f27,negated_conjecture,(
% 1.31/0.56    ~! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 1.31/0.56    inference(negated_conjecture,[],[f26])).
% 1.31/0.56  fof(f26,conjecture,(
% 1.31/0.56    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 1.31/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 1.31/0.56  fof(f53,plain,(
% 1.31/0.56    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.31/0.56    inference(cnf_transformation,[],[f10])).
% 1.31/0.56  fof(f10,axiom,(
% 1.31/0.56    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.31/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.31/0.56  fof(f104,plain,(
% 1.31/0.56    ( ! [X2] : (k1_xboole_0 = k1_tarski(sK0) | r2_hidden(sK2(k1_tarski(sK0)),X2)) )),
% 1.31/0.56    inference(subsumption_resolution,[],[f98,f103])).
% 1.31/0.56  fof(f98,plain,(
% 1.31/0.56    ( ! [X2] : (k1_xboole_0 = k1_tarski(sK0) | r2_hidden(sK2(k1_tarski(sK0)),k5_xboole_0(k1_xboole_0,X2)) | r2_hidden(sK2(k1_tarski(sK0)),X2)) )),
% 1.31/0.56    inference(resolution,[],[f81,f68])).
% 1.31/0.56  fof(f68,plain,(
% 1.31/0.56    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) )),
% 1.31/0.56    inference(cnf_transformation,[],[f43])).
% 1.31/0.56  fof(f76,plain,(
% 1.31/0.56    ( ! [X1] : (k1_tarski(X1) != k4_xboole_0(k1_tarski(X1),k1_tarski(X1))) )),
% 1.31/0.56    inference(equality_resolution,[],[f61])).
% 1.31/0.56  fof(f61,plain,(
% 1.31/0.56    ( ! [X0,X1] : (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 1.31/0.56    inference(cnf_transformation,[],[f42])).
% 1.31/0.56  fof(f42,plain,(
% 1.31/0.56    ! [X0,X1] : ((k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) & (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))))),
% 1.31/0.56    inference(nnf_transformation,[],[f25])).
% 1.31/0.56  fof(f25,axiom,(
% 1.31/0.56    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 1.31/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 1.31/0.56  % SZS output end Proof for theBenchmark
% 1.31/0.56  % (7799)------------------------------
% 1.31/0.56  % (7799)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.56  % (7799)Termination reason: Refutation
% 1.31/0.56  
% 1.31/0.56  % (7799)Memory used [KB]: 1791
% 1.31/0.56  % (7799)Time elapsed: 0.133 s
% 1.31/0.56  % (7799)------------------------------
% 1.31/0.56  % (7799)------------------------------
% 1.31/0.56  % (7793)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.56  
% 1.31/0.56  % (7793)Memory used [KB]: 10618
% 1.31/0.56  % (7793)Time elapsed: 0.128 s
% 1.31/0.56  % (7793)------------------------------
% 1.31/0.56  % (7793)------------------------------
% 1.31/0.56  % (7775)Success in time 0.18 s
%------------------------------------------------------------------------------
