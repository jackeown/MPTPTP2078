%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:29:35 EST 2020

% Result     : Theorem 1.50s
% Output     : Refutation 1.50s
% Verified   : 
% Statistics : Number of formulae       :   38 ( 137 expanded)
%              Number of leaves         :    6 (  36 expanded)
%              Depth                    :   13
%              Number of atoms          :   82 ( 366 expanded)
%              Number of equality atoms :   15 (  83 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1020,plain,(
    $false ),
    inference(global_subsumption,[],[f560,f1014])).

fof(f1014,plain,(
    ~ sP5(sK3(k2_xboole_0(sK0,sK2),sK1),sK2,sK0) ),
    inference(unit_resulting_resolution,[],[f867,f868,f24])).

fof(f24,plain,(
    ! [X0,X3,X1] :
      ( ~ sP5(X3,X1,X0)
      | r2_hidden(X3,X1)
      | r2_hidden(X3,X0) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f868,plain,(
    ~ r2_hidden(sK3(k2_xboole_0(sK0,sK2),sK1),sK2) ),
    inference(unit_resulting_resolution,[],[f14,f282,f19])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f282,plain,(
    ~ r2_hidden(sK3(k2_xboole_0(sK0,sK2),sK1),sK1) ),
    inference(unit_resulting_resolution,[],[f237,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f237,plain,(
    ~ r1_tarski(k2_xboole_0(sK0,sK2),sK1) ),
    inference(global_subsumption,[],[f15,f220])).

fof(f220,plain,
    ( sK1 = k2_xboole_0(sK0,sK2)
    | ~ r1_tarski(k2_xboole_0(sK0,sK2),sK1) ),
    inference(superposition,[],[f58,f57])).

fof(f57,plain,(
    k2_xboole_0(sK0,sK2) = k2_xboole_0(sK1,k2_xboole_0(sK0,sK2)) ),
    inference(unit_resulting_resolution,[],[f45,f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f45,plain,(
    r1_tarski(sK1,k2_xboole_0(sK0,sK2)) ),
    inference(forward_demodulation,[],[f40,f17])).

fof(f17,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f40,plain,(
    r1_tarski(sK1,k2_xboole_0(sK2,sK0)) ),
    inference(unit_resulting_resolution,[],[f16,f34,f12])).

fof(f12,plain,(
    ! [X3] :
      ( ~ r1_tarski(sK2,X3)
      | ~ r1_tarski(sK0,X3)
      | r1_tarski(sK1,X3) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( k2_xboole_0(X0,X2) != X1
      & ! [X3] :
          ( r1_tarski(X1,X3)
          | ~ r1_tarski(X2,X3)
          | ~ r1_tarski(X0,X3) )
      & r1_tarski(X2,X1)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( k2_xboole_0(X0,X2) != X1
      & ! [X3] :
          ( r1_tarski(X1,X3)
          | ~ r1_tarski(X2,X3)
          | ~ r1_tarski(X0,X3) )
      & r1_tarski(X2,X1)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( ! [X3] :
              ( ( r1_tarski(X2,X3)
                & r1_tarski(X0,X3) )
             => r1_tarski(X1,X3) )
          & r1_tarski(X2,X1)
          & r1_tarski(X0,X1) )
       => k2_xboole_0(X0,X2) = X1 ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( ( ! [X3] :
            ( ( r1_tarski(X2,X3)
              & r1_tarski(X0,X3) )
           => r1_tarski(X1,X3) )
        & r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => k2_xboole_0(X0,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_xboole_1)).

fof(f34,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X1,X0)) ),
    inference(superposition,[],[f16,f17])).

fof(f16,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f58,plain,(
    ! [X2,X3] :
      ( k2_xboole_0(X3,X2) = X3
      | ~ r1_tarski(X2,X3) ) ),
    inference(superposition,[],[f18,f17])).

fof(f15,plain,(
    sK1 != k2_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f14,plain,(
    r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f867,plain,(
    ~ r2_hidden(sK3(k2_xboole_0(sK0,sK2),sK1),sK0) ),
    inference(unit_resulting_resolution,[],[f13,f282,f19])).

fof(f13,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f560,plain,(
    sP5(sK3(k2_xboole_0(sK0,sK2),sK1),sK2,sK0) ),
    inference(unit_resulting_resolution,[],[f237,f105])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( sP5(sK3(k2_xboole_0(X0,X1),X2),X1,X0)
      | r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(resolution,[],[f29,f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f29,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k2_xboole_0(X0,X1))
      | sP5(X3,X1,X0) ) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] :
      ( sP5(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n001.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:19:15 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.52  % (22943)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.52  % (22924)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.52  % (22924)Refutation not found, incomplete strategy% (22924)------------------------------
% 0.20/0.52  % (22924)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (22924)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (22924)Memory used [KB]: 1663
% 0.20/0.52  % (22924)Time elapsed: 0.103 s
% 0.20/0.52  % (22924)------------------------------
% 0.20/0.52  % (22924)------------------------------
% 0.20/0.53  % (22951)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.53  % (22935)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.53  % (22930)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.31/0.54  % (22926)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.31/0.54  % (22927)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.31/0.54  % (22953)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.31/0.54  % (22935)Refutation not found, incomplete strategy% (22935)------------------------------
% 1.31/0.54  % (22935)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.54  % (22935)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.54  
% 1.31/0.54  % (22935)Memory used [KB]: 10746
% 1.31/0.54  % (22935)Time elapsed: 0.116 s
% 1.31/0.54  % (22935)------------------------------
% 1.31/0.54  % (22935)------------------------------
% 1.31/0.54  % (22929)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.31/0.54  % (22947)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.31/0.54  % (22946)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.31/0.55  % (22946)Refutation not found, incomplete strategy% (22946)------------------------------
% 1.31/0.55  % (22946)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.55  % (22946)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.55  
% 1.31/0.55  % (22946)Memory used [KB]: 10618
% 1.31/0.55  % (22946)Time elapsed: 0.127 s
% 1.31/0.55  % (22946)------------------------------
% 1.31/0.55  % (22946)------------------------------
% 1.31/0.55  % (22941)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.31/0.55  % (22925)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.31/0.55  % (22940)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.31/0.55  % (22950)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.31/0.55  % (22945)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.31/0.55  % (22949)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.31/0.55  % (22945)Refutation not found, incomplete strategy% (22945)------------------------------
% 1.31/0.55  % (22945)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.55  % (22945)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.55  
% 1.31/0.55  % (22945)Memory used [KB]: 1663
% 1.31/0.55  % (22945)Time elapsed: 0.140 s
% 1.31/0.55  % (22945)------------------------------
% 1.31/0.55  % (22945)------------------------------
% 1.31/0.55  % (22937)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.50/0.55  % (22933)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.50/0.56  % (22938)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.50/0.56  % (22948)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.50/0.56  % (22933)Refutation not found, incomplete strategy% (22933)------------------------------
% 1.50/0.56  % (22933)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.56  % (22933)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.56  
% 1.50/0.56  % (22933)Memory used [KB]: 10618
% 1.50/0.56  % (22933)Time elapsed: 0.100 s
% 1.50/0.56  % (22933)------------------------------
% 1.50/0.56  % (22933)------------------------------
% 1.50/0.56  % (22934)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.50/0.56  % (22934)Refutation not found, incomplete strategy% (22934)------------------------------
% 1.50/0.56  % (22934)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.56  % (22934)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.56  
% 1.50/0.56  % (22934)Memory used [KB]: 10618
% 1.50/0.56  % (22934)Time elapsed: 0.147 s
% 1.50/0.56  % (22934)------------------------------
% 1.50/0.56  % (22934)------------------------------
% 1.50/0.56  % (22939)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.50/0.56  % (22931)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.50/0.56  % (22928)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.50/0.56  % (22952)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.50/0.57  % (22941)Refutation not found, incomplete strategy% (22941)------------------------------
% 1.50/0.57  % (22941)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.57  % (22941)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.57  
% 1.50/0.57  % (22941)Memory used [KB]: 10618
% 1.50/0.57  % (22941)Time elapsed: 0.148 s
% 1.50/0.57  % (22941)------------------------------
% 1.50/0.57  % (22941)------------------------------
% 1.50/0.57  % (22932)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.50/0.57  % (22936)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.50/0.57  % (22942)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.50/0.58  % (22944)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.50/0.58  % (22944)Refutation not found, incomplete strategy% (22944)------------------------------
% 1.50/0.58  % (22944)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.59  % (22944)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.59  
% 1.50/0.59  % (22944)Memory used [KB]: 10746
% 1.50/0.59  % (22944)Time elapsed: 0.152 s
% 1.50/0.59  % (22944)------------------------------
% 1.50/0.59  % (22944)------------------------------
% 1.50/0.61  % (22948)Refutation found. Thanks to Tanya!
% 1.50/0.61  % SZS status Theorem for theBenchmark
% 1.50/0.61  % SZS output start Proof for theBenchmark
% 1.50/0.61  fof(f1020,plain,(
% 1.50/0.61    $false),
% 1.50/0.61    inference(global_subsumption,[],[f560,f1014])).
% 1.50/0.61  fof(f1014,plain,(
% 1.50/0.61    ~sP5(sK3(k2_xboole_0(sK0,sK2),sK1),sK2,sK0)),
% 1.50/0.61    inference(unit_resulting_resolution,[],[f867,f868,f24])).
% 1.50/0.61  fof(f24,plain,(
% 1.50/0.61    ( ! [X0,X3,X1] : (~sP5(X3,X1,X0) | r2_hidden(X3,X1) | r2_hidden(X3,X0)) )),
% 1.50/0.61    inference(cnf_transformation,[],[f3])).
% 1.50/0.61  fof(f3,axiom,(
% 1.50/0.61    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 1.50/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).
% 1.50/0.61  fof(f868,plain,(
% 1.50/0.61    ~r2_hidden(sK3(k2_xboole_0(sK0,sK2),sK1),sK2)),
% 1.50/0.61    inference(unit_resulting_resolution,[],[f14,f282,f19])).
% 1.50/0.61  fof(f19,plain,(
% 1.50/0.61    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 1.50/0.61    inference(cnf_transformation,[],[f11])).
% 1.50/0.61  fof(f11,plain,(
% 1.50/0.61    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.50/0.61    inference(ennf_transformation,[],[f2])).
% 1.50/0.61  fof(f2,axiom,(
% 1.50/0.61    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.50/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.50/0.61  fof(f282,plain,(
% 1.50/0.61    ~r2_hidden(sK3(k2_xboole_0(sK0,sK2),sK1),sK1)),
% 1.50/0.61    inference(unit_resulting_resolution,[],[f237,f21])).
% 1.50/0.61  fof(f21,plain,(
% 1.50/0.61    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.50/0.61    inference(cnf_transformation,[],[f11])).
% 1.50/0.61  fof(f237,plain,(
% 1.50/0.61    ~r1_tarski(k2_xboole_0(sK0,sK2),sK1)),
% 1.50/0.61    inference(global_subsumption,[],[f15,f220])).
% 1.50/0.61  fof(f220,plain,(
% 1.50/0.61    sK1 = k2_xboole_0(sK0,sK2) | ~r1_tarski(k2_xboole_0(sK0,sK2),sK1)),
% 1.50/0.61    inference(superposition,[],[f58,f57])).
% 1.50/0.61  fof(f57,plain,(
% 1.50/0.61    k2_xboole_0(sK0,sK2) = k2_xboole_0(sK1,k2_xboole_0(sK0,sK2))),
% 1.50/0.61    inference(unit_resulting_resolution,[],[f45,f18])).
% 1.50/0.61  fof(f18,plain,(
% 1.50/0.61    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 1.50/0.61    inference(cnf_transformation,[],[f10])).
% 1.50/0.61  fof(f10,plain,(
% 1.50/0.61    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.50/0.61    inference(ennf_transformation,[],[f4])).
% 1.50/0.61  fof(f4,axiom,(
% 1.50/0.61    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.50/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.50/0.61  fof(f45,plain,(
% 1.50/0.61    r1_tarski(sK1,k2_xboole_0(sK0,sK2))),
% 1.50/0.61    inference(forward_demodulation,[],[f40,f17])).
% 1.50/0.61  fof(f17,plain,(
% 1.50/0.61    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.50/0.61    inference(cnf_transformation,[],[f1])).
% 1.50/0.61  fof(f1,axiom,(
% 1.50/0.61    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.50/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.50/0.61  fof(f40,plain,(
% 1.50/0.61    r1_tarski(sK1,k2_xboole_0(sK2,sK0))),
% 1.50/0.61    inference(unit_resulting_resolution,[],[f16,f34,f12])).
% 1.50/0.61  fof(f12,plain,(
% 1.50/0.61    ( ! [X3] : (~r1_tarski(sK2,X3) | ~r1_tarski(sK0,X3) | r1_tarski(sK1,X3)) )),
% 1.50/0.61    inference(cnf_transformation,[],[f9])).
% 1.50/0.61  fof(f9,plain,(
% 1.50/0.61    ? [X0,X1,X2] : (k2_xboole_0(X0,X2) != X1 & ! [X3] : (r1_tarski(X1,X3) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X3)) & r1_tarski(X2,X1) & r1_tarski(X0,X1))),
% 1.50/0.61    inference(flattening,[],[f8])).
% 1.50/0.61  fof(f8,plain,(
% 1.50/0.61    ? [X0,X1,X2] : (k2_xboole_0(X0,X2) != X1 & (! [X3] : (r1_tarski(X1,X3) | (~r1_tarski(X2,X3) | ~r1_tarski(X0,X3))) & r1_tarski(X2,X1) & r1_tarski(X0,X1)))),
% 1.50/0.61    inference(ennf_transformation,[],[f7])).
% 1.50/0.61  fof(f7,negated_conjecture,(
% 1.50/0.61    ~! [X0,X1,X2] : ((! [X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X3)) => r1_tarski(X1,X3)) & r1_tarski(X2,X1) & r1_tarski(X0,X1)) => k2_xboole_0(X0,X2) = X1)),
% 1.50/0.61    inference(negated_conjecture,[],[f6])).
% 1.50/0.61  fof(f6,conjecture,(
% 1.50/0.61    ! [X0,X1,X2] : ((! [X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X3)) => r1_tarski(X1,X3)) & r1_tarski(X2,X1) & r1_tarski(X0,X1)) => k2_xboole_0(X0,X2) = X1)),
% 1.50/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_xboole_1)).
% 1.50/0.61  fof(f34,plain,(
% 1.50/0.61    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X0))) )),
% 1.50/0.61    inference(superposition,[],[f16,f17])).
% 1.50/0.61  fof(f16,plain,(
% 1.50/0.61    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.50/0.61    inference(cnf_transformation,[],[f5])).
% 1.50/0.61  fof(f5,axiom,(
% 1.50/0.61    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.50/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.50/0.61  fof(f58,plain,(
% 1.50/0.61    ( ! [X2,X3] : (k2_xboole_0(X3,X2) = X3 | ~r1_tarski(X2,X3)) )),
% 1.50/0.61    inference(superposition,[],[f18,f17])).
% 1.50/0.61  fof(f15,plain,(
% 1.50/0.61    sK1 != k2_xboole_0(sK0,sK2)),
% 1.50/0.61    inference(cnf_transformation,[],[f9])).
% 1.50/0.61  fof(f14,plain,(
% 1.50/0.61    r1_tarski(sK2,sK1)),
% 1.50/0.61    inference(cnf_transformation,[],[f9])).
% 1.50/0.61  fof(f867,plain,(
% 1.50/0.61    ~r2_hidden(sK3(k2_xboole_0(sK0,sK2),sK1),sK0)),
% 1.50/0.61    inference(unit_resulting_resolution,[],[f13,f282,f19])).
% 1.50/0.61  fof(f13,plain,(
% 1.50/0.61    r1_tarski(sK0,sK1)),
% 1.50/0.61    inference(cnf_transformation,[],[f9])).
% 1.50/0.61  fof(f560,plain,(
% 1.50/0.61    sP5(sK3(k2_xboole_0(sK0,sK2),sK1),sK2,sK0)),
% 1.50/0.61    inference(unit_resulting_resolution,[],[f237,f105])).
% 1.50/0.61  fof(f105,plain,(
% 1.50/0.61    ( ! [X2,X0,X1] : (sP5(sK3(k2_xboole_0(X0,X1),X2),X1,X0) | r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 1.50/0.61    inference(resolution,[],[f29,f20])).
% 1.50/0.61  fof(f20,plain,(
% 1.50/0.61    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.50/0.61    inference(cnf_transformation,[],[f11])).
% 1.50/0.61  fof(f29,plain,(
% 1.50/0.61    ( ! [X0,X3,X1] : (~r2_hidden(X3,k2_xboole_0(X0,X1)) | sP5(X3,X1,X0)) )),
% 1.50/0.61    inference(equality_resolution,[],[f26])).
% 1.50/0.61  fof(f26,plain,(
% 1.50/0.61    ( ! [X2,X0,X3,X1] : (sP5(X3,X1,X0) | ~r2_hidden(X3,X2) | k2_xboole_0(X0,X1) != X2) )),
% 1.50/0.61    inference(cnf_transformation,[],[f3])).
% 1.50/0.61  % SZS output end Proof for theBenchmark
% 1.50/0.61  % (22948)------------------------------
% 1.50/0.61  % (22948)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.61  % (22948)Termination reason: Refutation
% 1.50/0.61  
% 1.50/0.61  % (22948)Memory used [KB]: 6780
% 1.50/0.61  % (22948)Time elapsed: 0.202 s
% 1.50/0.61  % (22948)------------------------------
% 1.50/0.61  % (22948)------------------------------
% 1.50/0.62  % (22923)Success in time 0.245 s
%------------------------------------------------------------------------------
