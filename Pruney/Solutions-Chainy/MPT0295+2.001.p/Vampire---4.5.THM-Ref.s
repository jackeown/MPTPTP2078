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
% DateTime   : Thu Dec  3 12:41:49 EST 2020

% Result     : Theorem 7.17s
% Output     : Refutation 7.17s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 106 expanded)
%              Number of leaves         :   12 (  28 expanded)
%              Depth                    :   13
%              Number of atoms          :  138 ( 271 expanded)
%              Number of equality atoms :   21 (  57 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4951,plain,(
    $false ),
    inference(resolution,[],[f4934,f775])).

fof(f775,plain,(
    ~ r1_tarski(k1_tarski(sK3),k2_zfmisc_1(sK1,sK2)) ),
    inference(resolution,[],[f732,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f732,plain,(
    ~ r2_hidden(sK3,k2_zfmisc_1(sK1,sK2)) ),
    inference(resolution,[],[f731,f84])).

fof(f84,plain,(
    ! [X0,X3,X1] :
      ( sP8(X3,X1,X0)
      | ~ r2_hidden(X3,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( sP8(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(f731,plain,(
    ~ sP8(sK3,sK2,sK1) ),
    inference(duplicate_literal_removal,[],[f724])).

fof(f724,plain,
    ( ~ sP8(sK3,sK2,sK1)
    | ~ sP8(sK3,sK2,sK1) ),
    inference(resolution,[],[f393,f45])).

fof(f45,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(sK9(X0,X1,X3),X0)
      | ~ sP8(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f393,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK9(X0,sK2,sK3),sK1)
      | ~ sP8(sK3,sK2,X0) ) ),
    inference(duplicate_literal_removal,[],[f386])).

fof(f386,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK9(X0,sK2,sK3),sK1)
      | ~ sP8(sK3,sK2,X0)
      | ~ sP8(sK3,sK2,X0) ) ),
    inference(resolution,[],[f196,f46])).

fof(f46,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(sK10(X0,X1,X3),X1)
      | ~ sP8(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f196,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK10(X0,X1,sK3),sK2)
      | ~ r2_hidden(sK9(X0,X1,sK3),sK1)
      | ~ sP8(sK3,X1,X0) ) ),
    inference(equality_resolution,[],[f108])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( sK3 != X2
      | ~ r2_hidden(sK10(X0,X1,X2),sK2)
      | ~ r2_hidden(sK9(X0,X1,X2),sK1)
      | ~ sP8(X2,X1,X0) ) ),
    inference(superposition,[],[f28,f47])).

fof(f47,plain,(
    ! [X0,X3,X1] :
      ( k4_tarski(sK9(X0,X1,X3),sK10(X0,X1,X3)) = X3
      | ~ sP8(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f28,plain,(
    ! [X4,X5] :
      ( k4_tarski(X4,X5) != sK3
      | ~ r2_hidden(X5,sK2)
      | ~ r2_hidden(X4,sK1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4,X5] :
          ( k4_tarski(X4,X5) != X3
          | ~ r2_hidden(X5,X2)
          | ~ r2_hidden(X4,X1) )
      & r2_hidden(X3,X0)
      & r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ~ ( ! [X4,X5] :
              ~ ( k4_tarski(X4,X5) = X3
                & r2_hidden(X5,X2)
                & r2_hidden(X4,X1) )
          & r2_hidden(X3,X0)
          & r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1,X2,X3] :
      ~ ( ! [X4,X5] :
            ~ ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X2)
              & r2_hidden(X4,X1) )
        & r2_hidden(X3,X0)
        & r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_zfmisc_1)).

fof(f4934,plain,(
    ! [X2] : r1_tarski(k1_tarski(sK3),X2) ),
    inference(subsumption_resolution,[],[f4928,f3603])).

fof(f3603,plain,(
    r1_xboole_0(sK0,k1_tarski(sK3)) ),
    inference(resolution,[],[f916,f732])).

fof(f916,plain,(
    ! [X0] :
      ( r2_hidden(X0,k2_zfmisc_1(sK1,sK2))
      | r1_xboole_0(sK0,k1_tarski(X0)) ) ),
    inference(resolution,[],[f273,f83])).

fof(f83,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f273,plain,(
    ! [X14,X13] :
      ( ~ r1_tarski(k2_zfmisc_1(sK1,sK2),X13)
      | r1_xboole_0(sK0,k1_tarski(X14))
      | r2_hidden(X14,X13) ) ),
    inference(superposition,[],[f142,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k4_xboole_0(X0,k1_tarski(X1)) = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f142,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_zfmisc_1(sK1,sK2),k4_xboole_0(X1,X0))
      | r1_xboole_0(sK0,X0) ) ),
    inference(resolution,[],[f99,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f99,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(k2_zfmisc_1(sK1,sK2),X0)
      | r1_xboole_0(sK0,X0) ) ),
    inference(resolution,[],[f29,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_xboole_0(X1,X2)
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f29,plain,(
    r1_tarski(sK0,k2_zfmisc_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f21])).

fof(f4928,plain,(
    ! [X2] :
      ( ~ r1_xboole_0(sK0,k1_tarski(sK3))
      | r1_tarski(k1_tarski(sK3),X2) ) ),
    inference(resolution,[],[f1298,f79])).

fof(f79,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1))) ),
    inference(definition_unfolding,[],[f67,f72])).

fof(f72,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f71,f70])).

fof(f70,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f71,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f67,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f1298,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tarski(sK3),k3_tarski(k1_enumset1(X1,X1,X0)))
      | ~ r1_xboole_0(sK0,X1)
      | r1_tarski(k1_tarski(sK3),X0) ) ),
    inference(superposition,[],[f168,f73])).

fof(f73,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(definition_unfolding,[],[f41,f70,f70])).

fof(f41,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f168,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(k1_tarski(sK3),k3_tarski(k1_enumset1(X3,X3,X2)))
      | ~ r1_xboole_0(sK0,X2)
      | r1_tarski(k1_tarski(sK3),X3) ) ),
    inference(resolution,[],[f105,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X2)))
      | ~ r1_xboole_0(X0,X2)
      | r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f63,f72])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,k2_xboole_0(X1,X2)) )
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_xboole_1)).

fof(f105,plain,(
    ! [X0] :
      ( r1_xboole_0(k1_tarski(sK3),X0)
      | ~ r1_xboole_0(sK0,X0) ) ),
    inference(resolution,[],[f94,f64])).

fof(f94,plain,(
    r1_tarski(k1_tarski(sK3),sK0) ),
    inference(resolution,[],[f30,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f30,plain,(
    r2_hidden(sK3,sK0) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_vampire %s %d
% 0.13/0.32  % Computer   : n024.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % WCLimit    : 600
% 0.13/0.32  % DateTime   : Tue Dec  1 11:55:51 EST 2020
% 0.13/0.32  % CPUTime    : 
% 0.18/0.48  % (31748)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.18/0.48  % (31758)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.18/0.48  % (31764)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.18/0.48  % (31750)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.18/0.49  % (31750)Refutation not found, incomplete strategy% (31750)------------------------------
% 0.18/0.49  % (31750)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.49  % (31750)Termination reason: Refutation not found, incomplete strategy
% 0.18/0.49  
% 0.18/0.49  % (31750)Memory used [KB]: 1791
% 0.18/0.49  % (31750)Time elapsed: 0.060 s
% 0.18/0.49  % (31750)------------------------------
% 0.18/0.49  % (31750)------------------------------
% 0.18/0.49  % (31742)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.18/0.50  % (31756)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.18/0.51  % (31739)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.18/0.51  % (31761)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.18/0.51  % (31765)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.18/0.51  % (31740)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.18/0.51  % (31760)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.18/0.51  % (31765)Refutation not found, incomplete strategy% (31765)------------------------------
% 0.18/0.51  % (31765)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.51  % (31765)Termination reason: Refutation not found, incomplete strategy
% 0.18/0.51  
% 0.18/0.51  % (31765)Memory used [KB]: 1663
% 0.18/0.51  % (31765)Time elapsed: 0.137 s
% 0.18/0.51  % (31765)------------------------------
% 0.18/0.51  % (31765)------------------------------
% 0.18/0.51  % (31741)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.18/0.52  % (31737)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.18/0.52  % (31762)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.18/0.52  % (31753)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.18/0.52  % (31736)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.18/0.52  % (31738)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.18/0.52  % (31754)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.18/0.52  % (31757)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.18/0.53  % (31752)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.18/0.53  % (31752)Refutation not found, incomplete strategy% (31752)------------------------------
% 0.18/0.53  % (31752)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.53  % (31752)Termination reason: Refutation not found, incomplete strategy
% 0.18/0.53  
% 0.18/0.53  % (31752)Memory used [KB]: 10746
% 0.18/0.53  % (31752)Time elapsed: 0.146 s
% 0.18/0.53  % (31752)------------------------------
% 0.18/0.53  % (31752)------------------------------
% 0.18/0.53  % (31749)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.18/0.53  % (31746)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.18/0.53  % (31745)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.18/0.53  % (31744)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.57/0.54  % (31743)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.57/0.54  % (31763)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.57/0.55  % (31751)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.57/0.55  % (31755)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.57/0.55  % (31759)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.57/0.56  % (31747)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.76/0.61  % (31766)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.24/0.65  % (31739)Refutation not found, incomplete strategy% (31739)------------------------------
% 2.24/0.65  % (31739)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.24/0.65  % (31739)Termination reason: Refutation not found, incomplete strategy
% 2.24/0.65  
% 2.24/0.65  % (31739)Memory used [KB]: 6140
% 2.24/0.65  % (31739)Time elapsed: 0.265 s
% 2.24/0.65  % (31739)------------------------------
% 2.24/0.65  % (31739)------------------------------
% 2.24/0.66  % (31768)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 2.53/0.67  % (31767)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 3.32/0.78  % (31738)Time limit reached!
% 3.32/0.78  % (31738)------------------------------
% 3.32/0.78  % (31738)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.32/0.79  % (31760)Time limit reached!
% 3.32/0.79  % (31760)------------------------------
% 3.32/0.79  % (31760)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.32/0.79  % (31760)Termination reason: Time limit
% 3.32/0.79  
% 3.32/0.79  % (31760)Memory used [KB]: 13304
% 3.32/0.79  % (31760)Time elapsed: 0.406 s
% 3.32/0.79  % (31760)------------------------------
% 3.32/0.79  % (31760)------------------------------
% 3.32/0.79  % (31738)Termination reason: Time limit
% 3.32/0.79  % (31738)Termination phase: Saturation
% 3.32/0.79  
% 3.32/0.79  % (31738)Memory used [KB]: 6780
% 3.32/0.79  % (31738)Time elapsed: 0.400 s
% 3.32/0.79  % (31738)------------------------------
% 3.32/0.79  % (31738)------------------------------
% 3.32/0.83  % (31769)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 4.01/0.89  % (31770)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 4.01/0.92  % (31770)Refutation not found, incomplete strategy% (31770)------------------------------
% 4.01/0.92  % (31770)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.01/0.92  % (31770)Termination reason: Refutation not found, incomplete strategy
% 4.01/0.92  
% 4.01/0.92  % (31770)Memory used [KB]: 10746
% 4.01/0.92  % (31770)Time elapsed: 0.116 s
% 4.01/0.92  % (31770)------------------------------
% 4.01/0.92  % (31770)------------------------------
% 4.52/0.93  % (31771)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 4.52/0.95  % (31742)Time limit reached!
% 4.52/0.95  % (31742)------------------------------
% 4.52/0.95  % (31742)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.52/0.95  % (31742)Termination reason: Time limit
% 4.52/0.95  
% 4.52/0.95  % (31742)Memory used [KB]: 16247
% 4.52/0.95  % (31742)Time elapsed: 0.524 s
% 4.52/0.95  % (31742)------------------------------
% 4.52/0.95  % (31742)------------------------------
% 4.80/1.01  % (31743)Time limit reached!
% 4.80/1.01  % (31743)------------------------------
% 4.80/1.01  % (31743)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.80/1.01  % (31743)Termination reason: Time limit
% 4.80/1.01  
% 4.80/1.01  % (31743)Memory used [KB]: 6012
% 4.80/1.01  % (31743)Time elapsed: 0.628 s
% 4.80/1.01  % (31743)------------------------------
% 4.80/1.01  % (31743)------------------------------
% 5.25/1.05  % (31773)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 5.25/1.06  % (31772)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 5.80/1.13  % (31774)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 6.51/1.20  % (31737)Time limit reached!
% 6.51/1.20  % (31737)------------------------------
% 6.51/1.20  % (31737)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.51/1.20  % (31737)Termination reason: Time limit
% 6.51/1.20  
% 6.51/1.20  % (31737)Memory used [KB]: 7419
% 6.51/1.20  % (31737)Time elapsed: 0.816 s
% 6.51/1.20  % (31737)------------------------------
% 6.51/1.20  % (31737)------------------------------
% 7.17/1.28  % (31771)Refutation found. Thanks to Tanya!
% 7.17/1.28  % SZS status Theorem for theBenchmark
% 7.17/1.28  % SZS output start Proof for theBenchmark
% 7.17/1.28  fof(f4951,plain,(
% 7.17/1.28    $false),
% 7.17/1.28    inference(resolution,[],[f4934,f775])).
% 7.17/1.28  fof(f775,plain,(
% 7.17/1.28    ~r1_tarski(k1_tarski(sK3),k2_zfmisc_1(sK1,sK2))),
% 7.17/1.28    inference(resolution,[],[f732,f62])).
% 7.17/1.28  fof(f62,plain,(
% 7.17/1.28    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)) )),
% 7.17/1.28    inference(cnf_transformation,[],[f16])).
% 7.17/1.28  fof(f16,axiom,(
% 7.17/1.28    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 7.17/1.28    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 7.17/1.28  fof(f732,plain,(
% 7.17/1.28    ~r2_hidden(sK3,k2_zfmisc_1(sK1,sK2))),
% 7.17/1.28    inference(resolution,[],[f731,f84])).
% 7.17/1.28  fof(f84,plain,(
% 7.17/1.28    ( ! [X0,X3,X1] : (sP8(X3,X1,X0) | ~r2_hidden(X3,k2_zfmisc_1(X0,X1))) )),
% 7.17/1.28    inference(equality_resolution,[],[f49])).
% 7.17/1.28  fof(f49,plain,(
% 7.17/1.28    ( ! [X2,X0,X3,X1] : (sP8(X3,X1,X0) | ~r2_hidden(X3,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 7.17/1.28    inference(cnf_transformation,[],[f15])).
% 7.17/1.28  fof(f15,axiom,(
% 7.17/1.28    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 7.17/1.28    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).
% 7.17/1.28  fof(f731,plain,(
% 7.17/1.28    ~sP8(sK3,sK2,sK1)),
% 7.17/1.28    inference(duplicate_literal_removal,[],[f724])).
% 7.17/1.28  fof(f724,plain,(
% 7.17/1.28    ~sP8(sK3,sK2,sK1) | ~sP8(sK3,sK2,sK1)),
% 7.17/1.28    inference(resolution,[],[f393,f45])).
% 7.17/1.28  fof(f45,plain,(
% 7.17/1.28    ( ! [X0,X3,X1] : (r2_hidden(sK9(X0,X1,X3),X0) | ~sP8(X3,X1,X0)) )),
% 7.17/1.28    inference(cnf_transformation,[],[f15])).
% 7.17/1.28  fof(f393,plain,(
% 7.17/1.28    ( ! [X0] : (~r2_hidden(sK9(X0,sK2,sK3),sK1) | ~sP8(sK3,sK2,X0)) )),
% 7.17/1.28    inference(duplicate_literal_removal,[],[f386])).
% 7.17/1.28  fof(f386,plain,(
% 7.17/1.28    ( ! [X0] : (~r2_hidden(sK9(X0,sK2,sK3),sK1) | ~sP8(sK3,sK2,X0) | ~sP8(sK3,sK2,X0)) )),
% 7.17/1.28    inference(resolution,[],[f196,f46])).
% 7.17/1.28  fof(f46,plain,(
% 7.17/1.28    ( ! [X0,X3,X1] : (r2_hidden(sK10(X0,X1,X3),X1) | ~sP8(X3,X1,X0)) )),
% 7.17/1.28    inference(cnf_transformation,[],[f15])).
% 7.17/1.28  fof(f196,plain,(
% 7.17/1.28    ( ! [X0,X1] : (~r2_hidden(sK10(X0,X1,sK3),sK2) | ~r2_hidden(sK9(X0,X1,sK3),sK1) | ~sP8(sK3,X1,X0)) )),
% 7.17/1.28    inference(equality_resolution,[],[f108])).
% 7.17/1.28  fof(f108,plain,(
% 7.17/1.28    ( ! [X2,X0,X1] : (sK3 != X2 | ~r2_hidden(sK10(X0,X1,X2),sK2) | ~r2_hidden(sK9(X0,X1,X2),sK1) | ~sP8(X2,X1,X0)) )),
% 7.17/1.28    inference(superposition,[],[f28,f47])).
% 7.17/1.28  fof(f47,plain,(
% 7.17/1.28    ( ! [X0,X3,X1] : (k4_tarski(sK9(X0,X1,X3),sK10(X0,X1,X3)) = X3 | ~sP8(X3,X1,X0)) )),
% 7.17/1.28    inference(cnf_transformation,[],[f15])).
% 7.17/1.28  fof(f28,plain,(
% 7.17/1.28    ( ! [X4,X5] : (k4_tarski(X4,X5) != sK3 | ~r2_hidden(X5,sK2) | ~r2_hidden(X4,sK1)) )),
% 7.17/1.28    inference(cnf_transformation,[],[f21])).
% 7.17/1.28  fof(f21,plain,(
% 7.17/1.28    ? [X0,X1,X2,X3] : (! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X2) | ~r2_hidden(X4,X1)) & r2_hidden(X3,X0) & r1_tarski(X0,k2_zfmisc_1(X1,X2)))),
% 7.17/1.28    inference(ennf_transformation,[],[f20])).
% 7.17/1.28  fof(f20,negated_conjecture,(
% 7.17/1.28    ~! [X0,X1,X2,X3] : ~(! [X4,X5] : ~(k4_tarski(X4,X5) = X3 & r2_hidden(X5,X2) & r2_hidden(X4,X1)) & r2_hidden(X3,X0) & r1_tarski(X0,k2_zfmisc_1(X1,X2)))),
% 7.17/1.28    inference(negated_conjecture,[],[f19])).
% 7.17/1.28  fof(f19,conjecture,(
% 7.17/1.28    ! [X0,X1,X2,X3] : ~(! [X4,X5] : ~(k4_tarski(X4,X5) = X3 & r2_hidden(X5,X2) & r2_hidden(X4,X1)) & r2_hidden(X3,X0) & r1_tarski(X0,k2_zfmisc_1(X1,X2)))),
% 7.17/1.28    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_zfmisc_1)).
% 7.17/1.28  fof(f4934,plain,(
% 7.17/1.28    ( ! [X2] : (r1_tarski(k1_tarski(sK3),X2)) )),
% 7.17/1.28    inference(subsumption_resolution,[],[f4928,f3603])).
% 7.17/1.28  fof(f3603,plain,(
% 7.17/1.28    r1_xboole_0(sK0,k1_tarski(sK3))),
% 7.17/1.28    inference(resolution,[],[f916,f732])).
% 7.17/1.28  fof(f916,plain,(
% 7.17/1.28    ( ! [X0] : (r2_hidden(X0,k2_zfmisc_1(sK1,sK2)) | r1_xboole_0(sK0,k1_tarski(X0))) )),
% 7.17/1.28    inference(resolution,[],[f273,f83])).
% 7.17/1.28  fof(f83,plain,(
% 7.17/1.28    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.17/1.28    inference(equality_resolution,[],[f38])).
% 7.17/1.28  fof(f38,plain,(
% 7.17/1.28    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 7.17/1.28    inference(cnf_transformation,[],[f5])).
% 7.17/1.28  fof(f5,axiom,(
% 7.17/1.28    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.17/1.28    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 7.17/1.28  fof(f273,plain,(
% 7.17/1.28    ( ! [X14,X13] : (~r1_tarski(k2_zfmisc_1(sK1,sK2),X13) | r1_xboole_0(sK0,k1_tarski(X14)) | r2_hidden(X14,X13)) )),
% 7.17/1.28    inference(superposition,[],[f142,f59])).
% 7.17/1.28  fof(f59,plain,(
% 7.17/1.28    ( ! [X0,X1] : (r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) = X0) )),
% 7.17/1.28    inference(cnf_transformation,[],[f18])).
% 7.17/1.28  fof(f18,axiom,(
% 7.17/1.28    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 7.17/1.28    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 7.17/1.28  fof(f142,plain,(
% 7.17/1.28    ( ! [X0,X1] : (~r1_tarski(k2_zfmisc_1(sK1,sK2),k4_xboole_0(X1,X0)) | r1_xboole_0(sK0,X0)) )),
% 7.17/1.28    inference(resolution,[],[f99,f66])).
% 7.17/1.28  fof(f66,plain,(
% 7.17/1.28    ( ! [X2,X0,X1] : (~r1_tarski(X0,k4_xboole_0(X1,X2)) | r1_xboole_0(X0,X2)) )),
% 7.17/1.28    inference(cnf_transformation,[],[f27])).
% 7.17/1.28  fof(f27,plain,(
% 7.17/1.28    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 7.17/1.28    inference(ennf_transformation,[],[f6])).
% 7.17/1.28  fof(f6,axiom,(
% 7.17/1.28    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 7.17/1.28    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).
% 7.17/1.28  fof(f99,plain,(
% 7.17/1.28    ( ! [X0] : (~r1_xboole_0(k2_zfmisc_1(sK1,sK2),X0) | r1_xboole_0(sK0,X0)) )),
% 7.17/1.28    inference(resolution,[],[f29,f64])).
% 7.17/1.28  fof(f64,plain,(
% 7.17/1.28    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_xboole_0(X1,X2) | r1_xboole_0(X0,X2)) )),
% 7.17/1.28    inference(cnf_transformation,[],[f26])).
% 7.17/1.28  fof(f26,plain,(
% 7.17/1.28    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 7.17/1.28    inference(flattening,[],[f25])).
% 7.17/1.28  fof(f25,plain,(
% 7.17/1.28    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 7.17/1.28    inference(ennf_transformation,[],[f10])).
% 7.17/1.28  fof(f10,axiom,(
% 7.17/1.28    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 7.17/1.28    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).
% 7.17/1.28  fof(f29,plain,(
% 7.17/1.28    r1_tarski(sK0,k2_zfmisc_1(sK1,sK2))),
% 7.17/1.28    inference(cnf_transformation,[],[f21])).
% 7.17/1.28  fof(f4928,plain,(
% 7.17/1.28    ( ! [X2] : (~r1_xboole_0(sK0,k1_tarski(sK3)) | r1_tarski(k1_tarski(sK3),X2)) )),
% 7.17/1.28    inference(resolution,[],[f1298,f79])).
% 7.17/1.28  fof(f79,plain,(
% 7.17/1.28    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1)))) )),
% 7.17/1.28    inference(definition_unfolding,[],[f67,f72])).
% 7.17/1.28  fof(f72,plain,(
% 7.17/1.28    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 7.17/1.28    inference(definition_unfolding,[],[f71,f70])).
% 7.17/1.28  fof(f70,plain,(
% 7.17/1.28    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 7.17/1.28    inference(cnf_transformation,[],[f14])).
% 7.17/1.28  fof(f14,axiom,(
% 7.17/1.28    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 7.17/1.28    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 7.17/1.28  fof(f71,plain,(
% 7.17/1.28    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 7.17/1.28    inference(cnf_transformation,[],[f17])).
% 7.17/1.28  fof(f17,axiom,(
% 7.17/1.28    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 7.17/1.28    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 7.17/1.28  fof(f67,plain,(
% 7.17/1.28    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 7.17/1.28    inference(cnf_transformation,[],[f12])).
% 7.17/1.28  fof(f12,axiom,(
% 7.17/1.28    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 7.17/1.28    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 7.17/1.28  fof(f1298,plain,(
% 7.17/1.28    ( ! [X0,X1] : (~r1_tarski(k1_tarski(sK3),k3_tarski(k1_enumset1(X1,X1,X0))) | ~r1_xboole_0(sK0,X1) | r1_tarski(k1_tarski(sK3),X0)) )),
% 7.17/1.28    inference(superposition,[],[f168,f73])).
% 7.17/1.28  fof(f73,plain,(
% 7.17/1.28    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) )),
% 7.17/1.28    inference(definition_unfolding,[],[f41,f70,f70])).
% 7.17/1.28  fof(f41,plain,(
% 7.17/1.28    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 7.17/1.28    inference(cnf_transformation,[],[f13])).
% 7.17/1.28  fof(f13,axiom,(
% 7.17/1.28    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 7.17/1.28    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 7.17/1.28  fof(f168,plain,(
% 7.17/1.28    ( ! [X2,X3] : (~r1_tarski(k1_tarski(sK3),k3_tarski(k1_enumset1(X3,X3,X2))) | ~r1_xboole_0(sK0,X2) | r1_tarski(k1_tarski(sK3),X3)) )),
% 7.17/1.28    inference(resolution,[],[f105,f78])).
% 7.17/1.28  fof(f78,plain,(
% 7.17/1.28    ( ! [X2,X0,X1] : (~r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X2))) | ~r1_xboole_0(X0,X2) | r1_tarski(X0,X1)) )),
% 7.17/1.28    inference(definition_unfolding,[],[f63,f72])).
% 7.17/1.28  fof(f63,plain,(
% 7.17/1.28    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | r1_tarski(X0,X1)) )),
% 7.17/1.28    inference(cnf_transformation,[],[f24])).
% 7.17/1.28  fof(f24,plain,(
% 7.17/1.28    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 7.17/1.28    inference(flattening,[],[f23])).
% 7.17/1.28  fof(f23,plain,(
% 7.17/1.28    ! [X0,X1,X2] : (r1_tarski(X0,X1) | (~r1_xboole_0(X0,X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))))),
% 7.17/1.28    inference(ennf_transformation,[],[f11])).
% 7.17/1.28  fof(f11,axiom,(
% 7.17/1.28    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => r1_tarski(X0,X1))),
% 7.17/1.28    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_xboole_1)).
% 7.17/1.28  fof(f105,plain,(
% 7.17/1.28    ( ! [X0] : (r1_xboole_0(k1_tarski(sK3),X0) | ~r1_xboole_0(sK0,X0)) )),
% 7.17/1.28    inference(resolution,[],[f94,f64])).
% 7.17/1.28  fof(f94,plain,(
% 7.17/1.28    r1_tarski(k1_tarski(sK3),sK0)),
% 7.17/1.28    inference(resolution,[],[f30,f61])).
% 7.17/1.28  fof(f61,plain,(
% 7.17/1.28    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k1_tarski(X0),X1)) )),
% 7.17/1.28    inference(cnf_transformation,[],[f16])).
% 7.17/1.28  fof(f30,plain,(
% 7.17/1.28    r2_hidden(sK3,sK0)),
% 7.17/1.28    inference(cnf_transformation,[],[f21])).
% 7.17/1.28  % SZS output end Proof for theBenchmark
% 7.17/1.28  % (31771)------------------------------
% 7.17/1.28  % (31771)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.17/1.28  % (31771)Termination reason: Refutation
% 7.17/1.28  
% 7.17/1.28  % (31771)Memory used [KB]: 4093
% 7.17/1.28  % (31771)Time elapsed: 0.432 s
% 7.17/1.28  % (31771)------------------------------
% 7.17/1.28  % (31771)------------------------------
% 7.17/1.29  % (31735)Success in time 0.946 s
%------------------------------------------------------------------------------
