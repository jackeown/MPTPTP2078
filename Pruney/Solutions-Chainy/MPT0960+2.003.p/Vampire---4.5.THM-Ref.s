%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:06 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   43 (  58 expanded)
%              Number of leaves         :   11 (  17 expanded)
%              Depth                    :   12
%              Number of atoms          :   75 ( 104 expanded)
%              Number of equality atoms :   21 (  36 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f94,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f51,f93])).

fof(f93,plain,(
    spl1_1 ),
    inference(avatar_contradiction_clause,[],[f90])).

fof(f90,plain,
    ( $false
    | spl1_1 ),
    inference(unit_resulting_resolution,[],[f45,f50,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_wellord2(X1),k2_zfmisc_1(X1,X1))
      | ~ r1_tarski(X1,X0) ) ),
    inference(global_subsumption,[],[f34,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_wellord2(X1),k2_zfmisc_1(X1,X1))
      | ~ v1_relat_1(k1_wellord2(X0))
      | ~ r1_tarski(X1,X0) ) ),
    inference(superposition,[],[f78,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

% (7637)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% (7622)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% (7635)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% (7635)Refutation not found, incomplete strategy% (7635)------------------------------
% (7635)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (7635)Termination reason: Refutation not found, incomplete strategy

% (7635)Memory used [KB]: 10618
% (7635)Time elapsed: 0.169 s
% (7635)------------------------------
% (7635)------------------------------
% (7624)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% (7632)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% (7640)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% (7626)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% (7641)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% (7642)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% (7633)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% (7645)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% (7633)Refutation not found, incomplete strategy% (7633)------------------------------
% (7633)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (7633)Termination reason: Refutation not found, incomplete strategy

% (7633)Memory used [KB]: 1663
% (7633)Time elapsed: 0.152 s
% (7633)------------------------------
% (7633)------------------------------
fof(f20,plain,(
    ! [X0,X1] :
      ( k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_wellord2)).

fof(f78,plain,(
    ! [X4,X3] :
      ( r1_tarski(k2_wellord1(X3,X4),k2_zfmisc_1(X4,X4))
      | ~ v1_relat_1(X3) ) ),
    inference(superposition,[],[f64,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k2_wellord1(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,k2_zfmisc_1(X1,X1)))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f33,f39])).

fof(f39,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f35,f38])).

fof(f38,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f35,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f33,plain,(
    ! [X0,X1] :
      ( k2_wellord1(X0,X1) = k3_xboole_0(X0,k2_zfmisc_1(X1,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] : k2_wellord1(X0,X1) = k3_xboole_0(X0,k2_zfmisc_1(X1,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k2_wellord1(X0,X1) = k3_xboole_0(X0,k2_zfmisc_1(X1,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_wellord1)).

fof(f64,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k1_enumset1(X1,X1,X0)),X0) ),
    inference(superposition,[],[f59,f44])).

fof(f44,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(definition_unfolding,[],[f36,f38,f38])).

fof(f36,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f59,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X1)),X0) ),
    inference(resolution,[],[f41,f45])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k1_setfam_1(k1_enumset1(X1,X1,X2)))
      | r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f27,f39])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_xboole_1)).

fof(f34,plain,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).

fof(f50,plain,
    ( ~ r1_tarski(k1_wellord2(sK0),k2_zfmisc_1(sK0,sK0))
    | spl1_1 ),
    inference(avatar_component_clause,[],[f48])).

fof(f48,plain,
    ( spl1_1
  <=> r1_tarski(k1_wellord2(sK0),k2_zfmisc_1(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f45,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f51,plain,(
    ~ spl1_1 ),
    inference(avatar_split_clause,[],[f26,f48])).

fof(f26,plain,(
    ~ r1_tarski(k1_wellord2(sK0),k2_zfmisc_1(sK0,sK0)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ~ r1_tarski(k1_wellord2(sK0),k2_zfmisc_1(sK0,sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f22])).

fof(f22,plain,
    ( ? [X0] : ~ r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0))
   => ~ r1_tarski(k1_wellord2(sK0),k2_zfmisc_1(sK0,sK0)) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0] : ~ r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0)) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] : r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0)) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] : r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_wellord2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:29:19 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (7630)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.49  % (7646)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.49  % (7646)Refutation not found, incomplete strategy% (7646)------------------------------
% 0.21/0.49  % (7646)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (7646)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (7646)Memory used [KB]: 6140
% 0.21/0.49  % (7646)Time elapsed: 0.070 s
% 0.21/0.49  % (7646)------------------------------
% 0.21/0.49  % (7646)------------------------------
% 0.21/0.52  % (7627)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.54  % (7634)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.55  % (7629)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.55  % (7629)Refutation not found, incomplete strategy% (7629)------------------------------
% 0.21/0.55  % (7629)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (7629)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (7629)Memory used [KB]: 10618
% 0.21/0.55  % (7629)Time elapsed: 0.136 s
% 0.21/0.55  % (7629)------------------------------
% 0.21/0.55  % (7629)------------------------------
% 0.21/0.55  % (7620)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.55  % (7617)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.56  % (7618)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.57  % (7618)Refutation not found, incomplete strategy% (7618)------------------------------
% 0.21/0.57  % (7618)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (7618)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (7618)Memory used [KB]: 1663
% 0.21/0.57  % (7618)Time elapsed: 0.157 s
% 0.21/0.57  % (7618)------------------------------
% 0.21/0.57  % (7618)------------------------------
% 0.21/0.57  % (7643)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.57  % (7643)Refutation found. Thanks to Tanya!
% 0.21/0.57  % SZS status Theorem for theBenchmark
% 0.21/0.57  % SZS output start Proof for theBenchmark
% 0.21/0.57  fof(f94,plain,(
% 0.21/0.57    $false),
% 0.21/0.57    inference(avatar_sat_refutation,[],[f51,f93])).
% 0.21/0.57  fof(f93,plain,(
% 0.21/0.57    spl1_1),
% 0.21/0.57    inference(avatar_contradiction_clause,[],[f90])).
% 0.21/0.57  fof(f90,plain,(
% 0.21/0.57    $false | spl1_1),
% 0.21/0.57    inference(unit_resulting_resolution,[],[f45,f50,f89])).
% 0.21/0.57  fof(f89,plain,(
% 0.21/0.57    ( ! [X0,X1] : (r1_tarski(k1_wellord2(X1),k2_zfmisc_1(X1,X1)) | ~r1_tarski(X1,X0)) )),
% 0.21/0.57    inference(global_subsumption,[],[f34,f88])).
% 0.21/0.57  fof(f88,plain,(
% 0.21/0.57    ( ! [X0,X1] : (r1_tarski(k1_wellord2(X1),k2_zfmisc_1(X1,X1)) | ~v1_relat_1(k1_wellord2(X0)) | ~r1_tarski(X1,X0)) )),
% 0.21/0.57    inference(superposition,[],[f78,f31])).
% 0.21/0.57  fof(f31,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0) | ~r1_tarski(X0,X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f20])).
% 0.21/0.57  % (7637)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.57  % (7622)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.57  % (7635)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.57  % (7635)Refutation not found, incomplete strategy% (7635)------------------------------
% 0.21/0.57  % (7635)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (7635)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (7635)Memory used [KB]: 10618
% 0.21/0.57  % (7635)Time elapsed: 0.169 s
% 0.21/0.57  % (7635)------------------------------
% 0.21/0.57  % (7635)------------------------------
% 0.21/0.58  % (7624)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.58  % (7632)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.58  % (7640)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.58  % (7626)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.58  % (7641)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.59  % (7642)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.59  % (7633)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.59  % (7645)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.59  % (7633)Refutation not found, incomplete strategy% (7633)------------------------------
% 0.21/0.59  % (7633)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.59  % (7633)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.59  
% 0.21/0.59  % (7633)Memory used [KB]: 1663
% 0.21/0.59  % (7633)Time elapsed: 0.152 s
% 0.21/0.59  % (7633)------------------------------
% 0.21/0.59  % (7633)------------------------------
% 0.21/0.59  fof(f20,plain,(
% 0.21/0.59    ! [X0,X1] : (k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0) | ~r1_tarski(X0,X1))),
% 0.21/0.59    inference(ennf_transformation,[],[f15])).
% 0.21/0.59  fof(f15,axiom,(
% 0.21/0.59    ! [X0,X1] : (r1_tarski(X0,X1) => k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0))),
% 0.21/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_wellord2)).
% 0.21/0.59  fof(f78,plain,(
% 0.21/0.59    ( ! [X4,X3] : (r1_tarski(k2_wellord1(X3,X4),k2_zfmisc_1(X4,X4)) | ~v1_relat_1(X3)) )),
% 0.21/0.59    inference(superposition,[],[f64,f43])).
% 0.21/0.59  fof(f43,plain,(
% 0.21/0.59    ( ! [X0,X1] : (k2_wellord1(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,k2_zfmisc_1(X1,X1))) | ~v1_relat_1(X0)) )),
% 0.21/0.59    inference(definition_unfolding,[],[f33,f39])).
% 0.21/0.59  fof(f39,plain,(
% 0.21/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 0.21/0.59    inference(definition_unfolding,[],[f35,f38])).
% 0.21/0.59  fof(f38,plain,(
% 0.21/0.59    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f5])).
% 0.21/0.59  fof(f5,axiom,(
% 0.21/0.59    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.21/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.59  fof(f35,plain,(
% 0.21/0.59    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f12])).
% 0.21/0.59  fof(f12,axiom,(
% 0.21/0.59    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.21/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.21/0.59  fof(f33,plain,(
% 0.21/0.59    ( ! [X0,X1] : (k2_wellord1(X0,X1) = k3_xboole_0(X0,k2_zfmisc_1(X1,X1)) | ~v1_relat_1(X0)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f21])).
% 0.21/0.59  fof(f21,plain,(
% 0.21/0.59    ! [X0] : (! [X1] : k2_wellord1(X0,X1) = k3_xboole_0(X0,k2_zfmisc_1(X1,X1)) | ~v1_relat_1(X0))),
% 0.21/0.59    inference(ennf_transformation,[],[f13])).
% 0.21/0.59  fof(f13,axiom,(
% 0.21/0.59    ! [X0] : (v1_relat_1(X0) => ! [X1] : k2_wellord1(X0,X1) = k3_xboole_0(X0,k2_zfmisc_1(X1,X1)))),
% 0.21/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_wellord1)).
% 0.21/0.59  fof(f64,plain,(
% 0.21/0.59    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k1_enumset1(X1,X1,X0)),X0)) )),
% 0.21/0.59    inference(superposition,[],[f59,f44])).
% 0.21/0.59  fof(f44,plain,(
% 0.21/0.59    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) )),
% 0.21/0.59    inference(definition_unfolding,[],[f36,f38,f38])).
% 0.21/0.59  fof(f36,plain,(
% 0.21/0.59    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f4])).
% 0.21/0.59  fof(f4,axiom,(
% 0.21/0.59    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.21/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.21/0.59  fof(f59,plain,(
% 0.21/0.59    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X1)),X0)) )),
% 0.21/0.59    inference(resolution,[],[f41,f45])).
% 0.21/0.59  fof(f41,plain,(
% 0.21/0.59    ( ! [X2,X0,X1] : (~r1_tarski(X0,k1_setfam_1(k1_enumset1(X1,X1,X2))) | r1_tarski(X0,X1)) )),
% 0.21/0.59    inference(definition_unfolding,[],[f27,f39])).
% 0.21/0.59  fof(f27,plain,(
% 0.21/0.59    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2))) )),
% 0.21/0.59    inference(cnf_transformation,[],[f19])).
% 0.21/0.59  fof(f19,plain,(
% 0.21/0.59    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 0.21/0.59    inference(ennf_transformation,[],[f2])).
% 0.21/0.59  fof(f2,axiom,(
% 0.21/0.59    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) => r1_tarski(X0,X1))),
% 0.21/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_xboole_1)).
% 0.21/0.59  fof(f34,plain,(
% 0.21/0.59    ( ! [X0] : (v1_relat_1(k1_wellord2(X0))) )),
% 0.21/0.59    inference(cnf_transformation,[],[f14])).
% 0.21/0.59  fof(f14,axiom,(
% 0.21/0.59    ! [X0] : v1_relat_1(k1_wellord2(X0))),
% 0.21/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).
% 0.21/0.59  fof(f50,plain,(
% 0.21/0.59    ~r1_tarski(k1_wellord2(sK0),k2_zfmisc_1(sK0,sK0)) | spl1_1),
% 0.21/0.59    inference(avatar_component_clause,[],[f48])).
% 0.21/0.59  fof(f48,plain,(
% 0.21/0.59    spl1_1 <=> r1_tarski(k1_wellord2(sK0),k2_zfmisc_1(sK0,sK0))),
% 0.21/0.59    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.21/0.59  fof(f45,plain,(
% 0.21/0.59    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.59    inference(equality_resolution,[],[f29])).
% 0.21/0.59  fof(f29,plain,(
% 0.21/0.59    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.59    inference(cnf_transformation,[],[f25])).
% 0.21/0.59  fof(f25,plain,(
% 0.21/0.59    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.59    inference(flattening,[],[f24])).
% 0.21/0.59  fof(f24,plain,(
% 0.21/0.59    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.59    inference(nnf_transformation,[],[f1])).
% 0.21/0.59  fof(f1,axiom,(
% 0.21/0.59    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.59  fof(f51,plain,(
% 0.21/0.59    ~spl1_1),
% 0.21/0.59    inference(avatar_split_clause,[],[f26,f48])).
% 0.21/0.59  fof(f26,plain,(
% 0.21/0.59    ~r1_tarski(k1_wellord2(sK0),k2_zfmisc_1(sK0,sK0))),
% 0.21/0.59    inference(cnf_transformation,[],[f23])).
% 0.21/0.59  fof(f23,plain,(
% 0.21/0.59    ~r1_tarski(k1_wellord2(sK0),k2_zfmisc_1(sK0,sK0))),
% 0.21/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f22])).
% 0.21/0.59  fof(f22,plain,(
% 0.21/0.59    ? [X0] : ~r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0)) => ~r1_tarski(k1_wellord2(sK0),k2_zfmisc_1(sK0,sK0))),
% 0.21/0.59    introduced(choice_axiom,[])).
% 0.21/0.59  fof(f18,plain,(
% 0.21/0.59    ? [X0] : ~r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0))),
% 0.21/0.59    inference(ennf_transformation,[],[f17])).
% 0.21/0.59  fof(f17,negated_conjecture,(
% 0.21/0.59    ~! [X0] : r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0))),
% 0.21/0.59    inference(negated_conjecture,[],[f16])).
% 0.21/0.59  fof(f16,conjecture,(
% 0.21/0.59    ! [X0] : r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0))),
% 0.21/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_wellord2)).
% 0.21/0.59  % SZS output end Proof for theBenchmark
% 0.21/0.59  % (7643)------------------------------
% 0.21/0.59  % (7643)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.59  % (7643)Termination reason: Refutation
% 0.21/0.59  
% 0.21/0.59  % (7643)Memory used [KB]: 10746
% 0.21/0.59  % (7643)Time elapsed: 0.161 s
% 0.21/0.59  % (7643)------------------------------
% 0.21/0.59  % (7643)------------------------------
% 0.21/0.59  % (7648)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.59  % (7614)Success in time 0.226 s
%------------------------------------------------------------------------------
