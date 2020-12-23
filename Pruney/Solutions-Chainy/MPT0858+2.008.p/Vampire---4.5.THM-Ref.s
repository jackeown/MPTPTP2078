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
% DateTime   : Thu Dec  3 12:58:18 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   40 ( 120 expanded)
%              Number of leaves         :    9 (  38 expanded)
%              Depth                    :   12
%              Number of atoms          :   71 ( 193 expanded)
%              Number of equality atoms :   27 ( 111 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f165,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f37,f57,f164])).

fof(f164,plain,(
    spl3_2 ),
    inference(avatar_contradiction_clause,[],[f160])).

fof(f160,plain,
    ( $false
    | spl3_2 ),
    inference(unit_resulting_resolution,[],[f36,f138])).

fof(f138,plain,(
    sK1 = k1_mcart_1(sK0) ),
    inference(superposition,[],[f110,f19])).

fof(f19,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f110,plain,(
    sK1 = k2_mcart_1(k4_tarski(sK2,k1_mcart_1(sK0))) ),
    inference(unit_resulting_resolution,[],[f66,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,k1_enumset1(X2,X2,X2)))
      | k2_mcart_1(X0) = X2 ) ),
    inference(definition_unfolding,[],[f15,f25])).

fof(f25,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f23,f24])).

fof(f24,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f23,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f15,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2)))
      | k2_mcart_1(X0) = X2 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ( k2_mcart_1(X0) = X2
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2)))
     => ( k2_mcart_1(X0) = X2
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_mcart_1)).

fof(f66,plain,(
    r2_hidden(k4_tarski(sK2,k1_mcart_1(sK0)),k2_zfmisc_1(k1_enumset1(sK2,sK2,sK2),k1_enumset1(sK1,sK1,sK1))) ),
    inference(unit_resulting_resolution,[],[f58,f45,f22])).

fof(f22,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X1,X3)
      | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f45,plain,(
    r2_hidden(k1_mcart_1(sK0),k1_enumset1(sK1,sK1,sK1)) ),
    inference(unit_resulting_resolution,[],[f26,f16])).

fof(f16,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f26,plain,(
    r2_hidden(sK0,k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),k1_enumset1(sK2,sK2,sK2))) ),
    inference(definition_unfolding,[],[f13,f25,f25])).

fof(f13,plain,(
    r2_hidden(sK0,k2_zfmisc_1(k1_tarski(sK1),k1_tarski(sK2))) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ( k2_mcart_1(X0) != X2
        | k1_mcart_1(X0) != X1 )
      & r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),k1_tarski(X2))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),k1_tarski(X2)))
       => ( k2_mcart_1(X0) = X2
          & k1_mcart_1(X0) = X1 ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),k1_tarski(X2)))
     => ( k2_mcart_1(X0) = X2
        & k1_mcart_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_mcart_1)).

fof(f58,plain,(
    r2_hidden(sK2,k1_enumset1(sK2,sK2,sK2)) ),
    inference(backward_demodulation,[],[f46,f43])).

% (4898)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% (4903)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% (4885)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% (4895)Refutation not found, incomplete strategy% (4895)------------------------------
% (4895)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (4878)Refutation not found, incomplete strategy% (4878)------------------------------
% (4878)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (4878)Termination reason: Refutation not found, incomplete strategy

% (4878)Memory used [KB]: 1663
% (4878)Time elapsed: 0.113 s
% (4878)------------------------------
% (4878)------------------------------
% (4895)Termination reason: Refutation not found, incomplete strategy

% (4895)Memory used [KB]: 10618
% (4895)Time elapsed: 0.114 s
% (4895)------------------------------
% (4895)------------------------------
% (4890)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% (4879)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% (4904)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% (4886)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% (4886)Refutation not found, incomplete strategy% (4886)------------------------------
% (4886)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (4886)Termination reason: Refutation not found, incomplete strategy

% (4886)Memory used [KB]: 10618
% (4886)Time elapsed: 0.134 s
% (4886)------------------------------
% (4886)------------------------------
% (4880)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% (4905)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% (4880)Refutation not found, incomplete strategy% (4880)------------------------------
% (4880)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (4880)Termination reason: Refutation not found, incomplete strategy

% (4880)Memory used [KB]: 10618
% (4880)Time elapsed: 0.136 s
% (4880)------------------------------
% (4880)------------------------------
% (4883)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
fof(f43,plain,(
    sK2 = k2_mcart_1(sK0) ),
    inference(unit_resulting_resolution,[],[f26,f27])).

fof(f46,plain,(
    r2_hidden(k2_mcart_1(sK0),k1_enumset1(sK2,sK2,sK2)) ),
    inference(unit_resulting_resolution,[],[f26,f17])).

fof(f17,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k2_mcart_1(X0),X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f36,plain,
    ( sK1 != k1_mcart_1(sK0)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f34])).

fof(f34,plain,
    ( spl3_2
  <=> sK1 = k1_mcart_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f57,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f44])).

fof(f44,plain,
    ( $false
    | spl3_1 ),
    inference(unit_resulting_resolution,[],[f32,f26,f27])).

fof(f32,plain,
    ( sK2 != k2_mcart_1(sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f30])).

fof(f30,plain,
    ( spl3_1
  <=> sK2 = k2_mcart_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f37,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f12,f34,f30])).

fof(f12,plain,
    ( sK1 != k1_mcart_1(sK0)
    | sK2 != k2_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:50:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (4889)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.50  % (4900)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.51  % (4892)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.51  % (4878)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.51  % (4900)Refutation not found, incomplete strategy% (4900)------------------------------
% 0.21/0.51  % (4900)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (4895)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.51  % (4900)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (4900)Memory used [KB]: 10618
% 0.21/0.51  % (4900)Time elapsed: 0.060 s
% 0.21/0.51  % (4900)------------------------------
% 0.21/0.51  % (4900)------------------------------
% 0.21/0.51  % (4884)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.51  % (4882)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (4882)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f165,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f37,f57,f164])).
% 0.21/0.51  fof(f164,plain,(
% 0.21/0.51    spl3_2),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f160])).
% 0.21/0.51  fof(f160,plain,(
% 0.21/0.51    $false | spl3_2),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f36,f138])).
% 0.21/0.51  fof(f138,plain,(
% 0.21/0.51    sK1 = k1_mcart_1(sK0)),
% 0.21/0.51    inference(superposition,[],[f110,f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 0.21/0.51    inference(cnf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).
% 0.21/0.51  fof(f110,plain,(
% 0.21/0.51    sK1 = k2_mcart_1(k4_tarski(sK2,k1_mcart_1(sK0)))),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f66,f27])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,k1_enumset1(X2,X2,X2))) | k2_mcart_1(X0) = X2) )),
% 0.21/0.51    inference(definition_unfolding,[],[f15,f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.21/0.51    inference(definition_unfolding,[],[f23,f24])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2))) | k2_mcart_1(X0) = X2) )),
% 0.21/0.51    inference(cnf_transformation,[],[f10])).
% 0.21/0.51  fof(f10,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((k2_mcart_1(X0) = X2 & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2))))),
% 0.21/0.51    inference(ennf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2))) => (k2_mcart_1(X0) = X2 & r2_hidden(k1_mcart_1(X0),X1)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_mcart_1)).
% 0.21/0.51  fof(f66,plain,(
% 0.21/0.51    r2_hidden(k4_tarski(sK2,k1_mcart_1(sK0)),k2_zfmisc_1(k1_enumset1(sK2,sK2,sK2),k1_enumset1(sK1,sK1,sK1)))),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f58,f45,f22])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (~r2_hidden(X0,X2) | ~r2_hidden(X1,X3) | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 0.21/0.51  fof(f45,plain,(
% 0.21/0.51    r2_hidden(k1_mcart_1(sK0),k1_enumset1(sK1,sK1,sK1))),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f26,f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k1_mcart_1(X0),X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f11])).
% 0.21/0.51  fof(f11,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.21/0.51    inference(ennf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    r2_hidden(sK0,k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),k1_enumset1(sK2,sK2,sK2)))),
% 0.21/0.51    inference(definition_unfolding,[],[f13,f25,f25])).
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    r2_hidden(sK0,k2_zfmisc_1(k1_tarski(sK1),k1_tarski(sK2)))),
% 0.21/0.51    inference(cnf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,plain,(
% 0.21/0.51    ? [X0,X1,X2] : ((k2_mcart_1(X0) != X2 | k1_mcart_1(X0) != X1) & r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),k1_tarski(X2))))),
% 0.21/0.51    inference(ennf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,negated_conjecture,(
% 0.21/0.51    ~! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),k1_tarski(X2))) => (k2_mcart_1(X0) = X2 & k1_mcart_1(X0) = X1))),
% 0.21/0.51    inference(negated_conjecture,[],[f7])).
% 0.21/0.51  fof(f7,conjecture,(
% 0.21/0.51    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),k1_tarski(X2))) => (k2_mcart_1(X0) = X2 & k1_mcart_1(X0) = X1))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_mcart_1)).
% 0.21/0.51  fof(f58,plain,(
% 0.21/0.51    r2_hidden(sK2,k1_enumset1(sK2,sK2,sK2))),
% 0.21/0.51    inference(backward_demodulation,[],[f46,f43])).
% 0.21/0.52  % (4898)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.52  % (4903)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.52  % (4885)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.52  % (4895)Refutation not found, incomplete strategy% (4895)------------------------------
% 0.21/0.52  % (4895)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (4878)Refutation not found, incomplete strategy% (4878)------------------------------
% 0.21/0.52  % (4878)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (4878)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (4878)Memory used [KB]: 1663
% 0.21/0.52  % (4878)Time elapsed: 0.113 s
% 0.21/0.52  % (4878)------------------------------
% 0.21/0.52  % (4878)------------------------------
% 0.21/0.53  % (4895)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (4895)Memory used [KB]: 10618
% 0.21/0.53  % (4895)Time elapsed: 0.114 s
% 0.21/0.53  % (4895)------------------------------
% 0.21/0.53  % (4895)------------------------------
% 0.21/0.53  % (4890)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (4879)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (4904)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.53  % (4886)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.53  % (4886)Refutation not found, incomplete strategy% (4886)------------------------------
% 0.21/0.53  % (4886)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (4886)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (4886)Memory used [KB]: 10618
% 0.21/0.53  % (4886)Time elapsed: 0.134 s
% 0.21/0.53  % (4886)------------------------------
% 0.21/0.53  % (4886)------------------------------
% 0.21/0.53  % (4880)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (4905)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.53  % (4880)Refutation not found, incomplete strategy% (4880)------------------------------
% 0.21/0.53  % (4880)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (4880)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (4880)Memory used [KB]: 10618
% 0.21/0.53  % (4880)Time elapsed: 0.136 s
% 0.21/0.53  % (4880)------------------------------
% 0.21/0.53  % (4880)------------------------------
% 0.21/0.53  % (4883)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  fof(f43,plain,(
% 0.21/0.53    sK2 = k2_mcart_1(sK0)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f26,f27])).
% 0.21/0.53  fof(f46,plain,(
% 0.21/0.53    r2_hidden(k2_mcart_1(sK0),k1_enumset1(sK2,sK2,sK2))),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f26,f17])).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k2_mcart_1(X0),X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f11])).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    sK1 != k1_mcart_1(sK0) | spl3_2),
% 0.21/0.53    inference(avatar_component_clause,[],[f34])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    spl3_2 <=> sK1 = k1_mcart_1(sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.53  fof(f57,plain,(
% 0.21/0.53    spl3_1),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f44])).
% 0.21/0.53  fof(f44,plain,(
% 0.21/0.53    $false | spl3_1),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f32,f26,f27])).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    sK2 != k2_mcart_1(sK0) | spl3_1),
% 0.21/0.53    inference(avatar_component_clause,[],[f30])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    spl3_1 <=> sK2 = k2_mcart_1(sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    ~spl3_1 | ~spl3_2),
% 0.21/0.53    inference(avatar_split_clause,[],[f12,f34,f30])).
% 0.21/0.53  fof(f12,plain,(
% 0.21/0.53    sK1 != k1_mcart_1(sK0) | sK2 != k2_mcart_1(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f9])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (4882)------------------------------
% 0.21/0.53  % (4882)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (4882)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (4882)Memory used [KB]: 6268
% 0.21/0.53  % (4882)Time elapsed: 0.120 s
% 0.21/0.53  % (4882)------------------------------
% 0.21/0.53  % (4882)------------------------------
% 0.21/0.53  % (4887)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.54  % (4877)Success in time 0.178 s
%------------------------------------------------------------------------------
