%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:35:32 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 147 expanded)
%              Number of leaves         :   12 (  52 expanded)
%              Depth                    :    9
%              Number of atoms          :   91 ( 210 expanded)
%              Number of equality atoms :   57 ( 163 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f166,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f91,f96,f133,f156,f165])).

fof(f165,plain,
    ( spl3_1
    | ~ spl3_5 ),
    inference(avatar_contradiction_clause,[],[f157])).

fof(f157,plain,
    ( $false
    | spl3_1
    | ~ spl3_5 ),
    inference(unit_resulting_resolution,[],[f90,f90,f90,f155,f86])).

fof(f86,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,k5_enumset1(X0,X0,X0,X0,X0,X1,X2))
      | X1 = X4
      | X2 = X4
      | X0 = X4 ) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X0 = X4
      | X1 = X4
      | X2 = X4
      | ~ r2_hidden(X4,X3)
      | k5_enumset1(X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f49,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f42,f57])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f44,f54])).

fof(f54,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f44,plain,(
    ! [X2,X0,X3,X1] : k4_enumset1(X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] : k4_enumset1(X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_enumset1)).

fof(f42,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f49,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X0 = X4
      | X1 = X4
      | X2 = X4
      | ~ r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(f155,plain,
    ( r2_hidden(sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f153])).

fof(f153,plain,
    ( spl3_5
  <=> r2_hidden(sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f90,plain,
    ( sK0 != sK1
    | spl3_1 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl3_1
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f156,plain,
    ( spl3_5
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f143,f124,f153])).

fof(f124,plain,
    ( spl3_3
  <=> k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f143,plain,
    ( r2_hidden(sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | ~ spl3_3 ),
    inference(superposition,[],[f81,f126])).

fof(f126,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f124])).

fof(f81,plain,(
    ! [X4,X0,X1] : r2_hidden(X4,k5_enumset1(X0,X0,X0,X0,X0,X1,X4)) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X4,X0,X3,X1] :
      ( r2_hidden(X4,X3)
      | k5_enumset1(X0,X0,X0,X0,X0,X1,X4) != X3 ) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X2 != X4
      | r2_hidden(X4,X3)
      | k5_enumset1(X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f52,f58])).

fof(f52,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X2 != X4
      | r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f133,plain,
    ( spl3_3
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f107,f93,f124])).

fof(f93,plain,
    ( spl3_2
  <=> k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f107,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)
    | ~ spl3_2 ),
    inference(superposition,[],[f64,f95])).

fof(f95,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f93])).

fof(f64,plain,(
    ! [X0,X1] : k5_enumset1(X0,X0,X0,X0,X0,X0,X1) = k2_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X1,X1,X1,X1,X1,X1,X1)) ),
    inference(definition_unfolding,[],[f31,f59,f60,f60])).

fof(f60,plain,(
    ! [X0] : k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f28,f59])).

fof(f28,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f59,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f30,f58])).

fof(f30,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f31,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

fof(f96,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f63,f93])).

fof(f63,plain,(
    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(definition_unfolding,[],[f26,f60,f60,f60])).

fof(f26,plain,(
    k1_tarski(sK0) = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_zfmisc_1)).

fof(f91,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f27,f88])).

fof(f27,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:41:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.47  % (4410)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.49  % (4411)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.51  % (4406)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.53  % (4424)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.53  % (4432)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.53  % (4432)Refutation not found, incomplete strategy% (4432)------------------------------
% 0.21/0.53  % (4432)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (4432)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (4432)Memory used [KB]: 1663
% 0.21/0.53  % (4432)Time elapsed: 0.002 s
% 0.21/0.53  % (4432)------------------------------
% 0.21/0.53  % (4432)------------------------------
% 0.21/0.53  % (4417)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.53  % (4427)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.54  % (4404)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.54  % (4405)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.54  % (4404)Refutation not found, incomplete strategy% (4404)------------------------------
% 0.21/0.54  % (4404)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (4404)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (4404)Memory used [KB]: 1663
% 0.21/0.54  % (4404)Time elapsed: 0.136 s
% 0.21/0.54  % (4404)------------------------------
% 0.21/0.54  % (4404)------------------------------
% 0.21/0.54  % (4403)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.54  % (4428)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.54  % (4409)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (4419)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.54  % (4422)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.54  % (4408)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.54  % (4421)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.54  % (4412)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.54  % (4419)Refutation not found, incomplete strategy% (4419)------------------------------
% 0.21/0.54  % (4419)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (4431)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.54  % (4419)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (4419)Memory used [KB]: 10618
% 0.21/0.54  % (4419)Time elapsed: 0.139 s
% 0.21/0.54  % (4419)------------------------------
% 0.21/0.54  % (4419)------------------------------
% 0.21/0.55  % (4430)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.55  % (4431)Refutation found. Thanks to Tanya!
% 0.21/0.55  % SZS status Theorem for theBenchmark
% 0.21/0.55  % SZS output start Proof for theBenchmark
% 0.21/0.55  fof(f166,plain,(
% 0.21/0.55    $false),
% 0.21/0.55    inference(avatar_sat_refutation,[],[f91,f96,f133,f156,f165])).
% 0.21/0.55  fof(f165,plain,(
% 0.21/0.55    spl3_1 | ~spl3_5),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f157])).
% 0.21/0.55  fof(f157,plain,(
% 0.21/0.55    $false | (spl3_1 | ~spl3_5)),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f90,f90,f90,f155,f86])).
% 0.21/0.55  fof(f86,plain,(
% 0.21/0.55    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) | X1 = X4 | X2 = X4 | X0 = X4) )),
% 0.21/0.55    inference(equality_resolution,[],[f72])).
% 0.21/0.55  fof(f72,plain,(
% 0.21/0.55    ( ! [X4,X2,X0,X3,X1] : (X0 = X4 | X1 = X4 | X2 = X4 | ~r2_hidden(X4,X3) | k5_enumset1(X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 0.21/0.55    inference(definition_unfolding,[],[f49,f58])).
% 0.21/0.55  fof(f58,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) )),
% 0.21/0.55    inference(definition_unfolding,[],[f42,f57])).
% 0.21/0.55  fof(f57,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3)) )),
% 0.21/0.55    inference(definition_unfolding,[],[f44,f54])).
% 0.21/0.55  fof(f54,plain,(
% 0.21/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f18])).
% 0.21/0.55  fof(f18,axiom,(
% 0.21/0.55    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 0.21/0.55  fof(f44,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (k4_enumset1(X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f19])).
% 0.21/0.55  fof(f19,axiom,(
% 0.21/0.55    ! [X0,X1,X2,X3] : k4_enumset1(X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_enumset1)).
% 0.21/0.55  fof(f42,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f16])).
% 0.21/0.55  fof(f16,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.55  fof(f49,plain,(
% 0.21/0.55    ( ! [X4,X2,X0,X3,X1] : (X0 = X4 | X1 = X4 | X2 = X4 | ~r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 0.21/0.55    inference(cnf_transformation,[],[f25])).
% 0.21/0.55  fof(f25,plain,(
% 0.21/0.55    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 0.21/0.55    inference(ennf_transformation,[],[f11])).
% 0.21/0.55  fof(f11,axiom,(
% 0.21/0.55    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 0.21/0.55  fof(f155,plain,(
% 0.21/0.55    r2_hidden(sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | ~spl3_5),
% 0.21/0.55    inference(avatar_component_clause,[],[f153])).
% 0.21/0.55  fof(f153,plain,(
% 0.21/0.55    spl3_5 <=> r2_hidden(sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.55  fof(f90,plain,(
% 0.21/0.55    sK0 != sK1 | spl3_1),
% 0.21/0.55    inference(avatar_component_clause,[],[f88])).
% 0.21/0.55  fof(f88,plain,(
% 0.21/0.55    spl3_1 <=> sK0 = sK1),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.55  fof(f156,plain,(
% 0.21/0.55    spl3_5 | ~spl3_3),
% 0.21/0.55    inference(avatar_split_clause,[],[f143,f124,f153])).
% 0.21/0.55  fof(f124,plain,(
% 0.21/0.55    spl3_3 <=> k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.55  fof(f143,plain,(
% 0.21/0.55    r2_hidden(sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | ~spl3_3),
% 0.21/0.55    inference(superposition,[],[f81,f126])).
% 0.21/0.55  fof(f126,plain,(
% 0.21/0.55    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) | ~spl3_3),
% 0.21/0.55    inference(avatar_component_clause,[],[f124])).
% 0.21/0.55  fof(f81,plain,(
% 0.21/0.55    ( ! [X4,X0,X1] : (r2_hidden(X4,k5_enumset1(X0,X0,X0,X0,X0,X1,X4))) )),
% 0.21/0.55    inference(equality_resolution,[],[f80])).
% 0.21/0.55  fof(f80,plain,(
% 0.21/0.55    ( ! [X4,X0,X3,X1] : (r2_hidden(X4,X3) | k5_enumset1(X0,X0,X0,X0,X0,X1,X4) != X3) )),
% 0.21/0.55    inference(equality_resolution,[],[f69])).
% 0.21/0.55  fof(f69,plain,(
% 0.21/0.55    ( ! [X4,X2,X0,X3,X1] : (X2 != X4 | r2_hidden(X4,X3) | k5_enumset1(X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 0.21/0.55    inference(definition_unfolding,[],[f52,f58])).
% 0.21/0.55  fof(f52,plain,(
% 0.21/0.55    ( ! [X4,X2,X0,X3,X1] : (X2 != X4 | r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 0.21/0.55    inference(cnf_transformation,[],[f25])).
% 0.21/0.55  fof(f133,plain,(
% 0.21/0.55    spl3_3 | ~spl3_2),
% 0.21/0.55    inference(avatar_split_clause,[],[f107,f93,f124])).
% 0.21/0.55  fof(f93,plain,(
% 0.21/0.55    spl3_2 <=> k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.55  fof(f107,plain,(
% 0.21/0.55    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) | ~spl3_2),
% 0.21/0.55    inference(superposition,[],[f64,f95])).
% 0.21/0.55  fof(f95,plain,(
% 0.21/0.55    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)) | ~spl3_2),
% 0.21/0.55    inference(avatar_component_clause,[],[f93])).
% 0.21/0.55  fof(f64,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k5_enumset1(X0,X0,X0,X0,X0,X0,X1) = k2_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X1,X1,X1,X1,X1,X1,X1))) )),
% 0.21/0.55    inference(definition_unfolding,[],[f31,f59,f60,f60])).
% 0.21/0.55  fof(f60,plain,(
% 0.21/0.55    ( ! [X0] : (k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) )),
% 0.21/0.55    inference(definition_unfolding,[],[f28,f59])).
% 0.21/0.55  fof(f28,plain,(
% 0.21/0.55    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f14])).
% 0.21/0.55  fof(f14,axiom,(
% 0.21/0.55    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.55  fof(f59,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) )),
% 0.21/0.55    inference(definition_unfolding,[],[f30,f58])).
% 0.21/0.55  fof(f30,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f15])).
% 0.21/0.55  fof(f15,axiom,(
% 0.21/0.55    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.55  fof(f31,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f12])).
% 0.21/0.55  fof(f12,axiom,(
% 0.21/0.55    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).
% 0.21/0.55  fof(f96,plain,(
% 0.21/0.55    spl3_2),
% 0.21/0.55    inference(avatar_split_clause,[],[f63,f93])).
% 0.21/0.55  fof(f63,plain,(
% 0.21/0.55    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1))),
% 0.21/0.55    inference(definition_unfolding,[],[f26,f60,f60,f60])).
% 0.21/0.55  fof(f26,plain,(
% 0.21/0.55    k1_tarski(sK0) = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 0.21/0.55    inference(cnf_transformation,[],[f22])).
% 0.21/0.55  fof(f22,plain,(
% 0.21/0.55    ? [X0,X1] : (X0 != X1 & k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 0.21/0.55    inference(ennf_transformation,[],[f21])).
% 0.21/0.55  fof(f21,negated_conjecture,(
% 0.21/0.55    ~! [X0,X1] : (k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 0.21/0.55    inference(negated_conjecture,[],[f20])).
% 0.21/0.55  fof(f20,conjecture,(
% 0.21/0.55    ! [X0,X1] : (k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_zfmisc_1)).
% 0.21/0.55  fof(f91,plain,(
% 0.21/0.55    ~spl3_1),
% 0.21/0.55    inference(avatar_split_clause,[],[f27,f88])).
% 0.21/0.55  fof(f27,plain,(
% 0.21/0.55    sK0 != sK1),
% 0.21/0.55    inference(cnf_transformation,[],[f22])).
% 0.21/0.55  % SZS output end Proof for theBenchmark
% 0.21/0.55  % (4431)------------------------------
% 0.21/0.55  % (4431)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (4431)Termination reason: Refutation
% 0.21/0.55  
% 0.21/0.55  % (4431)Memory used [KB]: 10746
% 0.21/0.55  % (4431)Time elapsed: 0.145 s
% 0.21/0.55  % (4431)------------------------------
% 0.21/0.55  % (4431)------------------------------
% 0.21/0.55  % (4402)Success in time 0.189 s
%------------------------------------------------------------------------------
