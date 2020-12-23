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
% DateTime   : Thu Dec  3 12:48:49 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   51 (  58 expanded)
%              Number of leaves         :   15 (  22 expanded)
%              Depth                    :    8
%              Number of atoms          :   90 ( 104 expanded)
%              Number of equality atoms :   26 (  28 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f72,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f38,f45,f54,f64,f71])).

fof(f71,plain,(
    ~ spl2_4 ),
    inference(avatar_contradiction_clause,[],[f70])).

fof(f70,plain,
    ( $false
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f65,f22])).

% (20491)Refutation not found, incomplete strategy% (20491)------------------------------
% (20491)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (20491)Termination reason: Refutation not found, incomplete strategy

% (20491)Memory used [KB]: 10618
% (20491)Time elapsed: 0.118 s
% (20491)------------------------------
% (20491)------------------------------
fof(f22,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f65,plain,
    ( ! [X0] : ~ r1_xboole_0(k3_enumset1(sK1(k1_xboole_0),sK1(k1_xboole_0),sK1(k1_xboole_0),sK1(k1_xboole_0),X0),k1_xboole_0)
    | ~ spl2_4 ),
    inference(unit_resulting_resolution,[],[f63,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f29,f32])).

fof(f32,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f26,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f28,f30])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f28,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f26,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ~ ( r2_hidden(X0,X2)
        & r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).

fof(f63,plain,
    ( r2_hidden(sK1(k1_xboole_0),k1_xboole_0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl2_4
  <=> r2_hidden(sK1(k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f64,plain,
    ( spl2_4
    | spl2_3 ),
    inference(avatar_split_clause,[],[f55,f50,f61])).

fof(f50,plain,
    ( spl2_3
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f55,plain,
    ( r2_hidden(sK1(k1_xboole_0),k1_xboole_0)
    | spl2_3 ),
    inference(unit_resulting_resolution,[],[f52,f24])).

fof(f24,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | r2_hidden(sK1(X0),X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ( ! [X2,X3] : k4_tarski(X2,X3) != sK1(X0)
        & r2_hidden(sK1(X0),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f14,f19])).

fof(f19,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] : k4_tarski(X2,X3) != X1
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] : k4_tarski(X2,X3) != sK1(X0)
        & r2_hidden(sK1(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ? [X1] :
          ( ! [X2,X3] : k4_tarski(X2,X3) != X1
          & r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) )
     => v1_relat_1(X0) ) ),
    inference(unused_predicate_definition_removal,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

fof(f52,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | spl2_3 ),
    inference(avatar_component_clause,[],[f50])).

fof(f54,plain,
    ( ~ spl2_3
    | spl2_2 ),
    inference(avatar_split_clause,[],[f47,f42,f50])).

fof(f42,plain,
    ( spl2_2
  <=> r1_tarski(k7_relat_1(k1_xboole_0,sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f47,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | spl2_2 ),
    inference(resolution,[],[f44,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

fof(f44,plain,
    ( ~ r1_tarski(k7_relat_1(k1_xboole_0,sK0),k1_xboole_0)
    | spl2_2 ),
    inference(avatar_component_clause,[],[f42])).

fof(f45,plain,
    ( ~ spl2_2
    | spl2_1 ),
    inference(avatar_split_clause,[],[f39,f35,f42])).

fof(f35,plain,
    ( spl2_1
  <=> k1_xboole_0 = k7_relat_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f39,plain,
    ( ~ r1_tarski(k7_relat_1(k1_xboole_0,sK0),k1_xboole_0)
    | spl2_1 ),
    inference(unit_resulting_resolution,[],[f37,f23])).

fof(f23,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f37,plain,
    ( k1_xboole_0 != k7_relat_1(k1_xboole_0,sK0)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f35])).

fof(f38,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f21,f35])).

fof(f21,plain,(
    k1_xboole_0 != k7_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    k1_xboole_0 != k7_relat_1(k1_xboole_0,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f17])).

fof(f17,plain,
    ( ? [X0] : k1_xboole_0 != k7_relat_1(k1_xboole_0,X0)
   => k1_xboole_0 != k7_relat_1(k1_xboole_0,sK0) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] : k1_xboole_0 != k7_relat_1(k1_xboole_0,X0) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t111_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n012.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:10:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.52  % (20491)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.52  % (20490)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.52  % (20497)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.52  % (20482)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (20494)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.52  % (20482)Refutation not found, incomplete strategy% (20482)------------------------------
% 0.21/0.52  % (20482)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (20482)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (20482)Memory used [KB]: 10618
% 0.21/0.52  % (20482)Time elapsed: 0.115 s
% 0.21/0.52  % (20482)------------------------------
% 0.21/0.52  % (20482)------------------------------
% 0.21/0.52  % (20488)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.53  % (20488)Refutation not found, incomplete strategy% (20488)------------------------------
% 0.21/0.53  % (20488)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (20486)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (20497)Refutation not found, incomplete strategy% (20497)------------------------------
% 0.21/0.53  % (20497)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (20488)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (20488)Memory used [KB]: 10618
% 0.21/0.53  % (20488)Time elapsed: 0.107 s
% 0.21/0.53  % (20488)------------------------------
% 0.21/0.53  % (20488)------------------------------
% 0.21/0.53  % (20497)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (20497)Memory used [KB]: 10618
% 0.21/0.53  % (20497)Time elapsed: 0.114 s
% 0.21/0.53  % (20497)------------------------------
% 0.21/0.53  % (20497)------------------------------
% 0.21/0.53  % (20505)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.53  % (20480)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (20501)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.53  % (20480)Refutation not found, incomplete strategy% (20480)------------------------------
% 0.21/0.53  % (20480)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (20480)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (20480)Memory used [KB]: 1663
% 0.21/0.53  % (20480)Time elapsed: 0.115 s
% 0.21/0.53  % (20480)------------------------------
% 0.21/0.53  % (20480)------------------------------
% 0.21/0.53  % (20505)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f72,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(avatar_sat_refutation,[],[f38,f45,f54,f64,f71])).
% 0.21/0.53  fof(f71,plain,(
% 0.21/0.53    ~spl2_4),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f70])).
% 0.21/0.53  fof(f70,plain,(
% 0.21/0.53    $false | ~spl2_4),
% 0.21/0.53    inference(subsumption_resolution,[],[f65,f22])).
% 0.21/0.53  % (20491)Refutation not found, incomplete strategy% (20491)------------------------------
% 0.21/0.53  % (20491)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (20491)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (20491)Memory used [KB]: 10618
% 0.21/0.53  % (20491)Time elapsed: 0.118 s
% 0.21/0.53  % (20491)------------------------------
% 0.21/0.53  % (20491)------------------------------
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.21/0.53  fof(f65,plain,(
% 0.21/0.53    ( ! [X0] : (~r1_xboole_0(k3_enumset1(sK1(k1_xboole_0),sK1(k1_xboole_0),sK1(k1_xboole_0),sK1(k1_xboole_0),X0),k1_xboole_0)) ) | ~spl2_4),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f63,f33])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),X2)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f29,f32])).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f26,f31])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f28,f30])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r1_xboole_0(k2_tarski(X0,X1),X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f16])).
% 0.21/0.53  fof(f16,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (~r2_hidden(X0,X2) | ~r1_xboole_0(k2_tarski(X0,X1),X2))),
% 0.21/0.53    inference(ennf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : ~(r2_hidden(X0,X2) & r1_xboole_0(k2_tarski(X0,X1),X2))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).
% 0.21/0.53  fof(f63,plain,(
% 0.21/0.53    r2_hidden(sK1(k1_xboole_0),k1_xboole_0) | ~spl2_4),
% 0.21/0.53    inference(avatar_component_clause,[],[f61])).
% 0.21/0.53  fof(f61,plain,(
% 0.21/0.53    spl2_4 <=> r2_hidden(sK1(k1_xboole_0),k1_xboole_0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.53  fof(f64,plain,(
% 0.21/0.53    spl2_4 | spl2_3),
% 0.21/0.53    inference(avatar_split_clause,[],[f55,f50,f61])).
% 0.21/0.53  fof(f50,plain,(
% 0.21/0.53    spl2_3 <=> v1_relat_1(k1_xboole_0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.53  fof(f55,plain,(
% 0.21/0.53    r2_hidden(sK1(k1_xboole_0),k1_xboole_0) | spl2_3),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f52,f24])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ( ! [X0] : (v1_relat_1(X0) | r2_hidden(sK1(X0),X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f20])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ! [X0] : (v1_relat_1(X0) | (! [X2,X3] : k4_tarski(X2,X3) != sK1(X0) & r2_hidden(sK1(X0),X0)))),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f14,f19])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    ! [X0] : (? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)) => (! [X3,X2] : k4_tarski(X2,X3) != sK1(X0) & r2_hidden(sK1(X0),X0)))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f14,plain,(
% 0.21/0.53    ! [X0] : (v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f11])).
% 0.21/0.53  fof(f11,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)) => v1_relat_1(X0))),
% 0.21/0.53    inference(unused_predicate_definition_removal,[],[f7])).
% 0.21/0.53  fof(f7,axiom,(
% 0.21/0.53    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).
% 0.21/0.53  fof(f52,plain,(
% 0.21/0.53    ~v1_relat_1(k1_xboole_0) | spl2_3),
% 0.21/0.53    inference(avatar_component_clause,[],[f50])).
% 0.21/0.53  fof(f54,plain,(
% 0.21/0.53    ~spl2_3 | spl2_2),
% 0.21/0.53    inference(avatar_split_clause,[],[f47,f42,f50])).
% 0.21/0.53  fof(f42,plain,(
% 0.21/0.53    spl2_2 <=> r1_tarski(k7_relat_1(k1_xboole_0,sK0),k1_xboole_0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.53  fof(f47,plain,(
% 0.21/0.53    ~v1_relat_1(k1_xboole_0) | spl2_2),
% 0.21/0.53    inference(resolution,[],[f44,f27])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f15])).
% 0.21/0.53  fof(f15,plain,(
% 0.21/0.53    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,axiom,(
% 0.21/0.53    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).
% 0.21/0.53  fof(f44,plain,(
% 0.21/0.53    ~r1_tarski(k7_relat_1(k1_xboole_0,sK0),k1_xboole_0) | spl2_2),
% 0.21/0.53    inference(avatar_component_clause,[],[f42])).
% 0.21/0.53  fof(f45,plain,(
% 0.21/0.53    ~spl2_2 | spl2_1),
% 0.21/0.53    inference(avatar_split_clause,[],[f39,f35,f42])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    spl2_1 <=> k1_xboole_0 = k7_relat_1(k1_xboole_0,sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.53  fof(f39,plain,(
% 0.21/0.53    ~r1_tarski(k7_relat_1(k1_xboole_0,sK0),k1_xboole_0) | spl2_1),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f37,f23])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f13])).
% 0.21/0.53  fof(f13,plain,(
% 0.21/0.53    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.21/0.53    inference(ennf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    k1_xboole_0 != k7_relat_1(k1_xboole_0,sK0) | spl2_1),
% 0.21/0.53    inference(avatar_component_clause,[],[f35])).
% 0.21/0.53  fof(f38,plain,(
% 0.21/0.53    ~spl2_1),
% 0.21/0.53    inference(avatar_split_clause,[],[f21,f35])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    k1_xboole_0 != k7_relat_1(k1_xboole_0,sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f18])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    k1_xboole_0 != k7_relat_1(k1_xboole_0,sK0)),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f17])).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    ? [X0] : k1_xboole_0 != k7_relat_1(k1_xboole_0,X0) => k1_xboole_0 != k7_relat_1(k1_xboole_0,sK0)),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f12,plain,(
% 0.21/0.53    ? [X0] : k1_xboole_0 != k7_relat_1(k1_xboole_0,X0)),
% 0.21/0.53    inference(ennf_transformation,[],[f10])).
% 0.21/0.53  fof(f10,negated_conjecture,(
% 0.21/0.53    ~! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)),
% 0.21/0.53    inference(negated_conjecture,[],[f9])).
% 0.21/0.53  fof(f9,conjecture,(
% 0.21/0.53    ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t111_relat_1)).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (20505)------------------------------
% 0.21/0.53  % (20505)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (20505)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (20505)Memory used [KB]: 6140
% 0.21/0.53  % (20505)Time elapsed: 0.112 s
% 0.21/0.53  % (20505)------------------------------
% 0.21/0.53  % (20505)------------------------------
% 0.21/0.53  % (20484)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (20477)Success in time 0.17 s
%------------------------------------------------------------------------------
