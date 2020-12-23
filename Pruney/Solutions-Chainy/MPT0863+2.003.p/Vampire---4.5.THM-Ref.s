%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:29 EST 2020

% Result     : Theorem 1.50s
% Output     : Refutation 1.50s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 217 expanded)
%              Number of leaves         :   18 (  72 expanded)
%              Depth                    :   10
%              Number of atoms          :  168 ( 455 expanded)
%              Number of equality atoms :   54 ( 224 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f170,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f70,f75,f80,f81,f124,f134,f143,f169])).

fof(f169,plain,
    ( spl6_3
    | ~ spl6_6 ),
    inference(avatar_contradiction_clause,[],[f165])).

fof(f165,plain,
    ( $false
    | spl6_3
    | ~ spl6_6 ),
    inference(unit_resulting_resolution,[],[f74,f133,f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X1))
      | X0 = X1 ) ),
    inference(condensation,[],[f96])).

fof(f96,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,k2_enumset1(X2,X2,X2,X2)) ) ),
    inference(forward_demodulation,[],[f95,f25])).

fof(f25,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f95,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_mcart_1(k4_tarski(X0,X1)) = X2
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,k2_enumset1(X2,X2,X2,X2)) ) ),
    inference(resolution,[],[f52,f47])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(k2_enumset1(X1,X1,X1,X1),X2))
      | k1_mcart_1(X0) = X1 ) ),
    inference(definition_unfolding,[],[f33,f49])).

fof(f49,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f23,f48])).

fof(f48,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f24,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f24,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f23,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2))
      | k1_mcart_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & k1_mcart_1(X0) = X1 )
      | ~ r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & k1_mcart_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_mcart_1)).

fof(f133,plain,
    ( r2_hidden(sK3,k2_enumset1(k2_mcart_1(sK0),k2_mcart_1(sK0),k2_mcart_1(sK0),k2_mcart_1(sK0)))
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f131])).

fof(f131,plain,
    ( spl6_6
  <=> r2_hidden(sK3,k2_enumset1(k2_mcart_1(sK0),k2_mcart_1(sK0),k2_mcart_1(sK0),k2_mcart_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f74,plain,
    ( sK3 != k2_mcart_1(sK0)
    | spl6_3 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl6_3
  <=> sK3 = k2_mcart_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f143,plain,
    ( spl6_2
    | ~ spl6_5 ),
    inference(avatar_contradiction_clause,[],[f139])).

fof(f139,plain,
    ( $false
    | spl6_2
    | ~ spl6_5 ),
    inference(unit_resulting_resolution,[],[f69,f123,f97])).

fof(f123,plain,
    ( r2_hidden(sK1,k2_enumset1(k1_mcart_1(sK0),k1_mcart_1(sK0),k1_mcart_1(sK0),k1_mcart_1(sK0)))
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f121])).

fof(f121,plain,
    ( spl6_5
  <=> r2_hidden(sK1,k2_enumset1(k1_mcart_1(sK0),k1_mcart_1(sK0),k1_mcart_1(sK0),k1_mcart_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f69,plain,
    ( sK1 != k1_mcart_1(sK0)
    | spl6_2 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl6_2
  <=> sK1 = k1_mcart_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f134,plain,
    ( spl6_1
    | spl6_6 ),
    inference(avatar_split_clause,[],[f128,f131,f63])).

fof(f63,plain,
    ( spl6_1
  <=> sK4 = k2_mcart_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f128,plain,
    ( r2_hidden(sK3,k2_enumset1(k2_mcart_1(sK0),k2_mcart_1(sK0),k2_mcart_1(sK0),k2_mcart_1(sK0)))
    | sK4 = k2_mcart_1(sK0) ),
    inference(resolution,[],[f115,f97])).

fof(f115,plain,(
    ! [X0] :
      ( r2_hidden(sK4,k2_enumset1(X0,X0,X0,k2_mcart_1(sK0)))
      | r2_hidden(sK3,k2_enumset1(X0,X0,X0,k2_mcart_1(sK0))) ) ),
    inference(resolution,[],[f109,f83])).

fof(f83,plain,(
    ! [X0,X1] : r2_hidden(X0,k2_enumset1(X1,X1,X1,X0)) ),
    inference(resolution,[],[f54,f57])).

fof(f57,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_enumset1(X0,X0,X0,X1),X2)
      | r2_hidden(X1,X2) ) ),
    inference(definition_unfolding,[],[f42,f48])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f109,plain,(
    ! [X7] :
      ( ~ r2_hidden(k2_mcart_1(sK0),X7)
      | r2_hidden(sK4,X7)
      | r2_hidden(sK3,X7) ) ),
    inference(resolution,[],[f105,f87])).

fof(f87,plain,(
    r2_hidden(k2_mcart_1(sK0),k2_enumset1(sK3,sK3,sK3,sK4)) ),
    inference(resolution,[],[f50,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k2_mcart_1(X0),X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f50,plain,(
    r2_hidden(sK0,k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK2),k2_enumset1(sK3,sK3,sK3,sK4))) ),
    inference(definition_unfolding,[],[f22,f48,f48])).

fof(f22,plain,(
    r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4))) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( ( ( k2_mcart_1(X0) != X4
          & k2_mcart_1(X0) != X3 )
        | ( k1_mcart_1(X0) != X2
          & k1_mcart_1(X0) != X1 ) )
      & r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ( r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4)))
       => ( ( k2_mcart_1(X0) = X4
            | k2_mcart_1(X0) = X3 )
          & ( k1_mcart_1(X0) = X2
            | k1_mcart_1(X0) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2,X3,X4] :
      ( r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4)))
     => ( ( k2_mcart_1(X0) = X4
          | k2_mcart_1(X0) = X3 )
        & ( k1_mcart_1(X0) = X2
          | k1_mcart_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_mcart_1)).

fof(f105,plain,(
    ! [X10,X8,X11,X9] :
      ( ~ r2_hidden(X11,k2_enumset1(X9,X9,X9,X10))
      | ~ r2_hidden(X11,X8)
      | r2_hidden(X10,X8)
      | r2_hidden(X9,X8) ) ),
    inference(superposition,[],[f60,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X2,k2_enumset1(X0,X0,X0,X1)) = X2
      | r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f44,f48])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | r2_hidden(X1,X2)
      | k4_xboole_0(X2,k2_tarski(X0,X1)) = X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X2,k2_tarski(X0,X1)) = X2
      | r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ~ ( k4_xboole_0(X2,k2_tarski(X0,X1)) != X2
        & ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_zfmisc_1)).

fof(f60,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
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

fof(f124,plain,
    ( spl6_4
    | spl6_5 ),
    inference(avatar_split_clause,[],[f118,f121,f77])).

fof(f77,plain,
    ( spl6_4
  <=> sK2 = k1_mcart_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f118,plain,
    ( r2_hidden(sK1,k2_enumset1(k1_mcart_1(sK0),k1_mcart_1(sK0),k1_mcart_1(sK0),k1_mcart_1(sK0)))
    | sK2 = k1_mcart_1(sK0) ),
    inference(resolution,[],[f111,f97])).

fof(f111,plain,(
    ! [X0] :
      ( r2_hidden(sK2,k2_enumset1(X0,X0,X0,k1_mcart_1(sK0)))
      | r2_hidden(sK1,k2_enumset1(X0,X0,X0,k1_mcart_1(sK0))) ) ),
    inference(resolution,[],[f108,f83])).

fof(f108,plain,(
    ! [X6] :
      ( ~ r2_hidden(k1_mcart_1(sK0),X6)
      | r2_hidden(sK2,X6)
      | r2_hidden(sK1,X6) ) ),
    inference(resolution,[],[f105,f88])).

fof(f88,plain,(
    r2_hidden(k1_mcart_1(sK0),k2_enumset1(sK1,sK1,sK1,sK2)) ),
    inference(resolution,[],[f50,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f81,plain,
    ( ~ spl6_3
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f18,f77,f72])).

fof(f18,plain,
    ( sK2 != k1_mcart_1(sK0)
    | sK3 != k2_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f80,plain,
    ( ~ spl6_1
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f19,f77,f63])).

fof(f19,plain,
    ( sK2 != k1_mcart_1(sK0)
    | sK4 != k2_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f75,plain,
    ( ~ spl6_3
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f20,f67,f72])).

fof(f20,plain,
    ( sK1 != k1_mcart_1(sK0)
    | sK3 != k2_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f70,plain,
    ( ~ spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f21,f67,f63])).

fof(f21,plain,
    ( sK1 != k1_mcart_1(sK0)
    | sK4 != k2_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:32:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.49  % (27768)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.50  % (27760)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.50  % (27760)Refutation not found, incomplete strategy% (27760)------------------------------
% 0.20/0.50  % (27760)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (27760)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (27760)Memory used [KB]: 10746
% 0.20/0.50  % (27760)Time elapsed: 0.071 s
% 0.20/0.50  % (27760)------------------------------
% 0.20/0.50  % (27760)------------------------------
% 0.20/0.50  % (27768)Refutation not found, incomplete strategy% (27768)------------------------------
% 0.20/0.50  % (27768)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (27768)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (27768)Memory used [KB]: 1663
% 0.20/0.50  % (27768)Time elapsed: 0.072 s
% 0.20/0.50  % (27768)------------------------------
% 0.20/0.50  % (27768)------------------------------
% 0.20/0.51  % (27756)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.51  % (27772)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.51  % (27754)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.52  % (27764)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.52  % (27764)Refutation not found, incomplete strategy% (27764)------------------------------
% 0.20/0.52  % (27764)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (27764)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (27764)Memory used [KB]: 1663
% 0.20/0.52  % (27764)Time elapsed: 0.063 s
% 0.20/0.52  % (27764)------------------------------
% 0.20/0.52  % (27764)------------------------------
% 1.31/0.53  % (27750)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.31/0.54  % (27755)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.31/0.54  % (27752)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.31/0.54  % (27773)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.31/0.54  % (27777)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.31/0.55  % (27777)Refutation not found, incomplete strategy% (27777)------------------------------
% 1.31/0.55  % (27777)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.55  % (27777)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.55  
% 1.31/0.55  % (27777)Memory used [KB]: 6140
% 1.31/0.55  % (27777)Time elapsed: 0.140 s
% 1.31/0.55  % (27777)------------------------------
% 1.31/0.55  % (27777)------------------------------
% 1.31/0.55  % (27779)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.31/0.55  % (27770)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.31/0.55  % (27779)Refutation not found, incomplete strategy% (27779)------------------------------
% 1.31/0.55  % (27779)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.55  % (27779)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.55  
% 1.31/0.55  % (27779)Memory used [KB]: 1663
% 1.31/0.55  % (27779)Time elapsed: 0.138 s
% 1.31/0.55  % (27779)------------------------------
% 1.31/0.55  % (27779)------------------------------
% 1.31/0.55  % (27753)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.31/0.55  % (27765)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.31/0.55  % (27769)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.31/0.55  % (27771)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.50/0.55  % (27751)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.50/0.55  % (27751)Refutation not found, incomplete strategy% (27751)------------------------------
% 1.50/0.55  % (27751)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.55  % (27751)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.55  
% 1.50/0.55  % (27751)Memory used [KB]: 1663
% 1.50/0.55  % (27751)Time elapsed: 0.134 s
% 1.50/0.55  % (27751)------------------------------
% 1.50/0.55  % (27751)------------------------------
% 1.50/0.55  % (27762)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.50/0.55  % (27763)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.50/0.55  % (27762)Refutation not found, incomplete strategy% (27762)------------------------------
% 1.50/0.55  % (27762)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.55  % (27757)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.50/0.55  % (27761)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.50/0.55  % (27778)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.50/0.56  % (27763)Refutation found. Thanks to Tanya!
% 1.50/0.56  % SZS status Theorem for theBenchmark
% 1.50/0.56  % (27758)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.50/0.56  % (27774)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.50/0.56  % (27766)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.50/0.56  % (27778)Refutation not found, incomplete strategy% (27778)------------------------------
% 1.50/0.56  % (27778)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.56  % (27778)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.56  
% 1.50/0.56  % (27778)Memory used [KB]: 10746
% 1.50/0.56  % (27778)Time elapsed: 0.148 s
% 1.50/0.56  % (27778)------------------------------
% 1.50/0.56  % (27778)------------------------------
% 1.50/0.56  % (27762)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.56  
% 1.50/0.56  % (27762)Memory used [KB]: 10618
% 1.50/0.56  % (27762)Time elapsed: 0.141 s
% 1.50/0.56  % (27762)------------------------------
% 1.50/0.56  % (27762)------------------------------
% 1.50/0.57  % SZS output start Proof for theBenchmark
% 1.50/0.57  fof(f170,plain,(
% 1.50/0.57    $false),
% 1.50/0.57    inference(avatar_sat_refutation,[],[f70,f75,f80,f81,f124,f134,f143,f169])).
% 1.50/0.57  fof(f169,plain,(
% 1.50/0.57    spl6_3 | ~spl6_6),
% 1.50/0.57    inference(avatar_contradiction_clause,[],[f165])).
% 1.50/0.57  fof(f165,plain,(
% 1.50/0.57    $false | (spl6_3 | ~spl6_6)),
% 1.50/0.57    inference(unit_resulting_resolution,[],[f74,f133,f97])).
% 1.50/0.57  fof(f97,plain,(
% 1.50/0.57    ( ! [X0,X1] : (~r2_hidden(X0,k2_enumset1(X1,X1,X1,X1)) | X0 = X1) )),
% 1.50/0.57    inference(condensation,[],[f96])).
% 1.50/0.57  fof(f96,plain,(
% 1.50/0.57    ( ! [X2,X0,X3,X1] : (X0 = X2 | ~r2_hidden(X1,X3) | ~r2_hidden(X0,k2_enumset1(X2,X2,X2,X2))) )),
% 1.50/0.57    inference(forward_demodulation,[],[f95,f25])).
% 1.50/0.57  fof(f25,plain,(
% 1.50/0.57    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 1.50/0.57    inference(cnf_transformation,[],[f11])).
% 1.50/0.57  fof(f11,axiom,(
% 1.50/0.57    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 1.50/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).
% 1.50/0.57  fof(f95,plain,(
% 1.50/0.57    ( ! [X2,X0,X3,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X2 | ~r2_hidden(X1,X3) | ~r2_hidden(X0,k2_enumset1(X2,X2,X2,X2))) )),
% 1.50/0.57    inference(resolution,[],[f52,f47])).
% 1.50/0.57  fof(f47,plain,(
% 1.50/0.57    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 1.50/0.57    inference(cnf_transformation,[],[f6])).
% 1.50/0.57  fof(f6,axiom,(
% 1.50/0.57    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 1.50/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 1.50/0.57  fof(f52,plain,(
% 1.50/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(k2_enumset1(X1,X1,X1,X1),X2)) | k1_mcart_1(X0) = X1) )),
% 1.50/0.57    inference(definition_unfolding,[],[f33,f49])).
% 1.50/0.57  fof(f49,plain,(
% 1.50/0.57    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.50/0.57    inference(definition_unfolding,[],[f23,f48])).
% 1.50/0.57  fof(f48,plain,(
% 1.50/0.57    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.50/0.57    inference(definition_unfolding,[],[f24,f30])).
% 1.50/0.57  fof(f30,plain,(
% 1.50/0.57    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.50/0.57    inference(cnf_transformation,[],[f5])).
% 1.50/0.57  fof(f5,axiom,(
% 1.50/0.57    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.50/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.50/0.57  fof(f24,plain,(
% 1.50/0.57    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.50/0.57    inference(cnf_transformation,[],[f4])).
% 1.50/0.57  fof(f4,axiom,(
% 1.50/0.57    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.50/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.50/0.57  fof(f23,plain,(
% 1.50/0.57    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.50/0.57    inference(cnf_transformation,[],[f3])).
% 1.50/0.57  fof(f3,axiom,(
% 1.50/0.57    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.50/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.50/0.57  fof(f33,plain,(
% 1.50/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) | k1_mcart_1(X0) = X1) )),
% 1.50/0.57    inference(cnf_transformation,[],[f16])).
% 1.50/0.57  fof(f16,plain,(
% 1.50/0.57    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & k1_mcart_1(X0) = X1) | ~r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)))),
% 1.50/0.57    inference(ennf_transformation,[],[f10])).
% 1.50/0.57  fof(f10,axiom,(
% 1.50/0.57    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) => (r2_hidden(k2_mcart_1(X0),X2) & k1_mcart_1(X0) = X1))),
% 1.50/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_mcart_1)).
% 1.50/0.57  fof(f133,plain,(
% 1.50/0.57    r2_hidden(sK3,k2_enumset1(k2_mcart_1(sK0),k2_mcart_1(sK0),k2_mcart_1(sK0),k2_mcart_1(sK0))) | ~spl6_6),
% 1.50/0.57    inference(avatar_component_clause,[],[f131])).
% 1.50/0.57  fof(f131,plain,(
% 1.50/0.57    spl6_6 <=> r2_hidden(sK3,k2_enumset1(k2_mcart_1(sK0),k2_mcart_1(sK0),k2_mcart_1(sK0),k2_mcart_1(sK0)))),
% 1.50/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 1.50/0.57  fof(f74,plain,(
% 1.50/0.57    sK3 != k2_mcart_1(sK0) | spl6_3),
% 1.50/0.57    inference(avatar_component_clause,[],[f72])).
% 1.50/0.57  fof(f72,plain,(
% 1.50/0.57    spl6_3 <=> sK3 = k2_mcart_1(sK0)),
% 1.50/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 1.50/0.57  fof(f143,plain,(
% 1.50/0.57    spl6_2 | ~spl6_5),
% 1.50/0.57    inference(avatar_contradiction_clause,[],[f139])).
% 1.50/0.57  fof(f139,plain,(
% 1.50/0.57    $false | (spl6_2 | ~spl6_5)),
% 1.50/0.57    inference(unit_resulting_resolution,[],[f69,f123,f97])).
% 1.50/0.57  fof(f123,plain,(
% 1.50/0.57    r2_hidden(sK1,k2_enumset1(k1_mcart_1(sK0),k1_mcart_1(sK0),k1_mcart_1(sK0),k1_mcart_1(sK0))) | ~spl6_5),
% 1.50/0.57    inference(avatar_component_clause,[],[f121])).
% 1.50/0.57  fof(f121,plain,(
% 1.50/0.57    spl6_5 <=> r2_hidden(sK1,k2_enumset1(k1_mcart_1(sK0),k1_mcart_1(sK0),k1_mcart_1(sK0),k1_mcart_1(sK0)))),
% 1.50/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 1.50/0.57  fof(f69,plain,(
% 1.50/0.57    sK1 != k1_mcart_1(sK0) | spl6_2),
% 1.50/0.57    inference(avatar_component_clause,[],[f67])).
% 1.50/0.57  fof(f67,plain,(
% 1.50/0.57    spl6_2 <=> sK1 = k1_mcart_1(sK0)),
% 1.50/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 1.50/0.57  fof(f134,plain,(
% 1.50/0.57    spl6_1 | spl6_6),
% 1.50/0.57    inference(avatar_split_clause,[],[f128,f131,f63])).
% 1.50/0.57  fof(f63,plain,(
% 1.50/0.57    spl6_1 <=> sK4 = k2_mcart_1(sK0)),
% 1.50/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 1.50/0.57  fof(f128,plain,(
% 1.50/0.57    r2_hidden(sK3,k2_enumset1(k2_mcart_1(sK0),k2_mcart_1(sK0),k2_mcart_1(sK0),k2_mcart_1(sK0))) | sK4 = k2_mcart_1(sK0)),
% 1.50/0.57    inference(resolution,[],[f115,f97])).
% 1.50/0.57  fof(f115,plain,(
% 1.50/0.57    ( ! [X0] : (r2_hidden(sK4,k2_enumset1(X0,X0,X0,k2_mcart_1(sK0))) | r2_hidden(sK3,k2_enumset1(X0,X0,X0,k2_mcart_1(sK0)))) )),
% 1.50/0.57    inference(resolution,[],[f109,f83])).
% 1.50/0.57  fof(f83,plain,(
% 1.50/0.57    ( ! [X0,X1] : (r2_hidden(X0,k2_enumset1(X1,X1,X1,X0))) )),
% 1.50/0.57    inference(resolution,[],[f54,f57])).
% 1.50/0.57  fof(f57,plain,(
% 1.50/0.57    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.50/0.57    inference(equality_resolution,[],[f28])).
% 1.50/0.57  fof(f28,plain,(
% 1.50/0.57    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.50/0.57    inference(cnf_transformation,[],[f2])).
% 1.50/0.57  fof(f2,axiom,(
% 1.50/0.57    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.50/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.50/0.57  fof(f54,plain,(
% 1.50/0.57    ( ! [X2,X0,X1] : (~r1_tarski(k2_enumset1(X0,X0,X0,X1),X2) | r2_hidden(X1,X2)) )),
% 1.50/0.57    inference(definition_unfolding,[],[f42,f48])).
% 1.50/0.57  fof(f42,plain,(
% 1.50/0.57    ( ! [X2,X0,X1] : (r2_hidden(X1,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 1.50/0.57    inference(cnf_transformation,[],[f8])).
% 1.50/0.57  fof(f8,axiom,(
% 1.50/0.57    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 1.50/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 1.50/0.57  fof(f109,plain,(
% 1.50/0.57    ( ! [X7] : (~r2_hidden(k2_mcart_1(sK0),X7) | r2_hidden(sK4,X7) | r2_hidden(sK3,X7)) )),
% 1.50/0.57    inference(resolution,[],[f105,f87])).
% 1.50/0.57  fof(f87,plain,(
% 1.50/0.57    r2_hidden(k2_mcart_1(sK0),k2_enumset1(sK3,sK3,sK3,sK4))),
% 1.50/0.57    inference(resolution,[],[f50,f32])).
% 1.50/0.57  fof(f32,plain,(
% 1.50/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k2_mcart_1(X0),X2)) )),
% 1.50/0.57    inference(cnf_transformation,[],[f15])).
% 1.50/0.57  fof(f15,plain,(
% 1.50/0.57    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 1.50/0.57    inference(ennf_transformation,[],[f9])).
% 1.50/0.57  fof(f9,axiom,(
% 1.50/0.57    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 1.50/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).
% 1.50/0.57  fof(f50,plain,(
% 1.50/0.57    r2_hidden(sK0,k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK2),k2_enumset1(sK3,sK3,sK3,sK4)))),
% 1.50/0.57    inference(definition_unfolding,[],[f22,f48,f48])).
% 1.50/0.57  fof(f22,plain,(
% 1.50/0.57    r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)))),
% 1.50/0.57    inference(cnf_transformation,[],[f14])).
% 1.50/0.57  fof(f14,plain,(
% 1.50/0.57    ? [X0,X1,X2,X3,X4] : (((k2_mcart_1(X0) != X4 & k2_mcart_1(X0) != X3) | (k1_mcart_1(X0) != X2 & k1_mcart_1(X0) != X1)) & r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4))))),
% 1.50/0.57    inference(ennf_transformation,[],[f13])).
% 1.50/0.57  fof(f13,negated_conjecture,(
% 1.50/0.57    ~! [X0,X1,X2,X3,X4] : (r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4))) => ((k2_mcart_1(X0) = X4 | k2_mcart_1(X0) = X3) & (k1_mcart_1(X0) = X2 | k1_mcart_1(X0) = X1)))),
% 1.50/0.57    inference(negated_conjecture,[],[f12])).
% 1.50/0.57  fof(f12,conjecture,(
% 1.50/0.57    ! [X0,X1,X2,X3,X4] : (r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4))) => ((k2_mcart_1(X0) = X4 | k2_mcart_1(X0) = X3) & (k1_mcart_1(X0) = X2 | k1_mcart_1(X0) = X1)))),
% 1.50/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_mcart_1)).
% 1.50/0.57  fof(f105,plain,(
% 1.50/0.57    ( ! [X10,X8,X11,X9] : (~r2_hidden(X11,k2_enumset1(X9,X9,X9,X10)) | ~r2_hidden(X11,X8) | r2_hidden(X10,X8) | r2_hidden(X9,X8)) )),
% 1.50/0.57    inference(superposition,[],[f60,f56])).
% 1.50/0.57  fof(f56,plain,(
% 1.50/0.57    ( ! [X2,X0,X1] : (k4_xboole_0(X2,k2_enumset1(X0,X0,X0,X1)) = X2 | r2_hidden(X1,X2) | r2_hidden(X0,X2)) )),
% 1.50/0.57    inference(definition_unfolding,[],[f44,f48])).
% 1.50/0.57  fof(f44,plain,(
% 1.50/0.57    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | r2_hidden(X1,X2) | k4_xboole_0(X2,k2_tarski(X0,X1)) = X2) )),
% 1.50/0.57    inference(cnf_transformation,[],[f17])).
% 1.50/0.57  fof(f17,plain,(
% 1.50/0.57    ! [X0,X1,X2] : (k4_xboole_0(X2,k2_tarski(X0,X1)) = X2 | r2_hidden(X1,X2) | r2_hidden(X0,X2))),
% 1.50/0.57    inference(ennf_transformation,[],[f7])).
% 1.50/0.57  fof(f7,axiom,(
% 1.50/0.57    ! [X0,X1,X2] : ~(k4_xboole_0(X2,k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2))),
% 1.50/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_zfmisc_1)).
% 1.50/0.57  fof(f60,plain,(
% 1.50/0.57    ( ! [X0,X3,X1] : (~r2_hidden(X3,k4_xboole_0(X0,X1)) | ~r2_hidden(X3,X1)) )),
% 1.50/0.57    inference(equality_resolution,[],[f39])).
% 1.50/0.57  fof(f39,plain,(
% 1.50/0.57    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.50/0.57    inference(cnf_transformation,[],[f1])).
% 1.50/0.57  fof(f1,axiom,(
% 1.50/0.57    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.50/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.50/0.57  fof(f124,plain,(
% 1.50/0.57    spl6_4 | spl6_5),
% 1.50/0.57    inference(avatar_split_clause,[],[f118,f121,f77])).
% 1.50/0.57  fof(f77,plain,(
% 1.50/0.57    spl6_4 <=> sK2 = k1_mcart_1(sK0)),
% 1.50/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 1.50/0.57  fof(f118,plain,(
% 1.50/0.57    r2_hidden(sK1,k2_enumset1(k1_mcart_1(sK0),k1_mcart_1(sK0),k1_mcart_1(sK0),k1_mcart_1(sK0))) | sK2 = k1_mcart_1(sK0)),
% 1.50/0.57    inference(resolution,[],[f111,f97])).
% 1.50/0.57  fof(f111,plain,(
% 1.50/0.57    ( ! [X0] : (r2_hidden(sK2,k2_enumset1(X0,X0,X0,k1_mcart_1(sK0))) | r2_hidden(sK1,k2_enumset1(X0,X0,X0,k1_mcart_1(sK0)))) )),
% 1.50/0.57    inference(resolution,[],[f108,f83])).
% 1.50/0.57  fof(f108,plain,(
% 1.50/0.57    ( ! [X6] : (~r2_hidden(k1_mcart_1(sK0),X6) | r2_hidden(sK2,X6) | r2_hidden(sK1,X6)) )),
% 1.50/0.57    inference(resolution,[],[f105,f88])).
% 1.50/0.57  fof(f88,plain,(
% 1.50/0.57    r2_hidden(k1_mcart_1(sK0),k2_enumset1(sK1,sK1,sK1,sK2))),
% 1.50/0.57    inference(resolution,[],[f50,f31])).
% 1.50/0.57  fof(f31,plain,(
% 1.50/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k1_mcart_1(X0),X1)) )),
% 1.50/0.57    inference(cnf_transformation,[],[f15])).
% 1.50/0.57  fof(f81,plain,(
% 1.50/0.57    ~spl6_3 | ~spl6_4),
% 1.50/0.57    inference(avatar_split_clause,[],[f18,f77,f72])).
% 1.50/0.57  fof(f18,plain,(
% 1.50/0.57    sK2 != k1_mcart_1(sK0) | sK3 != k2_mcart_1(sK0)),
% 1.50/0.57    inference(cnf_transformation,[],[f14])).
% 1.50/0.57  fof(f80,plain,(
% 1.50/0.57    ~spl6_1 | ~spl6_4),
% 1.50/0.57    inference(avatar_split_clause,[],[f19,f77,f63])).
% 1.50/0.57  fof(f19,plain,(
% 1.50/0.57    sK2 != k1_mcart_1(sK0) | sK4 != k2_mcart_1(sK0)),
% 1.50/0.57    inference(cnf_transformation,[],[f14])).
% 1.50/0.57  fof(f75,plain,(
% 1.50/0.57    ~spl6_3 | ~spl6_2),
% 1.50/0.57    inference(avatar_split_clause,[],[f20,f67,f72])).
% 1.50/0.57  fof(f20,plain,(
% 1.50/0.57    sK1 != k1_mcart_1(sK0) | sK3 != k2_mcart_1(sK0)),
% 1.50/0.57    inference(cnf_transformation,[],[f14])).
% 1.50/0.57  fof(f70,plain,(
% 1.50/0.57    ~spl6_1 | ~spl6_2),
% 1.50/0.57    inference(avatar_split_clause,[],[f21,f67,f63])).
% 1.50/0.57  fof(f21,plain,(
% 1.50/0.57    sK1 != k1_mcart_1(sK0) | sK4 != k2_mcart_1(sK0)),
% 1.50/0.57    inference(cnf_transformation,[],[f14])).
% 1.50/0.57  % SZS output end Proof for theBenchmark
% 1.50/0.57  % (27763)------------------------------
% 1.50/0.57  % (27763)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.57  % (27763)Termination reason: Refutation
% 1.50/0.57  
% 1.50/0.57  % (27763)Memory used [KB]: 6268
% 1.50/0.57  % (27763)Time elapsed: 0.145 s
% 1.50/0.57  % (27763)------------------------------
% 1.50/0.57  % (27763)------------------------------
% 1.50/0.57  % (27746)Success in time 0.203 s
%------------------------------------------------------------------------------
