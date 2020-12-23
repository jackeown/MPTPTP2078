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
% DateTime   : Thu Dec  3 12:58:13 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 118 expanded)
%              Number of leaves         :   18 (  55 expanded)
%              Depth                    :    7
%              Number of atoms          :  175 ( 334 expanded)
%              Number of equality atoms :   26 (  71 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f110,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f25,f30,f35,f40,f44,f48,f52,f66,f72,f78,f84,f101,f106,f109])).

fof(f109,plain,
    ( spl5_1
    | ~ spl5_13
    | ~ spl5_17 ),
    inference(avatar_contradiction_clause,[],[f108])).

fof(f108,plain,
    ( $false
    | spl5_1
    | ~ spl5_13
    | ~ spl5_17 ),
    inference(subsumption_resolution,[],[f107,f24])).

fof(f24,plain,
    ( ~ r2_hidden(sK0,k2_zfmisc_1(sK1,sK2))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f22])).

fof(f22,plain,
    ( spl5_1
  <=> r2_hidden(sK0,k2_zfmisc_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f107,plain,
    ( r2_hidden(sK0,k2_zfmisc_1(sK1,sK2))
    | ~ spl5_13
    | ~ spl5_17 ),
    inference(resolution,[],[f105,f83])).

fof(f83,plain,
    ( r2_hidden(sK3,sK1)
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl5_13
  <=> r2_hidden(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f105,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3,X0)
        | r2_hidden(sK0,k2_zfmisc_1(X0,sK2)) )
    | ~ spl5_17 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl5_17
  <=> ! [X0] :
        ( r2_hidden(sK0,k2_zfmisc_1(X0,sK2))
        | ~ r2_hidden(sK3,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f106,plain,
    ( spl5_17
    | ~ spl5_11
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f102,f99,f69,f104])).

fof(f69,plain,
    ( spl5_11
  <=> r2_hidden(sK4,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f99,plain,
    ( spl5_16
  <=> ! [X1,X0] :
        ( r2_hidden(sK0,k2_zfmisc_1(X0,X1))
        | ~ r2_hidden(sK4,X1)
        | ~ r2_hidden(sK3,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f102,plain,
    ( ! [X0] :
        ( r2_hidden(sK0,k2_zfmisc_1(X0,sK2))
        | ~ r2_hidden(sK3,X0) )
    | ~ spl5_11
    | ~ spl5_16 ),
    inference(resolution,[],[f100,f71])).

fof(f71,plain,
    ( r2_hidden(sK4,sK2)
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f69])).

fof(f100,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK4,X1)
        | r2_hidden(sK0,k2_zfmisc_1(X0,X1))
        | ~ r2_hidden(sK3,X0) )
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f99])).

fof(f101,plain,
    ( spl5_16
    | ~ spl5_2
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f97,f50,f27,f99])).

fof(f27,plain,
    ( spl5_2
  <=> sK0 = k4_tarski(sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f50,plain,
    ( spl5_7
  <=> ! [X1,X3,X0,X2] :
        ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f97,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK0,k2_zfmisc_1(X0,X1))
        | ~ r2_hidden(sK4,X1)
        | ~ r2_hidden(sK3,X0) )
    | ~ spl5_2
    | ~ spl5_7 ),
    inference(superposition,[],[f51,f29])).

fof(f29,plain,
    ( sK0 = k4_tarski(sK3,sK4)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f27])).

fof(f51,plain,
    ( ! [X2,X0,X3,X1] :
        ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f50])).

fof(f84,plain,
    ( spl5_13
    | ~ spl5_4
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f79,f75,f37,f81])).

fof(f37,plain,
    ( spl5_4
  <=> r2_hidden(k1_mcart_1(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f75,plain,
    ( spl5_12
  <=> k1_mcart_1(sK0) = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f79,plain,
    ( r2_hidden(sK3,sK1)
    | ~ spl5_4
    | ~ spl5_12 ),
    inference(superposition,[],[f39,f77])).

fof(f77,plain,
    ( k1_mcart_1(sK0) = sK3
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f75])).

fof(f39,plain,
    ( r2_hidden(k1_mcart_1(sK0),sK1)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f37])).

fof(f78,plain,
    ( spl5_12
    | ~ spl5_2
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f73,f46,f27,f75])).

fof(f46,plain,
    ( spl5_6
  <=> ! [X1,X0] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f73,plain,
    ( k1_mcart_1(sK0) = sK3
    | ~ spl5_2
    | ~ spl5_6 ),
    inference(superposition,[],[f47,f29])).

fof(f47,plain,
    ( ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f46])).

fof(f72,plain,
    ( spl5_11
    | ~ spl5_3
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f67,f63,f32,f69])).

fof(f32,plain,
    ( spl5_3
  <=> r2_hidden(k2_mcart_1(sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f63,plain,
    ( spl5_10
  <=> k2_mcart_1(sK0) = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f67,plain,
    ( r2_hidden(sK4,sK2)
    | ~ spl5_3
    | ~ spl5_10 ),
    inference(superposition,[],[f34,f65])).

fof(f65,plain,
    ( k2_mcart_1(sK0) = sK4
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f63])).

fof(f34,plain,
    ( r2_hidden(k2_mcart_1(sK0),sK2)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f32])).

fof(f66,plain,
    ( spl5_10
    | ~ spl5_2
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f61,f42,f27,f63])).

fof(f42,plain,
    ( spl5_5
  <=> ! [X1,X0] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f61,plain,
    ( k2_mcart_1(sK0) = sK4
    | ~ spl5_2
    | ~ spl5_5 ),
    inference(superposition,[],[f43,f29])).

fof(f43,plain,
    ( ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f42])).

fof(f52,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f20,f50])).

% (23320)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
fof(f20,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f11])).

% (23318)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
fof(f11,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f48,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f16,f46])).

fof(f16,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f44,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f17,f42])).

fof(f17,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f2])).

fof(f40,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f12,f37])).

fof(f12,plain,(
    r2_hidden(k1_mcart_1(sK0),sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,
    ( ~ r2_hidden(sK0,k2_zfmisc_1(sK1,sK2))
    & sK0 = k4_tarski(sK3,sK4)
    & r2_hidden(k2_mcart_1(sK0),sK2)
    & r2_hidden(k1_mcart_1(sK0),sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f6,f8,f7])).

fof(f7,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
        & ? [X3,X4] : k4_tarski(X3,X4) = X0
        & r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
   => ( ~ r2_hidden(sK0,k2_zfmisc_1(sK1,sK2))
      & ? [X4,X3] : k4_tarski(X3,X4) = sK0
      & r2_hidden(k2_mcart_1(sK0),sK2)
      & r2_hidden(k1_mcart_1(sK0),sK1) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,
    ( ? [X4,X3] : k4_tarski(X3,X4) = sK0
   => sK0 = k4_tarski(sK3,sK4) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      & ? [X3,X4] : k4_tarski(X3,X4) = X0
      & r2_hidden(k2_mcart_1(X0),X2)
      & r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      & ? [X3,X4] : k4_tarski(X3,X4) = X0
      & r2_hidden(k2_mcart_1(X0),X2)
      & r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r2_hidden(k2_mcart_1(X0),X2)
          & r2_hidden(k1_mcart_1(X0),X1) )
       => ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
          | ! [X3,X4] : k4_tarski(X3,X4) != X0 ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
     => ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
        | ! [X3,X4] : k4_tarski(X3,X4) != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_mcart_1)).

fof(f35,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f13,f32])).

fof(f13,plain,(
    r2_hidden(k2_mcart_1(sK0),sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f30,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f14,f27])).

fof(f14,plain,(
    sK0 = k4_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f9])).

% (23329)lrs+10_5:1_add=large:afp=1000:afq=1.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=fast:fsr=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=2:nwc=1:stl=210:uhcvi=on_1759 on theBenchmark
fof(f25,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f15,f22])).

fof(f15,plain,(
    ~ r2_hidden(sK0,k2_zfmisc_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:56:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.41  % (23325)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.20/0.43  % (23323)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.20/0.43  % (23321)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.20/0.43  % (23324)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.20/0.44  % (23321)Refutation found. Thanks to Tanya!
% 0.20/0.44  % SZS status Theorem for theBenchmark
% 0.20/0.44  % SZS output start Proof for theBenchmark
% 0.20/0.44  fof(f110,plain,(
% 0.20/0.44    $false),
% 0.20/0.44    inference(avatar_sat_refutation,[],[f25,f30,f35,f40,f44,f48,f52,f66,f72,f78,f84,f101,f106,f109])).
% 0.20/0.44  fof(f109,plain,(
% 0.20/0.44    spl5_1 | ~spl5_13 | ~spl5_17),
% 0.20/0.44    inference(avatar_contradiction_clause,[],[f108])).
% 0.20/0.44  fof(f108,plain,(
% 0.20/0.44    $false | (spl5_1 | ~spl5_13 | ~spl5_17)),
% 0.20/0.44    inference(subsumption_resolution,[],[f107,f24])).
% 0.20/0.44  fof(f24,plain,(
% 0.20/0.44    ~r2_hidden(sK0,k2_zfmisc_1(sK1,sK2)) | spl5_1),
% 0.20/0.44    inference(avatar_component_clause,[],[f22])).
% 0.20/0.44  fof(f22,plain,(
% 0.20/0.44    spl5_1 <=> r2_hidden(sK0,k2_zfmisc_1(sK1,sK2))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.20/0.44  fof(f107,plain,(
% 0.20/0.44    r2_hidden(sK0,k2_zfmisc_1(sK1,sK2)) | (~spl5_13 | ~spl5_17)),
% 0.20/0.44    inference(resolution,[],[f105,f83])).
% 0.20/0.44  fof(f83,plain,(
% 0.20/0.44    r2_hidden(sK3,sK1) | ~spl5_13),
% 0.20/0.44    inference(avatar_component_clause,[],[f81])).
% 0.20/0.44  fof(f81,plain,(
% 0.20/0.44    spl5_13 <=> r2_hidden(sK3,sK1)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.20/0.44  fof(f105,plain,(
% 0.20/0.44    ( ! [X0] : (~r2_hidden(sK3,X0) | r2_hidden(sK0,k2_zfmisc_1(X0,sK2))) ) | ~spl5_17),
% 0.20/0.44    inference(avatar_component_clause,[],[f104])).
% 0.20/0.44  fof(f104,plain,(
% 0.20/0.44    spl5_17 <=> ! [X0] : (r2_hidden(sK0,k2_zfmisc_1(X0,sK2)) | ~r2_hidden(sK3,X0))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 0.20/0.44  fof(f106,plain,(
% 0.20/0.44    spl5_17 | ~spl5_11 | ~spl5_16),
% 0.20/0.44    inference(avatar_split_clause,[],[f102,f99,f69,f104])).
% 0.20/0.44  fof(f69,plain,(
% 0.20/0.44    spl5_11 <=> r2_hidden(sK4,sK2)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.20/0.44  fof(f99,plain,(
% 0.20/0.44    spl5_16 <=> ! [X1,X0] : (r2_hidden(sK0,k2_zfmisc_1(X0,X1)) | ~r2_hidden(sK4,X1) | ~r2_hidden(sK3,X0))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 0.20/0.44  fof(f102,plain,(
% 0.20/0.44    ( ! [X0] : (r2_hidden(sK0,k2_zfmisc_1(X0,sK2)) | ~r2_hidden(sK3,X0)) ) | (~spl5_11 | ~spl5_16)),
% 0.20/0.44    inference(resolution,[],[f100,f71])).
% 0.20/0.44  fof(f71,plain,(
% 0.20/0.44    r2_hidden(sK4,sK2) | ~spl5_11),
% 0.20/0.44    inference(avatar_component_clause,[],[f69])).
% 0.20/0.44  fof(f100,plain,(
% 0.20/0.44    ( ! [X0,X1] : (~r2_hidden(sK4,X1) | r2_hidden(sK0,k2_zfmisc_1(X0,X1)) | ~r2_hidden(sK3,X0)) ) | ~spl5_16),
% 0.20/0.44    inference(avatar_component_clause,[],[f99])).
% 0.20/0.44  fof(f101,plain,(
% 0.20/0.44    spl5_16 | ~spl5_2 | ~spl5_7),
% 0.20/0.44    inference(avatar_split_clause,[],[f97,f50,f27,f99])).
% 0.20/0.44  fof(f27,plain,(
% 0.20/0.44    spl5_2 <=> sK0 = k4_tarski(sK3,sK4)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.20/0.44  fof(f50,plain,(
% 0.20/0.44    spl5_7 <=> ! [X1,X3,X0,X2] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.20/0.44  fof(f97,plain,(
% 0.20/0.44    ( ! [X0,X1] : (r2_hidden(sK0,k2_zfmisc_1(X0,X1)) | ~r2_hidden(sK4,X1) | ~r2_hidden(sK3,X0)) ) | (~spl5_2 | ~spl5_7)),
% 0.20/0.44    inference(superposition,[],[f51,f29])).
% 0.20/0.44  fof(f29,plain,(
% 0.20/0.44    sK0 = k4_tarski(sK3,sK4) | ~spl5_2),
% 0.20/0.44    inference(avatar_component_clause,[],[f27])).
% 0.20/0.44  fof(f51,plain,(
% 0.20/0.44    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) ) | ~spl5_7),
% 0.20/0.44    inference(avatar_component_clause,[],[f50])).
% 0.20/0.44  fof(f84,plain,(
% 0.20/0.44    spl5_13 | ~spl5_4 | ~spl5_12),
% 0.20/0.44    inference(avatar_split_clause,[],[f79,f75,f37,f81])).
% 0.20/0.44  fof(f37,plain,(
% 0.20/0.44    spl5_4 <=> r2_hidden(k1_mcart_1(sK0),sK1)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.20/0.44  fof(f75,plain,(
% 0.20/0.44    spl5_12 <=> k1_mcart_1(sK0) = sK3),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.20/0.44  fof(f79,plain,(
% 0.20/0.44    r2_hidden(sK3,sK1) | (~spl5_4 | ~spl5_12)),
% 0.20/0.44    inference(superposition,[],[f39,f77])).
% 0.20/0.44  fof(f77,plain,(
% 0.20/0.44    k1_mcart_1(sK0) = sK3 | ~spl5_12),
% 0.20/0.44    inference(avatar_component_clause,[],[f75])).
% 0.20/0.44  fof(f39,plain,(
% 0.20/0.44    r2_hidden(k1_mcart_1(sK0),sK1) | ~spl5_4),
% 0.20/0.44    inference(avatar_component_clause,[],[f37])).
% 0.20/0.44  fof(f78,plain,(
% 0.20/0.44    spl5_12 | ~spl5_2 | ~spl5_6),
% 0.20/0.44    inference(avatar_split_clause,[],[f73,f46,f27,f75])).
% 0.20/0.44  fof(f46,plain,(
% 0.20/0.44    spl5_6 <=> ! [X1,X0] : k1_mcart_1(k4_tarski(X0,X1)) = X0),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.20/0.44  fof(f73,plain,(
% 0.20/0.44    k1_mcart_1(sK0) = sK3 | (~spl5_2 | ~spl5_6)),
% 0.20/0.44    inference(superposition,[],[f47,f29])).
% 0.20/0.44  fof(f47,plain,(
% 0.20/0.44    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) ) | ~spl5_6),
% 0.20/0.44    inference(avatar_component_clause,[],[f46])).
% 0.20/0.44  fof(f72,plain,(
% 0.20/0.44    spl5_11 | ~spl5_3 | ~spl5_10),
% 0.20/0.44    inference(avatar_split_clause,[],[f67,f63,f32,f69])).
% 0.20/0.44  fof(f32,plain,(
% 0.20/0.44    spl5_3 <=> r2_hidden(k2_mcart_1(sK0),sK2)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.20/0.44  fof(f63,plain,(
% 0.20/0.44    spl5_10 <=> k2_mcart_1(sK0) = sK4),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.20/0.44  fof(f67,plain,(
% 0.20/0.44    r2_hidden(sK4,sK2) | (~spl5_3 | ~spl5_10)),
% 0.20/0.44    inference(superposition,[],[f34,f65])).
% 0.20/0.44  fof(f65,plain,(
% 0.20/0.44    k2_mcart_1(sK0) = sK4 | ~spl5_10),
% 0.20/0.44    inference(avatar_component_clause,[],[f63])).
% 0.20/0.44  fof(f34,plain,(
% 0.20/0.44    r2_hidden(k2_mcart_1(sK0),sK2) | ~spl5_3),
% 0.20/0.44    inference(avatar_component_clause,[],[f32])).
% 0.20/0.44  fof(f66,plain,(
% 0.20/0.44    spl5_10 | ~spl5_2 | ~spl5_5),
% 0.20/0.44    inference(avatar_split_clause,[],[f61,f42,f27,f63])).
% 0.20/0.44  fof(f42,plain,(
% 0.20/0.44    spl5_5 <=> ! [X1,X0] : k2_mcart_1(k4_tarski(X0,X1)) = X1),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.20/0.44  fof(f61,plain,(
% 0.20/0.44    k2_mcart_1(sK0) = sK4 | (~spl5_2 | ~spl5_5)),
% 0.20/0.44    inference(superposition,[],[f43,f29])).
% 0.20/0.44  fof(f43,plain,(
% 0.20/0.44    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) ) | ~spl5_5),
% 0.20/0.44    inference(avatar_component_clause,[],[f42])).
% 0.20/0.44  fof(f52,plain,(
% 0.20/0.44    spl5_7),
% 0.20/0.44    inference(avatar_split_clause,[],[f20,f50])).
% 0.20/0.44  % (23320)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.20/0.44  fof(f20,plain,(
% 0.20/0.44    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f11])).
% 0.20/0.44  % (23318)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
% 0.20/0.44  fof(f11,plain,(
% 0.20/0.44    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 0.20/0.44    inference(flattening,[],[f10])).
% 0.20/0.44  fof(f10,plain,(
% 0.20/0.44    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 0.20/0.44    inference(nnf_transformation,[],[f1])).
% 0.20/0.44  fof(f1,axiom,(
% 0.20/0.44    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.20/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 0.20/0.44  fof(f48,plain,(
% 0.20/0.44    spl5_6),
% 0.20/0.44    inference(avatar_split_clause,[],[f16,f46])).
% 0.20/0.44  fof(f16,plain,(
% 0.20/0.44    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 0.20/0.44    inference(cnf_transformation,[],[f2])).
% 0.20/0.44  fof(f2,axiom,(
% 0.20/0.44    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 0.20/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).
% 0.20/0.44  fof(f44,plain,(
% 0.20/0.44    spl5_5),
% 0.20/0.44    inference(avatar_split_clause,[],[f17,f42])).
% 0.20/0.44  fof(f17,plain,(
% 0.20/0.44    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 0.20/0.44    inference(cnf_transformation,[],[f2])).
% 0.20/0.44  fof(f40,plain,(
% 0.20/0.44    spl5_4),
% 0.20/0.44    inference(avatar_split_clause,[],[f12,f37])).
% 0.20/0.44  fof(f12,plain,(
% 0.20/0.44    r2_hidden(k1_mcart_1(sK0),sK1)),
% 0.20/0.44    inference(cnf_transformation,[],[f9])).
% 0.20/0.44  fof(f9,plain,(
% 0.20/0.44    ~r2_hidden(sK0,k2_zfmisc_1(sK1,sK2)) & sK0 = k4_tarski(sK3,sK4) & r2_hidden(k2_mcart_1(sK0),sK2) & r2_hidden(k1_mcart_1(sK0),sK1)),
% 0.20/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f6,f8,f7])).
% 0.20/0.44  fof(f7,plain,(
% 0.20/0.44    ? [X0,X1,X2] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) & ? [X3,X4] : k4_tarski(X3,X4) = X0 & r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) => (~r2_hidden(sK0,k2_zfmisc_1(sK1,sK2)) & ? [X4,X3] : k4_tarski(X3,X4) = sK0 & r2_hidden(k2_mcart_1(sK0),sK2) & r2_hidden(k1_mcart_1(sK0),sK1))),
% 0.20/0.44    introduced(choice_axiom,[])).
% 0.20/0.44  fof(f8,plain,(
% 0.20/0.44    ? [X4,X3] : k4_tarski(X3,X4) = sK0 => sK0 = k4_tarski(sK3,sK4)),
% 0.20/0.44    introduced(choice_axiom,[])).
% 0.20/0.44  fof(f6,plain,(
% 0.20/0.44    ? [X0,X1,X2] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) & ? [X3,X4] : k4_tarski(X3,X4) = X0 & r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1))),
% 0.20/0.44    inference(flattening,[],[f5])).
% 0.20/0.44  fof(f5,plain,(
% 0.20/0.44    ? [X0,X1,X2] : ((~r2_hidden(X0,k2_zfmisc_1(X1,X2)) & ? [X3,X4] : k4_tarski(X3,X4) = X0) & (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 0.20/0.44    inference(ennf_transformation,[],[f4])).
% 0.20/0.44  fof(f4,negated_conjecture,(
% 0.20/0.44    ~! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) => (r2_hidden(X0,k2_zfmisc_1(X1,X2)) | ! [X3,X4] : k4_tarski(X3,X4) != X0))),
% 0.20/0.44    inference(negated_conjecture,[],[f3])).
% 0.20/0.44  fof(f3,conjecture,(
% 0.20/0.44    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) => (r2_hidden(X0,k2_zfmisc_1(X1,X2)) | ! [X3,X4] : k4_tarski(X3,X4) != X0))),
% 0.20/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_mcart_1)).
% 0.20/0.44  fof(f35,plain,(
% 0.20/0.44    spl5_3),
% 0.20/0.44    inference(avatar_split_clause,[],[f13,f32])).
% 0.20/0.44  fof(f13,plain,(
% 0.20/0.44    r2_hidden(k2_mcart_1(sK0),sK2)),
% 0.20/0.44    inference(cnf_transformation,[],[f9])).
% 0.20/0.44  fof(f30,plain,(
% 0.20/0.44    spl5_2),
% 0.20/0.44    inference(avatar_split_clause,[],[f14,f27])).
% 0.20/0.44  fof(f14,plain,(
% 0.20/0.44    sK0 = k4_tarski(sK3,sK4)),
% 0.20/0.44    inference(cnf_transformation,[],[f9])).
% 0.20/0.44  % (23329)lrs+10_5:1_add=large:afp=1000:afq=1.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=fast:fsr=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=2:nwc=1:stl=210:uhcvi=on_1759 on theBenchmark
% 0.20/0.44  fof(f25,plain,(
% 0.20/0.44    ~spl5_1),
% 0.20/0.44    inference(avatar_split_clause,[],[f15,f22])).
% 0.20/0.44  fof(f15,plain,(
% 0.20/0.44    ~r2_hidden(sK0,k2_zfmisc_1(sK1,sK2))),
% 0.20/0.44    inference(cnf_transformation,[],[f9])).
% 0.20/0.44  % SZS output end Proof for theBenchmark
% 0.20/0.44  % (23321)------------------------------
% 0.20/0.44  % (23321)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.44  % (23321)Termination reason: Refutation
% 0.20/0.44  
% 0.20/0.44  % (23321)Memory used [KB]: 10618
% 0.20/0.44  % (23321)Time elapsed: 0.035 s
% 0.20/0.44  % (23321)------------------------------
% 0.20/0.44  % (23321)------------------------------
% 0.20/0.44  % (23311)Success in time 0.091 s
%------------------------------------------------------------------------------
