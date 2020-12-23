%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:04 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 213 expanded)
%              Number of leaves         :   13 (  63 expanded)
%              Depth                    :   11
%              Number of atoms          :  213 ( 718 expanded)
%              Number of equality atoms :   27 (  97 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f185,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f103,f113,f117,f129,f134,f137,f151,f157,f184])).

fof(f184,plain,
    ( ~ spl3_1
    | ~ spl3_4 ),
    inference(avatar_contradiction_clause,[],[f180])).

fof(f180,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f19,f179])).

fof(f179,plain,
    ( sK0 = sK1
    | ~ spl3_1
    | ~ spl3_4 ),
    inference(resolution,[],[f148,f160])).

fof(f160,plain,
    ( ! [X0] : r1_tarski(sK1,X0)
    | ~ spl3_4 ),
    inference(resolution,[],[f56,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f13,f14])).

fof(f14,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f56,plain,
    ( ! [X4] : ~ r2_hidden(X4,sK1)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f55])).

fof(f55,plain,
    ( spl3_4
  <=> ! [X4] : ~ r2_hidden(X4,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f148,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK0)
        | sK0 = X0 )
    | ~ spl3_1 ),
    inference(resolution,[],[f141,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f141,plain,
    ( ! [X0] : r1_tarski(sK0,X0)
    | ~ spl3_1 ),
    inference(resolution,[],[f38,f24])).

fof(f38,plain,
    ( ! [X1] : ~ r2_hidden(X1,sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f37])).

fof(f37,plain,
    ( spl3_1
  <=> ! [X1] : ~ r2_hidden(X1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f19,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,
    ( sK0 != sK1
    & k2_zfmisc_1(sK0,sK0) = k2_zfmisc_1(sK1,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f6,f8])).

fof(f8,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k2_zfmisc_1(X0,X0) = k2_zfmisc_1(X1,X1) )
   => ( sK0 != sK1
      & k2_zfmisc_1(sK0,sK0) = k2_zfmisc_1(sK1,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k2_zfmisc_1(X0,X0) = k2_zfmisc_1(X1,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k2_zfmisc_1(X0,X0) = k2_zfmisc_1(X1,X1)
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X0) = k2_zfmisc_1(X1,X1)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t115_zfmisc_1)).

fof(f157,plain,
    ( spl3_4
    | spl3_3 ),
    inference(avatar_split_clause,[],[f155,f52,f55])).

fof(f52,plain,
    ( spl3_3
  <=> ! [X5] :
        ( ~ r2_hidden(X5,sK1)
        | r2_hidden(X5,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f155,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(X6,sK1)
      | ~ r2_hidden(X7,sK1)
      | r2_hidden(X6,sK0) ) ),
    inference(resolution,[],[f33,f27])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_zfmisc_1)).

fof(f33,plain,(
    ! [X4,X5] :
      ( r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(sK0,sK0))
      | ~ r2_hidden(X5,sK1)
      | ~ r2_hidden(X4,sK1) ) ),
    inference(superposition,[],[f28,f18])).

fof(f18,plain,(
    k2_zfmisc_1(sK0,sK0) = k2_zfmisc_1(sK1,sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f151,plain,
    ( ~ spl3_1
    | spl3_13 ),
    inference(avatar_contradiction_clause,[],[f150])).

fof(f150,plain,
    ( $false
    | ~ spl3_1
    | spl3_13 ),
    inference(resolution,[],[f116,f141])).

fof(f116,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl3_13 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl3_13
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f137,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f108,f40,f37])).

fof(f40,plain,
    ( spl3_2
  <=> ! [X0] :
        ( r2_hidden(X0,sK1)
        | ~ r2_hidden(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f108,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,sK1)
      | ~ r2_hidden(X1,sK0)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f64,f30])).

fof(f30,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(sK0,sK0))
      | r2_hidden(X0,sK1)
      | ~ r2_hidden(X3,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f35,f28])).

fof(f35,plain,(
    ! [X4,X2,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),X4)
      | r2_hidden(X2,sK1)
      | ~ r1_tarski(X4,k2_zfmisc_1(sK0,sK0)) ) ),
    inference(resolution,[],[f31,f23])).

fof(f23,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK0,sK0))
      | r2_hidden(X0,sK1) ) ),
    inference(superposition,[],[f26,f18])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f134,plain,(
    ~ spl3_12 ),
    inference(avatar_contradiction_clause,[],[f130])).

fof(f130,plain,
    ( $false
    | ~ spl3_12 ),
    inference(subsumption_resolution,[],[f19,f102])).

fof(f102,plain,
    ( sK0 = sK1
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl3_12
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f129,plain,
    ( spl3_1
    | spl3_1
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f127,f55,f37,f37])).

fof(f127,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,sK0)
        | ~ r2_hidden(X1,sK0) )
    | ~ spl3_4 ),
    inference(resolution,[],[f122,f28])).

fof(f122,plain,
    ( ! [X2,X3] : ~ r2_hidden(k4_tarski(X2,X3),k2_zfmisc_1(sK0,sK0))
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f32,f56])).

fof(f32,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),k2_zfmisc_1(sK0,sK0))
      | r2_hidden(X3,sK1) ) ),
    inference(superposition,[],[f27,f18])).

fof(f117,plain,
    ( ~ spl3_13
    | spl3_12
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f112,f52,f101,f115])).

fof(f112,plain,
    ( sK0 = sK1
    | ~ r1_tarski(sK0,sK1)
    | ~ spl3_3 ),
    inference(resolution,[],[f107,f22])).

fof(f107,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl3_3 ),
    inference(duplicate_literal_removal,[],[f104])).

fof(f104,plain,
    ( r1_tarski(sK1,sK0)
    | r1_tarski(sK1,sK0)
    | ~ spl3_3 ),
    inference(resolution,[],[f59,f24])).

fof(f59,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK2(X0,sK0),sK1)
        | r1_tarski(X0,sK0) )
    | ~ spl3_3 ),
    inference(resolution,[],[f53,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f53,plain,
    ( ! [X5] :
        ( r2_hidden(X5,sK0)
        | ~ r2_hidden(X5,sK1) )
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f52])).

fof(f113,plain,
    ( ~ spl3_3
    | spl3_11 ),
    inference(avatar_contradiction_clause,[],[f111])).

fof(f111,plain,
    ( $false
    | ~ spl3_3
    | spl3_11 ),
    inference(subsumption_resolution,[],[f99,f107])).

fof(f99,plain,
    ( ~ r1_tarski(sK1,sK0)
    | spl3_11 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl3_11
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f103,plain,
    ( ~ spl3_11
    | spl3_12
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f96,f40,f101,f98])).

fof(f96,plain,
    ( sK0 = sK1
    | ~ r1_tarski(sK1,sK0)
    | ~ spl3_2 ),
    inference(resolution,[],[f63,f22])).

fof(f63,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_2 ),
    inference(duplicate_literal_removal,[],[f60])).

fof(f60,plain,
    ( r1_tarski(sK0,sK1)
    | r1_tarski(sK0,sK1)
    | ~ spl3_2 ),
    inference(resolution,[],[f46,f24])).

fof(f46,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK2(X0,sK1),sK0)
        | r1_tarski(X0,sK1) )
    | ~ spl3_2 ),
    inference(resolution,[],[f41,f25])).

fof(f41,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK1)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:29:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.49  % (28486)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.49  % (28486)Refutation not found, incomplete strategy% (28486)------------------------------
% 0.21/0.49  % (28486)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (28486)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (28486)Memory used [KB]: 10618
% 0.21/0.50  % (28486)Time elapsed: 0.091 s
% 0.21/0.50  % (28486)------------------------------
% 0.21/0.50  % (28486)------------------------------
% 0.21/0.51  % (28478)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (28478)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f185,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f103,f113,f117,f129,f134,f137,f151,f157,f184])).
% 0.21/0.52  fof(f184,plain,(
% 0.21/0.52    ~spl3_1 | ~spl3_4),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f180])).
% 0.21/0.52  fof(f180,plain,(
% 0.21/0.52    $false | (~spl3_1 | ~spl3_4)),
% 0.21/0.52    inference(subsumption_resolution,[],[f19,f179])).
% 0.21/0.52  fof(f179,plain,(
% 0.21/0.52    sK0 = sK1 | (~spl3_1 | ~spl3_4)),
% 0.21/0.52    inference(resolution,[],[f148,f160])).
% 0.21/0.52  fof(f160,plain,(
% 0.21/0.52    ( ! [X0] : (r1_tarski(sK1,X0)) ) | ~spl3_4),
% 0.21/0.52    inference(resolution,[],[f56,f24])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f15])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f13,f14])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f13,plain,(
% 0.21/0.52    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.52    inference(rectify,[],[f12])).
% 0.21/0.52  fof(f12,plain,(
% 0.21/0.52    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.52    inference(nnf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,plain,(
% 0.21/0.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.52  fof(f56,plain,(
% 0.21/0.52    ( ! [X4] : (~r2_hidden(X4,sK1)) ) | ~spl3_4),
% 0.21/0.52    inference(avatar_component_clause,[],[f55])).
% 0.21/0.52  fof(f55,plain,(
% 0.21/0.52    spl3_4 <=> ! [X4] : ~r2_hidden(X4,sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.52  fof(f148,plain,(
% 0.21/0.52    ( ! [X0] : (~r1_tarski(X0,sK0) | sK0 = X0) ) | ~spl3_1),
% 0.21/0.52    inference(resolution,[],[f141,f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f11])).
% 0.21/0.52  fof(f11,plain,(
% 0.21/0.52    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.52    inference(flattening,[],[f10])).
% 0.21/0.52  fof(f10,plain,(
% 0.21/0.52    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.52    inference(nnf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.52  fof(f141,plain,(
% 0.21/0.52    ( ! [X0] : (r1_tarski(sK0,X0)) ) | ~spl3_1),
% 0.21/0.52    inference(resolution,[],[f38,f24])).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    ( ! [X1] : (~r2_hidden(X1,sK0)) ) | ~spl3_1),
% 0.21/0.52    inference(avatar_component_clause,[],[f37])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    spl3_1 <=> ! [X1] : ~r2_hidden(X1,sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    sK0 != sK1),
% 0.21/0.52    inference(cnf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,plain,(
% 0.21/0.52    sK0 != sK1 & k2_zfmisc_1(sK0,sK0) = k2_zfmisc_1(sK1,sK1)),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f6,f8])).
% 0.21/0.52  fof(f8,plain,(
% 0.21/0.52    ? [X0,X1] : (X0 != X1 & k2_zfmisc_1(X0,X0) = k2_zfmisc_1(X1,X1)) => (sK0 != sK1 & k2_zfmisc_1(sK0,sK0) = k2_zfmisc_1(sK1,sK1))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f6,plain,(
% 0.21/0.52    ? [X0,X1] : (X0 != X1 & k2_zfmisc_1(X0,X0) = k2_zfmisc_1(X1,X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,negated_conjecture,(
% 0.21/0.52    ~! [X0,X1] : (k2_zfmisc_1(X0,X0) = k2_zfmisc_1(X1,X1) => X0 = X1)),
% 0.21/0.52    inference(negated_conjecture,[],[f4])).
% 0.21/0.52  fof(f4,conjecture,(
% 0.21/0.52    ! [X0,X1] : (k2_zfmisc_1(X0,X0) = k2_zfmisc_1(X1,X1) => X0 = X1)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t115_zfmisc_1)).
% 0.21/0.52  fof(f157,plain,(
% 0.21/0.52    spl3_4 | spl3_3),
% 0.21/0.52    inference(avatar_split_clause,[],[f155,f52,f55])).
% 0.21/0.52  fof(f52,plain,(
% 0.21/0.52    spl3_3 <=> ! [X5] : (~r2_hidden(X5,sK1) | r2_hidden(X5,sK0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.52  fof(f155,plain,(
% 0.21/0.52    ( ! [X6,X7] : (~r2_hidden(X6,sK1) | ~r2_hidden(X7,sK1) | r2_hidden(X6,sK0)) )),
% 0.21/0.52    inference(resolution,[],[f33,f27])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X1,X3)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f17])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 0.21/0.52    inference(flattening,[],[f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 0.21/0.52    inference(nnf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_zfmisc_1)).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    ( ! [X4,X5] : (r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(sK0,sK0)) | ~r2_hidden(X5,sK1) | ~r2_hidden(X4,sK1)) )),
% 0.21/0.52    inference(superposition,[],[f28,f18])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    k2_zfmisc_1(sK0,sK0) = k2_zfmisc_1(sK1,sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f9])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f17])).
% 0.21/0.52  fof(f151,plain,(
% 0.21/0.52    ~spl3_1 | spl3_13),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f150])).
% 0.21/0.52  fof(f150,plain,(
% 0.21/0.52    $false | (~spl3_1 | spl3_13)),
% 0.21/0.52    inference(resolution,[],[f116,f141])).
% 0.21/0.52  fof(f116,plain,(
% 0.21/0.52    ~r1_tarski(sK0,sK1) | spl3_13),
% 0.21/0.52    inference(avatar_component_clause,[],[f115])).
% 0.21/0.52  fof(f115,plain,(
% 0.21/0.52    spl3_13 <=> r1_tarski(sK0,sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.21/0.52  fof(f137,plain,(
% 0.21/0.52    spl3_1 | spl3_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f108,f40,f37])).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    spl3_2 <=> ! [X0] : (r2_hidden(X0,sK1) | ~r2_hidden(X0,sK0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.52  fof(f108,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r2_hidden(X0,sK1) | ~r2_hidden(X1,sK0) | ~r2_hidden(X0,sK0)) )),
% 0.21/0.52    inference(resolution,[],[f64,f30])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.52    inference(equality_resolution,[],[f20])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f11])).
% 0.21/0.52  fof(f64,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (~r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(sK0,sK0)) | r2_hidden(X0,sK1) | ~r2_hidden(X3,X2) | ~r2_hidden(X0,X1)) )),
% 0.21/0.52    inference(resolution,[],[f35,f28])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    ( ! [X4,X2,X3] : (~r2_hidden(k4_tarski(X2,X3),X4) | r2_hidden(X2,sK1) | ~r1_tarski(X4,k2_zfmisc_1(sK0,sK0))) )),
% 0.21/0.52    inference(resolution,[],[f31,f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f15])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK0,sK0)) | r2_hidden(X0,sK1)) )),
% 0.21/0.52    inference(superposition,[],[f26,f18])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X0,X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f17])).
% 0.21/0.52  fof(f134,plain,(
% 0.21/0.52    ~spl3_12),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f130])).
% 0.21/0.52  fof(f130,plain,(
% 0.21/0.52    $false | ~spl3_12),
% 0.21/0.52    inference(subsumption_resolution,[],[f19,f102])).
% 0.21/0.52  fof(f102,plain,(
% 0.21/0.52    sK0 = sK1 | ~spl3_12),
% 0.21/0.52    inference(avatar_component_clause,[],[f101])).
% 0.21/0.52  fof(f101,plain,(
% 0.21/0.52    spl3_12 <=> sK0 = sK1),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.52  fof(f129,plain,(
% 0.21/0.52    spl3_1 | spl3_1 | ~spl3_4),
% 0.21/0.52    inference(avatar_split_clause,[],[f127,f55,f37,f37])).
% 0.21/0.52  fof(f127,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r2_hidden(X0,sK0) | ~r2_hidden(X1,sK0)) ) | ~spl3_4),
% 0.21/0.52    inference(resolution,[],[f122,f28])).
% 0.21/0.52  fof(f122,plain,(
% 0.21/0.52    ( ! [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),k2_zfmisc_1(sK0,sK0))) ) | ~spl3_4),
% 0.21/0.52    inference(subsumption_resolution,[],[f32,f56])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    ( ! [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),k2_zfmisc_1(sK0,sK0)) | r2_hidden(X3,sK1)) )),
% 0.21/0.52    inference(superposition,[],[f27,f18])).
% 0.21/0.52  fof(f117,plain,(
% 0.21/0.52    ~spl3_13 | spl3_12 | ~spl3_3),
% 0.21/0.52    inference(avatar_split_clause,[],[f112,f52,f101,f115])).
% 0.21/0.52  fof(f112,plain,(
% 0.21/0.52    sK0 = sK1 | ~r1_tarski(sK0,sK1) | ~spl3_3),
% 0.21/0.52    inference(resolution,[],[f107,f22])).
% 0.21/0.52  fof(f107,plain,(
% 0.21/0.52    r1_tarski(sK1,sK0) | ~spl3_3),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f104])).
% 0.21/0.52  fof(f104,plain,(
% 0.21/0.52    r1_tarski(sK1,sK0) | r1_tarski(sK1,sK0) | ~spl3_3),
% 0.21/0.52    inference(resolution,[],[f59,f24])).
% 0.21/0.52  fof(f59,plain,(
% 0.21/0.52    ( ! [X0] : (~r2_hidden(sK2(X0,sK0),sK1) | r1_tarski(X0,sK0)) ) | ~spl3_3),
% 0.21/0.52    inference(resolution,[],[f53,f25])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r2_hidden(sK2(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f15])).
% 0.21/0.52  fof(f53,plain,(
% 0.21/0.52    ( ! [X5] : (r2_hidden(X5,sK0) | ~r2_hidden(X5,sK1)) ) | ~spl3_3),
% 0.21/0.52    inference(avatar_component_clause,[],[f52])).
% 0.21/0.52  fof(f113,plain,(
% 0.21/0.52    ~spl3_3 | spl3_11),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f111])).
% 0.21/0.52  fof(f111,plain,(
% 0.21/0.52    $false | (~spl3_3 | spl3_11)),
% 0.21/0.52    inference(subsumption_resolution,[],[f99,f107])).
% 0.21/0.52  fof(f99,plain,(
% 0.21/0.52    ~r1_tarski(sK1,sK0) | spl3_11),
% 0.21/0.52    inference(avatar_component_clause,[],[f98])).
% 0.21/0.52  fof(f98,plain,(
% 0.21/0.52    spl3_11 <=> r1_tarski(sK1,sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.52  fof(f103,plain,(
% 0.21/0.52    ~spl3_11 | spl3_12 | ~spl3_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f96,f40,f101,f98])).
% 0.21/0.52  fof(f96,plain,(
% 0.21/0.52    sK0 = sK1 | ~r1_tarski(sK1,sK0) | ~spl3_2),
% 0.21/0.52    inference(resolution,[],[f63,f22])).
% 0.21/0.52  fof(f63,plain,(
% 0.21/0.52    r1_tarski(sK0,sK1) | ~spl3_2),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f60])).
% 0.21/0.52  fof(f60,plain,(
% 0.21/0.52    r1_tarski(sK0,sK1) | r1_tarski(sK0,sK1) | ~spl3_2),
% 0.21/0.52    inference(resolution,[],[f46,f24])).
% 0.21/0.52  fof(f46,plain,(
% 0.21/0.52    ( ! [X0] : (~r2_hidden(sK2(X0,sK1),sK0) | r1_tarski(X0,sK1)) ) | ~spl3_2),
% 0.21/0.52    inference(resolution,[],[f41,f25])).
% 0.21/0.52  fof(f41,plain,(
% 0.21/0.52    ( ! [X0] : (r2_hidden(X0,sK1) | ~r2_hidden(X0,sK0)) ) | ~spl3_2),
% 0.21/0.52    inference(avatar_component_clause,[],[f40])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (28478)------------------------------
% 0.21/0.52  % (28478)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (28478)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (28478)Memory used [KB]: 10746
% 0.21/0.52  % (28478)Time elapsed: 0.106 s
% 0.21/0.52  % (28478)------------------------------
% 0.21/0.52  % (28478)------------------------------
% 0.21/0.52  % (28475)Success in time 0.161 s
%------------------------------------------------------------------------------
