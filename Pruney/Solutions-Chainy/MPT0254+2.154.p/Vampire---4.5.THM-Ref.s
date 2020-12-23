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
% DateTime   : Thu Dec  3 12:39:33 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.20s
% Verified   : 
% Statistics : Number of formulae       :   58 (  87 expanded)
%              Number of leaves         :   17 (  39 expanded)
%              Depth                    :    7
%              Number of atoms          :  141 ( 199 expanded)
%              Number of equality atoms :   33 (  54 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f182,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f36,f45,f51,f126,f149,f177,f180,f181])).

fof(f181,plain,
    ( k1_xboole_0 != k1_tarski(sK0)
    | k1_xboole_0 != sK1
    | k1_xboole_0 != k2_xboole_0(k1_tarski(sK0),sK1)
    | r2_hidden(sK0,k2_xboole_0(sK1,sK1))
    | ~ r2_hidden(sK0,sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f180,plain,
    ( spl2_6
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f179,f119,f47,f41,f168])).

fof(f168,plain,
    ( spl2_6
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f41,plain,
    ( spl2_2
  <=> k1_xboole_0 = k1_tarski(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f47,plain,
    ( spl2_3
  <=> k1_xboole_0 = k2_xboole_0(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f119,plain,
    ( spl2_4
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f179,plain,
    ( k1_xboole_0 = sK1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(forward_demodulation,[],[f178,f49])).

fof(f49,plain,
    ( k1_xboole_0 = k2_xboole_0(k1_xboole_0,sK1)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f47])).

fof(f178,plain,
    ( sK1 = k2_xboole_0(k1_xboole_0,sK1)
    | ~ spl2_2
    | ~ spl2_4 ),
    inference(forward_demodulation,[],[f164,f43])).

fof(f43,plain,
    ( k1_xboole_0 = k1_tarski(sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f41])).

fof(f164,plain,
    ( sK1 = k2_xboole_0(k1_tarski(sK0),sK1)
    | ~ spl2_4 ),
    inference(resolution,[],[f121,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l22_zfmisc_1)).

fof(f121,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f119])).

fof(f177,plain,
    ( ~ spl2_7
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f160,f119,f47,f173])).

fof(f173,plain,
    ( spl2_7
  <=> r2_hidden(sK0,k2_xboole_0(sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f160,plain,
    ( ~ r2_hidden(sK0,k2_xboole_0(sK1,sK1))
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(unit_resulting_resolution,[],[f73,f121,f121,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,k2_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r2_hidden(X2,X0)
        & r2_hidden(X2,X1) )
      | ( ~ r2_hidden(X2,X1)
        & r2_hidden(X2,X0) )
      | ~ r2_hidden(X2,k2_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ( ~ r2_hidden(X2,X0)
            & r2_hidden(X2,X1) )
        & ~ ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) )
        & r2_hidden(X2,k2_xboole_0(X0,X1))
        & r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_xboole_0)).

fof(f73,plain,
    ( ! [X0] : r1_xboole_0(X0,sK1)
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f30,f57])).

fof(f57,plain,
    ( ! [X1] :
        ( ~ r1_xboole_0(X1,k1_xboole_0)
        | r1_xboole_0(X1,sK1) )
    | ~ spl2_3 ),
    inference(superposition,[],[f28,f49])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

fof(f30,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f149,plain,(
    spl2_5 ),
    inference(avatar_contradiction_clause,[],[f146])).

fof(f146,plain,
    ( $false
    | spl2_5 ),
    inference(unit_resulting_resolution,[],[f31,f125])).

fof(f125,plain,
    ( ~ r1_tarski(k1_xboole_0,sK1)
    | spl2_5 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl2_5
  <=> r1_tarski(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f31,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f126,plain,
    ( spl2_4
    | ~ spl2_5
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f117,f47,f41,f123,f119])).

fof(f117,plain,
    ( ~ r1_tarski(k1_xboole_0,sK1)
    | r2_hidden(sK0,sK1)
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(superposition,[],[f52,f49])).

fof(f52,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_xboole_0(k1_xboole_0,X0),X0)
        | r2_hidden(sK0,X0) )
    | ~ spl2_2 ),
    inference(superposition,[],[f29,f43])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1)
     => r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l20_zfmisc_1)).

fof(f51,plain,
    ( spl2_3
    | ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f50,f41,f33,f47])).

fof(f33,plain,
    ( spl2_1
  <=> k1_xboole_0 = k2_xboole_0(k1_tarski(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f50,plain,
    ( k1_xboole_0 = k2_xboole_0(k1_xboole_0,sK1)
    | ~ spl2_1
    | ~ spl2_2 ),
    inference(backward_demodulation,[],[f35,f43])).

fof(f35,plain,
    ( k1_xboole_0 = k2_xboole_0(k1_tarski(sK0),sK1)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f33])).

fof(f45,plain,
    ( spl2_2
    | ~ spl2_1 ),
    inference(avatar_split_clause,[],[f39,f33,f41])).

fof(f39,plain,
    ( k1_xboole_0 = k1_tarski(sK0)
    | ~ spl2_1 ),
    inference(trivial_inequality_removal,[],[f38])).

fof(f38,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k1_tarski(sK0)
    | ~ spl2_1 ),
    inference(superposition,[],[f20,f35])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) != k1_xboole_0
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | k2_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = k1_xboole_0
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_xboole_1)).

fof(f36,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f19,f33])).

fof(f19,plain,(
    k1_xboole_0 = k2_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    k1_xboole_0 = k2_xboole_0(k1_tarski(sK0),sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f17])).

fof(f17,plain,
    ( ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1)
   => k1_xboole_0 = k2_xboole_0(k1_tarski(sK0),sK1) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n009.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:47:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (29702)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.21/0.50  % (29707)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.21/0.50  % (29705)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.21/0.50  % (29717)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.21/0.50  % (29702)Refutation not found, incomplete strategy% (29702)------------------------------
% 0.21/0.50  % (29702)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (29704)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.21/0.51  % (29703)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.21/0.51  % (29701)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.21/0.51  % (29705)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % (29710)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.21/0.51  % (29702)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (29702)Memory used [KB]: 10490
% 0.21/0.51  % (29702)Time elapsed: 0.085 s
% 0.21/0.51  % (29702)------------------------------
% 0.21/0.51  % (29702)------------------------------
% 0.21/0.51  % (29700)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 1.20/0.51  % (29721)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 1.20/0.51  % (29708)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 1.20/0.51  % (29720)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 1.20/0.52  % (29713)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 1.20/0.52  % SZS output start Proof for theBenchmark
% 1.20/0.52  fof(f182,plain,(
% 1.20/0.52    $false),
% 1.20/0.52    inference(avatar_sat_refutation,[],[f36,f45,f51,f126,f149,f177,f180,f181])).
% 1.20/0.52  fof(f181,plain,(
% 1.20/0.52    k1_xboole_0 != k1_tarski(sK0) | k1_xboole_0 != sK1 | k1_xboole_0 != k2_xboole_0(k1_tarski(sK0),sK1) | r2_hidden(sK0,k2_xboole_0(sK1,sK1)) | ~r2_hidden(sK0,sK1)),
% 1.20/0.52    introduced(theory_tautology_sat_conflict,[])).
% 1.20/0.52  fof(f180,plain,(
% 1.20/0.52    spl2_6 | ~spl2_2 | ~spl2_3 | ~spl2_4),
% 1.20/0.52    inference(avatar_split_clause,[],[f179,f119,f47,f41,f168])).
% 1.20/0.52  fof(f168,plain,(
% 1.20/0.52    spl2_6 <=> k1_xboole_0 = sK1),
% 1.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 1.20/0.52  fof(f41,plain,(
% 1.20/0.52    spl2_2 <=> k1_xboole_0 = k1_tarski(sK0)),
% 1.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 1.20/0.52  fof(f47,plain,(
% 1.20/0.52    spl2_3 <=> k1_xboole_0 = k2_xboole_0(k1_xboole_0,sK1)),
% 1.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 1.20/0.52  fof(f119,plain,(
% 1.20/0.52    spl2_4 <=> r2_hidden(sK0,sK1)),
% 1.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 1.20/0.52  fof(f179,plain,(
% 1.20/0.52    k1_xboole_0 = sK1 | (~spl2_2 | ~spl2_3 | ~spl2_4)),
% 1.20/0.52    inference(forward_demodulation,[],[f178,f49])).
% 1.20/0.52  fof(f49,plain,(
% 1.20/0.52    k1_xboole_0 = k2_xboole_0(k1_xboole_0,sK1) | ~spl2_3),
% 1.20/0.52    inference(avatar_component_clause,[],[f47])).
% 1.20/0.52  fof(f178,plain,(
% 1.20/0.52    sK1 = k2_xboole_0(k1_xboole_0,sK1) | (~spl2_2 | ~spl2_4)),
% 1.20/0.52    inference(forward_demodulation,[],[f164,f43])).
% 1.20/0.52  fof(f43,plain,(
% 1.20/0.52    k1_xboole_0 = k1_tarski(sK0) | ~spl2_2),
% 1.20/0.52    inference(avatar_component_clause,[],[f41])).
% 1.20/0.52  fof(f164,plain,(
% 1.20/0.52    sK1 = k2_xboole_0(k1_tarski(sK0),sK1) | ~spl2_4),
% 1.20/0.52    inference(resolution,[],[f121,f21])).
% 1.20/0.52  fof(f21,plain,(
% 1.20/0.52    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k2_xboole_0(k1_tarski(X0),X1) = X1) )),
% 1.20/0.52    inference(cnf_transformation,[],[f13])).
% 1.20/0.52  fof(f13,plain,(
% 1.20/0.52    ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) = X1 | ~r2_hidden(X0,X1))),
% 1.20/0.52    inference(ennf_transformation,[],[f8])).
% 1.20/0.52  fof(f8,axiom,(
% 1.20/0.52    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 1.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l22_zfmisc_1)).
% 1.20/0.52  fof(f121,plain,(
% 1.20/0.52    r2_hidden(sK0,sK1) | ~spl2_4),
% 1.20/0.52    inference(avatar_component_clause,[],[f119])).
% 1.20/0.52  fof(f177,plain,(
% 1.20/0.52    ~spl2_7 | ~spl2_3 | ~spl2_4),
% 1.20/0.52    inference(avatar_split_clause,[],[f160,f119,f47,f173])).
% 1.20/0.52  fof(f173,plain,(
% 1.20/0.52    spl2_7 <=> r2_hidden(sK0,k2_xboole_0(sK1,sK1))),
% 1.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 1.20/0.52  fof(f160,plain,(
% 1.20/0.52    ~r2_hidden(sK0,k2_xboole_0(sK1,sK1)) | (~spl2_3 | ~spl2_4)),
% 1.20/0.52    inference(unit_resulting_resolution,[],[f73,f121,f121,f25])).
% 1.20/0.52  fof(f25,plain,(
% 1.20/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,k2_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 1.20/0.52    inference(cnf_transformation,[],[f14])).
% 1.20/0.52  fof(f14,plain,(
% 1.20/0.52    ! [X0,X1,X2] : ((~r2_hidden(X2,X0) & r2_hidden(X2,X1)) | (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) | ~r2_hidden(X2,k2_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1))),
% 1.20/0.52    inference(ennf_transformation,[],[f2])).
% 1.20/0.52  fof(f2,axiom,(
% 1.20/0.52    ! [X0,X1,X2] : ~(~(~r2_hidden(X2,X0) & r2_hidden(X2,X1)) & ~(~r2_hidden(X2,X1) & r2_hidden(X2,X0)) & r2_hidden(X2,k2_xboole_0(X0,X1)) & r1_xboole_0(X0,X1))),
% 1.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_xboole_0)).
% 1.20/0.52  fof(f73,plain,(
% 1.20/0.52    ( ! [X0] : (r1_xboole_0(X0,sK1)) ) | ~spl2_3),
% 1.20/0.52    inference(unit_resulting_resolution,[],[f30,f57])).
% 1.20/0.52  fof(f57,plain,(
% 1.20/0.52    ( ! [X1] : (~r1_xboole_0(X1,k1_xboole_0) | r1_xboole_0(X1,sK1)) ) | ~spl2_3),
% 1.20/0.52    inference(superposition,[],[f28,f49])).
% 1.20/0.52  fof(f28,plain,(
% 1.20/0.52    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | r1_xboole_0(X0,X2)) )),
% 1.20/0.52    inference(cnf_transformation,[],[f15])).
% 1.20/0.52  fof(f15,plain,(
% 1.20/0.52    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 1.20/0.52    inference(ennf_transformation,[],[f6])).
% 1.20/0.52  fof(f6,axiom,(
% 1.20/0.52    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 1.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).
% 1.20/0.52  fof(f30,plain,(
% 1.20/0.52    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.20/0.52    inference(cnf_transformation,[],[f5])).
% 1.20/0.52  fof(f5,axiom,(
% 1.20/0.52    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 1.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 1.20/0.52  fof(f149,plain,(
% 1.20/0.52    spl2_5),
% 1.20/0.52    inference(avatar_contradiction_clause,[],[f146])).
% 1.20/0.52  fof(f146,plain,(
% 1.20/0.52    $false | spl2_5),
% 1.20/0.52    inference(unit_resulting_resolution,[],[f31,f125])).
% 1.20/0.52  fof(f125,plain,(
% 1.20/0.52    ~r1_tarski(k1_xboole_0,sK1) | spl2_5),
% 1.20/0.52    inference(avatar_component_clause,[],[f123])).
% 1.20/0.52  fof(f123,plain,(
% 1.20/0.52    spl2_5 <=> r1_tarski(k1_xboole_0,sK1)),
% 1.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 1.20/0.52  fof(f31,plain,(
% 1.20/0.52    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.20/0.52    inference(cnf_transformation,[],[f4])).
% 1.20/0.52  fof(f4,axiom,(
% 1.20/0.52    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.20/0.52  fof(f126,plain,(
% 1.20/0.52    spl2_4 | ~spl2_5 | ~spl2_2 | ~spl2_3),
% 1.20/0.52    inference(avatar_split_clause,[],[f117,f47,f41,f123,f119])).
% 1.20/0.52  fof(f117,plain,(
% 1.20/0.52    ~r1_tarski(k1_xboole_0,sK1) | r2_hidden(sK0,sK1) | (~spl2_2 | ~spl2_3)),
% 1.20/0.52    inference(superposition,[],[f52,f49])).
% 1.20/0.52  fof(f52,plain,(
% 1.20/0.52    ( ! [X0] : (~r1_tarski(k2_xboole_0(k1_xboole_0,X0),X0) | r2_hidden(sK0,X0)) ) | ~spl2_2),
% 1.20/0.52    inference(superposition,[],[f29,f43])).
% 1.20/0.52  fof(f29,plain,(
% 1.20/0.52    ( ! [X0,X1] : (~r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) | r2_hidden(X0,X1)) )),
% 1.20/0.52    inference(cnf_transformation,[],[f16])).
% 1.20/0.52  fof(f16,plain,(
% 1.20/0.52    ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1))),
% 1.20/0.52    inference(ennf_transformation,[],[f7])).
% 1.20/0.52  fof(f7,axiom,(
% 1.20/0.52    ! [X0,X1] : (r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) => r2_hidden(X0,X1))),
% 1.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l20_zfmisc_1)).
% 1.20/0.52  fof(f51,plain,(
% 1.20/0.52    spl2_3 | ~spl2_1 | ~spl2_2),
% 1.20/0.52    inference(avatar_split_clause,[],[f50,f41,f33,f47])).
% 1.20/0.52  fof(f33,plain,(
% 1.20/0.52    spl2_1 <=> k1_xboole_0 = k2_xboole_0(k1_tarski(sK0),sK1)),
% 1.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 1.20/0.52  fof(f50,plain,(
% 1.20/0.52    k1_xboole_0 = k2_xboole_0(k1_xboole_0,sK1) | (~spl2_1 | ~spl2_2)),
% 1.20/0.52    inference(backward_demodulation,[],[f35,f43])).
% 1.20/0.52  fof(f35,plain,(
% 1.20/0.52    k1_xboole_0 = k2_xboole_0(k1_tarski(sK0),sK1) | ~spl2_1),
% 1.20/0.52    inference(avatar_component_clause,[],[f33])).
% 1.20/0.52  fof(f45,plain,(
% 1.20/0.52    spl2_2 | ~spl2_1),
% 1.20/0.52    inference(avatar_split_clause,[],[f39,f33,f41])).
% 1.20/0.52  fof(f39,plain,(
% 1.20/0.52    k1_xboole_0 = k1_tarski(sK0) | ~spl2_1),
% 1.20/0.52    inference(trivial_inequality_removal,[],[f38])).
% 1.20/0.52  fof(f38,plain,(
% 1.20/0.52    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k1_tarski(sK0) | ~spl2_1),
% 1.20/0.52    inference(superposition,[],[f20,f35])).
% 1.20/0.52  fof(f20,plain,(
% 1.20/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) != k1_xboole_0 | k1_xboole_0 = X0) )),
% 1.20/0.52    inference(cnf_transformation,[],[f12])).
% 1.20/0.52  fof(f12,plain,(
% 1.20/0.52    ! [X0,X1] : (k1_xboole_0 = X0 | k2_xboole_0(X0,X1) != k1_xboole_0)),
% 1.20/0.52    inference(ennf_transformation,[],[f3])).
% 1.20/0.52  fof(f3,axiom,(
% 1.20/0.52    ! [X0,X1] : (k2_xboole_0(X0,X1) = k1_xboole_0 => k1_xboole_0 = X0)),
% 1.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_xboole_1)).
% 1.20/0.52  fof(f36,plain,(
% 1.20/0.52    spl2_1),
% 1.20/0.52    inference(avatar_split_clause,[],[f19,f33])).
% 1.20/0.52  fof(f19,plain,(
% 1.20/0.52    k1_xboole_0 = k2_xboole_0(k1_tarski(sK0),sK1)),
% 1.20/0.52    inference(cnf_transformation,[],[f18])).
% 1.20/0.52  fof(f18,plain,(
% 1.20/0.52    k1_xboole_0 = k2_xboole_0(k1_tarski(sK0),sK1)),
% 1.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f17])).
% 1.20/0.52  fof(f17,plain,(
% 1.20/0.52    ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1) => k1_xboole_0 = k2_xboole_0(k1_tarski(sK0),sK1)),
% 1.20/0.52    introduced(choice_axiom,[])).
% 1.20/0.52  fof(f11,plain,(
% 1.20/0.52    ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1)),
% 1.20/0.52    inference(ennf_transformation,[],[f10])).
% 1.20/0.52  fof(f10,negated_conjecture,(
% 1.20/0.52    ~! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 1.20/0.52    inference(negated_conjecture,[],[f9])).
% 1.20/0.52  fof(f9,conjecture,(
% 1.20/0.52    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 1.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 1.20/0.52  % SZS output end Proof for theBenchmark
% 1.20/0.52  % (29705)------------------------------
% 1.20/0.52  % (29705)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.20/0.52  % (29705)Termination reason: Refutation
% 1.20/0.52  
% 1.20/0.52  % (29705)Memory used [KB]: 10746
% 1.20/0.52  % (29705)Time elapsed: 0.087 s
% 1.20/0.52  % (29705)------------------------------
% 1.20/0.52  % (29705)------------------------------
% 1.20/0.52  % (29698)Success in time 0.157 s
%------------------------------------------------------------------------------
