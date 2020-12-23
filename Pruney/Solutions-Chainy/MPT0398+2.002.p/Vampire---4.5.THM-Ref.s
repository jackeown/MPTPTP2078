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
% DateTime   : Thu Dec  3 12:46:06 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   31 (  38 expanded)
%              Number of leaves         :    9 (  16 expanded)
%              Depth                    :    5
%              Number of atoms          :   62 (  77 expanded)
%              Number of equality atoms :    8 (  10 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f48,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f22,f26,f30,f40,f44,f47])).

fof(f47,plain,
    ( spl3_1
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(avatar_contradiction_clause,[],[f45])).

fof(f45,plain,
    ( $false
    | spl3_1
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f21,f39,f43])).

fof(f43,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK1(X0,X1),X0)
        | r1_setfam_1(X0,X1) )
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f42])).

fof(f42,plain,
    ( spl3_6
  <=> ! [X1,X0] :
        ( r2_hidden(sK1(X0,X1),X0)
        | r1_setfam_1(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f39,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f38])).

fof(f38,plain,
    ( spl3_5
  <=> ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f21,plain,
    ( ~ r1_setfam_1(k1_xboole_0,sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f20])).

fof(f20,plain,
    ( spl3_1
  <=> r1_setfam_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f44,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f13,f42])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X0)
      | r1_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
    <=> ! [X2] :
          ( ? [X3] :
              ( r1_tarski(X2,X3)
              & r2_hidden(X3,X1) )
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
    <=> ! [X2] :
          ~ ( ! [X3] :
                ~ ( r1_tarski(X2,X3)
                  & r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_setfam_1)).

fof(f40,plain,
    ( spl3_5
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f35,f28,f24,f38])).

fof(f24,plain,
    ( spl3_2
  <=> ! [X1,X0] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f28,plain,
    ( spl3_3
  <=> ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f35,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(superposition,[],[f25,f29])).

fof(f29,plain,
    ( ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f28])).

fof(f25,plain,
    ( ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f24])).

fof(f30,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f17,f28])).

fof(f17,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k2_zfmisc_1(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f26,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f9,f24])).

fof(f9,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f22,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f8,f20])).

fof(f8,plain,(
    ~ r1_setfam_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0] : ~ r1_setfam_1(k1_xboole_0,X0) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] : r1_setfam_1(k1_xboole_0,X0) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] : r1_setfam_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_setfam_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:17:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.45  % (4055)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.45  % (4055)Refutation not found, incomplete strategy% (4055)------------------------------
% 0.20/0.45  % (4055)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.45  % (4055)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.45  
% 0.20/0.45  % (4055)Memory used [KB]: 6012
% 0.20/0.45  % (4055)Time elapsed: 0.003 s
% 0.20/0.45  % (4055)------------------------------
% 0.20/0.45  % (4055)------------------------------
% 0.20/0.46  % (4046)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.46  % (4049)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.46  % (4049)Refutation found. Thanks to Tanya!
% 0.20/0.46  % SZS status Theorem for theBenchmark
% 0.20/0.46  % SZS output start Proof for theBenchmark
% 0.20/0.46  fof(f48,plain,(
% 0.20/0.46    $false),
% 0.20/0.46    inference(avatar_sat_refutation,[],[f22,f26,f30,f40,f44,f47])).
% 0.20/0.46  fof(f47,plain,(
% 0.20/0.46    spl3_1 | ~spl3_5 | ~spl3_6),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f45])).
% 0.20/0.46  fof(f45,plain,(
% 0.20/0.46    $false | (spl3_1 | ~spl3_5 | ~spl3_6)),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f21,f39,f43])).
% 0.20/0.46  fof(f43,plain,(
% 0.20/0.46    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X0) | r1_setfam_1(X0,X1)) ) | ~spl3_6),
% 0.20/0.46    inference(avatar_component_clause,[],[f42])).
% 0.20/0.46  fof(f42,plain,(
% 0.20/0.46    spl3_6 <=> ! [X1,X0] : (r2_hidden(sK1(X0,X1),X0) | r1_setfam_1(X0,X1))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.46  fof(f39,plain,(
% 0.20/0.46    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | ~spl3_5),
% 0.20/0.46    inference(avatar_component_clause,[],[f38])).
% 0.20/0.46  fof(f38,plain,(
% 0.20/0.46    spl3_5 <=> ! [X0] : ~r2_hidden(X0,k1_xboole_0)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.46  fof(f21,plain,(
% 0.20/0.46    ~r1_setfam_1(k1_xboole_0,sK0) | spl3_1),
% 0.20/0.46    inference(avatar_component_clause,[],[f20])).
% 0.20/0.46  fof(f20,plain,(
% 0.20/0.46    spl3_1 <=> r1_setfam_1(k1_xboole_0,sK0)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.46  fof(f44,plain,(
% 0.20/0.46    spl3_6),
% 0.20/0.46    inference(avatar_split_clause,[],[f13,f42])).
% 0.20/0.46  fof(f13,plain,(
% 0.20/0.46    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X0) | r1_setfam_1(X0,X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f7])).
% 0.20/0.46  fof(f7,plain,(
% 0.20/0.46    ! [X0,X1] : (r1_setfam_1(X0,X1) <=> ! [X2] : (? [X3] : (r1_tarski(X2,X3) & r2_hidden(X3,X1)) | ~r2_hidden(X2,X0)))),
% 0.20/0.46    inference(ennf_transformation,[],[f3])).
% 0.20/0.46  fof(f3,axiom,(
% 0.20/0.46    ! [X0,X1] : (r1_setfam_1(X0,X1) <=> ! [X2] : ~(! [X3] : ~(r1_tarski(X2,X3) & r2_hidden(X3,X1)) & r2_hidden(X2,X0)))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_setfam_1)).
% 0.20/0.46  fof(f40,plain,(
% 0.20/0.46    spl3_5 | ~spl3_2 | ~spl3_3),
% 0.20/0.46    inference(avatar_split_clause,[],[f35,f28,f24,f38])).
% 0.20/0.46  fof(f24,plain,(
% 0.20/0.46    spl3_2 <=> ! [X1,X0] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.46  fof(f28,plain,(
% 0.20/0.46    spl3_3 <=> ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.46  fof(f35,plain,(
% 0.20/0.46    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | (~spl3_2 | ~spl3_3)),
% 0.20/0.46    inference(superposition,[],[f25,f29])).
% 0.20/0.46  fof(f29,plain,(
% 0.20/0.46    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) ) | ~spl3_3),
% 0.20/0.46    inference(avatar_component_clause,[],[f28])).
% 0.20/0.46  fof(f25,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) ) | ~spl3_2),
% 0.20/0.46    inference(avatar_component_clause,[],[f24])).
% 0.20/0.46  fof(f30,plain,(
% 0.20/0.46    spl3_3),
% 0.20/0.46    inference(avatar_split_clause,[],[f17,f28])).
% 0.20/0.46  fof(f17,plain,(
% 0.20/0.46    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.20/0.46    inference(equality_resolution,[],[f16])).
% 0.20/0.46  fof(f16,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k1_xboole_0 != X1 | k2_zfmisc_1(X0,X1) = k1_xboole_0) )),
% 0.20/0.46    inference(cnf_transformation,[],[f1])).
% 0.20/0.46  fof(f1,axiom,(
% 0.20/0.46    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.20/0.46  fof(f26,plain,(
% 0.20/0.46    spl3_2),
% 0.20/0.46    inference(avatar_split_clause,[],[f9,f24])).
% 0.20/0.46  fof(f9,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f2])).
% 0.20/0.46  fof(f2,axiom,(
% 0.20/0.46    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).
% 0.20/0.46  fof(f22,plain,(
% 0.20/0.46    ~spl3_1),
% 0.20/0.46    inference(avatar_split_clause,[],[f8,f20])).
% 0.20/0.46  fof(f8,plain,(
% 0.20/0.46    ~r1_setfam_1(k1_xboole_0,sK0)),
% 0.20/0.46    inference(cnf_transformation,[],[f6])).
% 0.20/0.46  fof(f6,plain,(
% 0.20/0.46    ? [X0] : ~r1_setfam_1(k1_xboole_0,X0)),
% 0.20/0.46    inference(ennf_transformation,[],[f5])).
% 0.20/0.46  fof(f5,negated_conjecture,(
% 0.20/0.46    ~! [X0] : r1_setfam_1(k1_xboole_0,X0)),
% 0.20/0.46    inference(negated_conjecture,[],[f4])).
% 0.20/0.46  fof(f4,conjecture,(
% 0.20/0.46    ! [X0] : r1_setfam_1(k1_xboole_0,X0)),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_setfam_1)).
% 0.20/0.46  % SZS output end Proof for theBenchmark
% 0.20/0.46  % (4049)------------------------------
% 0.20/0.46  % (4049)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (4049)Termination reason: Refutation
% 0.20/0.46  
% 0.20/0.46  % (4049)Memory used [KB]: 10618
% 0.20/0.46  % (4049)Time elapsed: 0.053 s
% 0.20/0.46  % (4049)------------------------------
% 0.20/0.46  % (4049)------------------------------
% 0.20/0.46  % (4039)Success in time 0.111 s
%------------------------------------------------------------------------------
