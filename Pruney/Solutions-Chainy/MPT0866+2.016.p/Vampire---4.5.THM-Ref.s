%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:45 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   56 (  88 expanded)
%              Number of leaves         :   16 (  37 expanded)
%              Depth                    :    8
%              Number of atoms          :  131 ( 243 expanded)
%              Number of equality atoms :   47 ( 113 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f75,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f34,f38,f42,f46,f55,f64,f71,f74])).

fof(f74,plain,
    ( spl5_4
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f72,f59,f44])).

fof(f44,plain,
    ( spl5_4
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f59,plain,
    ( spl5_6
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f72,plain,
    ( k1_xboole_0 = sK0
    | ~ spl5_6 ),
    inference(resolution,[],[f60,f25])).

fof(f25,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f60,plain,
    ( v1_xboole_0(sK0)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f59])).

fof(f71,plain,
    ( spl5_3
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f69,f62,f40])).

fof(f40,plain,
    ( spl5_3
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f62,plain,
    ( spl5_7
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f69,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_7 ),
    inference(resolution,[],[f63,f25])).

fof(f63,plain,
    ( v1_xboole_0(sK1)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f62])).

fof(f64,plain,
    ( spl5_6
    | spl5_7
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f56,f53,f62,f59])).

fof(f53,plain,
    ( spl5_5
  <=> v1_xboole_0(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f56,plain,
    ( v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | ~ spl5_5 ),
    inference(resolution,[],[f54,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k2_zfmisc_1(X0,X1))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k2_zfmisc_1(X0,X1))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k2_zfmisc_1(X0,X1))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_subset_1)).

fof(f54,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f53])).

fof(f55,plain,
    ( spl5_1
    | spl5_5
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f50,f36,f53,f32])).

fof(f32,plain,
    ( spl5_1
  <=> sK2 = k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f36,plain,
    ( spl5_2
  <=> m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f50,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | sK2 = k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2))
    | ~ spl5_2 ),
    inference(resolution,[],[f49,f37])).

fof(f37,plain,
    ( m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f36])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k2_zfmisc_1(X1,X2))
      | v1_xboole_0(k2_zfmisc_1(X1,X2))
      | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ),
    inference(resolution,[],[f47,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ),
    inference(superposition,[],[f30,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( k4_tarski(sK3(X0),sK4(X0)) = X0
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k4_tarski(sK3(X0),sK4(X0)) = X0
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f15,f19])).

fof(f19,plain,(
    ! [X0] :
      ( ? [X3,X4] : k4_tarski(X3,X4) = X0
     => k4_tarski(sK3(X0),sK4(X0)) = X0 ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ? [X3,X4] : k4_tarski(X3,X4) = X0
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f2])).

% (16606)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
fof(f2,axiom,(
    ! [X0,X1,X2] :
      ~ ( ! [X3,X4] : k4_tarski(X3,X4) != X0
        & r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l139_zfmisc_1)).

fof(f30,plain,(
    ! [X2,X1] : k4_tarski(X1,X2) = k4_tarski(k1_mcart_1(k4_tarski(X1,X2)),k2_mcart_1(k4_tarski(X1,X2))) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | k4_tarski(X1,X2) != X0 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ! [X1,X2] : k4_tarski(X1,X2) != X0 ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_mcart_1)).

fof(f46,plain,(
    ~ spl5_4 ),
    inference(avatar_split_clause,[],[f21,f44])).

fof(f21,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( sK2 != k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2))
    & m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1))
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f17,f16])).

fof(f16,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) != X2
            & m1_subset_1(X2,k2_zfmisc_1(X0,X1)) )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
   => ( ? [X2] :
          ( k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) != X2
          & m1_subset_1(X2,k2_zfmisc_1(sK0,sK1)) )
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0 ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X2] :
        ( k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) != X2
        & m1_subset_1(X2,k2_zfmisc_1(sK0,sK1)) )
   => ( sK2 != k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2))
      & m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) != X2
          & m1_subset_1(X2,k2_zfmisc_1(X0,X1)) )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( ~ ! [X2] :
                ( m1_subset_1(X2,k2_zfmisc_1(X0,X1))
               => k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) = X2 )
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ~ ( ~ ! [X2] :
              ( m1_subset_1(X2,k2_zfmisc_1(X0,X1))
             => k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) = X2 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_mcart_1)).

fof(f42,plain,(
    ~ spl5_3 ),
    inference(avatar_split_clause,[],[f22,f40])).

fof(f22,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f18])).

fof(f38,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f23,f36])).

fof(f23,plain,(
    m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f34,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f24,f32])).

fof(f24,plain,(
    sK2 != k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2)) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:47:29 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.41  % (16604)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.41  % (16604)Refutation not found, incomplete strategy% (16604)------------------------------
% 0.21/0.41  % (16604)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.41  % (16604)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.41  
% 0.21/0.41  % (16604)Memory used [KB]: 6012
% 0.21/0.41  % (16604)Time elapsed: 0.002 s
% 0.21/0.41  % (16604)------------------------------
% 0.21/0.41  % (16604)------------------------------
% 0.21/0.45  % (16612)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.45  % (16612)Refutation not found, incomplete strategy% (16612)------------------------------
% 0.21/0.45  % (16612)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.45  % (16612)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.45  
% 0.21/0.45  % (16612)Memory used [KB]: 10618
% 0.21/0.45  % (16612)Time elapsed: 0.044 s
% 0.21/0.45  % (16612)------------------------------
% 0.21/0.45  % (16612)------------------------------
% 0.21/0.47  % (16600)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.47  % (16598)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.47  % (16598)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f75,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f34,f38,f42,f46,f55,f64,f71,f74])).
% 0.21/0.47  fof(f74,plain,(
% 0.21/0.47    spl5_4 | ~spl5_6),
% 0.21/0.47    inference(avatar_split_clause,[],[f72,f59,f44])).
% 0.21/0.47  fof(f44,plain,(
% 0.21/0.47    spl5_4 <=> k1_xboole_0 = sK0),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.47  fof(f59,plain,(
% 0.21/0.47    spl5_6 <=> v1_xboole_0(sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.21/0.47  fof(f72,plain,(
% 0.21/0.47    k1_xboole_0 = sK0 | ~spl5_6),
% 0.21/0.47    inference(resolution,[],[f60,f25])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.21/0.47    inference(cnf_transformation,[],[f9])).
% 0.21/0.47  fof(f9,plain,(
% 0.21/0.47    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.21/0.47  fof(f60,plain,(
% 0.21/0.47    v1_xboole_0(sK0) | ~spl5_6),
% 0.21/0.47    inference(avatar_component_clause,[],[f59])).
% 0.21/0.47  fof(f71,plain,(
% 0.21/0.47    spl5_3 | ~spl5_7),
% 0.21/0.47    inference(avatar_split_clause,[],[f69,f62,f40])).
% 0.21/0.47  fof(f40,plain,(
% 0.21/0.47    spl5_3 <=> k1_xboole_0 = sK1),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.47  fof(f62,plain,(
% 0.21/0.47    spl5_7 <=> v1_xboole_0(sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.21/0.47  fof(f69,plain,(
% 0.21/0.47    k1_xboole_0 = sK1 | ~spl5_7),
% 0.21/0.47    inference(resolution,[],[f63,f25])).
% 0.21/0.47  fof(f63,plain,(
% 0.21/0.47    v1_xboole_0(sK1) | ~spl5_7),
% 0.21/0.47    inference(avatar_component_clause,[],[f62])).
% 0.21/0.47  fof(f64,plain,(
% 0.21/0.47    spl5_6 | spl5_7 | ~spl5_5),
% 0.21/0.47    inference(avatar_split_clause,[],[f56,f53,f62,f59])).
% 0.21/0.47  fof(f53,plain,(
% 0.21/0.47    spl5_5 <=> v1_xboole_0(k2_zfmisc_1(sK0,sK1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.21/0.47  fof(f56,plain,(
% 0.21/0.47    v1_xboole_0(sK1) | v1_xboole_0(sK0) | ~spl5_5),
% 0.21/0.47    inference(resolution,[],[f54,f28])).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~v1_xboole_0(k2_zfmisc_1(X0,X1)) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f14])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    ! [X0,X1] : (~v1_xboole_0(k2_zfmisc_1(X0,X1)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 0.21/0.47    inference(flattening,[],[f13])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    ! [X0,X1] : (~v1_xboole_0(k2_zfmisc_1(X0,X1)) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k2_zfmisc_1(X0,X1)))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_subset_1)).
% 0.21/0.47  fof(f54,plain,(
% 0.21/0.47    v1_xboole_0(k2_zfmisc_1(sK0,sK1)) | ~spl5_5),
% 0.21/0.47    inference(avatar_component_clause,[],[f53])).
% 0.21/0.47  fof(f55,plain,(
% 0.21/0.47    spl5_1 | spl5_5 | ~spl5_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f50,f36,f53,f32])).
% 0.21/0.47  fof(f32,plain,(
% 0.21/0.47    spl5_1 <=> sK2 = k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.47  fof(f36,plain,(
% 0.21/0.47    spl5_2 <=> m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.47  fof(f50,plain,(
% 0.21/0.47    v1_xboole_0(k2_zfmisc_1(sK0,sK1)) | sK2 = k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2)) | ~spl5_2),
% 0.21/0.47    inference(resolution,[],[f49,f37])).
% 0.21/0.47  fof(f37,plain,(
% 0.21/0.47    m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1)) | ~spl5_2),
% 0.21/0.47    inference(avatar_component_clause,[],[f36])).
% 0.21/0.47  fof(f49,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k2_zfmisc_1(X1,X2)) | v1_xboole_0(k2_zfmisc_1(X1,X2)) | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0) )),
% 0.21/0.47    inference(resolution,[],[f47,f27])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f12])).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.21/0.47    inference(flattening,[],[f11])).
% 0.21/0.47  fof(f11,plain,(
% 0.21/0.47    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.21/0.47  fof(f47,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0) )),
% 0.21/0.47    inference(superposition,[],[f30,f29])).
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k4_tarski(sK3(X0),sK4(X0)) = X0 | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f20])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (k4_tarski(sK3(X0),sK4(X0)) = X0 | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f15,f19])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    ! [X0] : (? [X3,X4] : k4_tarski(X3,X4) = X0 => k4_tarski(sK3(X0),sK4(X0)) = X0)),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (? [X3,X4] : k4_tarski(X3,X4) = X0 | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.21/0.47    inference(ennf_transformation,[],[f2])).
% 0.21/0.47  % (16606)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : ~(! [X3,X4] : k4_tarski(X3,X4) != X0 & r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l139_zfmisc_1)).
% 0.21/0.47  fof(f30,plain,(
% 0.21/0.47    ( ! [X2,X1] : (k4_tarski(X1,X2) = k4_tarski(k1_mcart_1(k4_tarski(X1,X2)),k2_mcart_1(k4_tarski(X1,X2)))) )),
% 0.21/0.47    inference(equality_resolution,[],[f26])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | k4_tarski(X1,X2) != X0) )),
% 0.21/0.47    inference(cnf_transformation,[],[f10])).
% 0.21/0.47  fof(f10,plain,(
% 0.21/0.47    ! [X0] : (k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ! [X1,X2] : k4_tarski(X1,X2) != X0)),
% 0.21/0.47    inference(ennf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,axiom,(
% 0.21/0.47    ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_mcart_1)).
% 0.21/0.47  fof(f46,plain,(
% 0.21/0.47    ~spl5_4),
% 0.21/0.47    inference(avatar_split_clause,[],[f21,f44])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    k1_xboole_0 != sK0),
% 0.21/0.47    inference(cnf_transformation,[],[f18])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    (sK2 != k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2)) & m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1))) & k1_xboole_0 != sK1 & k1_xboole_0 != sK0),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f17,f16])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    ? [X0,X1] : (? [X2] : (k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) != X2 & m1_subset_1(X2,k2_zfmisc_1(X0,X1))) & k1_xboole_0 != X1 & k1_xboole_0 != X0) => (? [X2] : (k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) != X2 & m1_subset_1(X2,k2_zfmisc_1(sK0,sK1))) & k1_xboole_0 != sK1 & k1_xboole_0 != sK0)),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ? [X2] : (k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) != X2 & m1_subset_1(X2,k2_zfmisc_1(sK0,sK1))) => (sK2 != k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2)) & m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f8,plain,(
% 0.21/0.47    ? [X0,X1] : (? [X2] : (k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) != X2 & m1_subset_1(X2,k2_zfmisc_1(X0,X1))) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.47    inference(ennf_transformation,[],[f7])).
% 0.21/0.47  fof(f7,negated_conjecture,(
% 0.21/0.47    ~! [X0,X1] : ~(~! [X2] : (m1_subset_1(X2,k2_zfmisc_1(X0,X1)) => k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) = X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.47    inference(negated_conjecture,[],[f6])).
% 0.21/0.47  fof(f6,conjecture,(
% 0.21/0.47    ! [X0,X1] : ~(~! [X2] : (m1_subset_1(X2,k2_zfmisc_1(X0,X1)) => k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) = X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_mcart_1)).
% 0.21/0.47  fof(f42,plain,(
% 0.21/0.47    ~spl5_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f22,f40])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    k1_xboole_0 != sK1),
% 0.21/0.47    inference(cnf_transformation,[],[f18])).
% 0.21/0.47  fof(f38,plain,(
% 0.21/0.47    spl5_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f23,f36])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1))),
% 0.21/0.47    inference(cnf_transformation,[],[f18])).
% 0.21/0.47  fof(f34,plain,(
% 0.21/0.47    ~spl5_1),
% 0.21/0.47    inference(avatar_split_clause,[],[f24,f32])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    sK2 != k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2))),
% 0.21/0.47    inference(cnf_transformation,[],[f18])).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (16598)------------------------------
% 0.21/0.47  % (16598)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (16598)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (16598)Memory used [KB]: 10618
% 0.21/0.47  % (16598)Time elapsed: 0.046 s
% 0.21/0.47  % (16598)------------------------------
% 0.21/0.47  % (16598)------------------------------
% 0.21/0.47  % (16590)Success in time 0.119 s
%------------------------------------------------------------------------------
