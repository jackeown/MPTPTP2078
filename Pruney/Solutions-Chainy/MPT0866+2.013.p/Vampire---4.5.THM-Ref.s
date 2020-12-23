%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:44 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   62 (  86 expanded)
%              Number of leaves         :   15 (  32 expanded)
%              Depth                    :    8
%              Number of atoms          :  145 ( 211 expanded)
%              Number of equality atoms :   42 (  76 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f90,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f32,f37,f42,f48,f57,f64,f79,f83,f89])).

fof(f89,plain,
    ( spl3_1
    | ~ spl3_9 ),
    inference(avatar_contradiction_clause,[],[f88])).

fof(f88,plain,
    ( $false
    | spl3_1
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f87,f31])).

fof(f31,plain,
    ( k1_xboole_0 != sK0
    | spl3_1 ),
    inference(avatar_component_clause,[],[f29])).

fof(f29,plain,
    ( spl3_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f87,plain,
    ( k1_xboole_0 = sK0
    | ~ spl3_9 ),
    inference(resolution,[],[f78,f21])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f78,plain,
    ( v1_xboole_0(sK0)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl3_9
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f83,plain,
    ( spl3_4
    | ~ spl3_5 ),
    inference(avatar_contradiction_clause,[],[f82])).

fof(f82,plain,
    ( $false
    | spl3_4
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f81,f47])).

fof(f47,plain,
    ( sK2 != k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2))
    | spl3_4 ),
    inference(avatar_component_clause,[],[f45])).

fof(f45,plain,
    ( spl3_4
  <=> sK2 = k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f81,plain,
    ( sK2 = k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2))
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f80,f23])).

fof(f23,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f80,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | sK2 = k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2))
    | ~ spl3_5 ),
    inference(resolution,[],[f52,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1)
      | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,X1)
       => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_mcart_1)).

fof(f52,plain,
    ( r2_hidden(sK2,k2_zfmisc_1(sK0,sK1))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f50])).

fof(f50,plain,
    ( spl3_5
  <=> r2_hidden(sK2,k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f79,plain,
    ( spl3_9
    | spl3_1
    | spl3_2
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f74,f61,f34,f29,f76])).

fof(f34,plain,
    ( spl3_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f61,plain,
    ( spl3_7
  <=> v1_xboole_0(k1_relat_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f74,plain,
    ( v1_xboole_0(sK0)
    | spl3_1
    | spl3_2
    | ~ spl3_7 ),
    inference(subsumption_resolution,[],[f73,f31])).

fof(f73,plain,
    ( v1_xboole_0(sK0)
    | k1_xboole_0 = sK0
    | spl3_2
    | ~ spl3_7 ),
    inference(subsumption_resolution,[],[f72,f36])).

fof(f36,plain,
    ( k1_xboole_0 != sK1
    | spl3_2 ),
    inference(avatar_component_clause,[],[f34])).

fof(f72,plain,
    ( v1_xboole_0(sK0)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl3_7 ),
    inference(superposition,[],[f63,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k2_zfmisc_1(X0,X1)) = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
        & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ~ ( ~ ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
            & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t195_relat_1)).

fof(f63,plain,
    ( v1_xboole_0(k1_relat_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f61])).

fof(f64,plain,
    ( spl3_7
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f58,f54,f61])).

fof(f54,plain,
    ( spl3_6
  <=> v1_xboole_0(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f58,plain,
    ( v1_xboole_0(k1_relat_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl3_6 ),
    inference(resolution,[],[f56,f22])).

fof(f22,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_xboole_0(k1_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_relat_1)).

fof(f56,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f54])).

fof(f57,plain,
    ( spl3_5
    | spl3_6
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f43,f39,f54,f50])).

fof(f39,plain,
    ( spl3_3
  <=> m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f43,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | r2_hidden(sK2,k2_zfmisc_1(sK0,sK1))
    | ~ spl3_3 ),
    inference(resolution,[],[f41,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f41,plain,
    ( m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f39])).

fof(f48,plain,(
    ~ spl3_4 ),
    inference(avatar_split_clause,[],[f18,f45])).

fof(f18,plain,(
    sK2 != k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) != X2
          & m1_subset_1(X2,k2_zfmisc_1(X0,X1)) )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( ~ ! [X2] :
                ( m1_subset_1(X2,k2_zfmisc_1(X0,X1))
               => k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) = X2 )
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ~ ( ~ ! [X2] :
              ( m1_subset_1(X2,k2_zfmisc_1(X0,X1))
             => k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) = X2 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_mcart_1)).

fof(f42,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f17,f39])).

fof(f17,plain,(
    m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f37,plain,(
    ~ spl3_2 ),
    inference(avatar_split_clause,[],[f20,f34])).

fof(f20,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f9])).

fof(f32,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f19,f29])).

fof(f19,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:24:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.46  % (24950)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.48  % (24950)Refutation not found, incomplete strategy% (24950)------------------------------
% 0.21/0.48  % (24950)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (24950)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (24950)Memory used [KB]: 10490
% 0.21/0.48  % (24950)Time elapsed: 0.050 s
% 0.21/0.48  % (24950)------------------------------
% 0.21/0.48  % (24950)------------------------------
% 0.21/0.48  % (24952)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.48  % (24952)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f90,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f32,f37,f42,f48,f57,f64,f79,f83,f89])).
% 0.21/0.48  fof(f89,plain,(
% 0.21/0.48    spl3_1 | ~spl3_9),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f88])).
% 0.21/0.48  fof(f88,plain,(
% 0.21/0.48    $false | (spl3_1 | ~spl3_9)),
% 0.21/0.48    inference(subsumption_resolution,[],[f87,f31])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    k1_xboole_0 != sK0 | spl3_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f29])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    spl3_1 <=> k1_xboole_0 = sK0),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.48  fof(f87,plain,(
% 0.21/0.48    k1_xboole_0 = sK0 | ~spl3_9),
% 0.21/0.48    inference(resolution,[],[f78,f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,plain,(
% 0.21/0.48    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.21/0.48  fof(f78,plain,(
% 0.21/0.48    v1_xboole_0(sK0) | ~spl3_9),
% 0.21/0.48    inference(avatar_component_clause,[],[f76])).
% 0.21/0.48  fof(f76,plain,(
% 0.21/0.48    spl3_9 <=> v1_xboole_0(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.48  fof(f83,plain,(
% 0.21/0.48    spl3_4 | ~spl3_5),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f82])).
% 0.21/0.48  fof(f82,plain,(
% 0.21/0.48    $false | (spl3_4 | ~spl3_5)),
% 0.21/0.48    inference(subsumption_resolution,[],[f81,f47])).
% 0.21/0.48  fof(f47,plain,(
% 0.21/0.48    sK2 != k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2)) | spl3_4),
% 0.21/0.48    inference(avatar_component_clause,[],[f45])).
% 0.21/0.48  fof(f45,plain,(
% 0.21/0.48    spl3_4 <=> sK2 = k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.48  fof(f81,plain,(
% 0.21/0.48    sK2 = k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2)) | ~spl3_5),
% 0.21/0.48    inference(subsumption_resolution,[],[f80,f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.48  fof(f80,plain,(
% 0.21/0.48    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | sK2 = k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2)) | ~spl3_5),
% 0.21/0.48    inference(resolution,[],[f52,f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~v1_relat_1(X1) | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ! [X0,X1] : (k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(flattening,[],[f12])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ! [X0,X1] : ((k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1)) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,X1) => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_mcart_1)).
% 0.21/0.48  fof(f52,plain,(
% 0.21/0.48    r2_hidden(sK2,k2_zfmisc_1(sK0,sK1)) | ~spl3_5),
% 0.21/0.48    inference(avatar_component_clause,[],[f50])).
% 0.21/0.48  fof(f50,plain,(
% 0.21/0.48    spl3_5 <=> r2_hidden(sK2,k2_zfmisc_1(sK0,sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.48  fof(f79,plain,(
% 0.21/0.48    spl3_9 | spl3_1 | spl3_2 | ~spl3_7),
% 0.21/0.48    inference(avatar_split_clause,[],[f74,f61,f34,f29,f76])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    spl3_2 <=> k1_xboole_0 = sK1),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.48  fof(f61,plain,(
% 0.21/0.48    spl3_7 <=> v1_xboole_0(k1_relat_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.48  fof(f74,plain,(
% 0.21/0.48    v1_xboole_0(sK0) | (spl3_1 | spl3_2 | ~spl3_7)),
% 0.21/0.48    inference(subsumption_resolution,[],[f73,f31])).
% 0.21/0.48  fof(f73,plain,(
% 0.21/0.48    v1_xboole_0(sK0) | k1_xboole_0 = sK0 | (spl3_2 | ~spl3_7)),
% 0.21/0.48    inference(subsumption_resolution,[],[f72,f36])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    k1_xboole_0 != sK1 | spl3_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f34])).
% 0.21/0.48  fof(f72,plain,(
% 0.21/0.48    v1_xboole_0(sK0) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl3_7),
% 0.21/0.48    inference(superposition,[],[f63,f26])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ! [X0,X1] : ((k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.21/0.48    inference(ennf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0,X1] : ~(~(k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t195_relat_1)).
% 0.21/0.48  fof(f63,plain,(
% 0.21/0.48    v1_xboole_0(k1_relat_1(k2_zfmisc_1(sK0,sK1))) | ~spl3_7),
% 0.21/0.48    inference(avatar_component_clause,[],[f61])).
% 0.21/0.48  fof(f64,plain,(
% 0.21/0.48    spl3_7 | ~spl3_6),
% 0.21/0.48    inference(avatar_split_clause,[],[f58,f54,f61])).
% 0.21/0.48  fof(f54,plain,(
% 0.21/0.48    spl3_6 <=> v1_xboole_0(k2_zfmisc_1(sK0,sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.48  fof(f58,plain,(
% 0.21/0.48    v1_xboole_0(k1_relat_1(k2_zfmisc_1(sK0,sK1))) | ~spl3_6),
% 0.21/0.48    inference(resolution,[],[f56,f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_xboole_0(X0) | v1_xboole_0(k1_relat_1(X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    ! [X0] : (v1_xboole_0(k1_relat_1(X0)) | ~v1_xboole_0(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0] : (v1_xboole_0(X0) => v1_xboole_0(k1_relat_1(X0)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_relat_1)).
% 0.21/0.48  fof(f56,plain,(
% 0.21/0.48    v1_xboole_0(k2_zfmisc_1(sK0,sK1)) | ~spl3_6),
% 0.21/0.48    inference(avatar_component_clause,[],[f54])).
% 0.21/0.48  fof(f57,plain,(
% 0.21/0.48    spl3_5 | spl3_6 | ~spl3_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f43,f39,f54,f50])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    spl3_3 <=> m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    v1_xboole_0(k2_zfmisc_1(sK0,sK1)) | r2_hidden(sK2,k2_zfmisc_1(sK0,sK1)) | ~spl3_3),
% 0.21/0.48    inference(resolution,[],[f41,f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.21/0.49    inference(flattening,[],[f14])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1)) | ~spl3_3),
% 0.21/0.49    inference(avatar_component_clause,[],[f39])).
% 0.21/0.49  fof(f48,plain,(
% 0.21/0.49    ~spl3_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f18,f45])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    sK2 != k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2))),
% 0.21/0.49    inference(cnf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,plain,(
% 0.21/0.49    ? [X0,X1] : (? [X2] : (k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) != X2 & m1_subset_1(X2,k2_zfmisc_1(X0,X1))) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.49    inference(ennf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,negated_conjecture,(
% 0.21/0.49    ~! [X0,X1] : ~(~! [X2] : (m1_subset_1(X2,k2_zfmisc_1(X0,X1)) => k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) = X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.49    inference(negated_conjecture,[],[f7])).
% 0.21/0.49  fof(f7,conjecture,(
% 0.21/0.49    ! [X0,X1] : ~(~! [X2] : (m1_subset_1(X2,k2_zfmisc_1(X0,X1)) => k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) = X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_mcart_1)).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    spl3_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f17,f39])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1))),
% 0.21/0.49    inference(cnf_transformation,[],[f9])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    ~spl3_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f20,f34])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    k1_xboole_0 != sK1),
% 0.21/0.49    inference(cnf_transformation,[],[f9])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    ~spl3_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f19,f29])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    k1_xboole_0 != sK0),
% 0.21/0.49    inference(cnf_transformation,[],[f9])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (24952)------------------------------
% 0.21/0.49  % (24952)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (24952)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (24952)Memory used [KB]: 10618
% 0.21/0.49  % (24952)Time elapsed: 0.060 s
% 0.21/0.49  % (24952)------------------------------
% 0.21/0.49  % (24952)------------------------------
% 0.21/0.49  % (24948)Success in time 0.123 s
%------------------------------------------------------------------------------
