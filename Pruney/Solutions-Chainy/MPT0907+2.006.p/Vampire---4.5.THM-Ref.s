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
% DateTime   : Thu Dec  3 12:59:21 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   42 (  70 expanded)
%              Number of leaves         :    9 (  25 expanded)
%              Depth                    :    8
%              Number of atoms          :   93 ( 157 expanded)
%              Number of equality atoms :   38 (  66 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f67,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f25,f36,f42,f47,f61,f66])).

fof(f66,plain,
    ( ~ spl3_2
    | ~ spl3_6 ),
    inference(avatar_contradiction_clause,[],[f65])).

fof(f65,plain,
    ( $false
    | ~ spl3_2
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f64,f31])).

fof(f31,plain,
    ( sK0 = k2_mcart_1(sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f29])).

fof(f29,plain,
    ( spl3_2
  <=> sK0 = k2_mcart_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f64,plain,
    ( sK0 != k2_mcart_1(sK0)
    | ~ spl3_6 ),
    inference(superposition,[],[f19,f60])).

fof(f60,plain,
    ( sK0 = k4_tarski(k1_mcart_1(sK0),sK0)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl3_6
  <=> sK0 = k4_tarski(k1_mcart_1(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f19,plain,(
    ! [X2,X1] : k4_tarski(X1,X2) != k2_mcart_1(k4_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f14])).

% (6684)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
fof(f14,plain,(
    ! [X2,X0,X1] :
      ( k4_tarski(X1,X2) != X0
      | k2_mcart_1(X0) != X0 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 )
      | ! [X1,X2] : k4_tarski(X1,X2) != X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).

fof(f61,plain,
    ( spl3_6
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f56,f29,f22,f58])).

fof(f22,plain,
    ( spl3_1
  <=> r2_hidden(sK0,k2_zfmisc_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f56,plain,
    ( sK0 = k4_tarski(k1_mcart_1(sK0),sK0)
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f27,f31])).

fof(f27,plain,
    ( sK0 = k4_tarski(k1_mcart_1(sK0),k2_mcart_1(sK0))
    | ~ spl3_1 ),
    inference(subsumption_resolution,[],[f26,f15])).

fof(f15,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f26,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK2))
    | sK0 = k4_tarski(k1_mcart_1(sK0),k2_mcart_1(sK0))
    | ~ spl3_1 ),
    inference(resolution,[],[f24,f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1)
      | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,X1)
       => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_mcart_1)).

fof(f24,plain,
    ( r2_hidden(sK0,k2_zfmisc_1(sK1,sK2))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f22])).

fof(f47,plain,
    ( ~ spl3_3
    | ~ spl3_4 ),
    inference(avatar_contradiction_clause,[],[f46])).

fof(f46,plain,
    ( $false
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f44,f35])).

fof(f35,plain,
    ( sK0 = k1_mcart_1(sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f33])).

fof(f33,plain,
    ( spl3_3
  <=> sK0 = k1_mcart_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f44,plain,
    ( sK0 != k1_mcart_1(sK0)
    | ~ spl3_4 ),
    inference(superposition,[],[f20,f41])).

fof(f41,plain,
    ( sK0 = k4_tarski(sK0,k2_mcart_1(sK0))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f39])).

fof(f39,plain,
    ( spl3_4
  <=> sK0 = k4_tarski(sK0,k2_mcart_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f20,plain,(
    ! [X2,X1] : k4_tarski(X1,X2) != k1_mcart_1(k4_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f13])).

fof(f13,plain,(
    ! [X2,X0,X1] :
      ( k4_tarski(X1,X2) != X0
      | k1_mcart_1(X0) != X0 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f42,plain,
    ( spl3_4
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f37,f33,f22,f39])).

fof(f37,plain,
    ( sK0 = k4_tarski(sK0,k2_mcart_1(sK0))
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f27,f35])).

fof(f36,plain,
    ( spl3_2
    | spl3_3 ),
    inference(avatar_split_clause,[],[f11,f33,f29])).

fof(f11,plain,
    ( sK0 = k1_mcart_1(sK0)
    | sK0 = k2_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( ( k2_mcart_1(X0) = X0
        | k1_mcart_1(X0) = X0 )
      & r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
       => ( k2_mcart_1(X0) != X0
          & k1_mcart_1(X0) != X0 ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_mcart_1)).

fof(f25,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f12,f22])).

fof(f12,plain,(
    r2_hidden(sK0,k2_zfmisc_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f7])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:50:37 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.21/0.48  % (6673)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.48  % (6673)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f67,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f25,f36,f42,f47,f61,f66])).
% 0.21/0.48  fof(f66,plain,(
% 0.21/0.48    ~spl3_2 | ~spl3_6),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f65])).
% 0.21/0.48  fof(f65,plain,(
% 0.21/0.48    $false | (~spl3_2 | ~spl3_6)),
% 0.21/0.48    inference(subsumption_resolution,[],[f64,f31])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    sK0 = k2_mcart_1(sK0) | ~spl3_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f29])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    spl3_2 <=> sK0 = k2_mcart_1(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.48  fof(f64,plain,(
% 0.21/0.48    sK0 != k2_mcart_1(sK0) | ~spl3_6),
% 0.21/0.48    inference(superposition,[],[f19,f60])).
% 0.21/0.48  fof(f60,plain,(
% 0.21/0.48    sK0 = k4_tarski(k1_mcart_1(sK0),sK0) | ~spl3_6),
% 0.21/0.48    inference(avatar_component_clause,[],[f58])).
% 0.21/0.48  fof(f58,plain,(
% 0.21/0.48    spl3_6 <=> sK0 = k4_tarski(k1_mcart_1(sK0),sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ( ! [X2,X1] : (k4_tarski(X1,X2) != k2_mcart_1(k4_tarski(X1,X2))) )),
% 0.21/0.48    inference(equality_resolution,[],[f14])).
% 0.21/0.48  % (6684)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k4_tarski(X1,X2) != X0 | k2_mcart_1(X0) != X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,plain,(
% 0.21/0.48    ! [X0] : ((k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0) | ! [X1,X2] : k4_tarski(X1,X2) != X0)),
% 0.21/0.48    inference(ennf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).
% 0.21/0.48  fof(f61,plain,(
% 0.21/0.48    spl3_6 | ~spl3_1 | ~spl3_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f56,f29,f22,f58])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    spl3_1 <=> r2_hidden(sK0,k2_zfmisc_1(sK1,sK2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.48  fof(f56,plain,(
% 0.21/0.48    sK0 = k4_tarski(k1_mcart_1(sK0),sK0) | (~spl3_1 | ~spl3_2)),
% 0.21/0.48    inference(forward_demodulation,[],[f27,f31])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    sK0 = k4_tarski(k1_mcart_1(sK0),k2_mcart_1(sK0)) | ~spl3_1),
% 0.21/0.48    inference(subsumption_resolution,[],[f26,f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ~v1_relat_1(k2_zfmisc_1(sK1,sK2)) | sK0 = k4_tarski(k1_mcart_1(sK0),k2_mcart_1(sK0)) | ~spl3_1),
% 0.21/0.48    inference(resolution,[],[f24,f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~v1_relat_1(X1) | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,plain,(
% 0.21/0.48    ! [X0,X1] : (k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(flattening,[],[f9])).
% 0.21/0.48  fof(f9,plain,(
% 0.21/0.48    ! [X0,X1] : ((k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1)) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,X1) => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_mcart_1)).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    r2_hidden(sK0,k2_zfmisc_1(sK1,sK2)) | ~spl3_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f22])).
% 0.21/0.48  fof(f47,plain,(
% 0.21/0.48    ~spl3_3 | ~spl3_4),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f46])).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    $false | (~spl3_3 | ~spl3_4)),
% 0.21/0.48    inference(subsumption_resolution,[],[f44,f35])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    sK0 = k1_mcart_1(sK0) | ~spl3_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f33])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    spl3_3 <=> sK0 = k1_mcart_1(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    sK0 != k1_mcart_1(sK0) | ~spl3_4),
% 0.21/0.48    inference(superposition,[],[f20,f41])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    sK0 = k4_tarski(sK0,k2_mcart_1(sK0)) | ~spl3_4),
% 0.21/0.48    inference(avatar_component_clause,[],[f39])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    spl3_4 <=> sK0 = k4_tarski(sK0,k2_mcart_1(sK0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ( ! [X2,X1] : (k4_tarski(X1,X2) != k1_mcart_1(k4_tarski(X1,X2))) )),
% 0.21/0.48    inference(equality_resolution,[],[f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k4_tarski(X1,X2) != X0 | k1_mcart_1(X0) != X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f8])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    spl3_4 | ~spl3_1 | ~spl3_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f37,f33,f22,f39])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    sK0 = k4_tarski(sK0,k2_mcart_1(sK0)) | (~spl3_1 | ~spl3_3)),
% 0.21/0.48    inference(forward_demodulation,[],[f27,f35])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    spl3_2 | spl3_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f11,f33,f29])).
% 0.21/0.49  fof(f11,plain,(
% 0.21/0.49    sK0 = k1_mcart_1(sK0) | sK0 = k2_mcart_1(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,plain,(
% 0.21/0.49    ? [X0,X1,X2] : ((k2_mcart_1(X0) = X0 | k1_mcart_1(X0) = X0) & r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.21/0.49    inference(ennf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,negated_conjecture,(
% 0.21/0.49    ~! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 0.21/0.49    inference(negated_conjecture,[],[f5])).
% 0.21/0.49  fof(f5,conjecture,(
% 0.21/0.49    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_mcart_1)).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    spl3_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f12,f22])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    r2_hidden(sK0,k2_zfmisc_1(sK1,sK2))),
% 0.21/0.49    inference(cnf_transformation,[],[f7])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (6673)------------------------------
% 0.21/0.49  % (6673)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (6673)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (6673)Memory used [KB]: 10618
% 0.21/0.49  % (6673)Time elapsed: 0.053 s
% 0.21/0.49  % (6673)------------------------------
% 0.21/0.49  % (6673)------------------------------
% 0.21/0.49  % (6669)Success in time 0.119 s
%------------------------------------------------------------------------------
