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
% DateTime   : Thu Dec  3 12:58:45 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   59 (  81 expanded)
%              Number of leaves         :   14 (  28 expanded)
%              Depth                    :    8
%              Number of atoms          :  133 ( 195 expanded)
%              Number of equality atoms :   29 (  62 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f76,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f29,f34,f39,f45,f54,f65,f68,f71,f75])).

fof(f75,plain,
    ( spl3_4
    | ~ spl3_5 ),
    inference(avatar_contradiction_clause,[],[f74])).

fof(f74,plain,
    ( $false
    | spl3_4
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f73,f44])).

fof(f44,plain,
    ( sK2 != k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2))
    | spl3_4 ),
    inference(avatar_component_clause,[],[f42])).

fof(f42,plain,
    ( spl3_4
  <=> sK2 = k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f73,plain,
    ( sK2 = k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2))
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f72,f21])).

fof(f21,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f72,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | sK2 = k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2))
    | ~ spl3_5 ),
    inference(resolution,[],[f49,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1)
      | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,X1)
       => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_mcart_1)).

fof(f49,plain,
    ( r2_hidden(sK2,k2_zfmisc_1(sK0,sK1))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f47])).

fof(f47,plain,
    ( spl3_5
  <=> r2_hidden(sK2,k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f71,plain,
    ( spl3_2
    | ~ spl3_8 ),
    inference(avatar_contradiction_clause,[],[f70])).

fof(f70,plain,
    ( $false
    | spl3_2
    | ~ spl3_8 ),
    inference(subsumption_resolution,[],[f69,f33])).

fof(f33,plain,
    ( k1_xboole_0 != sK1
    | spl3_2 ),
    inference(avatar_component_clause,[],[f31])).

fof(f31,plain,
    ( spl3_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f69,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_8 ),
    inference(resolution,[],[f64,f20])).

fof(f20,plain,(
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

fof(f64,plain,
    ( v1_xboole_0(sK1)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl3_8
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f68,plain,
    ( spl3_1
    | ~ spl3_7 ),
    inference(avatar_contradiction_clause,[],[f67])).

fof(f67,plain,
    ( $false
    | spl3_1
    | ~ spl3_7 ),
    inference(subsumption_resolution,[],[f66,f28])).

fof(f28,plain,
    ( k1_xboole_0 != sK0
    | spl3_1 ),
    inference(avatar_component_clause,[],[f26])).

fof(f26,plain,
    ( spl3_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f66,plain,
    ( k1_xboole_0 = sK0
    | ~ spl3_7 ),
    inference(resolution,[],[f60,f20])).

fof(f60,plain,
    ( v1_xboole_0(sK0)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl3_7
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f65,plain,
    ( spl3_7
    | spl3_8
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f55,f51,f62,f58])).

fof(f51,plain,
    ( spl3_6
  <=> v1_xboole_0(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f55,plain,
    ( v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | ~ spl3_6 ),
    inference(resolution,[],[f53,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k2_zfmisc_1(X0,X1))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k2_zfmisc_1(X0,X1))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k2_zfmisc_1(X0,X1))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_subset_1)).

fof(f53,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f51])).

fof(f54,plain,
    ( spl3_5
    | spl3_6
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f40,f36,f51,f47])).

fof(f36,plain,
    ( spl3_3
  <=> m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f40,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | r2_hidden(sK2,k2_zfmisc_1(sK0,sK1))
    | ~ spl3_3 ),
    inference(resolution,[],[f38,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f38,plain,
    ( m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f36])).

fof(f45,plain,(
    ~ spl3_4 ),
    inference(avatar_split_clause,[],[f17,f42])).

fof(f17,plain,(
    sK2 != k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2)) ),
    inference(cnf_transformation,[],[f8])).

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

fof(f39,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f16,f36])).

fof(f16,plain,(
    m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f34,plain,(
    ~ spl3_2 ),
    inference(avatar_split_clause,[],[f19,f31])).

fof(f19,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f8])).

fof(f29,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f18,f26])).

fof(f18,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:04:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (14915)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.48  % (14922)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.48  % (14912)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.48  % (14915)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f76,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f29,f34,f39,f45,f54,f65,f68,f71,f75])).
% 0.21/0.48  fof(f75,plain,(
% 0.21/0.48    spl3_4 | ~spl3_5),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f74])).
% 0.21/0.48  fof(f74,plain,(
% 0.21/0.48    $false | (spl3_4 | ~spl3_5)),
% 0.21/0.48    inference(subsumption_resolution,[],[f73,f44])).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    sK2 != k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2)) | spl3_4),
% 0.21/0.48    inference(avatar_component_clause,[],[f42])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    spl3_4 <=> sK2 = k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.48  fof(f73,plain,(
% 0.21/0.48    sK2 = k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2)) | ~spl3_5),
% 0.21/0.48    inference(subsumption_resolution,[],[f72,f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.48  fof(f72,plain,(
% 0.21/0.48    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | sK2 = k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2)) | ~spl3_5),
% 0.21/0.48    inference(resolution,[],[f49,f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~v1_relat_1(X1) | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    ! [X0,X1] : (k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(flattening,[],[f10])).
% 0.21/0.48  fof(f10,plain,(
% 0.21/0.48    ! [X0,X1] : ((k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1)) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,X1) => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_mcart_1)).
% 0.21/0.48  fof(f49,plain,(
% 0.21/0.48    r2_hidden(sK2,k2_zfmisc_1(sK0,sK1)) | ~spl3_5),
% 0.21/0.48    inference(avatar_component_clause,[],[f47])).
% 0.21/0.48  fof(f47,plain,(
% 0.21/0.48    spl3_5 <=> r2_hidden(sK2,k2_zfmisc_1(sK0,sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.48  fof(f71,plain,(
% 0.21/0.48    spl3_2 | ~spl3_8),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f70])).
% 0.21/0.48  fof(f70,plain,(
% 0.21/0.48    $false | (spl3_2 | ~spl3_8)),
% 0.21/0.48    inference(subsumption_resolution,[],[f69,f33])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    k1_xboole_0 != sK1 | spl3_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f31])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    spl3_2 <=> k1_xboole_0 = sK1),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.48  fof(f69,plain,(
% 0.21/0.48    k1_xboole_0 = sK1 | ~spl3_8),
% 0.21/0.48    inference(resolution,[],[f64,f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,plain,(
% 0.21/0.48    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.21/0.48  fof(f64,plain,(
% 0.21/0.48    v1_xboole_0(sK1) | ~spl3_8),
% 0.21/0.48    inference(avatar_component_clause,[],[f62])).
% 0.21/0.48  fof(f62,plain,(
% 0.21/0.48    spl3_8 <=> v1_xboole_0(sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.48  fof(f68,plain,(
% 0.21/0.48    spl3_1 | ~spl3_7),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f67])).
% 0.21/0.48  fof(f67,plain,(
% 0.21/0.48    $false | (spl3_1 | ~spl3_7)),
% 0.21/0.48    inference(subsumption_resolution,[],[f66,f28])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    k1_xboole_0 != sK0 | spl3_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f26])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    spl3_1 <=> k1_xboole_0 = sK0),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.48  fof(f66,plain,(
% 0.21/0.48    k1_xboole_0 = sK0 | ~spl3_7),
% 0.21/0.48    inference(resolution,[],[f60,f20])).
% 0.21/0.48  fof(f60,plain,(
% 0.21/0.48    v1_xboole_0(sK0) | ~spl3_7),
% 0.21/0.48    inference(avatar_component_clause,[],[f58])).
% 0.21/0.48  fof(f58,plain,(
% 0.21/0.48    spl3_7 <=> v1_xboole_0(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.48  fof(f65,plain,(
% 0.21/0.48    spl3_7 | spl3_8 | ~spl3_6),
% 0.21/0.48    inference(avatar_split_clause,[],[f55,f51,f62,f58])).
% 0.21/0.48  fof(f51,plain,(
% 0.21/0.48    spl3_6 <=> v1_xboole_0(k2_zfmisc_1(sK0,sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.48  fof(f55,plain,(
% 0.21/0.48    v1_xboole_0(sK1) | v1_xboole_0(sK0) | ~spl3_6),
% 0.21/0.48    inference(resolution,[],[f53,f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v1_xboole_0(k2_zfmisc_1(X0,X1)) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ! [X0,X1] : (~v1_xboole_0(k2_zfmisc_1(X0,X1)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 0.21/0.48    inference(flattening,[],[f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ! [X0,X1] : (~v1_xboole_0(k2_zfmisc_1(X0,X1)) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k2_zfmisc_1(X0,X1)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_subset_1)).
% 0.21/0.48  fof(f53,plain,(
% 0.21/0.48    v1_xboole_0(k2_zfmisc_1(sK0,sK1)) | ~spl3_6),
% 0.21/0.48    inference(avatar_component_clause,[],[f51])).
% 0.21/0.48  fof(f54,plain,(
% 0.21/0.48    spl3_5 | spl3_6 | ~spl3_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f40,f36,f51,f47])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    spl3_3 <=> m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    v1_xboole_0(k2_zfmisc_1(sK0,sK1)) | r2_hidden(sK2,k2_zfmisc_1(sK0,sK1)) | ~spl3_3),
% 0.21/0.48    inference(resolution,[],[f38,f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.21/0.48    inference(flattening,[],[f12])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1)) | ~spl3_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f36])).
% 0.21/0.48  fof(f45,plain,(
% 0.21/0.48    ~spl3_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f17,f42])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    sK2 != k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2))),
% 0.21/0.48    inference(cnf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,plain,(
% 0.21/0.48    ? [X0,X1] : (? [X2] : (k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) != X2 & m1_subset_1(X2,k2_zfmisc_1(X0,X1))) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.48    inference(ennf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1] : ~(~! [X2] : (m1_subset_1(X2,k2_zfmisc_1(X0,X1)) => k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) = X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.48    inference(negated_conjecture,[],[f6])).
% 0.21/0.48  fof(f6,conjecture,(
% 0.21/0.48    ! [X0,X1] : ~(~! [X2] : (m1_subset_1(X2,k2_zfmisc_1(X0,X1)) => k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) = X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_mcart_1)).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    spl3_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f16,f36])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1))),
% 0.21/0.48    inference(cnf_transformation,[],[f8])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    ~spl3_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f19,f31])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    k1_xboole_0 != sK1),
% 0.21/0.48    inference(cnf_transformation,[],[f8])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ~spl3_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f18,f26])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    k1_xboole_0 != sK0),
% 0.21/0.48    inference(cnf_transformation,[],[f8])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (14915)------------------------------
% 0.21/0.48  % (14915)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (14915)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (14915)Memory used [KB]: 10618
% 0.21/0.48  % (14915)Time elapsed: 0.062 s
% 0.21/0.48  % (14915)------------------------------
% 0.21/0.48  % (14915)------------------------------
% 0.21/0.48  % (14911)Success in time 0.12 s
%------------------------------------------------------------------------------
