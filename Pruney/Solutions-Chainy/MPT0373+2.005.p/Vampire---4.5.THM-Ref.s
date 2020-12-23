%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:30 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   40 (  52 expanded)
%              Number of leaves         :    9 (  14 expanded)
%              Depth                    :   11
%              Number of atoms          :   86 ( 126 expanded)
%              Number of equality atoms :   16 (  24 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f118,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f50,f115,f117])).

fof(f117,plain,(
    ~ spl4_2 ),
    inference(avatar_contradiction_clause,[],[f116])).

fof(f116,plain,
    ( $false
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f43,f51])).

fof(f51,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(unit_resulting_resolution,[],[f16,f30])).

fof(f30,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f16,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ~ m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
      & k1_xboole_0 != X0
      & m1_subset_1(X1,X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1] :
      ( ~ m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
      & k1_xboole_0 != X0
      & m1_subset_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,X0)
       => ( k1_xboole_0 != X0
         => m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
     => ( k1_xboole_0 != X0
       => m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_subset_1)).

fof(f43,plain,
    ( v1_xboole_0(sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f42])).

fof(f42,plain,
    ( spl4_2
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f115,plain,(
    ~ spl4_3 ),
    inference(avatar_contradiction_clause,[],[f114])).

fof(f114,plain,
    ( $false
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f110,f78])).

fof(f78,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_tarski(sK1),sK0)
    | ~ spl4_3 ),
    inference(unit_resulting_resolution,[],[f49,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l35_zfmisc_1)).

fof(f49,plain,
    ( r2_hidden(sK1,sK0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f47])).

fof(f47,plain,
    ( spl4_3
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f110,plain,(
    k1_xboole_0 != k4_xboole_0(k1_tarski(sK1),sK0) ),
    inference(resolution,[],[f98,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f98,plain,(
    ~ r1_tarski(k1_tarski(sK1),sK0) ),
    inference(unit_resulting_resolution,[],[f71,f34])).

fof(f34,plain,(
    ! [X2,X0] :
      ( ~ r1_tarski(X2,X0)
      | r2_hidden(X2,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f18])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X0)
      | r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f71,plain,(
    ~ r2_hidden(k1_tarski(sK1),k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f59,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f59,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ r2_hidden(k1_tarski(sK1),k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f17,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ r2_hidden(X1,X0)
      | m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f17,plain,(
    ~ m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f50,plain,
    ( spl4_3
    | spl4_2 ),
    inference(avatar_split_clause,[],[f36,f42,f47])).

fof(f36,plain,
    ( v1_xboole_0(sK0)
    | r2_hidden(sK1,sK0) ),
    inference(resolution,[],[f15,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f15,plain,(
    m1_subset_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 19:04:04 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.43  % (7295)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.19/0.45  % (7295)Refutation found. Thanks to Tanya!
% 0.19/0.45  % SZS status Theorem for theBenchmark
% 0.19/0.45  % SZS output start Proof for theBenchmark
% 0.19/0.45  fof(f118,plain,(
% 0.19/0.45    $false),
% 0.19/0.45    inference(avatar_sat_refutation,[],[f50,f115,f117])).
% 0.19/0.45  fof(f117,plain,(
% 0.19/0.45    ~spl4_2),
% 0.19/0.45    inference(avatar_contradiction_clause,[],[f116])).
% 0.19/0.45  fof(f116,plain,(
% 0.19/0.45    $false | ~spl4_2),
% 0.19/0.45    inference(subsumption_resolution,[],[f43,f51])).
% 0.19/0.45  fof(f51,plain,(
% 0.19/0.45    ~v1_xboole_0(sK0)),
% 0.19/0.45    inference(unit_resulting_resolution,[],[f16,f30])).
% 0.19/0.45  fof(f30,plain,(
% 0.19/0.45    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.19/0.45    inference(cnf_transformation,[],[f14])).
% 0.19/0.45  fof(f14,plain,(
% 0.19/0.45    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.19/0.45    inference(ennf_transformation,[],[f2])).
% 0.19/0.45  fof(f2,axiom,(
% 0.19/0.45    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.19/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.19/0.45  fof(f16,plain,(
% 0.19/0.45    k1_xboole_0 != sK0),
% 0.19/0.45    inference(cnf_transformation,[],[f12])).
% 0.19/0.45  fof(f12,plain,(
% 0.19/0.45    ? [X0,X1] : (~m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) & k1_xboole_0 != X0 & m1_subset_1(X1,X0))),
% 0.19/0.45    inference(flattening,[],[f11])).
% 0.19/0.45  fof(f11,plain,(
% 0.19/0.45    ? [X0,X1] : ((~m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) & k1_xboole_0 != X0) & m1_subset_1(X1,X0))),
% 0.19/0.45    inference(ennf_transformation,[],[f10])).
% 0.19/0.45  fof(f10,negated_conjecture,(
% 0.19/0.45    ~! [X0,X1] : (m1_subset_1(X1,X0) => (k1_xboole_0 != X0 => m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))))),
% 0.19/0.45    inference(negated_conjecture,[],[f9])).
% 0.19/0.45  fof(f9,conjecture,(
% 0.19/0.45    ! [X0,X1] : (m1_subset_1(X1,X0) => (k1_xboole_0 != X0 => m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))))),
% 0.19/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_subset_1)).
% 0.19/0.45  fof(f43,plain,(
% 0.19/0.45    v1_xboole_0(sK0) | ~spl4_2),
% 0.19/0.45    inference(avatar_component_clause,[],[f42])).
% 0.19/0.45  fof(f42,plain,(
% 0.19/0.45    spl4_2 <=> v1_xboole_0(sK0)),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.19/0.45  fof(f115,plain,(
% 0.19/0.45    ~spl4_3),
% 0.19/0.45    inference(avatar_contradiction_clause,[],[f114])).
% 0.19/0.45  fof(f114,plain,(
% 0.19/0.45    $false | ~spl4_3),
% 0.19/0.45    inference(subsumption_resolution,[],[f110,f78])).
% 0.19/0.45  fof(f78,plain,(
% 0.19/0.45    k1_xboole_0 = k4_xboole_0(k1_tarski(sK1),sK0) | ~spl4_3),
% 0.19/0.45    inference(unit_resulting_resolution,[],[f49,f31])).
% 0.19/0.45  fof(f31,plain,(
% 0.19/0.45    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)) )),
% 0.19/0.45    inference(cnf_transformation,[],[f7])).
% 0.19/0.45  fof(f7,axiom,(
% 0.19/0.45    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.19/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l35_zfmisc_1)).
% 0.19/0.45  fof(f49,plain,(
% 0.19/0.45    r2_hidden(sK1,sK0) | ~spl4_3),
% 0.19/0.45    inference(avatar_component_clause,[],[f47])).
% 0.19/0.45  fof(f47,plain,(
% 0.19/0.45    spl4_3 <=> r2_hidden(sK1,sK0)),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.19/0.45  fof(f110,plain,(
% 0.19/0.45    k1_xboole_0 != k4_xboole_0(k1_tarski(sK1),sK0)),
% 0.19/0.45    inference(resolution,[],[f98,f27])).
% 0.19/0.45  fof(f27,plain,(
% 0.19/0.45    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)) )),
% 0.19/0.45    inference(cnf_transformation,[],[f3])).
% 0.19/0.45  fof(f3,axiom,(
% 0.19/0.45    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 0.19/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.19/0.45  fof(f98,plain,(
% 0.19/0.45    ~r1_tarski(k1_tarski(sK1),sK0)),
% 0.19/0.45    inference(unit_resulting_resolution,[],[f71,f34])).
% 0.19/0.45  fof(f34,plain,(
% 0.19/0.45    ( ! [X2,X0] : (~r1_tarski(X2,X0) | r2_hidden(X2,k1_zfmisc_1(X0))) )),
% 0.19/0.45    inference(equality_resolution,[],[f18])).
% 0.19/0.45  fof(f18,plain,(
% 0.19/0.45    ( ! [X2,X0,X1] : (~r1_tarski(X2,X0) | r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.19/0.45    inference(cnf_transformation,[],[f6])).
% 0.19/0.45  fof(f6,axiom,(
% 0.19/0.45    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.19/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.19/0.45  fof(f71,plain,(
% 0.19/0.45    ~r2_hidden(k1_tarski(sK1),k1_zfmisc_1(sK0))),
% 0.19/0.45    inference(subsumption_resolution,[],[f59,f29])).
% 0.19/0.45  fof(f29,plain,(
% 0.19/0.45    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 0.19/0.45    inference(cnf_transformation,[],[f1])).
% 0.19/0.45  fof(f1,axiom,(
% 0.19/0.45    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.19/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.19/0.45  fof(f59,plain,(
% 0.19/0.45    v1_xboole_0(k1_zfmisc_1(sK0)) | ~r2_hidden(k1_tarski(sK1),k1_zfmisc_1(sK0))),
% 0.19/0.45    inference(resolution,[],[f17,f24])).
% 0.19/0.45  fof(f24,plain,(
% 0.19/0.45    ( ! [X0,X1] : (v1_xboole_0(X0) | ~r2_hidden(X1,X0) | m1_subset_1(X1,X0)) )),
% 0.19/0.45    inference(cnf_transformation,[],[f13])).
% 0.19/0.45  fof(f13,plain,(
% 0.19/0.45    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.19/0.45    inference(ennf_transformation,[],[f8])).
% 0.19/0.45  fof(f8,axiom,(
% 0.19/0.45    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.19/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 0.19/0.45  fof(f17,plain,(
% 0.19/0.45    ~m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(sK0))),
% 0.19/0.45    inference(cnf_transformation,[],[f12])).
% 0.19/0.45  fof(f50,plain,(
% 0.19/0.45    spl4_3 | spl4_2),
% 0.19/0.45    inference(avatar_split_clause,[],[f36,f42,f47])).
% 0.19/0.45  fof(f36,plain,(
% 0.19/0.45    v1_xboole_0(sK0) | r2_hidden(sK1,sK0)),
% 0.19/0.45    inference(resolution,[],[f15,f25])).
% 0.19/0.45  fof(f25,plain,(
% 0.19/0.45    ( ! [X0,X1] : (v1_xboole_0(X0) | r2_hidden(X1,X0) | ~m1_subset_1(X1,X0)) )),
% 0.19/0.45    inference(cnf_transformation,[],[f13])).
% 0.19/0.45  fof(f15,plain,(
% 0.19/0.45    m1_subset_1(sK1,sK0)),
% 0.19/0.45    inference(cnf_transformation,[],[f12])).
% 0.19/0.45  % SZS output end Proof for theBenchmark
% 0.19/0.45  % (7295)------------------------------
% 0.19/0.45  % (7295)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.45  % (7295)Termination reason: Refutation
% 0.19/0.45  
% 0.19/0.45  % (7295)Memory used [KB]: 10746
% 0.19/0.45  % (7295)Time elapsed: 0.059 s
% 0.19/0.45  % (7295)------------------------------
% 0.19/0.45  % (7295)------------------------------
% 0.19/0.46  % (7285)Success in time 0.105 s
%------------------------------------------------------------------------------
