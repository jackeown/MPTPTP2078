%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:21 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 194 expanded)
%              Number of leaves         :    8 (  50 expanded)
%              Depth                    :   15
%              Number of atoms          :  138 ( 599 expanded)
%              Number of equality atoms :    9 (  64 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f228,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f138,f227])).

fof(f227,plain,(
    ~ spl5_1 ),
    inference(avatar_contradiction_clause,[],[f225])).

fof(f225,plain,
    ( $false
    | ~ spl5_1 ),
    inference(unit_resulting_resolution,[],[f166,f17,f189,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f189,plain,
    ( ~ r2_hidden(sK1,k1_zfmisc_1(sK0))
    | ~ spl5_1 ),
    inference(unit_resulting_resolution,[],[f162,f36])).

fof(f36,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_zfmisc_1(X0))
      | r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f20])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f162,plain,
    ( ~ r1_tarski(sK1,sK0)
    | ~ spl5_1 ),
    inference(unit_resulting_resolution,[],[f139,f146,f26])).

% (11823)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f146,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl5_1 ),
    inference(unit_resulting_resolution,[],[f141,f16])).

fof(f16,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,sK0)
      | r2_hidden(X2,sK1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ m1_subset_1(X2,X0) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ m1_subset_1(X2,X0) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ( ! [X2] :
              ( m1_subset_1(X2,X0)
             => r2_hidden(X2,X1) )
         => X0 = X1 ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( ! [X2] :
            ( m1_subset_1(X2,X0)
           => r2_hidden(X2,X1) )
       => X0 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_subset_1)).

fof(f141,plain,
    ( m1_subset_1(sK0,sK0)
    | ~ spl5_1 ),
    inference(unit_resulting_resolution,[],[f42,f42,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f42,plain,
    ( v1_xboole_0(sK0)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f41])).

fof(f41,plain,
    ( spl5_1
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f139,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK0)
    | ~ spl5_1 ),
    inference(unit_resulting_resolution,[],[f42,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f17,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f166,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ spl5_1 ),
    inference(unit_resulting_resolution,[],[f17,f161,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f161,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl5_1 ),
    inference(unit_resulting_resolution,[],[f146,f35])).

fof(f138,plain,(
    spl5_1 ),
    inference(avatar_contradiction_clause,[],[f133])).

fof(f133,plain,
    ( $false
    | spl5_1 ),
    inference(unit_resulting_resolution,[],[f101,f102,f81])).

fof(f81,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK1)
        | ~ r2_hidden(X0,sK0) )
    | spl5_1 ),
    inference(resolution,[],[f51,f16])).

fof(f51,plain,
    ( ! [X1] :
        ( m1_subset_1(X1,sK0)
        | ~ r2_hidden(X1,sK0) )
    | spl5_1 ),
    inference(resolution,[],[f43,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ r2_hidden(X1,X0)
      | m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f43,plain,
    ( ~ v1_xboole_0(sK0)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f41])).

fof(f102,plain,
    ( ~ r2_hidden(sK3(sK0,sK1),sK1)
    | spl5_1 ),
    inference(unit_resulting_resolution,[],[f96,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f96,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl5_1 ),
    inference(unit_resulting_resolution,[],[f18,f88,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f88,plain,
    ( ~ r2_xboole_0(sK0,sK1)
    | spl5_1 ),
    inference(unit_resulting_resolution,[],[f83,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( r2_xboole_0(X1,X0)
        & r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_xboole_1)).

fof(f83,plain,
    ( r1_tarski(sK1,sK0)
    | spl5_1 ),
    inference(unit_resulting_resolution,[],[f71,f36])).

fof(f71,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | spl5_1 ),
    inference(unit_resulting_resolution,[],[f17,f64,f32])).

fof(f64,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(sK0))
    | spl5_1 ),
    inference(unit_resulting_resolution,[],[f17,f61,f30])).

fof(f61,plain,
    ( ~ v1_xboole_0(sK1)
    | spl5_1 ),
    inference(unit_resulting_resolution,[],[f56,f35])).

fof(f56,plain,
    ( r2_hidden(sK4(sK0),sK1)
    | spl5_1 ),
    inference(unit_resulting_resolution,[],[f54,f16])).

fof(f54,plain,
    ( m1_subset_1(sK4(sK0),sK0)
    | spl5_1 ),
    inference(unit_resulting_resolution,[],[f43,f48,f31])).

fof(f48,plain,
    ( r2_hidden(sK4(sK0),sK0)
    | spl5_1 ),
    inference(unit_resulting_resolution,[],[f43,f34])).

fof(f34,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK4(X0),X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f18,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f12])).

fof(f101,plain,
    ( r2_hidden(sK3(sK0,sK1),sK0)
    | spl5_1 ),
    inference(unit_resulting_resolution,[],[f96,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:51:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.49  % (11817)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.49  % (11825)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.50  % (11824)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.50  % (11825)Refutation not found, incomplete strategy% (11825)------------------------------
% 0.20/0.50  % (11825)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (11840)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.51  % (11825)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (11825)Memory used [KB]: 10746
% 0.20/0.51  % (11825)Time elapsed: 0.089 s
% 0.20/0.51  % (11825)------------------------------
% 0.20/0.51  % (11825)------------------------------
% 0.20/0.51  % (11821)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (11832)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.51  % (11841)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.51  % (11821)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  fof(f228,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(avatar_sat_refutation,[],[f138,f227])).
% 0.20/0.51  fof(f227,plain,(
% 0.20/0.51    ~spl5_1),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f225])).
% 0.20/0.51  fof(f225,plain,(
% 0.20/0.51    $false | ~spl5_1),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f166,f17,f189,f32])).
% 0.20/0.51  fof(f32,plain,(
% 0.20/0.51    ( ! [X0,X1] : (v1_xboole_0(X0) | r2_hidden(X1,X0) | ~m1_subset_1(X1,X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f14])).
% 0.20/0.51  fof(f14,plain,(
% 0.20/0.51    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f8])).
% 0.20/0.51  fof(f8,axiom,(
% 0.20/0.51    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 0.20/0.51  fof(f189,plain,(
% 0.20/0.51    ~r2_hidden(sK1,k1_zfmisc_1(sK0)) | ~spl5_1),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f162,f36])).
% 0.20/0.51  fof(f36,plain,(
% 0.20/0.51    ( ! [X2,X0] : (~r2_hidden(X2,k1_zfmisc_1(X0)) | r1_tarski(X2,X0)) )),
% 0.20/0.51    inference(equality_resolution,[],[f20])).
% 0.20/0.51  fof(f20,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.20/0.51    inference(cnf_transformation,[],[f7])).
% 0.20/0.51  fof(f7,axiom,(
% 0.20/0.51    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.20/0.51  fof(f162,plain,(
% 0.20/0.51    ~r1_tarski(sK1,sK0) | ~spl5_1),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f139,f146,f26])).
% 0.20/0.51  % (11823)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.51  fof(f26,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f13])).
% 0.20/0.51  fof(f13,plain,(
% 0.20/0.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f2])).
% 0.20/0.51  fof(f2,axiom,(
% 0.20/0.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.51  fof(f146,plain,(
% 0.20/0.51    r2_hidden(sK0,sK1) | ~spl5_1),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f141,f16])).
% 0.20/0.51  fof(f16,plain,(
% 0.20/0.51    ( ! [X2] : (~m1_subset_1(X2,sK0) | r2_hidden(X2,sK1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f12])).
% 0.20/0.51  fof(f12,plain,(
% 0.20/0.51    ? [X0,X1] : (X0 != X1 & ! [X2] : (r2_hidden(X2,X1) | ~m1_subset_1(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.51    inference(flattening,[],[f11])).
% 0.20/0.51  fof(f11,plain,(
% 0.20/0.51    ? [X0,X1] : ((X0 != X1 & ! [X2] : (r2_hidden(X2,X1) | ~m1_subset_1(X2,X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f10])).
% 0.20/0.51  fof(f10,negated_conjecture,(
% 0.20/0.51    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (! [X2] : (m1_subset_1(X2,X0) => r2_hidden(X2,X1)) => X0 = X1))),
% 0.20/0.51    inference(negated_conjecture,[],[f9])).
% 0.20/0.51  fof(f9,conjecture,(
% 0.20/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (! [X2] : (m1_subset_1(X2,X0) => r2_hidden(X2,X1)) => X0 = X1))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_subset_1)).
% 0.20/0.51  fof(f141,plain,(
% 0.20/0.51    m1_subset_1(sK0,sK0) | ~spl5_1),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f42,f42,f29])).
% 0.20/0.51  fof(f29,plain,(
% 0.20/0.51    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~v1_xboole_0(X1) | ~v1_xboole_0(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f14])).
% 0.20/0.51  fof(f42,plain,(
% 0.20/0.51    v1_xboole_0(sK0) | ~spl5_1),
% 0.20/0.51    inference(avatar_component_clause,[],[f41])).
% 0.20/0.51  fof(f41,plain,(
% 0.20/0.51    spl5_1 <=> v1_xboole_0(sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.20/0.51  fof(f139,plain,(
% 0.20/0.51    ( ! [X0] : (~r2_hidden(X0,sK0)) ) | ~spl5_1),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f42,f35])).
% 0.20/0.51  fof(f35,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f1])).
% 0.20/0.51  fof(f1,axiom,(
% 0.20/0.51    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.20/0.51  fof(f17,plain,(
% 0.20/0.51    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.20/0.51    inference(cnf_transformation,[],[f12])).
% 0.20/0.51  fof(f166,plain,(
% 0.20/0.51    ~v1_xboole_0(k1_zfmisc_1(sK0)) | ~spl5_1),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f17,f161,f30])).
% 0.20/0.51  fof(f30,plain,(
% 0.20/0.51    ( ! [X0,X1] : (v1_xboole_0(X1) | ~v1_xboole_0(X0) | ~m1_subset_1(X1,X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f14])).
% 0.20/0.51  fof(f161,plain,(
% 0.20/0.51    ~v1_xboole_0(sK1) | ~spl5_1),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f146,f35])).
% 0.20/0.51  fof(f138,plain,(
% 0.20/0.51    spl5_1),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f133])).
% 0.20/0.51  fof(f133,plain,(
% 0.20/0.51    $false | spl5_1),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f101,f102,f81])).
% 0.20/0.51  fof(f81,plain,(
% 0.20/0.51    ( ! [X0] : (r2_hidden(X0,sK1) | ~r2_hidden(X0,sK0)) ) | spl5_1),
% 0.20/0.51    inference(resolution,[],[f51,f16])).
% 0.20/0.51  fof(f51,plain,(
% 0.20/0.51    ( ! [X1] : (m1_subset_1(X1,sK0) | ~r2_hidden(X1,sK0)) ) | spl5_1),
% 0.20/0.51    inference(resolution,[],[f43,f31])).
% 0.20/0.51  fof(f31,plain,(
% 0.20/0.51    ( ! [X0,X1] : (v1_xboole_0(X0) | ~r2_hidden(X1,X0) | m1_subset_1(X1,X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f14])).
% 0.20/0.51  fof(f43,plain,(
% 0.20/0.51    ~v1_xboole_0(sK0) | spl5_1),
% 0.20/0.51    inference(avatar_component_clause,[],[f41])).
% 0.20/0.51  fof(f102,plain,(
% 0.20/0.51    ~r2_hidden(sK3(sK0,sK1),sK1) | spl5_1),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f96,f28])).
% 0.20/0.51  fof(f28,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f13])).
% 0.20/0.51  fof(f96,plain,(
% 0.20/0.51    ~r1_tarski(sK0,sK1) | spl5_1),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f18,f88,f25])).
% 0.20/0.51  fof(f25,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f3])).
% 0.20/0.51  fof(f3,axiom,(
% 0.20/0.51    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).
% 0.20/0.51  fof(f88,plain,(
% 0.20/0.51    ~r2_xboole_0(sK0,sK1) | spl5_1),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f83,f33])).
% 0.20/0.51  fof(f33,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r2_xboole_0(X1,X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f15])).
% 0.20/0.51  fof(f15,plain,(
% 0.20/0.51    ! [X0,X1] : (~r2_xboole_0(X1,X0) | ~r1_tarski(X0,X1))),
% 0.20/0.51    inference(ennf_transformation,[],[f6])).
% 0.20/0.51  fof(f6,axiom,(
% 0.20/0.51    ! [X0,X1] : ~(r2_xboole_0(X1,X0) & r1_tarski(X0,X1))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_xboole_1)).
% 0.20/0.51  fof(f83,plain,(
% 0.20/0.51    r1_tarski(sK1,sK0) | spl5_1),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f71,f36])).
% 0.20/0.51  fof(f71,plain,(
% 0.20/0.51    r2_hidden(sK1,k1_zfmisc_1(sK0)) | spl5_1),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f17,f64,f32])).
% 0.20/0.51  fof(f64,plain,(
% 0.20/0.51    ~v1_xboole_0(k1_zfmisc_1(sK0)) | spl5_1),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f17,f61,f30])).
% 0.20/0.51  fof(f61,plain,(
% 0.20/0.51    ~v1_xboole_0(sK1) | spl5_1),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f56,f35])).
% 0.20/0.51  fof(f56,plain,(
% 0.20/0.51    r2_hidden(sK4(sK0),sK1) | spl5_1),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f54,f16])).
% 0.20/0.51  fof(f54,plain,(
% 0.20/0.51    m1_subset_1(sK4(sK0),sK0) | spl5_1),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f43,f48,f31])).
% 0.20/0.51  fof(f48,plain,(
% 0.20/0.51    r2_hidden(sK4(sK0),sK0) | spl5_1),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f43,f34])).
% 0.20/0.51  fof(f34,plain,(
% 0.20/0.51    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK4(X0),X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f1])).
% 0.20/0.51  fof(f18,plain,(
% 0.20/0.51    sK0 != sK1),
% 0.20/0.51    inference(cnf_transformation,[],[f12])).
% 0.20/0.51  fof(f101,plain,(
% 0.20/0.51    r2_hidden(sK3(sK0,sK1),sK0) | spl5_1),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f96,f27])).
% 0.20/0.51  fof(f27,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f13])).
% 0.20/0.51  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (11821)------------------------------
% 0.20/0.51  % (11821)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (11821)Termination reason: Refutation
% 0.20/0.51  
% 0.20/0.51  % (11821)Memory used [KB]: 6268
% 0.20/0.51  % (11821)Time elapsed: 0.102 s
% 0.20/0.51  % (11821)------------------------------
% 0.20/0.51  % (11821)------------------------------
% 0.20/0.51  % (11816)Success in time 0.157 s
%------------------------------------------------------------------------------
