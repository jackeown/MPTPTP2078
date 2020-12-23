%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:20 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 111 expanded)
%              Number of leaves         :   13 (  32 expanded)
%              Depth                    :   11
%              Number of atoms          :  195 ( 390 expanded)
%              Number of equality atoms :   14 (  28 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f145,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f52,f66,f98,f110,f144])).

fof(f144,plain,(
    spl4_4 ),
    inference(avatar_contradiction_clause,[],[f142])).

fof(f142,plain,
    ( $false
    | spl4_4 ),
    inference(resolution,[],[f133,f64])).

fof(f64,plain,
    ( ~ r1_tarski(sK1,sK0)
    | spl4_4 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl4_4
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f133,plain,
    ( r1_tarski(sK1,sK0)
    | spl4_4 ),
    inference(resolution,[],[f131,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f23,f24])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f131,plain,
    ( ~ r2_hidden(sK3(sK1,sK0),sK1)
    | spl4_4 ),
    inference(resolution,[],[f106,f68])).

fof(f68,plain,
    ( ~ r2_hidden(sK3(sK1,sK0),sK0)
    | spl4_4 ),
    inference(resolution,[],[f64,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f106,plain,(
    ! [X0] :
      ( r2_hidden(X0,sK0)
      | ~ r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f35,f26])).

fof(f26,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( sK0 != sK1
    & ! [X2] :
        ( r2_hidden(X2,sK1)
        | ~ m1_subset_1(X2,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f13])).

fof(f13,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ m1_subset_1(X2,X0) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( sK0 != sK1
      & ! [X2] :
          ( r2_hidden(X2,sK1)
          | ~ m1_subset_1(X2,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ m1_subset_1(X2,X0) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ m1_subset_1(X2,X0) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ( ! [X2] :
              ( m1_subset_1(X2,X0)
             => r2_hidden(X2,X1) )
         => X0 = X1 ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( ! [X2] :
            ( m1_subset_1(X2,X0)
           => r2_hidden(X2,X1) )
       => X0 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_subset_1)).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f110,plain,
    ( ~ spl4_1
    | spl4_3 ),
    inference(avatar_contradiction_clause,[],[f108])).

fof(f108,plain,
    ( $false
    | ~ spl4_1
    | spl4_3 ),
    inference(resolution,[],[f105,f60])).

fof(f60,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl4_3 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl4_3
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f105,plain,
    ( ! [X3] : r1_tarski(sK0,X3)
    | ~ spl4_1 ),
    inference(resolution,[],[f101,f40])).

fof(f101,plain,
    ( ! [X2] : ~ r2_hidden(X2,sK0)
    | ~ spl4_1 ),
    inference(resolution,[],[f48,f29])).

fof(f29,plain,(
    ! [X2,X0] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK2(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f16,f17])).

fof(f17,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f48,plain,
    ( v1_xboole_0(sK0)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f46])).

fof(f46,plain,
    ( spl4_1
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f98,plain,
    ( ~ spl4_2
    | spl4_3 ),
    inference(avatar_contradiction_clause,[],[f96])).

fof(f96,plain,
    ( $false
    | ~ spl4_2
    | spl4_3 ),
    inference(resolution,[],[f88,f60])).

fof(f88,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl4_2
    | spl4_3 ),
    inference(resolution,[],[f69,f40])).

fof(f69,plain,
    ( ~ r2_hidden(sK3(sK0,sK1),sK0)
    | ~ spl4_2
    | spl4_3 ),
    inference(resolution,[],[f67,f51])).

fof(f51,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK1)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f50])).

fof(f50,plain,
    ( spl4_2
  <=> ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | r2_hidden(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

% (7213)Refutation not found, incomplete strategy% (7213)------------------------------
% (7213)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f67,plain,
    ( ~ r2_hidden(sK3(sK0,sK1),sK1)
    | spl4_3 ),
    inference(resolution,[],[f60,f41])).

fof(f66,plain,
    ( ~ spl4_4
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f54,f58,f62])).

% (7213)Termination reason: Refutation not found, incomplete strategy
fof(f54,plain,
    ( ~ r1_tarski(sK0,sK1)
    | ~ r1_tarski(sK1,sK0) ),
    inference(extensionality_resolution,[],[f38,f28])).

fof(f28,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f14])).

% (7213)Memory used [KB]: 10746
% (7213)Time elapsed: 0.109 s
% (7213)------------------------------
% (7213)------------------------------
fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f52,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f44,f50,f46])).

fof(f44,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | v1_xboole_0(sK0)
      | r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f32,f27])).

fof(f27,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,sK0)
      | r2_hidden(X2,sK1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f32,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:55:24 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.50  % (7220)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.50  % (7213)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.51  % (7234)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.51  % (7204)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.51  % (7205)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.52  % (7217)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.52  % (7217)Refutation found. Thanks to Tanya!
% 0.20/0.52  % SZS status Theorem for theBenchmark
% 0.20/0.52  % SZS output start Proof for theBenchmark
% 0.20/0.52  fof(f145,plain,(
% 0.20/0.52    $false),
% 0.20/0.52    inference(avatar_sat_refutation,[],[f52,f66,f98,f110,f144])).
% 0.20/0.52  fof(f144,plain,(
% 0.20/0.52    spl4_4),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f142])).
% 0.20/0.52  fof(f142,plain,(
% 0.20/0.52    $false | spl4_4),
% 0.20/0.52    inference(resolution,[],[f133,f64])).
% 0.20/0.52  fof(f64,plain,(
% 0.20/0.52    ~r1_tarski(sK1,sK0) | spl4_4),
% 0.20/0.52    inference(avatar_component_clause,[],[f62])).
% 0.20/0.52  fof(f62,plain,(
% 0.20/0.52    spl4_4 <=> r1_tarski(sK1,sK0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.20/0.52  fof(f133,plain,(
% 0.20/0.52    r1_tarski(sK1,sK0) | spl4_4),
% 0.20/0.52    inference(resolution,[],[f131,f40])).
% 0.20/0.52  fof(f40,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f25])).
% 0.20/0.52  fof(f25,plain,(
% 0.20/0.52    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f23,f24])).
% 0.20/0.52  fof(f24,plain,(
% 0.20/0.52    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f23,plain,(
% 0.20/0.52    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.52    inference(rectify,[],[f22])).
% 0.20/0.52  fof(f22,plain,(
% 0.20/0.52    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.52    inference(nnf_transformation,[],[f12])).
% 0.20/0.52  fof(f12,plain,(
% 0.20/0.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f2])).
% 0.20/0.52  fof(f2,axiom,(
% 0.20/0.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.52  fof(f131,plain,(
% 0.20/0.52    ~r2_hidden(sK3(sK1,sK0),sK1) | spl4_4),
% 0.20/0.52    inference(resolution,[],[f106,f68])).
% 0.20/0.52  fof(f68,plain,(
% 0.20/0.52    ~r2_hidden(sK3(sK1,sK0),sK0) | spl4_4),
% 0.20/0.52    inference(resolution,[],[f64,f41])).
% 0.20/0.52  fof(f41,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK3(X0,X1),X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f25])).
% 0.20/0.52  fof(f106,plain,(
% 0.20/0.52    ( ! [X0] : (r2_hidden(X0,sK0) | ~r2_hidden(X0,sK1)) )),
% 0.20/0.52    inference(resolution,[],[f35,f26])).
% 0.20/0.52  fof(f26,plain,(
% 0.20/0.52    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.20/0.52    inference(cnf_transformation,[],[f14])).
% 0.20/0.52  fof(f14,plain,(
% 0.20/0.52    sK0 != sK1 & ! [X2] : (r2_hidden(X2,sK1) | ~m1_subset_1(X2,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f13])).
% 0.20/0.52  fof(f13,plain,(
% 0.20/0.52    ? [X0,X1] : (X0 != X1 & ! [X2] : (r2_hidden(X2,X1) | ~m1_subset_1(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (sK0 != sK1 & ! [X2] : (r2_hidden(X2,sK1) | ~m1_subset_1(X2,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f9,plain,(
% 0.20/0.52    ? [X0,X1] : (X0 != X1 & ! [X2] : (r2_hidden(X2,X1) | ~m1_subset_1(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.52    inference(flattening,[],[f8])).
% 0.20/0.52  fof(f8,plain,(
% 0.20/0.52    ? [X0,X1] : ((X0 != X1 & ! [X2] : (r2_hidden(X2,X1) | ~m1_subset_1(X2,X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f7])).
% 0.20/0.52  fof(f7,negated_conjecture,(
% 0.20/0.52    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (! [X2] : (m1_subset_1(X2,X0) => r2_hidden(X2,X1)) => X0 = X1))),
% 0.20/0.52    inference(negated_conjecture,[],[f6])).
% 0.20/0.52  fof(f6,conjecture,(
% 0.20/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (! [X2] : (m1_subset_1(X2,X0) => r2_hidden(X2,X1)) => X0 = X1))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_subset_1)).
% 0.20/0.52  fof(f35,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f11])).
% 0.20/0.52  fof(f11,plain,(
% 0.20/0.52    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f5])).
% 0.20/0.52  fof(f5,axiom,(
% 0.20/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 0.20/0.52  fof(f110,plain,(
% 0.20/0.52    ~spl4_1 | spl4_3),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f108])).
% 0.20/0.52  fof(f108,plain,(
% 0.20/0.52    $false | (~spl4_1 | spl4_3)),
% 0.20/0.52    inference(resolution,[],[f105,f60])).
% 0.20/0.52  fof(f60,plain,(
% 0.20/0.52    ~r1_tarski(sK0,sK1) | spl4_3),
% 0.20/0.52    inference(avatar_component_clause,[],[f58])).
% 0.20/0.52  fof(f58,plain,(
% 0.20/0.52    spl4_3 <=> r1_tarski(sK0,sK1)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.52  fof(f105,plain,(
% 0.20/0.52    ( ! [X3] : (r1_tarski(sK0,X3)) ) | ~spl4_1),
% 0.20/0.52    inference(resolution,[],[f101,f40])).
% 0.20/0.52  fof(f101,plain,(
% 0.20/0.52    ( ! [X2] : (~r2_hidden(X2,sK0)) ) | ~spl4_1),
% 0.20/0.52    inference(resolution,[],[f48,f29])).
% 0.20/0.52  fof(f29,plain,(
% 0.20/0.52    ( ! [X2,X0] : (~v1_xboole_0(X0) | ~r2_hidden(X2,X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f18])).
% 0.20/0.52  fof(f18,plain,(
% 0.20/0.52    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK2(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f16,f17])).
% 0.20/0.52  fof(f17,plain,(
% 0.20/0.52    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f16,plain,(
% 0.20/0.52    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.52    inference(rectify,[],[f15])).
% 0.20/0.52  fof(f15,plain,(
% 0.20/0.52    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.52    inference(nnf_transformation,[],[f1])).
% 0.20/0.52  fof(f1,axiom,(
% 0.20/0.52    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.20/0.52  fof(f48,plain,(
% 0.20/0.52    v1_xboole_0(sK0) | ~spl4_1),
% 0.20/0.52    inference(avatar_component_clause,[],[f46])).
% 0.20/0.52  fof(f46,plain,(
% 0.20/0.52    spl4_1 <=> v1_xboole_0(sK0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.52  fof(f98,plain,(
% 0.20/0.52    ~spl4_2 | spl4_3),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f96])).
% 0.20/0.52  fof(f96,plain,(
% 0.20/0.52    $false | (~spl4_2 | spl4_3)),
% 0.20/0.52    inference(resolution,[],[f88,f60])).
% 0.20/0.52  fof(f88,plain,(
% 0.20/0.52    r1_tarski(sK0,sK1) | (~spl4_2 | spl4_3)),
% 0.20/0.52    inference(resolution,[],[f69,f40])).
% 0.20/0.52  fof(f69,plain,(
% 0.20/0.52    ~r2_hidden(sK3(sK0,sK1),sK0) | (~spl4_2 | spl4_3)),
% 0.20/0.52    inference(resolution,[],[f67,f51])).
% 0.20/0.52  fof(f51,plain,(
% 0.20/0.52    ( ! [X0] : (r2_hidden(X0,sK1) | ~r2_hidden(X0,sK0)) ) | ~spl4_2),
% 0.20/0.52    inference(avatar_component_clause,[],[f50])).
% 0.20/0.52  fof(f50,plain,(
% 0.20/0.52    spl4_2 <=> ! [X0] : (~r2_hidden(X0,sK0) | r2_hidden(X0,sK1))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.52  % (7213)Refutation not found, incomplete strategy% (7213)------------------------------
% 0.20/0.52  % (7213)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  fof(f67,plain,(
% 0.20/0.52    ~r2_hidden(sK3(sK0,sK1),sK1) | spl4_3),
% 0.20/0.52    inference(resolution,[],[f60,f41])).
% 0.20/0.52  fof(f66,plain,(
% 0.20/0.52    ~spl4_4 | ~spl4_3),
% 0.20/0.52    inference(avatar_split_clause,[],[f54,f58,f62])).
% 0.20/0.52  % (7213)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  fof(f54,plain,(
% 0.20/0.52    ~r1_tarski(sK0,sK1) | ~r1_tarski(sK1,sK0)),
% 0.20/0.52    inference(extensionality_resolution,[],[f38,f28])).
% 0.20/0.52  
% 0.20/0.52  fof(f28,plain,(
% 0.20/0.52    sK0 != sK1),
% 0.20/0.52    inference(cnf_transformation,[],[f14])).
% 0.20/0.52  % (7213)Memory used [KB]: 10746
% 0.20/0.52  % (7213)Time elapsed: 0.109 s
% 0.20/0.52  % (7213)------------------------------
% 0.20/0.52  % (7213)------------------------------
% 0.20/0.52  fof(f38,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f21])).
% 0.20/0.52  fof(f21,plain,(
% 0.20/0.52    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.52    inference(flattening,[],[f20])).
% 0.20/0.52  fof(f20,plain,(
% 0.20/0.52    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.52    inference(nnf_transformation,[],[f3])).
% 0.20/0.52  fof(f3,axiom,(
% 0.20/0.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.52  fof(f52,plain,(
% 0.20/0.52    spl4_1 | spl4_2),
% 0.20/0.52    inference(avatar_split_clause,[],[f44,f50,f46])).
% 0.20/0.52  fof(f44,plain,(
% 0.20/0.52    ( ! [X0] : (~r2_hidden(X0,sK0) | v1_xboole_0(sK0) | r2_hidden(X0,sK1)) )),
% 0.20/0.52    inference(resolution,[],[f32,f27])).
% 0.20/0.52  fof(f27,plain,(
% 0.20/0.52    ( ! [X2] : (~m1_subset_1(X2,sK0) | r2_hidden(X2,sK1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f14])).
% 0.20/0.52  fof(f32,plain,(
% 0.20/0.52    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f19])).
% 0.20/0.52  fof(f19,plain,(
% 0.20/0.52    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 0.20/0.52    inference(nnf_transformation,[],[f10])).
% 0.20/0.52  fof(f10,plain,(
% 0.20/0.52    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f4])).
% 0.20/0.52  fof(f4,axiom,(
% 0.20/0.52    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 0.20/0.52  % SZS output end Proof for theBenchmark
% 0.20/0.52  % (7217)------------------------------
% 0.20/0.52  % (7217)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (7217)Termination reason: Refutation
% 0.20/0.52  
% 0.20/0.52  % (7217)Memory used [KB]: 6268
% 0.20/0.52  % (7217)Time elapsed: 0.125 s
% 0.20/0.52  % (7217)------------------------------
% 0.20/0.52  % (7217)------------------------------
% 0.20/0.52  % (7203)Success in time 0.167 s
%------------------------------------------------------------------------------
