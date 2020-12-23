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
% DateTime   : Thu Dec  3 12:45:23 EST 2020

% Result     : Theorem 1.46s
% Output     : Refutation 1.67s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 158 expanded)
%              Number of leaves         :   12 (  45 expanded)
%              Depth                    :   14
%              Number of atoms          :  208 ( 591 expanded)
%              Number of equality atoms :   20 (  67 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f173,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f71,f94,f128,f151,f172])).

fof(f172,plain,
    ( ~ spl4_3
    | ~ spl4_11 ),
    inference(avatar_contradiction_clause,[],[f171])).

fof(f171,plain,
    ( $false
    | ~ spl4_3
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f170,f66])).

fof(f66,plain,
    ( r2_hidden(sK3(sK0,sK1),sK1)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl4_3
  <=> r2_hidden(sK3(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f170,plain,
    ( ~ r2_hidden(sK3(sK0,sK1),sK1)
    | ~ spl4_11 ),
    inference(resolution,[],[f127,f22])).

fof(f22,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( sK0 != sK1
    & ! [X2] :
        ( r2_hidden(X2,sK1)
        | ~ m1_subset_1(X2,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f12])).

fof(f12,plain,
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

fof(f8,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ m1_subset_1(X2,X0) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ m1_subset_1(X2,X0) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ( ! [X2] :
              ( m1_subset_1(X2,X0)
             => r2_hidden(X2,X1) )
         => X0 = X1 ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( ! [X2] :
            ( m1_subset_1(X2,X0)
           => r2_hidden(X2,X1) )
       => X0 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_subset_1)).

fof(f127,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(sK0))
        | ~ r2_hidden(sK3(sK0,sK1),X2) )
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f126])).

fof(f126,plain,
    ( spl4_11
  <=> ! [X2] :
        ( ~ r2_hidden(sK3(sK0,sK1),X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f151,plain,
    ( ~ spl4_3
    | ~ spl4_9 ),
    inference(avatar_contradiction_clause,[],[f149])).

fof(f149,plain,
    ( $false
    | ~ spl4_3
    | ~ spl4_9 ),
    inference(resolution,[],[f144,f66])).

fof(f144,plain,
    ( ! [X2] : ~ r2_hidden(X2,sK1)
    | ~ spl4_9 ),
    inference(resolution,[],[f140,f25])).

fof(f25,plain,(
    ! [X2,X0] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK2(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f15,f16])).

fof(f16,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f14])).

fof(f14,plain,(
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

fof(f140,plain,
    ( v1_xboole_0(sK1)
    | ~ spl4_9 ),
    inference(resolution,[],[f130,f22])).

fof(f130,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(sK0))
        | v1_xboole_0(X1) )
    | ~ spl4_9 ),
    inference(resolution,[],[f119,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f119,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl4_9
  <=> v1_xboole_0(k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f128,plain,
    ( spl4_9
    | spl4_11
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f114,f69,f126,f117])).

fof(f69,plain,
    ( spl4_4
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k1_zfmisc_1(sK0))
        | ~ r2_hidden(sK3(sK0,sK1),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f114,plain,
    ( ! [X2] :
        ( ~ r2_hidden(sK3(sK0,sK1),X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(sK0))
        | v1_xboole_0(k1_zfmisc_1(sK0)) )
    | ~ spl4_4 ),
    inference(resolution,[],[f70,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f70,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_zfmisc_1(sK0))
        | ~ r2_hidden(sK3(sK0,sK1),X0) )
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f69])).

fof(f94,plain,(
    spl4_3 ),
    inference(avatar_contradiction_clause,[],[f93])).

fof(f93,plain,
    ( $false
    | spl4_3 ),
    inference(subsumption_resolution,[],[f76,f73])).

fof(f73,plain,
    ( ~ r2_hidden(sK3(sK0,sK1),sK0)
    | spl4_3 ),
    inference(resolution,[],[f67,f35])).

fof(f35,plain,(
    ! [X0] :
      ( r2_hidden(X0,sK1)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f34,f23])).

fof(f23,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,sK0)
      | r2_hidden(X2,sK1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(subsumption_resolution,[],[f28,f25])).

% (24307)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f67,plain,
    ( ~ r2_hidden(sK3(sK0,sK1),sK1)
    | spl4_3 ),
    inference(avatar_component_clause,[],[f65])).

fof(f76,plain,
    ( r2_hidden(sK3(sK0,sK1),sK0)
    | spl4_3 ),
    inference(subsumption_resolution,[],[f72,f24])).

fof(f24,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f13])).

fof(f72,plain,
    ( sK0 = sK1
    | r2_hidden(sK3(sK0,sK1),sK0)
    | spl4_3 ),
    inference(resolution,[],[f67,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X1)
      | X0 = X1
      | r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK3(X0,X1),X1)
          | ~ r2_hidden(sK3(X0,X1),X0) )
        & ( r2_hidden(sK3(X0,X1),X1)
          | r2_hidden(sK3(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f19,f20])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) )
     => ( ( ~ r2_hidden(sK3(X0,X1),X1)
          | ~ r2_hidden(sK3(X0,X1),X0) )
        & ( r2_hidden(sK3(X0,X1),X1)
          | r2_hidden(sK3(X0,X1),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

fof(f71,plain,
    ( ~ spl4_3
    | spl4_4 ),
    inference(avatar_split_clause,[],[f63,f69,f65])).

fof(f63,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_zfmisc_1(sK0))
      | ~ r2_hidden(sK3(sK0,sK1),sK1)
      | ~ r2_hidden(sK3(sK0,sK1),X0) ) ),
    inference(subsumption_resolution,[],[f61,f24])).

fof(f61,plain,(
    ! [X0] :
      ( sK0 = sK1
      | ~ r2_hidden(X0,k1_zfmisc_1(sK0))
      | ~ r2_hidden(sK3(sK0,sK1),sK1)
      | ~ r2_hidden(sK3(sK0,sK1),X0) ) ),
    inference(resolution,[],[f56,f22])).

fof(f56,plain,(
    ! [X2,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(X1))
      | sK1 = X1
      | ~ r2_hidden(X2,k1_zfmisc_1(sK0))
      | ~ r2_hidden(sK3(X1,sK1),X3)
      | ~ r2_hidden(sK3(X1,sK1),X2) ) ),
    inference(resolution,[],[f54,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f54,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(sK3(X1,sK1),X1)
      | ~ r2_hidden(sK3(X1,sK1),X2)
      | sK1 = X1
      | ~ r2_hidden(X2,k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f42,f34])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(sK0))
      | sK1 = X0
      | ~ r2_hidden(sK3(X0,sK1),X1)
      | ~ r2_hidden(sK3(X0,sK1),X0) ) ),
    inference(resolution,[],[f40,f31])).

fof(f40,plain,(
    ! [X7] :
      ( ~ r2_hidden(sK3(X7,sK1),sK0)
      | ~ r2_hidden(sK3(X7,sK1),X7)
      | sK1 = X7 ) ),
    inference(resolution,[],[f33,f35])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | X0 = X1
      | ~ r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:24:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.54  % (24282)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.46/0.56  % (24282)Refutation not found, incomplete strategy% (24282)------------------------------
% 1.46/0.56  % (24282)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.56  % (24282)Termination reason: Refutation not found, incomplete strategy
% 1.46/0.56  
% 1.46/0.56  % (24282)Memory used [KB]: 10618
% 1.46/0.56  % (24282)Time elapsed: 0.138 s
% 1.46/0.56  % (24282)------------------------------
% 1.46/0.56  % (24282)------------------------------
% 1.46/0.56  % (24283)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.46/0.56  % (24303)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.46/0.56  % (24283)Refutation found. Thanks to Tanya!
% 1.46/0.56  % SZS status Theorem for theBenchmark
% 1.67/0.57  % (24299)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.67/0.57  % (24287)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.67/0.57  % (24290)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.67/0.57  % (24298)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.67/0.58  % (24291)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.67/0.58  % SZS output start Proof for theBenchmark
% 1.67/0.58  fof(f173,plain,(
% 1.67/0.58    $false),
% 1.67/0.58    inference(avatar_sat_refutation,[],[f71,f94,f128,f151,f172])).
% 1.67/0.58  fof(f172,plain,(
% 1.67/0.58    ~spl4_3 | ~spl4_11),
% 1.67/0.58    inference(avatar_contradiction_clause,[],[f171])).
% 1.67/0.58  fof(f171,plain,(
% 1.67/0.58    $false | (~spl4_3 | ~spl4_11)),
% 1.67/0.58    inference(subsumption_resolution,[],[f170,f66])).
% 1.67/0.58  fof(f66,plain,(
% 1.67/0.58    r2_hidden(sK3(sK0,sK1),sK1) | ~spl4_3),
% 1.67/0.58    inference(avatar_component_clause,[],[f65])).
% 1.67/0.58  fof(f65,plain,(
% 1.67/0.58    spl4_3 <=> r2_hidden(sK3(sK0,sK1),sK1)),
% 1.67/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.67/0.58  fof(f170,plain,(
% 1.67/0.58    ~r2_hidden(sK3(sK0,sK1),sK1) | ~spl4_11),
% 1.67/0.58    inference(resolution,[],[f127,f22])).
% 1.67/0.58  fof(f22,plain,(
% 1.67/0.58    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.67/0.58    inference(cnf_transformation,[],[f13])).
% 1.67/0.58  fof(f13,plain,(
% 1.67/0.58    sK0 != sK1 & ! [X2] : (r2_hidden(X2,sK1) | ~m1_subset_1(X2,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.67/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f12])).
% 1.67/0.58  fof(f12,plain,(
% 1.67/0.58    ? [X0,X1] : (X0 != X1 & ! [X2] : (r2_hidden(X2,X1) | ~m1_subset_1(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (sK0 != sK1 & ! [X2] : (r2_hidden(X2,sK1) | ~m1_subset_1(X2,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 1.67/0.58    introduced(choice_axiom,[])).
% 1.67/0.58  fof(f8,plain,(
% 1.67/0.58    ? [X0,X1] : (X0 != X1 & ! [X2] : (r2_hidden(X2,X1) | ~m1_subset_1(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.67/0.58    inference(flattening,[],[f7])).
% 1.67/0.58  fof(f7,plain,(
% 1.67/0.58    ? [X0,X1] : ((X0 != X1 & ! [X2] : (r2_hidden(X2,X1) | ~m1_subset_1(X2,X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.67/0.58    inference(ennf_transformation,[],[f6])).
% 1.67/0.58  fof(f6,negated_conjecture,(
% 1.67/0.58    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (! [X2] : (m1_subset_1(X2,X0) => r2_hidden(X2,X1)) => X0 = X1))),
% 1.67/0.58    inference(negated_conjecture,[],[f5])).
% 1.67/0.58  fof(f5,conjecture,(
% 1.67/0.58    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (! [X2] : (m1_subset_1(X2,X0) => r2_hidden(X2,X1)) => X0 = X1))),
% 1.67/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_subset_1)).
% 1.67/0.58  fof(f127,plain,(
% 1.67/0.58    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(sK0)) | ~r2_hidden(sK3(sK0,sK1),X2)) ) | ~spl4_11),
% 1.67/0.58    inference(avatar_component_clause,[],[f126])).
% 1.67/0.58  fof(f126,plain,(
% 1.67/0.58    spl4_11 <=> ! [X2] : (~r2_hidden(sK3(sK0,sK1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(sK0)))),
% 1.67/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 1.67/0.58  fof(f151,plain,(
% 1.67/0.58    ~spl4_3 | ~spl4_9),
% 1.67/0.58    inference(avatar_contradiction_clause,[],[f149])).
% 1.67/0.58  fof(f149,plain,(
% 1.67/0.58    $false | (~spl4_3 | ~spl4_9)),
% 1.67/0.58    inference(resolution,[],[f144,f66])).
% 1.67/0.58  fof(f144,plain,(
% 1.67/0.58    ( ! [X2] : (~r2_hidden(X2,sK1)) ) | ~spl4_9),
% 1.67/0.58    inference(resolution,[],[f140,f25])).
% 1.67/0.58  fof(f25,plain,(
% 1.67/0.58    ( ! [X2,X0] : (~v1_xboole_0(X0) | ~r2_hidden(X2,X0)) )),
% 1.67/0.58    inference(cnf_transformation,[],[f17])).
% 1.67/0.58  fof(f17,plain,(
% 1.67/0.58    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK2(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.67/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f15,f16])).
% 1.67/0.58  fof(f16,plain,(
% 1.67/0.58    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 1.67/0.58    introduced(choice_axiom,[])).
% 1.67/0.58  fof(f15,plain,(
% 1.67/0.58    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.67/0.58    inference(rectify,[],[f14])).
% 1.67/0.58  fof(f14,plain,(
% 1.67/0.58    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.67/0.58    inference(nnf_transformation,[],[f1])).
% 1.67/0.58  fof(f1,axiom,(
% 1.67/0.58    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.67/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.67/0.58  fof(f140,plain,(
% 1.67/0.58    v1_xboole_0(sK1) | ~spl4_9),
% 1.67/0.58    inference(resolution,[],[f130,f22])).
% 1.67/0.58  fof(f130,plain,(
% 1.67/0.58    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(sK0)) | v1_xboole_0(X1)) ) | ~spl4_9),
% 1.67/0.58    inference(resolution,[],[f119,f29])).
% 1.67/0.58  fof(f29,plain,(
% 1.67/0.58    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X1)) )),
% 1.67/0.58    inference(cnf_transformation,[],[f18])).
% 1.67/0.58  fof(f18,plain,(
% 1.67/0.58    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 1.67/0.58    inference(nnf_transformation,[],[f9])).
% 1.67/0.58  fof(f9,plain,(
% 1.67/0.58    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.67/0.58    inference(ennf_transformation,[],[f3])).
% 1.67/0.58  fof(f3,axiom,(
% 1.67/0.58    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.67/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 1.67/0.58  fof(f119,plain,(
% 1.67/0.58    v1_xboole_0(k1_zfmisc_1(sK0)) | ~spl4_9),
% 1.67/0.58    inference(avatar_component_clause,[],[f117])).
% 1.67/0.58  fof(f117,plain,(
% 1.67/0.58    spl4_9 <=> v1_xboole_0(k1_zfmisc_1(sK0))),
% 1.67/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 1.67/0.58  fof(f128,plain,(
% 1.67/0.58    spl4_9 | spl4_11 | ~spl4_4),
% 1.67/0.58    inference(avatar_split_clause,[],[f114,f69,f126,f117])).
% 1.67/0.58  fof(f69,plain,(
% 1.67/0.58    spl4_4 <=> ! [X0] : (~r2_hidden(X0,k1_zfmisc_1(sK0)) | ~r2_hidden(sK3(sK0,sK1),X0))),
% 1.67/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.67/0.58  fof(f114,plain,(
% 1.67/0.58    ( ! [X2] : (~r2_hidden(sK3(sK0,sK1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))) ) | ~spl4_4),
% 1.67/0.58    inference(resolution,[],[f70,f27])).
% 1.67/0.58  fof(f27,plain,(
% 1.67/0.58    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.67/0.58    inference(cnf_transformation,[],[f18])).
% 1.67/0.58  fof(f70,plain,(
% 1.67/0.58    ( ! [X0] : (~r2_hidden(X0,k1_zfmisc_1(sK0)) | ~r2_hidden(sK3(sK0,sK1),X0)) ) | ~spl4_4),
% 1.67/0.58    inference(avatar_component_clause,[],[f69])).
% 1.67/0.58  fof(f94,plain,(
% 1.67/0.58    spl4_3),
% 1.67/0.58    inference(avatar_contradiction_clause,[],[f93])).
% 1.67/0.58  fof(f93,plain,(
% 1.67/0.58    $false | spl4_3),
% 1.67/0.58    inference(subsumption_resolution,[],[f76,f73])).
% 1.67/0.58  fof(f73,plain,(
% 1.67/0.58    ~r2_hidden(sK3(sK0,sK1),sK0) | spl4_3),
% 1.67/0.58    inference(resolution,[],[f67,f35])).
% 1.67/0.58  fof(f35,plain,(
% 1.67/0.58    ( ! [X0] : (r2_hidden(X0,sK1) | ~r2_hidden(X0,sK0)) )),
% 1.67/0.58    inference(resolution,[],[f34,f23])).
% 1.67/0.58  fof(f23,plain,(
% 1.67/0.58    ( ! [X2] : (~m1_subset_1(X2,sK0) | r2_hidden(X2,sK1)) )),
% 1.67/0.58    inference(cnf_transformation,[],[f13])).
% 1.67/0.58  fof(f34,plain,(
% 1.67/0.58    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) )),
% 1.67/0.58    inference(subsumption_resolution,[],[f28,f25])).
% 1.67/0.58  % (24307)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.67/0.58  fof(f28,plain,(
% 1.67/0.58    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 1.67/0.58    inference(cnf_transformation,[],[f18])).
% 1.67/0.58  fof(f67,plain,(
% 1.67/0.58    ~r2_hidden(sK3(sK0,sK1),sK1) | spl4_3),
% 1.67/0.58    inference(avatar_component_clause,[],[f65])).
% 1.67/0.58  fof(f76,plain,(
% 1.67/0.58    r2_hidden(sK3(sK0,sK1),sK0) | spl4_3),
% 1.67/0.58    inference(subsumption_resolution,[],[f72,f24])).
% 1.67/0.58  fof(f24,plain,(
% 1.67/0.58    sK0 != sK1),
% 1.67/0.58    inference(cnf_transformation,[],[f13])).
% 1.67/0.58  fof(f72,plain,(
% 1.67/0.58    sK0 = sK1 | r2_hidden(sK3(sK0,sK1),sK0) | spl4_3),
% 1.67/0.58    inference(resolution,[],[f67,f32])).
% 1.67/0.58  fof(f32,plain,(
% 1.67/0.58    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X1) | X0 = X1 | r2_hidden(sK3(X0,X1),X0)) )),
% 1.67/0.58    inference(cnf_transformation,[],[f21])).
% 1.67/0.58  fof(f21,plain,(
% 1.67/0.58    ! [X0,X1] : (X0 = X1 | ((~r2_hidden(sK3(X0,X1),X1) | ~r2_hidden(sK3(X0,X1),X0)) & (r2_hidden(sK3(X0,X1),X1) | r2_hidden(sK3(X0,X1),X0))))),
% 1.67/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f19,f20])).
% 1.67/0.58  fof(f20,plain,(
% 1.67/0.58    ! [X1,X0] : (? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))) => ((~r2_hidden(sK3(X0,X1),X1) | ~r2_hidden(sK3(X0,X1),X0)) & (r2_hidden(sK3(X0,X1),X1) | r2_hidden(sK3(X0,X1),X0))))),
% 1.67/0.58    introduced(choice_axiom,[])).
% 1.67/0.58  fof(f19,plain,(
% 1.67/0.58    ! [X0,X1] : (X0 = X1 | ? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))))),
% 1.67/0.58    inference(nnf_transformation,[],[f11])).
% 1.67/0.58  fof(f11,plain,(
% 1.67/0.58    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 1.67/0.58    inference(ennf_transformation,[],[f2])).
% 1.67/0.58  fof(f2,axiom,(
% 1.67/0.58    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 1.67/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).
% 1.67/0.58  fof(f71,plain,(
% 1.67/0.58    ~spl4_3 | spl4_4),
% 1.67/0.58    inference(avatar_split_clause,[],[f63,f69,f65])).
% 1.67/0.58  fof(f63,plain,(
% 1.67/0.58    ( ! [X0] : (~r2_hidden(X0,k1_zfmisc_1(sK0)) | ~r2_hidden(sK3(sK0,sK1),sK1) | ~r2_hidden(sK3(sK0,sK1),X0)) )),
% 1.67/0.58    inference(subsumption_resolution,[],[f61,f24])).
% 1.67/0.58  fof(f61,plain,(
% 1.67/0.58    ( ! [X0] : (sK0 = sK1 | ~r2_hidden(X0,k1_zfmisc_1(sK0)) | ~r2_hidden(sK3(sK0,sK1),sK1) | ~r2_hidden(sK3(sK0,sK1),X0)) )),
% 1.67/0.58    inference(resolution,[],[f56,f22])).
% 1.67/0.58  fof(f56,plain,(
% 1.67/0.58    ( ! [X2,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(X1)) | sK1 = X1 | ~r2_hidden(X2,k1_zfmisc_1(sK0)) | ~r2_hidden(sK3(X1,sK1),X3) | ~r2_hidden(sK3(X1,sK1),X2)) )),
% 1.67/0.58    inference(resolution,[],[f54,f31])).
% 1.67/0.58  fof(f31,plain,(
% 1.67/0.58    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.67/0.58    inference(cnf_transformation,[],[f10])).
% 1.67/0.58  fof(f10,plain,(
% 1.67/0.58    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.67/0.58    inference(ennf_transformation,[],[f4])).
% 1.67/0.58  fof(f4,axiom,(
% 1.67/0.58    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 1.67/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 1.67/0.58  fof(f54,plain,(
% 1.67/0.58    ( ! [X2,X1] : (~r2_hidden(sK3(X1,sK1),X1) | ~r2_hidden(sK3(X1,sK1),X2) | sK1 = X1 | ~r2_hidden(X2,k1_zfmisc_1(sK0))) )),
% 1.67/0.58    inference(resolution,[],[f42,f34])).
% 1.67/0.58  fof(f42,plain,(
% 1.67/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(sK0)) | sK1 = X0 | ~r2_hidden(sK3(X0,sK1),X1) | ~r2_hidden(sK3(X0,sK1),X0)) )),
% 1.67/0.58    inference(resolution,[],[f40,f31])).
% 1.67/0.58  fof(f40,plain,(
% 1.67/0.58    ( ! [X7] : (~r2_hidden(sK3(X7,sK1),sK0) | ~r2_hidden(sK3(X7,sK1),X7) | sK1 = X7) )),
% 1.67/0.58    inference(resolution,[],[f33,f35])).
% 1.67/0.58  fof(f33,plain,(
% 1.67/0.58    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | X0 = X1 | ~r2_hidden(sK3(X0,X1),X0)) )),
% 1.67/0.58    inference(cnf_transformation,[],[f21])).
% 1.67/0.58  % SZS output end Proof for theBenchmark
% 1.67/0.58  % (24283)------------------------------
% 1.67/0.58  % (24283)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.67/0.58  % (24283)Termination reason: Refutation
% 1.67/0.58  
% 1.67/0.58  % (24283)Memory used [KB]: 10746
% 1.67/0.58  % (24283)Time elapsed: 0.139 s
% 1.67/0.58  % (24283)------------------------------
% 1.67/0.58  % (24283)------------------------------
% 1.67/0.58  % (24279)Success in time 0.221 s
%------------------------------------------------------------------------------
