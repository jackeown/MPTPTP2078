%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:42 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 131 expanded)
%              Number of leaves         :   14 (  37 expanded)
%              Depth                    :   15
%              Number of atoms          :  205 ( 431 expanded)
%              Number of equality atoms :   42 ( 124 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f105,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f54,f55,f82,f94,f102,f104])).

fof(f104,plain,
    ( spl3_2
    | ~ spl3_6 ),
    inference(avatar_contradiction_clause,[],[f103])).

fof(f103,plain,
    ( $false
    | spl3_2
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f93,f95])).

fof(f95,plain,
    ( sK0 != k3_tarski(sK1)
    | spl3_2 ),
    inference(superposition,[],[f53,f56])).

fof(f56,plain,(
    k5_setfam_1(sK0,sK1) = k3_tarski(sK1) ),
    inference(resolution,[],[f26,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k3_tarski(X1) = k5_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k3_tarski(X1) = k5_setfam_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k3_tarski(X1) = k5_setfam_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

fof(f26,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f18])).

% (28893)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
fof(f18,plain,
    ( ( sK0 != k5_setfam_1(sK0,sK1)
      | ~ m1_setfam_1(sK1,sK0) )
    & ( sK0 = k5_setfam_1(sK0,sK1)
      | m1_setfam_1(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f17])).

fof(f17,plain,
    ( ? [X0,X1] :
        ( ( k5_setfam_1(X0,X1) != X0
          | ~ m1_setfam_1(X1,X0) )
        & ( k5_setfam_1(X0,X1) = X0
          | m1_setfam_1(X1,X0) )
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
   => ( ( sK0 != k5_setfam_1(sK0,sK1)
        | ~ m1_setfam_1(sK1,sK0) )
      & ( sK0 = k5_setfam_1(sK0,sK1)
        | m1_setfam_1(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1] :
      ( ( k5_setfam_1(X0,X1) != X0
        | ~ m1_setfam_1(X1,X0) )
      & ( k5_setfam_1(X0,X1) = X0
        | m1_setfam_1(X1,X0) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ( k5_setfam_1(X0,X1) != X0
        | ~ m1_setfam_1(X1,X0) )
      & ( k5_setfam_1(X0,X1) = X0
        | m1_setfam_1(X1,X0) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ( m1_setfam_1(X1,X0)
      <~> k5_setfam_1(X0,X1) = X0 )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ( m1_setfam_1(X1,X0)
        <=> k5_setfam_1(X0,X1) = X0 ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( m1_setfam_1(X1,X0)
      <=> k5_setfam_1(X0,X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_setfam_1)).

fof(f53,plain,
    ( sK0 != k5_setfam_1(sK0,sK1)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f51])).

fof(f51,plain,
    ( spl3_2
  <=> sK0 = k5_setfam_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f93,plain,
    ( sK0 = k3_tarski(sK1)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl3_6
  <=> sK0 = k3_tarski(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f102,plain,(
    spl3_5 ),
    inference(avatar_contradiction_clause,[],[f101])).

fof(f101,plain,
    ( $false
    | spl3_5 ),
    inference(subsumption_resolution,[],[f100,f89])).

fof(f89,plain,
    ( ~ r1_tarski(k3_tarski(sK1),sK0)
    | spl3_5 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl3_5
  <=> r1_tarski(k3_tarski(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f100,plain,(
    r1_tarski(k3_tarski(sK1),sK0) ),
    inference(resolution,[],[f99,f45])).

fof(f45,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_zfmisc_1(X0))
      | r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK2(X0,X1),X0)
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( r1_tarski(sK2(X0,X1),X0)
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f23,f24])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK2(X0,X1),X0)
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( r1_tarski(sK2(X0,X1),X0)
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f99,plain,(
    r2_hidden(k3_tarski(sK1),k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f98,f29])).

fof(f29,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f98,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK0))
    | r2_hidden(k3_tarski(sK1),k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f97,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f97,plain,(
    m1_subset_1(k3_tarski(sK1),k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f96,f26])).

fof(f96,plain,
    ( m1_subset_1(k3_tarski(sK1),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(superposition,[],[f32,f56])).

fof(f32,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_setfam_1)).

fof(f94,plain,
    ( ~ spl3_5
    | spl3_6
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f85,f47,f91,f87])).

fof(f47,plain,
    ( spl3_1
  <=> m1_setfam_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f85,plain,
    ( sK0 = k3_tarski(sK1)
    | ~ r1_tarski(k3_tarski(sK1),sK0)
    | ~ spl3_1 ),
    inference(resolution,[],[f83,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f83,plain,
    ( r1_tarski(sK0,k3_tarski(sK1))
    | ~ spl3_1 ),
    inference(resolution,[],[f48,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ m1_setfam_1(X1,X0)
      | r1_tarski(X0,k3_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( m1_setfam_1(X1,X0)
        | ~ r1_tarski(X0,k3_tarski(X1)) )
      & ( r1_tarski(X0,k3_tarski(X1))
        | ~ m1_setfam_1(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_setfam_1(X1,X0)
    <=> r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_setfam_1)).

fof(f48,plain,
    ( m1_setfam_1(sK1,sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f47])).

fof(f82,plain,
    ( spl3_1
    | ~ spl3_2 ),
    inference(avatar_contradiction_clause,[],[f81])).

fof(f81,plain,
    ( $false
    | spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f78,f49])).

fof(f49,plain,
    ( ~ m1_setfam_1(sK1,sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f47])).

fof(f78,plain,
    ( m1_setfam_1(sK1,sK0)
    | ~ spl3_2 ),
    inference(resolution,[],[f76,f42])).

fof(f42,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f76,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK0)
        | m1_setfam_1(sK1,X0) )
    | ~ spl3_2 ),
    inference(superposition,[],[f37,f75])).

fof(f75,plain,
    ( sK0 = k3_tarski(sK1)
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f56,f52])).

fof(f52,plain,
    ( sK0 = k5_setfam_1(sK0,sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f51])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k3_tarski(X1))
      | m1_setfam_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f55,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f27,f51,f47])).

fof(f27,plain,
    ( sK0 = k5_setfam_1(sK0,sK1)
    | m1_setfam_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f54,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f28,f51,f47])).

fof(f28,plain,
    ( sK0 != k5_setfam_1(sK0,sK1)
    | ~ m1_setfam_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 09:39:31 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.47  % (28872)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.48  % (28872)Refutation not found, incomplete strategy% (28872)------------------------------
% 0.20/0.48  % (28872)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (28872)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (28872)Memory used [KB]: 10618
% 0.20/0.48  % (28872)Time elapsed: 0.062 s
% 0.20/0.48  % (28872)------------------------------
% 0.20/0.48  % (28872)------------------------------
% 0.20/0.48  % (28883)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.48  % (28883)Refutation not found, incomplete strategy% (28883)------------------------------
% 0.20/0.48  % (28883)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (28883)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (28883)Memory used [KB]: 10618
% 0.20/0.48  % (28883)Time elapsed: 0.072 s
% 0.20/0.48  % (28883)------------------------------
% 0.20/0.48  % (28883)------------------------------
% 0.20/0.49  % (28876)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.50  % (28873)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.50  % (28881)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.20/0.50  % (28873)Refutation found. Thanks to Tanya!
% 0.20/0.50  % SZS status Theorem for theBenchmark
% 0.20/0.50  % SZS output start Proof for theBenchmark
% 0.20/0.50  fof(f105,plain,(
% 0.20/0.50    $false),
% 0.20/0.50    inference(avatar_sat_refutation,[],[f54,f55,f82,f94,f102,f104])).
% 0.20/0.50  fof(f104,plain,(
% 0.20/0.50    spl3_2 | ~spl3_6),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f103])).
% 0.20/0.50  fof(f103,plain,(
% 0.20/0.50    $false | (spl3_2 | ~spl3_6)),
% 0.20/0.50    inference(subsumption_resolution,[],[f93,f95])).
% 0.20/0.50  fof(f95,plain,(
% 0.20/0.50    sK0 != k3_tarski(sK1) | spl3_2),
% 0.20/0.50    inference(superposition,[],[f53,f56])).
% 0.20/0.50  fof(f56,plain,(
% 0.20/0.50    k5_setfam_1(sK0,sK1) = k3_tarski(sK1)),
% 0.20/0.50    inference(resolution,[],[f26,f31])).
% 0.20/0.50  fof(f31,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k3_tarski(X1) = k5_setfam_1(X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f13])).
% 0.20/0.50  fof(f13,plain,(
% 0.20/0.50    ! [X0,X1] : (k3_tarski(X1) = k5_setfam_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.20/0.50    inference(ennf_transformation,[],[f6])).
% 0.20/0.50  fof(f6,axiom,(
% 0.20/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k3_tarski(X1) = k5_setfam_1(X0,X1))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).
% 0.20/0.50  fof(f26,plain,(
% 0.20/0.50    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.20/0.50    inference(cnf_transformation,[],[f18])).
% 0.20/0.50  % (28893)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.50  fof(f18,plain,(
% 0.20/0.50    (sK0 != k5_setfam_1(sK0,sK1) | ~m1_setfam_1(sK1,sK0)) & (sK0 = k5_setfam_1(sK0,sK1) | m1_setfam_1(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.20/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f17])).
% 0.20/0.50  fof(f17,plain,(
% 0.20/0.50    ? [X0,X1] : ((k5_setfam_1(X0,X1) != X0 | ~m1_setfam_1(X1,X0)) & (k5_setfam_1(X0,X1) = X0 | m1_setfam_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) => ((sK0 != k5_setfam_1(sK0,sK1) | ~m1_setfam_1(sK1,sK0)) & (sK0 = k5_setfam_1(sK0,sK1) | m1_setfam_1(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f16,plain,(
% 0.20/0.50    ? [X0,X1] : ((k5_setfam_1(X0,X1) != X0 | ~m1_setfam_1(X1,X0)) & (k5_setfam_1(X0,X1) = X0 | m1_setfam_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.20/0.50    inference(flattening,[],[f15])).
% 0.20/0.50  fof(f15,plain,(
% 0.20/0.50    ? [X0,X1] : (((k5_setfam_1(X0,X1) != X0 | ~m1_setfam_1(X1,X0)) & (k5_setfam_1(X0,X1) = X0 | m1_setfam_1(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.20/0.50    inference(nnf_transformation,[],[f10])).
% 0.20/0.50  fof(f10,plain,(
% 0.20/0.50    ? [X0,X1] : ((m1_setfam_1(X1,X0) <~> k5_setfam_1(X0,X1) = X0) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.20/0.50    inference(ennf_transformation,[],[f9])).
% 0.20/0.50  fof(f9,negated_conjecture,(
% 0.20/0.50    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (m1_setfam_1(X1,X0) <=> k5_setfam_1(X0,X1) = X0))),
% 0.20/0.50    inference(negated_conjecture,[],[f8])).
% 0.20/0.50  fof(f8,conjecture,(
% 0.20/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (m1_setfam_1(X1,X0) <=> k5_setfam_1(X0,X1) = X0))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_setfam_1)).
% 0.20/0.50  fof(f53,plain,(
% 0.20/0.50    sK0 != k5_setfam_1(sK0,sK1) | spl3_2),
% 0.20/0.50    inference(avatar_component_clause,[],[f51])).
% 0.20/0.50  fof(f51,plain,(
% 0.20/0.50    spl3_2 <=> sK0 = k5_setfam_1(sK0,sK1)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.50  fof(f93,plain,(
% 0.20/0.50    sK0 = k3_tarski(sK1) | ~spl3_6),
% 0.20/0.50    inference(avatar_component_clause,[],[f91])).
% 0.20/0.50  fof(f91,plain,(
% 0.20/0.50    spl3_6 <=> sK0 = k3_tarski(sK1)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.50  fof(f102,plain,(
% 0.20/0.50    spl3_5),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f101])).
% 0.20/0.50  fof(f101,plain,(
% 0.20/0.50    $false | spl3_5),
% 0.20/0.50    inference(subsumption_resolution,[],[f100,f89])).
% 0.20/0.50  fof(f89,plain,(
% 0.20/0.50    ~r1_tarski(k3_tarski(sK1),sK0) | spl3_5),
% 0.20/0.50    inference(avatar_component_clause,[],[f87])).
% 0.20/0.50  fof(f87,plain,(
% 0.20/0.50    spl3_5 <=> r1_tarski(k3_tarski(sK1),sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.50  fof(f100,plain,(
% 0.20/0.50    r1_tarski(k3_tarski(sK1),sK0)),
% 0.20/0.50    inference(resolution,[],[f99,f45])).
% 0.20/0.50  fof(f45,plain,(
% 0.20/0.50    ( ! [X0,X3] : (~r2_hidden(X3,k1_zfmisc_1(X0)) | r1_tarski(X3,X0)) )),
% 0.20/0.50    inference(equality_resolution,[],[f38])).
% 0.20/0.50  fof(f38,plain,(
% 0.20/0.50    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.20/0.50    inference(cnf_transformation,[],[f25])).
% 0.20/0.50  fof(f25,plain,(
% 0.20/0.50    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.20/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f23,f24])).
% 0.20/0.50  fof(f24,plain,(
% 0.20/0.50    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1))))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f23,plain,(
% 0.20/0.50    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.20/0.50    inference(rectify,[],[f22])).
% 0.20/0.50  fof(f22,plain,(
% 0.20/0.50    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.20/0.50    inference(nnf_transformation,[],[f2])).
% 0.20/0.50  fof(f2,axiom,(
% 0.20/0.50    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.20/0.50  fof(f99,plain,(
% 0.20/0.50    r2_hidden(k3_tarski(sK1),k1_zfmisc_1(sK0))),
% 0.20/0.50    inference(subsumption_resolution,[],[f98,f29])).
% 0.20/0.50  fof(f29,plain,(
% 0.20/0.50    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f3])).
% 0.20/0.50  fof(f3,axiom,(
% 0.20/0.50    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).
% 0.20/0.50  fof(f98,plain,(
% 0.20/0.50    v1_xboole_0(k1_zfmisc_1(sK0)) | r2_hidden(k3_tarski(sK1),k1_zfmisc_1(sK0))),
% 0.20/0.50    inference(resolution,[],[f97,f30])).
% 0.20/0.50  fof(f30,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f12])).
% 0.20/0.50  fof(f12,plain,(
% 0.20/0.50    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.20/0.50    inference(flattening,[],[f11])).
% 0.20/0.50  fof(f11,plain,(
% 0.20/0.50    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.20/0.50    inference(ennf_transformation,[],[f7])).
% 0.20/0.50  fof(f7,axiom,(
% 0.20/0.50    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.20/0.50  fof(f97,plain,(
% 0.20/0.50    m1_subset_1(k3_tarski(sK1),k1_zfmisc_1(sK0))),
% 0.20/0.50    inference(subsumption_resolution,[],[f96,f26])).
% 0.20/0.50  fof(f96,plain,(
% 0.20/0.50    m1_subset_1(k3_tarski(sK1),k1_zfmisc_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.20/0.50    inference(superposition,[],[f32,f56])).
% 0.20/0.50  fof(f32,plain,(
% 0.20/0.50    ( ! [X0,X1] : (m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f14])).
% 0.20/0.50  fof(f14,plain,(
% 0.20/0.50    ! [X0,X1] : (m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.20/0.50    inference(ennf_transformation,[],[f5])).
% 0.20/0.50  fof(f5,axiom,(
% 0.20/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_setfam_1)).
% 0.20/0.50  fof(f94,plain,(
% 0.20/0.50    ~spl3_5 | spl3_6 | ~spl3_1),
% 0.20/0.50    inference(avatar_split_clause,[],[f85,f47,f91,f87])).
% 0.20/0.50  fof(f47,plain,(
% 0.20/0.50    spl3_1 <=> m1_setfam_1(sK1,sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.50  fof(f85,plain,(
% 0.20/0.50    sK0 = k3_tarski(sK1) | ~r1_tarski(k3_tarski(sK1),sK0) | ~spl3_1),
% 0.20/0.50    inference(resolution,[],[f83,f35])).
% 0.20/0.50  fof(f35,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f20])).
% 0.20/0.50  fof(f20,plain,(
% 0.20/0.50    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.50    inference(flattening,[],[f19])).
% 0.20/0.50  fof(f19,plain,(
% 0.20/0.50    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.50    inference(nnf_transformation,[],[f1])).
% 0.20/0.50  fof(f1,axiom,(
% 0.20/0.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.50  fof(f83,plain,(
% 0.20/0.50    r1_tarski(sK0,k3_tarski(sK1)) | ~spl3_1),
% 0.20/0.50    inference(resolution,[],[f48,f36])).
% 0.20/0.50  fof(f36,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_setfam_1(X1,X0) | r1_tarski(X0,k3_tarski(X1))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f21])).
% 0.20/0.50  fof(f21,plain,(
% 0.20/0.50    ! [X0,X1] : ((m1_setfam_1(X1,X0) | ~r1_tarski(X0,k3_tarski(X1))) & (r1_tarski(X0,k3_tarski(X1)) | ~m1_setfam_1(X1,X0)))),
% 0.20/0.50    inference(nnf_transformation,[],[f4])).
% 0.20/0.50  fof(f4,axiom,(
% 0.20/0.50    ! [X0,X1] : (m1_setfam_1(X1,X0) <=> r1_tarski(X0,k3_tarski(X1)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_setfam_1)).
% 0.20/0.50  fof(f48,plain,(
% 0.20/0.50    m1_setfam_1(sK1,sK0) | ~spl3_1),
% 0.20/0.50    inference(avatar_component_clause,[],[f47])).
% 0.20/0.50  fof(f82,plain,(
% 0.20/0.50    spl3_1 | ~spl3_2),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f81])).
% 0.20/0.50  fof(f81,plain,(
% 0.20/0.50    $false | (spl3_1 | ~spl3_2)),
% 0.20/0.50    inference(subsumption_resolution,[],[f78,f49])).
% 0.20/0.50  fof(f49,plain,(
% 0.20/0.50    ~m1_setfam_1(sK1,sK0) | spl3_1),
% 0.20/0.50    inference(avatar_component_clause,[],[f47])).
% 0.20/0.50  fof(f78,plain,(
% 0.20/0.50    m1_setfam_1(sK1,sK0) | ~spl3_2),
% 0.20/0.50    inference(resolution,[],[f76,f42])).
% 0.20/0.50  fof(f42,plain,(
% 0.20/0.50    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.20/0.50    inference(equality_resolution,[],[f34])).
% 0.20/0.50  fof(f34,plain,(
% 0.20/0.50    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.20/0.50    inference(cnf_transformation,[],[f20])).
% 0.20/0.50  fof(f76,plain,(
% 0.20/0.50    ( ! [X0] : (~r1_tarski(X0,sK0) | m1_setfam_1(sK1,X0)) ) | ~spl3_2),
% 0.20/0.50    inference(superposition,[],[f37,f75])).
% 0.20/0.50  fof(f75,plain,(
% 0.20/0.50    sK0 = k3_tarski(sK1) | ~spl3_2),
% 0.20/0.50    inference(forward_demodulation,[],[f56,f52])).
% 0.20/0.50  fof(f52,plain,(
% 0.20/0.50    sK0 = k5_setfam_1(sK0,sK1) | ~spl3_2),
% 0.20/0.50    inference(avatar_component_clause,[],[f51])).
% 0.20/0.50  fof(f37,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~r1_tarski(X0,k3_tarski(X1)) | m1_setfam_1(X1,X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f21])).
% 0.20/0.50  fof(f55,plain,(
% 0.20/0.50    spl3_1 | spl3_2),
% 0.20/0.50    inference(avatar_split_clause,[],[f27,f51,f47])).
% 0.20/0.50  fof(f27,plain,(
% 0.20/0.50    sK0 = k5_setfam_1(sK0,sK1) | m1_setfam_1(sK1,sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f18])).
% 0.20/0.50  fof(f54,plain,(
% 0.20/0.50    ~spl3_1 | ~spl3_2),
% 0.20/0.50    inference(avatar_split_clause,[],[f28,f51,f47])).
% 0.20/0.50  fof(f28,plain,(
% 0.20/0.50    sK0 != k5_setfam_1(sK0,sK1) | ~m1_setfam_1(sK1,sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f18])).
% 0.20/0.50  % SZS output end Proof for theBenchmark
% 0.20/0.50  % (28873)------------------------------
% 0.20/0.50  % (28873)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (28873)Termination reason: Refutation
% 0.20/0.50  
% 0.20/0.50  % (28873)Memory used [KB]: 10618
% 0.20/0.50  % (28873)Time elapsed: 0.094 s
% 0.20/0.50  % (28873)------------------------------
% 0.20/0.50  % (28873)------------------------------
% 0.20/0.51  % (28871)Success in time 0.146 s
%------------------------------------------------------------------------------
