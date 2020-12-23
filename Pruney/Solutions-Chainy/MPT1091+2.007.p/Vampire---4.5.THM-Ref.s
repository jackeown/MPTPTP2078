%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:25 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 150 expanded)
%              Number of leaves         :   12 (  43 expanded)
%              Depth                    :   15
%              Number of atoms          :  205 ( 538 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f118,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f47,f88,f117])).

fof(f117,plain,
    ( ~ spl4_1
    | spl4_2 ),
    inference(avatar_contradiction_clause,[],[f116])).

fof(f116,plain,
    ( $false
    | ~ spl4_1
    | spl4_2 ),
    inference(subsumption_resolution,[],[f115,f89])).

fof(f89,plain,
    ( v1_finset_1(sK2)
    | ~ spl4_1 ),
    inference(resolution,[],[f42,f27])).

fof(f27,plain,(
    ! [X0] :
      ( ~ sP0(X0)
      | v1_finset_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ( ~ v1_finset_1(sK1(X0))
          & r2_hidden(sK1(X0),X0) )
        | ~ v1_finset_1(X0) )
      & ( ( ! [X2] :
              ( v1_finset_1(X2)
              | ~ r2_hidden(X2,X0) )
          & v1_finset_1(X0) )
        | ~ sP0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f20])).

fof(f20,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_finset_1(X1)
          & r2_hidden(X1,X0) )
     => ( ~ v1_finset_1(sK1(X0))
        & r2_hidden(sK1(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ? [X1] :
            ( ~ v1_finset_1(X1)
            & r2_hidden(X1,X0) )
        | ~ v1_finset_1(X0) )
      & ( ( ! [X2] :
              ( v1_finset_1(X2)
              | ~ r2_hidden(X2,X0) )
          & v1_finset_1(X0) )
        | ~ sP0(X0) ) ) ),
    inference(rectify,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ? [X1] :
            ( ~ v1_finset_1(X1)
            & r2_hidden(X1,X0) )
        | ~ v1_finset_1(X0) )
      & ( ( ! [X1] :
              ( v1_finset_1(X1)
              | ~ r2_hidden(X1,X0) )
          & v1_finset_1(X0) )
        | ~ sP0(X0) ) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ? [X1] :
            ( ~ v1_finset_1(X1)
            & r2_hidden(X1,X0) )
        | ~ v1_finset_1(X0) )
      & ( ( ! [X1] :
              ( v1_finset_1(X1)
              | ~ r2_hidden(X1,X0) )
          & v1_finset_1(X0) )
        | ~ sP0(X0) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( sP0(X0)
    <=> ( ! [X1] :
            ( v1_finset_1(X1)
            | ~ r2_hidden(X1,X0) )
        & v1_finset_1(X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f42,plain,
    ( sP0(sK2)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f40])).

fof(f40,plain,
    ( spl4_1
  <=> sP0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f115,plain,
    ( ~ v1_finset_1(sK2)
    | ~ spl4_1
    | spl4_2 ),
    inference(subsumption_resolution,[],[f110,f45])).

fof(f45,plain,
    ( ~ v1_finset_1(k3_tarski(sK2))
    | spl4_2 ),
    inference(avatar_component_clause,[],[f44])).

fof(f44,plain,
    ( spl4_2
  <=> v1_finset_1(k3_tarski(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f110,plain,
    ( v1_finset_1(k3_tarski(sK2))
    | ~ v1_finset_1(sK2)
    | ~ spl4_1
    | spl4_2 ),
    inference(resolution,[],[f108,f36])).

fof(f36,plain,(
    ! [X0] :
      ( ~ v1_finset_1(sK3(X0))
      | v1_finset_1(k3_tarski(X0))
      | ~ v1_finset_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( v1_finset_1(k3_tarski(X0))
      | ( ~ v1_finset_1(sK3(X0))
        & r2_hidden(sK3(X0),X0) )
      | ~ v1_finset_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f11,f25])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_finset_1(X1)
          & r2_hidden(X1,X0) )
     => ( ~ v1_finset_1(sK3(X0))
        & r2_hidden(sK3(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ! [X0] :
      ( v1_finset_1(k3_tarski(X0))
      | ? [X1] :
          ( ~ v1_finset_1(X1)
          & r2_hidden(X1,X0) )
      | ~ v1_finset_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( v1_finset_1(k3_tarski(X0))
      | ? [X1] :
          ( ~ v1_finset_1(X1)
          & r2_hidden(X1,X0) )
      | ~ v1_finset_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( ! [X1] :
            ( r2_hidden(X1,X0)
           => v1_finset_1(X1) )
        & v1_finset_1(X0) )
     => v1_finset_1(k3_tarski(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l22_finset_1)).

fof(f108,plain,
    ( v1_finset_1(sK3(sK2))
    | ~ spl4_1
    | spl4_2 ),
    inference(resolution,[],[f107,f90])).

fof(f90,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | v1_finset_1(X0) )
    | ~ spl4_1 ),
    inference(resolution,[],[f42,f28])).

fof(f28,plain,(
    ! [X2,X0] :
      ( ~ sP0(X0)
      | ~ r2_hidden(X2,X0)
      | v1_finset_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f107,plain,
    ( r2_hidden(sK3(sK2),sK2)
    | ~ spl4_1
    | spl4_2 ),
    inference(subsumption_resolution,[],[f92,f45])).

fof(f92,plain,
    ( r2_hidden(sK3(sK2),sK2)
    | v1_finset_1(k3_tarski(sK2))
    | ~ spl4_1 ),
    inference(resolution,[],[f89,f35])).

fof(f35,plain,(
    ! [X0] :
      ( ~ v1_finset_1(X0)
      | r2_hidden(sK3(X0),X0)
      | v1_finset_1(k3_tarski(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f88,plain,(
    ~ spl4_2 ),
    inference(avatar_contradiction_clause,[],[f87])).

fof(f87,plain,
    ( $false
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f86,f65])).

fof(f65,plain,
    ( v1_finset_1(sK2)
    | ~ spl4_2 ),
    inference(resolution,[],[f52,f33])).

fof(f33,plain,(
    ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0))) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_zfmisc_1)).

fof(f52,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_zfmisc_1(k3_tarski(sK2)))
        | v1_finset_1(X0) )
    | ~ spl4_2 ),
    inference(resolution,[],[f50,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ v1_finset_1(X1)
      | v1_finset_1(X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( v1_finset_1(X0)
      | ~ v1_finset_1(X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( v1_finset_1(X0)
      | ~ v1_finset_1(X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_finset_1(X1)
        & r1_tarski(X0,X1) )
     => v1_finset_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_finset_1)).

fof(f50,plain,
    ( v1_finset_1(k1_zfmisc_1(k3_tarski(sK2)))
    | ~ spl4_2 ),
    inference(resolution,[],[f46,f34])).

fof(f34,plain,(
    ! [X0] :
      ( ~ v1_finset_1(X0)
      | v1_finset_1(k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( v1_finset_1(k1_zfmisc_1(X0))
      | ~ v1_finset_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_finset_1(X0)
     => v1_finset_1(k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc17_finset_1)).

fof(f46,plain,
    ( v1_finset_1(k3_tarski(sK2))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f44])).

fof(f86,plain,
    ( ~ v1_finset_1(sK2)
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f81,f56])).

fof(f56,plain,
    ( ~ sP0(sK2)
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f32,f46])).

fof(f32,plain,
    ( ~ v1_finset_1(k3_tarski(sK2))
    | ~ sP0(sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ( ~ v1_finset_1(k3_tarski(sK2))
      | ~ sP0(sK2) )
    & ( v1_finset_1(k3_tarski(sK2))
      | sP0(sK2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f22,f23])).

fof(f23,plain,
    ( ? [X0] :
        ( ( ~ v1_finset_1(k3_tarski(X0))
          | ~ sP0(X0) )
        & ( v1_finset_1(k3_tarski(X0))
          | sP0(X0) ) )
   => ( ( ~ v1_finset_1(k3_tarski(sK2))
        | ~ sP0(sK2) )
      & ( v1_finset_1(k3_tarski(sK2))
        | sP0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0] :
      ( ( ~ v1_finset_1(k3_tarski(X0))
        | ~ sP0(X0) )
      & ( v1_finset_1(k3_tarski(X0))
        | sP0(X0) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( sP0(X0)
    <~> v1_finset_1(k3_tarski(X0)) ) ),
    inference(definition_folding,[],[f8,f15])).

fof(f8,plain,(
    ? [X0] :
      ( ( ! [X1] :
            ( v1_finset_1(X1)
            | ~ r2_hidden(X1,X0) )
        & v1_finset_1(X0) )
    <~> v1_finset_1(k3_tarski(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( ( ! [X1] :
              ( r2_hidden(X1,X0)
             => v1_finset_1(X1) )
          & v1_finset_1(X0) )
      <=> v1_finset_1(k3_tarski(X0)) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( ( ! [X1] :
            ( r2_hidden(X1,X0)
           => v1_finset_1(X1) )
        & v1_finset_1(X0) )
    <=> v1_finset_1(k3_tarski(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_finset_1)).

fof(f81,plain,
    ( sP0(sK2)
    | ~ v1_finset_1(sK2)
    | ~ spl4_2 ),
    inference(resolution,[],[f80,f30])).

fof(f30,plain,(
    ! [X0] :
      ( ~ v1_finset_1(sK1(X0))
      | sP0(X0)
      | ~ v1_finset_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f80,plain,
    ( v1_finset_1(sK1(sK2))
    | ~ spl4_2 ),
    inference(resolution,[],[f75,f48])).

fof(f48,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k3_tarski(sK2))
        | v1_finset_1(X0) )
    | ~ spl4_2 ),
    inference(resolution,[],[f46,f38])).

fof(f75,plain,
    ( r1_tarski(sK1(sK2),k3_tarski(sK2))
    | ~ spl4_2 ),
    inference(resolution,[],[f70,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(X0,k3_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_zfmisc_1)).

fof(f70,plain,
    ( r2_hidden(sK1(sK2),sK2)
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f69,f56])).

fof(f69,plain,
    ( r2_hidden(sK1(sK2),sK2)
    | sP0(sK2)
    | ~ spl4_2 ),
    inference(resolution,[],[f65,f29])).

fof(f29,plain,(
    ! [X0] :
      ( ~ v1_finset_1(X0)
      | r2_hidden(sK1(X0),X0)
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f47,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f31,f44,f40])).

fof(f31,plain,
    ( v1_finset_1(k3_tarski(sK2))
    | sP0(sK2) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:19:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.48  % (2617)dis+1_3_add=large:afp=4000:afq=1.0:anc=none:gs=on:gsem=off:inw=on:lcm=reverse:lwlo=on:nm=64:nwc=1:sas=z3:sos=all:sac=on:thi=all:uwa=all:updr=off:uhcvi=on_12 on theBenchmark
% 0.22/0.48  % (2627)lrs+1_1_av=off:bsr=on:br=off:gs=on:gsem=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_152 on theBenchmark
% 0.22/0.48  % (2631)lrs+1010_4:1_aac=none:add=off:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=on:gs=on:gsem=on:irw=on:nm=0:nwc=2.5:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.48  % (2627)Refutation not found, incomplete strategy% (2627)------------------------------
% 0.22/0.48  % (2627)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (2627)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (2627)Memory used [KB]: 5373
% 0.22/0.48  % (2627)Time elapsed: 0.005 s
% 0.22/0.48  % (2627)------------------------------
% 0.22/0.48  % (2627)------------------------------
% 0.22/0.48  % (2618)dis+1002_8_awrs=converge:awrsf=64:av=off:cond=fast:fsr=off:gsp=input_only:lma=on:nm=64:nwc=1.2:s2a=on:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_12 on theBenchmark
% 0.22/0.48  % (2618)Refutation not found, incomplete strategy% (2618)------------------------------
% 0.22/0.48  % (2618)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (2618)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (2618)Memory used [KB]: 895
% 0.22/0.48  % (2618)Time elapsed: 0.002 s
% 0.22/0.48  % (2618)------------------------------
% 0.22/0.48  % (2618)------------------------------
% 0.22/0.49  % (2622)dis+11_24_afp=40000:afq=1.1:amm=sco:anc=none:bs=on:gs=on:gsem=off:lcm=predicate:lma=on:nm=2:nwc=1:sos=on:sac=on:updr=off_91 on theBenchmark
% 0.22/0.49  % (2616)lrs-11_4:1_afp=4000:afq=2.0:anc=none:br=off:gs=on:lwlo=on:nm=64:nwc=3:stl=30:urr=on_3 on theBenchmark
% 0.22/0.49  % (2622)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f118,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(avatar_sat_refutation,[],[f47,f88,f117])).
% 0.22/0.49  fof(f117,plain,(
% 0.22/0.49    ~spl4_1 | spl4_2),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f116])).
% 0.22/0.49  fof(f116,plain,(
% 0.22/0.49    $false | (~spl4_1 | spl4_2)),
% 0.22/0.49    inference(subsumption_resolution,[],[f115,f89])).
% 0.22/0.49  fof(f89,plain,(
% 0.22/0.49    v1_finset_1(sK2) | ~spl4_1),
% 0.22/0.49    inference(resolution,[],[f42,f27])).
% 0.22/0.49  fof(f27,plain,(
% 0.22/0.49    ( ! [X0] : (~sP0(X0) | v1_finset_1(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f21])).
% 0.22/0.49  fof(f21,plain,(
% 0.22/0.49    ! [X0] : ((sP0(X0) | (~v1_finset_1(sK1(X0)) & r2_hidden(sK1(X0),X0)) | ~v1_finset_1(X0)) & ((! [X2] : (v1_finset_1(X2) | ~r2_hidden(X2,X0)) & v1_finset_1(X0)) | ~sP0(X0)))),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f20])).
% 0.22/0.49  fof(f20,plain,(
% 0.22/0.49    ! [X0] : (? [X1] : (~v1_finset_1(X1) & r2_hidden(X1,X0)) => (~v1_finset_1(sK1(X0)) & r2_hidden(sK1(X0),X0)))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f19,plain,(
% 0.22/0.49    ! [X0] : ((sP0(X0) | ? [X1] : (~v1_finset_1(X1) & r2_hidden(X1,X0)) | ~v1_finset_1(X0)) & ((! [X2] : (v1_finset_1(X2) | ~r2_hidden(X2,X0)) & v1_finset_1(X0)) | ~sP0(X0)))),
% 0.22/0.49    inference(rectify,[],[f18])).
% 0.22/0.49  fof(f18,plain,(
% 0.22/0.49    ! [X0] : ((sP0(X0) | ? [X1] : (~v1_finset_1(X1) & r2_hidden(X1,X0)) | ~v1_finset_1(X0)) & ((! [X1] : (v1_finset_1(X1) | ~r2_hidden(X1,X0)) & v1_finset_1(X0)) | ~sP0(X0)))),
% 0.22/0.49    inference(flattening,[],[f17])).
% 0.22/0.49  fof(f17,plain,(
% 0.22/0.49    ! [X0] : ((sP0(X0) | (? [X1] : (~v1_finset_1(X1) & r2_hidden(X1,X0)) | ~v1_finset_1(X0))) & ((! [X1] : (v1_finset_1(X1) | ~r2_hidden(X1,X0)) & v1_finset_1(X0)) | ~sP0(X0)))),
% 0.22/0.49    inference(nnf_transformation,[],[f15])).
% 0.22/0.49  fof(f15,plain,(
% 0.22/0.49    ! [X0] : (sP0(X0) <=> (! [X1] : (v1_finset_1(X1) | ~r2_hidden(X1,X0)) & v1_finset_1(X0)))),
% 0.22/0.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.22/0.49  fof(f42,plain,(
% 0.22/0.49    sP0(sK2) | ~spl4_1),
% 0.22/0.49    inference(avatar_component_clause,[],[f40])).
% 0.22/0.49  fof(f40,plain,(
% 0.22/0.49    spl4_1 <=> sP0(sK2)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.22/0.49  fof(f115,plain,(
% 0.22/0.49    ~v1_finset_1(sK2) | (~spl4_1 | spl4_2)),
% 0.22/0.49    inference(subsumption_resolution,[],[f110,f45])).
% 0.22/0.49  fof(f45,plain,(
% 0.22/0.49    ~v1_finset_1(k3_tarski(sK2)) | spl4_2),
% 0.22/0.49    inference(avatar_component_clause,[],[f44])).
% 0.22/0.49  fof(f44,plain,(
% 0.22/0.49    spl4_2 <=> v1_finset_1(k3_tarski(sK2))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.22/0.49  fof(f110,plain,(
% 0.22/0.49    v1_finset_1(k3_tarski(sK2)) | ~v1_finset_1(sK2) | (~spl4_1 | spl4_2)),
% 0.22/0.49    inference(resolution,[],[f108,f36])).
% 0.22/0.49  fof(f36,plain,(
% 0.22/0.49    ( ! [X0] : (~v1_finset_1(sK3(X0)) | v1_finset_1(k3_tarski(X0)) | ~v1_finset_1(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f26])).
% 0.22/0.49  fof(f26,plain,(
% 0.22/0.49    ! [X0] : (v1_finset_1(k3_tarski(X0)) | (~v1_finset_1(sK3(X0)) & r2_hidden(sK3(X0),X0)) | ~v1_finset_1(X0))),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f11,f25])).
% 0.22/0.49  fof(f25,plain,(
% 0.22/0.49    ! [X0] : (? [X1] : (~v1_finset_1(X1) & r2_hidden(X1,X0)) => (~v1_finset_1(sK3(X0)) & r2_hidden(sK3(X0),X0)))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f11,plain,(
% 0.22/0.49    ! [X0] : (v1_finset_1(k3_tarski(X0)) | ? [X1] : (~v1_finset_1(X1) & r2_hidden(X1,X0)) | ~v1_finset_1(X0))),
% 0.22/0.49    inference(flattening,[],[f10])).
% 0.22/0.49  fof(f10,plain,(
% 0.22/0.49    ! [X0] : (v1_finset_1(k3_tarski(X0)) | (? [X1] : (~v1_finset_1(X1) & r2_hidden(X1,X0)) | ~v1_finset_1(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f4])).
% 0.22/0.49  fof(f4,axiom,(
% 0.22/0.49    ! [X0] : ((! [X1] : (r2_hidden(X1,X0) => v1_finset_1(X1)) & v1_finset_1(X0)) => v1_finset_1(k3_tarski(X0)))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l22_finset_1)).
% 0.22/0.49  fof(f108,plain,(
% 0.22/0.49    v1_finset_1(sK3(sK2)) | (~spl4_1 | spl4_2)),
% 0.22/0.49    inference(resolution,[],[f107,f90])).
% 0.22/0.49  fof(f90,plain,(
% 0.22/0.49    ( ! [X0] : (~r2_hidden(X0,sK2) | v1_finset_1(X0)) ) | ~spl4_1),
% 0.22/0.49    inference(resolution,[],[f42,f28])).
% 0.22/0.49  fof(f28,plain,(
% 0.22/0.49    ( ! [X2,X0] : (~sP0(X0) | ~r2_hidden(X2,X0) | v1_finset_1(X2)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f21])).
% 0.22/0.49  fof(f107,plain,(
% 0.22/0.49    r2_hidden(sK3(sK2),sK2) | (~spl4_1 | spl4_2)),
% 0.22/0.49    inference(subsumption_resolution,[],[f92,f45])).
% 0.22/0.49  fof(f92,plain,(
% 0.22/0.49    r2_hidden(sK3(sK2),sK2) | v1_finset_1(k3_tarski(sK2)) | ~spl4_1),
% 0.22/0.49    inference(resolution,[],[f89,f35])).
% 0.22/0.49  fof(f35,plain,(
% 0.22/0.49    ( ! [X0] : (~v1_finset_1(X0) | r2_hidden(sK3(X0),X0) | v1_finset_1(k3_tarski(X0))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f26])).
% 0.22/0.49  fof(f88,plain,(
% 0.22/0.49    ~spl4_2),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f87])).
% 0.22/0.49  fof(f87,plain,(
% 0.22/0.49    $false | ~spl4_2),
% 0.22/0.49    inference(subsumption_resolution,[],[f86,f65])).
% 0.22/0.49  fof(f65,plain,(
% 0.22/0.49    v1_finset_1(sK2) | ~spl4_2),
% 0.22/0.49    inference(resolution,[],[f52,f33])).
% 0.22/0.49  fof(f33,plain,(
% 0.22/0.49    ( ! [X0] : (r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0)))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f1])).
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0)))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_zfmisc_1)).
% 0.22/0.49  fof(f52,plain,(
% 0.22/0.49    ( ! [X0] : (~r1_tarski(X0,k1_zfmisc_1(k3_tarski(sK2))) | v1_finset_1(X0)) ) | ~spl4_2),
% 0.22/0.49    inference(resolution,[],[f50,f38])).
% 0.22/0.49  fof(f38,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~v1_finset_1(X1) | v1_finset_1(X0) | ~r1_tarski(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f14])).
% 0.22/0.49  fof(f14,plain,(
% 0.22/0.49    ! [X0,X1] : (v1_finset_1(X0) | ~v1_finset_1(X1) | ~r1_tarski(X0,X1))),
% 0.22/0.49    inference(flattening,[],[f13])).
% 0.22/0.49  fof(f13,plain,(
% 0.22/0.49    ! [X0,X1] : (v1_finset_1(X0) | (~v1_finset_1(X1) | ~r1_tarski(X0,X1)))),
% 0.22/0.49    inference(ennf_transformation,[],[f5])).
% 0.22/0.49  fof(f5,axiom,(
% 0.22/0.49    ! [X0,X1] : ((v1_finset_1(X1) & r1_tarski(X0,X1)) => v1_finset_1(X0))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_finset_1)).
% 0.22/0.49  fof(f50,plain,(
% 0.22/0.49    v1_finset_1(k1_zfmisc_1(k3_tarski(sK2))) | ~spl4_2),
% 0.22/0.49    inference(resolution,[],[f46,f34])).
% 0.22/0.49  fof(f34,plain,(
% 0.22/0.49    ( ! [X0] : (~v1_finset_1(X0) | v1_finset_1(k1_zfmisc_1(X0))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f9])).
% 0.22/0.49  fof(f9,plain,(
% 0.22/0.49    ! [X0] : (v1_finset_1(k1_zfmisc_1(X0)) | ~v1_finset_1(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f3])).
% 0.22/0.49  fof(f3,axiom,(
% 0.22/0.49    ! [X0] : (v1_finset_1(X0) => v1_finset_1(k1_zfmisc_1(X0)))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc17_finset_1)).
% 0.22/0.49  fof(f46,plain,(
% 0.22/0.49    v1_finset_1(k3_tarski(sK2)) | ~spl4_2),
% 0.22/0.49    inference(avatar_component_clause,[],[f44])).
% 0.22/0.49  fof(f86,plain,(
% 0.22/0.49    ~v1_finset_1(sK2) | ~spl4_2),
% 0.22/0.49    inference(subsumption_resolution,[],[f81,f56])).
% 0.22/0.49  fof(f56,plain,(
% 0.22/0.49    ~sP0(sK2) | ~spl4_2),
% 0.22/0.49    inference(subsumption_resolution,[],[f32,f46])).
% 0.22/0.49  fof(f32,plain,(
% 0.22/0.49    ~v1_finset_1(k3_tarski(sK2)) | ~sP0(sK2)),
% 0.22/0.49    inference(cnf_transformation,[],[f24])).
% 0.22/0.49  fof(f24,plain,(
% 0.22/0.49    (~v1_finset_1(k3_tarski(sK2)) | ~sP0(sK2)) & (v1_finset_1(k3_tarski(sK2)) | sP0(sK2))),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f22,f23])).
% 0.22/0.49  fof(f23,plain,(
% 0.22/0.49    ? [X0] : ((~v1_finset_1(k3_tarski(X0)) | ~sP0(X0)) & (v1_finset_1(k3_tarski(X0)) | sP0(X0))) => ((~v1_finset_1(k3_tarski(sK2)) | ~sP0(sK2)) & (v1_finset_1(k3_tarski(sK2)) | sP0(sK2)))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f22,plain,(
% 0.22/0.49    ? [X0] : ((~v1_finset_1(k3_tarski(X0)) | ~sP0(X0)) & (v1_finset_1(k3_tarski(X0)) | sP0(X0)))),
% 0.22/0.49    inference(nnf_transformation,[],[f16])).
% 0.22/0.49  fof(f16,plain,(
% 0.22/0.49    ? [X0] : (sP0(X0) <~> v1_finset_1(k3_tarski(X0)))),
% 0.22/0.49    inference(definition_folding,[],[f8,f15])).
% 0.22/0.49  fof(f8,plain,(
% 0.22/0.49    ? [X0] : ((! [X1] : (v1_finset_1(X1) | ~r2_hidden(X1,X0)) & v1_finset_1(X0)) <~> v1_finset_1(k3_tarski(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f7])).
% 0.22/0.49  fof(f7,negated_conjecture,(
% 0.22/0.49    ~! [X0] : ((! [X1] : (r2_hidden(X1,X0) => v1_finset_1(X1)) & v1_finset_1(X0)) <=> v1_finset_1(k3_tarski(X0)))),
% 0.22/0.49    inference(negated_conjecture,[],[f6])).
% 0.22/0.49  fof(f6,conjecture,(
% 0.22/0.49    ! [X0] : ((! [X1] : (r2_hidden(X1,X0) => v1_finset_1(X1)) & v1_finset_1(X0)) <=> v1_finset_1(k3_tarski(X0)))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_finset_1)).
% 0.22/0.49  fof(f81,plain,(
% 0.22/0.49    sP0(sK2) | ~v1_finset_1(sK2) | ~spl4_2),
% 0.22/0.49    inference(resolution,[],[f80,f30])).
% 0.22/0.49  fof(f30,plain,(
% 0.22/0.49    ( ! [X0] : (~v1_finset_1(sK1(X0)) | sP0(X0) | ~v1_finset_1(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f21])).
% 0.22/0.49  fof(f80,plain,(
% 0.22/0.49    v1_finset_1(sK1(sK2)) | ~spl4_2),
% 0.22/0.49    inference(resolution,[],[f75,f48])).
% 0.22/0.49  fof(f48,plain,(
% 0.22/0.49    ( ! [X0] : (~r1_tarski(X0,k3_tarski(sK2)) | v1_finset_1(X0)) ) | ~spl4_2),
% 0.22/0.49    inference(resolution,[],[f46,f38])).
% 0.22/0.49  fof(f75,plain,(
% 0.22/0.49    r1_tarski(sK1(sK2),k3_tarski(sK2)) | ~spl4_2),
% 0.22/0.49    inference(resolution,[],[f70,f37])).
% 0.22/0.49  fof(f37,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(X0,k3_tarski(X1))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f12])).
% 0.22/0.49  fof(f12,plain,(
% 0.22/0.49    ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1))),
% 0.22/0.49    inference(ennf_transformation,[],[f2])).
% 0.22/0.49  fof(f2,axiom,(
% 0.22/0.49    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(X0,k3_tarski(X1)))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_zfmisc_1)).
% 0.22/0.49  fof(f70,plain,(
% 0.22/0.49    r2_hidden(sK1(sK2),sK2) | ~spl4_2),
% 0.22/0.49    inference(subsumption_resolution,[],[f69,f56])).
% 0.22/0.49  fof(f69,plain,(
% 0.22/0.49    r2_hidden(sK1(sK2),sK2) | sP0(sK2) | ~spl4_2),
% 0.22/0.49    inference(resolution,[],[f65,f29])).
% 0.22/0.49  fof(f29,plain,(
% 0.22/0.49    ( ! [X0] : (~v1_finset_1(X0) | r2_hidden(sK1(X0),X0) | sP0(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f21])).
% 0.22/0.49  fof(f47,plain,(
% 0.22/0.49    spl4_1 | spl4_2),
% 0.22/0.49    inference(avatar_split_clause,[],[f31,f44,f40])).
% 0.22/0.49  fof(f31,plain,(
% 0.22/0.49    v1_finset_1(k3_tarski(sK2)) | sP0(sK2)),
% 0.22/0.49    inference(cnf_transformation,[],[f24])).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (2622)------------------------------
% 0.22/0.49  % (2622)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (2622)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (2622)Memory used [KB]: 9850
% 0.22/0.49  % (2622)Time elapsed: 0.072 s
% 0.22/0.49  % (2622)------------------------------
% 0.22/0.49  % (2622)------------------------------
% 0.22/0.49  % (2612)Success in time 0.125 s
%------------------------------------------------------------------------------
