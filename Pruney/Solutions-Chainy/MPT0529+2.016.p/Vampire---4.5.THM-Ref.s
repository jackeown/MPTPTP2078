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
% DateTime   : Thu Dec  3 12:49:00 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.38s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 101 expanded)
%              Number of leaves         :   11 (  32 expanded)
%              Depth                    :   14
%              Number of atoms          :  148 ( 323 expanded)
%              Number of equality atoms :   26 (  49 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f230,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f32,f36,f40,f217,f229])).

fof(f229,plain,
    ( spl4_1
    | ~ spl4_2
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f218,f215,f34,f30])).

fof(f30,plain,
    ( spl4_1
  <=> k8_relat_1(sK0,sK2) = k8_relat_1(sK1,k8_relat_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f34,plain,
    ( spl4_2
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f215,plain,
    ( spl4_10
  <=> ! [X1,X0] :
        ( k8_relat_1(X0,sK2) = k8_relat_1(X1,k8_relat_1(X0,sK2))
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f218,plain,
    ( k8_relat_1(sK0,sK2) = k8_relat_1(sK1,k8_relat_1(sK0,sK2))
    | ~ spl4_2
    | ~ spl4_10 ),
    inference(resolution,[],[f216,f35])).

fof(f35,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f34])).

fof(f216,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k8_relat_1(X0,sK2) = k8_relat_1(X1,k8_relat_1(X0,sK2)) )
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f215])).

% (15858)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
fof(f217,plain,
    ( ~ spl4_3
    | spl4_10
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f208,f38,f215,f38])).

fof(f38,plain,
    ( spl4_3
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f208,plain,
    ( ! [X0,X1] :
        ( k8_relat_1(X0,sK2) = k8_relat_1(X1,k8_relat_1(X0,sK2))
        | ~ r1_tarski(X0,X1)
        | ~ v1_relat_1(sK2) )
    | ~ spl4_3 ),
    inference(resolution,[],[f207,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_relat_1)).

fof(f207,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(k2_relat_1(k8_relat_1(X0,sK2)),X2)
        | k8_relat_1(X0,sK2) = k8_relat_1(X1,k8_relat_1(X0,sK2))
        | ~ r1_tarski(X2,X1) )
    | ~ spl4_3 ),
    inference(duplicate_literal_removal,[],[f205])).

fof(f205,plain,
    ( ! [X2,X0,X1] :
        ( k8_relat_1(X0,sK2) = k8_relat_1(X1,k8_relat_1(X0,sK2))
        | ~ r1_tarski(k2_relat_1(k8_relat_1(X0,sK2)),X2)
        | ~ r1_tarski(X2,X1)
        | k8_relat_1(X0,sK2) = k8_relat_1(X1,k8_relat_1(X0,sK2)) )
    | ~ spl4_3 ),
    inference(resolution,[],[f149,f57])).

fof(f57,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k2_relat_1(k8_relat_1(X0,sK2)),X1)
        | k8_relat_1(X0,sK2) = k8_relat_1(X1,k8_relat_1(X0,sK2)) )
    | ~ spl4_3 ),
    inference(resolution,[],[f42,f39])).

fof(f39,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f38])).

fof(f42,plain,(
    ! [X2,X3,X1] :
      ( ~ v1_relat_1(X2)
      | k8_relat_1(X1,X2) = k8_relat_1(X3,k8_relat_1(X1,X2))
      | ~ r1_tarski(k2_relat_1(k8_relat_1(X1,X2)),X3) ) ),
    inference(resolution,[],[f25,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relat_1)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | k8_relat_1(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k8_relat_1(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).

fof(f149,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(k2_relat_1(k8_relat_1(X2,sK2)),X1)
        | k8_relat_1(X2,sK2) = k8_relat_1(X1,k8_relat_1(X2,sK2))
        | ~ r1_tarski(k2_relat_1(k8_relat_1(X2,sK2)),X0)
        | ~ r1_tarski(X0,X1) )
    | ~ spl4_3 ),
    inference(resolution,[],[f91,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f17,f18])).

fof(f18,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f91,plain,
    ( ! [X4,X2,X5,X3] :
        ( ~ r2_hidden(sK3(k2_relat_1(k8_relat_1(X2,sK2)),X3),X5)
        | ~ r1_tarski(X4,X3)
        | k8_relat_1(X2,sK2) = k8_relat_1(X3,k8_relat_1(X2,sK2))
        | ~ r1_tarski(X5,X4) )
    | ~ spl4_3 ),
    inference(resolution,[],[f75,f26])).

fof(f26,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f75,plain,
    ( ! [X2,X3,X1] :
        ( ~ r2_hidden(sK3(k2_relat_1(k8_relat_1(X1,sK2)),X2),X3)
        | k8_relat_1(X1,sK2) = k8_relat_1(X2,k8_relat_1(X1,sK2))
        | ~ r1_tarski(X3,X2) )
    | ~ spl4_3 ),
    inference(resolution,[],[f63,f26])).

fof(f63,plain,
    ( ! [X2,X1] :
        ( ~ r2_hidden(sK3(k2_relat_1(k8_relat_1(X1,sK2)),X2),X2)
        | k8_relat_1(X1,sK2) = k8_relat_1(X2,k8_relat_1(X1,sK2)) )
    | ~ spl4_3 ),
    inference(resolution,[],[f57,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f40,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f20,f38])).

fof(f20,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( k8_relat_1(sK0,sK2) != k8_relat_1(sK1,k8_relat_1(sK0,sK2))
    & r1_tarski(sK0,sK1)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f14])).

fof(f14,plain,
    ( ? [X0,X1,X2] :
        ( k8_relat_1(X0,X2) != k8_relat_1(X1,k8_relat_1(X0,X2))
        & r1_tarski(X0,X1)
        & v1_relat_1(X2) )
   => ( k8_relat_1(sK0,sK2) != k8_relat_1(sK1,k8_relat_1(sK0,sK2))
      & r1_tarski(sK0,sK1)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( k8_relat_1(X0,X2) != k8_relat_1(X1,k8_relat_1(X0,X2))
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( k8_relat_1(X0,X2) != k8_relat_1(X1,k8_relat_1(X0,X2))
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X0,X1)
         => k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_relat_1)).

fof(f36,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f21,f34])).

fof(f21,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f32,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f22,f30])).

fof(f22,plain,(
    k8_relat_1(sK0,sK2) != k8_relat_1(sK1,k8_relat_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:34:54 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.50  % (15866)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.50  % (15882)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.51  % (15875)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.51  % (15867)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (15873)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.51  % (15859)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (15874)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.52  % (15857)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (15857)Refutation not found, incomplete strategy% (15857)------------------------------
% 0.21/0.52  % (15857)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (15857)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (15857)Memory used [KB]: 10618
% 0.21/0.52  % (15857)Time elapsed: 0.113 s
% 0.21/0.52  % (15857)------------------------------
% 0.21/0.52  % (15857)------------------------------
% 0.21/0.52  % (15865)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.52  % (15874)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 1.38/0.53  % SZS output start Proof for theBenchmark
% 1.38/0.53  fof(f230,plain,(
% 1.38/0.53    $false),
% 1.38/0.53    inference(avatar_sat_refutation,[],[f32,f36,f40,f217,f229])).
% 1.38/0.53  fof(f229,plain,(
% 1.38/0.53    spl4_1 | ~spl4_2 | ~spl4_10),
% 1.38/0.53    inference(avatar_split_clause,[],[f218,f215,f34,f30])).
% 1.38/0.53  fof(f30,plain,(
% 1.38/0.53    spl4_1 <=> k8_relat_1(sK0,sK2) = k8_relat_1(sK1,k8_relat_1(sK0,sK2))),
% 1.38/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.38/0.53  fof(f34,plain,(
% 1.38/0.53    spl4_2 <=> r1_tarski(sK0,sK1)),
% 1.38/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.38/0.53  fof(f215,plain,(
% 1.38/0.53    spl4_10 <=> ! [X1,X0] : (k8_relat_1(X0,sK2) = k8_relat_1(X1,k8_relat_1(X0,sK2)) | ~r1_tarski(X0,X1))),
% 1.38/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 1.38/0.53  fof(f218,plain,(
% 1.38/0.53    k8_relat_1(sK0,sK2) = k8_relat_1(sK1,k8_relat_1(sK0,sK2)) | (~spl4_2 | ~spl4_10)),
% 1.38/0.53    inference(resolution,[],[f216,f35])).
% 1.38/0.53  fof(f35,plain,(
% 1.38/0.53    r1_tarski(sK0,sK1) | ~spl4_2),
% 1.38/0.53    inference(avatar_component_clause,[],[f34])).
% 1.38/0.53  fof(f216,plain,(
% 1.38/0.53    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k8_relat_1(X0,sK2) = k8_relat_1(X1,k8_relat_1(X0,sK2))) ) | ~spl4_10),
% 1.38/0.53    inference(avatar_component_clause,[],[f215])).
% 1.38/0.53  % (15858)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.38/0.53  fof(f217,plain,(
% 1.38/0.53    ~spl4_3 | spl4_10 | ~spl4_3),
% 1.38/0.53    inference(avatar_split_clause,[],[f208,f38,f215,f38])).
% 1.38/0.53  fof(f38,plain,(
% 1.38/0.53    spl4_3 <=> v1_relat_1(sK2)),
% 1.38/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.38/0.53  fof(f208,plain,(
% 1.38/0.53    ( ! [X0,X1] : (k8_relat_1(X0,sK2) = k8_relat_1(X1,k8_relat_1(X0,sK2)) | ~r1_tarski(X0,X1) | ~v1_relat_1(sK2)) ) | ~spl4_3),
% 1.38/0.53    inference(resolution,[],[f207,f24])).
% 1.38/0.53  fof(f24,plain,(
% 1.38/0.53    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) | ~v1_relat_1(X1)) )),
% 1.38/0.53    inference(cnf_transformation,[],[f10])).
% 1.38/0.53  fof(f10,plain,(
% 1.38/0.53    ! [X0,X1] : (r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) | ~v1_relat_1(X1))),
% 1.38/0.53    inference(ennf_transformation,[],[f3])).
% 1.38/0.53  fof(f3,axiom,(
% 1.38/0.53    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0))),
% 1.38/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_relat_1)).
% 1.38/0.53  fof(f207,plain,(
% 1.38/0.53    ( ! [X2,X0,X1] : (~r1_tarski(k2_relat_1(k8_relat_1(X0,sK2)),X2) | k8_relat_1(X0,sK2) = k8_relat_1(X1,k8_relat_1(X0,sK2)) | ~r1_tarski(X2,X1)) ) | ~spl4_3),
% 1.38/0.53    inference(duplicate_literal_removal,[],[f205])).
% 1.38/0.53  fof(f205,plain,(
% 1.38/0.53    ( ! [X2,X0,X1] : (k8_relat_1(X0,sK2) = k8_relat_1(X1,k8_relat_1(X0,sK2)) | ~r1_tarski(k2_relat_1(k8_relat_1(X0,sK2)),X2) | ~r1_tarski(X2,X1) | k8_relat_1(X0,sK2) = k8_relat_1(X1,k8_relat_1(X0,sK2))) ) | ~spl4_3),
% 1.38/0.53    inference(resolution,[],[f149,f57])).
% 1.38/0.53  fof(f57,plain,(
% 1.38/0.53    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(k8_relat_1(X0,sK2)),X1) | k8_relat_1(X0,sK2) = k8_relat_1(X1,k8_relat_1(X0,sK2))) ) | ~spl4_3),
% 1.38/0.53    inference(resolution,[],[f42,f39])).
% 1.38/0.53  fof(f39,plain,(
% 1.38/0.53    v1_relat_1(sK2) | ~spl4_3),
% 1.38/0.53    inference(avatar_component_clause,[],[f38])).
% 1.38/0.53  fof(f42,plain,(
% 1.38/0.53    ( ! [X2,X3,X1] : (~v1_relat_1(X2) | k8_relat_1(X1,X2) = k8_relat_1(X3,k8_relat_1(X1,X2)) | ~r1_tarski(k2_relat_1(k8_relat_1(X1,X2)),X3)) )),
% 1.38/0.53    inference(resolution,[],[f25,f23])).
% 1.38/0.53  fof(f23,plain,(
% 1.38/0.53    ( ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1)) )),
% 1.38/0.53    inference(cnf_transformation,[],[f9])).
% 1.38/0.53  fof(f9,plain,(
% 1.38/0.53    ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1))),
% 1.38/0.53    inference(ennf_transformation,[],[f2])).
% 1.38/0.53  fof(f2,axiom,(
% 1.38/0.53    ! [X0,X1] : (v1_relat_1(X1) => v1_relat_1(k8_relat_1(X0,X1)))),
% 1.38/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relat_1)).
% 1.38/0.53  fof(f25,plain,(
% 1.38/0.53    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | k8_relat_1(X0,X1) = X1) )),
% 1.38/0.53    inference(cnf_transformation,[],[f12])).
% 1.38/0.53  fof(f12,plain,(
% 1.38/0.53    ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.38/0.53    inference(flattening,[],[f11])).
% 1.38/0.53  fof(f11,plain,(
% 1.38/0.53    ! [X0,X1] : ((k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.38/0.53    inference(ennf_transformation,[],[f4])).
% 1.38/0.53  fof(f4,axiom,(
% 1.38/0.53    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k8_relat_1(X0,X1) = X1))),
% 1.38/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).
% 1.38/0.53  fof(f149,plain,(
% 1.38/0.53    ( ! [X2,X0,X1] : (r1_tarski(k2_relat_1(k8_relat_1(X2,sK2)),X1) | k8_relat_1(X2,sK2) = k8_relat_1(X1,k8_relat_1(X2,sK2)) | ~r1_tarski(k2_relat_1(k8_relat_1(X2,sK2)),X0) | ~r1_tarski(X0,X1)) ) | ~spl4_3),
% 1.38/0.53    inference(resolution,[],[f91,f27])).
% 1.38/0.53  fof(f27,plain,(
% 1.38/0.53    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.38/0.53    inference(cnf_transformation,[],[f19])).
% 1.38/0.53  fof(f19,plain,(
% 1.38/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.38/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f17,f18])).
% 1.38/0.53  fof(f18,plain,(
% 1.38/0.53    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 1.38/0.53    introduced(choice_axiom,[])).
% 1.38/0.53  fof(f17,plain,(
% 1.38/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.38/0.53    inference(rectify,[],[f16])).
% 1.38/0.53  fof(f16,plain,(
% 1.38/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.38/0.53    inference(nnf_transformation,[],[f13])).
% 1.38/0.53  fof(f13,plain,(
% 1.38/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.38/0.53    inference(ennf_transformation,[],[f1])).
% 1.38/0.53  fof(f1,axiom,(
% 1.38/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.38/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.38/0.53  fof(f91,plain,(
% 1.38/0.53    ( ! [X4,X2,X5,X3] : (~r2_hidden(sK3(k2_relat_1(k8_relat_1(X2,sK2)),X3),X5) | ~r1_tarski(X4,X3) | k8_relat_1(X2,sK2) = k8_relat_1(X3,k8_relat_1(X2,sK2)) | ~r1_tarski(X5,X4)) ) | ~spl4_3),
% 1.38/0.53    inference(resolution,[],[f75,f26])).
% 1.38/0.53  fof(f26,plain,(
% 1.38/0.53    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 1.38/0.53    inference(cnf_transformation,[],[f19])).
% 1.38/0.53  fof(f75,plain,(
% 1.38/0.53    ( ! [X2,X3,X1] : (~r2_hidden(sK3(k2_relat_1(k8_relat_1(X1,sK2)),X2),X3) | k8_relat_1(X1,sK2) = k8_relat_1(X2,k8_relat_1(X1,sK2)) | ~r1_tarski(X3,X2)) ) | ~spl4_3),
% 1.38/0.53    inference(resolution,[],[f63,f26])).
% 1.38/0.53  fof(f63,plain,(
% 1.38/0.53    ( ! [X2,X1] : (~r2_hidden(sK3(k2_relat_1(k8_relat_1(X1,sK2)),X2),X2) | k8_relat_1(X1,sK2) = k8_relat_1(X2,k8_relat_1(X1,sK2))) ) | ~spl4_3),
% 1.38/0.53    inference(resolution,[],[f57,f28])).
% 1.38/0.53  fof(f28,plain,(
% 1.38/0.53    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK3(X0,X1),X1)) )),
% 1.38/0.53    inference(cnf_transformation,[],[f19])).
% 1.38/0.53  fof(f40,plain,(
% 1.38/0.53    spl4_3),
% 1.38/0.53    inference(avatar_split_clause,[],[f20,f38])).
% 1.38/0.53  fof(f20,plain,(
% 1.38/0.53    v1_relat_1(sK2)),
% 1.38/0.53    inference(cnf_transformation,[],[f15])).
% 1.38/0.53  fof(f15,plain,(
% 1.38/0.53    k8_relat_1(sK0,sK2) != k8_relat_1(sK1,k8_relat_1(sK0,sK2)) & r1_tarski(sK0,sK1) & v1_relat_1(sK2)),
% 1.38/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f14])).
% 1.38/0.53  fof(f14,plain,(
% 1.38/0.53    ? [X0,X1,X2] : (k8_relat_1(X0,X2) != k8_relat_1(X1,k8_relat_1(X0,X2)) & r1_tarski(X0,X1) & v1_relat_1(X2)) => (k8_relat_1(sK0,sK2) != k8_relat_1(sK1,k8_relat_1(sK0,sK2)) & r1_tarski(sK0,sK1) & v1_relat_1(sK2))),
% 1.38/0.53    introduced(choice_axiom,[])).
% 1.38/0.53  fof(f8,plain,(
% 1.38/0.53    ? [X0,X1,X2] : (k8_relat_1(X0,X2) != k8_relat_1(X1,k8_relat_1(X0,X2)) & r1_tarski(X0,X1) & v1_relat_1(X2))),
% 1.38/0.53    inference(flattening,[],[f7])).
% 1.38/0.53  fof(f7,plain,(
% 1.38/0.53    ? [X0,X1,X2] : ((k8_relat_1(X0,X2) != k8_relat_1(X1,k8_relat_1(X0,X2)) & r1_tarski(X0,X1)) & v1_relat_1(X2))),
% 1.38/0.53    inference(ennf_transformation,[],[f6])).
% 1.38/0.53  fof(f6,negated_conjecture,(
% 1.38/0.53    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2))))),
% 1.38/0.53    inference(negated_conjecture,[],[f5])).
% 1.38/0.53  fof(f5,conjecture,(
% 1.38/0.53    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2))))),
% 1.38/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_relat_1)).
% 1.38/0.53  fof(f36,plain,(
% 1.38/0.53    spl4_2),
% 1.38/0.53    inference(avatar_split_clause,[],[f21,f34])).
% 1.38/0.53  fof(f21,plain,(
% 1.38/0.53    r1_tarski(sK0,sK1)),
% 1.38/0.53    inference(cnf_transformation,[],[f15])).
% 1.38/0.53  fof(f32,plain,(
% 1.38/0.53    ~spl4_1),
% 1.38/0.53    inference(avatar_split_clause,[],[f22,f30])).
% 1.38/0.53  fof(f22,plain,(
% 1.38/0.53    k8_relat_1(sK0,sK2) != k8_relat_1(sK1,k8_relat_1(sK0,sK2))),
% 1.38/0.53    inference(cnf_transformation,[],[f15])).
% 1.38/0.53  % SZS output end Proof for theBenchmark
% 1.38/0.53  % (15874)------------------------------
% 1.38/0.53  % (15874)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.53  % (15874)Termination reason: Refutation
% 1.38/0.53  
% 1.38/0.53  % (15874)Memory used [KB]: 10874
% 1.38/0.53  % (15874)Time elapsed: 0.126 s
% 1.38/0.53  % (15874)------------------------------
% 1.38/0.53  % (15874)------------------------------
% 1.38/0.53  % (15854)Success in time 0.177 s
%------------------------------------------------------------------------------
