%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:25 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 116 expanded)
%              Number of leaves         :   14 (  41 expanded)
%              Depth                    :    9
%              Number of atoms          :  202 ( 463 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f93,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f45,f50,f54,f55,f60,f67,f92])).

fof(f92,plain,
    ( ~ spl3_1
    | spl3_3
    | ~ spl3_5 ),
    inference(avatar_contradiction_clause,[],[f91])).

fof(f91,plain,
    ( $false
    | ~ spl3_1
    | spl3_3
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f86,f68])).

fof(f68,plain,
    ( r2_hidden(sK2(sK0),sK0)
    | ~ spl3_1
    | spl3_3 ),
    inference(unit_resulting_resolution,[],[f35,f44,f29])).

fof(f29,plain,(
    ! [X0] :
      ( v1_finset_1(k3_tarski(X0))
      | r2_hidden(sK2(X0),X0)
      | ~ v1_finset_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( v1_finset_1(k3_tarski(X0))
      | ( ~ v1_finset_1(sK2(X0))
        & r2_hidden(sK2(X0),X0) )
      | ~ v1_finset_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f11,f21])).

fof(f21,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_finset_1(X1)
          & r2_hidden(X1,X0) )
     => ( ~ v1_finset_1(sK2(X0))
        & r2_hidden(sK2(X0),X0) ) ) ),
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

fof(f44,plain,
    ( ~ v1_finset_1(k3_tarski(sK0))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f42])).

fof(f42,plain,
    ( spl3_3
  <=> v1_finset_1(k3_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f35,plain,
    ( v1_finset_1(sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f34])).

fof(f34,plain,
    ( spl3_1
  <=> v1_finset_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f86,plain,
    ( ~ r2_hidden(sK2(sK0),sK0)
    | ~ spl3_1
    | spl3_3
    | ~ spl3_5 ),
    inference(unit_resulting_resolution,[],[f69,f53])).

fof(f53,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,sK0)
        | v1_finset_1(X2) )
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f52])).

fof(f52,plain,
    ( spl3_5
  <=> ! [X2] :
        ( v1_finset_1(X2)
        | ~ r2_hidden(X2,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f69,plain,
    ( ~ v1_finset_1(sK2(sK0))
    | ~ spl3_1
    | spl3_3 ),
    inference(unit_resulting_resolution,[],[f35,f44,f30])).

fof(f30,plain,(
    ! [X0] :
      ( v1_finset_1(k3_tarski(X0))
      | ~ v1_finset_1(sK2(X0))
      | ~ v1_finset_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f67,plain,
    ( spl3_2
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(avatar_contradiction_clause,[],[f66])).

fof(f66,plain,
    ( $false
    | spl3_2
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f65,f62])).

fof(f62,plain,
    ( ~ r1_tarski(sK1,k3_tarski(sK0))
    | spl3_2
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f43,f40,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( v1_finset_1(X0)
      | ~ v1_finset_1(X1)
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

fof(f40,plain,
    ( ~ v1_finset_1(sK1)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f38])).

fof(f38,plain,
    ( spl3_2
  <=> v1_finset_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f43,plain,
    ( v1_finset_1(k3_tarski(sK0))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f42])).

fof(f65,plain,
    ( r1_tarski(sK1,k3_tarski(sK0))
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f49,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

fof(f49,plain,
    ( r2_hidden(sK1,sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f47])).

fof(f47,plain,
    ( spl3_4
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f60,plain,
    ( spl3_1
    | ~ spl3_3 ),
    inference(avatar_contradiction_clause,[],[f59])).

fof(f59,plain,
    ( $false
    | spl3_1
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f58,f56])).

fof(f56,plain,
    ( ~ v1_finset_1(k1_zfmisc_1(k3_tarski(sK0)))
    | spl3_1 ),
    inference(unit_resulting_resolution,[],[f27,f36,f32])).

fof(f36,plain,
    ( ~ v1_finset_1(sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f34])).

fof(f27,plain,(
    ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0))) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_zfmisc_1)).

fof(f58,plain,
    ( v1_finset_1(k1_zfmisc_1(k3_tarski(sK0)))
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f43,f28])).

fof(f28,plain,(
    ! [X0] :
      ( v1_finset_1(k1_zfmisc_1(X0))
      | ~ v1_finset_1(X0) ) ),
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

fof(f55,plain,
    ( spl3_1
    | spl3_3 ),
    inference(avatar_split_clause,[],[f23,f42,f34])).

fof(f23,plain,
    ( v1_finset_1(k3_tarski(sK0))
    | v1_finset_1(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ( ~ v1_finset_1(k3_tarski(sK0))
      | ( ~ v1_finset_1(sK1)
        & r2_hidden(sK1,sK0) )
      | ~ v1_finset_1(sK0) )
    & ( v1_finset_1(k3_tarski(sK0))
      | ( ! [X2] :
            ( v1_finset_1(X2)
            | ~ r2_hidden(X2,sK0) )
        & v1_finset_1(sK0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f19,f18])).

fof(f18,plain,
    ( ? [X0] :
        ( ( ~ v1_finset_1(k3_tarski(X0))
          | ? [X1] :
              ( ~ v1_finset_1(X1)
              & r2_hidden(X1,X0) )
          | ~ v1_finset_1(X0) )
        & ( v1_finset_1(k3_tarski(X0))
          | ( ! [X2] :
                ( v1_finset_1(X2)
                | ~ r2_hidden(X2,X0) )
            & v1_finset_1(X0) ) ) )
   => ( ( ~ v1_finset_1(k3_tarski(sK0))
        | ? [X1] :
            ( ~ v1_finset_1(X1)
            & r2_hidden(X1,sK0) )
        | ~ v1_finset_1(sK0) )
      & ( v1_finset_1(k3_tarski(sK0))
        | ( ! [X2] :
              ( v1_finset_1(X2)
              | ~ r2_hidden(X2,sK0) )
          & v1_finset_1(sK0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X1] :
        ( ~ v1_finset_1(X1)
        & r2_hidden(X1,sK0) )
   => ( ~ v1_finset_1(sK1)
      & r2_hidden(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

% (12584)dis+1011_10_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=64:nwc=4:sac=on:sp=occurrence_2 on theBenchmark
fof(f17,plain,(
    ? [X0] :
      ( ( ~ v1_finset_1(k3_tarski(X0))
        | ? [X1] :
            ( ~ v1_finset_1(X1)
            & r2_hidden(X1,X0) )
        | ~ v1_finset_1(X0) )
      & ( v1_finset_1(k3_tarski(X0))
        | ( ! [X2] :
              ( v1_finset_1(X2)
              | ~ r2_hidden(X2,X0) )
          & v1_finset_1(X0) ) ) ) ),
    inference(rectify,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ( ~ v1_finset_1(k3_tarski(X0))
        | ? [X1] :
            ( ~ v1_finset_1(X1)
            & r2_hidden(X1,X0) )
        | ~ v1_finset_1(X0) )
      & ( v1_finset_1(k3_tarski(X0))
        | ( ! [X1] :
              ( v1_finset_1(X1)
              | ~ r2_hidden(X1,X0) )
          & v1_finset_1(X0) ) ) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ( ~ v1_finset_1(k3_tarski(X0))
        | ? [X1] :
            ( ~ v1_finset_1(X1)
            & r2_hidden(X1,X0) )
        | ~ v1_finset_1(X0) )
      & ( v1_finset_1(k3_tarski(X0))
        | ( ! [X1] :
              ( v1_finset_1(X1)
              | ~ r2_hidden(X1,X0) )
          & v1_finset_1(X0) ) ) ) ),
    inference(nnf_transformation,[],[f8])).

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

fof(f54,plain,
    ( spl3_5
    | spl3_3 ),
    inference(avatar_split_clause,[],[f24,f42,f52])).

fof(f24,plain,(
    ! [X2] :
      ( v1_finset_1(k3_tarski(sK0))
      | v1_finset_1(X2)
      | ~ r2_hidden(X2,sK0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f50,plain,
    ( ~ spl3_1
    | spl3_4
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f25,f42,f47,f34])).

fof(f25,plain,
    ( ~ v1_finset_1(k3_tarski(sK0))
    | r2_hidden(sK1,sK0)
    | ~ v1_finset_1(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f45,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f26,f42,f38,f34])).

fof(f26,plain,
    ( ~ v1_finset_1(k3_tarski(sK0))
    | ~ v1_finset_1(sK1)
    | ~ v1_finset_1(sK0) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:16:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.46  % (12602)ott+11_5:1_afp=100000:afq=1.1:br=off:gs=on:nm=64:nwc=1:sos=all:urr=on:updr=off_287 on theBenchmark
% 0.21/0.46  % (12594)dis+11_24_afp=40000:afq=1.1:amm=sco:anc=none:bs=on:gs=on:gsem=off:lcm=predicate:lma=on:nm=2:nwc=1:sos=on:sac=on:updr=off_91 on theBenchmark
% 0.21/0.47  % (12602)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % (12592)dis+10_128_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=2:nwc=1:sp=reverse_arity_3 on theBenchmark
% 0.21/0.47  % (12590)dis+1002_8_awrs=converge:awrsf=64:av=off:cond=fast:fsr=off:gsp=input_only:lma=on:nm=64:nwc=1.2:s2a=on:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_12 on theBenchmark
% 0.21/0.47  % (12590)Refutation not found, incomplete strategy% (12590)------------------------------
% 0.21/0.47  % (12590)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (12590)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (12590)Memory used [KB]: 895
% 0.21/0.47  % (12590)Time elapsed: 0.052 s
% 0.21/0.47  % (12590)------------------------------
% 0.21/0.47  % (12590)------------------------------
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f93,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f45,f50,f54,f55,f60,f67,f92])).
% 0.21/0.47  fof(f92,plain,(
% 0.21/0.47    ~spl3_1 | spl3_3 | ~spl3_5),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f91])).
% 0.21/0.47  fof(f91,plain,(
% 0.21/0.47    $false | (~spl3_1 | spl3_3 | ~spl3_5)),
% 0.21/0.47    inference(subsumption_resolution,[],[f86,f68])).
% 0.21/0.47  fof(f68,plain,(
% 0.21/0.47    r2_hidden(sK2(sK0),sK0) | (~spl3_1 | spl3_3)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f35,f44,f29])).
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    ( ! [X0] : (v1_finset_1(k3_tarski(X0)) | r2_hidden(sK2(X0),X0) | ~v1_finset_1(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f22])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    ! [X0] : (v1_finset_1(k3_tarski(X0)) | (~v1_finset_1(sK2(X0)) & r2_hidden(sK2(X0),X0)) | ~v1_finset_1(X0))),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f11,f21])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    ! [X0] : (? [X1] : (~v1_finset_1(X1) & r2_hidden(X1,X0)) => (~v1_finset_1(sK2(X0)) & r2_hidden(sK2(X0),X0)))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f11,plain,(
% 0.21/0.47    ! [X0] : (v1_finset_1(k3_tarski(X0)) | ? [X1] : (~v1_finset_1(X1) & r2_hidden(X1,X0)) | ~v1_finset_1(X0))),
% 0.21/0.47    inference(flattening,[],[f10])).
% 0.21/0.47  fof(f10,plain,(
% 0.21/0.47    ! [X0] : (v1_finset_1(k3_tarski(X0)) | (? [X1] : (~v1_finset_1(X1) & r2_hidden(X1,X0)) | ~v1_finset_1(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0] : ((! [X1] : (r2_hidden(X1,X0) => v1_finset_1(X1)) & v1_finset_1(X0)) => v1_finset_1(k3_tarski(X0)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l22_finset_1)).
% 0.21/0.47  fof(f44,plain,(
% 0.21/0.47    ~v1_finset_1(k3_tarski(sK0)) | spl3_3),
% 0.21/0.47    inference(avatar_component_clause,[],[f42])).
% 0.21/0.47  fof(f42,plain,(
% 0.21/0.47    spl3_3 <=> v1_finset_1(k3_tarski(sK0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.47  fof(f35,plain,(
% 0.21/0.47    v1_finset_1(sK0) | ~spl3_1),
% 0.21/0.47    inference(avatar_component_clause,[],[f34])).
% 0.21/0.47  fof(f34,plain,(
% 0.21/0.47    spl3_1 <=> v1_finset_1(sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.47  fof(f86,plain,(
% 0.21/0.47    ~r2_hidden(sK2(sK0),sK0) | (~spl3_1 | spl3_3 | ~spl3_5)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f69,f53])).
% 0.21/0.47  fof(f53,plain,(
% 0.21/0.47    ( ! [X2] : (~r2_hidden(X2,sK0) | v1_finset_1(X2)) ) | ~spl3_5),
% 0.21/0.47    inference(avatar_component_clause,[],[f52])).
% 0.21/0.47  fof(f52,plain,(
% 0.21/0.47    spl3_5 <=> ! [X2] : (v1_finset_1(X2) | ~r2_hidden(X2,sK0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.47  fof(f69,plain,(
% 0.21/0.47    ~v1_finset_1(sK2(sK0)) | (~spl3_1 | spl3_3)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f35,f44,f30])).
% 0.21/0.47  fof(f30,plain,(
% 0.21/0.47    ( ! [X0] : (v1_finset_1(k3_tarski(X0)) | ~v1_finset_1(sK2(X0)) | ~v1_finset_1(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f22])).
% 0.21/0.47  fof(f67,plain,(
% 0.21/0.47    spl3_2 | ~spl3_3 | ~spl3_4),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f66])).
% 0.21/0.47  fof(f66,plain,(
% 0.21/0.47    $false | (spl3_2 | ~spl3_3 | ~spl3_4)),
% 0.21/0.47    inference(subsumption_resolution,[],[f65,f62])).
% 0.21/0.47  fof(f62,plain,(
% 0.21/0.47    ~r1_tarski(sK1,k3_tarski(sK0)) | (spl3_2 | ~spl3_3)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f43,f40,f32])).
% 0.21/0.47  fof(f32,plain,(
% 0.21/0.47    ( ! [X0,X1] : (v1_finset_1(X0) | ~v1_finset_1(X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f14])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    ! [X0,X1] : (v1_finset_1(X0) | ~v1_finset_1(X1) | ~r1_tarski(X0,X1))),
% 0.21/0.47    inference(flattening,[],[f13])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    ! [X0,X1] : (v1_finset_1(X0) | (~v1_finset_1(X1) | ~r1_tarski(X0,X1)))),
% 0.21/0.47    inference(ennf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,axiom,(
% 0.21/0.47    ! [X0,X1] : ((v1_finset_1(X1) & r1_tarski(X0,X1)) => v1_finset_1(X0))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_finset_1)).
% 0.21/0.47  fof(f40,plain,(
% 0.21/0.47    ~v1_finset_1(sK1) | spl3_2),
% 0.21/0.47    inference(avatar_component_clause,[],[f38])).
% 0.21/0.47  fof(f38,plain,(
% 0.21/0.47    spl3_2 <=> v1_finset_1(sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.47  fof(f43,plain,(
% 0.21/0.47    v1_finset_1(k3_tarski(sK0)) | ~spl3_3),
% 0.21/0.47    inference(avatar_component_clause,[],[f42])).
% 0.21/0.47  fof(f65,plain,(
% 0.21/0.47    r1_tarski(sK1,k3_tarski(sK0)) | ~spl3_4),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f49,f31])).
% 0.21/0.47  fof(f31,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f12])).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(X0,k3_tarski(X1)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).
% 0.21/0.47  fof(f49,plain,(
% 0.21/0.47    r2_hidden(sK1,sK0) | ~spl3_4),
% 0.21/0.47    inference(avatar_component_clause,[],[f47])).
% 0.21/0.47  fof(f47,plain,(
% 0.21/0.47    spl3_4 <=> r2_hidden(sK1,sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.47  fof(f60,plain,(
% 0.21/0.47    spl3_1 | ~spl3_3),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f59])).
% 0.21/0.47  fof(f59,plain,(
% 0.21/0.47    $false | (spl3_1 | ~spl3_3)),
% 0.21/0.47    inference(subsumption_resolution,[],[f58,f56])).
% 0.21/0.47  fof(f56,plain,(
% 0.21/0.47    ~v1_finset_1(k1_zfmisc_1(k3_tarski(sK0))) | spl3_1),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f27,f36,f32])).
% 0.21/0.47  fof(f36,plain,(
% 0.21/0.47    ~v1_finset_1(sK0) | spl3_1),
% 0.21/0.47    inference(avatar_component_clause,[],[f34])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    ( ! [X0] : (r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0)))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_zfmisc_1)).
% 0.21/0.47  fof(f58,plain,(
% 0.21/0.47    v1_finset_1(k1_zfmisc_1(k3_tarski(sK0))) | ~spl3_3),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f43,f28])).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    ( ! [X0] : (v1_finset_1(k1_zfmisc_1(X0)) | ~v1_finset_1(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f9])).
% 0.21/0.47  fof(f9,plain,(
% 0.21/0.47    ! [X0] : (v1_finset_1(k1_zfmisc_1(X0)) | ~v1_finset_1(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0] : (v1_finset_1(X0) => v1_finset_1(k1_zfmisc_1(X0)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc17_finset_1)).
% 0.21/0.47  fof(f55,plain,(
% 0.21/0.47    spl3_1 | spl3_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f23,f42,f34])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    v1_finset_1(k3_tarski(sK0)) | v1_finset_1(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f20])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    (~v1_finset_1(k3_tarski(sK0)) | (~v1_finset_1(sK1) & r2_hidden(sK1,sK0)) | ~v1_finset_1(sK0)) & (v1_finset_1(k3_tarski(sK0)) | (! [X2] : (v1_finset_1(X2) | ~r2_hidden(X2,sK0)) & v1_finset_1(sK0)))),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f19,f18])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    ? [X0] : ((~v1_finset_1(k3_tarski(X0)) | ? [X1] : (~v1_finset_1(X1) & r2_hidden(X1,X0)) | ~v1_finset_1(X0)) & (v1_finset_1(k3_tarski(X0)) | (! [X2] : (v1_finset_1(X2) | ~r2_hidden(X2,X0)) & v1_finset_1(X0)))) => ((~v1_finset_1(k3_tarski(sK0)) | ? [X1] : (~v1_finset_1(X1) & r2_hidden(X1,sK0)) | ~v1_finset_1(sK0)) & (v1_finset_1(k3_tarski(sK0)) | (! [X2] : (v1_finset_1(X2) | ~r2_hidden(X2,sK0)) & v1_finset_1(sK0))))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    ? [X1] : (~v1_finset_1(X1) & r2_hidden(X1,sK0)) => (~v1_finset_1(sK1) & r2_hidden(sK1,sK0))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  % (12584)dis+1011_10_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=64:nwc=4:sac=on:sp=occurrence_2 on theBenchmark
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ? [X0] : ((~v1_finset_1(k3_tarski(X0)) | ? [X1] : (~v1_finset_1(X1) & r2_hidden(X1,X0)) | ~v1_finset_1(X0)) & (v1_finset_1(k3_tarski(X0)) | (! [X2] : (v1_finset_1(X2) | ~r2_hidden(X2,X0)) & v1_finset_1(X0))))),
% 0.21/0.47    inference(rectify,[],[f16])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    ? [X0] : ((~v1_finset_1(k3_tarski(X0)) | ? [X1] : (~v1_finset_1(X1) & r2_hidden(X1,X0)) | ~v1_finset_1(X0)) & (v1_finset_1(k3_tarski(X0)) | (! [X1] : (v1_finset_1(X1) | ~r2_hidden(X1,X0)) & v1_finset_1(X0))))),
% 0.21/0.47    inference(flattening,[],[f15])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    ? [X0] : ((~v1_finset_1(k3_tarski(X0)) | (? [X1] : (~v1_finset_1(X1) & r2_hidden(X1,X0)) | ~v1_finset_1(X0))) & (v1_finset_1(k3_tarski(X0)) | (! [X1] : (v1_finset_1(X1) | ~r2_hidden(X1,X0)) & v1_finset_1(X0))))),
% 0.21/0.47    inference(nnf_transformation,[],[f8])).
% 0.21/0.47  fof(f8,plain,(
% 0.21/0.47    ? [X0] : ((! [X1] : (v1_finset_1(X1) | ~r2_hidden(X1,X0)) & v1_finset_1(X0)) <~> v1_finset_1(k3_tarski(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f7])).
% 0.21/0.47  fof(f7,negated_conjecture,(
% 0.21/0.47    ~! [X0] : ((! [X1] : (r2_hidden(X1,X0) => v1_finset_1(X1)) & v1_finset_1(X0)) <=> v1_finset_1(k3_tarski(X0)))),
% 0.21/0.47    inference(negated_conjecture,[],[f6])).
% 0.21/0.47  fof(f6,conjecture,(
% 0.21/0.47    ! [X0] : ((! [X1] : (r2_hidden(X1,X0) => v1_finset_1(X1)) & v1_finset_1(X0)) <=> v1_finset_1(k3_tarski(X0)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_finset_1)).
% 0.21/0.47  fof(f54,plain,(
% 0.21/0.47    spl3_5 | spl3_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f24,f42,f52])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    ( ! [X2] : (v1_finset_1(k3_tarski(sK0)) | v1_finset_1(X2) | ~r2_hidden(X2,sK0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f20])).
% 0.21/0.47  fof(f50,plain,(
% 0.21/0.47    ~spl3_1 | spl3_4 | ~spl3_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f25,f42,f47,f34])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    ~v1_finset_1(k3_tarski(sK0)) | r2_hidden(sK1,sK0) | ~v1_finset_1(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f20])).
% 0.21/0.47  fof(f45,plain,(
% 0.21/0.47    ~spl3_1 | ~spl3_2 | ~spl3_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f26,f42,f38,f34])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    ~v1_finset_1(k3_tarski(sK0)) | ~v1_finset_1(sK1) | ~v1_finset_1(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f20])).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (12602)------------------------------
% 0.21/0.47  % (12602)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (12602)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (12598)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
% 0.21/0.47  % (12602)Memory used [KB]: 9850
% 0.21/0.47  % (12602)Time elapsed: 0.050 s
% 0.21/0.47  % (12602)------------------------------
% 0.21/0.47  % (12602)------------------------------
% 0.21/0.47  % (12583)Success in time 0.111 s
%------------------------------------------------------------------------------
