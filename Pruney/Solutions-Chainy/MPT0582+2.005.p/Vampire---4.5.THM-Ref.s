%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:50:50 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 101 expanded)
%              Number of leaves         :   14 (  42 expanded)
%              Depth                    :    7
%              Number of atoms          :  179 ( 397 expanded)
%              Number of equality atoms :   10 (  14 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f77,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f25,f30,f35,f40,f45,f49,f53,f60,f67,f76])).

fof(f76,plain,
    ( spl3_1
    | ~ spl3_2
    | ~ spl3_5
    | ~ spl3_9 ),
    inference(avatar_contradiction_clause,[],[f75])).

fof(f75,plain,
    ( $false
    | spl3_1
    | ~ spl3_2
    | ~ spl3_5
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f74,f44])).

fof(f44,plain,
    ( v1_relat_1(sK1)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f42])).

fof(f42,plain,
    ( spl3_5
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f74,plain,
    ( ~ v1_relat_1(sK1)
    | spl3_1
    | ~ spl3_2
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f73,f24])).

fof(f24,plain,
    ( ~ r1_tarski(sK2,k7_relat_1(sK1,sK0))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f22])).

fof(f22,plain,
    ( spl3_1
  <=> r1_tarski(sK2,k7_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f73,plain,
    ( r1_tarski(sK2,k7_relat_1(sK1,sK0))
    | ~ v1_relat_1(sK1)
    | ~ spl3_2
    | ~ spl3_9 ),
    inference(resolution,[],[f66,f29])).

fof(f29,plain,
    ( r1_tarski(sK2,sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f27])).

fof(f27,plain,
    ( spl3_2
  <=> r1_tarski(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f66,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK2,X0)
        | r1_tarski(sK2,k7_relat_1(X0,sK0))
        | ~ v1_relat_1(X0) )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl3_9
  <=> ! [X0] :
        ( r1_tarski(sK2,k7_relat_1(X0,sK0))
        | ~ r1_tarski(sK2,X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f67,plain,
    ( spl3_9
    | ~ spl3_4
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f63,f57,f51,f37,f65])).

fof(f37,plain,
    ( spl3_4
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f51,plain,
    ( spl3_7
  <=> ! [X1,X0,X2] :
        ( r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0))
        | ~ r1_tarski(X1,X2)
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f57,plain,
    ( spl3_8
  <=> sK2 = k7_relat_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f63,plain,
    ( ! [X0] :
        ( r1_tarski(sK2,k7_relat_1(X0,sK0))
        | ~ r1_tarski(sK2,X0)
        | ~ v1_relat_1(X0) )
    | ~ spl3_4
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(subsumption_resolution,[],[f61,f39])).

fof(f39,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f37])).

fof(f61,plain,
    ( ! [X0] :
        ( r1_tarski(sK2,k7_relat_1(X0,sK0))
        | ~ r1_tarski(sK2,X0)
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(sK2) )
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(superposition,[],[f52,f59])).

fof(f59,plain,
    ( sK2 = k7_relat_1(sK2,sK0)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f57])).

fof(f52,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0))
        | ~ r1_tarski(X1,X2)
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(X1) )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f51])).

fof(f60,plain,
    ( spl3_8
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f55,f47,f37,f32,f57])).

fof(f32,plain,
    ( spl3_3
  <=> r1_tarski(k1_relat_1(sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f47,plain,
    ( spl3_6
  <=> ! [X1,X0] :
        ( k7_relat_1(X1,X0) = X1
        | ~ r1_tarski(k1_relat_1(X1),X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f55,plain,
    ( sK2 = k7_relat_1(sK2,sK0)
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f54,f39])).

fof(f54,plain,
    ( sK2 = k7_relat_1(sK2,sK0)
    | ~ v1_relat_1(sK2)
    | ~ spl3_3
    | ~ spl3_6 ),
    inference(resolution,[],[f48,f34])).

fof(f34,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f32])).

fof(f48,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k1_relat_1(X1),X0)
        | k7_relat_1(X1,X0) = X1
        | ~ v1_relat_1(X1) )
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f47])).

fof(f53,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f20,f51])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0))
      | ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_relat_1)).

fof(f49,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f19,f47])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

fof(f45,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f14,f42])).

fof(f14,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( ~ r1_tarski(sK2,k7_relat_1(sK1,sK0))
    & r1_tarski(sK2,sK1)
    & r1_tarski(k1_relat_1(sK2),sK0)
    & v1_relat_1(sK2)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f6,f12,f11])).

fof(f11,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r1_tarski(X2,k7_relat_1(X1,X0))
            & r1_tarski(X2,X1)
            & r1_tarski(k1_relat_1(X2),X0)
            & v1_relat_1(X2) )
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( ~ r1_tarski(X2,k7_relat_1(sK1,sK0))
          & r1_tarski(X2,sK1)
          & r1_tarski(k1_relat_1(X2),sK0)
          & v1_relat_1(X2) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,
    ( ? [X2] :
        ( ~ r1_tarski(X2,k7_relat_1(sK1,sK0))
        & r1_tarski(X2,sK1)
        & r1_tarski(k1_relat_1(X2),sK0)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(sK2,k7_relat_1(sK1,sK0))
      & r1_tarski(sK2,sK1)
      & r1_tarski(k1_relat_1(sK2),sK0)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(X2,k7_relat_1(X1,X0))
          & r1_tarski(X2,X1)
          & r1_tarski(k1_relat_1(X2),X0)
          & v1_relat_1(X2) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(X2,k7_relat_1(X1,X0))
          & r1_tarski(X2,X1)
          & r1_tarski(k1_relat_1(X2),X0)
          & v1_relat_1(X2) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => ( ( r1_tarski(X2,X1)
                & r1_tarski(k1_relat_1(X2),X0) )
             => r1_tarski(X2,k7_relat_1(X1,X0)) ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( ( r1_tarski(X2,X1)
              & r1_tarski(k1_relat_1(X2),X0) )
           => r1_tarski(X2,k7_relat_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t186_relat_1)).

fof(f40,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f15,f37])).

fof(f15,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f35,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f16,f32])).

fof(f16,plain,(
    r1_tarski(k1_relat_1(sK2),sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f30,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f17,f27])).

fof(f17,plain,(
    r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f25,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f18,f22])).

fof(f18,plain,(
    ~ r1_tarski(sK2,k7_relat_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:24:23 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.41  % (31963)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.21/0.42  % (31964)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.21/0.42  % (31963)Refutation found. Thanks to Tanya!
% 0.21/0.42  % SZS status Theorem for theBenchmark
% 0.21/0.42  % SZS output start Proof for theBenchmark
% 0.21/0.42  fof(f77,plain,(
% 0.21/0.42    $false),
% 0.21/0.42    inference(avatar_sat_refutation,[],[f25,f30,f35,f40,f45,f49,f53,f60,f67,f76])).
% 0.21/0.42  fof(f76,plain,(
% 0.21/0.42    spl3_1 | ~spl3_2 | ~spl3_5 | ~spl3_9),
% 0.21/0.42    inference(avatar_contradiction_clause,[],[f75])).
% 0.21/0.42  fof(f75,plain,(
% 0.21/0.42    $false | (spl3_1 | ~spl3_2 | ~spl3_5 | ~spl3_9)),
% 0.21/0.42    inference(subsumption_resolution,[],[f74,f44])).
% 0.21/0.42  fof(f44,plain,(
% 0.21/0.42    v1_relat_1(sK1) | ~spl3_5),
% 0.21/0.42    inference(avatar_component_clause,[],[f42])).
% 0.21/0.42  fof(f42,plain,(
% 0.21/0.42    spl3_5 <=> v1_relat_1(sK1)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.42  fof(f74,plain,(
% 0.21/0.42    ~v1_relat_1(sK1) | (spl3_1 | ~spl3_2 | ~spl3_9)),
% 0.21/0.42    inference(subsumption_resolution,[],[f73,f24])).
% 0.21/0.42  fof(f24,plain,(
% 0.21/0.42    ~r1_tarski(sK2,k7_relat_1(sK1,sK0)) | spl3_1),
% 0.21/0.42    inference(avatar_component_clause,[],[f22])).
% 0.21/0.42  fof(f22,plain,(
% 0.21/0.42    spl3_1 <=> r1_tarski(sK2,k7_relat_1(sK1,sK0))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.42  fof(f73,plain,(
% 0.21/0.42    r1_tarski(sK2,k7_relat_1(sK1,sK0)) | ~v1_relat_1(sK1) | (~spl3_2 | ~spl3_9)),
% 0.21/0.42    inference(resolution,[],[f66,f29])).
% 0.21/0.42  fof(f29,plain,(
% 0.21/0.42    r1_tarski(sK2,sK1) | ~spl3_2),
% 0.21/0.42    inference(avatar_component_clause,[],[f27])).
% 0.21/0.42  fof(f27,plain,(
% 0.21/0.42    spl3_2 <=> r1_tarski(sK2,sK1)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.42  fof(f66,plain,(
% 0.21/0.42    ( ! [X0] : (~r1_tarski(sK2,X0) | r1_tarski(sK2,k7_relat_1(X0,sK0)) | ~v1_relat_1(X0)) ) | ~spl3_9),
% 0.21/0.42    inference(avatar_component_clause,[],[f65])).
% 0.21/0.42  fof(f65,plain,(
% 0.21/0.42    spl3_9 <=> ! [X0] : (r1_tarski(sK2,k7_relat_1(X0,sK0)) | ~r1_tarski(sK2,X0) | ~v1_relat_1(X0))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.42  fof(f67,plain,(
% 0.21/0.42    spl3_9 | ~spl3_4 | ~spl3_7 | ~spl3_8),
% 0.21/0.42    inference(avatar_split_clause,[],[f63,f57,f51,f37,f65])).
% 0.21/0.42  fof(f37,plain,(
% 0.21/0.42    spl3_4 <=> v1_relat_1(sK2)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.42  fof(f51,plain,(
% 0.21/0.42    spl3_7 <=> ! [X1,X0,X2] : (r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.42  fof(f57,plain,(
% 0.21/0.42    spl3_8 <=> sK2 = k7_relat_1(sK2,sK0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.42  fof(f63,plain,(
% 0.21/0.42    ( ! [X0] : (r1_tarski(sK2,k7_relat_1(X0,sK0)) | ~r1_tarski(sK2,X0) | ~v1_relat_1(X0)) ) | (~spl3_4 | ~spl3_7 | ~spl3_8)),
% 0.21/0.42    inference(subsumption_resolution,[],[f61,f39])).
% 0.21/0.42  fof(f39,plain,(
% 0.21/0.42    v1_relat_1(sK2) | ~spl3_4),
% 0.21/0.42    inference(avatar_component_clause,[],[f37])).
% 0.21/0.42  fof(f61,plain,(
% 0.21/0.42    ( ! [X0] : (r1_tarski(sK2,k7_relat_1(X0,sK0)) | ~r1_tarski(sK2,X0) | ~v1_relat_1(X0) | ~v1_relat_1(sK2)) ) | (~spl3_7 | ~spl3_8)),
% 0.21/0.42    inference(superposition,[],[f52,f59])).
% 0.21/0.42  fof(f59,plain,(
% 0.21/0.42    sK2 = k7_relat_1(sK2,sK0) | ~spl3_8),
% 0.21/0.42    inference(avatar_component_clause,[],[f57])).
% 0.21/0.42  fof(f52,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) ) | ~spl3_7),
% 0.21/0.42    inference(avatar_component_clause,[],[f51])).
% 0.21/0.42  fof(f60,plain,(
% 0.21/0.42    spl3_8 | ~spl3_3 | ~spl3_4 | ~spl3_6),
% 0.21/0.42    inference(avatar_split_clause,[],[f55,f47,f37,f32,f57])).
% 0.21/0.42  fof(f32,plain,(
% 0.21/0.42    spl3_3 <=> r1_tarski(k1_relat_1(sK2),sK0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.42  fof(f47,plain,(
% 0.21/0.42    spl3_6 <=> ! [X1,X0] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.42  fof(f55,plain,(
% 0.21/0.42    sK2 = k7_relat_1(sK2,sK0) | (~spl3_3 | ~spl3_4 | ~spl3_6)),
% 0.21/0.42    inference(subsumption_resolution,[],[f54,f39])).
% 0.21/0.42  fof(f54,plain,(
% 0.21/0.42    sK2 = k7_relat_1(sK2,sK0) | ~v1_relat_1(sK2) | (~spl3_3 | ~spl3_6)),
% 0.21/0.42    inference(resolution,[],[f48,f34])).
% 0.21/0.42  fof(f34,plain,(
% 0.21/0.42    r1_tarski(k1_relat_1(sK2),sK0) | ~spl3_3),
% 0.21/0.42    inference(avatar_component_clause,[],[f32])).
% 0.21/0.42  fof(f48,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X1),X0) | k7_relat_1(X1,X0) = X1 | ~v1_relat_1(X1)) ) | ~spl3_6),
% 0.21/0.42    inference(avatar_component_clause,[],[f47])).
% 0.21/0.42  fof(f53,plain,(
% 0.21/0.42    spl3_7),
% 0.21/0.42    inference(avatar_split_clause,[],[f20,f51])).
% 0.21/0.42  fof(f20,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f10])).
% 0.21/0.42  fof(f10,plain,(
% 0.21/0.42    ! [X0,X1] : (! [X2] : (r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.21/0.42    inference(flattening,[],[f9])).
% 0.21/0.42  fof(f9,plain,(
% 0.21/0.42    ! [X0,X1] : (! [X2] : ((r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.21/0.42    inference(ennf_transformation,[],[f1])).
% 0.21/0.42  fof(f1,axiom,(
% 0.21/0.42    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X1,X2) => r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)))))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_relat_1)).
% 0.21/0.42  fof(f49,plain,(
% 0.21/0.42    spl3_6),
% 0.21/0.42    inference(avatar_split_clause,[],[f19,f47])).
% 0.21/0.42  fof(f19,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f8])).
% 0.21/0.42  fof(f8,plain,(
% 0.21/0.42    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.42    inference(flattening,[],[f7])).
% 0.21/0.42  fof(f7,plain,(
% 0.21/0.42    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.42    inference(ennf_transformation,[],[f2])).
% 0.21/0.42  fof(f2,axiom,(
% 0.21/0.42    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).
% 0.21/0.42  fof(f45,plain,(
% 0.21/0.42    spl3_5),
% 0.21/0.42    inference(avatar_split_clause,[],[f14,f42])).
% 0.21/0.42  fof(f14,plain,(
% 0.21/0.42    v1_relat_1(sK1)),
% 0.21/0.42    inference(cnf_transformation,[],[f13])).
% 0.21/0.42  fof(f13,plain,(
% 0.21/0.42    (~r1_tarski(sK2,k7_relat_1(sK1,sK0)) & r1_tarski(sK2,sK1) & r1_tarski(k1_relat_1(sK2),sK0) & v1_relat_1(sK2)) & v1_relat_1(sK1)),
% 0.21/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f6,f12,f11])).
% 0.21/0.42  fof(f11,plain,(
% 0.21/0.42    ? [X0,X1] : (? [X2] : (~r1_tarski(X2,k7_relat_1(X1,X0)) & r1_tarski(X2,X1) & r1_tarski(k1_relat_1(X2),X0) & v1_relat_1(X2)) & v1_relat_1(X1)) => (? [X2] : (~r1_tarski(X2,k7_relat_1(sK1,sK0)) & r1_tarski(X2,sK1) & r1_tarski(k1_relat_1(X2),sK0) & v1_relat_1(X2)) & v1_relat_1(sK1))),
% 0.21/0.42    introduced(choice_axiom,[])).
% 0.21/0.42  fof(f12,plain,(
% 0.21/0.42    ? [X2] : (~r1_tarski(X2,k7_relat_1(sK1,sK0)) & r1_tarski(X2,sK1) & r1_tarski(k1_relat_1(X2),sK0) & v1_relat_1(X2)) => (~r1_tarski(sK2,k7_relat_1(sK1,sK0)) & r1_tarski(sK2,sK1) & r1_tarski(k1_relat_1(sK2),sK0) & v1_relat_1(sK2))),
% 0.21/0.42    introduced(choice_axiom,[])).
% 0.21/0.42  fof(f6,plain,(
% 0.21/0.42    ? [X0,X1] : (? [X2] : (~r1_tarski(X2,k7_relat_1(X1,X0)) & r1_tarski(X2,X1) & r1_tarski(k1_relat_1(X2),X0) & v1_relat_1(X2)) & v1_relat_1(X1))),
% 0.21/0.42    inference(flattening,[],[f5])).
% 0.21/0.42  fof(f5,plain,(
% 0.21/0.42    ? [X0,X1] : (? [X2] : ((~r1_tarski(X2,k7_relat_1(X1,X0)) & (r1_tarski(X2,X1) & r1_tarski(k1_relat_1(X2),X0))) & v1_relat_1(X2)) & v1_relat_1(X1))),
% 0.21/0.42    inference(ennf_transformation,[],[f4])).
% 0.21/0.42  fof(f4,negated_conjecture,(
% 0.21/0.42    ~! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => ((r1_tarski(X2,X1) & r1_tarski(k1_relat_1(X2),X0)) => r1_tarski(X2,k7_relat_1(X1,X0)))))),
% 0.21/0.42    inference(negated_conjecture,[],[f3])).
% 0.21/0.42  fof(f3,conjecture,(
% 0.21/0.42    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => ((r1_tarski(X2,X1) & r1_tarski(k1_relat_1(X2),X0)) => r1_tarski(X2,k7_relat_1(X1,X0)))))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t186_relat_1)).
% 0.21/0.42  fof(f40,plain,(
% 0.21/0.42    spl3_4),
% 0.21/0.42    inference(avatar_split_clause,[],[f15,f37])).
% 0.21/0.42  fof(f15,plain,(
% 0.21/0.42    v1_relat_1(sK2)),
% 0.21/0.42    inference(cnf_transformation,[],[f13])).
% 0.21/0.42  fof(f35,plain,(
% 0.21/0.42    spl3_3),
% 0.21/0.42    inference(avatar_split_clause,[],[f16,f32])).
% 0.21/0.42  fof(f16,plain,(
% 0.21/0.42    r1_tarski(k1_relat_1(sK2),sK0)),
% 0.21/0.42    inference(cnf_transformation,[],[f13])).
% 0.21/0.42  fof(f30,plain,(
% 0.21/0.42    spl3_2),
% 0.21/0.42    inference(avatar_split_clause,[],[f17,f27])).
% 0.21/0.42  fof(f17,plain,(
% 0.21/0.42    r1_tarski(sK2,sK1)),
% 0.21/0.42    inference(cnf_transformation,[],[f13])).
% 0.21/0.42  fof(f25,plain,(
% 0.21/0.42    ~spl3_1),
% 0.21/0.42    inference(avatar_split_clause,[],[f18,f22])).
% 0.21/0.42  fof(f18,plain,(
% 0.21/0.42    ~r1_tarski(sK2,k7_relat_1(sK1,sK0))),
% 0.21/0.42    inference(cnf_transformation,[],[f13])).
% 0.21/0.42  % SZS output end Proof for theBenchmark
% 0.21/0.42  % (31963)------------------------------
% 0.21/0.42  % (31963)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.42  % (31963)Termination reason: Refutation
% 0.21/0.42  
% 0.21/0.42  % (31963)Memory used [KB]: 10490
% 0.21/0.42  % (31963)Time elapsed: 0.006 s
% 0.21/0.42  % (31963)------------------------------
% 0.21/0.42  % (31963)------------------------------
% 0.21/0.42  % (31955)Success in time 0.064 s
%------------------------------------------------------------------------------
