%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:50:52 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 102 expanded)
%              Number of leaves         :   14 (  47 expanded)
%              Depth                    :    7
%              Number of atoms          :  149 ( 390 expanded)
%              Number of equality atoms :   45 ( 145 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f68,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f22,f27,f32,f37,f42,f46,f51,f59,f64,f67])).

fof(f67,plain,
    ( spl4_1
    | ~ spl4_8
    | ~ spl4_9 ),
    inference(avatar_contradiction_clause,[],[f66])).

fof(f66,plain,
    ( $false
    | spl4_1
    | ~ spl4_8
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f65,f21])).

fof(f21,plain,
    ( k7_relat_1(sK0,sK2) != k7_relat_1(sK1,sK2)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f19])).

fof(f19,plain,
    ( spl4_1
  <=> k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f65,plain,
    ( k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2)
    | ~ spl4_8
    | ~ spl4_9 ),
    inference(forward_demodulation,[],[f58,f63])).

fof(f63,plain,
    ( k7_relat_1(sK0,sK2) = k7_relat_1(k7_relat_1(sK0,sK3),sK2)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl4_9
  <=> k7_relat_1(sK0,sK2) = k7_relat_1(k7_relat_1(sK0,sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f58,plain,
    ( k7_relat_1(sK1,sK2) = k7_relat_1(k7_relat_1(sK0,sK3),sK2)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f56])).

fof(f56,plain,
    ( spl4_8
  <=> k7_relat_1(sK1,sK2) = k7_relat_1(k7_relat_1(sK0,sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f64,plain,
    ( spl4_9
    | ~ spl4_5
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f53,f49,f39,f61])).

fof(f39,plain,
    ( spl4_5
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f49,plain,
    ( spl4_7
  <=> ! [X0] :
        ( k7_relat_1(k7_relat_1(X0,sK3),sK2) = k7_relat_1(X0,sK2)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f53,plain,
    ( k7_relat_1(sK0,sK2) = k7_relat_1(k7_relat_1(sK0,sK3),sK2)
    | ~ spl4_5
    | ~ spl4_7 ),
    inference(resolution,[],[f50,f41])).

% (15991)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
fof(f41,plain,
    ( v1_relat_1(sK0)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f39])).

fof(f50,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k7_relat_1(k7_relat_1(X0,sK3),sK2) = k7_relat_1(X0,sK2) )
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f49])).

fof(f59,plain,
    ( spl4_8
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f54,f49,f34,f24,f56])).

fof(f24,plain,
    ( spl4_2
  <=> k7_relat_1(sK0,sK3) = k7_relat_1(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f34,plain,
    ( spl4_4
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f54,plain,
    ( k7_relat_1(sK1,sK2) = k7_relat_1(k7_relat_1(sK0,sK3),sK2)
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_7 ),
    inference(forward_demodulation,[],[f52,f26])).

fof(f26,plain,
    ( k7_relat_1(sK0,sK3) = k7_relat_1(sK1,sK3)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f24])).

fof(f52,plain,
    ( k7_relat_1(sK1,sK2) = k7_relat_1(k7_relat_1(sK1,sK3),sK2)
    | ~ spl4_4
    | ~ spl4_7 ),
    inference(resolution,[],[f50,f36])).

fof(f36,plain,
    ( v1_relat_1(sK1)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f34])).

fof(f51,plain,
    ( spl4_7
    | ~ spl4_3
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f47,f44,f29,f49])).

fof(f29,plain,
    ( spl4_3
  <=> r1_tarski(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f44,plain,
    ( spl4_6
  <=> ! [X1,X0,X2] :
        ( k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0)
        | ~ r1_tarski(X0,X1)
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f47,plain,
    ( ! [X0] :
        ( k7_relat_1(k7_relat_1(X0,sK3),sK2) = k7_relat_1(X0,sK2)
        | ~ v1_relat_1(X0) )
    | ~ spl4_3
    | ~ spl4_6 ),
    inference(resolution,[],[f45,f31])).

fof(f31,plain,
    ( r1_tarski(sK2,sK3)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f29])).

fof(f45,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0)
        | ~ v1_relat_1(X2) )
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f44])).

fof(f46,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f17,f44])).

fof(f17,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_relat_1)).

fof(f42,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f12,f39])).

fof(f12,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,
    ( k7_relat_1(sK0,sK2) != k7_relat_1(sK1,sK2)
    & k7_relat_1(sK0,sK3) = k7_relat_1(sK1,sK3)
    & r1_tarski(sK2,sK3)
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f5,f10,f9,f8])).

fof(f8,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2,X3] :
                ( k7_relat_1(X0,X2) != k7_relat_1(X1,X2)
                & k7_relat_1(X0,X3) = k7_relat_1(X1,X3)
                & r1_tarski(X2,X3) )
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ? [X3,X2] :
              ( k7_relat_1(X1,X2) != k7_relat_1(sK0,X2)
              & k7_relat_1(X1,X3) = k7_relat_1(sK0,X3)
              & r1_tarski(X2,X3) )
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,
    ( ? [X1] :
        ( ? [X3,X2] :
            ( k7_relat_1(X1,X2) != k7_relat_1(sK0,X2)
            & k7_relat_1(X1,X3) = k7_relat_1(sK0,X3)
            & r1_tarski(X2,X3) )
        & v1_relat_1(X1) )
   => ( ? [X3,X2] :
          ( k7_relat_1(sK0,X2) != k7_relat_1(sK1,X2)
          & k7_relat_1(sK0,X3) = k7_relat_1(sK1,X3)
          & r1_tarski(X2,X3) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,
    ( ? [X3,X2] :
        ( k7_relat_1(sK0,X2) != k7_relat_1(sK1,X2)
        & k7_relat_1(sK0,X3) = k7_relat_1(sK1,X3)
        & r1_tarski(X2,X3) )
   => ( k7_relat_1(sK0,sK2) != k7_relat_1(sK1,sK2)
      & k7_relat_1(sK0,sK3) = k7_relat_1(sK1,sK3)
      & r1_tarski(sK2,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f5,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2,X3] :
              ( k7_relat_1(X0,X2) != k7_relat_1(X1,X2)
              & k7_relat_1(X0,X3) = k7_relat_1(X1,X3)
              & r1_tarski(X2,X3) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f4])).

fof(f4,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2,X3] :
              ( k7_relat_1(X0,X2) != k7_relat_1(X1,X2)
              & k7_relat_1(X0,X3) = k7_relat_1(X1,X3)
              & r1_tarski(X2,X3) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ! [X2,X3] :
                ( ( k7_relat_1(X0,X3) = k7_relat_1(X1,X3)
                  & r1_tarski(X2,X3) )
               => k7_relat_1(X0,X2) = k7_relat_1(X1,X2) ) ) ) ),
    inference(negated_conjecture,[],[f2])).

fof(f2,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2,X3] :
              ( ( k7_relat_1(X0,X3) = k7_relat_1(X1,X3)
                & r1_tarski(X2,X3) )
             => k7_relat_1(X0,X2) = k7_relat_1(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t188_relat_1)).

fof(f37,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f13,f34])).

fof(f13,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f32,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f14,f29])).

fof(f14,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f11])).

fof(f27,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f15,f24])).

fof(f15,plain,(
    k7_relat_1(sK0,sK3) = k7_relat_1(sK1,sK3) ),
    inference(cnf_transformation,[],[f11])).

fof(f22,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f16,f19])).

fof(f16,plain,(
    k7_relat_1(sK0,sK2) != k7_relat_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:36:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.22/0.43  % (15992)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.22/0.44  % (15990)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.22/0.44  % (15990)Refutation found. Thanks to Tanya!
% 0.22/0.44  % SZS status Theorem for theBenchmark
% 0.22/0.44  % SZS output start Proof for theBenchmark
% 0.22/0.44  fof(f68,plain,(
% 0.22/0.44    $false),
% 0.22/0.44    inference(avatar_sat_refutation,[],[f22,f27,f32,f37,f42,f46,f51,f59,f64,f67])).
% 0.22/0.44  fof(f67,plain,(
% 0.22/0.44    spl4_1 | ~spl4_8 | ~spl4_9),
% 0.22/0.44    inference(avatar_contradiction_clause,[],[f66])).
% 0.22/0.44  fof(f66,plain,(
% 0.22/0.44    $false | (spl4_1 | ~spl4_8 | ~spl4_9)),
% 0.22/0.44    inference(subsumption_resolution,[],[f65,f21])).
% 0.22/0.44  fof(f21,plain,(
% 0.22/0.44    k7_relat_1(sK0,sK2) != k7_relat_1(sK1,sK2) | spl4_1),
% 0.22/0.44    inference(avatar_component_clause,[],[f19])).
% 0.22/0.44  fof(f19,plain,(
% 0.22/0.44    spl4_1 <=> k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.22/0.44  fof(f65,plain,(
% 0.22/0.44    k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2) | (~spl4_8 | ~spl4_9)),
% 0.22/0.44    inference(forward_demodulation,[],[f58,f63])).
% 0.22/0.44  fof(f63,plain,(
% 0.22/0.44    k7_relat_1(sK0,sK2) = k7_relat_1(k7_relat_1(sK0,sK3),sK2) | ~spl4_9),
% 0.22/0.44    inference(avatar_component_clause,[],[f61])).
% 0.22/0.44  fof(f61,plain,(
% 0.22/0.44    spl4_9 <=> k7_relat_1(sK0,sK2) = k7_relat_1(k7_relat_1(sK0,sK3),sK2)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.22/0.44  fof(f58,plain,(
% 0.22/0.44    k7_relat_1(sK1,sK2) = k7_relat_1(k7_relat_1(sK0,sK3),sK2) | ~spl4_8),
% 0.22/0.44    inference(avatar_component_clause,[],[f56])).
% 0.22/0.44  fof(f56,plain,(
% 0.22/0.44    spl4_8 <=> k7_relat_1(sK1,sK2) = k7_relat_1(k7_relat_1(sK0,sK3),sK2)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.22/0.44  fof(f64,plain,(
% 0.22/0.44    spl4_9 | ~spl4_5 | ~spl4_7),
% 0.22/0.44    inference(avatar_split_clause,[],[f53,f49,f39,f61])).
% 0.22/0.44  fof(f39,plain,(
% 0.22/0.44    spl4_5 <=> v1_relat_1(sK0)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.22/0.44  fof(f49,plain,(
% 0.22/0.44    spl4_7 <=> ! [X0] : (k7_relat_1(k7_relat_1(X0,sK3),sK2) = k7_relat_1(X0,sK2) | ~v1_relat_1(X0))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.22/0.44  fof(f53,plain,(
% 0.22/0.44    k7_relat_1(sK0,sK2) = k7_relat_1(k7_relat_1(sK0,sK3),sK2) | (~spl4_5 | ~spl4_7)),
% 0.22/0.44    inference(resolution,[],[f50,f41])).
% 0.22/0.44  % (15991)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.22/0.44  fof(f41,plain,(
% 0.22/0.44    v1_relat_1(sK0) | ~spl4_5),
% 0.22/0.44    inference(avatar_component_clause,[],[f39])).
% 0.22/0.44  fof(f50,plain,(
% 0.22/0.44    ( ! [X0] : (~v1_relat_1(X0) | k7_relat_1(k7_relat_1(X0,sK3),sK2) = k7_relat_1(X0,sK2)) ) | ~spl4_7),
% 0.22/0.44    inference(avatar_component_clause,[],[f49])).
% 0.22/0.44  fof(f59,plain,(
% 0.22/0.44    spl4_8 | ~spl4_2 | ~spl4_4 | ~spl4_7),
% 0.22/0.44    inference(avatar_split_clause,[],[f54,f49,f34,f24,f56])).
% 0.22/0.44  fof(f24,plain,(
% 0.22/0.44    spl4_2 <=> k7_relat_1(sK0,sK3) = k7_relat_1(sK1,sK3)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.22/0.44  fof(f34,plain,(
% 0.22/0.44    spl4_4 <=> v1_relat_1(sK1)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.22/0.44  fof(f54,plain,(
% 0.22/0.44    k7_relat_1(sK1,sK2) = k7_relat_1(k7_relat_1(sK0,sK3),sK2) | (~spl4_2 | ~spl4_4 | ~spl4_7)),
% 0.22/0.44    inference(forward_demodulation,[],[f52,f26])).
% 0.22/0.44  fof(f26,plain,(
% 0.22/0.44    k7_relat_1(sK0,sK3) = k7_relat_1(sK1,sK3) | ~spl4_2),
% 0.22/0.44    inference(avatar_component_clause,[],[f24])).
% 0.22/0.44  fof(f52,plain,(
% 0.22/0.44    k7_relat_1(sK1,sK2) = k7_relat_1(k7_relat_1(sK1,sK3),sK2) | (~spl4_4 | ~spl4_7)),
% 0.22/0.44    inference(resolution,[],[f50,f36])).
% 0.22/0.44  fof(f36,plain,(
% 0.22/0.44    v1_relat_1(sK1) | ~spl4_4),
% 0.22/0.44    inference(avatar_component_clause,[],[f34])).
% 0.22/0.44  fof(f51,plain,(
% 0.22/0.44    spl4_7 | ~spl4_3 | ~spl4_6),
% 0.22/0.44    inference(avatar_split_clause,[],[f47,f44,f29,f49])).
% 0.22/0.44  fof(f29,plain,(
% 0.22/0.44    spl4_3 <=> r1_tarski(sK2,sK3)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.22/0.45  fof(f44,plain,(
% 0.22/0.45    spl4_6 <=> ! [X1,X0,X2] : (k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.22/0.45  fof(f47,plain,(
% 0.22/0.45    ( ! [X0] : (k7_relat_1(k7_relat_1(X0,sK3),sK2) = k7_relat_1(X0,sK2) | ~v1_relat_1(X0)) ) | (~spl4_3 | ~spl4_6)),
% 0.22/0.45    inference(resolution,[],[f45,f31])).
% 0.22/0.45  fof(f31,plain,(
% 0.22/0.45    r1_tarski(sK2,sK3) | ~spl4_3),
% 0.22/0.45    inference(avatar_component_clause,[],[f29])).
% 0.22/0.45  fof(f45,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0) | ~v1_relat_1(X2)) ) | ~spl4_6),
% 0.22/0.45    inference(avatar_component_clause,[],[f44])).
% 0.22/0.45  fof(f46,plain,(
% 0.22/0.45    spl4_6),
% 0.22/0.45    inference(avatar_split_clause,[],[f17,f44])).
% 0.22/0.45  fof(f17,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f7])).
% 0.22/0.45  fof(f7,plain,(
% 0.22/0.45    ! [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 0.22/0.45    inference(flattening,[],[f6])).
% 0.22/0.45  fof(f6,plain,(
% 0.22/0.45    ! [X0,X1,X2] : ((k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 0.22/0.45    inference(ennf_transformation,[],[f1])).
% 0.22/0.45  fof(f1,axiom,(
% 0.22/0.45    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0)))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_relat_1)).
% 0.22/0.45  fof(f42,plain,(
% 0.22/0.45    spl4_5),
% 0.22/0.45    inference(avatar_split_clause,[],[f12,f39])).
% 0.22/0.45  fof(f12,plain,(
% 0.22/0.45    v1_relat_1(sK0)),
% 0.22/0.45    inference(cnf_transformation,[],[f11])).
% 0.22/0.45  fof(f11,plain,(
% 0.22/0.45    ((k7_relat_1(sK0,sK2) != k7_relat_1(sK1,sK2) & k7_relat_1(sK0,sK3) = k7_relat_1(sK1,sK3) & r1_tarski(sK2,sK3)) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 0.22/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f5,f10,f9,f8])).
% 0.22/0.45  fof(f8,plain,(
% 0.22/0.45    ? [X0] : (? [X1] : (? [X2,X3] : (k7_relat_1(X0,X2) != k7_relat_1(X1,X2) & k7_relat_1(X0,X3) = k7_relat_1(X1,X3) & r1_tarski(X2,X3)) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (? [X3,X2] : (k7_relat_1(X1,X2) != k7_relat_1(sK0,X2) & k7_relat_1(X1,X3) = k7_relat_1(sK0,X3) & r1_tarski(X2,X3)) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 0.22/0.45    introduced(choice_axiom,[])).
% 0.22/0.45  fof(f9,plain,(
% 0.22/0.45    ? [X1] : (? [X3,X2] : (k7_relat_1(X1,X2) != k7_relat_1(sK0,X2) & k7_relat_1(X1,X3) = k7_relat_1(sK0,X3) & r1_tarski(X2,X3)) & v1_relat_1(X1)) => (? [X3,X2] : (k7_relat_1(sK0,X2) != k7_relat_1(sK1,X2) & k7_relat_1(sK0,X3) = k7_relat_1(sK1,X3) & r1_tarski(X2,X3)) & v1_relat_1(sK1))),
% 0.22/0.45    introduced(choice_axiom,[])).
% 0.22/0.45  fof(f10,plain,(
% 0.22/0.45    ? [X3,X2] : (k7_relat_1(sK0,X2) != k7_relat_1(sK1,X2) & k7_relat_1(sK0,X3) = k7_relat_1(sK1,X3) & r1_tarski(X2,X3)) => (k7_relat_1(sK0,sK2) != k7_relat_1(sK1,sK2) & k7_relat_1(sK0,sK3) = k7_relat_1(sK1,sK3) & r1_tarski(sK2,sK3))),
% 0.22/0.45    introduced(choice_axiom,[])).
% 0.22/0.45  fof(f5,plain,(
% 0.22/0.45    ? [X0] : (? [X1] : (? [X2,X3] : (k7_relat_1(X0,X2) != k7_relat_1(X1,X2) & k7_relat_1(X0,X3) = k7_relat_1(X1,X3) & r1_tarski(X2,X3)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.22/0.45    inference(flattening,[],[f4])).
% 0.22/0.45  fof(f4,plain,(
% 0.22/0.45    ? [X0] : (? [X1] : (? [X2,X3] : (k7_relat_1(X0,X2) != k7_relat_1(X1,X2) & (k7_relat_1(X0,X3) = k7_relat_1(X1,X3) & r1_tarski(X2,X3))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.22/0.45    inference(ennf_transformation,[],[f3])).
% 0.22/0.45  fof(f3,negated_conjecture,(
% 0.22/0.45    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2,X3] : ((k7_relat_1(X0,X3) = k7_relat_1(X1,X3) & r1_tarski(X2,X3)) => k7_relat_1(X0,X2) = k7_relat_1(X1,X2))))),
% 0.22/0.45    inference(negated_conjecture,[],[f2])).
% 0.22/0.45  fof(f2,conjecture,(
% 0.22/0.45    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2,X3] : ((k7_relat_1(X0,X3) = k7_relat_1(X1,X3) & r1_tarski(X2,X3)) => k7_relat_1(X0,X2) = k7_relat_1(X1,X2))))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t188_relat_1)).
% 0.22/0.45  fof(f37,plain,(
% 0.22/0.45    spl4_4),
% 0.22/0.45    inference(avatar_split_clause,[],[f13,f34])).
% 0.22/0.45  fof(f13,plain,(
% 0.22/0.45    v1_relat_1(sK1)),
% 0.22/0.45    inference(cnf_transformation,[],[f11])).
% 0.22/0.45  fof(f32,plain,(
% 0.22/0.45    spl4_3),
% 0.22/0.45    inference(avatar_split_clause,[],[f14,f29])).
% 0.22/0.45  fof(f14,plain,(
% 0.22/0.45    r1_tarski(sK2,sK3)),
% 0.22/0.45    inference(cnf_transformation,[],[f11])).
% 0.22/0.45  fof(f27,plain,(
% 0.22/0.45    spl4_2),
% 0.22/0.45    inference(avatar_split_clause,[],[f15,f24])).
% 0.22/0.45  fof(f15,plain,(
% 0.22/0.45    k7_relat_1(sK0,sK3) = k7_relat_1(sK1,sK3)),
% 0.22/0.45    inference(cnf_transformation,[],[f11])).
% 0.22/0.45  fof(f22,plain,(
% 0.22/0.45    ~spl4_1),
% 0.22/0.45    inference(avatar_split_clause,[],[f16,f19])).
% 0.22/0.45  fof(f16,plain,(
% 0.22/0.45    k7_relat_1(sK0,sK2) != k7_relat_1(sK1,sK2)),
% 0.22/0.45    inference(cnf_transformation,[],[f11])).
% 0.22/0.45  % SZS output end Proof for theBenchmark
% 0.22/0.45  % (15990)------------------------------
% 0.22/0.45  % (15990)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.45  % (15990)Termination reason: Refutation
% 0.22/0.45  
% 0.22/0.45  % (15990)Memory used [KB]: 10490
% 0.22/0.45  % (15990)Time elapsed: 0.005 s
% 0.22/0.45  % (15990)------------------------------
% 0.22/0.45  % (15990)------------------------------
% 0.22/0.45  % (15984)Success in time 0.089 s
%------------------------------------------------------------------------------
