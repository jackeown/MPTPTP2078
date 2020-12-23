%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:20:08 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   52 (  92 expanded)
%              Number of leaves         :   13 (  37 expanded)
%              Depth                    :    7
%              Number of atoms          :  157 ( 359 expanded)
%              Number of equality atoms :   12 (  50 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f66,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f25,f30,f35,f40,f45,f49,f53,f61,f65])).

fof(f65,plain,
    ( ~ spl2_2
    | ~ spl2_5
    | ~ spl2_7
    | spl2_8 ),
    inference(avatar_contradiction_clause,[],[f64])).

fof(f64,plain,
    ( $false
    | ~ spl2_2
    | ~ spl2_5
    | ~ spl2_7
    | spl2_8 ),
    inference(subsumption_resolution,[],[f63,f60])).

fof(f60,plain,
    ( ~ v1_zfmisc_1(u1_struct_0(sK0))
    | spl2_8 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl2_8
  <=> v1_zfmisc_1(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f63,plain,
    ( v1_zfmisc_1(u1_struct_0(sK0))
    | ~ spl2_2
    | ~ spl2_5
    | ~ spl2_7 ),
    inference(subsumption_resolution,[],[f62,f44])).

fof(f44,plain,
    ( l1_struct_0(sK0)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f42])).

fof(f42,plain,
    ( spl2_5
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f62,plain,
    ( ~ l1_struct_0(sK0)
    | v1_zfmisc_1(u1_struct_0(sK0))
    | ~ spl2_2
    | ~ spl2_7 ),
    inference(resolution,[],[f52,f29])).

fof(f29,plain,
    ( v7_struct_0(sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f27])).

fof(f27,plain,
    ( spl2_2
  <=> v7_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f52,plain,
    ( ! [X0] :
        ( ~ v7_struct_0(X0)
        | ~ l1_struct_0(X0)
        | v1_zfmisc_1(u1_struct_0(X0)) )
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f51])).

fof(f51,plain,
    ( spl2_7
  <=> ! [X0] :
        ( v1_zfmisc_1(u1_struct_0(X0))
        | ~ l1_struct_0(X0)
        | ~ v7_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f61,plain,
    ( ~ spl2_8
    | spl2_1
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f56,f47,f37,f32,f22,f58])).

fof(f22,plain,
    ( spl2_1
  <=> v7_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f32,plain,
    ( spl2_3
  <=> u1_struct_0(sK0) = u1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f37,plain,
    ( spl2_4
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f47,plain,
    ( spl2_6
  <=> ! [X0] :
        ( ~ v1_zfmisc_1(u1_struct_0(X0))
        | ~ l1_struct_0(X0)
        | v7_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f56,plain,
    ( ~ v1_zfmisc_1(u1_struct_0(sK0))
    | spl2_1
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_6 ),
    inference(subsumption_resolution,[],[f55,f24])).

fof(f24,plain,
    ( ~ v7_struct_0(sK1)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f22])).

fof(f55,plain,
    ( ~ v1_zfmisc_1(u1_struct_0(sK0))
    | v7_struct_0(sK1)
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_6 ),
    inference(subsumption_resolution,[],[f54,f39])).

fof(f39,plain,
    ( l1_struct_0(sK1)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f37])).

fof(f54,plain,
    ( ~ v1_zfmisc_1(u1_struct_0(sK0))
    | ~ l1_struct_0(sK1)
    | v7_struct_0(sK1)
    | ~ spl2_3
    | ~ spl2_6 ),
    inference(superposition,[],[f48,f34])).

fof(f34,plain,
    ( u1_struct_0(sK0) = u1_struct_0(sK1)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f32])).

fof(f48,plain,
    ( ! [X0] :
        ( ~ v1_zfmisc_1(u1_struct_0(X0))
        | ~ l1_struct_0(X0)
        | v7_struct_0(X0) )
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f47])).

fof(f53,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f20,f51])).

fof(f20,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v7_struct_0(X0) )
     => v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_struct_0)).

fof(f49,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f19,f47])).

fof(f19,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v7_struct_0(X0) )
     => ~ v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_struct_0)).

fof(f45,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f14,f42])).

fof(f14,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( ~ v7_struct_0(sK1)
    & v7_struct_0(sK0)
    & u1_struct_0(sK0) = u1_struct_0(sK1)
    & l1_struct_0(sK1)
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f6,f12,f11])).

fof(f11,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v7_struct_0(X1)
            & v7_struct_0(X0)
            & u1_struct_0(X0) = u1_struct_0(X1)
            & l1_struct_0(X1) )
        & l1_struct_0(X0) )
   => ( ? [X1] :
          ( ~ v7_struct_0(X1)
          & v7_struct_0(sK0)
          & u1_struct_0(X1) = u1_struct_0(sK0)
          & l1_struct_0(X1) )
      & l1_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,
    ( ? [X1] :
        ( ~ v7_struct_0(X1)
        & v7_struct_0(sK0)
        & u1_struct_0(X1) = u1_struct_0(sK0)
        & l1_struct_0(X1) )
   => ( ~ v7_struct_0(sK1)
      & v7_struct_0(sK0)
      & u1_struct_0(sK0) = u1_struct_0(sK1)
      & l1_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v7_struct_0(X1)
          & v7_struct_0(X0)
          & u1_struct_0(X0) = u1_struct_0(X1)
          & l1_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v7_struct_0(X1)
          & v7_struct_0(X0)
          & u1_struct_0(X0) = u1_struct_0(X1)
          & l1_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( l1_struct_0(X1)
           => ( ( v7_struct_0(X0)
                & u1_struct_0(X0) = u1_struct_0(X1) )
             => v7_struct_0(X1) ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ( ( v7_struct_0(X0)
              & u1_struct_0(X0) = u1_struct_0(X1) )
           => v7_struct_0(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_tex_2)).

fof(f40,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f15,f37])).

fof(f15,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f35,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f16,f32])).

fof(f16,plain,(
    u1_struct_0(sK0) = u1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f30,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f17,f27])).

fof(f17,plain,(
    v7_struct_0(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f25,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f18,f22])).

fof(f18,plain,(
    ~ v7_struct_0(sK1) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 17:20:51 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.41  % (18082)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.21/0.42  % (18081)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.21/0.42  % (18080)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.21/0.42  % (18080)Refutation found. Thanks to Tanya!
% 0.21/0.42  % SZS status Theorem for theBenchmark
% 0.21/0.42  % SZS output start Proof for theBenchmark
% 0.21/0.42  fof(f66,plain,(
% 0.21/0.42    $false),
% 0.21/0.42    inference(avatar_sat_refutation,[],[f25,f30,f35,f40,f45,f49,f53,f61,f65])).
% 0.21/0.42  fof(f65,plain,(
% 0.21/0.42    ~spl2_2 | ~spl2_5 | ~spl2_7 | spl2_8),
% 0.21/0.42    inference(avatar_contradiction_clause,[],[f64])).
% 0.21/0.42  fof(f64,plain,(
% 0.21/0.42    $false | (~spl2_2 | ~spl2_5 | ~spl2_7 | spl2_8)),
% 0.21/0.42    inference(subsumption_resolution,[],[f63,f60])).
% 0.21/0.42  fof(f60,plain,(
% 0.21/0.42    ~v1_zfmisc_1(u1_struct_0(sK0)) | spl2_8),
% 0.21/0.42    inference(avatar_component_clause,[],[f58])).
% 0.21/0.42  fof(f58,plain,(
% 0.21/0.42    spl2_8 <=> v1_zfmisc_1(u1_struct_0(sK0))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.21/0.42  fof(f63,plain,(
% 0.21/0.42    v1_zfmisc_1(u1_struct_0(sK0)) | (~spl2_2 | ~spl2_5 | ~spl2_7)),
% 0.21/0.42    inference(subsumption_resolution,[],[f62,f44])).
% 0.21/0.42  fof(f44,plain,(
% 0.21/0.42    l1_struct_0(sK0) | ~spl2_5),
% 0.21/0.42    inference(avatar_component_clause,[],[f42])).
% 0.21/0.42  fof(f42,plain,(
% 0.21/0.42    spl2_5 <=> l1_struct_0(sK0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.42  fof(f62,plain,(
% 0.21/0.42    ~l1_struct_0(sK0) | v1_zfmisc_1(u1_struct_0(sK0)) | (~spl2_2 | ~spl2_7)),
% 0.21/0.42    inference(resolution,[],[f52,f29])).
% 0.21/0.42  fof(f29,plain,(
% 0.21/0.42    v7_struct_0(sK0) | ~spl2_2),
% 0.21/0.42    inference(avatar_component_clause,[],[f27])).
% 0.21/0.42  fof(f27,plain,(
% 0.21/0.42    spl2_2 <=> v7_struct_0(sK0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.42  fof(f52,plain,(
% 0.21/0.42    ( ! [X0] : (~v7_struct_0(X0) | ~l1_struct_0(X0) | v1_zfmisc_1(u1_struct_0(X0))) ) | ~spl2_7),
% 0.21/0.42    inference(avatar_component_clause,[],[f51])).
% 0.21/0.42  fof(f51,plain,(
% 0.21/0.42    spl2_7 <=> ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.21/0.42  fof(f61,plain,(
% 0.21/0.42    ~spl2_8 | spl2_1 | ~spl2_3 | ~spl2_4 | ~spl2_6),
% 0.21/0.42    inference(avatar_split_clause,[],[f56,f47,f37,f32,f22,f58])).
% 0.21/0.42  fof(f22,plain,(
% 0.21/0.42    spl2_1 <=> v7_struct_0(sK1)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.42  fof(f32,plain,(
% 0.21/0.42    spl2_3 <=> u1_struct_0(sK0) = u1_struct_0(sK1)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.42  fof(f37,plain,(
% 0.21/0.42    spl2_4 <=> l1_struct_0(sK1)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.42  fof(f47,plain,(
% 0.21/0.42    spl2_6 <=> ! [X0] : (~v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | v7_struct_0(X0))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.42  fof(f56,plain,(
% 0.21/0.42    ~v1_zfmisc_1(u1_struct_0(sK0)) | (spl2_1 | ~spl2_3 | ~spl2_4 | ~spl2_6)),
% 0.21/0.42    inference(subsumption_resolution,[],[f55,f24])).
% 0.21/0.42  fof(f24,plain,(
% 0.21/0.42    ~v7_struct_0(sK1) | spl2_1),
% 0.21/0.42    inference(avatar_component_clause,[],[f22])).
% 0.21/0.42  fof(f55,plain,(
% 0.21/0.42    ~v1_zfmisc_1(u1_struct_0(sK0)) | v7_struct_0(sK1) | (~spl2_3 | ~spl2_4 | ~spl2_6)),
% 0.21/0.42    inference(subsumption_resolution,[],[f54,f39])).
% 0.21/0.42  fof(f39,plain,(
% 0.21/0.42    l1_struct_0(sK1) | ~spl2_4),
% 0.21/0.42    inference(avatar_component_clause,[],[f37])).
% 0.21/0.42  fof(f54,plain,(
% 0.21/0.42    ~v1_zfmisc_1(u1_struct_0(sK0)) | ~l1_struct_0(sK1) | v7_struct_0(sK1) | (~spl2_3 | ~spl2_6)),
% 0.21/0.42    inference(superposition,[],[f48,f34])).
% 0.21/0.42  fof(f34,plain,(
% 0.21/0.42    u1_struct_0(sK0) = u1_struct_0(sK1) | ~spl2_3),
% 0.21/0.42    inference(avatar_component_clause,[],[f32])).
% 0.21/0.42  fof(f48,plain,(
% 0.21/0.42    ( ! [X0] : (~v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | v7_struct_0(X0)) ) | ~spl2_6),
% 0.21/0.42    inference(avatar_component_clause,[],[f47])).
% 0.21/0.42  fof(f53,plain,(
% 0.21/0.42    spl2_7),
% 0.21/0.42    inference(avatar_split_clause,[],[f20,f51])).
% 0.21/0.42  fof(f20,plain,(
% 0.21/0.42    ( ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f10])).
% 0.21/0.42  fof(f10,plain,(
% 0.21/0.42    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0))),
% 0.21/0.42    inference(flattening,[],[f9])).
% 0.21/0.42  fof(f9,plain,(
% 0.21/0.42    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | (~l1_struct_0(X0) | ~v7_struct_0(X0)))),
% 0.21/0.42    inference(ennf_transformation,[],[f2])).
% 0.21/0.42  fof(f2,axiom,(
% 0.21/0.42    ! [X0] : ((l1_struct_0(X0) & v7_struct_0(X0)) => v1_zfmisc_1(u1_struct_0(X0)))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_struct_0)).
% 0.21/0.42  fof(f49,plain,(
% 0.21/0.42    spl2_6),
% 0.21/0.42    inference(avatar_split_clause,[],[f19,f47])).
% 0.21/0.42  fof(f19,plain,(
% 0.21/0.42    ( ! [X0] : (~v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | v7_struct_0(X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f8])).
% 0.21/0.42  fof(f8,plain,(
% 0.21/0.42    ! [X0] : (~v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | v7_struct_0(X0))),
% 0.21/0.42    inference(flattening,[],[f7])).
% 0.21/0.42  fof(f7,plain,(
% 0.21/0.42    ! [X0] : (~v1_zfmisc_1(u1_struct_0(X0)) | (~l1_struct_0(X0) | v7_struct_0(X0)))),
% 0.21/0.42    inference(ennf_transformation,[],[f1])).
% 0.21/0.42  fof(f1,axiom,(
% 0.21/0.42    ! [X0] : ((l1_struct_0(X0) & ~v7_struct_0(X0)) => ~v1_zfmisc_1(u1_struct_0(X0)))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_struct_0)).
% 0.21/0.42  fof(f45,plain,(
% 0.21/0.42    spl2_5),
% 0.21/0.42    inference(avatar_split_clause,[],[f14,f42])).
% 0.21/0.42  fof(f14,plain,(
% 0.21/0.42    l1_struct_0(sK0)),
% 0.21/0.42    inference(cnf_transformation,[],[f13])).
% 0.21/0.42  fof(f13,plain,(
% 0.21/0.42    (~v7_struct_0(sK1) & v7_struct_0(sK0) & u1_struct_0(sK0) = u1_struct_0(sK1) & l1_struct_0(sK1)) & l1_struct_0(sK0)),
% 0.21/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f6,f12,f11])).
% 0.21/0.42  fof(f11,plain,(
% 0.21/0.42    ? [X0] : (? [X1] : (~v7_struct_0(X1) & v7_struct_0(X0) & u1_struct_0(X0) = u1_struct_0(X1) & l1_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (~v7_struct_0(X1) & v7_struct_0(sK0) & u1_struct_0(X1) = u1_struct_0(sK0) & l1_struct_0(X1)) & l1_struct_0(sK0))),
% 0.21/0.42    introduced(choice_axiom,[])).
% 0.21/0.42  fof(f12,plain,(
% 0.21/0.42    ? [X1] : (~v7_struct_0(X1) & v7_struct_0(sK0) & u1_struct_0(X1) = u1_struct_0(sK0) & l1_struct_0(X1)) => (~v7_struct_0(sK1) & v7_struct_0(sK0) & u1_struct_0(sK0) = u1_struct_0(sK1) & l1_struct_0(sK1))),
% 0.21/0.42    introduced(choice_axiom,[])).
% 0.21/0.42  fof(f6,plain,(
% 0.21/0.42    ? [X0] : (? [X1] : (~v7_struct_0(X1) & v7_struct_0(X0) & u1_struct_0(X0) = u1_struct_0(X1) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 0.21/0.42    inference(flattening,[],[f5])).
% 0.21/0.42  fof(f5,plain,(
% 0.21/0.42    ? [X0] : (? [X1] : ((~v7_struct_0(X1) & (v7_struct_0(X0) & u1_struct_0(X0) = u1_struct_0(X1))) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 0.21/0.42    inference(ennf_transformation,[],[f4])).
% 0.21/0.42  fof(f4,negated_conjecture,(
% 0.21/0.42    ~! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ((v7_struct_0(X0) & u1_struct_0(X0) = u1_struct_0(X1)) => v7_struct_0(X1))))),
% 0.21/0.42    inference(negated_conjecture,[],[f3])).
% 0.21/0.42  fof(f3,conjecture,(
% 0.21/0.42    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ((v7_struct_0(X0) & u1_struct_0(X0) = u1_struct_0(X1)) => v7_struct_0(X1))))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_tex_2)).
% 0.21/0.42  fof(f40,plain,(
% 0.21/0.42    spl2_4),
% 0.21/0.42    inference(avatar_split_clause,[],[f15,f37])).
% 0.21/0.42  fof(f15,plain,(
% 0.21/0.42    l1_struct_0(sK1)),
% 0.21/0.42    inference(cnf_transformation,[],[f13])).
% 0.21/0.42  fof(f35,plain,(
% 0.21/0.42    spl2_3),
% 0.21/0.42    inference(avatar_split_clause,[],[f16,f32])).
% 0.21/0.42  fof(f16,plain,(
% 0.21/0.42    u1_struct_0(sK0) = u1_struct_0(sK1)),
% 0.21/0.42    inference(cnf_transformation,[],[f13])).
% 0.21/0.42  fof(f30,plain,(
% 0.21/0.42    spl2_2),
% 0.21/0.42    inference(avatar_split_clause,[],[f17,f27])).
% 0.21/0.42  fof(f17,plain,(
% 0.21/0.42    v7_struct_0(sK0)),
% 0.21/0.42    inference(cnf_transformation,[],[f13])).
% 0.21/0.42  fof(f25,plain,(
% 0.21/0.42    ~spl2_1),
% 0.21/0.42    inference(avatar_split_clause,[],[f18,f22])).
% 0.21/0.42  fof(f18,plain,(
% 0.21/0.42    ~v7_struct_0(sK1)),
% 0.21/0.42    inference(cnf_transformation,[],[f13])).
% 0.21/0.42  % SZS output end Proof for theBenchmark
% 0.21/0.42  % (18080)------------------------------
% 0.21/0.42  % (18080)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.42  % (18080)Termination reason: Refutation
% 0.21/0.42  
% 0.21/0.42  % (18080)Memory used [KB]: 10490
% 0.21/0.42  % (18080)Time elapsed: 0.006 s
% 0.21/0.42  % (18080)------------------------------
% 0.21/0.42  % (18080)------------------------------
% 0.21/0.42  % (18074)Success in time 0.063 s
%------------------------------------------------------------------------------
