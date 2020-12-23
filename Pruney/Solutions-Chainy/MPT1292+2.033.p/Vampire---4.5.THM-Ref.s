%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:13:15 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 123 expanded)
%              Number of leaves         :   21 (  52 expanded)
%              Depth                    :    8
%              Number of atoms          :  200 ( 368 expanded)
%              Number of equality atoms :   17 (  51 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f103,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f33,f38,f43,f48,f53,f57,f61,f65,f69,f75,f80,f86,f98,f102])).

fof(f102,plain,
    ( ~ spl2_3
    | spl2_4
    | ~ spl2_7
    | ~ spl2_14 ),
    inference(avatar_contradiction_clause,[],[f101])).

fof(f101,plain,
    ( $false
    | ~ spl2_3
    | spl2_4
    | ~ spl2_7
    | ~ spl2_14 ),
    inference(subsumption_resolution,[],[f100,f47])).

fof(f47,plain,
    ( ~ v2_struct_0(sK0)
    | spl2_4 ),
    inference(avatar_component_clause,[],[f45])).

fof(f45,plain,
    ( spl2_4
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f100,plain,
    ( v2_struct_0(sK0)
    | ~ spl2_3
    | ~ spl2_7
    | ~ spl2_14 ),
    inference(subsumption_resolution,[],[f99,f42])).

fof(f42,plain,
    ( l1_struct_0(sK0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f40])).

fof(f40,plain,
    ( spl2_3
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f99,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl2_7
    | ~ spl2_14 ),
    inference(resolution,[],[f97,f60])).

fof(f60,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(u1_struct_0(X0))
        | ~ l1_struct_0(X0)
        | v2_struct_0(X0) )
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl2_7
  <=> ! [X0] :
        ( ~ v1_xboole_0(u1_struct_0(X0))
        | ~ l1_struct_0(X0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f97,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl2_14
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f98,plain,
    ( spl2_14
    | ~ spl2_6
    | ~ spl2_8
    | ~ spl2_12 ),
    inference(avatar_split_clause,[],[f93,f83,f63,f55,f95])).

fof(f55,plain,
    ( spl2_6
  <=> ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f63,plain,
    ( spl2_8
  <=> ! [X1,X0] :
        ( ~ r1_xboole_0(X1,X0)
        | ~ r1_tarski(X1,X0)
        | v1_xboole_0(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f83,plain,
    ( spl2_12
  <=> r1_tarski(u1_struct_0(sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f93,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl2_6
    | ~ spl2_8
    | ~ spl2_12 ),
    inference(subsumption_resolution,[],[f88,f56])).

fof(f56,plain,
    ( ! [X0] : r1_xboole_0(X0,k1_xboole_0)
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f55])).

fof(f88,plain,
    ( ~ r1_xboole_0(u1_struct_0(sK0),k1_xboole_0)
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl2_8
    | ~ spl2_12 ),
    inference(resolution,[],[f64,f85])).

fof(f85,plain,
    ( r1_tarski(u1_struct_0(sK0),k1_xboole_0)
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f83])).

fof(f64,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X1,X0)
        | ~ r1_xboole_0(X1,X0)
        | v1_xboole_0(X1) )
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f63])).

fof(f86,plain,
    ( spl2_12
    | ~ spl2_10
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f81,f78,f72,f83])).

fof(f72,plain,
    ( spl2_10
  <=> m1_setfam_1(k1_xboole_0,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f78,plain,
    ( spl2_11
  <=> ! [X0] :
        ( r1_tarski(X0,k1_xboole_0)
        | ~ m1_setfam_1(k1_xboole_0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f81,plain,
    ( r1_tarski(u1_struct_0(sK0),k1_xboole_0)
    | ~ spl2_10
    | ~ spl2_11 ),
    inference(resolution,[],[f79,f74])).

fof(f74,plain,
    ( m1_setfam_1(k1_xboole_0,u1_struct_0(sK0))
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f72])).

fof(f79,plain,
    ( ! [X0] :
        ( ~ m1_setfam_1(k1_xboole_0,X0)
        | r1_tarski(X0,k1_xboole_0) )
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f78])).

fof(f80,plain,
    ( spl2_11
    | ~ spl2_5
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f76,f67,f50,f78])).

fof(f50,plain,
    ( spl2_5
  <=> k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f67,plain,
    ( spl2_9
  <=> ! [X1,X0] :
        ( r1_tarski(X0,k3_tarski(X1))
        | ~ m1_setfam_1(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f76,plain,
    ( ! [X0] :
        ( r1_tarski(X0,k1_xboole_0)
        | ~ m1_setfam_1(k1_xboole_0,X0) )
    | ~ spl2_5
    | ~ spl2_9 ),
    inference(superposition,[],[f68,f52])).

fof(f52,plain,
    ( k1_xboole_0 = k3_tarski(k1_xboole_0)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f50])).

fof(f68,plain,
    ( ! [X0,X1] :
        ( r1_tarski(X0,k3_tarski(X1))
        | ~ m1_setfam_1(X1,X0) )
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f67])).

fof(f75,plain,
    ( spl2_10
    | ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f70,f35,f30,f72])).

fof(f30,plain,
    ( spl2_1
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f35,plain,
    ( spl2_2
  <=> m1_setfam_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f70,plain,
    ( m1_setfam_1(k1_xboole_0,u1_struct_0(sK0))
    | ~ spl2_1
    | ~ spl2_2 ),
    inference(backward_demodulation,[],[f37,f32])).

fof(f32,plain,
    ( k1_xboole_0 = sK1
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f30])).

fof(f37,plain,
    ( m1_setfam_1(sK1,u1_struct_0(sK0))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f35])).

fof(f69,plain,(
    spl2_9 ),
    inference(avatar_split_clause,[],[f28,f67])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ m1_setfam_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ m1_setfam_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( m1_setfam_1(X1,X0)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    inference(unused_predicate_definition_removal,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_setfam_1(X1,X0)
    <=> r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_setfam_1)).

fof(f65,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f27,f63])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

fof(f61,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f26,f59])).

fof(f26,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f57,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f25,f55])).

fof(f25,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f53,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f24,f50])).

fof(f24,plain,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_zfmisc_1)).

fof(f48,plain,(
    ~ spl2_4 ),
    inference(avatar_split_clause,[],[f20,f45])).

fof(f20,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( k1_xboole_0 = sK1
    & m1_setfam_1(sK1,u1_struct_0(sK0))
    & l1_struct_0(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f18,f17])).

fof(f17,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k1_xboole_0 = X1
            & m1_setfam_1(X1,u1_struct_0(X0)) )
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( k1_xboole_0 = X1
          & m1_setfam_1(X1,u1_struct_0(sK0)) )
      & l1_struct_0(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X1] :
        ( k1_xboole_0 = X1
        & m1_setfam_1(X1,u1_struct_0(sK0)) )
   => ( k1_xboole_0 = sK1
      & m1_setfam_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 = X1
          & m1_setfam_1(X1,u1_struct_0(X0)) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 = X1
          & m1_setfam_1(X1,u1_struct_0(X0)) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,plain,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ~ ( k1_xboole_0 = X1
              & m1_setfam_1(X1,u1_struct_0(X0)) ) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ~ ( k1_xboole_0 = X1
                & m1_setfam_1(X1,u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ~ ( k1_xboole_0 = X1
              & m1_setfam_1(X1,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_tops_2)).

fof(f43,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f21,f40])).

fof(f21,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f38,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f22,f35])).

fof(f22,plain,(
    m1_setfam_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f33,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f23,f30])).

fof(f23,plain,(
    k1_xboole_0 = sK1 ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:29:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.40  % (3839)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.19/0.41  % (3838)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.19/0.42  % (3840)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.19/0.43  % (3842)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 0.19/0.43  % (3842)Refutation found. Thanks to Tanya!
% 0.19/0.43  % SZS status Theorem for theBenchmark
% 0.19/0.43  % SZS output start Proof for theBenchmark
% 0.19/0.43  fof(f103,plain,(
% 0.19/0.43    $false),
% 0.19/0.43    inference(avatar_sat_refutation,[],[f33,f38,f43,f48,f53,f57,f61,f65,f69,f75,f80,f86,f98,f102])).
% 0.19/0.43  fof(f102,plain,(
% 0.19/0.43    ~spl2_3 | spl2_4 | ~spl2_7 | ~spl2_14),
% 0.19/0.43    inference(avatar_contradiction_clause,[],[f101])).
% 0.19/0.43  fof(f101,plain,(
% 0.19/0.43    $false | (~spl2_3 | spl2_4 | ~spl2_7 | ~spl2_14)),
% 0.19/0.43    inference(subsumption_resolution,[],[f100,f47])).
% 0.19/0.43  fof(f47,plain,(
% 0.19/0.43    ~v2_struct_0(sK0) | spl2_4),
% 0.19/0.43    inference(avatar_component_clause,[],[f45])).
% 0.19/0.43  fof(f45,plain,(
% 0.19/0.43    spl2_4 <=> v2_struct_0(sK0)),
% 0.19/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.19/0.43  fof(f100,plain,(
% 0.19/0.43    v2_struct_0(sK0) | (~spl2_3 | ~spl2_7 | ~spl2_14)),
% 0.19/0.43    inference(subsumption_resolution,[],[f99,f42])).
% 0.19/0.43  fof(f42,plain,(
% 0.19/0.43    l1_struct_0(sK0) | ~spl2_3),
% 0.19/0.43    inference(avatar_component_clause,[],[f40])).
% 0.19/0.43  fof(f40,plain,(
% 0.19/0.43    spl2_3 <=> l1_struct_0(sK0)),
% 0.19/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.19/0.43  fof(f99,plain,(
% 0.19/0.43    ~l1_struct_0(sK0) | v2_struct_0(sK0) | (~spl2_7 | ~spl2_14)),
% 0.19/0.43    inference(resolution,[],[f97,f60])).
% 0.19/0.43  fof(f60,plain,(
% 0.19/0.43    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) ) | ~spl2_7),
% 0.19/0.43    inference(avatar_component_clause,[],[f59])).
% 0.19/0.43  fof(f59,plain,(
% 0.19/0.43    spl2_7 <=> ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.19/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.19/0.43  fof(f97,plain,(
% 0.19/0.43    v1_xboole_0(u1_struct_0(sK0)) | ~spl2_14),
% 0.19/0.43    inference(avatar_component_clause,[],[f95])).
% 0.19/0.43  fof(f95,plain,(
% 0.19/0.43    spl2_14 <=> v1_xboole_0(u1_struct_0(sK0))),
% 0.19/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.19/0.43  fof(f98,plain,(
% 0.19/0.43    spl2_14 | ~spl2_6 | ~spl2_8 | ~spl2_12),
% 0.19/0.43    inference(avatar_split_clause,[],[f93,f83,f63,f55,f95])).
% 0.19/0.43  fof(f55,plain,(
% 0.19/0.43    spl2_6 <=> ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.19/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.19/0.43  fof(f63,plain,(
% 0.19/0.43    spl2_8 <=> ! [X1,X0] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 0.19/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.19/0.43  fof(f83,plain,(
% 0.19/0.43    spl2_12 <=> r1_tarski(u1_struct_0(sK0),k1_xboole_0)),
% 0.19/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.19/0.43  fof(f93,plain,(
% 0.19/0.43    v1_xboole_0(u1_struct_0(sK0)) | (~spl2_6 | ~spl2_8 | ~spl2_12)),
% 0.19/0.43    inference(subsumption_resolution,[],[f88,f56])).
% 0.19/0.43  fof(f56,plain,(
% 0.19/0.43    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) ) | ~spl2_6),
% 0.19/0.43    inference(avatar_component_clause,[],[f55])).
% 0.19/0.43  fof(f88,plain,(
% 0.19/0.43    ~r1_xboole_0(u1_struct_0(sK0),k1_xboole_0) | v1_xboole_0(u1_struct_0(sK0)) | (~spl2_8 | ~spl2_12)),
% 0.19/0.43    inference(resolution,[],[f64,f85])).
% 0.19/0.43  fof(f85,plain,(
% 0.19/0.43    r1_tarski(u1_struct_0(sK0),k1_xboole_0) | ~spl2_12),
% 0.19/0.43    inference(avatar_component_clause,[],[f83])).
% 0.19/0.43  fof(f64,plain,(
% 0.19/0.43    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_xboole_0(X1,X0) | v1_xboole_0(X1)) ) | ~spl2_8),
% 0.19/0.43    inference(avatar_component_clause,[],[f63])).
% 0.19/0.43  fof(f86,plain,(
% 0.19/0.43    spl2_12 | ~spl2_10 | ~spl2_11),
% 0.19/0.43    inference(avatar_split_clause,[],[f81,f78,f72,f83])).
% 0.19/0.43  fof(f72,plain,(
% 0.19/0.43    spl2_10 <=> m1_setfam_1(k1_xboole_0,u1_struct_0(sK0))),
% 0.19/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.19/0.43  fof(f78,plain,(
% 0.19/0.43    spl2_11 <=> ! [X0] : (r1_tarski(X0,k1_xboole_0) | ~m1_setfam_1(k1_xboole_0,X0))),
% 0.19/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.19/0.43  fof(f81,plain,(
% 0.19/0.43    r1_tarski(u1_struct_0(sK0),k1_xboole_0) | (~spl2_10 | ~spl2_11)),
% 0.19/0.43    inference(resolution,[],[f79,f74])).
% 0.19/0.43  fof(f74,plain,(
% 0.19/0.43    m1_setfam_1(k1_xboole_0,u1_struct_0(sK0)) | ~spl2_10),
% 0.19/0.43    inference(avatar_component_clause,[],[f72])).
% 0.19/0.43  fof(f79,plain,(
% 0.19/0.43    ( ! [X0] : (~m1_setfam_1(k1_xboole_0,X0) | r1_tarski(X0,k1_xboole_0)) ) | ~spl2_11),
% 0.19/0.43    inference(avatar_component_clause,[],[f78])).
% 0.19/0.43  fof(f80,plain,(
% 0.19/0.43    spl2_11 | ~spl2_5 | ~spl2_9),
% 0.19/0.43    inference(avatar_split_clause,[],[f76,f67,f50,f78])).
% 0.19/0.43  fof(f50,plain,(
% 0.19/0.43    spl2_5 <=> k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 0.19/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.19/0.43  fof(f67,plain,(
% 0.19/0.43    spl2_9 <=> ! [X1,X0] : (r1_tarski(X0,k3_tarski(X1)) | ~m1_setfam_1(X1,X0))),
% 0.19/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.19/0.43  fof(f76,plain,(
% 0.19/0.43    ( ! [X0] : (r1_tarski(X0,k1_xboole_0) | ~m1_setfam_1(k1_xboole_0,X0)) ) | (~spl2_5 | ~spl2_9)),
% 0.19/0.43    inference(superposition,[],[f68,f52])).
% 0.19/0.43  fof(f52,plain,(
% 0.19/0.43    k1_xboole_0 = k3_tarski(k1_xboole_0) | ~spl2_5),
% 0.19/0.43    inference(avatar_component_clause,[],[f50])).
% 0.19/0.43  fof(f68,plain,(
% 0.19/0.43    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~m1_setfam_1(X1,X0)) ) | ~spl2_9),
% 0.19/0.43    inference(avatar_component_clause,[],[f67])).
% 0.19/0.43  fof(f75,plain,(
% 0.19/0.43    spl2_10 | ~spl2_1 | ~spl2_2),
% 0.19/0.43    inference(avatar_split_clause,[],[f70,f35,f30,f72])).
% 0.19/0.43  fof(f30,plain,(
% 0.19/0.43    spl2_1 <=> k1_xboole_0 = sK1),
% 0.19/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.19/0.43  fof(f35,plain,(
% 0.19/0.43    spl2_2 <=> m1_setfam_1(sK1,u1_struct_0(sK0))),
% 0.19/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.19/0.43  fof(f70,plain,(
% 0.19/0.43    m1_setfam_1(k1_xboole_0,u1_struct_0(sK0)) | (~spl2_1 | ~spl2_2)),
% 0.19/0.43    inference(backward_demodulation,[],[f37,f32])).
% 0.19/0.43  fof(f32,plain,(
% 0.19/0.43    k1_xboole_0 = sK1 | ~spl2_1),
% 0.19/0.43    inference(avatar_component_clause,[],[f30])).
% 0.19/0.43  fof(f37,plain,(
% 0.19/0.43    m1_setfam_1(sK1,u1_struct_0(sK0)) | ~spl2_2),
% 0.19/0.43    inference(avatar_component_clause,[],[f35])).
% 0.19/0.43  fof(f69,plain,(
% 0.19/0.43    spl2_9),
% 0.19/0.43    inference(avatar_split_clause,[],[f28,f67])).
% 0.19/0.43  fof(f28,plain,(
% 0.19/0.43    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~m1_setfam_1(X1,X0)) )),
% 0.19/0.43    inference(cnf_transformation,[],[f16])).
% 0.19/0.43  fof(f16,plain,(
% 0.19/0.43    ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~m1_setfam_1(X1,X0))),
% 0.19/0.43    inference(ennf_transformation,[],[f8])).
% 0.19/0.43  fof(f8,plain,(
% 0.19/0.43    ! [X0,X1] : (m1_setfam_1(X1,X0) => r1_tarski(X0,k3_tarski(X1)))),
% 0.19/0.43    inference(unused_predicate_definition_removal,[],[f4])).
% 0.19/0.43  fof(f4,axiom,(
% 0.19/0.43    ! [X0,X1] : (m1_setfam_1(X1,X0) <=> r1_tarski(X0,k3_tarski(X1)))),
% 0.19/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_setfam_1)).
% 0.19/0.43  fof(f65,plain,(
% 0.19/0.43    spl2_8),
% 0.19/0.43    inference(avatar_split_clause,[],[f27,f63])).
% 0.19/0.43  fof(f27,plain,(
% 0.19/0.43    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)) )),
% 0.19/0.43    inference(cnf_transformation,[],[f15])).
% 0.19/0.43  fof(f15,plain,(
% 0.19/0.43    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 0.19/0.43    inference(flattening,[],[f14])).
% 0.19/0.43  fof(f14,plain,(
% 0.19/0.43    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 0.19/0.43    inference(ennf_transformation,[],[f2])).
% 0.19/0.43  fof(f2,axiom,(
% 0.19/0.43    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 0.19/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).
% 0.19/0.43  fof(f61,plain,(
% 0.19/0.43    spl2_7),
% 0.19/0.43    inference(avatar_split_clause,[],[f26,f59])).
% 0.19/0.43  fof(f26,plain,(
% 0.19/0.43    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.19/0.43    inference(cnf_transformation,[],[f13])).
% 0.19/0.43  fof(f13,plain,(
% 0.19/0.43    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.19/0.43    inference(flattening,[],[f12])).
% 0.19/0.43  fof(f12,plain,(
% 0.19/0.43    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.19/0.43    inference(ennf_transformation,[],[f5])).
% 0.19/0.43  fof(f5,axiom,(
% 0.19/0.43    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.19/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.19/0.43  fof(f57,plain,(
% 0.19/0.43    spl2_6),
% 0.19/0.43    inference(avatar_split_clause,[],[f25,f55])).
% 0.19/0.43  fof(f25,plain,(
% 0.19/0.43    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.19/0.43    inference(cnf_transformation,[],[f1])).
% 0.19/0.43  fof(f1,axiom,(
% 0.19/0.43    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.19/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.19/0.43  fof(f53,plain,(
% 0.19/0.43    spl2_5),
% 0.19/0.43    inference(avatar_split_clause,[],[f24,f50])).
% 0.19/0.43  fof(f24,plain,(
% 0.19/0.43    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 0.19/0.43    inference(cnf_transformation,[],[f3])).
% 0.19/0.43  fof(f3,axiom,(
% 0.19/0.43    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 0.19/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_zfmisc_1)).
% 0.19/0.43  fof(f48,plain,(
% 0.19/0.43    ~spl2_4),
% 0.19/0.43    inference(avatar_split_clause,[],[f20,f45])).
% 0.19/0.43  fof(f20,plain,(
% 0.19/0.43    ~v2_struct_0(sK0)),
% 0.19/0.43    inference(cnf_transformation,[],[f19])).
% 0.19/0.43  fof(f19,plain,(
% 0.19/0.43    (k1_xboole_0 = sK1 & m1_setfam_1(sK1,u1_struct_0(sK0))) & l1_struct_0(sK0) & ~v2_struct_0(sK0)),
% 0.19/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f18,f17])).
% 0.19/0.43  fof(f17,plain,(
% 0.19/0.43    ? [X0] : (? [X1] : (k1_xboole_0 = X1 & m1_setfam_1(X1,u1_struct_0(X0))) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (? [X1] : (k1_xboole_0 = X1 & m1_setfam_1(X1,u1_struct_0(sK0))) & l1_struct_0(sK0) & ~v2_struct_0(sK0))),
% 0.19/0.43    introduced(choice_axiom,[])).
% 0.19/0.43  fof(f18,plain,(
% 0.19/0.43    ? [X1] : (k1_xboole_0 = X1 & m1_setfam_1(X1,u1_struct_0(sK0))) => (k1_xboole_0 = sK1 & m1_setfam_1(sK1,u1_struct_0(sK0)))),
% 0.19/0.43    introduced(choice_axiom,[])).
% 0.19/0.43  fof(f11,plain,(
% 0.19/0.43    ? [X0] : (? [X1] : (k1_xboole_0 = X1 & m1_setfam_1(X1,u1_struct_0(X0))) & l1_struct_0(X0) & ~v2_struct_0(X0))),
% 0.19/0.43    inference(flattening,[],[f10])).
% 0.19/0.43  fof(f10,plain,(
% 0.19/0.43    ? [X0] : (? [X1] : (k1_xboole_0 = X1 & m1_setfam_1(X1,u1_struct_0(X0))) & (l1_struct_0(X0) & ~v2_struct_0(X0)))),
% 0.19/0.43    inference(ennf_transformation,[],[f9])).
% 0.19/0.43  fof(f9,plain,(
% 0.19/0.43    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ~(k1_xboole_0 = X1 & m1_setfam_1(X1,u1_struct_0(X0))))),
% 0.19/0.43    inference(pure_predicate_removal,[],[f7])).
% 0.19/0.43  fof(f7,negated_conjecture,(
% 0.19/0.43    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ~(k1_xboole_0 = X1 & m1_setfam_1(X1,u1_struct_0(X0)))))),
% 0.19/0.43    inference(negated_conjecture,[],[f6])).
% 0.19/0.43  fof(f6,conjecture,(
% 0.19/0.43    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ~(k1_xboole_0 = X1 & m1_setfam_1(X1,u1_struct_0(X0)))))),
% 0.19/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_tops_2)).
% 0.19/0.43  fof(f43,plain,(
% 0.19/0.43    spl2_3),
% 0.19/0.43    inference(avatar_split_clause,[],[f21,f40])).
% 0.19/0.43  fof(f21,plain,(
% 0.19/0.43    l1_struct_0(sK0)),
% 0.19/0.43    inference(cnf_transformation,[],[f19])).
% 0.19/0.43  fof(f38,plain,(
% 0.19/0.43    spl2_2),
% 0.19/0.43    inference(avatar_split_clause,[],[f22,f35])).
% 0.19/0.43  fof(f22,plain,(
% 0.19/0.43    m1_setfam_1(sK1,u1_struct_0(sK0))),
% 0.19/0.43    inference(cnf_transformation,[],[f19])).
% 0.19/0.43  fof(f33,plain,(
% 0.19/0.43    spl2_1),
% 0.19/0.43    inference(avatar_split_clause,[],[f23,f30])).
% 0.19/0.43  fof(f23,plain,(
% 0.19/0.43    k1_xboole_0 = sK1),
% 0.19/0.43    inference(cnf_transformation,[],[f19])).
% 0.19/0.43  % SZS output end Proof for theBenchmark
% 0.19/0.43  % (3842)------------------------------
% 0.19/0.43  % (3842)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.43  % (3842)Termination reason: Refutation
% 0.19/0.43  
% 0.19/0.43  % (3842)Memory used [KB]: 6140
% 0.19/0.43  % (3842)Time elapsed: 0.027 s
% 0.19/0.43  % (3842)------------------------------
% 0.19/0.43  % (3842)------------------------------
% 0.19/0.43  % (3836)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.19/0.43  % (3837)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.19/0.43  % (3831)Success in time 0.082 s
%------------------------------------------------------------------------------
