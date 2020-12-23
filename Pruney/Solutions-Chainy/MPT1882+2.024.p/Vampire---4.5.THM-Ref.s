%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:03 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 370 expanded)
%              Number of leaves         :   22 ( 112 expanded)
%              Depth                    :   18
%              Number of atoms          :  506 (2573 expanded)
%              Number of equality atoms :   33 (  65 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f350,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f82,f83,f192,f202,f204,f329,f340,f344,f349])).

fof(f349,plain,
    ( spl7_7
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f347,f189,f119])).

fof(f119,plain,
    ( spl7_7
  <=> v2_tex_2(sK4,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f189,plain,
    ( spl7_10
  <=> sP1(sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f347,plain,
    ( v2_tex_2(sK4,sK3)
    | ~ spl7_10 ),
    inference(resolution,[],[f191,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,X1)
      | v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ~ sP0(X1,X0)
        | ~ v2_tex_2(X1,X0) )
      & ( ( sP0(X1,X0)
          & v2_tex_2(X1,X0) )
        | ~ sP1(X0,X1) ) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ~ sP0(X1,X0)
        | ~ v2_tex_2(X1,X0) )
      & ( ( sP0(X1,X0)
          & v2_tex_2(X1,X0) )
        | ~ sP1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
    <=> ( sP0(X1,X0)
        & v2_tex_2(X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f191,plain,
    ( sP1(sK3,sK4)
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f189])).

fof(f344,plain,
    ( spl7_2
    | ~ spl7_7 ),
    inference(avatar_split_clause,[],[f343,f119,f79])).

fof(f79,plain,
    ( spl7_2
  <=> v1_zfmisc_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f343,plain,
    ( ~ v2_tex_2(sK4,sK3)
    | v1_zfmisc_1(sK4) ),
    inference(subsumption_resolution,[],[f342,f46])).

fof(f46,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,
    ( ( ~ v1_zfmisc_1(sK4)
      | ~ v3_tex_2(sK4,sK3) )
    & ( v1_zfmisc_1(sK4)
      | v3_tex_2(sK4,sK3) )
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    & ~ v1_xboole_0(sK4)
    & l1_pre_topc(sK3)
    & v2_tdlat_3(sK3)
    & v2_pre_topc(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f31,f33,f32])).

fof(f32,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ v1_zfmisc_1(X1)
              | ~ v3_tex_2(X1,X0) )
            & ( v1_zfmisc_1(X1)
              | v3_tex_2(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
        & l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ~ v1_zfmisc_1(X1)
            | ~ v3_tex_2(X1,sK3) )
          & ( v1_zfmisc_1(X1)
            | v3_tex_2(X1,sK3) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(sK3)
      & v2_tdlat_3(sK3)
      & v2_pre_topc(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X1] :
        ( ( ~ v1_zfmisc_1(X1)
          | ~ v3_tex_2(X1,sK3) )
        & ( v1_zfmisc_1(X1)
          | v3_tex_2(X1,sK3) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
        & ~ v1_xboole_0(X1) )
   => ( ( ~ v1_zfmisc_1(sK4)
        | ~ v3_tex_2(sK4,sK3) )
      & ( v1_zfmisc_1(sK4)
        | v3_tex_2(sK4,sK3) )
      & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
      & ~ v1_xboole_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_zfmisc_1(X1)
            | ~ v3_tex_2(X1,X0) )
          & ( v1_zfmisc_1(X1)
            | v3_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_zfmisc_1(X1)
            | ~ v3_tex_2(X1,X0) )
          & ( v1_zfmisc_1(X1)
            | v3_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tex_2(X1,X0)
          <~> v1_zfmisc_1(X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tex_2(X1,X0)
          <~> v1_zfmisc_1(X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & ~ v1_xboole_0(X1) )
           => ( v3_tex_2(X1,X0)
            <=> v1_zfmisc_1(X1) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ( v3_tex_2(X1,X0)
          <=> v1_zfmisc_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_tex_2)).

fof(f342,plain,
    ( ~ v2_tex_2(sK4,sK3)
    | v1_zfmisc_1(sK4)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f341,f48])).

fof(f48,plain,(
    v2_tdlat_3(sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f341,plain,
    ( ~ v2_tex_2(sK4,sK3)
    | v1_zfmisc_1(sK4)
    | ~ v2_tdlat_3(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f238,f49])).

fof(f49,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f238,plain,
    ( ~ v2_tex_2(sK4,sK3)
    | v1_zfmisc_1(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_tdlat_3(sK3)
    | v2_struct_0(sK3) ),
    inference(resolution,[],[f220,f51])).

fof(f51,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f34])).

fof(f220,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | v1_zfmisc_1(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f219,f67])).

fof(f67,plain,(
    ! [X0] :
      ( v1_zfmisc_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( v1_zfmisc_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_zfmisc_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_zfmisc_1)).

fof(f219,plain,(
    ! [X0,X1] :
      ( v1_zfmisc_1(X1)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f68,f55])).

fof(f55,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_tdlat_3(X0)
       => v2_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tdlat_3)).

fof(f68,plain,(
    ! [X0,X1] :
      ( v1_zfmisc_1(X1)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ~ v1_zfmisc_1(X1) )
            & ( v1_zfmisc_1(X1)
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> v1_zfmisc_1(X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> v1_zfmisc_1(X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ( v2_tex_2(X1,X0)
          <=> v1_zfmisc_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tex_2)).

fof(f340,plain,
    ( spl7_7
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f339,f79,f119])).

fof(f339,plain,
    ( ~ v1_zfmisc_1(sK4)
    | v2_tex_2(sK4,sK3) ),
    inference(subsumption_resolution,[],[f338,f46])).

fof(f338,plain,
    ( ~ v1_zfmisc_1(sK4)
    | v2_tex_2(sK4,sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f337,f48])).

fof(f337,plain,
    ( ~ v1_zfmisc_1(sK4)
    | v2_tex_2(sK4,sK3)
    | ~ v2_tdlat_3(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f336,f49])).

fof(f336,plain,
    ( ~ v1_zfmisc_1(sK4)
    | v2_tex_2(sK4,sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v2_tdlat_3(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f299,f50])).

fof(f50,plain,(
    ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f34])).

fof(f299,plain,
    ( ~ v1_zfmisc_1(sK4)
    | v2_tex_2(sK4,sK3)
    | v1_xboole_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_tdlat_3(sK3)
    | v2_struct_0(sK3) ),
    inference(resolution,[],[f218,f51])).

fof(f218,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_zfmisc_1(X1)
      | v2_tex_2(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f69,f55])).

fof(f69,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | ~ v1_zfmisc_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f329,plain,(
    spl7_8 ),
    inference(avatar_contradiction_clause,[],[f328])).

fof(f328,plain,
    ( $false
    | spl7_8 ),
    inference(subsumption_resolution,[],[f327,f50])).

fof(f327,plain,
    ( v1_xboole_0(sK4)
    | spl7_8 ),
    inference(subsumption_resolution,[],[f326,f49])).

fof(f326,plain,
    ( ~ l1_pre_topc(sK3)
    | v1_xboole_0(sK4)
    | spl7_8 ),
    inference(subsumption_resolution,[],[f325,f46])).

fof(f325,plain,
    ( v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3)
    | v1_xboole_0(sK4)
    | spl7_8 ),
    inference(subsumption_resolution,[],[f319,f48])).

fof(f319,plain,
    ( ~ v2_tdlat_3(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3)
    | v1_xboole_0(sK4)
    | spl7_8 ),
    inference(resolution,[],[f316,f125])).

fof(f125,plain,
    ( ~ sP0(sK4,sK3)
    | spl7_8 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl7_8
  <=> sP0(sK4,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f316,plain,(
    ! [X0,X1] :
      ( sP0(X1,X0)
      | ~ v2_tdlat_3(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1) ) ),
    inference(duplicate_literal_removal,[],[f313])).

fof(f313,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | v2_struct_0(X0)
      | sP0(X1,X0)
      | v1_xboole_0(X1)
      | sP0(X1,X0) ) ),
    inference(resolution,[],[f248,f233])).

% (25624)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% (25638)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% (25636)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% (25642)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% (25640)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% (25633)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% (25626)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% (25644)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% (25646)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% (25643)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% (25641)Refutation not found, incomplete strategy% (25641)------------------------------
% (25641)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (25641)Termination reason: Refutation not found, incomplete strategy

% (25641)Memory used [KB]: 6268
% (25641)Time elapsed: 0.110 s
% (25641)------------------------------
% (25641)------------------------------
fof(f233,plain,(
    ! [X0,X1] :
      ( ~ v1_zfmisc_1(sK5(X0,X1))
      | v1_xboole_0(X0)
      | sP0(X0,X1) ) ),
    inference(subsumption_resolution,[],[f232,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( sK5(X0,X1) != X0
      | sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( sK5(X0,X1) != X0
          & r1_tarski(X0,sK5(X0,X1))
          & v2_tex_2(sK5(X0,X1),X1)
          & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) ) )
      & ( ! [X3] :
            ( X0 = X3
            | ~ r1_tarski(X0,X3)
            | ~ v2_tex_2(X3,X1)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f40,f41])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X0 != X2
          & r1_tarski(X0,X2)
          & v2_tex_2(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( sK5(X0,X1) != X0
        & r1_tarski(X0,sK5(X0,X1))
        & v2_tex_2(sK5(X0,X1),X1)
        & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( X0 != X2
            & r1_tarski(X0,X2)
            & v2_tex_2(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ) )
      & ( ! [X3] :
            ( X0 = X3
            | ~ r1_tarski(X0,X3)
            | ~ v2_tex_2(X3,X1)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f39])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ( sP0(X1,X0)
        | ? [X2] :
            ( X1 != X2
            & r1_tarski(X1,X2)
            & v2_tex_2(X2,X0)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ! [X2] :
            ( X1 = X2
            | ~ r1_tarski(X1,X2)
            | ~ v2_tex_2(X2,X0)
            | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP0(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X1,X0] :
      ( sP0(X1,X0)
    <=> ! [X2] :
          ( X1 = X2
          | ~ r1_tarski(X1,X2)
          | ~ v2_tex_2(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f232,plain,(
    ! [X0,X1] :
      ( sK5(X0,X1) = X0
      | ~ v1_zfmisc_1(sK5(X0,X1))
      | v1_xboole_0(X0)
      | sP0(X0,X1) ) ),
    inference(resolution,[],[f229,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,sK5(X0,X1))
      | sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f229,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | ~ v1_zfmisc_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f54,f116])).

fof(f116,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(trivial_inequality_removal,[],[f115])).

fof(f115,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k1_xboole_0
      | X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f72,f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k6_subset_1(X0,X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f87,f70])).

fof(f70,plain,(
    ! [X0] :
      ( r2_hidden(sK6(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f45])).

% (25632)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
fof(f45,plain,(
    ! [X0] :
      ( r2_hidden(sK6(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f23,f44])).

fof(f44,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK6(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f87,plain,(
    ! [X2,X3,X1] :
      ( ~ r2_hidden(X2,k6_subset_1(X1,X3))
      | ~ v1_xboole_0(X1) ) ),
    inference(resolution,[],[f73,f71])).

fof(f71,plain,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f72,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k6_subset_1(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k6_subset_1(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ~ ( k1_xboole_0 = k6_subset_1(X1,X0)
        & X0 != X1
        & r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l48_tex_2)).

fof(f54,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X0,X1)
      | ~ v1_zfmisc_1(X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

fof(f248,plain,(
    ! [X4,X3] :
      ( v1_zfmisc_1(sK5(X3,X4))
      | ~ l1_pre_topc(X4)
      | ~ v2_tdlat_3(X4)
      | v2_struct_0(X4)
      | sP0(X3,X4) ) ),
    inference(subsumption_resolution,[],[f239,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( v2_tex_2(sK5(X0,X1),X1)
      | sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f239,plain,(
    ! [X4,X3] :
      ( ~ v2_tex_2(sK5(X3,X4),X4)
      | v1_zfmisc_1(sK5(X3,X4))
      | ~ l1_pre_topc(X4)
      | ~ v2_tdlat_3(X4)
      | v2_struct_0(X4)
      | sP0(X3,X4) ) ),
    inference(resolution,[],[f220,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))
      | sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f204,plain,
    ( ~ spl7_7
    | ~ spl7_8
    | spl7_10 ),
    inference(avatar_split_clause,[],[f203,f189,f123,f119])).

fof(f203,plain,
    ( ~ sP0(sK4,sK3)
    | ~ v2_tex_2(sK4,sK3)
    | spl7_10 ),
    inference(resolution,[],[f190,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
      | ~ sP0(X1,X0)
      | ~ v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f190,plain,
    ( ~ sP1(sK3,sK4)
    | spl7_10 ),
    inference(avatar_component_clause,[],[f189])).

fof(f202,plain,
    ( ~ spl7_10
    | spl7_1 ),
    inference(avatar_split_clause,[],[f114,f75,f189])).

fof(f75,plain,
    ( spl7_1
  <=> v3_tex_2(sK4,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f114,plain,
    ( ~ sP1(sK3,sK4)
    | spl7_1 ),
    inference(subsumption_resolution,[],[f112,f77])).

fof(f77,plain,
    ( ~ v3_tex_2(sK4,sK3)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f75])).

fof(f112,plain,
    ( ~ sP1(sK3,sK4)
    | v3_tex_2(sK4,sK3) ),
    inference(resolution,[],[f111,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ sP2(X0,X1)
      | ~ sP1(X1,X0)
      | v3_tex_2(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( ( v3_tex_2(X0,X1)
          | ~ sP1(X1,X0) )
        & ( sP1(X1,X0)
          | ~ v3_tex_2(X0,X1) ) )
      | ~ sP2(X0,X1) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ( ( v3_tex_2(X1,X0)
          | ~ sP1(X0,X1) )
        & ( sP1(X0,X1)
          | ~ v3_tex_2(X1,X0) ) )
      | ~ sP2(X1,X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ( v3_tex_2(X1,X0)
      <=> sP1(X0,X1) )
      | ~ sP2(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f111,plain,(
    sP2(sK4,sK3) ),
    inference(subsumption_resolution,[],[f108,f49])).

fof(f108,plain,
    ( sP2(sK4,sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(resolution,[],[f66,f51])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | sP2(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f19,f28,f27,f26])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( X1 = X2
                  | ~ r1_tarski(X1,X2)
                  | ~ v2_tex_2(X2,X0)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( X1 = X2
                  | ~ r1_tarski(X1,X2)
                  | ~ v2_tex_2(X2,X0)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r1_tarski(X1,X2)
                      & v2_tex_2(X2,X0) )
                   => X1 = X2 ) )
              & v2_tex_2(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tex_2)).

fof(f192,plain,
    ( spl7_10
    | ~ spl7_1 ),
    inference(avatar_split_clause,[],[f113,f75,f189])).

fof(f113,plain,
    ( ~ v3_tex_2(sK4,sK3)
    | sP1(sK3,sK4) ),
    inference(resolution,[],[f111,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ sP2(X0,X1)
      | ~ v3_tex_2(X0,X1)
      | sP1(X1,X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f83,plain,
    ( spl7_1
    | spl7_2 ),
    inference(avatar_split_clause,[],[f52,f79,f75])).

fof(f52,plain,
    ( v1_zfmisc_1(sK4)
    | v3_tex_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f82,plain,
    ( ~ spl7_1
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f53,f79,f75])).

fof(f53,plain,
    ( ~ v1_zfmisc_1(sK4)
    | ~ v3_tex_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:11:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.22/0.46  % (25641)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.22/0.47  % (25625)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.47  % (25625)Refutation not found, incomplete strategy% (25625)------------------------------
% 0.22/0.47  % (25625)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (25625)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (25625)Memory used [KB]: 10618
% 0.22/0.48  % (25625)Time elapsed: 0.061 s
% 0.22/0.48  % (25625)------------------------------
% 0.22/0.48  % (25625)------------------------------
% 0.22/0.50  % (25639)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.50  % (25628)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.50  % (25631)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.50  % (25631)Refutation not found, incomplete strategy% (25631)------------------------------
% 0.22/0.50  % (25631)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (25631)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (25631)Memory used [KB]: 1663
% 0.22/0.50  % (25631)Time elapsed: 0.085 s
% 0.22/0.50  % (25631)------------------------------
% 0.22/0.50  % (25631)------------------------------
% 0.22/0.50  % (25647)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.51  % (25628)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f350,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(avatar_sat_refutation,[],[f82,f83,f192,f202,f204,f329,f340,f344,f349])).
% 0.22/0.51  fof(f349,plain,(
% 0.22/0.51    spl7_7 | ~spl7_10),
% 0.22/0.51    inference(avatar_split_clause,[],[f347,f189,f119])).
% 0.22/0.51  fof(f119,plain,(
% 0.22/0.51    spl7_7 <=> v2_tex_2(sK4,sK3)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.22/0.51  fof(f189,plain,(
% 0.22/0.51    spl7_10 <=> sP1(sK3,sK4)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 0.22/0.51  fof(f347,plain,(
% 0.22/0.51    v2_tex_2(sK4,sK3) | ~spl7_10),
% 0.22/0.51    inference(resolution,[],[f191,f58])).
% 0.22/0.51  fof(f58,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~sP1(X0,X1) | v2_tex_2(X1,X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f38])).
% 0.22/0.51  fof(f38,plain,(
% 0.22/0.51    ! [X0,X1] : ((sP1(X0,X1) | ~sP0(X1,X0) | ~v2_tex_2(X1,X0)) & ((sP0(X1,X0) & v2_tex_2(X1,X0)) | ~sP1(X0,X1)))),
% 0.22/0.51    inference(flattening,[],[f37])).
% 0.22/0.51  fof(f37,plain,(
% 0.22/0.51    ! [X0,X1] : ((sP1(X0,X1) | (~sP0(X1,X0) | ~v2_tex_2(X1,X0))) & ((sP0(X1,X0) & v2_tex_2(X1,X0)) | ~sP1(X0,X1)))),
% 0.22/0.51    inference(nnf_transformation,[],[f27])).
% 0.22/0.51  fof(f27,plain,(
% 0.22/0.51    ! [X0,X1] : (sP1(X0,X1) <=> (sP0(X1,X0) & v2_tex_2(X1,X0)))),
% 0.22/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.22/0.51  fof(f191,plain,(
% 0.22/0.51    sP1(sK3,sK4) | ~spl7_10),
% 0.22/0.51    inference(avatar_component_clause,[],[f189])).
% 0.22/0.51  fof(f344,plain,(
% 0.22/0.51    spl7_2 | ~spl7_7),
% 0.22/0.51    inference(avatar_split_clause,[],[f343,f119,f79])).
% 0.22/0.51  fof(f79,plain,(
% 0.22/0.51    spl7_2 <=> v1_zfmisc_1(sK4)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.22/0.51  fof(f343,plain,(
% 0.22/0.51    ~v2_tex_2(sK4,sK3) | v1_zfmisc_1(sK4)),
% 0.22/0.51    inference(subsumption_resolution,[],[f342,f46])).
% 0.22/0.51  fof(f46,plain,(
% 0.22/0.51    ~v2_struct_0(sK3)),
% 0.22/0.51    inference(cnf_transformation,[],[f34])).
% 0.22/0.51  fof(f34,plain,(
% 0.22/0.51    ((~v1_zfmisc_1(sK4) | ~v3_tex_2(sK4,sK3)) & (v1_zfmisc_1(sK4) | v3_tex_2(sK4,sK3)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) & ~v1_xboole_0(sK4)) & l1_pre_topc(sK3) & v2_tdlat_3(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f31,f33,f32])).
% 0.22/0.51  fof(f32,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,sK3)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,sK3)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) & ~v1_xboole_0(X1)) & l1_pre_topc(sK3) & v2_tdlat_3(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f33,plain,(
% 0.22/0.51    ? [X1] : ((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,sK3)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,sK3)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) & ~v1_xboole_0(X1)) => ((~v1_zfmisc_1(sK4) | ~v3_tex_2(sK4,sK3)) & (v1_zfmisc_1(sK4) | v3_tex_2(sK4,sK3)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) & ~v1_xboole_0(sK4))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f31,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f30])).
% 0.22/0.51  fof(f30,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.51    inference(nnf_transformation,[],[f13])).
% 0.22/0.51  fof(f13,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f12])).
% 0.22/0.51  fof(f12,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f11])).
% 0.22/0.51  fof(f11,negated_conjecture,(
% 0.22/0.51    ~! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v3_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 0.22/0.51    inference(negated_conjecture,[],[f10])).
% 0.22/0.51  fof(f10,conjecture,(
% 0.22/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v3_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_tex_2)).
% 0.22/0.51  fof(f342,plain,(
% 0.22/0.51    ~v2_tex_2(sK4,sK3) | v1_zfmisc_1(sK4) | v2_struct_0(sK3)),
% 0.22/0.51    inference(subsumption_resolution,[],[f341,f48])).
% 0.22/0.51  fof(f48,plain,(
% 0.22/0.51    v2_tdlat_3(sK3)),
% 0.22/0.51    inference(cnf_transformation,[],[f34])).
% 0.22/0.51  fof(f341,plain,(
% 0.22/0.51    ~v2_tex_2(sK4,sK3) | v1_zfmisc_1(sK4) | ~v2_tdlat_3(sK3) | v2_struct_0(sK3)),
% 0.22/0.51    inference(subsumption_resolution,[],[f238,f49])).
% 0.22/0.51  fof(f49,plain,(
% 0.22/0.51    l1_pre_topc(sK3)),
% 0.22/0.51    inference(cnf_transformation,[],[f34])).
% 0.22/0.51  fof(f238,plain,(
% 0.22/0.51    ~v2_tex_2(sK4,sK3) | v1_zfmisc_1(sK4) | ~l1_pre_topc(sK3) | ~v2_tdlat_3(sK3) | v2_struct_0(sK3)),
% 0.22/0.51    inference(resolution,[],[f220,f51])).
% 0.22/0.51  fof(f51,plain,(
% 0.22/0.51    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))),
% 0.22/0.51    inference(cnf_transformation,[],[f34])).
% 0.22/0.51  fof(f220,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | v1_zfmisc_1(X1) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | v2_struct_0(X0)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f219,f67])).
% 0.22/0.51  fof(f67,plain,(
% 0.22/0.51    ( ! [X0] : (v1_zfmisc_1(X0) | ~v1_xboole_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f20])).
% 0.22/0.51  fof(f20,plain,(
% 0.22/0.51    ! [X0] : (v1_zfmisc_1(X0) | ~v1_xboole_0(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f2])).
% 0.22/0.51  fof(f2,axiom,(
% 0.22/0.51    ! [X0] : (v1_xboole_0(X0) => v1_zfmisc_1(X0))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_zfmisc_1)).
% 0.22/0.51  fof(f219,plain,(
% 0.22/0.51    ( ! [X0,X1] : (v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | v2_struct_0(X0)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f68,f55])).
% 0.22/0.51  fof(f55,plain,(
% 0.22/0.51    ( ! [X0] : (v2_pre_topc(X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f17])).
% 0.22/0.51  fof(f17,plain,(
% 0.22/0.51    ! [X0] : (v2_pre_topc(X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(flattening,[],[f16])).
% 0.22/0.51  fof(f16,plain,(
% 0.22/0.51    ! [X0] : ((v2_pre_topc(X0) | ~v2_tdlat_3(X0)) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f5])).
% 0.22/0.51  fof(f5,axiom,(
% 0.22/0.51    ! [X0] : (l1_pre_topc(X0) => (v2_tdlat_3(X0) => v2_pre_topc(X0)))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tdlat_3)).
% 0.22/0.51  fof(f68,plain,(
% 0.22/0.51    ( ! [X0,X1] : (v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f43])).
% 0.22/0.51  fof(f43,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ~v1_zfmisc_1(X1)) & (v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(nnf_transformation,[],[f22])).
% 0.22/0.51  fof(f22,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f21])).
% 0.22/0.51  fof(f21,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f9])).
% 0.22/0.51  fof(f9,axiom,(
% 0.22/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tex_2)).
% 0.22/0.51  fof(f340,plain,(
% 0.22/0.51    spl7_7 | ~spl7_2),
% 0.22/0.51    inference(avatar_split_clause,[],[f339,f79,f119])).
% 0.22/0.51  fof(f339,plain,(
% 0.22/0.51    ~v1_zfmisc_1(sK4) | v2_tex_2(sK4,sK3)),
% 0.22/0.51    inference(subsumption_resolution,[],[f338,f46])).
% 0.22/0.51  fof(f338,plain,(
% 0.22/0.51    ~v1_zfmisc_1(sK4) | v2_tex_2(sK4,sK3) | v2_struct_0(sK3)),
% 0.22/0.51    inference(subsumption_resolution,[],[f337,f48])).
% 0.22/0.51  fof(f337,plain,(
% 0.22/0.51    ~v1_zfmisc_1(sK4) | v2_tex_2(sK4,sK3) | ~v2_tdlat_3(sK3) | v2_struct_0(sK3)),
% 0.22/0.51    inference(subsumption_resolution,[],[f336,f49])).
% 0.22/0.51  fof(f336,plain,(
% 0.22/0.51    ~v1_zfmisc_1(sK4) | v2_tex_2(sK4,sK3) | ~l1_pre_topc(sK3) | ~v2_tdlat_3(sK3) | v2_struct_0(sK3)),
% 0.22/0.51    inference(subsumption_resolution,[],[f299,f50])).
% 0.22/0.51  fof(f50,plain,(
% 0.22/0.51    ~v1_xboole_0(sK4)),
% 0.22/0.51    inference(cnf_transformation,[],[f34])).
% 0.22/0.51  fof(f299,plain,(
% 0.22/0.51    ~v1_zfmisc_1(sK4) | v2_tex_2(sK4,sK3) | v1_xboole_0(sK4) | ~l1_pre_topc(sK3) | ~v2_tdlat_3(sK3) | v2_struct_0(sK3)),
% 0.22/0.51    inference(resolution,[],[f218,f51])).
% 0.22/0.51  fof(f218,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_zfmisc_1(X1) | v2_tex_2(X1,X0) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | v2_struct_0(X0)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f69,f55])).
% 0.22/0.51  fof(f69,plain,(
% 0.22/0.51    ( ! [X0,X1] : (v2_tex_2(X1,X0) | ~v1_zfmisc_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f43])).
% 0.22/0.51  fof(f329,plain,(
% 0.22/0.51    spl7_8),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f328])).
% 0.22/0.51  fof(f328,plain,(
% 0.22/0.51    $false | spl7_8),
% 0.22/0.51    inference(subsumption_resolution,[],[f327,f50])).
% 0.22/0.51  fof(f327,plain,(
% 0.22/0.51    v1_xboole_0(sK4) | spl7_8),
% 0.22/0.51    inference(subsumption_resolution,[],[f326,f49])).
% 0.22/0.51  fof(f326,plain,(
% 0.22/0.51    ~l1_pre_topc(sK3) | v1_xboole_0(sK4) | spl7_8),
% 0.22/0.51    inference(subsumption_resolution,[],[f325,f46])).
% 0.22/0.51  fof(f325,plain,(
% 0.22/0.51    v2_struct_0(sK3) | ~l1_pre_topc(sK3) | v1_xboole_0(sK4) | spl7_8),
% 0.22/0.51    inference(subsumption_resolution,[],[f319,f48])).
% 0.22/0.51  fof(f319,plain,(
% 0.22/0.51    ~v2_tdlat_3(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK3) | v1_xboole_0(sK4) | spl7_8),
% 0.22/0.51    inference(resolution,[],[f316,f125])).
% 0.22/0.51  fof(f125,plain,(
% 0.22/0.51    ~sP0(sK4,sK3) | spl7_8),
% 0.22/0.51    inference(avatar_component_clause,[],[f123])).
% 0.22/0.51  fof(f123,plain,(
% 0.22/0.51    spl7_8 <=> sP0(sK4,sK3)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 0.22/0.51  fof(f316,plain,(
% 0.22/0.51    ( ! [X0,X1] : (sP0(X1,X0) | ~v2_tdlat_3(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | v1_xboole_0(X1)) )),
% 0.22/0.51    inference(duplicate_literal_removal,[],[f313])).
% 0.22/0.51  fof(f313,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | v2_struct_0(X0) | sP0(X1,X0) | v1_xboole_0(X1) | sP0(X1,X0)) )),
% 0.22/0.51    inference(resolution,[],[f248,f233])).
% 0.22/0.51  % (25624)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.51  % (25638)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.51  % (25636)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.51  % (25642)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.51  % (25640)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.22/0.51  % (25633)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.52  % (25626)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.52  % (25644)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.52  % (25646)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.52  % (25643)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.52  % (25641)Refutation not found, incomplete strategy% (25641)------------------------------
% 0.22/0.52  % (25641)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (25641)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (25641)Memory used [KB]: 6268
% 0.22/0.52  % (25641)Time elapsed: 0.110 s
% 0.22/0.52  % (25641)------------------------------
% 0.22/0.52  % (25641)------------------------------
% 0.22/0.52  fof(f233,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~v1_zfmisc_1(sK5(X0,X1)) | v1_xboole_0(X0) | sP0(X0,X1)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f232,f65])).
% 0.22/0.52  fof(f65,plain,(
% 0.22/0.52    ( ! [X0,X1] : (sK5(X0,X1) != X0 | sP0(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f42])).
% 0.22/0.52  fof(f42,plain,(
% 0.22/0.52    ! [X0,X1] : ((sP0(X0,X1) | (sK5(X0,X1) != X0 & r1_tarski(X0,sK5(X0,X1)) & v2_tex_2(sK5(X0,X1),X1) & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X1))))) & (! [X3] : (X0 = X3 | ~r1_tarski(X0,X3) | ~v2_tex_2(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~sP0(X0,X1)))),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f40,f41])).
% 0.22/0.52  fof(f41,plain,(
% 0.22/0.52    ! [X1,X0] : (? [X2] : (X0 != X2 & r1_tarski(X0,X2) & v2_tex_2(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) => (sK5(X0,X1) != X0 & r1_tarski(X0,sK5(X0,X1)) & v2_tex_2(sK5(X0,X1),X1) & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f40,plain,(
% 0.22/0.52    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : (X0 != X2 & r1_tarski(X0,X2) & v2_tex_2(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X3] : (X0 = X3 | ~r1_tarski(X0,X3) | ~v2_tex_2(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~sP0(X0,X1)))),
% 0.22/0.52    inference(rectify,[],[f39])).
% 0.22/0.52  fof(f39,plain,(
% 0.22/0.52    ! [X1,X0] : ((sP0(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP0(X1,X0)))),
% 0.22/0.52    inference(nnf_transformation,[],[f26])).
% 0.22/0.52  fof(f26,plain,(
% 0.22/0.52    ! [X1,X0] : (sP0(X1,X0) <=> ! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.22/0.52  fof(f232,plain,(
% 0.22/0.52    ( ! [X0,X1] : (sK5(X0,X1) = X0 | ~v1_zfmisc_1(sK5(X0,X1)) | v1_xboole_0(X0) | sP0(X0,X1)) )),
% 0.22/0.52    inference(resolution,[],[f229,f64])).
% 0.22/0.52  fof(f64,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r1_tarski(X0,sK5(X0,X1)) | sP0(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f42])).
% 0.22/0.52  fof(f229,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r1_tarski(X0,X1) | X0 = X1 | ~v1_zfmisc_1(X1) | v1_xboole_0(X0)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f54,f116])).
% 0.22/0.52  fof(f116,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 0.22/0.52    inference(trivial_inequality_removal,[],[f115])).
% 0.22/0.52  fof(f115,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k1_xboole_0 != k1_xboole_0 | X0 = X1 | ~r1_tarski(X1,X0) | ~v1_xboole_0(X0)) )),
% 0.22/0.52    inference(superposition,[],[f72,f97])).
% 0.22/0.52  fof(f97,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k1_xboole_0 = k6_subset_1(X0,X1) | ~v1_xboole_0(X0)) )),
% 0.22/0.52    inference(resolution,[],[f87,f70])).
% 0.22/0.52  fof(f70,plain,(
% 0.22/0.52    ( ! [X0] : (r2_hidden(sK6(X0),X0) | k1_xboole_0 = X0) )),
% 0.22/0.52    inference(cnf_transformation,[],[f45])).
% 0.22/0.52  % (25632)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.52  fof(f45,plain,(
% 0.22/0.52    ! [X0] : (r2_hidden(sK6(X0),X0) | k1_xboole_0 = X0)),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f23,f44])).
% 0.22/0.52  fof(f44,plain,(
% 0.22/0.52    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK6(X0),X0))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f23,plain,(
% 0.22/0.52    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.22/0.52    inference(ennf_transformation,[],[f1])).
% 0.22/0.52  fof(f1,axiom,(
% 0.22/0.52    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.22/0.52  fof(f87,plain,(
% 0.22/0.52    ( ! [X2,X3,X1] : (~r2_hidden(X2,k6_subset_1(X1,X3)) | ~v1_xboole_0(X1)) )),
% 0.22/0.52    inference(resolution,[],[f73,f71])).
% 0.22/0.52  fof(f71,plain,(
% 0.22/0.52    ( ! [X0,X1] : (m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f3])).
% 0.22/0.52  fof(f3,axiom,(
% 0.22/0.52    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).
% 0.22/0.52  fof(f73,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2) | ~r2_hidden(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f25])).
% 0.22/0.52  fof(f25,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.22/0.52    inference(ennf_transformation,[],[f4])).
% 0.22/0.52  fof(f4,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 0.22/0.52  fof(f72,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k1_xboole_0 != k6_subset_1(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f24])).
% 0.22/0.52  fof(f24,plain,(
% 0.22/0.52    ! [X0,X1] : (k1_xboole_0 != k6_subset_1(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1))),
% 0.22/0.52    inference(ennf_transformation,[],[f7])).
% 0.22/0.52  fof(f7,axiom,(
% 0.22/0.52    ! [X0,X1] : ~(k1_xboole_0 = k6_subset_1(X1,X0) & X0 != X1 & r1_tarski(X0,X1))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l48_tex_2)).
% 0.22/0.52  fof(f54,plain,(
% 0.22/0.52    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f15])).
% 0.22/0.52  fof(f15,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.22/0.52    inference(flattening,[],[f14])).
% 0.22/0.52  fof(f14,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : ((X0 = X1 | ~r1_tarski(X0,X1)) | (~v1_zfmisc_1(X1) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f8])).
% 0.22/0.52  fof(f8,axiom,(
% 0.22/0.52    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).
% 0.22/0.52  fof(f248,plain,(
% 0.22/0.52    ( ! [X4,X3] : (v1_zfmisc_1(sK5(X3,X4)) | ~l1_pre_topc(X4) | ~v2_tdlat_3(X4) | v2_struct_0(X4) | sP0(X3,X4)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f239,f63])).
% 0.22/0.52  fof(f63,plain,(
% 0.22/0.52    ( ! [X0,X1] : (v2_tex_2(sK5(X0,X1),X1) | sP0(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f42])).
% 0.22/0.52  fof(f239,plain,(
% 0.22/0.52    ( ! [X4,X3] : (~v2_tex_2(sK5(X3,X4),X4) | v1_zfmisc_1(sK5(X3,X4)) | ~l1_pre_topc(X4) | ~v2_tdlat_3(X4) | v2_struct_0(X4) | sP0(X3,X4)) )),
% 0.22/0.52    inference(resolution,[],[f220,f62])).
% 0.22/0.52  fof(f62,plain,(
% 0.22/0.52    ( ! [X0,X1] : (m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) | sP0(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f42])).
% 0.22/0.52  fof(f204,plain,(
% 0.22/0.52    ~spl7_7 | ~spl7_8 | spl7_10),
% 0.22/0.52    inference(avatar_split_clause,[],[f203,f189,f123,f119])).
% 0.22/0.52  fof(f203,plain,(
% 0.22/0.52    ~sP0(sK4,sK3) | ~v2_tex_2(sK4,sK3) | spl7_10),
% 0.22/0.52    inference(resolution,[],[f190,f60])).
% 0.22/0.52  fof(f60,plain,(
% 0.22/0.52    ( ! [X0,X1] : (sP1(X0,X1) | ~sP0(X1,X0) | ~v2_tex_2(X1,X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f38])).
% 0.22/0.52  fof(f190,plain,(
% 0.22/0.52    ~sP1(sK3,sK4) | spl7_10),
% 0.22/0.52    inference(avatar_component_clause,[],[f189])).
% 0.22/0.52  fof(f202,plain,(
% 0.22/0.52    ~spl7_10 | spl7_1),
% 0.22/0.52    inference(avatar_split_clause,[],[f114,f75,f189])).
% 0.22/0.52  fof(f75,plain,(
% 0.22/0.52    spl7_1 <=> v3_tex_2(sK4,sK3)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.22/0.52  fof(f114,plain,(
% 0.22/0.52    ~sP1(sK3,sK4) | spl7_1),
% 0.22/0.52    inference(subsumption_resolution,[],[f112,f77])).
% 0.22/0.52  fof(f77,plain,(
% 0.22/0.52    ~v3_tex_2(sK4,sK3) | spl7_1),
% 0.22/0.52    inference(avatar_component_clause,[],[f75])).
% 0.22/0.52  fof(f112,plain,(
% 0.22/0.52    ~sP1(sK3,sK4) | v3_tex_2(sK4,sK3)),
% 0.22/0.52    inference(resolution,[],[f111,f57])).
% 0.22/0.52  fof(f57,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~sP2(X0,X1) | ~sP1(X1,X0) | v3_tex_2(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f36])).
% 0.22/0.52  fof(f36,plain,(
% 0.22/0.52    ! [X0,X1] : (((v3_tex_2(X0,X1) | ~sP1(X1,X0)) & (sP1(X1,X0) | ~v3_tex_2(X0,X1))) | ~sP2(X0,X1))),
% 0.22/0.52    inference(rectify,[],[f35])).
% 0.22/0.52  fof(f35,plain,(
% 0.22/0.52    ! [X1,X0] : (((v3_tex_2(X1,X0) | ~sP1(X0,X1)) & (sP1(X0,X1) | ~v3_tex_2(X1,X0))) | ~sP2(X1,X0))),
% 0.22/0.52    inference(nnf_transformation,[],[f28])).
% 0.22/0.52  fof(f28,plain,(
% 0.22/0.52    ! [X1,X0] : ((v3_tex_2(X1,X0) <=> sP1(X0,X1)) | ~sP2(X1,X0))),
% 0.22/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.22/0.52  fof(f111,plain,(
% 0.22/0.52    sP2(sK4,sK3)),
% 0.22/0.52    inference(subsumption_resolution,[],[f108,f49])).
% 0.22/0.52  fof(f108,plain,(
% 0.22/0.52    sP2(sK4,sK3) | ~l1_pre_topc(sK3)),
% 0.22/0.52    inference(resolution,[],[f66,f51])).
% 0.22/0.52  fof(f66,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | sP2(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f29])).
% 0.22/0.52  fof(f29,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (sP2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.52    inference(definition_folding,[],[f19,f28,f27,f26])).
% 0.22/0.52  fof(f19,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.52    inference(flattening,[],[f18])).
% 0.22/0.52  fof(f18,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : ((X1 = X2 | (~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f6])).
% 0.22/0.52  fof(f6,axiom,(
% 0.22/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v2_tex_2(X2,X0)) => X1 = X2)) & v2_tex_2(X1,X0)))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tex_2)).
% 0.22/0.52  fof(f192,plain,(
% 0.22/0.52    spl7_10 | ~spl7_1),
% 0.22/0.52    inference(avatar_split_clause,[],[f113,f75,f189])).
% 0.22/0.52  fof(f113,plain,(
% 0.22/0.52    ~v3_tex_2(sK4,sK3) | sP1(sK3,sK4)),
% 0.22/0.52    inference(resolution,[],[f111,f56])).
% 0.22/0.52  fof(f56,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~sP2(X0,X1) | ~v3_tex_2(X0,X1) | sP1(X1,X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f36])).
% 0.22/0.52  fof(f83,plain,(
% 0.22/0.52    spl7_1 | spl7_2),
% 0.22/0.52    inference(avatar_split_clause,[],[f52,f79,f75])).
% 0.22/0.52  fof(f52,plain,(
% 0.22/0.52    v1_zfmisc_1(sK4) | v3_tex_2(sK4,sK3)),
% 0.22/0.52    inference(cnf_transformation,[],[f34])).
% 0.22/0.52  fof(f82,plain,(
% 0.22/0.52    ~spl7_1 | ~spl7_2),
% 0.22/0.52    inference(avatar_split_clause,[],[f53,f79,f75])).
% 0.22/0.52  fof(f53,plain,(
% 0.22/0.52    ~v1_zfmisc_1(sK4) | ~v3_tex_2(sK4,sK3)),
% 0.22/0.52    inference(cnf_transformation,[],[f34])).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (25628)------------------------------
% 0.22/0.52  % (25628)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (25628)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (25628)Memory used [KB]: 6268
% 0.22/0.52  % (25628)Time elapsed: 0.087 s
% 0.22/0.52  % (25628)------------------------------
% 0.22/0.52  % (25628)------------------------------
% 0.22/0.52  % (25623)Success in time 0.16 s
%------------------------------------------------------------------------------
