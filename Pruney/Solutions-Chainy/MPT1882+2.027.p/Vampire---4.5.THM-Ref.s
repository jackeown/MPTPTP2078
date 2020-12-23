%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:03 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 373 expanded)
%              Number of leaves         :   21 ( 111 expanded)
%              Depth                    :   17
%              Number of atoms          :  526 (2634 expanded)
%              Number of equality atoms :   18 (  59 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (13939)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% (13941)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% (13955)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% (13948)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% (13956)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
fof(f213,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f84,f85,f108,f175,f191,f205,f207,f212])).

fof(f212,plain,
    ( spl7_3
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f210,f172,f101])).

fof(f101,plain,
    ( spl7_3
  <=> v2_tex_2(sK4,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f172,plain,
    ( spl7_5
  <=> sP1(sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f210,plain,
    ( v2_tex_2(sK4,sK3)
    | ~ spl7_5 ),
    inference(resolution,[],[f174,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,X1)
      | v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ~ sP0(X1,X0)
        | ~ v2_tex_2(X1,X0) )
      & ( ( sP0(X1,X0)
          & v2_tex_2(X1,X0) )
        | ~ sP1(X0,X1) ) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ~ sP0(X1,X0)
        | ~ v2_tex_2(X1,X0) )
      & ( ( sP0(X1,X0)
          & v2_tex_2(X1,X0) )
        | ~ sP1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
    <=> ( sP0(X1,X0)
        & v2_tex_2(X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f174,plain,
    ( sP1(sK3,sK4)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f172])).

fof(f207,plain,
    ( ~ spl7_2
    | spl7_3 ),
    inference(avatar_split_clause,[],[f181,f101,f81])).

fof(f81,plain,
    ( spl7_2
  <=> v1_zfmisc_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f181,plain,
    ( ~ v1_zfmisc_1(sK4)
    | spl7_3 ),
    inference(subsumption_resolution,[],[f180,f47])).

fof(f47,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f32,f34,f33])).

fof(f33,plain,
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

fof(f34,plain,
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

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

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
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
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
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
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

fof(f180,plain,
    ( ~ v1_zfmisc_1(sK4)
    | v2_struct_0(sK3)
    | spl7_3 ),
    inference(subsumption_resolution,[],[f179,f49])).

fof(f49,plain,(
    v2_tdlat_3(sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f179,plain,
    ( ~ v1_zfmisc_1(sK4)
    | ~ v2_tdlat_3(sK3)
    | v2_struct_0(sK3)
    | spl7_3 ),
    inference(subsumption_resolution,[],[f178,f50])).

fof(f50,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f178,plain,
    ( ~ v1_zfmisc_1(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_tdlat_3(sK3)
    | v2_struct_0(sK3)
    | spl7_3 ),
    inference(subsumption_resolution,[],[f177,f51])).

fof(f51,plain,(
    ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f35])).

fof(f177,plain,
    ( ~ v1_zfmisc_1(sK4)
    | v1_xboole_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_tdlat_3(sK3)
    | v2_struct_0(sK3)
    | spl7_3 ),
    inference(subsumption_resolution,[],[f162,f103])).

fof(f103,plain,
    ( ~ v2_tex_2(sK4,sK3)
    | spl7_3 ),
    inference(avatar_component_clause,[],[f101])).

fof(f162,plain,
    ( ~ v1_zfmisc_1(sK4)
    | v2_tex_2(sK4,sK3)
    | v1_xboole_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_tdlat_3(sK3)
    | v2_struct_0(sK3) ),
    inference(resolution,[],[f161,f52])).

fof(f52,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f35])).

fof(f161,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_zfmisc_1(X1)
      | v2_tex_2(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f70,f56])).

fof(f56,plain,(
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

fof(f70,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | ~ v1_zfmisc_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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

fof(f205,plain,(
    spl7_4 ),
    inference(avatar_contradiction_clause,[],[f204])).

fof(f204,plain,
    ( $false
    | spl7_4 ),
    inference(subsumption_resolution,[],[f203,f51])).

fof(f203,plain,
    ( v1_xboole_0(sK4)
    | spl7_4 ),
    inference(subsumption_resolution,[],[f202,f50])).

fof(f202,plain,
    ( ~ l1_pre_topc(sK3)
    | v1_xboole_0(sK4)
    | spl7_4 ),
    inference(subsumption_resolution,[],[f201,f47])).

fof(f201,plain,
    ( v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3)
    | v1_xboole_0(sK4)
    | spl7_4 ),
    inference(subsumption_resolution,[],[f199,f49])).

fof(f199,plain,
    ( ~ v2_tdlat_3(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3)
    | v1_xboole_0(sK4)
    | spl7_4 ),
    inference(resolution,[],[f107,f154])).

fof(f154,plain,(
    ! [X0,X1] :
      ( sP0(X1,X0)
      | ~ v2_tdlat_3(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1) ) ),
    inference(duplicate_literal_removal,[],[f153])).

fof(f153,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | v2_struct_0(X0)
      | sP0(X1,X0)
      | v1_xboole_0(X1)
      | sP0(X1,X0) ) ),
    inference(resolution,[],[f152,f141])).

fof(f141,plain,(
    ! [X0,X1] :
      ( ~ v1_zfmisc_1(sK5(X0,X1))
      | v1_xboole_0(X0)
      | sP0(X0,X1) ) ),
    inference(subsumption_resolution,[],[f110,f111])).

fof(f111,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(sK5(X0,X1))
      | sP0(X0,X1)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f88,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(resolution,[],[f72,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

fof(f72,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK6(X0,X1),X1)
          & r2_hidden(sK6(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f23,f45])).

fof(f45,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK6(X0,X1),X1)
        & r2_hidden(sK6(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,sK5(X0,X1))
      | v1_xboole_0(X0)
      | sP0(X0,X1) ) ),
    inference(resolution,[],[f74,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,sK5(X0,X1))
      | sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f41,f42])).

fof(f42,plain,(
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

fof(f41,plain,(
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
    inference(rectify,[],[f40])).

fof(f40,plain,(
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
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X1,X0] :
      ( sP0(X1,X0)
    <=> ! [X2] :
          ( X1 = X2
          | ~ r1_tarski(X1,X2)
          | ~ v2_tex_2(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_xboole_0(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

fof(f110,plain,(
    ! [X0,X1] :
      ( ~ v1_zfmisc_1(sK5(X0,X1))
      | v1_xboole_0(sK5(X0,X1))
      | v1_xboole_0(X0)
      | sP0(X0,X1) ) ),
    inference(subsumption_resolution,[],[f109,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( sK5(X0,X1) != X0
      | sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f109,plain,(
    ! [X0,X1] :
      ( sK5(X0,X1) = X0
      | ~ v1_zfmisc_1(sK5(X0,X1))
      | v1_xboole_0(sK5(X0,X1))
      | v1_xboole_0(X0)
      | sP0(X0,X1) ) ),
    inference(resolution,[],[f55,f65])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

fof(f152,plain,(
    ! [X0,X1] :
      ( v1_zfmisc_1(sK5(X0,X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_tdlat_3(X1)
      | v2_struct_0(X1)
      | sP0(X0,X1) ) ),
    inference(subsumption_resolution,[],[f151,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( v2_tex_2(sK5(X0,X1),X1)
      | sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f151,plain,(
    ! [X0,X1] :
      ( ~ v2_tex_2(sK5(X0,X1),X1)
      | v1_zfmisc_1(sK5(X0,X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_tdlat_3(X1)
      | v2_struct_0(X1)
      | sP0(X0,X1) ) ),
    inference(resolution,[],[f140,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))
      | sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f140,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | v1_zfmisc_1(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f139,f68])).

fof(f68,plain,(
    ! [X0] :
      ( v1_zfmisc_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( v1_zfmisc_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_zfmisc_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_zfmisc_1)).

fof(f139,plain,(
    ! [X0,X1] :
      ( v1_zfmisc_1(X1)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f69,f56])).

fof(f69,plain,(
    ! [X0,X1] :
      ( v1_zfmisc_1(X1)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f107,plain,
    ( ~ sP0(sK4,sK3)
    | spl7_4 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl7_4
  <=> sP0(sK4,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f191,plain,
    ( spl7_2
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f190,f101,f81])).

fof(f190,plain,
    ( ~ v2_tex_2(sK4,sK3)
    | v1_zfmisc_1(sK4) ),
    inference(subsumption_resolution,[],[f189,f47])).

fof(f189,plain,
    ( ~ v2_tex_2(sK4,sK3)
    | v1_zfmisc_1(sK4)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f188,f49])).

fof(f188,plain,
    ( ~ v2_tex_2(sK4,sK3)
    | v1_zfmisc_1(sK4)
    | ~ v2_tdlat_3(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f150,f50])).

fof(f150,plain,
    ( ~ v2_tex_2(sK4,sK3)
    | v1_zfmisc_1(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_tdlat_3(sK3)
    | v2_struct_0(sK3) ),
    inference(resolution,[],[f140,f52])).

fof(f175,plain,
    ( spl7_5
    | ~ spl7_1 ),
    inference(avatar_split_clause,[],[f97,f77,f172])).

fof(f77,plain,
    ( spl7_1
  <=> v3_tex_2(sK4,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f97,plain,
    ( ~ v3_tex_2(sK4,sK3)
    | sP1(sK3,sK4) ),
    inference(resolution,[],[f95,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ sP2(X0,X1)
      | ~ v3_tex_2(X0,X1)
      | sP1(X1,X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( ( v3_tex_2(X0,X1)
          | ~ sP1(X1,X0) )
        & ( sP1(X1,X0)
          | ~ v3_tex_2(X0,X1) ) )
      | ~ sP2(X0,X1) ) ),
    inference(rectify,[],[f36])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ( ( v3_tex_2(X1,X0)
          | ~ sP1(X0,X1) )
        & ( sP1(X0,X1)
          | ~ v3_tex_2(X1,X0) ) )
      | ~ sP2(X1,X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ( v3_tex_2(X1,X0)
      <=> sP1(X0,X1) )
      | ~ sP2(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f95,plain,(
    sP2(sK4,sK3) ),
    inference(subsumption_resolution,[],[f93,f50])).

fof(f93,plain,
    ( sP2(sK4,sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(resolution,[],[f67,f52])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | sP2(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f19,f29,f28,f27])).

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

fof(f108,plain,
    ( ~ spl7_3
    | ~ spl7_4
    | spl7_1 ),
    inference(avatar_split_clause,[],[f99,f77,f105,f101])).

fof(f99,plain,
    ( ~ sP0(sK4,sK3)
    | ~ v2_tex_2(sK4,sK3)
    | spl7_1 ),
    inference(resolution,[],[f98,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
      | ~ sP0(X1,X0)
      | ~ v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f98,plain,
    ( ~ sP1(sK3,sK4)
    | spl7_1 ),
    inference(subsumption_resolution,[],[f96,f79])).

fof(f79,plain,
    ( ~ v3_tex_2(sK4,sK3)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f77])).

fof(f96,plain,
    ( ~ sP1(sK3,sK4)
    | v3_tex_2(sK4,sK3) ),
    inference(resolution,[],[f95,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ sP2(X0,X1)
      | ~ sP1(X1,X0)
      | v3_tex_2(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f85,plain,
    ( spl7_1
    | spl7_2 ),
    inference(avatar_split_clause,[],[f53,f81,f77])).

fof(f53,plain,
    ( v1_zfmisc_1(sK4)
    | v3_tex_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f84,plain,
    ( ~ spl7_1
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f54,f81,f77])).

fof(f54,plain,
    ( ~ v1_zfmisc_1(sK4)
    | ~ v3_tex_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:16:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (13960)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.20/0.46  % (13945)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.20/0.48  % (13940)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.48  % (13947)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.48  % (13940)Refutation found. Thanks to Tanya!
% 0.20/0.48  % SZS status Theorem for theBenchmark
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.49  % (13939)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.49  % (13941)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.50  % (13955)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.50  % (13948)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.50  % (13956)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.50  fof(f213,plain,(
% 0.20/0.50    $false),
% 0.20/0.50    inference(avatar_sat_refutation,[],[f84,f85,f108,f175,f191,f205,f207,f212])).
% 0.20/0.50  fof(f212,plain,(
% 0.20/0.50    spl7_3 | ~spl7_5),
% 0.20/0.50    inference(avatar_split_clause,[],[f210,f172,f101])).
% 0.20/0.50  fof(f101,plain,(
% 0.20/0.50    spl7_3 <=> v2_tex_2(sK4,sK3)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.20/0.50  fof(f172,plain,(
% 0.20/0.50    spl7_5 <=> sP1(sK3,sK4)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.20/0.50  fof(f210,plain,(
% 0.20/0.50    v2_tex_2(sK4,sK3) | ~spl7_5),
% 0.20/0.50    inference(resolution,[],[f174,f59])).
% 0.20/0.50  fof(f59,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~sP1(X0,X1) | v2_tex_2(X1,X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f39])).
% 0.20/0.50  fof(f39,plain,(
% 0.20/0.50    ! [X0,X1] : ((sP1(X0,X1) | ~sP0(X1,X0) | ~v2_tex_2(X1,X0)) & ((sP0(X1,X0) & v2_tex_2(X1,X0)) | ~sP1(X0,X1)))),
% 0.20/0.50    inference(flattening,[],[f38])).
% 0.20/0.50  fof(f38,plain,(
% 0.20/0.50    ! [X0,X1] : ((sP1(X0,X1) | (~sP0(X1,X0) | ~v2_tex_2(X1,X0))) & ((sP0(X1,X0) & v2_tex_2(X1,X0)) | ~sP1(X0,X1)))),
% 0.20/0.50    inference(nnf_transformation,[],[f28])).
% 0.20/0.50  fof(f28,plain,(
% 0.20/0.50    ! [X0,X1] : (sP1(X0,X1) <=> (sP0(X1,X0) & v2_tex_2(X1,X0)))),
% 0.20/0.50    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.20/0.50  fof(f174,plain,(
% 0.20/0.50    sP1(sK3,sK4) | ~spl7_5),
% 0.20/0.50    inference(avatar_component_clause,[],[f172])).
% 0.20/0.50  fof(f207,plain,(
% 0.20/0.50    ~spl7_2 | spl7_3),
% 0.20/0.50    inference(avatar_split_clause,[],[f181,f101,f81])).
% 0.20/0.50  fof(f81,plain,(
% 0.20/0.50    spl7_2 <=> v1_zfmisc_1(sK4)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.20/0.50  fof(f181,plain,(
% 0.20/0.50    ~v1_zfmisc_1(sK4) | spl7_3),
% 0.20/0.50    inference(subsumption_resolution,[],[f180,f47])).
% 0.20/0.50  fof(f47,plain,(
% 0.20/0.50    ~v2_struct_0(sK3)),
% 0.20/0.50    inference(cnf_transformation,[],[f35])).
% 0.20/0.50  fof(f35,plain,(
% 0.20/0.50    ((~v1_zfmisc_1(sK4) | ~v3_tex_2(sK4,sK3)) & (v1_zfmisc_1(sK4) | v3_tex_2(sK4,sK3)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) & ~v1_xboole_0(sK4)) & l1_pre_topc(sK3) & v2_tdlat_3(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)),
% 0.20/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f32,f34,f33])).
% 0.20/0.50  fof(f33,plain,(
% 0.20/0.50    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,sK3)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,sK3)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) & ~v1_xboole_0(X1)) & l1_pre_topc(sK3) & v2_tdlat_3(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f34,plain,(
% 0.20/0.50    ? [X1] : ((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,sK3)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,sK3)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) & ~v1_xboole_0(X1)) => ((~v1_zfmisc_1(sK4) | ~v3_tex_2(sK4,sK3)) & (v1_zfmisc_1(sK4) | v3_tex_2(sK4,sK3)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) & ~v1_xboole_0(sK4))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f32,plain,(
% 0.20/0.50    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f31])).
% 0.20/0.50  fof(f31,plain,(
% 0.20/0.50    ? [X0] : (? [X1] : (((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.50    inference(nnf_transformation,[],[f13])).
% 0.20/0.50  fof(f13,plain,(
% 0.20/0.50    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f12])).
% 0.20/0.50  fof(f12,plain,(
% 0.20/0.50    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f10])).
% 0.20/0.50  fof(f10,negated_conjecture,(
% 0.20/0.50    ~! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v3_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 0.20/0.50    inference(negated_conjecture,[],[f9])).
% 0.20/0.50  fof(f9,conjecture,(
% 0.20/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v3_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_tex_2)).
% 0.20/0.50  fof(f180,plain,(
% 0.20/0.50    ~v1_zfmisc_1(sK4) | v2_struct_0(sK3) | spl7_3),
% 0.20/0.50    inference(subsumption_resolution,[],[f179,f49])).
% 0.20/0.50  fof(f49,plain,(
% 0.20/0.50    v2_tdlat_3(sK3)),
% 0.20/0.50    inference(cnf_transformation,[],[f35])).
% 0.20/0.50  fof(f179,plain,(
% 0.20/0.50    ~v1_zfmisc_1(sK4) | ~v2_tdlat_3(sK3) | v2_struct_0(sK3) | spl7_3),
% 0.20/0.50    inference(subsumption_resolution,[],[f178,f50])).
% 0.20/0.50  fof(f50,plain,(
% 0.20/0.50    l1_pre_topc(sK3)),
% 0.20/0.50    inference(cnf_transformation,[],[f35])).
% 0.20/0.50  fof(f178,plain,(
% 0.20/0.50    ~v1_zfmisc_1(sK4) | ~l1_pre_topc(sK3) | ~v2_tdlat_3(sK3) | v2_struct_0(sK3) | spl7_3),
% 0.20/0.50    inference(subsumption_resolution,[],[f177,f51])).
% 0.20/0.50  fof(f51,plain,(
% 0.20/0.50    ~v1_xboole_0(sK4)),
% 0.20/0.50    inference(cnf_transformation,[],[f35])).
% 0.20/0.50  fof(f177,plain,(
% 0.20/0.50    ~v1_zfmisc_1(sK4) | v1_xboole_0(sK4) | ~l1_pre_topc(sK3) | ~v2_tdlat_3(sK3) | v2_struct_0(sK3) | spl7_3),
% 0.20/0.50    inference(subsumption_resolution,[],[f162,f103])).
% 0.20/0.50  fof(f103,plain,(
% 0.20/0.50    ~v2_tex_2(sK4,sK3) | spl7_3),
% 0.20/0.50    inference(avatar_component_clause,[],[f101])).
% 0.20/0.50  fof(f162,plain,(
% 0.20/0.50    ~v1_zfmisc_1(sK4) | v2_tex_2(sK4,sK3) | v1_xboole_0(sK4) | ~l1_pre_topc(sK3) | ~v2_tdlat_3(sK3) | v2_struct_0(sK3)),
% 0.20/0.50    inference(resolution,[],[f161,f52])).
% 0.20/0.50  fof(f52,plain,(
% 0.20/0.50    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))),
% 0.20/0.50    inference(cnf_transformation,[],[f35])).
% 0.20/0.50  fof(f161,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_zfmisc_1(X1) | v2_tex_2(X1,X0) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | v2_struct_0(X0)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f70,f56])).
% 0.20/0.50  fof(f56,plain,(
% 0.20/0.50    ( ! [X0] : (v2_pre_topc(X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f17])).
% 0.20/0.50  fof(f17,plain,(
% 0.20/0.50    ! [X0] : (v2_pre_topc(X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0))),
% 0.20/0.50    inference(flattening,[],[f16])).
% 0.20/0.50  fof(f16,plain,(
% 0.20/0.50    ! [X0] : ((v2_pre_topc(X0) | ~v2_tdlat_3(X0)) | ~l1_pre_topc(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f5])).
% 0.20/0.50  fof(f5,axiom,(
% 0.20/0.50    ! [X0] : (l1_pre_topc(X0) => (v2_tdlat_3(X0) => v2_pre_topc(X0)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tdlat_3)).
% 0.20/0.50  fof(f70,plain,(
% 0.20/0.50    ( ! [X0,X1] : (v2_tex_2(X1,X0) | ~v1_zfmisc_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f44])).
% 0.20/0.50  fof(f44,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ~v1_zfmisc_1(X1)) & (v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.50    inference(nnf_transformation,[],[f22])).
% 0.20/0.50  fof(f22,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f21])).
% 0.20/0.50  fof(f21,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f8])).
% 0.20/0.50  fof(f8,axiom,(
% 0.20/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tex_2)).
% 0.20/0.50  fof(f205,plain,(
% 0.20/0.50    spl7_4),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f204])).
% 0.20/0.50  fof(f204,plain,(
% 0.20/0.50    $false | spl7_4),
% 0.20/0.50    inference(subsumption_resolution,[],[f203,f51])).
% 0.20/0.50  fof(f203,plain,(
% 0.20/0.50    v1_xboole_0(sK4) | spl7_4),
% 0.20/0.50    inference(subsumption_resolution,[],[f202,f50])).
% 0.20/0.50  fof(f202,plain,(
% 0.20/0.50    ~l1_pre_topc(sK3) | v1_xboole_0(sK4) | spl7_4),
% 0.20/0.50    inference(subsumption_resolution,[],[f201,f47])).
% 0.20/0.50  fof(f201,plain,(
% 0.20/0.50    v2_struct_0(sK3) | ~l1_pre_topc(sK3) | v1_xboole_0(sK4) | spl7_4),
% 0.20/0.50    inference(subsumption_resolution,[],[f199,f49])).
% 0.20/0.50  fof(f199,plain,(
% 0.20/0.50    ~v2_tdlat_3(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK3) | v1_xboole_0(sK4) | spl7_4),
% 0.20/0.50    inference(resolution,[],[f107,f154])).
% 0.20/0.50  fof(f154,plain,(
% 0.20/0.50    ( ! [X0,X1] : (sP0(X1,X0) | ~v2_tdlat_3(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | v1_xboole_0(X1)) )),
% 0.20/0.50    inference(duplicate_literal_removal,[],[f153])).
% 0.20/0.50  fof(f153,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | v2_struct_0(X0) | sP0(X1,X0) | v1_xboole_0(X1) | sP0(X1,X0)) )),
% 0.20/0.50    inference(resolution,[],[f152,f141])).
% 0.20/0.50  fof(f141,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~v1_zfmisc_1(sK5(X0,X1)) | v1_xboole_0(X0) | sP0(X0,X1)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f110,f111])).
% 0.20/0.50  fof(f111,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~v1_xboole_0(sK5(X0,X1)) | sP0(X0,X1) | v1_xboole_0(X0)) )),
% 0.20/0.50    inference(resolution,[],[f88,f87])).
% 0.20/0.50  fof(f87,plain,(
% 0.20/0.50    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | ~v1_xboole_0(X1)) )),
% 0.20/0.50    inference(resolution,[],[f72,f75])).
% 0.20/0.50  fof(f75,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~v1_xboole_0(X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f26])).
% 0.20/0.50  fof(f26,plain,(
% 0.20/0.50    ! [X0,X1] : (~v1_xboole_0(X1) | ~r2_hidden(X0,X1))),
% 0.20/0.50    inference(ennf_transformation,[],[f3])).
% 0.20/0.50  fof(f3,axiom,(
% 0.20/0.50    ! [X0,X1] : ~(v1_xboole_0(X1) & r2_hidden(X0,X1))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).
% 0.20/0.50  fof(f72,plain,(
% 0.20/0.50    ( ! [X0,X1] : (r2_hidden(sK6(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f46])).
% 0.20/0.50  fof(f46,plain,(
% 0.20/0.50    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.20/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f23,f45])).
% 0.20/0.50  fof(f45,plain,(
% 0.20/0.50    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0)))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f23,plain,(
% 0.20/0.50    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.20/0.50    inference(ennf_transformation,[],[f11])).
% 0.20/0.50  fof(f11,plain,(
% 0.20/0.50    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.50    inference(rectify,[],[f1])).
% 0.20/0.50  fof(f1,axiom,(
% 0.20/0.50    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.20/0.50  fof(f88,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~r1_xboole_0(X0,sK5(X0,X1)) | v1_xboole_0(X0) | sP0(X0,X1)) )),
% 0.20/0.50    inference(resolution,[],[f74,f65])).
% 0.20/0.50  fof(f65,plain,(
% 0.20/0.50    ( ! [X0,X1] : (r1_tarski(X0,sK5(X0,X1)) | sP0(X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f43])).
% 0.20/0.50  fof(f43,plain,(
% 0.20/0.50    ! [X0,X1] : ((sP0(X0,X1) | (sK5(X0,X1) != X0 & r1_tarski(X0,sK5(X0,X1)) & v2_tex_2(sK5(X0,X1),X1) & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X1))))) & (! [X3] : (X0 = X3 | ~r1_tarski(X0,X3) | ~v2_tex_2(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~sP0(X0,X1)))),
% 0.20/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f41,f42])).
% 0.20/0.50  fof(f42,plain,(
% 0.20/0.50    ! [X1,X0] : (? [X2] : (X0 != X2 & r1_tarski(X0,X2) & v2_tex_2(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) => (sK5(X0,X1) != X0 & r1_tarski(X0,sK5(X0,X1)) & v2_tex_2(sK5(X0,X1),X1) & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f41,plain,(
% 0.20/0.50    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : (X0 != X2 & r1_tarski(X0,X2) & v2_tex_2(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X3] : (X0 = X3 | ~r1_tarski(X0,X3) | ~v2_tex_2(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~sP0(X0,X1)))),
% 0.20/0.50    inference(rectify,[],[f40])).
% 0.20/0.50  fof(f40,plain,(
% 0.20/0.50    ! [X1,X0] : ((sP0(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP0(X1,X0)))),
% 0.20/0.50    inference(nnf_transformation,[],[f27])).
% 0.20/0.50  fof(f27,plain,(
% 0.20/0.50    ! [X1,X0] : (sP0(X1,X0) <=> ! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.50    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.20/0.50  fof(f74,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_xboole_0(X1,X0) | v1_xboole_0(X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f25])).
% 0.20/0.50  fof(f25,plain,(
% 0.20/0.50    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 0.20/0.50    inference(flattening,[],[f24])).
% 0.20/0.50  fof(f24,plain,(
% 0.20/0.50    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 0.20/0.50    inference(ennf_transformation,[],[f2])).
% 0.20/0.50  fof(f2,axiom,(
% 0.20/0.50    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).
% 0.20/0.50  fof(f110,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~v1_zfmisc_1(sK5(X0,X1)) | v1_xboole_0(sK5(X0,X1)) | v1_xboole_0(X0) | sP0(X0,X1)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f109,f66])).
% 0.20/0.50  fof(f66,plain,(
% 0.20/0.50    ( ! [X0,X1] : (sK5(X0,X1) != X0 | sP0(X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f43])).
% 0.20/0.50  fof(f109,plain,(
% 0.20/0.50    ( ! [X0,X1] : (sK5(X0,X1) = X0 | ~v1_zfmisc_1(sK5(X0,X1)) | v1_xboole_0(sK5(X0,X1)) | v1_xboole_0(X0) | sP0(X0,X1)) )),
% 0.20/0.50    inference(resolution,[],[f55,f65])).
% 0.20/0.50  fof(f55,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~r1_tarski(X0,X1) | X0 = X1 | ~v1_zfmisc_1(X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f15])).
% 0.20/0.50  fof(f15,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.20/0.50    inference(flattening,[],[f14])).
% 0.20/0.50  fof(f14,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : ((X0 = X1 | ~r1_tarski(X0,X1)) | (~v1_zfmisc_1(X1) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f7])).
% 0.20/0.50  fof(f7,axiom,(
% 0.20/0.50    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).
% 0.20/0.50  fof(f152,plain,(
% 0.20/0.50    ( ! [X0,X1] : (v1_zfmisc_1(sK5(X0,X1)) | ~l1_pre_topc(X1) | ~v2_tdlat_3(X1) | v2_struct_0(X1) | sP0(X0,X1)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f151,f64])).
% 0.20/0.50  fof(f64,plain,(
% 0.20/0.50    ( ! [X0,X1] : (v2_tex_2(sK5(X0,X1),X1) | sP0(X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f43])).
% 0.20/0.50  fof(f151,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~v2_tex_2(sK5(X0,X1),X1) | v1_zfmisc_1(sK5(X0,X1)) | ~l1_pre_topc(X1) | ~v2_tdlat_3(X1) | v2_struct_0(X1) | sP0(X0,X1)) )),
% 0.20/0.50    inference(resolution,[],[f140,f63])).
% 0.20/0.50  fof(f63,plain,(
% 0.20/0.50    ( ! [X0,X1] : (m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) | sP0(X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f43])).
% 0.20/0.50  fof(f140,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | v1_zfmisc_1(X1) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | v2_struct_0(X0)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f139,f68])).
% 0.20/0.50  fof(f68,plain,(
% 0.20/0.50    ( ! [X0] : (v1_zfmisc_1(X0) | ~v1_xboole_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f20])).
% 0.20/0.50  fof(f20,plain,(
% 0.20/0.50    ! [X0] : (v1_zfmisc_1(X0) | ~v1_xboole_0(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f4])).
% 0.20/0.50  fof(f4,axiom,(
% 0.20/0.50    ! [X0] : (v1_xboole_0(X0) => v1_zfmisc_1(X0))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_zfmisc_1)).
% 0.20/0.50  fof(f139,plain,(
% 0.20/0.50    ( ! [X0,X1] : (v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | v2_struct_0(X0)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f69,f56])).
% 0.20/0.50  fof(f69,plain,(
% 0.20/0.50    ( ! [X0,X1] : (v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f44])).
% 0.20/0.50  fof(f107,plain,(
% 0.20/0.50    ~sP0(sK4,sK3) | spl7_4),
% 0.20/0.50    inference(avatar_component_clause,[],[f105])).
% 0.20/0.50  fof(f105,plain,(
% 0.20/0.50    spl7_4 <=> sP0(sK4,sK3)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.20/0.50  fof(f191,plain,(
% 0.20/0.50    spl7_2 | ~spl7_3),
% 0.20/0.50    inference(avatar_split_clause,[],[f190,f101,f81])).
% 0.20/0.50  fof(f190,plain,(
% 0.20/0.50    ~v2_tex_2(sK4,sK3) | v1_zfmisc_1(sK4)),
% 0.20/0.50    inference(subsumption_resolution,[],[f189,f47])).
% 0.20/0.50  fof(f189,plain,(
% 0.20/0.50    ~v2_tex_2(sK4,sK3) | v1_zfmisc_1(sK4) | v2_struct_0(sK3)),
% 0.20/0.50    inference(subsumption_resolution,[],[f188,f49])).
% 0.20/0.50  fof(f188,plain,(
% 0.20/0.50    ~v2_tex_2(sK4,sK3) | v1_zfmisc_1(sK4) | ~v2_tdlat_3(sK3) | v2_struct_0(sK3)),
% 0.20/0.50    inference(subsumption_resolution,[],[f150,f50])).
% 0.20/0.50  fof(f150,plain,(
% 0.20/0.50    ~v2_tex_2(sK4,sK3) | v1_zfmisc_1(sK4) | ~l1_pre_topc(sK3) | ~v2_tdlat_3(sK3) | v2_struct_0(sK3)),
% 0.20/0.50    inference(resolution,[],[f140,f52])).
% 0.20/0.50  fof(f175,plain,(
% 0.20/0.50    spl7_5 | ~spl7_1),
% 0.20/0.50    inference(avatar_split_clause,[],[f97,f77,f172])).
% 0.20/0.50  fof(f77,plain,(
% 0.20/0.50    spl7_1 <=> v3_tex_2(sK4,sK3)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.20/0.50  fof(f97,plain,(
% 0.20/0.50    ~v3_tex_2(sK4,sK3) | sP1(sK3,sK4)),
% 0.20/0.50    inference(resolution,[],[f95,f57])).
% 0.20/0.50  fof(f57,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~sP2(X0,X1) | ~v3_tex_2(X0,X1) | sP1(X1,X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f37])).
% 0.20/0.50  fof(f37,plain,(
% 0.20/0.50    ! [X0,X1] : (((v3_tex_2(X0,X1) | ~sP1(X1,X0)) & (sP1(X1,X0) | ~v3_tex_2(X0,X1))) | ~sP2(X0,X1))),
% 0.20/0.50    inference(rectify,[],[f36])).
% 0.20/0.50  fof(f36,plain,(
% 0.20/0.50    ! [X1,X0] : (((v3_tex_2(X1,X0) | ~sP1(X0,X1)) & (sP1(X0,X1) | ~v3_tex_2(X1,X0))) | ~sP2(X1,X0))),
% 0.20/0.50    inference(nnf_transformation,[],[f29])).
% 0.20/0.50  fof(f29,plain,(
% 0.20/0.50    ! [X1,X0] : ((v3_tex_2(X1,X0) <=> sP1(X0,X1)) | ~sP2(X1,X0))),
% 0.20/0.50    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.20/0.50  fof(f95,plain,(
% 0.20/0.50    sP2(sK4,sK3)),
% 0.20/0.50    inference(subsumption_resolution,[],[f93,f50])).
% 0.20/0.50  fof(f93,plain,(
% 0.20/0.50    sP2(sK4,sK3) | ~l1_pre_topc(sK3)),
% 0.20/0.50    inference(resolution,[],[f67,f52])).
% 0.20/0.50  fof(f67,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | sP2(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f30])).
% 0.20/0.50  fof(f30,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (sP2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.50    inference(definition_folding,[],[f19,f29,f28,f27])).
% 0.20/0.50  fof(f19,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.50    inference(flattening,[],[f18])).
% 0.20/0.50  fof(f18,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : ((X1 = X2 | (~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f6])).
% 0.20/0.50  fof(f6,axiom,(
% 0.20/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v2_tex_2(X2,X0)) => X1 = X2)) & v2_tex_2(X1,X0)))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tex_2)).
% 0.20/0.50  fof(f108,plain,(
% 0.20/0.50    ~spl7_3 | ~spl7_4 | spl7_1),
% 0.20/0.50    inference(avatar_split_clause,[],[f99,f77,f105,f101])).
% 0.20/0.50  fof(f99,plain,(
% 0.20/0.50    ~sP0(sK4,sK3) | ~v2_tex_2(sK4,sK3) | spl7_1),
% 0.20/0.50    inference(resolution,[],[f98,f61])).
% 0.20/0.50  fof(f61,plain,(
% 0.20/0.50    ( ! [X0,X1] : (sP1(X0,X1) | ~sP0(X1,X0) | ~v2_tex_2(X1,X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f39])).
% 0.20/0.50  fof(f98,plain,(
% 0.20/0.50    ~sP1(sK3,sK4) | spl7_1),
% 0.20/0.50    inference(subsumption_resolution,[],[f96,f79])).
% 0.20/0.50  fof(f79,plain,(
% 0.20/0.50    ~v3_tex_2(sK4,sK3) | spl7_1),
% 0.20/0.50    inference(avatar_component_clause,[],[f77])).
% 0.20/0.50  fof(f96,plain,(
% 0.20/0.50    ~sP1(sK3,sK4) | v3_tex_2(sK4,sK3)),
% 0.20/0.50    inference(resolution,[],[f95,f58])).
% 0.20/0.50  fof(f58,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~sP2(X0,X1) | ~sP1(X1,X0) | v3_tex_2(X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f37])).
% 0.20/0.50  fof(f85,plain,(
% 0.20/0.50    spl7_1 | spl7_2),
% 0.20/0.50    inference(avatar_split_clause,[],[f53,f81,f77])).
% 0.20/0.50  fof(f53,plain,(
% 0.20/0.50    v1_zfmisc_1(sK4) | v3_tex_2(sK4,sK3)),
% 0.20/0.50    inference(cnf_transformation,[],[f35])).
% 0.20/0.50  fof(f84,plain,(
% 0.20/0.50    ~spl7_1 | ~spl7_2),
% 0.20/0.50    inference(avatar_split_clause,[],[f54,f81,f77])).
% 0.20/0.50  fof(f54,plain,(
% 0.20/0.50    ~v1_zfmisc_1(sK4) | ~v3_tex_2(sK4,sK3)),
% 0.20/0.50    inference(cnf_transformation,[],[f35])).
% 0.20/0.50  % SZS output end Proof for theBenchmark
% 0.20/0.50  % (13940)------------------------------
% 0.20/0.50  % (13940)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (13940)Termination reason: Refutation
% 0.20/0.50  
% 0.20/0.50  % (13940)Memory used [KB]: 6140
% 0.20/0.50  % (13940)Time elapsed: 0.087 s
% 0.20/0.50  % (13940)------------------------------
% 0.20/0.50  % (13940)------------------------------
% 0.20/0.51  % (13935)Success in time 0.154 s
%------------------------------------------------------------------------------
