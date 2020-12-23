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
% DateTime   : Thu Dec  3 13:22:03 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 386 expanded)
%              Number of leaves         :   23 ( 117 expanded)
%              Depth                    :   19
%              Number of atoms          :  528 (2685 expanded)
%              Number of equality atoms :   37 (  88 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f359,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f91,f92,f205,f215,f217,f335,f349,f353,f358])).

fof(f358,plain,
    ( spl8_7
    | ~ spl8_10 ),
    inference(avatar_split_clause,[],[f356,f202,f126])).

fof(f126,plain,
    ( spl8_7
  <=> v2_tex_2(sK5,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f202,plain,
    ( spl8_10
  <=> sP1(sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f356,plain,
    ( v2_tex_2(sK5,sK4)
    | ~ spl8_10 ),
    inference(resolution,[],[f204,f62])).

% (545)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
fof(f62,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,X1)
      | v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ~ sP0(X1,X0)
        | ~ v2_tex_2(X1,X0) )
      & ( ( sP0(X1,X0)
          & v2_tex_2(X1,X0) )
        | ~ sP1(X0,X1) ) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
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

fof(f204,plain,
    ( sP1(sK4,sK5)
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f202])).

fof(f353,plain,
    ( spl8_2
    | ~ spl8_7 ),
    inference(avatar_split_clause,[],[f352,f126,f88])).

fof(f88,plain,
    ( spl8_2
  <=> v1_zfmisc_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f352,plain,
    ( ~ v2_tex_2(sK5,sK4)
    | v1_zfmisc_1(sK5) ),
    inference(subsumption_resolution,[],[f351,f50])).

fof(f50,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( ( ~ v1_zfmisc_1(sK5)
      | ~ v3_tex_2(sK5,sK4) )
    & ( v1_zfmisc_1(sK5)
      | v3_tex_2(sK5,sK4) )
    & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    & ~ v1_xboole_0(sK5)
    & l1_pre_topc(sK4)
    & v2_tdlat_3(sK4)
    & v2_pre_topc(sK4)
    & ~ v2_struct_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f33,f35,f34])).

fof(f34,plain,
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
            | ~ v3_tex_2(X1,sK4) )
          & ( v1_zfmisc_1(X1)
            | v3_tex_2(X1,sK4) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(sK4)
      & v2_tdlat_3(sK4)
      & v2_pre_topc(sK4)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X1] :
        ( ( ~ v1_zfmisc_1(X1)
          | ~ v3_tex_2(X1,sK4) )
        & ( v1_zfmisc_1(X1)
          | v3_tex_2(X1,sK4) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
        & ~ v1_xboole_0(X1) )
   => ( ( ~ v1_zfmisc_1(sK5)
        | ~ v3_tex_2(sK5,sK4) )
      & ( v1_zfmisc_1(sK5)
        | v3_tex_2(sK5,sK4) )
      & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
      & ~ v1_xboole_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_tex_2)).

fof(f351,plain,
    ( ~ v2_tex_2(sK5,sK4)
    | v1_zfmisc_1(sK5)
    | v2_struct_0(sK4) ),
    inference(subsumption_resolution,[],[f350,f52])).

fof(f52,plain,(
    v2_tdlat_3(sK4) ),
    inference(cnf_transformation,[],[f36])).

fof(f350,plain,
    ( ~ v2_tex_2(sK5,sK4)
    | v1_zfmisc_1(sK5)
    | ~ v2_tdlat_3(sK4)
    | v2_struct_0(sK4) ),
    inference(subsumption_resolution,[],[f244,f53])).

fof(f53,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f36])).

fof(f244,plain,
    ( ~ v2_tex_2(sK5,sK4)
    | v1_zfmisc_1(sK5)
    | ~ l1_pre_topc(sK4)
    | ~ v2_tdlat_3(sK4)
    | v2_struct_0(sK4) ),
    inference(resolution,[],[f225,f55])).

fof(f55,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f36])).

fof(f225,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | v1_zfmisc_1(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f224,f71])).

fof(f71,plain,(
    ! [X0] :
      ( v1_zfmisc_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( v1_zfmisc_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_zfmisc_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_zfmisc_1)).

fof(f224,plain,(
    ! [X0,X1] :
      ( v1_zfmisc_1(X1)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f72,f59])).

fof(f59,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tdlat_3)).

fof(f72,plain,(
    ! [X0,X1] :
      ( v1_zfmisc_1(X1)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tex_2)).

fof(f349,plain,
    ( spl8_7
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f348,f88,f126])).

fof(f348,plain,
    ( ~ v1_zfmisc_1(sK5)
    | v2_tex_2(sK5,sK4) ),
    inference(subsumption_resolution,[],[f347,f50])).

fof(f347,plain,
    ( ~ v1_zfmisc_1(sK5)
    | v2_tex_2(sK5,sK4)
    | v2_struct_0(sK4) ),
    inference(subsumption_resolution,[],[f346,f52])).

fof(f346,plain,
    ( ~ v1_zfmisc_1(sK5)
    | v2_tex_2(sK5,sK4)
    | ~ v2_tdlat_3(sK4)
    | v2_struct_0(sK4) ),
    inference(subsumption_resolution,[],[f345,f53])).

fof(f345,plain,
    ( ~ v1_zfmisc_1(sK5)
    | v2_tex_2(sK5,sK4)
    | ~ l1_pre_topc(sK4)
    | ~ v2_tdlat_3(sK4)
    | v2_struct_0(sK4) ),
    inference(subsumption_resolution,[],[f297,f54])).

fof(f54,plain,(
    ~ v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f36])).

fof(f297,plain,
    ( ~ v1_zfmisc_1(sK5)
    | v2_tex_2(sK5,sK4)
    | v1_xboole_0(sK5)
    | ~ l1_pre_topc(sK4)
    | ~ v2_tdlat_3(sK4)
    | v2_struct_0(sK4) ),
    inference(resolution,[],[f223,f55])).

fof(f223,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_zfmisc_1(X1)
      | v2_tex_2(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f73,f59])).

fof(f73,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | ~ v1_zfmisc_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f335,plain,(
    spl8_8 ),
    inference(avatar_contradiction_clause,[],[f334])).

fof(f334,plain,
    ( $false
    | spl8_8 ),
    inference(subsumption_resolution,[],[f333,f54])).

fof(f333,plain,
    ( v1_xboole_0(sK5)
    | spl8_8 ),
    inference(subsumption_resolution,[],[f332,f53])).

fof(f332,plain,
    ( ~ l1_pre_topc(sK4)
    | v1_xboole_0(sK5)
    | spl8_8 ),
    inference(subsumption_resolution,[],[f331,f50])).

fof(f331,plain,
    ( v2_struct_0(sK4)
    | ~ l1_pre_topc(sK4)
    | v1_xboole_0(sK5)
    | spl8_8 ),
    inference(subsumption_resolution,[],[f327,f52])).

fof(f327,plain,
    ( ~ v2_tdlat_3(sK4)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK4)
    | v1_xboole_0(sK5)
    | spl8_8 ),
    inference(resolution,[],[f325,f132])).

fof(f132,plain,
    ( ~ sP0(sK5,sK4)
    | spl8_8 ),
    inference(avatar_component_clause,[],[f130])).

fof(f130,plain,
    ( spl8_8
  <=> sP0(sK5,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f325,plain,(
    ! [X0,X1] :
      ( sP0(X1,X0)
      | ~ v2_tdlat_3(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1) ) ),
    inference(duplicate_literal_removal,[],[f322])).

fof(f322,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | v2_struct_0(X0)
      | sP0(X1,X0)
      | v1_xboole_0(X1)
      | sP0(X1,X0) ) ),
    inference(resolution,[],[f254,f313])).

fof(f313,plain,(
    ! [X0,X1] :
      ( ~ v1_zfmisc_1(sK6(X0,X1))
      | v1_xboole_0(X0)
      | sP0(X0,X1) ) ),
    inference(subsumption_resolution,[],[f232,f241])).

fof(f241,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(sK6(X0,X1))
      | sP0(X0,X1) ) ),
    inference(subsumption_resolution,[],[f240,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( sK6(X0,X1) != X0
      | sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( sK6(X0,X1) != X0
          & r1_tarski(X0,sK6(X0,X1))
          & v2_tex_2(sK6(X0,X1),X1)
          & m1_subset_1(sK6(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) ) )
      & ( ! [X3] :
            ( X0 = X3
            | ~ r1_tarski(X0,X3)
            | ~ v2_tex_2(X3,X1)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f42,f43])).

fof(f43,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X0 != X2
          & r1_tarski(X0,X2)
          & v2_tex_2(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( sK6(X0,X1) != X0
        & r1_tarski(X0,sK6(X0,X1))
        & v2_tex_2(sK6(X0,X1),X1)
        & m1_subset_1(sK6(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
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
    inference(rectify,[],[f41])).

fof(f41,plain,(
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

fof(f240,plain,(
    ! [X0,X1] :
      ( sK6(X0,X1) = X0
      | ~ v1_xboole_0(sK6(X0,X1))
      | sP0(X0,X1) ) ),
    inference(resolution,[],[f140,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,sK6(X0,X1))
      | sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f140,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(trivial_inequality_removal,[],[f139])).

fof(f139,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k1_xboole_0
      | X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f79,f105])).

% (554)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
fof(f105,plain,(
    ! [X0,X1] :
      ( k6_subset_1(X0,X1) = k1_xboole_0
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f96,f76])).

fof(f76,plain,(
    ! [X0] :
      ( r2_hidden(sK7(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ( sP3(sK7(X0),X0)
        & r2_hidden(sK7(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f31,f48])).

fof(f48,plain,(
    ! [X0] :
      ( ? [X1] :
          ( sP3(X1,X0)
          & r2_hidden(X1,X0) )
     => ( sP3(sK7(X0),X0)
        & r2_hidden(sK7(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] :
          ( sP3(X1,X0)
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(definition_folding,[],[f23,f30])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ! [X2,X3] :
          ( k4_tarski(X2,X3) != X1
          | ( ~ r2_hidden(X3,X0)
            & ~ r2_hidden(X2,X0) ) )
      | ~ sP3(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3] :
                  ~ ( k4_tarski(X2,X3) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).

fof(f96,plain,(
    ! [X2,X3,X1] :
      ( ~ r2_hidden(X2,k6_subset_1(X1,X3))
      | ~ v1_xboole_0(X1) ) ),
    inference(resolution,[],[f80,f78])).

fof(f78,plain,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_subset_1)).

fof(f80,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f79,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l48_tex_2)).

fof(f232,plain,(
    ! [X0,X1] :
      ( ~ v1_zfmisc_1(sK6(X0,X1))
      | v1_xboole_0(sK6(X0,X1))
      | v1_xboole_0(X0)
      | sP0(X0,X1) ) ),
    inference(subsumption_resolution,[],[f231,f69])).

fof(f231,plain,(
    ! [X0,X1] :
      ( sK6(X0,X1) = X0
      | ~ v1_zfmisc_1(sK6(X0,X1))
      | v1_xboole_0(sK6(X0,X1))
      | v1_xboole_0(X0)
      | sP0(X0,X1) ) ),
    inference(resolution,[],[f58,f68])).

fof(f58,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

fof(f254,plain,(
    ! [X4,X3] :
      ( v1_zfmisc_1(sK6(X3,X4))
      | ~ l1_pre_topc(X4)
      | ~ v2_tdlat_3(X4)
      | v2_struct_0(X4)
      | sP0(X3,X4) ) ),
    inference(subsumption_resolution,[],[f245,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( v2_tex_2(sK6(X0,X1),X1)
      | sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f245,plain,(
    ! [X4,X3] :
      ( ~ v2_tex_2(sK6(X3,X4),X4)
      | v1_zfmisc_1(sK6(X3,X4))
      | ~ l1_pre_topc(X4)
      | ~ v2_tdlat_3(X4)
      | v2_struct_0(X4)
      | sP0(X3,X4) ) ),
    inference(resolution,[],[f225,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK6(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))
      | sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f217,plain,
    ( ~ spl8_7
    | ~ spl8_8
    | spl8_10 ),
    inference(avatar_split_clause,[],[f216,f202,f130,f126])).

fof(f216,plain,
    ( ~ sP0(sK5,sK4)
    | ~ v2_tex_2(sK5,sK4)
    | spl8_10 ),
    inference(resolution,[],[f203,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
      | ~ sP0(X1,X0)
      | ~ v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f203,plain,
    ( ~ sP1(sK4,sK5)
    | spl8_10 ),
    inference(avatar_component_clause,[],[f202])).

fof(f215,plain,
    ( ~ spl8_10
    | spl8_1 ),
    inference(avatar_split_clause,[],[f123,f84,f202])).

fof(f84,plain,
    ( spl8_1
  <=> v3_tex_2(sK5,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f123,plain,
    ( ~ sP1(sK4,sK5)
    | spl8_1 ),
    inference(subsumption_resolution,[],[f121,f86])).

fof(f86,plain,
    ( ~ v3_tex_2(sK5,sK4)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f84])).

fof(f121,plain,
    ( ~ sP1(sK4,sK5)
    | v3_tex_2(sK5,sK4) ),
    inference(resolution,[],[f120,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ sP2(X0,X1)
      | ~ sP1(X1,X0)
      | v3_tex_2(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( ( v3_tex_2(X0,X1)
          | ~ sP1(X1,X0) )
        & ( sP1(X1,X0)
          | ~ v3_tex_2(X0,X1) ) )
      | ~ sP2(X0,X1) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
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

fof(f120,plain,(
    sP2(sK5,sK4) ),
    inference(subsumption_resolution,[],[f117,f53])).

fof(f117,plain,
    ( sP2(sK5,sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(resolution,[],[f70,f55])).

fof(f70,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tex_2)).

fof(f205,plain,
    ( spl8_10
    | ~ spl8_1 ),
    inference(avatar_split_clause,[],[f122,f84,f202])).

fof(f122,plain,
    ( ~ v3_tex_2(sK5,sK4)
    | sP1(sK4,sK5) ),
    inference(resolution,[],[f120,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ sP2(X0,X1)
      | ~ v3_tex_2(X0,X1)
      | sP1(X1,X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f92,plain,
    ( spl8_1
    | spl8_2 ),
    inference(avatar_split_clause,[],[f56,f88,f84])).

fof(f56,plain,
    ( v1_zfmisc_1(sK5)
    | v3_tex_2(sK5,sK4) ),
    inference(cnf_transformation,[],[f36])).

fof(f91,plain,
    ( ~ spl8_1
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f57,f88,f84])).

fof(f57,plain,
    ( ~ v1_zfmisc_1(sK5)
    | ~ v3_tex_2(sK5,sK4) ),
    inference(cnf_transformation,[],[f36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:20:15 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.50  % (544)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.51  % (562)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.51  % (560)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.51  % (543)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.51  % (547)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.51  % (544)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.52  % (555)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.52  % (551)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.52  % (547)Refutation not found, incomplete strategy% (547)------------------------------
% 0.21/0.52  % (547)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (547)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (547)Memory used [KB]: 1663
% 0.21/0.52  % (547)Time elapsed: 0.098 s
% 0.21/0.52  % (547)------------------------------
% 0.21/0.52  % (547)------------------------------
% 0.21/0.52  % (550)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.52  % (563)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.52  % (542)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.52  % (564)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.52  % (553)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.52  % (556)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.52  % (552)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f359,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f91,f92,f205,f215,f217,f335,f349,f353,f358])).
% 0.21/0.52  fof(f358,plain,(
% 0.21/0.52    spl8_7 | ~spl8_10),
% 0.21/0.52    inference(avatar_split_clause,[],[f356,f202,f126])).
% 0.21/0.52  fof(f126,plain,(
% 0.21/0.52    spl8_7 <=> v2_tex_2(sK5,sK4)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 0.21/0.52  fof(f202,plain,(
% 0.21/0.52    spl8_10 <=> sP1(sK4,sK5)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 0.21/0.52  fof(f356,plain,(
% 0.21/0.52    v2_tex_2(sK5,sK4) | ~spl8_10),
% 0.21/0.52    inference(resolution,[],[f204,f62])).
% 0.21/0.52  % (545)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.52  fof(f62,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~sP1(X0,X1) | v2_tex_2(X1,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f40])).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    ! [X0,X1] : ((sP1(X0,X1) | ~sP0(X1,X0) | ~v2_tex_2(X1,X0)) & ((sP0(X1,X0) & v2_tex_2(X1,X0)) | ~sP1(X0,X1)))),
% 0.21/0.52    inference(flattening,[],[f39])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    ! [X0,X1] : ((sP1(X0,X1) | (~sP0(X1,X0) | ~v2_tex_2(X1,X0))) & ((sP0(X1,X0) & v2_tex_2(X1,X0)) | ~sP1(X0,X1)))),
% 0.21/0.52    inference(nnf_transformation,[],[f27])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ! [X0,X1] : (sP1(X0,X1) <=> (sP0(X1,X0) & v2_tex_2(X1,X0)))),
% 0.21/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.52  fof(f204,plain,(
% 0.21/0.52    sP1(sK4,sK5) | ~spl8_10),
% 0.21/0.52    inference(avatar_component_clause,[],[f202])).
% 0.21/0.52  fof(f353,plain,(
% 0.21/0.52    spl8_2 | ~spl8_7),
% 0.21/0.52    inference(avatar_split_clause,[],[f352,f126,f88])).
% 0.21/0.52  fof(f88,plain,(
% 0.21/0.52    spl8_2 <=> v1_zfmisc_1(sK5)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.21/0.52  fof(f352,plain,(
% 0.21/0.52    ~v2_tex_2(sK5,sK4) | v1_zfmisc_1(sK5)),
% 0.21/0.52    inference(subsumption_resolution,[],[f351,f50])).
% 0.21/0.52  fof(f50,plain,(
% 0.21/0.52    ~v2_struct_0(sK4)),
% 0.21/0.52    inference(cnf_transformation,[],[f36])).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    ((~v1_zfmisc_1(sK5) | ~v3_tex_2(sK5,sK4)) & (v1_zfmisc_1(sK5) | v3_tex_2(sK5,sK4)) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) & ~v1_xboole_0(sK5)) & l1_pre_topc(sK4) & v2_tdlat_3(sK4) & v2_pre_topc(sK4) & ~v2_struct_0(sK4)),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f33,f35,f34])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,sK4)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,sK4)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) & ~v1_xboole_0(X1)) & l1_pre_topc(sK4) & v2_tdlat_3(sK4) & v2_pre_topc(sK4) & ~v2_struct_0(sK4))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    ? [X1] : ((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,sK4)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,sK4)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) & ~v1_xboole_0(X1)) => ((~v1_zfmisc_1(sK5) | ~v3_tex_2(sK5,sK4)) & (v1_zfmisc_1(sK5) | v3_tex_2(sK5,sK4)) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) & ~v1_xboole_0(sK5))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.52    inference(flattening,[],[f32])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : (((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.52    inference(nnf_transformation,[],[f13])).
% 0.21/0.52  fof(f13,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.52    inference(flattening,[],[f12])).
% 0.21/0.52  fof(f12,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f11])).
% 0.21/0.52  fof(f11,negated_conjecture,(
% 0.21/0.52    ~! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v3_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 0.21/0.52    inference(negated_conjecture,[],[f10])).
% 0.21/0.52  fof(f10,conjecture,(
% 0.21/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v3_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_tex_2)).
% 0.21/0.52  fof(f351,plain,(
% 0.21/0.52    ~v2_tex_2(sK5,sK4) | v1_zfmisc_1(sK5) | v2_struct_0(sK4)),
% 0.21/0.52    inference(subsumption_resolution,[],[f350,f52])).
% 0.21/0.52  fof(f52,plain,(
% 0.21/0.52    v2_tdlat_3(sK4)),
% 0.21/0.52    inference(cnf_transformation,[],[f36])).
% 0.21/0.52  fof(f350,plain,(
% 0.21/0.52    ~v2_tex_2(sK5,sK4) | v1_zfmisc_1(sK5) | ~v2_tdlat_3(sK4) | v2_struct_0(sK4)),
% 0.21/0.52    inference(subsumption_resolution,[],[f244,f53])).
% 0.21/0.52  fof(f53,plain,(
% 0.21/0.52    l1_pre_topc(sK4)),
% 0.21/0.52    inference(cnf_transformation,[],[f36])).
% 0.21/0.52  fof(f244,plain,(
% 0.21/0.52    ~v2_tex_2(sK5,sK4) | v1_zfmisc_1(sK5) | ~l1_pre_topc(sK4) | ~v2_tdlat_3(sK4) | v2_struct_0(sK4)),
% 0.21/0.52    inference(resolution,[],[f225,f55])).
% 0.21/0.52  fof(f55,plain,(
% 0.21/0.52    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))),
% 0.21/0.52    inference(cnf_transformation,[],[f36])).
% 0.21/0.52  fof(f225,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | v1_zfmisc_1(X1) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | v2_struct_0(X0)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f224,f71])).
% 0.21/0.52  fof(f71,plain,(
% 0.21/0.52    ( ! [X0] : (v1_zfmisc_1(X0) | ~v1_xboole_0(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f20])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ! [X0] : (v1_zfmisc_1(X0) | ~v1_xboole_0(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0] : (v1_xboole_0(X0) => v1_zfmisc_1(X0))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_zfmisc_1)).
% 0.21/0.52  fof(f224,plain,(
% 0.21/0.52    ( ! [X0,X1] : (v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | v2_struct_0(X0)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f72,f59])).
% 0.21/0.52  fof(f59,plain,(
% 0.21/0.52    ( ! [X0] : (v2_pre_topc(X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f17])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ! [X0] : (v2_pre_topc(X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(flattening,[],[f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ! [X0] : ((v2_pre_topc(X0) | ~v2_tdlat_3(X0)) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0] : (l1_pre_topc(X0) => (v2_tdlat_3(X0) => v2_pre_topc(X0)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tdlat_3)).
% 0.21/0.52  fof(f72,plain,(
% 0.21/0.52    ( ! [X0,X1] : (v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f45])).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ~v1_zfmisc_1(X1)) & (v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.52    inference(nnf_transformation,[],[f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.52    inference(flattening,[],[f21])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,axiom,(
% 0.21/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tex_2)).
% 0.21/0.52  fof(f349,plain,(
% 0.21/0.52    spl8_7 | ~spl8_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f348,f88,f126])).
% 0.21/0.52  fof(f348,plain,(
% 0.21/0.52    ~v1_zfmisc_1(sK5) | v2_tex_2(sK5,sK4)),
% 0.21/0.52    inference(subsumption_resolution,[],[f347,f50])).
% 0.21/0.52  fof(f347,plain,(
% 0.21/0.52    ~v1_zfmisc_1(sK5) | v2_tex_2(sK5,sK4) | v2_struct_0(sK4)),
% 0.21/0.52    inference(subsumption_resolution,[],[f346,f52])).
% 0.21/0.52  fof(f346,plain,(
% 0.21/0.52    ~v1_zfmisc_1(sK5) | v2_tex_2(sK5,sK4) | ~v2_tdlat_3(sK4) | v2_struct_0(sK4)),
% 0.21/0.52    inference(subsumption_resolution,[],[f345,f53])).
% 0.21/0.52  fof(f345,plain,(
% 0.21/0.52    ~v1_zfmisc_1(sK5) | v2_tex_2(sK5,sK4) | ~l1_pre_topc(sK4) | ~v2_tdlat_3(sK4) | v2_struct_0(sK4)),
% 0.21/0.52    inference(subsumption_resolution,[],[f297,f54])).
% 0.21/0.52  fof(f54,plain,(
% 0.21/0.52    ~v1_xboole_0(sK5)),
% 0.21/0.52    inference(cnf_transformation,[],[f36])).
% 0.21/0.52  fof(f297,plain,(
% 0.21/0.52    ~v1_zfmisc_1(sK5) | v2_tex_2(sK5,sK4) | v1_xboole_0(sK5) | ~l1_pre_topc(sK4) | ~v2_tdlat_3(sK4) | v2_struct_0(sK4)),
% 0.21/0.52    inference(resolution,[],[f223,f55])).
% 0.21/0.52  fof(f223,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_zfmisc_1(X1) | v2_tex_2(X1,X0) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | v2_struct_0(X0)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f73,f59])).
% 0.21/0.52  fof(f73,plain,(
% 0.21/0.52    ( ! [X0,X1] : (v2_tex_2(X1,X0) | ~v1_zfmisc_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f45])).
% 0.21/0.52  fof(f335,plain,(
% 0.21/0.52    spl8_8),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f334])).
% 0.21/0.52  fof(f334,plain,(
% 0.21/0.52    $false | spl8_8),
% 0.21/0.52    inference(subsumption_resolution,[],[f333,f54])).
% 0.21/0.52  fof(f333,plain,(
% 0.21/0.52    v1_xboole_0(sK5) | spl8_8),
% 0.21/0.52    inference(subsumption_resolution,[],[f332,f53])).
% 0.21/0.52  fof(f332,plain,(
% 0.21/0.52    ~l1_pre_topc(sK4) | v1_xboole_0(sK5) | spl8_8),
% 0.21/0.52    inference(subsumption_resolution,[],[f331,f50])).
% 0.21/0.52  fof(f331,plain,(
% 0.21/0.52    v2_struct_0(sK4) | ~l1_pre_topc(sK4) | v1_xboole_0(sK5) | spl8_8),
% 0.21/0.52    inference(subsumption_resolution,[],[f327,f52])).
% 0.21/0.52  fof(f327,plain,(
% 0.21/0.52    ~v2_tdlat_3(sK4) | v2_struct_0(sK4) | ~l1_pre_topc(sK4) | v1_xboole_0(sK5) | spl8_8),
% 0.21/0.52    inference(resolution,[],[f325,f132])).
% 0.21/0.52  fof(f132,plain,(
% 0.21/0.52    ~sP0(sK5,sK4) | spl8_8),
% 0.21/0.52    inference(avatar_component_clause,[],[f130])).
% 0.21/0.52  fof(f130,plain,(
% 0.21/0.52    spl8_8 <=> sP0(sK5,sK4)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 0.21/0.52  fof(f325,plain,(
% 0.21/0.52    ( ! [X0,X1] : (sP0(X1,X0) | ~v2_tdlat_3(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | v1_xboole_0(X1)) )),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f322])).
% 0.21/0.52  fof(f322,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | v2_struct_0(X0) | sP0(X1,X0) | v1_xboole_0(X1) | sP0(X1,X0)) )),
% 0.21/0.52    inference(resolution,[],[f254,f313])).
% 0.21/0.52  fof(f313,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v1_zfmisc_1(sK6(X0,X1)) | v1_xboole_0(X0) | sP0(X0,X1)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f232,f241])).
% 0.21/0.52  fof(f241,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v1_xboole_0(sK6(X0,X1)) | sP0(X0,X1)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f240,f69])).
% 0.21/0.52  fof(f69,plain,(
% 0.21/0.52    ( ! [X0,X1] : (sK6(X0,X1) != X0 | sP0(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f44])).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    ! [X0,X1] : ((sP0(X0,X1) | (sK6(X0,X1) != X0 & r1_tarski(X0,sK6(X0,X1)) & v2_tex_2(sK6(X0,X1),X1) & m1_subset_1(sK6(X0,X1),k1_zfmisc_1(u1_struct_0(X1))))) & (! [X3] : (X0 = X3 | ~r1_tarski(X0,X3) | ~v2_tex_2(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~sP0(X0,X1)))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f42,f43])).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    ! [X1,X0] : (? [X2] : (X0 != X2 & r1_tarski(X0,X2) & v2_tex_2(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) => (sK6(X0,X1) != X0 & r1_tarski(X0,sK6(X0,X1)) & v2_tex_2(sK6(X0,X1),X1) & m1_subset_1(sK6(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : (X0 != X2 & r1_tarski(X0,X2) & v2_tex_2(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X3] : (X0 = X3 | ~r1_tarski(X0,X3) | ~v2_tex_2(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~sP0(X0,X1)))),
% 0.21/0.52    inference(rectify,[],[f41])).
% 0.21/0.52  fof(f41,plain,(
% 0.21/0.52    ! [X1,X0] : ((sP0(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP0(X1,X0)))),
% 0.21/0.52    inference(nnf_transformation,[],[f26])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ! [X1,X0] : (sP0(X1,X0) <=> ! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.52  fof(f240,plain,(
% 0.21/0.52    ( ! [X0,X1] : (sK6(X0,X1) = X0 | ~v1_xboole_0(sK6(X0,X1)) | sP0(X0,X1)) )),
% 0.21/0.52    inference(resolution,[],[f140,f68])).
% 0.21/0.52  fof(f68,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_tarski(X0,sK6(X0,X1)) | sP0(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f44])).
% 0.21/0.52  fof(f140,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 0.21/0.52    inference(trivial_inequality_removal,[],[f139])).
% 0.21/0.52  fof(f139,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k1_xboole_0 != k1_xboole_0 | X0 = X1 | ~r1_tarski(X1,X0) | ~v1_xboole_0(X0)) )),
% 0.21/0.52    inference(superposition,[],[f79,f105])).
% 0.21/0.52  % (554)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.52  fof(f105,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k6_subset_1(X0,X1) = k1_xboole_0 | ~v1_xboole_0(X0)) )),
% 0.21/0.52    inference(resolution,[],[f96,f76])).
% 0.21/0.52  fof(f76,plain,(
% 0.21/0.52    ( ! [X0] : (r2_hidden(sK7(X0),X0) | k1_xboole_0 = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f49])).
% 0.21/0.52  fof(f49,plain,(
% 0.21/0.52    ! [X0] : ((sP3(sK7(X0),X0) & r2_hidden(sK7(X0),X0)) | k1_xboole_0 = X0)),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f31,f48])).
% 0.21/0.52  fof(f48,plain,(
% 0.21/0.52    ! [X0] : (? [X1] : (sP3(X1,X0) & r2_hidden(X1,X0)) => (sP3(sK7(X0),X0) & r2_hidden(sK7(X0),X0)))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ! [X0] : (? [X1] : (sP3(X1,X0) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.21/0.52    inference(definition_folding,[],[f23,f30])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ! [X1,X0] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) | ~sP3(X1,X0))),
% 0.21/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.21/0.52    inference(ennf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0] : ~(! [X1] : ~(! [X2,X3] : ~(k4_tarski(X2,X3) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).
% 0.21/0.52  fof(f96,plain,(
% 0.21/0.52    ( ! [X2,X3,X1] : (~r2_hidden(X2,k6_subset_1(X1,X3)) | ~v1_xboole_0(X1)) )),
% 0.21/0.52    inference(resolution,[],[f80,f78])).
% 0.21/0.52  fof(f78,plain,(
% 0.21/0.52    ( ! [X0,X1] : (m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_subset_1)).
% 0.21/0.52  fof(f80,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2) | ~r2_hidden(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f25])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 0.21/0.52  fof(f79,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k1_xboole_0 != k6_subset_1(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f24])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ! [X0,X1] : (k1_xboole_0 != k6_subset_1(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,axiom,(
% 0.21/0.52    ! [X0,X1] : ~(k1_xboole_0 = k6_subset_1(X1,X0) & X0 != X1 & r1_tarski(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l48_tex_2)).
% 0.21/0.52  fof(f232,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v1_zfmisc_1(sK6(X0,X1)) | v1_xboole_0(sK6(X0,X1)) | v1_xboole_0(X0) | sP0(X0,X1)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f231,f69])).
% 0.21/0.52  fof(f231,plain,(
% 0.21/0.52    ( ! [X0,X1] : (sK6(X0,X1) = X0 | ~v1_zfmisc_1(sK6(X0,X1)) | v1_xboole_0(sK6(X0,X1)) | v1_xboole_0(X0) | sP0(X0,X1)) )),
% 0.21/0.52    inference(resolution,[],[f58,f68])).
% 0.21/0.52  fof(f58,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r1_tarski(X0,X1) | X0 = X1 | ~v1_zfmisc_1(X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f15])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.21/0.52    inference(flattening,[],[f14])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : ((X0 = X1 | ~r1_tarski(X0,X1)) | (~v1_zfmisc_1(X1) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,axiom,(
% 0.21/0.52    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).
% 0.21/0.52  fof(f254,plain,(
% 0.21/0.52    ( ! [X4,X3] : (v1_zfmisc_1(sK6(X3,X4)) | ~l1_pre_topc(X4) | ~v2_tdlat_3(X4) | v2_struct_0(X4) | sP0(X3,X4)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f245,f67])).
% 0.21/0.52  fof(f67,plain,(
% 0.21/0.52    ( ! [X0,X1] : (v2_tex_2(sK6(X0,X1),X1) | sP0(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f44])).
% 0.21/0.52  fof(f245,plain,(
% 0.21/0.52    ( ! [X4,X3] : (~v2_tex_2(sK6(X3,X4),X4) | v1_zfmisc_1(sK6(X3,X4)) | ~l1_pre_topc(X4) | ~v2_tdlat_3(X4) | v2_struct_0(X4) | sP0(X3,X4)) )),
% 0.21/0.52    inference(resolution,[],[f225,f66])).
% 0.21/0.52  fof(f66,plain,(
% 0.21/0.52    ( ! [X0,X1] : (m1_subset_1(sK6(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) | sP0(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f44])).
% 0.21/0.52  fof(f217,plain,(
% 0.21/0.52    ~spl8_7 | ~spl8_8 | spl8_10),
% 0.21/0.52    inference(avatar_split_clause,[],[f216,f202,f130,f126])).
% 0.21/0.52  fof(f216,plain,(
% 0.21/0.52    ~sP0(sK5,sK4) | ~v2_tex_2(sK5,sK4) | spl8_10),
% 0.21/0.52    inference(resolution,[],[f203,f64])).
% 0.21/0.52  fof(f64,plain,(
% 0.21/0.52    ( ! [X0,X1] : (sP1(X0,X1) | ~sP0(X1,X0) | ~v2_tex_2(X1,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f40])).
% 0.21/0.52  fof(f203,plain,(
% 0.21/0.52    ~sP1(sK4,sK5) | spl8_10),
% 0.21/0.52    inference(avatar_component_clause,[],[f202])).
% 0.21/0.52  fof(f215,plain,(
% 0.21/0.52    ~spl8_10 | spl8_1),
% 0.21/0.52    inference(avatar_split_clause,[],[f123,f84,f202])).
% 0.21/0.52  fof(f84,plain,(
% 0.21/0.52    spl8_1 <=> v3_tex_2(sK5,sK4)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.21/0.52  fof(f123,plain,(
% 0.21/0.52    ~sP1(sK4,sK5) | spl8_1),
% 0.21/0.52    inference(subsumption_resolution,[],[f121,f86])).
% 0.21/0.52  fof(f86,plain,(
% 0.21/0.52    ~v3_tex_2(sK5,sK4) | spl8_1),
% 0.21/0.52    inference(avatar_component_clause,[],[f84])).
% 0.21/0.52  fof(f121,plain,(
% 0.21/0.52    ~sP1(sK4,sK5) | v3_tex_2(sK5,sK4)),
% 0.21/0.52    inference(resolution,[],[f120,f61])).
% 0.21/0.52  fof(f61,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~sP2(X0,X1) | ~sP1(X1,X0) | v3_tex_2(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f38])).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    ! [X0,X1] : (((v3_tex_2(X0,X1) | ~sP1(X1,X0)) & (sP1(X1,X0) | ~v3_tex_2(X0,X1))) | ~sP2(X0,X1))),
% 0.21/0.52    inference(rectify,[],[f37])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    ! [X1,X0] : (((v3_tex_2(X1,X0) | ~sP1(X0,X1)) & (sP1(X0,X1) | ~v3_tex_2(X1,X0))) | ~sP2(X1,X0))),
% 0.21/0.52    inference(nnf_transformation,[],[f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ! [X1,X0] : ((v3_tex_2(X1,X0) <=> sP1(X0,X1)) | ~sP2(X1,X0))),
% 0.21/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.21/0.52  fof(f120,plain,(
% 0.21/0.52    sP2(sK5,sK4)),
% 0.21/0.52    inference(subsumption_resolution,[],[f117,f53])).
% 0.21/0.52  fof(f117,plain,(
% 0.21/0.52    sP2(sK5,sK4) | ~l1_pre_topc(sK4)),
% 0.21/0.52    inference(resolution,[],[f70,f55])).
% 0.21/0.52  fof(f70,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | sP2(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f29])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (sP2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(definition_folding,[],[f19,f28,f27,f26])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(flattening,[],[f18])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : ((X1 = X2 | (~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,axiom,(
% 0.21/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v2_tex_2(X2,X0)) => X1 = X2)) & v2_tex_2(X1,X0)))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tex_2)).
% 0.21/0.52  fof(f205,plain,(
% 0.21/0.52    spl8_10 | ~spl8_1),
% 0.21/0.52    inference(avatar_split_clause,[],[f122,f84,f202])).
% 0.21/0.52  fof(f122,plain,(
% 0.21/0.52    ~v3_tex_2(sK5,sK4) | sP1(sK4,sK5)),
% 0.21/0.52    inference(resolution,[],[f120,f60])).
% 0.21/0.52  fof(f60,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~sP2(X0,X1) | ~v3_tex_2(X0,X1) | sP1(X1,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f38])).
% 0.21/0.52  fof(f92,plain,(
% 0.21/0.52    spl8_1 | spl8_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f56,f88,f84])).
% 0.21/0.52  fof(f56,plain,(
% 0.21/0.52    v1_zfmisc_1(sK5) | v3_tex_2(sK5,sK4)),
% 0.21/0.52    inference(cnf_transformation,[],[f36])).
% 0.21/0.52  fof(f91,plain,(
% 0.21/0.52    ~spl8_1 | ~spl8_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f57,f88,f84])).
% 0.21/0.52  fof(f57,plain,(
% 0.21/0.52    ~v1_zfmisc_1(sK5) | ~v3_tex_2(sK5,sK4)),
% 0.21/0.52    inference(cnf_transformation,[],[f36])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (544)------------------------------
% 0.21/0.52  % (544)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (544)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (544)Memory used [KB]: 6268
% 0.21/0.52  % (544)Time elapsed: 0.098 s
% 0.21/0.52  % (544)------------------------------
% 0.21/0.52  % (544)------------------------------
% 0.21/0.52  % (533)Success in time 0.165 s
%------------------------------------------------------------------------------
