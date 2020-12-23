%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:24 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  163 ( 464 expanded)
%              Number of leaves         :   25 ( 184 expanded)
%              Depth                    :   13
%              Number of atoms          :  832 (2036 expanded)
%              Number of equality atoms :   18 (  40 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f377,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f55,f59,f63,f67,f71,f75,f79,f91,f149,f163,f178,f229,f233,f237,f254,f298,f369,f376])).

fof(f376,plain,
    ( ~ spl4_21
    | spl4_22
    | ~ spl4_23
    | ~ spl4_27
    | ~ spl4_38 ),
    inference(avatar_contradiction_clause,[],[f375])).

fof(f375,plain,
    ( $false
    | ~ spl4_21
    | spl4_22
    | ~ spl4_23
    | ~ spl4_27
    | ~ spl4_38 ),
    inference(subsumption_resolution,[],[f374,f232])).

fof(f232,plain,
    ( ~ v2_struct_0(sK2(sK0,sK3(sK0,u1_struct_0(sK1))))
    | spl4_22 ),
    inference(avatar_component_clause,[],[f231])).

fof(f231,plain,
    ( spl4_22
  <=> v2_struct_0(sK2(sK0,sK3(sK0,u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f374,plain,
    ( v2_struct_0(sK2(sK0,sK3(sK0,u1_struct_0(sK1))))
    | ~ spl4_21
    | ~ spl4_23
    | ~ spl4_27
    | ~ spl4_38 ),
    inference(subsumption_resolution,[],[f373,f297])).

fof(f297,plain,
    ( m1_pre_topc(sK1,sK2(sK0,sK3(sK0,u1_struct_0(sK1))))
    | ~ spl4_27 ),
    inference(avatar_component_clause,[],[f296])).

fof(f296,plain,
    ( spl4_27
  <=> m1_pre_topc(sK1,sK2(sK0,sK3(sK0,u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f373,plain,
    ( ~ m1_pre_topc(sK1,sK2(sK0,sK3(sK0,u1_struct_0(sK1))))
    | v2_struct_0(sK2(sK0,sK3(sK0,u1_struct_0(sK1))))
    | ~ spl4_21
    | ~ spl4_23
    | ~ spl4_38 ),
    inference(subsumption_resolution,[],[f372,f236])).

fof(f236,plain,
    ( m1_pre_topc(sK2(sK0,sK3(sK0,u1_struct_0(sK1))),sK0)
    | ~ spl4_23 ),
    inference(avatar_component_clause,[],[f235])).

fof(f235,plain,
    ( spl4_23
  <=> m1_pre_topc(sK2(sK0,sK3(sK0,u1_struct_0(sK1))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f372,plain,
    ( ~ m1_pre_topc(sK2(sK0,sK3(sK0,u1_struct_0(sK1))),sK0)
    | ~ m1_pre_topc(sK1,sK2(sK0,sK3(sK0,u1_struct_0(sK1))))
    | v2_struct_0(sK2(sK0,sK3(sK0,u1_struct_0(sK1))))
    | ~ spl4_21
    | ~ spl4_38 ),
    inference(subsumption_resolution,[],[f370,f228])).

fof(f228,plain,
    ( v1_pre_topc(sK2(sK0,sK3(sK0,u1_struct_0(sK1))))
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f227])).

fof(f227,plain,
    ( spl4_21
  <=> v1_pre_topc(sK2(sK0,sK3(sK0,u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f370,plain,
    ( ~ v1_pre_topc(sK2(sK0,sK3(sK0,u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK2(sK0,sK3(sK0,u1_struct_0(sK1))),sK0)
    | ~ m1_pre_topc(sK1,sK2(sK0,sK3(sK0,u1_struct_0(sK1))))
    | v2_struct_0(sK2(sK0,sK3(sK0,u1_struct_0(sK1))))
    | ~ spl4_38 ),
    inference(resolution,[],[f368,f25])).

fof(f25,plain,(
    ! [X2] :
      ( ~ v4_tex_2(X2,sK0)
      | ~ v1_pre_topc(X2)
      | ~ m1_pre_topc(X2,sK0)
      | ~ m1_pre_topc(sK1,X2)
      | v2_struct_0(X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( ~ v4_tex_2(X2,X0)
              | ~ m1_pre_topc(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2)
              | v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & v1_tdlat_3(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( ~ v4_tex_2(X2,X0)
              | ~ m1_pre_topc(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2)
              | v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & v1_tdlat_3(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v3_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & v1_tdlat_3(X1)
              & ~ v2_struct_0(X1) )
           => ? [X2] :
                ( v4_tex_2(X2,X0)
                & m1_pre_topc(X1,X2)
                & m1_pre_topc(X2,X0)
                & v1_pre_topc(X2)
                & ~ v2_struct_0(X2) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & v1_tdlat_3(X1)
            & ~ v2_struct_0(X1) )
         => ? [X2] :
              ( v4_tex_2(X2,X0)
              & m1_pre_topc(X1,X2)
              & m1_pre_topc(X2,X0)
              & v1_pre_topc(X2)
              & ~ v2_struct_0(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_tex_2)).

fof(f368,plain,
    ( v4_tex_2(sK2(sK0,sK3(sK0,u1_struct_0(sK1))),sK0)
    | ~ spl4_38 ),
    inference(avatar_component_clause,[],[f367])).

fof(f367,plain,
    ( spl4_38
  <=> v4_tex_2(sK2(sK0,sK3(sK0,u1_struct_0(sK1))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).

fof(f369,plain,
    ( spl4_38
    | spl4_3
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_17
    | ~ spl4_23
    | ~ spl4_24 ),
    inference(avatar_split_clause,[],[f365,f252,f235,f176,f147,f73,f61,f367])).

fof(f61,plain,
    ( spl4_3
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f73,plain,
    ( spl4_6
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f147,plain,
    ( spl4_10
  <=> v3_tex_2(sK3(sK0,u1_struct_0(sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f176,plain,
    ( spl4_17
  <=> m1_subset_1(sK3(sK0,u1_struct_0(sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f252,plain,
    ( spl4_24
  <=> sK3(sK0,u1_struct_0(sK1)) = u1_struct_0(sK2(sK0,sK3(sK0,u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f365,plain,
    ( v4_tex_2(sK2(sK0,sK3(sK0,u1_struct_0(sK1))),sK0)
    | spl4_3
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_17
    | ~ spl4_23
    | ~ spl4_24 ),
    inference(subsumption_resolution,[],[f364,f148])).

fof(f148,plain,
    ( v3_tex_2(sK3(sK0,u1_struct_0(sK1)),sK0)
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f147])).

% (24214)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
fof(f364,plain,
    ( v4_tex_2(sK2(sK0,sK3(sK0,u1_struct_0(sK1))),sK0)
    | ~ v3_tex_2(sK3(sK0,u1_struct_0(sK1)),sK0)
    | spl4_3
    | ~ spl4_6
    | ~ spl4_17
    | ~ spl4_23
    | ~ spl4_24 ),
    inference(subsumption_resolution,[],[f363,f62])).

fof(f62,plain,
    ( ~ v2_struct_0(sK0)
    | spl4_3 ),
    inference(avatar_component_clause,[],[f61])).

fof(f363,plain,
    ( v2_struct_0(sK0)
    | v4_tex_2(sK2(sK0,sK3(sK0,u1_struct_0(sK1))),sK0)
    | ~ v3_tex_2(sK3(sK0,u1_struct_0(sK1)),sK0)
    | ~ spl4_6
    | ~ spl4_17
    | ~ spl4_23
    | ~ spl4_24 ),
    inference(subsumption_resolution,[],[f362,f236])).

fof(f362,plain,
    ( ~ m1_pre_topc(sK2(sK0,sK3(sK0,u1_struct_0(sK1))),sK0)
    | v2_struct_0(sK0)
    | v4_tex_2(sK2(sK0,sK3(sK0,u1_struct_0(sK1))),sK0)
    | ~ v3_tex_2(sK3(sK0,u1_struct_0(sK1)),sK0)
    | ~ spl4_6
    | ~ spl4_17
    | ~ spl4_24 ),
    inference(subsumption_resolution,[],[f360,f74])).

fof(f74,plain,
    ( l1_pre_topc(sK0)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f73])).

fof(f360,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK2(sK0,sK3(sK0,u1_struct_0(sK1))),sK0)
    | v2_struct_0(sK0)
    | v4_tex_2(sK2(sK0,sK3(sK0,u1_struct_0(sK1))),sK0)
    | ~ v3_tex_2(sK3(sK0,u1_struct_0(sK1)),sK0)
    | ~ spl4_17
    | ~ spl4_24 ),
    inference(resolution,[],[f263,f177])).

fof(f177,plain,
    ( m1_subset_1(sK3(sK0,u1_struct_0(sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f176])).

fof(f263,plain,
    ( ! [X8] :
        ( ~ m1_subset_1(sK3(sK0,u1_struct_0(sK1)),k1_zfmisc_1(u1_struct_0(X8)))
        | ~ l1_pre_topc(X8)
        | ~ m1_pre_topc(sK2(sK0,sK3(sK0,u1_struct_0(sK1))),X8)
        | v2_struct_0(X8)
        | v4_tex_2(sK2(sK0,sK3(sK0,u1_struct_0(sK1))),X8)
        | ~ v3_tex_2(sK3(sK0,u1_struct_0(sK1)),X8) )
    | ~ spl4_24 ),
    inference(superposition,[],[f48,f253])).

fof(f253,plain,
    ( sK3(sK0,u1_struct_0(sK1)) = u1_struct_0(sK2(sK0,sK3(sK0,u1_struct_0(sK1))))
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f252])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X0)
      | v4_tex_2(X1,X0)
      | ~ v3_tex_2(u1_struct_0(X1),X0) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X1) != X2
      | v4_tex_2(X1,X0)
      | ~ v3_tex_2(X2,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v3_tex_2(X2,X0)
              <=> v4_tex_2(X1,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v3_tex_2(X2,X0)
              <=> v4_tex_2(X1,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( v3_tex_2(X2,X0)
                <=> v4_tex_2(X1,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_tex_2)).

fof(f298,plain,
    ( spl4_27
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_13
    | ~ spl4_23
    | ~ spl4_24 ),
    inference(avatar_split_clause,[],[f287,f252,f235,f161,f77,f73,f65,f296])).

fof(f65,plain,
    ( spl4_4
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f77,plain,
    ( spl4_7
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f161,plain,
    ( spl4_13
  <=> r1_tarski(u1_struct_0(sK1),sK3(sK0,u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f287,plain,
    ( m1_pre_topc(sK1,sK2(sK0,sK3(sK0,u1_struct_0(sK1))))
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_13
    | ~ spl4_23
    | ~ spl4_24 ),
    inference(subsumption_resolution,[],[f286,f236])).

fof(f286,plain,
    ( m1_pre_topc(sK1,sK2(sK0,sK3(sK0,u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK2(sK0,sK3(sK0,u1_struct_0(sK1))),sK0)
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_13
    | ~ spl4_24 ),
    inference(subsumption_resolution,[],[f271,f162])).

fof(f162,plain,
    ( r1_tarski(u1_struct_0(sK1),sK3(sK0,u1_struct_0(sK1)))
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f161])).

fof(f271,plain,
    ( ~ r1_tarski(u1_struct_0(sK1),sK3(sK0,u1_struct_0(sK1)))
    | m1_pre_topc(sK1,sK2(sK0,sK3(sK0,u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK2(sK0,sK3(sK0,u1_struct_0(sK1))),sK0)
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_24 ),
    inference(superposition,[],[f86,f253])).

fof(f86,plain,
    ( ! [X1] :
        ( ~ r1_tarski(u1_struct_0(sK1),u1_struct_0(X1))
        | m1_pre_topc(sK1,X1)
        | ~ m1_pre_topc(X1,sK0) )
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f85,f66])).

fof(f66,plain,
    ( v2_pre_topc(sK0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f65])).

fof(f85,plain,
    ( ! [X1] :
        ( ~ v2_pre_topc(sK0)
        | ~ m1_pre_topc(X1,sK0)
        | m1_pre_topc(sK1,X1)
        | ~ r1_tarski(u1_struct_0(sK1),u1_struct_0(X1)) )
    | ~ spl4_6
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f81,f74])).

fof(f81,plain,
    ( ! [X1] :
        ( ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ m1_pre_topc(X1,sK0)
        | m1_pre_topc(sK1,X1)
        | ~ r1_tarski(u1_struct_0(sK1),u1_struct_0(X1)) )
    | ~ spl4_7 ),
    inference(resolution,[],[f78,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X2,X0)
      | m1_pre_topc(X1,X2)
      | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_tsep_1)).

fof(f78,plain,
    ( m1_pre_topc(sK1,sK0)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f77])).

fof(f254,plain,
    ( spl4_24
    | spl4_3
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_17 ),
    inference(avatar_split_clause,[],[f218,f176,f147,f73,f65,f61,f252])).

fof(f218,plain,
    ( sK3(sK0,u1_struct_0(sK1)) = u1_struct_0(sK2(sK0,sK3(sK0,u1_struct_0(sK1))))
    | spl4_3
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_17 ),
    inference(subsumption_resolution,[],[f201,f217])).

fof(f217,plain,
    ( ~ v1_xboole_0(sK3(sK0,u1_struct_0(sK1)))
    | spl4_3
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_17 ),
    inference(subsumption_resolution,[],[f216,f148])).

fof(f216,plain,
    ( ~ v1_xboole_0(sK3(sK0,u1_struct_0(sK1)))
    | ~ v3_tex_2(sK3(sK0,u1_struct_0(sK1)),sK0)
    | spl4_3
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_17 ),
    inference(subsumption_resolution,[],[f215,f62])).

fof(f215,plain,
    ( ~ v1_xboole_0(sK3(sK0,u1_struct_0(sK1)))
    | v2_struct_0(sK0)
    | ~ v3_tex_2(sK3(sK0,u1_struct_0(sK1)),sK0)
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_17 ),
    inference(subsumption_resolution,[],[f214,f74])).

fof(f214,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v1_xboole_0(sK3(sK0,u1_struct_0(sK1)))
    | v2_struct_0(sK0)
    | ~ v3_tex_2(sK3(sK0,u1_struct_0(sK1)),sK0)
    | ~ spl4_4
    | ~ spl4_17 ),
    inference(subsumption_resolution,[],[f193,f66])).

fof(f193,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v1_xboole_0(sK3(sK0,u1_struct_0(sK1)))
    | v2_struct_0(sK0)
    | ~ v3_tex_2(sK3(sK0,u1_struct_0(sK1)),sK0)
    | ~ spl4_17 ),
    inference(resolution,[],[f177,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v1_xboole_0(X1)
      | v2_struct_0(X0)
      | ~ v3_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v3_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v3_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
         => ~ v3_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_tex_2)).

fof(f201,plain,
    ( v1_xboole_0(sK3(sK0,u1_struct_0(sK1)))
    | sK3(sK0,u1_struct_0(sK1)) = u1_struct_0(sK2(sK0,sK3(sK0,u1_struct_0(sK1))))
    | spl4_3
    | ~ spl4_6
    | ~ spl4_17 ),
    inference(subsumption_resolution,[],[f200,f62])).

fof(f200,plain,
    ( v1_xboole_0(sK3(sK0,u1_struct_0(sK1)))
    | v2_struct_0(sK0)
    | sK3(sK0,u1_struct_0(sK1)) = u1_struct_0(sK2(sK0,sK3(sK0,u1_struct_0(sK1))))
    | ~ spl4_6
    | ~ spl4_17 ),
    inference(subsumption_resolution,[],[f189,f74])).

fof(f189,plain,
    ( ~ l1_pre_topc(sK0)
    | v1_xboole_0(sK3(sK0,u1_struct_0(sK1)))
    | v2_struct_0(sK0)
    | sK3(sK0,u1_struct_0(sK1)) = u1_struct_0(sK2(sK0,sK3(sK0,u1_struct_0(sK1))))
    | ~ spl4_17 ),
    inference(resolution,[],[f177,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1)
      | v2_struct_0(X0)
      | u1_struct_0(sK2(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_pre_topc(X2)
              & ~ v2_struct_0(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_tsep_1)).

fof(f237,plain,
    ( spl4_23
    | spl4_3
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_17 ),
    inference(avatar_split_clause,[],[f219,f176,f147,f73,f65,f61,f235])).

fof(f219,plain,
    ( m1_pre_topc(sK2(sK0,sK3(sK0,u1_struct_0(sK1))),sK0)
    | spl4_3
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_17 ),
    inference(subsumption_resolution,[],[f199,f217])).

fof(f199,plain,
    ( v1_xboole_0(sK3(sK0,u1_struct_0(sK1)))
    | m1_pre_topc(sK2(sK0,sK3(sK0,u1_struct_0(sK1))),sK0)
    | spl4_3
    | ~ spl4_6
    | ~ spl4_17 ),
    inference(subsumption_resolution,[],[f198,f62])).

fof(f198,plain,
    ( v1_xboole_0(sK3(sK0,u1_struct_0(sK1)))
    | v2_struct_0(sK0)
    | m1_pre_topc(sK2(sK0,sK3(sK0,u1_struct_0(sK1))),sK0)
    | ~ spl4_6
    | ~ spl4_17 ),
    inference(subsumption_resolution,[],[f188,f74])).

fof(f188,plain,
    ( ~ l1_pre_topc(sK0)
    | v1_xboole_0(sK3(sK0,u1_struct_0(sK1)))
    | v2_struct_0(sK0)
    | m1_pre_topc(sK2(sK0,sK3(sK0,u1_struct_0(sK1))),sK0)
    | ~ spl4_17 ),
    inference(resolution,[],[f177,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1)
      | v2_struct_0(X0)
      | m1_pre_topc(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f233,plain,
    ( ~ spl4_22
    | spl4_3
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_17 ),
    inference(avatar_split_clause,[],[f221,f176,f147,f73,f65,f61,f231])).

fof(f221,plain,
    ( ~ v2_struct_0(sK2(sK0,sK3(sK0,u1_struct_0(sK1))))
    | spl4_3
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_17 ),
    inference(subsumption_resolution,[],[f195,f217])).

fof(f195,plain,
    ( v1_xboole_0(sK3(sK0,u1_struct_0(sK1)))
    | ~ v2_struct_0(sK2(sK0,sK3(sK0,u1_struct_0(sK1))))
    | spl4_3
    | ~ spl4_6
    | ~ spl4_17 ),
    inference(subsumption_resolution,[],[f194,f62])).

fof(f194,plain,
    ( v1_xboole_0(sK3(sK0,u1_struct_0(sK1)))
    | v2_struct_0(sK0)
    | ~ v2_struct_0(sK2(sK0,sK3(sK0,u1_struct_0(sK1))))
    | ~ spl4_6
    | ~ spl4_17 ),
    inference(subsumption_resolution,[],[f186,f74])).

fof(f186,plain,
    ( ~ l1_pre_topc(sK0)
    | v1_xboole_0(sK3(sK0,u1_struct_0(sK1)))
    | v2_struct_0(sK0)
    | ~ v2_struct_0(sK2(sK0,sK3(sK0,u1_struct_0(sK1))))
    | ~ spl4_17 ),
    inference(resolution,[],[f177,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1)
      | v2_struct_0(X0)
      | ~ v2_struct_0(sK2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f229,plain,
    ( spl4_21
    | spl4_3
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_17 ),
    inference(avatar_split_clause,[],[f220,f176,f147,f73,f65,f61,f227])).

fof(f220,plain,
    ( v1_pre_topc(sK2(sK0,sK3(sK0,u1_struct_0(sK1))))
    | spl4_3
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_17 ),
    inference(subsumption_resolution,[],[f197,f217])).

fof(f197,plain,
    ( v1_xboole_0(sK3(sK0,u1_struct_0(sK1)))
    | v1_pre_topc(sK2(sK0,sK3(sK0,u1_struct_0(sK1))))
    | spl4_3
    | ~ spl4_6
    | ~ spl4_17 ),
    inference(subsumption_resolution,[],[f196,f62])).

fof(f196,plain,
    ( v1_xboole_0(sK3(sK0,u1_struct_0(sK1)))
    | v2_struct_0(sK0)
    | v1_pre_topc(sK2(sK0,sK3(sK0,u1_struct_0(sK1))))
    | ~ spl4_6
    | ~ spl4_17 ),
    inference(subsumption_resolution,[],[f187,f74])).

fof(f187,plain,
    ( ~ l1_pre_topc(sK0)
    | v1_xboole_0(sK3(sK0,u1_struct_0(sK1)))
    | v2_struct_0(sK0)
    | v1_pre_topc(sK2(sK0,sK3(sK0,u1_struct_0(sK1))))
    | ~ spl4_17 ),
    inference(resolution,[],[f177,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1)
      | v2_struct_0(X0)
      | v1_pre_topc(sK2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f178,plain,
    ( spl4_17
    | spl4_1
    | ~ spl4_2
    | spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f127,f89,f77,f73,f69,f65,f61,f57,f53,f176])).

fof(f53,plain,
    ( spl4_1
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f57,plain,
    ( spl4_2
  <=> v1_tdlat_3(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f69,plain,
    ( spl4_5
  <=> v3_tdlat_3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f89,plain,
    ( spl4_8
  <=> m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f127,plain,
    ( m1_subset_1(sK3(sK0,u1_struct_0(sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_1
    | ~ spl4_2
    | spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f126,f108])).

fof(f108,plain,
    ( v2_tex_2(u1_struct_0(sK1),sK0)
    | spl4_1
    | ~ spl4_2
    | spl4_3
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f107,f58])).

fof(f58,plain,
    ( v1_tdlat_3(sK1)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f57])).

fof(f107,plain,
    ( ~ v1_tdlat_3(sK1)
    | v2_tex_2(u1_struct_0(sK1),sK0)
    | spl4_1
    | spl4_3
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f106,f62])).

fof(f106,plain,
    ( v2_struct_0(sK0)
    | ~ v1_tdlat_3(sK1)
    | v2_tex_2(u1_struct_0(sK1),sK0)
    | spl4_1
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f105,f78])).

fof(f105,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0)
    | ~ v1_tdlat_3(sK1)
    | v2_tex_2(u1_struct_0(sK1),sK0)
    | spl4_1
    | ~ spl4_6
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f104,f54])).

fof(f54,plain,
    ( ~ v2_struct_0(sK1)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f53])).

fof(f104,plain,
    ( v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0)
    | ~ v1_tdlat_3(sK1)
    | v2_tex_2(u1_struct_0(sK1),sK0)
    | ~ spl4_6
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f92,f74])).

fof(f92,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0)
    | ~ v1_tdlat_3(sK1)
    | v2_tex_2(u1_struct_0(sK1),sK0)
    | ~ spl4_8 ),
    inference(resolution,[],[f90,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X0)
      | ~ v1_tdlat_3(X1)
      | v2_tex_2(u1_struct_0(X1),X0) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X1) != X2
      | ~ v1_tdlat_3(X1)
      | v2_tex_2(X2,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v2_tex_2(X2,X0)
              <=> v1_tdlat_3(X1) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v2_tex_2(X2,X0)
              <=> v1_tdlat_3(X1) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( v2_tex_2(X2,X0)
                <=> v1_tdlat_3(X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_tex_2)).

fof(f90,plain,
    ( m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f89])).

fof(f126,plain,
    ( ~ v2_tex_2(u1_struct_0(sK1),sK0)
    | m1_subset_1(sK3(sK0,u1_struct_0(sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f125,f62])).

fof(f125,plain,
    ( v2_struct_0(sK0)
    | ~ v2_tex_2(u1_struct_0(sK1),sK0)
    | m1_subset_1(sK3(sK0,u1_struct_0(sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f124,f74])).

fof(f124,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ v2_tex_2(u1_struct_0(sK1),sK0)
    | m1_subset_1(sK3(sK0,u1_struct_0(sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f123,f70])).

fof(f70,plain,
    ( v3_tdlat_3(sK0)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f69])).

fof(f123,plain,
    ( ~ v3_tdlat_3(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ v2_tex_2(u1_struct_0(sK1),sK0)
    | m1_subset_1(sK3(sK0,u1_struct_0(sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_4
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f100,f66])).

fof(f100,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ v3_tdlat_3(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ v2_tex_2(u1_struct_0(sK1),sK0)
    | m1_subset_1(sK3(sK0,u1_struct_0(sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_8 ),
    inference(resolution,[],[f90,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ v2_tex_2(X1,X0)
      | m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( v3_tex_2(X2,X0)
              & r1_tarski(X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( v3_tex_2(X2,X0)
              & r1_tarski(X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ~ ( ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ~ ( v3_tex_2(X2,X0)
                      & r1_tarski(X1,X2) ) )
              & v2_tex_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tex_2)).

fof(f163,plain,
    ( spl4_13
    | spl4_1
    | ~ spl4_2
    | spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f132,f89,f77,f73,f69,f65,f61,f57,f53,f161])).

fof(f132,plain,
    ( r1_tarski(u1_struct_0(sK1),sK3(sK0,u1_struct_0(sK1)))
    | spl4_1
    | ~ spl4_2
    | spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f131,f108])).

fof(f131,plain,
    ( ~ v2_tex_2(u1_struct_0(sK1),sK0)
    | r1_tarski(u1_struct_0(sK1),sK3(sK0,u1_struct_0(sK1)))
    | spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f130,f62])).

fof(f130,plain,
    ( v2_struct_0(sK0)
    | ~ v2_tex_2(u1_struct_0(sK1),sK0)
    | r1_tarski(u1_struct_0(sK1),sK3(sK0,u1_struct_0(sK1)))
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f129,f74])).

fof(f129,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ v2_tex_2(u1_struct_0(sK1),sK0)
    | r1_tarski(u1_struct_0(sK1),sK3(sK0,u1_struct_0(sK1)))
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f128,f70])).

fof(f128,plain,
    ( ~ v3_tdlat_3(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ v2_tex_2(u1_struct_0(sK1),sK0)
    | r1_tarski(u1_struct_0(sK1),sK3(sK0,u1_struct_0(sK1)))
    | ~ spl4_4
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f101,f66])).

fof(f101,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ v3_tdlat_3(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ v2_tex_2(u1_struct_0(sK1),sK0)
    | r1_tarski(u1_struct_0(sK1),sK3(sK0,u1_struct_0(sK1)))
    | ~ spl4_8 ),
    inference(resolution,[],[f90,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ v2_tex_2(X1,X0)
      | r1_tarski(X1,sK3(X0,X1)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f149,plain,
    ( spl4_10
    | spl4_1
    | ~ spl4_2
    | spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f137,f89,f77,f73,f69,f65,f61,f57,f53,f147])).

fof(f137,plain,
    ( v3_tex_2(sK3(sK0,u1_struct_0(sK1)),sK0)
    | spl4_1
    | ~ spl4_2
    | spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f136,f108])).

fof(f136,plain,
    ( ~ v2_tex_2(u1_struct_0(sK1),sK0)
    | v3_tex_2(sK3(sK0,u1_struct_0(sK1)),sK0)
    | spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f135,f62])).

fof(f135,plain,
    ( v2_struct_0(sK0)
    | ~ v2_tex_2(u1_struct_0(sK1),sK0)
    | v3_tex_2(sK3(sK0,u1_struct_0(sK1)),sK0)
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f134,f74])).

fof(f134,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ v2_tex_2(u1_struct_0(sK1),sK0)
    | v3_tex_2(sK3(sK0,u1_struct_0(sK1)),sK0)
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f133,f70])).

fof(f133,plain,
    ( ~ v3_tdlat_3(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ v2_tex_2(u1_struct_0(sK1),sK0)
    | v3_tex_2(sK3(sK0,u1_struct_0(sK1)),sK0)
    | ~ spl4_4
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f102,f66])).

fof(f102,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ v3_tdlat_3(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ v2_tex_2(u1_struct_0(sK1),sK0)
    | v3_tex_2(sK3(sK0,u1_struct_0(sK1)),sK0)
    | ~ spl4_8 ),
    inference(resolution,[],[f90,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ v2_tex_2(X1,X0)
      | v3_tex_2(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f91,plain,
    ( spl4_8
    | ~ spl4_6
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f87,f77,f73,f89])).

fof(f87,plain,
    ( m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_6
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f82,f74])).

fof(f82,plain,
    ( ~ l1_pre_topc(sK0)
    | m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_7 ),
    inference(resolution,[],[f78,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f79,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f28,f77])).

fof(f28,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f75,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f32,f73])).

fof(f32,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f71,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f31,f69])).

fof(f31,plain,(
    v3_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f67,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f30,f65])).

fof(f30,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f63,plain,(
    ~ spl4_3 ),
    inference(avatar_split_clause,[],[f29,f61])).

fof(f29,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f59,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f27,f57])).

fof(f27,plain,(
    v1_tdlat_3(sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f55,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f26,f53])).

fof(f26,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:45:19 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.48  % (24210)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.48  % (24205)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.48  % (24219)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.49  % (24205)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f377,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(avatar_sat_refutation,[],[f55,f59,f63,f67,f71,f75,f79,f91,f149,f163,f178,f229,f233,f237,f254,f298,f369,f376])).
% 0.22/0.49  fof(f376,plain,(
% 0.22/0.49    ~spl4_21 | spl4_22 | ~spl4_23 | ~spl4_27 | ~spl4_38),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f375])).
% 0.22/0.49  fof(f375,plain,(
% 0.22/0.49    $false | (~spl4_21 | spl4_22 | ~spl4_23 | ~spl4_27 | ~spl4_38)),
% 0.22/0.49    inference(subsumption_resolution,[],[f374,f232])).
% 0.22/0.49  fof(f232,plain,(
% 0.22/0.49    ~v2_struct_0(sK2(sK0,sK3(sK0,u1_struct_0(sK1)))) | spl4_22),
% 0.22/0.49    inference(avatar_component_clause,[],[f231])).
% 0.22/0.49  fof(f231,plain,(
% 0.22/0.49    spl4_22 <=> v2_struct_0(sK2(sK0,sK3(sK0,u1_struct_0(sK1))))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 0.22/0.49  fof(f374,plain,(
% 0.22/0.49    v2_struct_0(sK2(sK0,sK3(sK0,u1_struct_0(sK1)))) | (~spl4_21 | ~spl4_23 | ~spl4_27 | ~spl4_38)),
% 0.22/0.49    inference(subsumption_resolution,[],[f373,f297])).
% 0.22/0.49  fof(f297,plain,(
% 0.22/0.49    m1_pre_topc(sK1,sK2(sK0,sK3(sK0,u1_struct_0(sK1)))) | ~spl4_27),
% 0.22/0.49    inference(avatar_component_clause,[],[f296])).
% 0.22/0.49  fof(f296,plain,(
% 0.22/0.49    spl4_27 <=> m1_pre_topc(sK1,sK2(sK0,sK3(sK0,u1_struct_0(sK1))))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).
% 0.22/0.49  fof(f373,plain,(
% 0.22/0.49    ~m1_pre_topc(sK1,sK2(sK0,sK3(sK0,u1_struct_0(sK1)))) | v2_struct_0(sK2(sK0,sK3(sK0,u1_struct_0(sK1)))) | (~spl4_21 | ~spl4_23 | ~spl4_38)),
% 0.22/0.49    inference(subsumption_resolution,[],[f372,f236])).
% 0.22/0.49  fof(f236,plain,(
% 0.22/0.49    m1_pre_topc(sK2(sK0,sK3(sK0,u1_struct_0(sK1))),sK0) | ~spl4_23),
% 0.22/0.49    inference(avatar_component_clause,[],[f235])).
% 0.22/0.49  fof(f235,plain,(
% 0.22/0.49    spl4_23 <=> m1_pre_topc(sK2(sK0,sK3(sK0,u1_struct_0(sK1))),sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 0.22/0.49  fof(f372,plain,(
% 0.22/0.49    ~m1_pre_topc(sK2(sK0,sK3(sK0,u1_struct_0(sK1))),sK0) | ~m1_pre_topc(sK1,sK2(sK0,sK3(sK0,u1_struct_0(sK1)))) | v2_struct_0(sK2(sK0,sK3(sK0,u1_struct_0(sK1)))) | (~spl4_21 | ~spl4_38)),
% 0.22/0.49    inference(subsumption_resolution,[],[f370,f228])).
% 0.22/0.49  fof(f228,plain,(
% 0.22/0.49    v1_pre_topc(sK2(sK0,sK3(sK0,u1_struct_0(sK1)))) | ~spl4_21),
% 0.22/0.49    inference(avatar_component_clause,[],[f227])).
% 0.22/0.49  fof(f227,plain,(
% 0.22/0.49    spl4_21 <=> v1_pre_topc(sK2(sK0,sK3(sK0,u1_struct_0(sK1))))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 0.22/0.49  fof(f370,plain,(
% 0.22/0.49    ~v1_pre_topc(sK2(sK0,sK3(sK0,u1_struct_0(sK1)))) | ~m1_pre_topc(sK2(sK0,sK3(sK0,u1_struct_0(sK1))),sK0) | ~m1_pre_topc(sK1,sK2(sK0,sK3(sK0,u1_struct_0(sK1)))) | v2_struct_0(sK2(sK0,sK3(sK0,u1_struct_0(sK1)))) | ~spl4_38),
% 0.22/0.49    inference(resolution,[],[f368,f25])).
% 0.22/0.49  fof(f25,plain,(
% 0.22/0.49    ( ! [X2] : (~v4_tex_2(X2,sK0) | ~v1_pre_topc(X2) | ~m1_pre_topc(X2,sK0) | ~m1_pre_topc(sK1,X2) | v2_struct_0(X2)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f11])).
% 0.22/0.49  fof(f11,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : (! [X2] : (~v4_tex_2(X2,X0) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2)) & m1_pre_topc(X1,X0) & v1_tdlat_3(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f10])).
% 0.22/0.49  fof(f10,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : (! [X2] : (~v4_tex_2(X2,X0) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2)) & (m1_pre_topc(X1,X0) & v1_tdlat_3(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f9])).
% 0.22/0.49  fof(f9,negated_conjecture,(
% 0.22/0.49    ~! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v1_tdlat_3(X1) & ~v2_struct_0(X1)) => ? [X2] : (v4_tex_2(X2,X0) & m1_pre_topc(X1,X2) & m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2))))),
% 0.22/0.49    inference(negated_conjecture,[],[f8])).
% 0.22/0.49  fof(f8,conjecture,(
% 0.22/0.49    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v1_tdlat_3(X1) & ~v2_struct_0(X1)) => ? [X2] : (v4_tex_2(X2,X0) & m1_pre_topc(X1,X2) & m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_tex_2)).
% 0.22/0.49  fof(f368,plain,(
% 0.22/0.49    v4_tex_2(sK2(sK0,sK3(sK0,u1_struct_0(sK1))),sK0) | ~spl4_38),
% 0.22/0.49    inference(avatar_component_clause,[],[f367])).
% 0.22/0.49  fof(f367,plain,(
% 0.22/0.49    spl4_38 <=> v4_tex_2(sK2(sK0,sK3(sK0,u1_struct_0(sK1))),sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).
% 0.22/0.49  fof(f369,plain,(
% 0.22/0.49    spl4_38 | spl4_3 | ~spl4_6 | ~spl4_10 | ~spl4_17 | ~spl4_23 | ~spl4_24),
% 0.22/0.49    inference(avatar_split_clause,[],[f365,f252,f235,f176,f147,f73,f61,f367])).
% 0.22/0.49  fof(f61,plain,(
% 0.22/0.49    spl4_3 <=> v2_struct_0(sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.22/0.49  fof(f73,plain,(
% 0.22/0.49    spl4_6 <=> l1_pre_topc(sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.22/0.49  fof(f147,plain,(
% 0.22/0.49    spl4_10 <=> v3_tex_2(sK3(sK0,u1_struct_0(sK1)),sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.22/0.49  fof(f176,plain,(
% 0.22/0.49    spl4_17 <=> m1_subset_1(sK3(sK0,u1_struct_0(sK1)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 0.22/0.49  fof(f252,plain,(
% 0.22/0.49    spl4_24 <=> sK3(sK0,u1_struct_0(sK1)) = u1_struct_0(sK2(sK0,sK3(sK0,u1_struct_0(sK1))))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 0.22/0.49  fof(f365,plain,(
% 0.22/0.49    v4_tex_2(sK2(sK0,sK3(sK0,u1_struct_0(sK1))),sK0) | (spl4_3 | ~spl4_6 | ~spl4_10 | ~spl4_17 | ~spl4_23 | ~spl4_24)),
% 0.22/0.49    inference(subsumption_resolution,[],[f364,f148])).
% 0.22/0.49  fof(f148,plain,(
% 0.22/0.49    v3_tex_2(sK3(sK0,u1_struct_0(sK1)),sK0) | ~spl4_10),
% 0.22/0.49    inference(avatar_component_clause,[],[f147])).
% 0.22/0.49  % (24214)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.49  fof(f364,plain,(
% 0.22/0.49    v4_tex_2(sK2(sK0,sK3(sK0,u1_struct_0(sK1))),sK0) | ~v3_tex_2(sK3(sK0,u1_struct_0(sK1)),sK0) | (spl4_3 | ~spl4_6 | ~spl4_17 | ~spl4_23 | ~spl4_24)),
% 0.22/0.49    inference(subsumption_resolution,[],[f363,f62])).
% 0.22/0.49  fof(f62,plain,(
% 0.22/0.49    ~v2_struct_0(sK0) | spl4_3),
% 0.22/0.49    inference(avatar_component_clause,[],[f61])).
% 0.22/0.49  fof(f363,plain,(
% 0.22/0.49    v2_struct_0(sK0) | v4_tex_2(sK2(sK0,sK3(sK0,u1_struct_0(sK1))),sK0) | ~v3_tex_2(sK3(sK0,u1_struct_0(sK1)),sK0) | (~spl4_6 | ~spl4_17 | ~spl4_23 | ~spl4_24)),
% 0.22/0.49    inference(subsumption_resolution,[],[f362,f236])).
% 0.22/0.49  fof(f362,plain,(
% 0.22/0.49    ~m1_pre_topc(sK2(sK0,sK3(sK0,u1_struct_0(sK1))),sK0) | v2_struct_0(sK0) | v4_tex_2(sK2(sK0,sK3(sK0,u1_struct_0(sK1))),sK0) | ~v3_tex_2(sK3(sK0,u1_struct_0(sK1)),sK0) | (~spl4_6 | ~spl4_17 | ~spl4_24)),
% 0.22/0.49    inference(subsumption_resolution,[],[f360,f74])).
% 0.22/0.49  fof(f74,plain,(
% 0.22/0.49    l1_pre_topc(sK0) | ~spl4_6),
% 0.22/0.49    inference(avatar_component_clause,[],[f73])).
% 0.22/0.49  fof(f360,plain,(
% 0.22/0.49    ~l1_pre_topc(sK0) | ~m1_pre_topc(sK2(sK0,sK3(sK0,u1_struct_0(sK1))),sK0) | v2_struct_0(sK0) | v4_tex_2(sK2(sK0,sK3(sK0,u1_struct_0(sK1))),sK0) | ~v3_tex_2(sK3(sK0,u1_struct_0(sK1)),sK0) | (~spl4_17 | ~spl4_24)),
% 0.22/0.49    inference(resolution,[],[f263,f177])).
% 0.22/0.49  fof(f177,plain,(
% 0.22/0.49    m1_subset_1(sK3(sK0,u1_struct_0(sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_17),
% 0.22/0.49    inference(avatar_component_clause,[],[f176])).
% 0.22/0.49  fof(f263,plain,(
% 0.22/0.49    ( ! [X8] : (~m1_subset_1(sK3(sK0,u1_struct_0(sK1)),k1_zfmisc_1(u1_struct_0(X8))) | ~l1_pre_topc(X8) | ~m1_pre_topc(sK2(sK0,sK3(sK0,u1_struct_0(sK1))),X8) | v2_struct_0(X8) | v4_tex_2(sK2(sK0,sK3(sK0,u1_struct_0(sK1))),X8) | ~v3_tex_2(sK3(sK0,u1_struct_0(sK1)),X8)) ) | ~spl4_24),
% 0.22/0.49    inference(superposition,[],[f48,f253])).
% 0.22/0.49  fof(f253,plain,(
% 0.22/0.49    sK3(sK0,u1_struct_0(sK1)) = u1_struct_0(sK2(sK0,sK3(sK0,u1_struct_0(sK1)))) | ~spl4_24),
% 0.22/0.49    inference(avatar_component_clause,[],[f252])).
% 0.22/0.49  fof(f48,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | v2_struct_0(X0) | v4_tex_2(X1,X0) | ~v3_tex_2(u1_struct_0(X1),X0)) )),
% 0.22/0.49    inference(equality_resolution,[],[f34])).
% 0.22/0.49  fof(f34,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(X1) != X2 | v4_tex_2(X1,X0) | ~v3_tex_2(X2,X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f13])).
% 0.22/0.49  fof(f13,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : ((v3_tex_2(X2,X0) <=> v4_tex_2(X1,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f12])).
% 0.22/0.49  fof(f12,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : (((v3_tex_2(X2,X0) <=> v4_tex_2(X1,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f6])).
% 0.22/0.49  fof(f6,axiom,(
% 0.22/0.49    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => (v3_tex_2(X2,X0) <=> v4_tex_2(X1,X0))))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_tex_2)).
% 0.22/0.49  fof(f298,plain,(
% 0.22/0.49    spl4_27 | ~spl4_4 | ~spl4_6 | ~spl4_7 | ~spl4_13 | ~spl4_23 | ~spl4_24),
% 0.22/0.49    inference(avatar_split_clause,[],[f287,f252,f235,f161,f77,f73,f65,f296])).
% 0.22/0.49  fof(f65,plain,(
% 0.22/0.49    spl4_4 <=> v2_pre_topc(sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.22/0.49  fof(f77,plain,(
% 0.22/0.49    spl4_7 <=> m1_pre_topc(sK1,sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.22/0.49  fof(f161,plain,(
% 0.22/0.49    spl4_13 <=> r1_tarski(u1_struct_0(sK1),sK3(sK0,u1_struct_0(sK1)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.22/0.49  fof(f287,plain,(
% 0.22/0.49    m1_pre_topc(sK1,sK2(sK0,sK3(sK0,u1_struct_0(sK1)))) | (~spl4_4 | ~spl4_6 | ~spl4_7 | ~spl4_13 | ~spl4_23 | ~spl4_24)),
% 0.22/0.49    inference(subsumption_resolution,[],[f286,f236])).
% 0.22/0.49  fof(f286,plain,(
% 0.22/0.49    m1_pre_topc(sK1,sK2(sK0,sK3(sK0,u1_struct_0(sK1)))) | ~m1_pre_topc(sK2(sK0,sK3(sK0,u1_struct_0(sK1))),sK0) | (~spl4_4 | ~spl4_6 | ~spl4_7 | ~spl4_13 | ~spl4_24)),
% 0.22/0.49    inference(subsumption_resolution,[],[f271,f162])).
% 0.22/0.49  fof(f162,plain,(
% 0.22/0.49    r1_tarski(u1_struct_0(sK1),sK3(sK0,u1_struct_0(sK1))) | ~spl4_13),
% 0.22/0.49    inference(avatar_component_clause,[],[f161])).
% 0.22/0.49  fof(f271,plain,(
% 0.22/0.49    ~r1_tarski(u1_struct_0(sK1),sK3(sK0,u1_struct_0(sK1))) | m1_pre_topc(sK1,sK2(sK0,sK3(sK0,u1_struct_0(sK1)))) | ~m1_pre_topc(sK2(sK0,sK3(sK0,u1_struct_0(sK1))),sK0) | (~spl4_4 | ~spl4_6 | ~spl4_7 | ~spl4_24)),
% 0.22/0.49    inference(superposition,[],[f86,f253])).
% 0.22/0.49  fof(f86,plain,(
% 0.22/0.49    ( ! [X1] : (~r1_tarski(u1_struct_0(sK1),u1_struct_0(X1)) | m1_pre_topc(sK1,X1) | ~m1_pre_topc(X1,sK0)) ) | (~spl4_4 | ~spl4_6 | ~spl4_7)),
% 0.22/0.49    inference(subsumption_resolution,[],[f85,f66])).
% 0.22/0.49  fof(f66,plain,(
% 0.22/0.49    v2_pre_topc(sK0) | ~spl4_4),
% 0.22/0.49    inference(avatar_component_clause,[],[f65])).
% 0.22/0.49  fof(f85,plain,(
% 0.22/0.49    ( ! [X1] : (~v2_pre_topc(sK0) | ~m1_pre_topc(X1,sK0) | m1_pre_topc(sK1,X1) | ~r1_tarski(u1_struct_0(sK1),u1_struct_0(X1))) ) | (~spl4_6 | ~spl4_7)),
% 0.22/0.49    inference(subsumption_resolution,[],[f81,f74])).
% 0.22/0.49  fof(f81,plain,(
% 0.22/0.49    ( ! [X1] : (~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~m1_pre_topc(X1,sK0) | m1_pre_topc(sK1,X1) | ~r1_tarski(u1_struct_0(sK1),u1_struct_0(X1))) ) | ~spl4_7),
% 0.22/0.49    inference(resolution,[],[f78,f46])).
% 0.22/0.49  fof(f46,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~m1_pre_topc(X2,X0) | m1_pre_topc(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f22])).
% 0.22/0.49  fof(f22,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.49    inference(flattening,[],[f21])).
% 0.22/0.49  fof(f21,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f2])).
% 0.22/0.49  fof(f2,axiom,(
% 0.22/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_tsep_1)).
% 0.22/0.49  fof(f78,plain,(
% 0.22/0.49    m1_pre_topc(sK1,sK0) | ~spl4_7),
% 0.22/0.49    inference(avatar_component_clause,[],[f77])).
% 0.22/0.49  fof(f254,plain,(
% 0.22/0.49    spl4_24 | spl4_3 | ~spl4_4 | ~spl4_6 | ~spl4_10 | ~spl4_17),
% 0.22/0.49    inference(avatar_split_clause,[],[f218,f176,f147,f73,f65,f61,f252])).
% 0.22/0.49  fof(f218,plain,(
% 0.22/0.49    sK3(sK0,u1_struct_0(sK1)) = u1_struct_0(sK2(sK0,sK3(sK0,u1_struct_0(sK1)))) | (spl4_3 | ~spl4_4 | ~spl4_6 | ~spl4_10 | ~spl4_17)),
% 0.22/0.49    inference(subsumption_resolution,[],[f201,f217])).
% 0.22/0.49  fof(f217,plain,(
% 0.22/0.49    ~v1_xboole_0(sK3(sK0,u1_struct_0(sK1))) | (spl4_3 | ~spl4_4 | ~spl4_6 | ~spl4_10 | ~spl4_17)),
% 0.22/0.49    inference(subsumption_resolution,[],[f216,f148])).
% 0.22/0.49  fof(f216,plain,(
% 0.22/0.49    ~v1_xboole_0(sK3(sK0,u1_struct_0(sK1))) | ~v3_tex_2(sK3(sK0,u1_struct_0(sK1)),sK0) | (spl4_3 | ~spl4_4 | ~spl4_6 | ~spl4_17)),
% 0.22/0.49    inference(subsumption_resolution,[],[f215,f62])).
% 0.22/0.49  fof(f215,plain,(
% 0.22/0.49    ~v1_xboole_0(sK3(sK0,u1_struct_0(sK1))) | v2_struct_0(sK0) | ~v3_tex_2(sK3(sK0,u1_struct_0(sK1)),sK0) | (~spl4_4 | ~spl4_6 | ~spl4_17)),
% 0.22/0.49    inference(subsumption_resolution,[],[f214,f74])).
% 0.22/0.49  fof(f214,plain,(
% 0.22/0.49    ~l1_pre_topc(sK0) | ~v1_xboole_0(sK3(sK0,u1_struct_0(sK1))) | v2_struct_0(sK0) | ~v3_tex_2(sK3(sK0,u1_struct_0(sK1)),sK0) | (~spl4_4 | ~spl4_17)),
% 0.22/0.49    inference(subsumption_resolution,[],[f193,f66])).
% 0.22/0.49  fof(f193,plain,(
% 0.22/0.49    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_xboole_0(sK3(sK0,u1_struct_0(sK1))) | v2_struct_0(sK0) | ~v3_tex_2(sK3(sK0,u1_struct_0(sK1)),sK0) | ~spl4_17),
% 0.22/0.49    inference(resolution,[],[f177,f47])).
% 0.22/0.49  fof(f47,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_xboole_0(X1) | v2_struct_0(X0) | ~v3_tex_2(X1,X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f24])).
% 0.22/0.49  fof(f24,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f23])).
% 0.22/0.49  fof(f23,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (~v3_tex_2(X1,X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f5])).
% 0.22/0.49  fof(f5,axiom,(
% 0.22/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => ~v3_tex_2(X1,X0)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_tex_2)).
% 0.22/0.49  fof(f201,plain,(
% 0.22/0.49    v1_xboole_0(sK3(sK0,u1_struct_0(sK1))) | sK3(sK0,u1_struct_0(sK1)) = u1_struct_0(sK2(sK0,sK3(sK0,u1_struct_0(sK1)))) | (spl4_3 | ~spl4_6 | ~spl4_17)),
% 0.22/0.49    inference(subsumption_resolution,[],[f200,f62])).
% 0.22/0.49  fof(f200,plain,(
% 0.22/0.49    v1_xboole_0(sK3(sK0,u1_struct_0(sK1))) | v2_struct_0(sK0) | sK3(sK0,u1_struct_0(sK1)) = u1_struct_0(sK2(sK0,sK3(sK0,u1_struct_0(sK1)))) | (~spl4_6 | ~spl4_17)),
% 0.22/0.49    inference(subsumption_resolution,[],[f189,f74])).
% 0.22/0.49  fof(f189,plain,(
% 0.22/0.49    ~l1_pre_topc(sK0) | v1_xboole_0(sK3(sK0,u1_struct_0(sK1))) | v2_struct_0(sK0) | sK3(sK0,u1_struct_0(sK1)) = u1_struct_0(sK2(sK0,sK3(sK0,u1_struct_0(sK1)))) | ~spl4_17),
% 0.22/0.49    inference(resolution,[],[f177,f38])).
% 0.22/0.49  fof(f38,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v1_xboole_0(X1) | v2_struct_0(X0) | u1_struct_0(sK2(X0,X1)) = X1) )),
% 0.22/0.49    inference(cnf_transformation,[],[f15])).
% 0.22/0.49  fof(f15,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f14])).
% 0.22/0.49  fof(f14,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f3])).
% 0.22/0.49  fof(f3,axiom,(
% 0.22/0.49    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_tsep_1)).
% 0.22/0.49  fof(f237,plain,(
% 0.22/0.49    spl4_23 | spl4_3 | ~spl4_4 | ~spl4_6 | ~spl4_10 | ~spl4_17),
% 0.22/0.49    inference(avatar_split_clause,[],[f219,f176,f147,f73,f65,f61,f235])).
% 0.22/0.49  fof(f219,plain,(
% 0.22/0.49    m1_pre_topc(sK2(sK0,sK3(sK0,u1_struct_0(sK1))),sK0) | (spl4_3 | ~spl4_4 | ~spl4_6 | ~spl4_10 | ~spl4_17)),
% 0.22/0.49    inference(subsumption_resolution,[],[f199,f217])).
% 0.22/0.49  fof(f199,plain,(
% 0.22/0.49    v1_xboole_0(sK3(sK0,u1_struct_0(sK1))) | m1_pre_topc(sK2(sK0,sK3(sK0,u1_struct_0(sK1))),sK0) | (spl4_3 | ~spl4_6 | ~spl4_17)),
% 0.22/0.49    inference(subsumption_resolution,[],[f198,f62])).
% 0.22/0.49  fof(f198,plain,(
% 0.22/0.49    v1_xboole_0(sK3(sK0,u1_struct_0(sK1))) | v2_struct_0(sK0) | m1_pre_topc(sK2(sK0,sK3(sK0,u1_struct_0(sK1))),sK0) | (~spl4_6 | ~spl4_17)),
% 0.22/0.49    inference(subsumption_resolution,[],[f188,f74])).
% 0.22/0.49  fof(f188,plain,(
% 0.22/0.49    ~l1_pre_topc(sK0) | v1_xboole_0(sK3(sK0,u1_struct_0(sK1))) | v2_struct_0(sK0) | m1_pre_topc(sK2(sK0,sK3(sK0,u1_struct_0(sK1))),sK0) | ~spl4_17),
% 0.22/0.49    inference(resolution,[],[f177,f37])).
% 0.22/0.49  fof(f37,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v1_xboole_0(X1) | v2_struct_0(X0) | m1_pre_topc(sK2(X0,X1),X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f15])).
% 0.22/0.49  fof(f233,plain,(
% 0.22/0.49    ~spl4_22 | spl4_3 | ~spl4_4 | ~spl4_6 | ~spl4_10 | ~spl4_17),
% 0.22/0.49    inference(avatar_split_clause,[],[f221,f176,f147,f73,f65,f61,f231])).
% 0.22/0.49  fof(f221,plain,(
% 0.22/0.49    ~v2_struct_0(sK2(sK0,sK3(sK0,u1_struct_0(sK1)))) | (spl4_3 | ~spl4_4 | ~spl4_6 | ~spl4_10 | ~spl4_17)),
% 0.22/0.49    inference(subsumption_resolution,[],[f195,f217])).
% 0.22/0.49  fof(f195,plain,(
% 0.22/0.49    v1_xboole_0(sK3(sK0,u1_struct_0(sK1))) | ~v2_struct_0(sK2(sK0,sK3(sK0,u1_struct_0(sK1)))) | (spl4_3 | ~spl4_6 | ~spl4_17)),
% 0.22/0.49    inference(subsumption_resolution,[],[f194,f62])).
% 0.22/0.49  fof(f194,plain,(
% 0.22/0.49    v1_xboole_0(sK3(sK0,u1_struct_0(sK1))) | v2_struct_0(sK0) | ~v2_struct_0(sK2(sK0,sK3(sK0,u1_struct_0(sK1)))) | (~spl4_6 | ~spl4_17)),
% 0.22/0.49    inference(subsumption_resolution,[],[f186,f74])).
% 0.22/0.49  fof(f186,plain,(
% 0.22/0.49    ~l1_pre_topc(sK0) | v1_xboole_0(sK3(sK0,u1_struct_0(sK1))) | v2_struct_0(sK0) | ~v2_struct_0(sK2(sK0,sK3(sK0,u1_struct_0(sK1)))) | ~spl4_17),
% 0.22/0.49    inference(resolution,[],[f177,f35])).
% 0.22/0.49  fof(f35,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v1_xboole_0(X1) | v2_struct_0(X0) | ~v2_struct_0(sK2(X0,X1))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f15])).
% 0.22/0.49  fof(f229,plain,(
% 0.22/0.49    spl4_21 | spl4_3 | ~spl4_4 | ~spl4_6 | ~spl4_10 | ~spl4_17),
% 0.22/0.49    inference(avatar_split_clause,[],[f220,f176,f147,f73,f65,f61,f227])).
% 0.22/0.49  fof(f220,plain,(
% 0.22/0.49    v1_pre_topc(sK2(sK0,sK3(sK0,u1_struct_0(sK1)))) | (spl4_3 | ~spl4_4 | ~spl4_6 | ~spl4_10 | ~spl4_17)),
% 0.22/0.49    inference(subsumption_resolution,[],[f197,f217])).
% 0.22/0.49  fof(f197,plain,(
% 0.22/0.49    v1_xboole_0(sK3(sK0,u1_struct_0(sK1))) | v1_pre_topc(sK2(sK0,sK3(sK0,u1_struct_0(sK1)))) | (spl4_3 | ~spl4_6 | ~spl4_17)),
% 0.22/0.49    inference(subsumption_resolution,[],[f196,f62])).
% 0.22/0.49  fof(f196,plain,(
% 0.22/0.49    v1_xboole_0(sK3(sK0,u1_struct_0(sK1))) | v2_struct_0(sK0) | v1_pre_topc(sK2(sK0,sK3(sK0,u1_struct_0(sK1)))) | (~spl4_6 | ~spl4_17)),
% 0.22/0.49    inference(subsumption_resolution,[],[f187,f74])).
% 0.22/0.49  fof(f187,plain,(
% 0.22/0.49    ~l1_pre_topc(sK0) | v1_xboole_0(sK3(sK0,u1_struct_0(sK1))) | v2_struct_0(sK0) | v1_pre_topc(sK2(sK0,sK3(sK0,u1_struct_0(sK1)))) | ~spl4_17),
% 0.22/0.49    inference(resolution,[],[f177,f36])).
% 0.22/0.49  fof(f36,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v1_xboole_0(X1) | v2_struct_0(X0) | v1_pre_topc(sK2(X0,X1))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f15])).
% 0.22/0.49  fof(f178,plain,(
% 0.22/0.49    spl4_17 | spl4_1 | ~spl4_2 | spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_6 | ~spl4_7 | ~spl4_8),
% 0.22/0.49    inference(avatar_split_clause,[],[f127,f89,f77,f73,f69,f65,f61,f57,f53,f176])).
% 0.22/0.49  fof(f53,plain,(
% 0.22/0.49    spl4_1 <=> v2_struct_0(sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.22/0.49  fof(f57,plain,(
% 0.22/0.49    spl4_2 <=> v1_tdlat_3(sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.22/0.49  fof(f69,plain,(
% 0.22/0.49    spl4_5 <=> v3_tdlat_3(sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.22/0.49  fof(f89,plain,(
% 0.22/0.49    spl4_8 <=> m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.22/0.49  fof(f127,plain,(
% 0.22/0.49    m1_subset_1(sK3(sK0,u1_struct_0(sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | (spl4_1 | ~spl4_2 | spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_6 | ~spl4_7 | ~spl4_8)),
% 0.22/0.49    inference(subsumption_resolution,[],[f126,f108])).
% 0.22/0.49  fof(f108,plain,(
% 0.22/0.49    v2_tex_2(u1_struct_0(sK1),sK0) | (spl4_1 | ~spl4_2 | spl4_3 | ~spl4_6 | ~spl4_7 | ~spl4_8)),
% 0.22/0.49    inference(subsumption_resolution,[],[f107,f58])).
% 0.22/0.49  fof(f58,plain,(
% 0.22/0.49    v1_tdlat_3(sK1) | ~spl4_2),
% 0.22/0.49    inference(avatar_component_clause,[],[f57])).
% 0.22/0.49  fof(f107,plain,(
% 0.22/0.49    ~v1_tdlat_3(sK1) | v2_tex_2(u1_struct_0(sK1),sK0) | (spl4_1 | spl4_3 | ~spl4_6 | ~spl4_7 | ~spl4_8)),
% 0.22/0.49    inference(subsumption_resolution,[],[f106,f62])).
% 0.22/0.49  fof(f106,plain,(
% 0.22/0.49    v2_struct_0(sK0) | ~v1_tdlat_3(sK1) | v2_tex_2(u1_struct_0(sK1),sK0) | (spl4_1 | ~spl4_6 | ~spl4_7 | ~spl4_8)),
% 0.22/0.49    inference(subsumption_resolution,[],[f105,f78])).
% 0.22/0.49  fof(f105,plain,(
% 0.22/0.49    ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK0) | ~v1_tdlat_3(sK1) | v2_tex_2(u1_struct_0(sK1),sK0) | (spl4_1 | ~spl4_6 | ~spl4_8)),
% 0.22/0.49    inference(subsumption_resolution,[],[f104,f54])).
% 0.22/0.49  fof(f54,plain,(
% 0.22/0.49    ~v2_struct_0(sK1) | spl4_1),
% 0.22/0.49    inference(avatar_component_clause,[],[f53])).
% 0.22/0.49  fof(f104,plain,(
% 0.22/0.49    v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK0) | ~v1_tdlat_3(sK1) | v2_tex_2(u1_struct_0(sK1),sK0) | (~spl4_6 | ~spl4_8)),
% 0.22/0.49    inference(subsumption_resolution,[],[f92,f74])).
% 0.22/0.49  fof(f92,plain,(
% 0.22/0.49    ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK0) | ~v1_tdlat_3(sK1) | v2_tex_2(u1_struct_0(sK1),sK0) | ~spl4_8),
% 0.22/0.49    inference(resolution,[],[f90,f51])).
% 0.22/0.49  fof(f51,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X0) | ~v1_tdlat_3(X1) | v2_tex_2(u1_struct_0(X1),X0)) )),
% 0.22/0.49    inference(equality_resolution,[],[f40])).
% 0.22/0.49  fof(f40,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(X1) != X2 | ~v1_tdlat_3(X1) | v2_tex_2(X2,X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f18])).
% 0.22/0.49  fof(f18,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : ((v2_tex_2(X2,X0) <=> v1_tdlat_3(X1)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f17])).
% 0.22/0.49  fof(f17,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : (((v2_tex_2(X2,X0) <=> v1_tdlat_3(X1)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f4])).
% 0.22/0.49  fof(f4,axiom,(
% 0.22/0.49    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => (v2_tex_2(X2,X0) <=> v1_tdlat_3(X1))))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_tex_2)).
% 0.22/0.49  fof(f90,plain,(
% 0.22/0.49    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_8),
% 0.22/0.49    inference(avatar_component_clause,[],[f89])).
% 0.22/0.49  fof(f126,plain,(
% 0.22/0.49    ~v2_tex_2(u1_struct_0(sK1),sK0) | m1_subset_1(sK3(sK0,u1_struct_0(sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | (spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_6 | ~spl4_8)),
% 0.22/0.49    inference(subsumption_resolution,[],[f125,f62])).
% 0.22/0.49  fof(f125,plain,(
% 0.22/0.49    v2_struct_0(sK0) | ~v2_tex_2(u1_struct_0(sK1),sK0) | m1_subset_1(sK3(sK0,u1_struct_0(sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl4_4 | ~spl4_5 | ~spl4_6 | ~spl4_8)),
% 0.22/0.49    inference(subsumption_resolution,[],[f124,f74])).
% 0.22/0.49  fof(f124,plain,(
% 0.22/0.49    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~v2_tex_2(u1_struct_0(sK1),sK0) | m1_subset_1(sK3(sK0,u1_struct_0(sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl4_4 | ~spl4_5 | ~spl4_8)),
% 0.22/0.49    inference(subsumption_resolution,[],[f123,f70])).
% 0.22/0.49  fof(f70,plain,(
% 0.22/0.49    v3_tdlat_3(sK0) | ~spl4_5),
% 0.22/0.49    inference(avatar_component_clause,[],[f69])).
% 0.22/0.49  fof(f123,plain,(
% 0.22/0.49    ~v3_tdlat_3(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~v2_tex_2(u1_struct_0(sK1),sK0) | m1_subset_1(sK3(sK0,u1_struct_0(sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl4_4 | ~spl4_8)),
% 0.22/0.49    inference(subsumption_resolution,[],[f100,f66])).
% 0.22/0.49  fof(f100,plain,(
% 0.22/0.49    ~v2_pre_topc(sK0) | ~v3_tdlat_3(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~v2_tex_2(u1_struct_0(sK1),sK0) | m1_subset_1(sK3(sK0,u1_struct_0(sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_8),
% 0.22/0.49    inference(resolution,[],[f90,f42])).
% 0.22/0.49  fof(f42,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~v3_tdlat_3(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~v2_tex_2(X1,X0) | m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f20])).
% 0.22/0.49  fof(f20,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (? [X2] : (v3_tex_2(X2,X0) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f19])).
% 0.22/0.49  fof(f19,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : ((? [X2] : ((v3_tex_2(X2,X0) & r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f7])).
% 0.22/0.49  fof(f7,axiom,(
% 0.22/0.49    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(v3_tex_2(X2,X0) & r1_tarski(X1,X2))) & v2_tex_2(X1,X0))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tex_2)).
% 0.22/0.49  fof(f163,plain,(
% 0.22/0.49    spl4_13 | spl4_1 | ~spl4_2 | spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_6 | ~spl4_7 | ~spl4_8),
% 0.22/0.49    inference(avatar_split_clause,[],[f132,f89,f77,f73,f69,f65,f61,f57,f53,f161])).
% 0.22/0.49  fof(f132,plain,(
% 0.22/0.49    r1_tarski(u1_struct_0(sK1),sK3(sK0,u1_struct_0(sK1))) | (spl4_1 | ~spl4_2 | spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_6 | ~spl4_7 | ~spl4_8)),
% 0.22/0.49    inference(subsumption_resolution,[],[f131,f108])).
% 0.22/0.49  fof(f131,plain,(
% 0.22/0.49    ~v2_tex_2(u1_struct_0(sK1),sK0) | r1_tarski(u1_struct_0(sK1),sK3(sK0,u1_struct_0(sK1))) | (spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_6 | ~spl4_8)),
% 0.22/0.49    inference(subsumption_resolution,[],[f130,f62])).
% 0.22/0.49  fof(f130,plain,(
% 0.22/0.49    v2_struct_0(sK0) | ~v2_tex_2(u1_struct_0(sK1),sK0) | r1_tarski(u1_struct_0(sK1),sK3(sK0,u1_struct_0(sK1))) | (~spl4_4 | ~spl4_5 | ~spl4_6 | ~spl4_8)),
% 0.22/0.49    inference(subsumption_resolution,[],[f129,f74])).
% 0.22/0.49  fof(f129,plain,(
% 0.22/0.49    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~v2_tex_2(u1_struct_0(sK1),sK0) | r1_tarski(u1_struct_0(sK1),sK3(sK0,u1_struct_0(sK1))) | (~spl4_4 | ~spl4_5 | ~spl4_8)),
% 0.22/0.49    inference(subsumption_resolution,[],[f128,f70])).
% 0.22/0.49  fof(f128,plain,(
% 0.22/0.49    ~v3_tdlat_3(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~v2_tex_2(u1_struct_0(sK1),sK0) | r1_tarski(u1_struct_0(sK1),sK3(sK0,u1_struct_0(sK1))) | (~spl4_4 | ~spl4_8)),
% 0.22/0.49    inference(subsumption_resolution,[],[f101,f66])).
% 0.22/0.49  fof(f101,plain,(
% 0.22/0.49    ~v2_pre_topc(sK0) | ~v3_tdlat_3(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~v2_tex_2(u1_struct_0(sK1),sK0) | r1_tarski(u1_struct_0(sK1),sK3(sK0,u1_struct_0(sK1))) | ~spl4_8),
% 0.22/0.49    inference(resolution,[],[f90,f43])).
% 0.22/0.49  fof(f43,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~v3_tdlat_3(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~v2_tex_2(X1,X0) | r1_tarski(X1,sK3(X0,X1))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f20])).
% 0.22/0.49  fof(f149,plain,(
% 0.22/0.49    spl4_10 | spl4_1 | ~spl4_2 | spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_6 | ~spl4_7 | ~spl4_8),
% 0.22/0.49    inference(avatar_split_clause,[],[f137,f89,f77,f73,f69,f65,f61,f57,f53,f147])).
% 0.22/0.49  fof(f137,plain,(
% 0.22/0.49    v3_tex_2(sK3(sK0,u1_struct_0(sK1)),sK0) | (spl4_1 | ~spl4_2 | spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_6 | ~spl4_7 | ~spl4_8)),
% 0.22/0.49    inference(subsumption_resolution,[],[f136,f108])).
% 0.22/0.49  fof(f136,plain,(
% 0.22/0.49    ~v2_tex_2(u1_struct_0(sK1),sK0) | v3_tex_2(sK3(sK0,u1_struct_0(sK1)),sK0) | (spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_6 | ~spl4_8)),
% 0.22/0.49    inference(subsumption_resolution,[],[f135,f62])).
% 0.22/0.49  fof(f135,plain,(
% 0.22/0.49    v2_struct_0(sK0) | ~v2_tex_2(u1_struct_0(sK1),sK0) | v3_tex_2(sK3(sK0,u1_struct_0(sK1)),sK0) | (~spl4_4 | ~spl4_5 | ~spl4_6 | ~spl4_8)),
% 0.22/0.49    inference(subsumption_resolution,[],[f134,f74])).
% 0.22/0.49  fof(f134,plain,(
% 0.22/0.49    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~v2_tex_2(u1_struct_0(sK1),sK0) | v3_tex_2(sK3(sK0,u1_struct_0(sK1)),sK0) | (~spl4_4 | ~spl4_5 | ~spl4_8)),
% 0.22/0.49    inference(subsumption_resolution,[],[f133,f70])).
% 0.22/0.49  fof(f133,plain,(
% 0.22/0.49    ~v3_tdlat_3(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~v2_tex_2(u1_struct_0(sK1),sK0) | v3_tex_2(sK3(sK0,u1_struct_0(sK1)),sK0) | (~spl4_4 | ~spl4_8)),
% 0.22/0.49    inference(subsumption_resolution,[],[f102,f66])).
% 0.22/0.49  fof(f102,plain,(
% 0.22/0.49    ~v2_pre_topc(sK0) | ~v3_tdlat_3(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~v2_tex_2(u1_struct_0(sK1),sK0) | v3_tex_2(sK3(sK0,u1_struct_0(sK1)),sK0) | ~spl4_8),
% 0.22/0.49    inference(resolution,[],[f90,f44])).
% 0.22/0.49  fof(f44,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~v3_tdlat_3(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~v2_tex_2(X1,X0) | v3_tex_2(sK3(X0,X1),X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f20])).
% 0.22/0.49  fof(f91,plain,(
% 0.22/0.49    spl4_8 | ~spl4_6 | ~spl4_7),
% 0.22/0.49    inference(avatar_split_clause,[],[f87,f77,f73,f89])).
% 0.22/0.49  fof(f87,plain,(
% 0.22/0.49    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl4_6 | ~spl4_7)),
% 0.22/0.49    inference(subsumption_resolution,[],[f82,f74])).
% 0.22/0.49  fof(f82,plain,(
% 0.22/0.49    ~l1_pre_topc(sK0) | m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_7),
% 0.22/0.49    inference(resolution,[],[f78,f39])).
% 0.22/0.49  fof(f39,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f16])).
% 0.22/0.49  fof(f16,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f1])).
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).
% 0.22/0.49  fof(f79,plain,(
% 0.22/0.49    spl4_7),
% 0.22/0.49    inference(avatar_split_clause,[],[f28,f77])).
% 0.22/0.49  fof(f28,plain,(
% 0.22/0.49    m1_pre_topc(sK1,sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f11])).
% 0.22/0.49  fof(f75,plain,(
% 0.22/0.49    spl4_6),
% 0.22/0.49    inference(avatar_split_clause,[],[f32,f73])).
% 0.22/0.49  fof(f32,plain,(
% 0.22/0.49    l1_pre_topc(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f11])).
% 0.22/0.49  fof(f71,plain,(
% 0.22/0.49    spl4_5),
% 0.22/0.49    inference(avatar_split_clause,[],[f31,f69])).
% 0.22/0.49  fof(f31,plain,(
% 0.22/0.49    v3_tdlat_3(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f11])).
% 0.22/0.49  fof(f67,plain,(
% 0.22/0.49    spl4_4),
% 0.22/0.49    inference(avatar_split_clause,[],[f30,f65])).
% 0.22/0.49  fof(f30,plain,(
% 0.22/0.49    v2_pre_topc(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f11])).
% 0.22/0.49  fof(f63,plain,(
% 0.22/0.49    ~spl4_3),
% 0.22/0.49    inference(avatar_split_clause,[],[f29,f61])).
% 0.22/0.49  fof(f29,plain,(
% 0.22/0.49    ~v2_struct_0(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f11])).
% 0.22/0.49  fof(f59,plain,(
% 0.22/0.49    spl4_2),
% 0.22/0.49    inference(avatar_split_clause,[],[f27,f57])).
% 0.22/0.49  fof(f27,plain,(
% 0.22/0.49    v1_tdlat_3(sK1)),
% 0.22/0.49    inference(cnf_transformation,[],[f11])).
% 0.22/0.49  fof(f55,plain,(
% 0.22/0.49    ~spl4_1),
% 0.22/0.49    inference(avatar_split_clause,[],[f26,f53])).
% 0.22/0.49  fof(f26,plain,(
% 0.22/0.49    ~v2_struct_0(sK1)),
% 0.22/0.49    inference(cnf_transformation,[],[f11])).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (24205)------------------------------
% 0.22/0.49  % (24205)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (24205)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (24205)Memory used [KB]: 6396
% 0.22/0.49  % (24205)Time elapsed: 0.077 s
% 0.22/0.49  % (24205)------------------------------
% 0.22/0.49  % (24205)------------------------------
% 0.22/0.49  % (24211)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.49  % (24215)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.49  % (24207)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.49  % (24212)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.50  % (24209)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.50  % (24201)Success in time 0.132 s
%------------------------------------------------------------------------------
