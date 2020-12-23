%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:18:57 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  261 ( 502 expanded)
%              Number of leaves         :   44 ( 173 expanded)
%              Depth                    :   24
%              Number of atoms          : 1734 (3662 expanded)
%              Number of equality atoms :   19 ( 102 expanded)
%              Maximal formula depth    :   31 (   8 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f415,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f82,f87,f92,f97,f102,f107,f112,f117,f122,f127,f132,f137,f142,f147,f174,f179,f187,f192,f197,f213,f222,f229,f235,f262,f305,f311,f329,f332,f362,f369,f378,f388,f396,f414])).

fof(f414,plain,
    ( spl9_2
    | spl9_3
    | spl9_7
    | ~ spl9_8
    | ~ spl9_9
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_16
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_21
    | ~ spl9_22
    | ~ spl9_24
    | ~ spl9_28
    | ~ spl9_30
    | ~ spl9_32 ),
    inference(avatar_contradiction_clause,[],[f413])).

fof(f413,plain,
    ( $false
    | spl9_2
    | spl9_3
    | spl9_7
    | ~ spl9_8
    | ~ spl9_9
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_16
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_21
    | ~ spl9_22
    | ~ spl9_24
    | ~ spl9_28
    | ~ spl9_30
    | ~ spl9_32 ),
    inference(subsumption_resolution,[],[f412,f111])).

fof(f111,plain,
    ( ~ v2_struct_0(sK0)
    | spl9_7 ),
    inference(avatar_component_clause,[],[f109])).

fof(f109,plain,
    ( spl9_7
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f412,plain,
    ( v2_struct_0(sK0)
    | spl9_2
    | spl9_3
    | ~ spl9_8
    | ~ spl9_9
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_16
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_21
    | ~ spl9_22
    | ~ spl9_24
    | ~ spl9_28
    | ~ spl9_30
    | ~ spl9_32 ),
    inference(subsumption_resolution,[],[f411,f121])).

fof(f121,plain,
    ( l1_pre_topc(sK0)
    | ~ spl9_9 ),
    inference(avatar_component_clause,[],[f119])).

fof(f119,plain,
    ( spl9_9
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).

% (23178)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
fof(f411,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl9_2
    | spl9_3
    | ~ spl9_8
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_16
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_21
    | ~ spl9_22
    | ~ spl9_24
    | ~ spl9_28
    | ~ spl9_30
    | ~ spl9_32 ),
    inference(subsumption_resolution,[],[f410,f141])).

fof(f141,plain,
    ( m1_pre_topc(sK3,sK0)
    | ~ spl9_13 ),
    inference(avatar_component_clause,[],[f139])).

fof(f139,plain,
    ( spl9_13
  <=> m1_pre_topc(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).

fof(f410,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl9_2
    | spl9_3
    | ~ spl9_8
    | ~ spl9_12
    | ~ spl9_16
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_21
    | ~ spl9_22
    | ~ spl9_24
    | ~ spl9_28
    | ~ spl9_30
    | ~ spl9_32 ),
    inference(subsumption_resolution,[],[f407,f116])).

fof(f116,plain,
    ( v2_pre_topc(sK0)
    | ~ spl9_8 ),
    inference(avatar_component_clause,[],[f114])).

fof(f114,plain,
    ( spl9_8
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f407,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl9_2
    | spl9_3
    | ~ spl9_12
    | ~ spl9_16
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_21
    | ~ spl9_22
    | ~ spl9_24
    | ~ spl9_28
    | ~ spl9_30
    | ~ spl9_32 ),
    inference(resolution,[],[f404,f221])).

fof(f221,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)
    | ~ spl9_24 ),
    inference(avatar_component_clause,[],[f219])).

fof(f219,plain,
    ( spl9_24
  <=> r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_24])])).

fof(f404,plain,
    ( ! [X0] :
        ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(X0,sK1,sK3,sK2,sK4),sK5)
        | ~ v2_pre_topc(X0)
        | ~ m1_pre_topc(sK3,X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X0) )
    | spl9_2
    | spl9_3
    | ~ spl9_12
    | ~ spl9_16
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_21
    | ~ spl9_22
    | ~ spl9_28
    | ~ spl9_30
    | ~ spl9_32 ),
    inference(subsumption_resolution,[],[f403,f208])).

fof(f208,plain,
    ( v3_pre_topc(u1_struct_0(sK2),sK3)
    | ~ spl9_21 ),
    inference(avatar_component_clause,[],[f206])).

fof(f206,plain,
    ( spl9_21
  <=> v3_pre_topc(u1_struct_0(sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_21])])).

fof(f403,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(X0)
        | ~ r1_tmap_1(sK2,sK1,k3_tmap_1(X0,sK1,sK3,sK2,sK4),sK5)
        | ~ m1_pre_topc(sK3,X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ v3_pre_topc(u1_struct_0(sK2),sK3) )
    | spl9_2
    | spl9_3
    | ~ spl9_12
    | ~ spl9_16
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_22
    | ~ spl9_28
    | ~ spl9_30
    | ~ spl9_32 ),
    inference(subsumption_resolution,[],[f402,f300])).

fof(f300,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl9_28 ),
    inference(avatar_component_clause,[],[f299])).

fof(f299,plain,
    ( spl9_28
  <=> m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_28])])).

fof(f402,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(X0)
        | ~ r1_tmap_1(sK2,sK1,k3_tmap_1(X0,sK1,sK3,sK2,sK4),sK5)
        | ~ m1_pre_topc(sK3,X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ v3_pre_topc(u1_struct_0(sK2),sK3) )
    | spl9_2
    | spl9_3
    | ~ spl9_12
    | ~ spl9_16
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_22
    | ~ spl9_30
    | ~ spl9_32 ),
    inference(subsumption_resolution,[],[f401,f353])).

fof(f353,plain,
    ( r2_hidden(sK5,u1_struct_0(sK2))
    | ~ spl9_30 ),
    inference(avatar_component_clause,[],[f352])).

fof(f352,plain,
    ( spl9_30
  <=> r2_hidden(sK5,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_30])])).

fof(f401,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(X0)
        | ~ r1_tmap_1(sK2,sK1,k3_tmap_1(X0,sK1,sK3,sK2,sK4),sK5)
        | ~ m1_pre_topc(sK3,X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ r2_hidden(sK5,u1_struct_0(sK2))
        | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ v3_pre_topc(u1_struct_0(sK2),sK3) )
    | spl9_2
    | spl9_3
    | ~ spl9_12
    | ~ spl9_16
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_22
    | ~ spl9_32 ),
    inference(subsumption_resolution,[],[f400,f178])).

fof(f178,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ spl9_16 ),
    inference(avatar_component_clause,[],[f176])).

fof(f176,plain,
    ( spl9_16
  <=> m1_subset_1(sK5,u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).

fof(f400,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(X0)
        | ~ r1_tmap_1(sK2,sK1,k3_tmap_1(X0,sK1,sK3,sK2,sK4),sK5)
        | ~ m1_pre_topc(sK3,X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ m1_subset_1(sK5,u1_struct_0(sK3))
        | ~ r2_hidden(sK5,u1_struct_0(sK2))
        | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ v3_pre_topc(u1_struct_0(sK2),sK3) )
    | spl9_2
    | spl9_3
    | ~ spl9_12
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_22
    | ~ spl9_32 ),
    inference(subsumption_resolution,[],[f399,f136])).

fof(f136,plain,
    ( m1_pre_topc(sK2,sK3)
    | ~ spl9_12 ),
    inference(avatar_component_clause,[],[f134])).

fof(f134,plain,
    ( spl9_12
  <=> m1_pre_topc(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).

fof(f399,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(X0)
        | ~ r1_tmap_1(sK2,sK1,k3_tmap_1(X0,sK1,sK3,sK2,sK4),sK5)
        | ~ m1_pre_topc(sK2,sK3)
        | ~ m1_pre_topc(sK3,X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ m1_subset_1(sK5,u1_struct_0(sK3))
        | ~ r2_hidden(sK5,u1_struct_0(sK2))
        | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ v3_pre_topc(u1_struct_0(sK2),sK3) )
    | spl9_2
    | spl9_3
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_22
    | ~ spl9_32 ),
    inference(subsumption_resolution,[],[f398,f191])).

fof(f191,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ spl9_18 ),
    inference(avatar_component_clause,[],[f189])).

fof(f189,plain,
    ( spl9_18
  <=> m1_subset_1(sK5,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).

fof(f398,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(X0)
        | ~ r1_tmap_1(sK2,sK1,k3_tmap_1(X0,sK1,sK3,sK2,sK4),sK5)
        | ~ m1_subset_1(sK5,u1_struct_0(sK2))
        | ~ m1_pre_topc(sK2,sK3)
        | ~ m1_pre_topc(sK3,X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ m1_subset_1(sK5,u1_struct_0(sK3))
        | ~ r2_hidden(sK5,u1_struct_0(sK2))
        | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ v3_pre_topc(u1_struct_0(sK2),sK3) )
    | spl9_2
    | spl9_3
    | ~ spl9_20
    | ~ spl9_22
    | ~ spl9_32 ),
    inference(subsumption_resolution,[],[f397,f91])).

fof(f91,plain,
    ( ~ v2_struct_0(sK2)
    | spl9_3 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl9_3
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f397,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(X0)
        | ~ r1_tmap_1(sK2,sK1,k3_tmap_1(X0,sK1,sK3,sK2,sK4),sK5)
        | v2_struct_0(sK2)
        | ~ m1_subset_1(sK5,u1_struct_0(sK2))
        | ~ m1_pre_topc(sK2,sK3)
        | ~ m1_pre_topc(sK3,X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ m1_subset_1(sK5,u1_struct_0(sK3))
        | ~ r2_hidden(sK5,u1_struct_0(sK2))
        | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ v3_pre_topc(u1_struct_0(sK2),sK3) )
    | spl9_2
    | ~ spl9_20
    | ~ spl9_22
    | ~ spl9_32 ),
    inference(resolution,[],[f361,f276])).

fof(f276,plain,
    ( ! [X4,X5] :
        ( r1_tarski(sK8(sK3,X4,X5),X4)
        | ~ m1_subset_1(X5,u1_struct_0(sK3))
        | ~ r2_hidden(X5,X4)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ v3_pre_topc(X4,sK3) )
    | spl9_2
    | ~ spl9_20
    | ~ spl9_22 ),
    inference(subsumption_resolution,[],[f275,f211])).

fof(f211,plain,
    ( l1_pre_topc(sK3)
    | ~ spl9_22 ),
    inference(avatar_component_clause,[],[f210])).

fof(f210,plain,
    ( spl9_22
  <=> l1_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_22])])).

fof(f275,plain,
    ( ! [X4,X5] :
        ( ~ l1_pre_topc(sK3)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_subset_1(X5,u1_struct_0(sK3))
        | ~ r2_hidden(X5,X4)
        | r1_tarski(sK8(sK3,X4,X5),X4)
        | ~ v3_pre_topc(X4,sK3) )
    | spl9_2
    | ~ spl9_20 ),
    inference(subsumption_resolution,[],[f156,f203])).

fof(f203,plain,
    ( v2_pre_topc(sK3)
    | ~ spl9_20 ),
    inference(avatar_component_clause,[],[f202])).

fof(f202,plain,
    ( spl9_20
  <=> v2_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_20])])).

fof(f156,plain,
    ( ! [X4,X5] :
        ( ~ v2_pre_topc(sK3)
        | ~ l1_pre_topc(sK3)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_subset_1(X5,u1_struct_0(sK3))
        | ~ r2_hidden(X5,X4)
        | r1_tarski(sK8(sK3,X4,X5),X4)
        | ~ v3_pre_topc(X4,sK3) )
    | spl9_2 ),
    inference(resolution,[],[f86,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_hidden(X2,X1)
      | r1_tarski(sK8(X0,X1,X2),X1)
      | ~ v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( r1_tarski(X3,X1)
                    & m1_connsp_2(X3,X0,X2)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( r1_tarski(X3,X1)
                    & m1_connsp_2(X3,X0,X2)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ~ ( r1_tarski(X3,X1)
                            & m1_connsp_2(X3,X0,X2) ) )
                    & r2_hidden(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_connsp_2)).

fof(f86,plain,
    ( ~ v2_struct_0(sK3)
    | spl9_2 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl9_2
  <=> v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f361,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(sK8(sK3,u1_struct_0(sK2),sK5),u1_struct_0(X0))
        | ~ v2_pre_topc(X1)
        | ~ r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5)
        | v2_struct_0(X0)
        | ~ m1_subset_1(sK5,u1_struct_0(X0))
        | ~ m1_pre_topc(X0,sK3)
        | ~ m1_pre_topc(sK3,X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl9_32 ),
    inference(avatar_component_clause,[],[f360])).

fof(f360,plain,
    ( spl9_32
  <=> ! [X1,X0] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X1)
        | ~ r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5)
        | ~ r1_tarski(sK8(sK3,u1_struct_0(sK2),sK5),u1_struct_0(X0))
        | ~ m1_subset_1(sK5,u1_struct_0(X0))
        | ~ m1_pre_topc(X0,sK3)
        | ~ m1_pre_topc(sK3,X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_32])])).

fof(f396,plain,
    ( ~ spl9_26
    | spl9_34 ),
    inference(avatar_contradiction_clause,[],[f395])).

fof(f395,plain,
    ( $false
    | ~ spl9_26
    | spl9_34 ),
    inference(subsumption_resolution,[],[f394,f244])).

fof(f244,plain,
    ( l1_pre_topc(sK2)
    | ~ spl9_26 ),
    inference(avatar_component_clause,[],[f243])).

fof(f243,plain,
    ( spl9_26
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_26])])).

fof(f394,plain,
    ( ~ l1_pre_topc(sK2)
    | spl9_34 ),
    inference(resolution,[],[f387,f55])).

fof(f55,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f387,plain,
    ( ~ l1_struct_0(sK2)
    | spl9_34 ),
    inference(avatar_component_clause,[],[f385])).

fof(f385,plain,
    ( spl9_34
  <=> l1_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_34])])).

fof(f388,plain,
    ( ~ spl9_34
    | spl9_3
    | ~ spl9_33 ),
    inference(avatar_split_clause,[],[f382,f366,f89,f385])).

fof(f366,plain,
    ( spl9_33
  <=> v1_xboole_0(u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_33])])).

fof(f382,plain,
    ( ~ l1_struct_0(sK2)
    | spl9_3
    | ~ spl9_33 ),
    inference(subsumption_resolution,[],[f381,f91])).

fof(f381,plain,
    ( ~ l1_struct_0(sK2)
    | v2_struct_0(sK2)
    | ~ spl9_33 ),
    inference(resolution,[],[f368,f58])).

fof(f58,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
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

fof(f368,plain,
    ( v1_xboole_0(u1_struct_0(sK2))
    | ~ spl9_33 ),
    inference(avatar_component_clause,[],[f366])).

fof(f378,plain,
    ( spl9_2
    | ~ spl9_16
    | ~ spl9_20
    | ~ spl9_21
    | ~ spl9_22
    | ~ spl9_28
    | ~ spl9_30
    | spl9_31 ),
    inference(avatar_contradiction_clause,[],[f377])).

fof(f377,plain,
    ( $false
    | spl9_2
    | ~ spl9_16
    | ~ spl9_20
    | ~ spl9_21
    | ~ spl9_22
    | ~ spl9_28
    | ~ spl9_30
    | spl9_31 ),
    inference(subsumption_resolution,[],[f376,f208])).

fof(f376,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK2),sK3)
    | spl9_2
    | ~ spl9_16
    | ~ spl9_20
    | ~ spl9_22
    | ~ spl9_28
    | ~ spl9_30
    | spl9_31 ),
    inference(subsumption_resolution,[],[f375,f86])).

fof(f375,plain,
    ( v2_struct_0(sK3)
    | ~ v3_pre_topc(u1_struct_0(sK2),sK3)
    | ~ spl9_16
    | ~ spl9_20
    | ~ spl9_22
    | ~ spl9_28
    | ~ spl9_30
    | spl9_31 ),
    inference(subsumption_resolution,[],[f374,f353])).

fof(f374,plain,
    ( ~ r2_hidden(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK3)
    | ~ v3_pre_topc(u1_struct_0(sK2),sK3)
    | ~ spl9_16
    | ~ spl9_20
    | ~ spl9_22
    | ~ spl9_28
    | spl9_31 ),
    inference(subsumption_resolution,[],[f373,f178])).

fof(f373,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ r2_hidden(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK3)
    | ~ v3_pre_topc(u1_struct_0(sK2),sK3)
    | ~ spl9_20
    | ~ spl9_22
    | ~ spl9_28
    | spl9_31 ),
    inference(subsumption_resolution,[],[f372,f300])).

fof(f372,plain,
    ( ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ r2_hidden(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK3)
    | ~ v3_pre_topc(u1_struct_0(sK2),sK3)
    | ~ spl9_20
    | ~ spl9_22
    | spl9_31 ),
    inference(subsumption_resolution,[],[f371,f211])).

fof(f371,plain,
    ( ~ l1_pre_topc(sK3)
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ r2_hidden(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK3)
    | ~ v3_pre_topc(u1_struct_0(sK2),sK3)
    | ~ spl9_20
    | spl9_31 ),
    inference(subsumption_resolution,[],[f370,f203])).

fof(f370,plain,
    ( ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ r2_hidden(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK3)
    | ~ v3_pre_topc(u1_struct_0(sK2),sK3)
    | spl9_31 ),
    inference(resolution,[],[f358,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK8(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_hidden(X2,X1)
      | v2_struct_0(X0)
      | ~ v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f358,plain,
    ( ~ m1_subset_1(sK8(sK3,u1_struct_0(sK2),sK5),k1_zfmisc_1(u1_struct_0(sK3)))
    | spl9_31 ),
    inference(avatar_component_clause,[],[f356])).

fof(f356,plain,
    ( spl9_31
  <=> m1_subset_1(sK8(sK3,u1_struct_0(sK2),sK5),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_31])])).

fof(f369,plain,
    ( spl9_33
    | ~ spl9_18
    | spl9_30 ),
    inference(avatar_split_clause,[],[f364,f352,f189,f366])).

fof(f364,plain,
    ( v1_xboole_0(u1_struct_0(sK2))
    | ~ spl9_18
    | spl9_30 ),
    inference(subsumption_resolution,[],[f363,f191])).

fof(f363,plain,
    ( v1_xboole_0(u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | spl9_30 ),
    inference(resolution,[],[f354,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f354,plain,
    ( ~ r2_hidden(sK5,u1_struct_0(sK2))
    | spl9_30 ),
    inference(avatar_component_clause,[],[f352])).

fof(f362,plain,
    ( ~ spl9_30
    | ~ spl9_31
    | spl9_32
    | ~ spl9_1
    | spl9_2
    | spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_16
    | ~ spl9_17
    | ~ spl9_19
    | spl9_23
    | ~ spl9_29 ),
    inference(avatar_split_clause,[],[f343,f303,f215,f194,f184,f176,f104,f99,f94,f84,f79,f360,f356,f352])).

fof(f79,plain,
    ( spl9_1
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f94,plain,
    ( spl9_4
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f99,plain,
    ( spl9_5
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f104,plain,
    ( spl9_6
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f184,plain,
    ( spl9_17
  <=> v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_17])])).

fof(f194,plain,
    ( spl9_19
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_19])])).

fof(f215,plain,
    ( spl9_23
  <=> r1_tmap_1(sK3,sK1,sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_23])])).

fof(f303,plain,
    ( spl9_29
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK3))
        | m1_connsp_2(sK8(sK3,u1_struct_0(sK2),X0),sK3,X0)
        | ~ r2_hidden(X0,u1_struct_0(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_29])])).

fof(f343,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(sK3,X1)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X0,sK3)
        | ~ m1_subset_1(sK8(sK3,u1_struct_0(sK2),sK5),k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_subset_1(sK5,u1_struct_0(X0))
        | ~ r1_tarski(sK8(sK3,u1_struct_0(sK2),sK5),u1_struct_0(X0))
        | ~ l1_pre_topc(X1)
        | ~ r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5)
        | ~ v2_pre_topc(X1)
        | ~ r2_hidden(sK5,u1_struct_0(sK2)) )
    | ~ spl9_1
    | spl9_2
    | spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_16
    | ~ spl9_17
    | ~ spl9_19
    | spl9_23
    | ~ spl9_29 ),
    inference(subsumption_resolution,[],[f342,f178])).

fof(f342,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(sK3,X1)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X0,sK3)
        | ~ m1_subset_1(sK8(sK3,u1_struct_0(sK2),sK5),k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_subset_1(sK5,u1_struct_0(X0))
        | ~ r1_tarski(sK8(sK3,u1_struct_0(sK2),sK5),u1_struct_0(X0))
        | ~ l1_pre_topc(X1)
        | ~ r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5)
        | ~ v2_pre_topc(X1)
        | ~ m1_subset_1(sK5,u1_struct_0(sK3))
        | ~ r2_hidden(sK5,u1_struct_0(sK2)) )
    | ~ spl9_1
    | spl9_2
    | spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_16
    | ~ spl9_17
    | ~ spl9_19
    | spl9_23
    | ~ spl9_29 ),
    inference(resolution,[],[f341,f304])).

fof(f304,plain,
    ( ! [X0] :
        ( m1_connsp_2(sK8(sK3,u1_struct_0(sK2),X0),sK3,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ r2_hidden(X0,u1_struct_0(sK2)) )
    | ~ spl9_29 ),
    inference(avatar_component_clause,[],[f303])).

fof(f341,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_connsp_2(X2,sK3,sK5)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X1,sK3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_subset_1(sK5,u1_struct_0(X1))
        | ~ r1_tarski(X2,u1_struct_0(X1))
        | ~ l1_pre_topc(X0)
        | ~ r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),sK5)
        | ~ v2_pre_topc(X0) )
    | ~ spl9_1
    | spl9_2
    | spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_16
    | ~ spl9_17
    | ~ spl9_19
    | spl9_23 ),
    inference(subsumption_resolution,[],[f340,f178])).

fof(f340,plain,
    ( ! [X2,X0,X1] :
        ( ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X1,sK3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_subset_1(sK5,u1_struct_0(sK3))
        | ~ m1_subset_1(sK5,u1_struct_0(X1))
        | ~ r1_tarski(X2,u1_struct_0(X1))
        | ~ m1_connsp_2(X2,sK3,sK5)
        | ~ r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),sK5)
        | ~ v2_pre_topc(X0) )
    | ~ spl9_1
    | spl9_2
    | spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_17
    | ~ spl9_19
    | spl9_23 ),
    inference(subsumption_resolution,[],[f339,f196])).

fof(f196,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ spl9_19 ),
    inference(avatar_component_clause,[],[f194])).

fof(f339,plain,
    ( ! [X2,X0,X1] :
        ( ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(X0)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ m1_pre_topc(X1,sK3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_subset_1(sK5,u1_struct_0(sK3))
        | ~ m1_subset_1(sK5,u1_struct_0(X1))
        | ~ r1_tarski(X2,u1_struct_0(X1))
        | ~ m1_connsp_2(X2,sK3,sK5)
        | ~ r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),sK5)
        | ~ v2_pre_topc(X0) )
    | ~ spl9_1
    | spl9_2
    | spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_17
    | spl9_23 ),
    inference(subsumption_resolution,[],[f338,f186])).

fof(f186,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ spl9_17 ),
    inference(avatar_component_clause,[],[f184])).

fof(f338,plain,
    ( ! [X2,X0,X1] :
        ( ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(X0)
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ m1_pre_topc(X1,sK3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_subset_1(sK5,u1_struct_0(sK3))
        | ~ m1_subset_1(sK5,u1_struct_0(X1))
        | ~ r1_tarski(X2,u1_struct_0(X1))
        | ~ m1_connsp_2(X2,sK3,sK5)
        | ~ r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),sK5)
        | ~ v2_pre_topc(X0) )
    | ~ spl9_1
    | spl9_2
    | spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | spl9_23 ),
    inference(subsumption_resolution,[],[f337,f86])).

fof(f337,plain,
    ( ! [X2,X0,X1] :
        ( ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(X0)
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ m1_pre_topc(X1,sK3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_subset_1(sK5,u1_struct_0(sK3))
        | ~ m1_subset_1(sK5,u1_struct_0(X1))
        | ~ r1_tarski(X2,u1_struct_0(X1))
        | ~ m1_connsp_2(X2,sK3,sK5)
        | ~ r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),sK5)
        | ~ v2_pre_topc(X0) )
    | ~ spl9_1
    | spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | spl9_23 ),
    inference(subsumption_resolution,[],[f336,f106])).

fof(f106,plain,
    ( l1_pre_topc(sK1)
    | ~ spl9_6 ),
    inference(avatar_component_clause,[],[f104])).

fof(f336,plain,
    ( ! [X2,X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(X1)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(X0)
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ m1_pre_topc(X1,sK3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_subset_1(sK5,u1_struct_0(sK3))
        | ~ m1_subset_1(sK5,u1_struct_0(X1))
        | ~ r1_tarski(X2,u1_struct_0(X1))
        | ~ m1_connsp_2(X2,sK3,sK5)
        | ~ r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),sK5)
        | ~ v2_pre_topc(X0) )
    | ~ spl9_1
    | spl9_4
    | ~ spl9_5
    | spl9_23 ),
    inference(subsumption_resolution,[],[f335,f101])).

fof(f101,plain,
    ( v2_pre_topc(sK1)
    | ~ spl9_5 ),
    inference(avatar_component_clause,[],[f99])).

fof(f335,plain,
    ( ! [X2,X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(X1)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(X0)
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ m1_pre_topc(X1,sK3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_subset_1(sK5,u1_struct_0(sK3))
        | ~ m1_subset_1(sK5,u1_struct_0(X1))
        | ~ r1_tarski(X2,u1_struct_0(X1))
        | ~ m1_connsp_2(X2,sK3,sK5)
        | ~ r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),sK5)
        | ~ v2_pre_topc(X0) )
    | ~ spl9_1
    | spl9_4
    | spl9_23 ),
    inference(subsumption_resolution,[],[f334,f96])).

fof(f96,plain,
    ( ~ v2_struct_0(sK1)
    | spl9_4 ),
    inference(avatar_component_clause,[],[f94])).

fof(f334,plain,
    ( ! [X2,X0,X1] :
        ( ~ l1_pre_topc(X0)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(X1)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(X0)
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ m1_pre_topc(X1,sK3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_subset_1(sK5,u1_struct_0(sK3))
        | ~ m1_subset_1(sK5,u1_struct_0(X1))
        | ~ r1_tarski(X2,u1_struct_0(X1))
        | ~ m1_connsp_2(X2,sK3,sK5)
        | ~ r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),sK5)
        | ~ v2_pre_topc(X0) )
    | ~ spl9_1
    | spl9_23 ),
    inference(resolution,[],[f216,f152])).

fof(f152,plain,
    ( ! [X6,X10,X8,X7,X5,X9] :
        ( r1_tmap_1(X8,X6,sK4,X10)
        | ~ l1_pre_topc(X5)
        | v2_struct_0(X6)
        | ~ v2_pre_topc(X6)
        | ~ l1_pre_topc(X6)
        | v2_struct_0(X7)
        | v2_struct_0(X8)
        | ~ m1_pre_topc(X8,X5)
        | v2_struct_0(X5)
        | ~ v1_funct_2(sK4,u1_struct_0(X8),u1_struct_0(X6))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(X6))))
        | ~ m1_pre_topc(X7,X8)
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))
        | ~ m1_subset_1(X10,u1_struct_0(X8))
        | ~ m1_subset_1(X10,u1_struct_0(X7))
        | ~ r1_tarski(X9,u1_struct_0(X7))
        | ~ m1_connsp_2(X9,X8,X10)
        | ~ r1_tmap_1(X7,X6,k3_tmap_1(X5,X6,X8,X7,sK4),X10)
        | ~ v2_pre_topc(X5) )
    | ~ spl9_1 ),
    inference(subsumption_resolution,[],[f149,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X2,X1)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tsep_1)).

fof(f149,plain,
    ( ! [X6,X10,X8,X7,X5,X9] :
        ( ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X5)
        | v2_struct_0(X6)
        | ~ v2_pre_topc(X6)
        | ~ l1_pre_topc(X6)
        | v2_struct_0(X7)
        | ~ m1_pre_topc(X7,X5)
        | v2_struct_0(X8)
        | ~ m1_pre_topc(X8,X5)
        | v2_struct_0(X5)
        | ~ v1_funct_2(sK4,u1_struct_0(X8),u1_struct_0(X6))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(X6))))
        | ~ m1_pre_topc(X7,X8)
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))
        | ~ m1_subset_1(X10,u1_struct_0(X8))
        | ~ m1_subset_1(X10,u1_struct_0(X7))
        | ~ r1_tarski(X9,u1_struct_0(X7))
        | ~ m1_connsp_2(X9,X8,X10)
        | ~ r1_tmap_1(X7,X6,k3_tmap_1(X5,X6,X8,X7,sK4),X10)
        | r1_tmap_1(X8,X6,sK4,X10) )
    | ~ spl9_1 ),
    inference(resolution,[],[f81,f74])).

fof(f74,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( ~ v1_funct_1(X4)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X0)
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ m1_subset_1(X7,u1_struct_0(X3))
      | ~ m1_subset_1(X7,u1_struct_0(X2))
      | ~ r1_tarski(X5,u1_struct_0(X2))
      | ~ m1_connsp_2(X5,X3,X7)
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
      | r1_tmap_1(X3,X1,X4,X7) ) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X7,u1_struct_0(X2))
      | ~ r1_tarski(X5,u1_struct_0(X2))
      | ~ m1_connsp_2(X5,X3,X6)
      | X6 != X7
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
      | r1_tmap_1(X3,X1,X4,X6) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ! [X7] :
                                  ( ( r1_tmap_1(X3,X1,X4,X6)
                                  <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) )
                                  | X6 != X7
                                  | ~ m1_connsp_2(X5,X3,X6)
                                  | ~ r1_tarski(X5,u1_struct_0(X2))
                                  | ~ m1_subset_1(X7,u1_struct_0(X2)) )
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ! [X7] :
                                  ( ( r1_tmap_1(X3,X1,X4,X6)
                                  <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) )
                                  | X6 != X7
                                  | ~ m1_connsp_2(X5,X3,X6)
                                  | ~ r1_tarski(X5,u1_struct_0(X2))
                                  | ~ m1_subset_1(X7,u1_struct_0(X2)) )
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( m1_pre_topc(X2,X3)
                       => ! [X5] :
                            ( m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X3))
                               => ! [X7] :
                                    ( m1_subset_1(X7,u1_struct_0(X2))
                                   => ( ( X6 = X7
                                        & m1_connsp_2(X5,X3,X6)
                                        & r1_tarski(X5,u1_struct_0(X2)) )
                                     => ( r1_tmap_1(X3,X1,X4,X6)
                                      <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) ) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_tmap_1)).

fof(f81,plain,
    ( v1_funct_1(sK4)
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f79])).

fof(f216,plain,
    ( ~ r1_tmap_1(sK3,sK1,sK4,sK5)
    | spl9_23 ),
    inference(avatar_component_clause,[],[f215])).

fof(f332,plain,
    ( ~ spl9_10
    | ~ spl9_23
    | ~ spl9_24 ),
    inference(avatar_contradiction_clause,[],[f331])).

fof(f331,plain,
    ( $false
    | ~ spl9_10
    | ~ spl9_23
    | ~ spl9_24 ),
    inference(subsumption_resolution,[],[f330,f221])).

fof(f330,plain,
    ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)
    | ~ spl9_10
    | ~ spl9_23 ),
    inference(subsumption_resolution,[],[f200,f217])).

fof(f217,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK5)
    | ~ spl9_23 ),
    inference(avatar_component_clause,[],[f215])).

fof(f200,plain,
    ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)
    | ~ r1_tmap_1(sK3,sK1,sK4,sK5)
    | ~ spl9_10 ),
    inference(forward_demodulation,[],[f36,f126])).

fof(f126,plain,
    ( sK5 = sK6
    | ~ spl9_10 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl9_10
  <=> sK5 = sK6 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).

fof(f36,plain,
    ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)
    | ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( r1_tmap_1(X3,X1,X4,X5)
                              <~> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) )
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
                      & v1_tsep_1(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( r1_tmap_1(X3,X1,X4,X5)
                              <~> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) )
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
                      & v1_tsep_1(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => ( ( m1_pre_topc(X2,X3)
                            & v1_tsep_1(X2,X3) )
                         => ! [X5] :
                              ( m1_subset_1(X5,u1_struct_0(X3))
                             => ! [X6] :
                                  ( m1_subset_1(X6,u1_struct_0(X2))
                                 => ( X5 = X6
                                   => ( r1_tmap_1(X3,X1,X4,X5)
                                    <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) ) ) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( ( m1_pre_topc(X2,X3)
                          & v1_tsep_1(X2,X3) )
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X3))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X2))
                               => ( X5 = X6
                                 => ( r1_tmap_1(X3,X1,X4,X5)
                                  <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_tmap_1)).

fof(f329,plain,
    ( ~ spl9_1
    | spl9_2
    | spl9_3
    | spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | spl9_7
    | ~ spl9_8
    | ~ spl9_9
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_16
    | ~ spl9_17
    | ~ spl9_18
    | ~ spl9_19
    | ~ spl9_23
    | spl9_24 ),
    inference(avatar_contradiction_clause,[],[f328])).

fof(f328,plain,
    ( $false
    | ~ spl9_1
    | spl9_2
    | spl9_3
    | spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | spl9_7
    | ~ spl9_8
    | ~ spl9_9
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_16
    | ~ spl9_17
    | ~ spl9_18
    | ~ spl9_19
    | ~ spl9_23
    | spl9_24 ),
    inference(subsumption_resolution,[],[f327,f121])).

fof(f327,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl9_1
    | spl9_2
    | spl9_3
    | spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | spl9_7
    | ~ spl9_8
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_16
    | ~ spl9_17
    | ~ spl9_18
    | ~ spl9_19
    | ~ spl9_23
    | spl9_24 ),
    inference(subsumption_resolution,[],[f326,f217])).

fof(f326,plain,
    ( ~ r1_tmap_1(sK3,sK1,sK4,sK5)
    | ~ l1_pre_topc(sK0)
    | ~ spl9_1
    | spl9_2
    | spl9_3
    | spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | spl9_7
    | ~ spl9_8
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_16
    | ~ spl9_17
    | ~ spl9_18
    | ~ spl9_19
    | spl9_24 ),
    inference(subsumption_resolution,[],[f325,f136])).

fof(f325,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | ~ r1_tmap_1(sK3,sK1,sK4,sK5)
    | ~ l1_pre_topc(sK0)
    | ~ spl9_1
    | spl9_2
    | spl9_3
    | spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | spl9_7
    | ~ spl9_8
    | ~ spl9_13
    | ~ spl9_16
    | ~ spl9_17
    | ~ spl9_18
    | ~ spl9_19
    | spl9_24 ),
    inference(subsumption_resolution,[],[f324,f191])).

fof(f324,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ r1_tmap_1(sK3,sK1,sK4,sK5)
    | ~ l1_pre_topc(sK0)
    | ~ spl9_1
    | spl9_2
    | spl9_3
    | spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | spl9_7
    | ~ spl9_8
    | ~ spl9_13
    | ~ spl9_16
    | ~ spl9_17
    | ~ spl9_19
    | spl9_24 ),
    inference(subsumption_resolution,[],[f323,f178])).

fof(f323,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ r1_tmap_1(sK3,sK1,sK4,sK5)
    | ~ l1_pre_topc(sK0)
    | ~ spl9_1
    | spl9_2
    | spl9_3
    | spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | spl9_7
    | ~ spl9_8
    | ~ spl9_13
    | ~ spl9_17
    | ~ spl9_19
    | spl9_24 ),
    inference(subsumption_resolution,[],[f322,f116])).

fof(f322,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ r1_tmap_1(sK3,sK1,sK4,sK5)
    | ~ l1_pre_topc(sK0)
    | ~ spl9_1
    | spl9_2
    | spl9_3
    | spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | spl9_7
    | ~ spl9_13
    | ~ spl9_17
    | ~ spl9_19
    | spl9_24 ),
    inference(subsumption_resolution,[],[f321,f111])).

fof(f321,plain,
    ( v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ r1_tmap_1(sK3,sK1,sK4,sK5)
    | ~ l1_pre_topc(sK0)
    | ~ spl9_1
    | spl9_2
    | spl9_3
    | spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_13
    | ~ spl9_17
    | ~ spl9_19
    | spl9_24 ),
    inference(subsumption_resolution,[],[f320,f91])).

fof(f320,plain,
    ( v2_struct_0(sK2)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ r1_tmap_1(sK3,sK1,sK4,sK5)
    | ~ l1_pre_topc(sK0)
    | ~ spl9_1
    | spl9_2
    | spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_13
    | ~ spl9_17
    | ~ spl9_19
    | spl9_24 ),
    inference(subsumption_resolution,[],[f319,f141])).

fof(f319,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ r1_tmap_1(sK3,sK1,sK4,sK5)
    | ~ l1_pre_topc(sK0)
    | ~ spl9_1
    | spl9_2
    | spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_17
    | ~ spl9_19
    | spl9_24 ),
    inference(resolution,[],[f317,f220])).

fof(f220,plain,
    ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)
    | spl9_24 ),
    inference(avatar_component_clause,[],[f219])).

fof(f317,plain,
    ( ! [X2,X0,X1] :
        ( r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),X2)
        | ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(X1)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ m1_subset_1(X2,u1_struct_0(sK3))
        | ~ m1_subset_1(X2,u1_struct_0(X1))
        | ~ m1_pre_topc(X1,sK3)
        | ~ r1_tmap_1(sK3,sK1,sK4,X2)
        | ~ l1_pre_topc(X0) )
    | ~ spl9_1
    | spl9_2
    | spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_17
    | ~ spl9_19 ),
    inference(subsumption_resolution,[],[f316,f196])).

fof(f316,plain,
    ( ! [X2,X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(X1)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ m1_subset_1(X2,u1_struct_0(sK3))
        | ~ m1_subset_1(X2,u1_struct_0(X1))
        | ~ m1_pre_topc(X1,sK3)
        | ~ r1_tmap_1(sK3,sK1,sK4,X2)
        | r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),X2) )
    | ~ spl9_1
    | spl9_2
    | spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_17 ),
    inference(subsumption_resolution,[],[f315,f86])).

fof(f315,plain,
    ( ! [X2,X0,X1] :
        ( ~ l1_pre_topc(X0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(X1)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ m1_subset_1(X2,u1_struct_0(sK3))
        | ~ m1_subset_1(X2,u1_struct_0(X1))
        | ~ m1_pre_topc(X1,sK3)
        | ~ r1_tmap_1(sK3,sK1,sK4,X2)
        | r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),X2) )
    | ~ spl9_1
    | spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_17 ),
    inference(subsumption_resolution,[],[f314,f106])).

fof(f314,plain,
    ( ! [X2,X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(X1)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ m1_subset_1(X2,u1_struct_0(sK3))
        | ~ m1_subset_1(X2,u1_struct_0(X1))
        | ~ m1_pre_topc(X1,sK3)
        | ~ r1_tmap_1(sK3,sK1,sK4,X2)
        | r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),X2) )
    | ~ spl9_1
    | spl9_4
    | ~ spl9_5
    | ~ spl9_17 ),
    inference(subsumption_resolution,[],[f313,f101])).

fof(f313,plain,
    ( ! [X2,X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(X1)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ m1_subset_1(X2,u1_struct_0(sK3))
        | ~ m1_subset_1(X2,u1_struct_0(X1))
        | ~ m1_pre_topc(X1,sK3)
        | ~ r1_tmap_1(sK3,sK1,sK4,X2)
        | r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),X2) )
    | ~ spl9_1
    | spl9_4
    | ~ spl9_17 ),
    inference(subsumption_resolution,[],[f312,f96])).

fof(f312,plain,
    ( ! [X2,X0,X1] :
        ( ~ l1_pre_topc(X0)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(X1)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ m1_subset_1(X2,u1_struct_0(sK3))
        | ~ m1_subset_1(X2,u1_struct_0(X1))
        | ~ m1_pre_topc(X1,sK3)
        | ~ r1_tmap_1(sK3,sK1,sK4,X2)
        | r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),X2) )
    | ~ spl9_1
    | ~ spl9_17 ),
    inference(resolution,[],[f151,f186])).

fof(f151,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( ~ v1_funct_2(sK4,u1_struct_0(X2),u1_struct_0(X1))
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X0)
        | v2_struct_0(X3)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        | ~ m1_subset_1(X4,u1_struct_0(X2))
        | ~ m1_subset_1(X4,u1_struct_0(X3))
        | ~ m1_pre_topc(X3,X2)
        | ~ r1_tmap_1(X2,X1,sK4,X4)
        | r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,sK4),X4) )
    | ~ spl9_1 ),
    inference(subsumption_resolution,[],[f148,f69])).

fof(f148,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X0)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,X0)
        | v2_struct_0(X0)
        | ~ v1_funct_2(sK4,u1_struct_0(X2),u1_struct_0(X1))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        | ~ m1_subset_1(X4,u1_struct_0(X2))
        | ~ m1_subset_1(X4,u1_struct_0(X3))
        | ~ m1_pre_topc(X3,X2)
        | ~ r1_tmap_1(X2,X1,sK4,X4)
        | r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,sK4),X4) )
    | ~ spl9_1 ),
    inference(resolution,[],[f81,f75])).

fof(f75,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( ~ v1_funct_1(X4)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X0)
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ m1_subset_1(X6,u1_struct_0(X2))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_pre_topc(X3,X2)
      | ~ r1_tmap_1(X2,X1,X4,X6)
      | r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) ) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ m1_subset_1(X5,u1_struct_0(X2))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | X5 != X6
      | ~ m1_pre_topc(X3,X2)
      | ~ r1_tmap_1(X2,X1,X4,X5)
      | r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)
                              | ~ r1_tmap_1(X2,X1,X4,X5)
                              | ~ m1_pre_topc(X3,X2)
                              | X5 != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X2)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)
                              | ~ r1_tmap_1(X2,X1,X4,X5)
                              | ~ m1_pre_topc(X3,X2)
                              | X5 != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X2)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X2))
                         => ! [X6] :
                              ( m1_subset_1(X6,u1_struct_0(X3))
                             => ( ( r1_tmap_1(X2,X1,X4,X5)
                                  & m1_pre_topc(X3,X2)
                                  & X5 = X6 )
                               => r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_tmap_1)).

fof(f311,plain,
    ( ~ spl9_12
    | ~ spl9_22
    | spl9_28 ),
    inference(avatar_contradiction_clause,[],[f310])).

fof(f310,plain,
    ( $false
    | ~ spl9_12
    | ~ spl9_22
    | spl9_28 ),
    inference(subsumption_resolution,[],[f309,f211])).

fof(f309,plain,
    ( ~ l1_pre_topc(sK3)
    | ~ spl9_12
    | spl9_28 ),
    inference(subsumption_resolution,[],[f308,f136])).

fof(f308,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | ~ l1_pre_topc(sK3)
    | spl9_28 ),
    inference(resolution,[],[f301,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f301,plain,
    ( ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
    | spl9_28 ),
    inference(avatar_component_clause,[],[f299])).

fof(f305,plain,
    ( ~ spl9_28
    | spl9_29
    | spl9_2
    | ~ spl9_20
    | ~ spl9_21
    | ~ spl9_22 ),
    inference(avatar_split_clause,[],[f287,f210,f206,f202,f84,f303,f299])).

fof(f287,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ r2_hidden(X0,u1_struct_0(sK2))
        | m1_connsp_2(sK8(sK3,u1_struct_0(sK2),X0),sK3,X0)
        | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3))) )
    | spl9_2
    | ~ spl9_20
    | ~ spl9_21
    | ~ spl9_22 ),
    inference(resolution,[],[f286,f208])).

fof(f286,plain,
    ( ! [X2,X3] :
        ( ~ v3_pre_topc(X2,sK3)
        | ~ m1_subset_1(X3,u1_struct_0(sK3))
        | ~ r2_hidden(X3,X2)
        | m1_connsp_2(sK8(sK3,X2,X3),sK3,X3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) )
    | spl9_2
    | ~ spl9_20
    | ~ spl9_22 ),
    inference(subsumption_resolution,[],[f285,f211])).

fof(f285,plain,
    ( ! [X2,X3] :
        ( ~ l1_pre_topc(sK3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_subset_1(X3,u1_struct_0(sK3))
        | ~ r2_hidden(X3,X2)
        | m1_connsp_2(sK8(sK3,X2,X3),sK3,X3)
        | ~ v3_pre_topc(X2,sK3) )
    | spl9_2
    | ~ spl9_20 ),
    inference(subsumption_resolution,[],[f155,f203])).

fof(f155,plain,
    ( ! [X2,X3] :
        ( ~ v2_pre_topc(sK3)
        | ~ l1_pre_topc(sK3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_subset_1(X3,u1_struct_0(sK3))
        | ~ r2_hidden(X3,X2)
        | m1_connsp_2(sK8(sK3,X2,X3),sK3,X3)
        | ~ v3_pre_topc(X2,sK3) )
    | spl9_2 ),
    inference(resolution,[],[f86,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_hidden(X2,X1)
      | m1_connsp_2(sK8(X0,X1,X2),X0,X2)
      | ~ v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f262,plain,
    ( ~ spl9_9
    | ~ spl9_14
    | spl9_26 ),
    inference(avatar_contradiction_clause,[],[f261])).

fof(f261,plain,
    ( $false
    | ~ spl9_9
    | ~ spl9_14
    | spl9_26 ),
    inference(subsumption_resolution,[],[f256,f121])).

fof(f256,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl9_14
    | spl9_26 ),
    inference(resolution,[],[f251,f146])).

fof(f146,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ spl9_14 ),
    inference(avatar_component_clause,[],[f144])).

fof(f144,plain,
    ( spl9_14
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).

fof(f251,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK2,X0)
        | ~ l1_pre_topc(X0) )
    | spl9_26 ),
    inference(resolution,[],[f245,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f245,plain,
    ( ~ l1_pre_topc(sK2)
    | spl9_26 ),
    inference(avatar_component_clause,[],[f243])).

fof(f235,plain,
    ( ~ spl9_8
    | ~ spl9_9
    | ~ spl9_13
    | spl9_20 ),
    inference(avatar_contradiction_clause,[],[f234])).

fof(f234,plain,
    ( $false
    | ~ spl9_8
    | ~ spl9_9
    | ~ spl9_13
    | spl9_20 ),
    inference(subsumption_resolution,[],[f233,f116])).

fof(f233,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ spl9_9
    | ~ spl9_13
    | spl9_20 ),
    inference(subsumption_resolution,[],[f230,f121])).

fof(f230,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl9_13
    | spl9_20 ),
    inference(resolution,[],[f223,f141])).

fof(f223,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK3,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | spl9_20 ),
    inference(resolution,[],[f204,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
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
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f204,plain,
    ( ~ v2_pre_topc(sK3)
    | spl9_20 ),
    inference(avatar_component_clause,[],[f202])).

fof(f229,plain,
    ( ~ spl9_9
    | ~ spl9_13
    | spl9_22 ),
    inference(avatar_contradiction_clause,[],[f228])).

fof(f228,plain,
    ( $false
    | ~ spl9_9
    | ~ spl9_13
    | spl9_22 ),
    inference(subsumption_resolution,[],[f225,f121])).

fof(f225,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl9_13
    | spl9_22 ),
    inference(resolution,[],[f224,f141])).

fof(f224,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK3,X0)
        | ~ l1_pre_topc(X0) )
    | spl9_22 ),
    inference(resolution,[],[f212,f56])).

fof(f212,plain,
    ( ~ l1_pre_topc(sK3)
    | spl9_22 ),
    inference(avatar_component_clause,[],[f210])).

fof(f222,plain,
    ( spl9_23
    | spl9_24
    | ~ spl9_10 ),
    inference(avatar_split_clause,[],[f198,f124,f219,f215])).

fof(f198,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)
    | r1_tmap_1(sK3,sK1,sK4,sK5)
    | ~ spl9_10 ),
    inference(forward_demodulation,[],[f35,f126])).

fof(f35,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)
    | r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f15])).

fof(f213,plain,
    ( ~ spl9_20
    | spl9_21
    | ~ spl9_22
    | ~ spl9_11
    | ~ spl9_12 ),
    inference(avatar_split_clause,[],[f199,f134,f129,f210,f206,f202])).

fof(f129,plain,
    ( spl9_11
  <=> v1_tsep_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).

fof(f199,plain,
    ( ~ l1_pre_topc(sK3)
    | v3_pre_topc(u1_struct_0(sK2),sK3)
    | ~ v2_pre_topc(sK3)
    | ~ spl9_11
    | ~ spl9_12 ),
    inference(subsumption_resolution,[],[f181,f136])).

fof(f181,plain,
    ( ~ l1_pre_topc(sK3)
    | v3_pre_topc(u1_struct_0(sK2),sK3)
    | ~ v2_pre_topc(sK3)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ spl9_11 ),
    inference(subsumption_resolution,[],[f180,f57])).

fof(f180,plain,
    ( ~ l1_pre_topc(sK3)
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
    | v3_pre_topc(u1_struct_0(sK2),sK3)
    | ~ v2_pre_topc(sK3)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ spl9_11 ),
    inference(resolution,[],[f131,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ v1_tsep_1(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(u1_struct_0(X1),X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0) ) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X1) != X2
      | v3_pre_topc(X2,X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) )
              <=> v3_pre_topc(X2,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) )
              <=> v3_pre_topc(X2,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( ( m1_pre_topc(X1,X0)
                    & v1_tsep_1(X1,X0) )
                <=> v3_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_tsep_1)).

fof(f131,plain,
    ( v1_tsep_1(sK2,sK3)
    | ~ spl9_11 ),
    inference(avatar_component_clause,[],[f129])).

fof(f197,plain,(
    spl9_19 ),
    inference(avatar_split_clause,[],[f42,f194])).

fof(f42,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f15])).

fof(f192,plain,
    ( spl9_18
    | ~ spl9_10
    | ~ spl9_15 ),
    inference(avatar_split_clause,[],[f182,f171,f124,f189])).

fof(f171,plain,
    ( spl9_15
  <=> m1_subset_1(sK6,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).

fof(f182,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ spl9_10
    | ~ spl9_15 ),
    inference(forward_demodulation,[],[f173,f126])).

fof(f173,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ spl9_15 ),
    inference(avatar_component_clause,[],[f171])).

fof(f187,plain,(
    spl9_17 ),
    inference(avatar_split_clause,[],[f41,f184])).

fof(f41,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f179,plain,(
    spl9_16 ),
    inference(avatar_split_clause,[],[f39,f176])).

fof(f39,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f15])).

fof(f174,plain,(
    spl9_15 ),
    inference(avatar_split_clause,[],[f37,f171])).

fof(f37,plain,(
    m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f15])).

fof(f147,plain,(
    spl9_14 ),
    inference(avatar_split_clause,[],[f48,f144])).

fof(f48,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f142,plain,(
    spl9_13 ),
    inference(avatar_split_clause,[],[f46,f139])).

fof(f46,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f137,plain,(
    spl9_12 ),
    inference(avatar_split_clause,[],[f44,f134])).

fof(f44,plain,(
    m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f15])).

fof(f132,plain,(
    spl9_11 ),
    inference(avatar_split_clause,[],[f43,f129])).

fof(f43,plain,(
    v1_tsep_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f15])).

fof(f127,plain,(
    spl9_10 ),
    inference(avatar_split_clause,[],[f38,f124])).

fof(f38,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f15])).

fof(f122,plain,(
    spl9_9 ),
    inference(avatar_split_clause,[],[f54,f119])).

fof(f54,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f117,plain,(
    spl9_8 ),
    inference(avatar_split_clause,[],[f53,f114])).

fof(f53,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f112,plain,(
    ~ spl9_7 ),
    inference(avatar_split_clause,[],[f52,f109])).

fof(f52,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f107,plain,(
    spl9_6 ),
    inference(avatar_split_clause,[],[f51,f104])).

fof(f51,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f102,plain,(
    spl9_5 ),
    inference(avatar_split_clause,[],[f50,f99])).

fof(f50,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f97,plain,(
    ~ spl9_4 ),
    inference(avatar_split_clause,[],[f49,f94])).

fof(f49,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f92,plain,(
    ~ spl9_3 ),
    inference(avatar_split_clause,[],[f47,f89])).

fof(f47,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f87,plain,(
    ~ spl9_2 ),
    inference(avatar_split_clause,[],[f45,f84])).

fof(f45,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f15])).

fof(f82,plain,(
    spl9_1 ),
    inference(avatar_split_clause,[],[f40,f79])).

fof(f40,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:46:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.45  % (23192)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.45  % (23175)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.46  % (23175)Refutation found. Thanks to Tanya!
% 0.20/0.46  % SZS status Theorem for theBenchmark
% 0.20/0.46  % (23192)Refutation not found, incomplete strategy% (23192)------------------------------
% 0.20/0.46  % (23192)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % SZS output start Proof for theBenchmark
% 0.20/0.46  fof(f415,plain,(
% 0.20/0.46    $false),
% 0.20/0.46    inference(avatar_sat_refutation,[],[f82,f87,f92,f97,f102,f107,f112,f117,f122,f127,f132,f137,f142,f147,f174,f179,f187,f192,f197,f213,f222,f229,f235,f262,f305,f311,f329,f332,f362,f369,f378,f388,f396,f414])).
% 0.20/0.46  fof(f414,plain,(
% 0.20/0.46    spl9_2 | spl9_3 | spl9_7 | ~spl9_8 | ~spl9_9 | ~spl9_12 | ~spl9_13 | ~spl9_16 | ~spl9_18 | ~spl9_20 | ~spl9_21 | ~spl9_22 | ~spl9_24 | ~spl9_28 | ~spl9_30 | ~spl9_32),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f413])).
% 0.20/0.46  fof(f413,plain,(
% 0.20/0.46    $false | (spl9_2 | spl9_3 | spl9_7 | ~spl9_8 | ~spl9_9 | ~spl9_12 | ~spl9_13 | ~spl9_16 | ~spl9_18 | ~spl9_20 | ~spl9_21 | ~spl9_22 | ~spl9_24 | ~spl9_28 | ~spl9_30 | ~spl9_32)),
% 0.20/0.46    inference(subsumption_resolution,[],[f412,f111])).
% 0.20/0.46  fof(f111,plain,(
% 0.20/0.46    ~v2_struct_0(sK0) | spl9_7),
% 0.20/0.46    inference(avatar_component_clause,[],[f109])).
% 0.20/0.46  fof(f109,plain,(
% 0.20/0.46    spl9_7 <=> v2_struct_0(sK0)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).
% 0.20/0.46  fof(f412,plain,(
% 0.20/0.46    v2_struct_0(sK0) | (spl9_2 | spl9_3 | ~spl9_8 | ~spl9_9 | ~spl9_12 | ~spl9_13 | ~spl9_16 | ~spl9_18 | ~spl9_20 | ~spl9_21 | ~spl9_22 | ~spl9_24 | ~spl9_28 | ~spl9_30 | ~spl9_32)),
% 0.20/0.46    inference(subsumption_resolution,[],[f411,f121])).
% 0.20/0.46  fof(f121,plain,(
% 0.20/0.46    l1_pre_topc(sK0) | ~spl9_9),
% 0.20/0.46    inference(avatar_component_clause,[],[f119])).
% 0.20/0.46  fof(f119,plain,(
% 0.20/0.46    spl9_9 <=> l1_pre_topc(sK0)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).
% 0.20/0.46  % (23178)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.46  fof(f411,plain,(
% 0.20/0.46    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | (spl9_2 | spl9_3 | ~spl9_8 | ~spl9_12 | ~spl9_13 | ~spl9_16 | ~spl9_18 | ~spl9_20 | ~spl9_21 | ~spl9_22 | ~spl9_24 | ~spl9_28 | ~spl9_30 | ~spl9_32)),
% 0.20/0.46    inference(subsumption_resolution,[],[f410,f141])).
% 0.20/0.46  fof(f141,plain,(
% 0.20/0.46    m1_pre_topc(sK3,sK0) | ~spl9_13),
% 0.20/0.46    inference(avatar_component_clause,[],[f139])).
% 0.20/0.46  fof(f139,plain,(
% 0.20/0.46    spl9_13 <=> m1_pre_topc(sK3,sK0)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).
% 0.20/0.46  fof(f410,plain,(
% 0.20/0.46    ~m1_pre_topc(sK3,sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | (spl9_2 | spl9_3 | ~spl9_8 | ~spl9_12 | ~spl9_16 | ~spl9_18 | ~spl9_20 | ~spl9_21 | ~spl9_22 | ~spl9_24 | ~spl9_28 | ~spl9_30 | ~spl9_32)),
% 0.20/0.46    inference(subsumption_resolution,[],[f407,f116])).
% 0.20/0.46  fof(f116,plain,(
% 0.20/0.46    v2_pre_topc(sK0) | ~spl9_8),
% 0.20/0.46    inference(avatar_component_clause,[],[f114])).
% 0.20/0.46  fof(f114,plain,(
% 0.20/0.46    spl9_8 <=> v2_pre_topc(sK0)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).
% 0.20/0.46  fof(f407,plain,(
% 0.20/0.46    ~v2_pre_topc(sK0) | ~m1_pre_topc(sK3,sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | (spl9_2 | spl9_3 | ~spl9_12 | ~spl9_16 | ~spl9_18 | ~spl9_20 | ~spl9_21 | ~spl9_22 | ~spl9_24 | ~spl9_28 | ~spl9_30 | ~spl9_32)),
% 0.20/0.46    inference(resolution,[],[f404,f221])).
% 0.20/0.46  fof(f221,plain,(
% 0.20/0.46    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) | ~spl9_24),
% 0.20/0.46    inference(avatar_component_clause,[],[f219])).
% 0.20/0.46  fof(f219,plain,(
% 0.20/0.46    spl9_24 <=> r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl9_24])])).
% 0.20/0.46  fof(f404,plain,(
% 0.20/0.46    ( ! [X0] : (~r1_tmap_1(sK2,sK1,k3_tmap_1(X0,sK1,sK3,sK2,sK4),sK5) | ~v2_pre_topc(X0) | ~m1_pre_topc(sK3,X0) | ~l1_pre_topc(X0) | v2_struct_0(X0)) ) | (spl9_2 | spl9_3 | ~spl9_12 | ~spl9_16 | ~spl9_18 | ~spl9_20 | ~spl9_21 | ~spl9_22 | ~spl9_28 | ~spl9_30 | ~spl9_32)),
% 0.20/0.46    inference(subsumption_resolution,[],[f403,f208])).
% 0.20/0.46  fof(f208,plain,(
% 0.20/0.46    v3_pre_topc(u1_struct_0(sK2),sK3) | ~spl9_21),
% 0.20/0.46    inference(avatar_component_clause,[],[f206])).
% 0.20/0.46  fof(f206,plain,(
% 0.20/0.46    spl9_21 <=> v3_pre_topc(u1_struct_0(sK2),sK3)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl9_21])])).
% 0.20/0.46  fof(f403,plain,(
% 0.20/0.46    ( ! [X0] : (~v2_pre_topc(X0) | ~r1_tmap_1(sK2,sK1,k3_tmap_1(X0,sK1,sK3,sK2,sK4),sK5) | ~m1_pre_topc(sK3,X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~v3_pre_topc(u1_struct_0(sK2),sK3)) ) | (spl9_2 | spl9_3 | ~spl9_12 | ~spl9_16 | ~spl9_18 | ~spl9_20 | ~spl9_22 | ~spl9_28 | ~spl9_30 | ~spl9_32)),
% 0.20/0.46    inference(subsumption_resolution,[],[f402,f300])).
% 0.20/0.46  fof(f300,plain,(
% 0.20/0.46    m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3))) | ~spl9_28),
% 0.20/0.46    inference(avatar_component_clause,[],[f299])).
% 0.20/0.46  fof(f299,plain,(
% 0.20/0.46    spl9_28 <=> m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl9_28])])).
% 0.20/0.46  fof(f402,plain,(
% 0.20/0.46    ( ! [X0] : (~v2_pre_topc(X0) | ~r1_tmap_1(sK2,sK1,k3_tmap_1(X0,sK1,sK3,sK2,sK4),sK5) | ~m1_pre_topc(sK3,X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3))) | ~v3_pre_topc(u1_struct_0(sK2),sK3)) ) | (spl9_2 | spl9_3 | ~spl9_12 | ~spl9_16 | ~spl9_18 | ~spl9_20 | ~spl9_22 | ~spl9_30 | ~spl9_32)),
% 0.20/0.46    inference(subsumption_resolution,[],[f401,f353])).
% 0.20/0.46  fof(f353,plain,(
% 0.20/0.46    r2_hidden(sK5,u1_struct_0(sK2)) | ~spl9_30),
% 0.20/0.46    inference(avatar_component_clause,[],[f352])).
% 0.20/0.46  fof(f352,plain,(
% 0.20/0.46    spl9_30 <=> r2_hidden(sK5,u1_struct_0(sK2))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl9_30])])).
% 0.20/0.46  fof(f401,plain,(
% 0.20/0.46    ( ! [X0] : (~v2_pre_topc(X0) | ~r1_tmap_1(sK2,sK1,k3_tmap_1(X0,sK1,sK3,sK2,sK4),sK5) | ~m1_pre_topc(sK3,X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~r2_hidden(sK5,u1_struct_0(sK2)) | ~m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3))) | ~v3_pre_topc(u1_struct_0(sK2),sK3)) ) | (spl9_2 | spl9_3 | ~spl9_12 | ~spl9_16 | ~spl9_18 | ~spl9_20 | ~spl9_22 | ~spl9_32)),
% 0.20/0.46    inference(subsumption_resolution,[],[f400,f178])).
% 0.20/0.46  fof(f178,plain,(
% 0.20/0.46    m1_subset_1(sK5,u1_struct_0(sK3)) | ~spl9_16),
% 0.20/0.46    inference(avatar_component_clause,[],[f176])).
% 0.20/0.46  fof(f176,plain,(
% 0.20/0.46    spl9_16 <=> m1_subset_1(sK5,u1_struct_0(sK3))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).
% 0.20/0.46  fof(f400,plain,(
% 0.20/0.46    ( ! [X0] : (~v2_pre_topc(X0) | ~r1_tmap_1(sK2,sK1,k3_tmap_1(X0,sK1,sK3,sK2,sK4),sK5) | ~m1_pre_topc(sK3,X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~r2_hidden(sK5,u1_struct_0(sK2)) | ~m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3))) | ~v3_pre_topc(u1_struct_0(sK2),sK3)) ) | (spl9_2 | spl9_3 | ~spl9_12 | ~spl9_18 | ~spl9_20 | ~spl9_22 | ~spl9_32)),
% 0.20/0.46    inference(subsumption_resolution,[],[f399,f136])).
% 0.20/0.46  fof(f136,plain,(
% 0.20/0.46    m1_pre_topc(sK2,sK3) | ~spl9_12),
% 0.20/0.46    inference(avatar_component_clause,[],[f134])).
% 0.20/0.46  fof(f134,plain,(
% 0.20/0.46    spl9_12 <=> m1_pre_topc(sK2,sK3)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).
% 0.20/0.46  fof(f399,plain,(
% 0.20/0.46    ( ! [X0] : (~v2_pre_topc(X0) | ~r1_tmap_1(sK2,sK1,k3_tmap_1(X0,sK1,sK3,sK2,sK4),sK5) | ~m1_pre_topc(sK2,sK3) | ~m1_pre_topc(sK3,X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~r2_hidden(sK5,u1_struct_0(sK2)) | ~m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3))) | ~v3_pre_topc(u1_struct_0(sK2),sK3)) ) | (spl9_2 | spl9_3 | ~spl9_18 | ~spl9_20 | ~spl9_22 | ~spl9_32)),
% 0.20/0.46    inference(subsumption_resolution,[],[f398,f191])).
% 0.20/0.46  fof(f191,plain,(
% 0.20/0.46    m1_subset_1(sK5,u1_struct_0(sK2)) | ~spl9_18),
% 0.20/0.46    inference(avatar_component_clause,[],[f189])).
% 0.20/0.46  fof(f189,plain,(
% 0.20/0.46    spl9_18 <=> m1_subset_1(sK5,u1_struct_0(sK2))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).
% 0.20/0.46  fof(f398,plain,(
% 0.20/0.46    ( ! [X0] : (~v2_pre_topc(X0) | ~r1_tmap_1(sK2,sK1,k3_tmap_1(X0,sK1,sK3,sK2,sK4),sK5) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~m1_pre_topc(sK2,sK3) | ~m1_pre_topc(sK3,X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~r2_hidden(sK5,u1_struct_0(sK2)) | ~m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3))) | ~v3_pre_topc(u1_struct_0(sK2),sK3)) ) | (spl9_2 | spl9_3 | ~spl9_20 | ~spl9_22 | ~spl9_32)),
% 0.20/0.46    inference(subsumption_resolution,[],[f397,f91])).
% 0.20/0.46  fof(f91,plain,(
% 0.20/0.46    ~v2_struct_0(sK2) | spl9_3),
% 0.20/0.46    inference(avatar_component_clause,[],[f89])).
% 0.20/0.46  fof(f89,plain,(
% 0.20/0.46    spl9_3 <=> v2_struct_0(sK2)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 0.20/0.46  fof(f397,plain,(
% 0.20/0.46    ( ! [X0] : (~v2_pre_topc(X0) | ~r1_tmap_1(sK2,sK1,k3_tmap_1(X0,sK1,sK3,sK2,sK4),sK5) | v2_struct_0(sK2) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~m1_pre_topc(sK2,sK3) | ~m1_pre_topc(sK3,X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~r2_hidden(sK5,u1_struct_0(sK2)) | ~m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3))) | ~v3_pre_topc(u1_struct_0(sK2),sK3)) ) | (spl9_2 | ~spl9_20 | ~spl9_22 | ~spl9_32)),
% 0.20/0.46    inference(resolution,[],[f361,f276])).
% 0.20/0.46  fof(f276,plain,(
% 0.20/0.46    ( ! [X4,X5] : (r1_tarski(sK8(sK3,X4,X5),X4) | ~m1_subset_1(X5,u1_struct_0(sK3)) | ~r2_hidden(X5,X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK3))) | ~v3_pre_topc(X4,sK3)) ) | (spl9_2 | ~spl9_20 | ~spl9_22)),
% 0.20/0.46    inference(subsumption_resolution,[],[f275,f211])).
% 0.20/0.46  fof(f211,plain,(
% 0.20/0.46    l1_pre_topc(sK3) | ~spl9_22),
% 0.20/0.46    inference(avatar_component_clause,[],[f210])).
% 0.20/0.46  fof(f210,plain,(
% 0.20/0.46    spl9_22 <=> l1_pre_topc(sK3)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl9_22])])).
% 0.20/0.46  fof(f275,plain,(
% 0.20/0.46    ( ! [X4,X5] : (~l1_pre_topc(sK3) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(X5,u1_struct_0(sK3)) | ~r2_hidden(X5,X4) | r1_tarski(sK8(sK3,X4,X5),X4) | ~v3_pre_topc(X4,sK3)) ) | (spl9_2 | ~spl9_20)),
% 0.20/0.46    inference(subsumption_resolution,[],[f156,f203])).
% 0.20/0.46  fof(f203,plain,(
% 0.20/0.46    v2_pre_topc(sK3) | ~spl9_20),
% 0.20/0.46    inference(avatar_component_clause,[],[f202])).
% 0.20/0.46  fof(f202,plain,(
% 0.20/0.46    spl9_20 <=> v2_pre_topc(sK3)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl9_20])])).
% 0.20/0.46  fof(f156,plain,(
% 0.20/0.46    ( ! [X4,X5] : (~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(X5,u1_struct_0(sK3)) | ~r2_hidden(X5,X4) | r1_tarski(sK8(sK3,X4,X5),X4) | ~v3_pre_topc(X4,sK3)) ) | spl9_2),
% 0.20/0.46    inference(resolution,[],[f86,f62])).
% 0.20/0.46  fof(f62,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r2_hidden(X2,X1) | r1_tarski(sK8(X0,X1,X2),X1) | ~v3_pre_topc(X1,X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f22])).
% 0.20/0.46  fof(f22,plain,(
% 0.20/0.46    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> ! [X2] : (? [X3] : (r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.46    inference(flattening,[],[f21])).
% 0.20/0.46  fof(f21,plain,(
% 0.20/0.46    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> ! [X2] : ((? [X3] : ((r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.46    inference(ennf_transformation,[],[f6])).
% 0.20/0.46  fof(f6,axiom,(
% 0.20/0.46    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2))) & r2_hidden(X2,X1))))))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_connsp_2)).
% 0.20/0.46  fof(f86,plain,(
% 0.20/0.46    ~v2_struct_0(sK3) | spl9_2),
% 0.20/0.46    inference(avatar_component_clause,[],[f84])).
% 0.20/0.46  fof(f84,plain,(
% 0.20/0.46    spl9_2 <=> v2_struct_0(sK3)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 0.20/0.46  fof(f361,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~r1_tarski(sK8(sK3,u1_struct_0(sK2),sK5),u1_struct_0(X0)) | ~v2_pre_topc(X1) | ~r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5) | v2_struct_0(X0) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~m1_pre_topc(X0,sK3) | ~m1_pre_topc(sK3,X1) | ~l1_pre_topc(X1) | v2_struct_0(X1)) ) | ~spl9_32),
% 0.20/0.46    inference(avatar_component_clause,[],[f360])).
% 0.20/0.46  fof(f360,plain,(
% 0.20/0.46    spl9_32 <=> ! [X1,X0] : (v2_struct_0(X0) | ~v2_pre_topc(X1) | ~r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5) | ~r1_tarski(sK8(sK3,u1_struct_0(sK2),sK5),u1_struct_0(X0)) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~m1_pre_topc(X0,sK3) | ~m1_pre_topc(sK3,X1) | ~l1_pre_topc(X1) | v2_struct_0(X1))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl9_32])])).
% 0.20/0.46  fof(f396,plain,(
% 0.20/0.46    ~spl9_26 | spl9_34),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f395])).
% 0.20/0.46  fof(f395,plain,(
% 0.20/0.46    $false | (~spl9_26 | spl9_34)),
% 0.20/0.46    inference(subsumption_resolution,[],[f394,f244])).
% 0.20/0.46  fof(f244,plain,(
% 0.20/0.46    l1_pre_topc(sK2) | ~spl9_26),
% 0.20/0.46    inference(avatar_component_clause,[],[f243])).
% 0.20/0.46  fof(f243,plain,(
% 0.20/0.46    spl9_26 <=> l1_pre_topc(sK2)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl9_26])])).
% 0.20/0.46  fof(f394,plain,(
% 0.20/0.46    ~l1_pre_topc(sK2) | spl9_34),
% 0.20/0.46    inference(resolution,[],[f387,f55])).
% 0.20/0.46  fof(f55,plain,(
% 0.20/0.46    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f16])).
% 0.20/0.46  fof(f16,plain,(
% 0.20/0.46    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.20/0.46    inference(ennf_transformation,[],[f3])).
% 0.20/0.46  fof(f3,axiom,(
% 0.20/0.46    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.20/0.46  fof(f387,plain,(
% 0.20/0.46    ~l1_struct_0(sK2) | spl9_34),
% 0.20/0.46    inference(avatar_component_clause,[],[f385])).
% 0.20/0.46  fof(f385,plain,(
% 0.20/0.46    spl9_34 <=> l1_struct_0(sK2)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl9_34])])).
% 0.20/0.46  fof(f388,plain,(
% 0.20/0.46    ~spl9_34 | spl9_3 | ~spl9_33),
% 0.20/0.46    inference(avatar_split_clause,[],[f382,f366,f89,f385])).
% 0.20/0.46  fof(f366,plain,(
% 0.20/0.46    spl9_33 <=> v1_xboole_0(u1_struct_0(sK2))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl9_33])])).
% 0.20/0.46  fof(f382,plain,(
% 0.20/0.46    ~l1_struct_0(sK2) | (spl9_3 | ~spl9_33)),
% 0.20/0.46    inference(subsumption_resolution,[],[f381,f91])).
% 0.20/0.46  fof(f381,plain,(
% 0.20/0.46    ~l1_struct_0(sK2) | v2_struct_0(sK2) | ~spl9_33),
% 0.20/0.46    inference(resolution,[],[f368,f58])).
% 0.20/0.46  fof(f58,plain,(
% 0.20/0.46    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f20])).
% 0.20/0.46  fof(f20,plain,(
% 0.20/0.46    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.20/0.46    inference(flattening,[],[f19])).
% 0.20/0.46  fof(f19,plain,(
% 0.20/0.46    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.20/0.46    inference(ennf_transformation,[],[f5])).
% 0.20/0.46  fof(f5,axiom,(
% 0.20/0.46    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.20/0.46  fof(f368,plain,(
% 0.20/0.46    v1_xboole_0(u1_struct_0(sK2)) | ~spl9_33),
% 0.20/0.46    inference(avatar_component_clause,[],[f366])).
% 0.20/0.46  fof(f378,plain,(
% 0.20/0.46    spl9_2 | ~spl9_16 | ~spl9_20 | ~spl9_21 | ~spl9_22 | ~spl9_28 | ~spl9_30 | spl9_31),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f377])).
% 0.20/0.46  fof(f377,plain,(
% 0.20/0.46    $false | (spl9_2 | ~spl9_16 | ~spl9_20 | ~spl9_21 | ~spl9_22 | ~spl9_28 | ~spl9_30 | spl9_31)),
% 0.20/0.46    inference(subsumption_resolution,[],[f376,f208])).
% 0.20/0.46  fof(f376,plain,(
% 0.20/0.46    ~v3_pre_topc(u1_struct_0(sK2),sK3) | (spl9_2 | ~spl9_16 | ~spl9_20 | ~spl9_22 | ~spl9_28 | ~spl9_30 | spl9_31)),
% 0.20/0.46    inference(subsumption_resolution,[],[f375,f86])).
% 0.20/0.46  fof(f375,plain,(
% 0.20/0.46    v2_struct_0(sK3) | ~v3_pre_topc(u1_struct_0(sK2),sK3) | (~spl9_16 | ~spl9_20 | ~spl9_22 | ~spl9_28 | ~spl9_30 | spl9_31)),
% 0.20/0.46    inference(subsumption_resolution,[],[f374,f353])).
% 0.20/0.46  fof(f374,plain,(
% 0.20/0.46    ~r2_hidden(sK5,u1_struct_0(sK2)) | v2_struct_0(sK3) | ~v3_pre_topc(u1_struct_0(sK2),sK3) | (~spl9_16 | ~spl9_20 | ~spl9_22 | ~spl9_28 | spl9_31)),
% 0.20/0.46    inference(subsumption_resolution,[],[f373,f178])).
% 0.20/0.46  fof(f373,plain,(
% 0.20/0.46    ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~r2_hidden(sK5,u1_struct_0(sK2)) | v2_struct_0(sK3) | ~v3_pre_topc(u1_struct_0(sK2),sK3) | (~spl9_20 | ~spl9_22 | ~spl9_28 | spl9_31)),
% 0.20/0.46    inference(subsumption_resolution,[],[f372,f300])).
% 0.20/0.46  fof(f372,plain,(
% 0.20/0.46    ~m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~r2_hidden(sK5,u1_struct_0(sK2)) | v2_struct_0(sK3) | ~v3_pre_topc(u1_struct_0(sK2),sK3) | (~spl9_20 | ~spl9_22 | spl9_31)),
% 0.20/0.46    inference(subsumption_resolution,[],[f371,f211])).
% 0.20/0.46  fof(f371,plain,(
% 0.20/0.46    ~l1_pre_topc(sK3) | ~m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~r2_hidden(sK5,u1_struct_0(sK2)) | v2_struct_0(sK3) | ~v3_pre_topc(u1_struct_0(sK2),sK3) | (~spl9_20 | spl9_31)),
% 0.20/0.46    inference(subsumption_resolution,[],[f370,f203])).
% 0.20/0.46  fof(f370,plain,(
% 0.20/0.46    ~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | ~m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~r2_hidden(sK5,u1_struct_0(sK2)) | v2_struct_0(sK3) | ~v3_pre_topc(u1_struct_0(sK2),sK3) | spl9_31),
% 0.20/0.46    inference(resolution,[],[f358,f60])).
% 0.20/0.46  fof(f60,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (m1_subset_1(sK8(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r2_hidden(X2,X1) | v2_struct_0(X0) | ~v3_pre_topc(X1,X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f22])).
% 0.20/0.46  fof(f358,plain,(
% 0.20/0.46    ~m1_subset_1(sK8(sK3,u1_struct_0(sK2),sK5),k1_zfmisc_1(u1_struct_0(sK3))) | spl9_31),
% 0.20/0.46    inference(avatar_component_clause,[],[f356])).
% 0.20/0.46  fof(f356,plain,(
% 0.20/0.46    spl9_31 <=> m1_subset_1(sK8(sK3,u1_struct_0(sK2),sK5),k1_zfmisc_1(u1_struct_0(sK3)))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl9_31])])).
% 0.20/0.46  fof(f369,plain,(
% 0.20/0.46    spl9_33 | ~spl9_18 | spl9_30),
% 0.20/0.46    inference(avatar_split_clause,[],[f364,f352,f189,f366])).
% 0.20/0.46  fof(f364,plain,(
% 0.20/0.46    v1_xboole_0(u1_struct_0(sK2)) | (~spl9_18 | spl9_30)),
% 0.20/0.46    inference(subsumption_resolution,[],[f363,f191])).
% 0.20/0.46  fof(f363,plain,(
% 0.20/0.46    v1_xboole_0(u1_struct_0(sK2)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | spl9_30),
% 0.20/0.46    inference(resolution,[],[f354,f72])).
% 0.20/0.46  fof(f72,plain,(
% 0.20/0.46    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f34])).
% 0.20/0.46  fof(f34,plain,(
% 0.20/0.46    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.20/0.46    inference(flattening,[],[f33])).
% 0.20/0.46  fof(f33,plain,(
% 0.20/0.46    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.20/0.46    inference(ennf_transformation,[],[f1])).
% 0.20/0.46  fof(f1,axiom,(
% 0.20/0.46    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.20/0.46  fof(f354,plain,(
% 0.20/0.46    ~r2_hidden(sK5,u1_struct_0(sK2)) | spl9_30),
% 0.20/0.46    inference(avatar_component_clause,[],[f352])).
% 0.20/0.46  fof(f362,plain,(
% 0.20/0.46    ~spl9_30 | ~spl9_31 | spl9_32 | ~spl9_1 | spl9_2 | spl9_4 | ~spl9_5 | ~spl9_6 | ~spl9_16 | ~spl9_17 | ~spl9_19 | spl9_23 | ~spl9_29),
% 0.20/0.46    inference(avatar_split_clause,[],[f343,f303,f215,f194,f184,f176,f104,f99,f94,f84,f79,f360,f356,f352])).
% 0.20/0.46  fof(f79,plain,(
% 0.20/0.46    spl9_1 <=> v1_funct_1(sK4)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 0.20/0.46  fof(f94,plain,(
% 0.20/0.46    spl9_4 <=> v2_struct_0(sK1)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).
% 0.20/0.46  fof(f99,plain,(
% 0.20/0.46    spl9_5 <=> v2_pre_topc(sK1)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).
% 0.20/0.46  fof(f104,plain,(
% 0.20/0.46    spl9_6 <=> l1_pre_topc(sK1)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).
% 0.20/0.46  fof(f184,plain,(
% 0.20/0.46    spl9_17 <=> v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl9_17])])).
% 0.20/0.46  fof(f194,plain,(
% 0.20/0.46    spl9_19 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl9_19])])).
% 0.20/0.46  fof(f215,plain,(
% 0.20/0.46    spl9_23 <=> r1_tmap_1(sK3,sK1,sK4,sK5)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl9_23])])).
% 0.20/0.46  fof(f303,plain,(
% 0.20/0.46    spl9_29 <=> ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK3)) | m1_connsp_2(sK8(sK3,u1_struct_0(sK2),X0),sK3,X0) | ~r2_hidden(X0,u1_struct_0(sK2)))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl9_29])])).
% 0.20/0.46  fof(f343,plain,(
% 0.20/0.46    ( ! [X0,X1] : (v2_struct_0(X0) | ~m1_pre_topc(sK3,X1) | v2_struct_0(X1) | ~m1_pre_topc(X0,sK3) | ~m1_subset_1(sK8(sK3,u1_struct_0(sK2),sK5),k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~r1_tarski(sK8(sK3,u1_struct_0(sK2),sK5),u1_struct_0(X0)) | ~l1_pre_topc(X1) | ~r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5) | ~v2_pre_topc(X1) | ~r2_hidden(sK5,u1_struct_0(sK2))) ) | (~spl9_1 | spl9_2 | spl9_4 | ~spl9_5 | ~spl9_6 | ~spl9_16 | ~spl9_17 | ~spl9_19 | spl9_23 | ~spl9_29)),
% 0.20/0.46    inference(subsumption_resolution,[],[f342,f178])).
% 0.20/0.46  fof(f342,plain,(
% 0.20/0.46    ( ! [X0,X1] : (v2_struct_0(X0) | ~m1_pre_topc(sK3,X1) | v2_struct_0(X1) | ~m1_pre_topc(X0,sK3) | ~m1_subset_1(sK8(sK3,u1_struct_0(sK2),sK5),k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~r1_tarski(sK8(sK3,u1_struct_0(sK2),sK5),u1_struct_0(X0)) | ~l1_pre_topc(X1) | ~r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5) | ~v2_pre_topc(X1) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~r2_hidden(sK5,u1_struct_0(sK2))) ) | (~spl9_1 | spl9_2 | spl9_4 | ~spl9_5 | ~spl9_6 | ~spl9_16 | ~spl9_17 | ~spl9_19 | spl9_23 | ~spl9_29)),
% 0.20/0.46    inference(resolution,[],[f341,f304])).
% 0.20/0.46  fof(f304,plain,(
% 0.20/0.46    ( ! [X0] : (m1_connsp_2(sK8(sK3,u1_struct_0(sK2),X0),sK3,X0) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~r2_hidden(X0,u1_struct_0(sK2))) ) | ~spl9_29),
% 0.20/0.46    inference(avatar_component_clause,[],[f303])).
% 0.20/0.46  fof(f341,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (~m1_connsp_2(X2,sK3,sK5) | v2_struct_0(X1) | ~m1_pre_topc(sK3,X0) | v2_struct_0(X0) | ~m1_pre_topc(X1,sK3) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK5,u1_struct_0(X1)) | ~r1_tarski(X2,u1_struct_0(X1)) | ~l1_pre_topc(X0) | ~r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),sK5) | ~v2_pre_topc(X0)) ) | (~spl9_1 | spl9_2 | spl9_4 | ~spl9_5 | ~spl9_6 | ~spl9_16 | ~spl9_17 | ~spl9_19 | spl9_23)),
% 0.20/0.46    inference(subsumption_resolution,[],[f340,f178])).
% 0.20/0.46  fof(f340,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(sK3,X0) | v2_struct_0(X0) | ~m1_pre_topc(X1,sK3) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(X1)) | ~r1_tarski(X2,u1_struct_0(X1)) | ~m1_connsp_2(X2,sK3,sK5) | ~r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),sK5) | ~v2_pre_topc(X0)) ) | (~spl9_1 | spl9_2 | spl9_4 | ~spl9_5 | ~spl9_6 | ~spl9_17 | ~spl9_19 | spl9_23)),
% 0.20/0.46    inference(subsumption_resolution,[],[f339,f196])).
% 0.20/0.46  fof(f196,plain,(
% 0.20/0.46    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~spl9_19),
% 0.20/0.46    inference(avatar_component_clause,[],[f194])).
% 0.20/0.46  fof(f339,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(sK3,X0) | v2_struct_0(X0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(X1,sK3) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(X1)) | ~r1_tarski(X2,u1_struct_0(X1)) | ~m1_connsp_2(X2,sK3,sK5) | ~r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),sK5) | ~v2_pre_topc(X0)) ) | (~spl9_1 | spl9_2 | spl9_4 | ~spl9_5 | ~spl9_6 | ~spl9_17 | spl9_23)),
% 0.20/0.46    inference(subsumption_resolution,[],[f338,f186])).
% 0.20/0.46  fof(f186,plain,(
% 0.20/0.46    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~spl9_17),
% 0.20/0.46    inference(avatar_component_clause,[],[f184])).
% 0.20/0.46  fof(f338,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(sK3,X0) | v2_struct_0(X0) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(X1,sK3) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(X1)) | ~r1_tarski(X2,u1_struct_0(X1)) | ~m1_connsp_2(X2,sK3,sK5) | ~r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),sK5) | ~v2_pre_topc(X0)) ) | (~spl9_1 | spl9_2 | spl9_4 | ~spl9_5 | ~spl9_6 | spl9_23)),
% 0.20/0.46    inference(subsumption_resolution,[],[f337,f86])).
% 0.20/0.46  fof(f337,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | v2_struct_0(X1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,X0) | v2_struct_0(X0) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(X1,sK3) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(X1)) | ~r1_tarski(X2,u1_struct_0(X1)) | ~m1_connsp_2(X2,sK3,sK5) | ~r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),sK5) | ~v2_pre_topc(X0)) ) | (~spl9_1 | spl9_4 | ~spl9_5 | ~spl9_6 | spl9_23)),
% 0.20/0.46    inference(subsumption_resolution,[],[f336,f106])).
% 0.20/0.46  fof(f106,plain,(
% 0.20/0.46    l1_pre_topc(sK1) | ~spl9_6),
% 0.20/0.46    inference(avatar_component_clause,[],[f104])).
% 0.20/0.46  fof(f336,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~l1_pre_topc(sK1) | v2_struct_0(X1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,X0) | v2_struct_0(X0) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(X1,sK3) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(X1)) | ~r1_tarski(X2,u1_struct_0(X1)) | ~m1_connsp_2(X2,sK3,sK5) | ~r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),sK5) | ~v2_pre_topc(X0)) ) | (~spl9_1 | spl9_4 | ~spl9_5 | spl9_23)),
% 0.20/0.46    inference(subsumption_resolution,[],[f335,f101])).
% 0.20/0.46  fof(f101,plain,(
% 0.20/0.46    v2_pre_topc(sK1) | ~spl9_5),
% 0.20/0.46    inference(avatar_component_clause,[],[f99])).
% 0.20/0.46  fof(f335,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(X1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,X0) | v2_struct_0(X0) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(X1,sK3) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(X1)) | ~r1_tarski(X2,u1_struct_0(X1)) | ~m1_connsp_2(X2,sK3,sK5) | ~r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),sK5) | ~v2_pre_topc(X0)) ) | (~spl9_1 | spl9_4 | spl9_23)),
% 0.20/0.46    inference(subsumption_resolution,[],[f334,f96])).
% 0.20/0.46  fof(f96,plain,(
% 0.20/0.46    ~v2_struct_0(sK1) | spl9_4),
% 0.20/0.46    inference(avatar_component_clause,[],[f94])).
% 0.20/0.46  fof(f334,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(X1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,X0) | v2_struct_0(X0) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(X1,sK3) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(X1)) | ~r1_tarski(X2,u1_struct_0(X1)) | ~m1_connsp_2(X2,sK3,sK5) | ~r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),sK5) | ~v2_pre_topc(X0)) ) | (~spl9_1 | spl9_23)),
% 0.20/0.46    inference(resolution,[],[f216,f152])).
% 0.20/0.46  fof(f152,plain,(
% 0.20/0.46    ( ! [X6,X10,X8,X7,X5,X9] : (r1_tmap_1(X8,X6,sK4,X10) | ~l1_pre_topc(X5) | v2_struct_0(X6) | ~v2_pre_topc(X6) | ~l1_pre_topc(X6) | v2_struct_0(X7) | v2_struct_0(X8) | ~m1_pre_topc(X8,X5) | v2_struct_0(X5) | ~v1_funct_2(sK4,u1_struct_0(X8),u1_struct_0(X6)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(X6)))) | ~m1_pre_topc(X7,X8) | ~m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8))) | ~m1_subset_1(X10,u1_struct_0(X8)) | ~m1_subset_1(X10,u1_struct_0(X7)) | ~r1_tarski(X9,u1_struct_0(X7)) | ~m1_connsp_2(X9,X8,X10) | ~r1_tmap_1(X7,X6,k3_tmap_1(X5,X6,X8,X7,sK4),X10) | ~v2_pre_topc(X5)) ) | ~spl9_1),
% 0.20/0.46    inference(subsumption_resolution,[],[f149,f69])).
% 0.20/0.46  fof(f69,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(X2,X1) | ~v2_pre_topc(X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f30])).
% 0.20/0.46  fof(f30,plain,(
% 0.20/0.46    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.46    inference(flattening,[],[f29])).
% 0.20/0.46  fof(f29,plain,(
% 0.20/0.46    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.46    inference(ennf_transformation,[],[f9])).
% 0.20/0.46  fof(f9,axiom,(
% 0.20/0.46    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tsep_1)).
% 0.20/0.46  fof(f149,plain,(
% 0.20/0.46    ( ! [X6,X10,X8,X7,X5,X9] : (~v2_pre_topc(X5) | ~l1_pre_topc(X5) | v2_struct_0(X6) | ~v2_pre_topc(X6) | ~l1_pre_topc(X6) | v2_struct_0(X7) | ~m1_pre_topc(X7,X5) | v2_struct_0(X8) | ~m1_pre_topc(X8,X5) | v2_struct_0(X5) | ~v1_funct_2(sK4,u1_struct_0(X8),u1_struct_0(X6)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(X6)))) | ~m1_pre_topc(X7,X8) | ~m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8))) | ~m1_subset_1(X10,u1_struct_0(X8)) | ~m1_subset_1(X10,u1_struct_0(X7)) | ~r1_tarski(X9,u1_struct_0(X7)) | ~m1_connsp_2(X9,X8,X10) | ~r1_tmap_1(X7,X6,k3_tmap_1(X5,X6,X8,X7,sK4),X10) | r1_tmap_1(X8,X6,sK4,X10)) ) | ~spl9_1),
% 0.20/0.46    inference(resolution,[],[f81,f74])).
% 0.20/0.46  fof(f74,plain,(
% 0.20/0.46    ( ! [X4,X2,X0,X7,X5,X3,X1] : (~v1_funct_1(X4) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X0) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_connsp_2(X5,X3,X7) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X7)) )),
% 0.20/0.46    inference(equality_resolution,[],[f65])).
% 0.20/0.46  fof(f65,plain,(
% 0.20/0.46    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_connsp_2(X5,X3,X6) | X6 != X7 | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f24])).
% 0.20/0.46  fof(f24,plain,(
% 0.20/0.46    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : ((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.46    inference(flattening,[],[f23])).
% 0.20/0.46  fof(f23,plain,(
% 0.20/0.46    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | (X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)))) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.46    inference(ennf_transformation,[],[f11])).
% 0.20/0.46  fof(f11,axiom,(
% 0.20/0.46    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & m1_connsp_2(X5,X3,X6) & r1_tarski(X5,u1_struct_0(X2))) => (r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7))))))))))))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_tmap_1)).
% 0.20/0.46  fof(f81,plain,(
% 0.20/0.46    v1_funct_1(sK4) | ~spl9_1),
% 0.20/0.46    inference(avatar_component_clause,[],[f79])).
% 0.20/0.46  fof(f216,plain,(
% 0.20/0.46    ~r1_tmap_1(sK3,sK1,sK4,sK5) | spl9_23),
% 0.20/0.46    inference(avatar_component_clause,[],[f215])).
% 0.20/0.46  fof(f332,plain,(
% 0.20/0.46    ~spl9_10 | ~spl9_23 | ~spl9_24),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f331])).
% 0.20/0.46  fof(f331,plain,(
% 0.20/0.46    $false | (~spl9_10 | ~spl9_23 | ~spl9_24)),
% 0.20/0.46    inference(subsumption_resolution,[],[f330,f221])).
% 0.20/0.46  fof(f330,plain,(
% 0.20/0.46    ~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) | (~spl9_10 | ~spl9_23)),
% 0.20/0.46    inference(subsumption_resolution,[],[f200,f217])).
% 0.20/0.46  fof(f217,plain,(
% 0.20/0.46    r1_tmap_1(sK3,sK1,sK4,sK5) | ~spl9_23),
% 0.20/0.46    inference(avatar_component_clause,[],[f215])).
% 0.20/0.46  fof(f200,plain,(
% 0.20/0.46    ~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) | ~r1_tmap_1(sK3,sK1,sK4,sK5) | ~spl9_10),
% 0.20/0.46    inference(forward_demodulation,[],[f36,f126])).
% 0.20/0.46  fof(f126,plain,(
% 0.20/0.46    sK5 = sK6 | ~spl9_10),
% 0.20/0.46    inference(avatar_component_clause,[],[f124])).
% 0.20/0.46  fof(f124,plain,(
% 0.20/0.46    spl9_10 <=> sK5 = sK6),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).
% 0.20/0.46  fof(f36,plain,(
% 0.20/0.46    ~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) | ~r1_tmap_1(sK3,sK1,sK4,sK5)),
% 0.20/0.46    inference(cnf_transformation,[],[f15])).
% 0.20/0.46  fof(f15,plain,(
% 0.20/0.46    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((r1_tmap_1(X3,X1,X4,X5) <~> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.46    inference(flattening,[],[f14])).
% 0.20/0.46  fof(f14,plain,(
% 0.20/0.46    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : (((r1_tmap_1(X3,X1,X4,X5) <~> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) & X5 = X6) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & (m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.46    inference(ennf_transformation,[],[f13])).
% 0.20/0.46  fof(f13,negated_conjecture,(
% 0.20/0.46    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => ((m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (X5 = X6 => (r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)))))))))))),
% 0.20/0.46    inference(negated_conjecture,[],[f12])).
% 0.20/0.46  fof(f12,conjecture,(
% 0.20/0.46    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => ((m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (X5 = X6 => (r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)))))))))))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_tmap_1)).
% 0.20/0.46  fof(f329,plain,(
% 0.20/0.46    ~spl9_1 | spl9_2 | spl9_3 | spl9_4 | ~spl9_5 | ~spl9_6 | spl9_7 | ~spl9_8 | ~spl9_9 | ~spl9_12 | ~spl9_13 | ~spl9_16 | ~spl9_17 | ~spl9_18 | ~spl9_19 | ~spl9_23 | spl9_24),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f328])).
% 0.20/0.46  fof(f328,plain,(
% 0.20/0.46    $false | (~spl9_1 | spl9_2 | spl9_3 | spl9_4 | ~spl9_5 | ~spl9_6 | spl9_7 | ~spl9_8 | ~spl9_9 | ~spl9_12 | ~spl9_13 | ~spl9_16 | ~spl9_17 | ~spl9_18 | ~spl9_19 | ~spl9_23 | spl9_24)),
% 0.20/0.46    inference(subsumption_resolution,[],[f327,f121])).
% 0.20/0.46  fof(f327,plain,(
% 0.20/0.46    ~l1_pre_topc(sK0) | (~spl9_1 | spl9_2 | spl9_3 | spl9_4 | ~spl9_5 | ~spl9_6 | spl9_7 | ~spl9_8 | ~spl9_12 | ~spl9_13 | ~spl9_16 | ~spl9_17 | ~spl9_18 | ~spl9_19 | ~spl9_23 | spl9_24)),
% 0.20/0.46    inference(subsumption_resolution,[],[f326,f217])).
% 0.20/0.46  fof(f326,plain,(
% 0.20/0.46    ~r1_tmap_1(sK3,sK1,sK4,sK5) | ~l1_pre_topc(sK0) | (~spl9_1 | spl9_2 | spl9_3 | spl9_4 | ~spl9_5 | ~spl9_6 | spl9_7 | ~spl9_8 | ~spl9_12 | ~spl9_13 | ~spl9_16 | ~spl9_17 | ~spl9_18 | ~spl9_19 | spl9_24)),
% 0.20/0.46    inference(subsumption_resolution,[],[f325,f136])).
% 0.20/0.46  fof(f325,plain,(
% 0.20/0.46    ~m1_pre_topc(sK2,sK3) | ~r1_tmap_1(sK3,sK1,sK4,sK5) | ~l1_pre_topc(sK0) | (~spl9_1 | spl9_2 | spl9_3 | spl9_4 | ~spl9_5 | ~spl9_6 | spl9_7 | ~spl9_8 | ~spl9_13 | ~spl9_16 | ~spl9_17 | ~spl9_18 | ~spl9_19 | spl9_24)),
% 0.20/0.46    inference(subsumption_resolution,[],[f324,f191])).
% 0.20/0.46  fof(f324,plain,(
% 0.20/0.46    ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~m1_pre_topc(sK2,sK3) | ~r1_tmap_1(sK3,sK1,sK4,sK5) | ~l1_pre_topc(sK0) | (~spl9_1 | spl9_2 | spl9_3 | spl9_4 | ~spl9_5 | ~spl9_6 | spl9_7 | ~spl9_8 | ~spl9_13 | ~spl9_16 | ~spl9_17 | ~spl9_19 | spl9_24)),
% 0.20/0.46    inference(subsumption_resolution,[],[f323,f178])).
% 0.20/0.46  fof(f323,plain,(
% 0.20/0.46    ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~m1_pre_topc(sK2,sK3) | ~r1_tmap_1(sK3,sK1,sK4,sK5) | ~l1_pre_topc(sK0) | (~spl9_1 | spl9_2 | spl9_3 | spl9_4 | ~spl9_5 | ~spl9_6 | spl9_7 | ~spl9_8 | ~spl9_13 | ~spl9_17 | ~spl9_19 | spl9_24)),
% 0.20/0.46    inference(subsumption_resolution,[],[f322,f116])).
% 0.20/0.46  fof(f322,plain,(
% 0.20/0.46    ~v2_pre_topc(sK0) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~m1_pre_topc(sK2,sK3) | ~r1_tmap_1(sK3,sK1,sK4,sK5) | ~l1_pre_topc(sK0) | (~spl9_1 | spl9_2 | spl9_3 | spl9_4 | ~spl9_5 | ~spl9_6 | spl9_7 | ~spl9_13 | ~spl9_17 | ~spl9_19 | spl9_24)),
% 0.20/0.46    inference(subsumption_resolution,[],[f321,f111])).
% 0.20/0.46  fof(f321,plain,(
% 0.20/0.46    v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~m1_pre_topc(sK2,sK3) | ~r1_tmap_1(sK3,sK1,sK4,sK5) | ~l1_pre_topc(sK0) | (~spl9_1 | spl9_2 | spl9_3 | spl9_4 | ~spl9_5 | ~spl9_6 | ~spl9_13 | ~spl9_17 | ~spl9_19 | spl9_24)),
% 0.20/0.46    inference(subsumption_resolution,[],[f320,f91])).
% 0.20/0.46  fof(f320,plain,(
% 0.20/0.46    v2_struct_0(sK2) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~m1_pre_topc(sK2,sK3) | ~r1_tmap_1(sK3,sK1,sK4,sK5) | ~l1_pre_topc(sK0) | (~spl9_1 | spl9_2 | spl9_4 | ~spl9_5 | ~spl9_6 | ~spl9_13 | ~spl9_17 | ~spl9_19 | spl9_24)),
% 0.20/0.46    inference(subsumption_resolution,[],[f319,f141])).
% 0.20/0.46  fof(f319,plain,(
% 0.20/0.46    ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK2) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~m1_pre_topc(sK2,sK3) | ~r1_tmap_1(sK3,sK1,sK4,sK5) | ~l1_pre_topc(sK0) | (~spl9_1 | spl9_2 | spl9_4 | ~spl9_5 | ~spl9_6 | ~spl9_17 | ~spl9_19 | spl9_24)),
% 0.20/0.46    inference(resolution,[],[f317,f220])).
% 0.20/0.46  fof(f220,plain,(
% 0.20/0.46    ~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) | spl9_24),
% 0.20/0.46    inference(avatar_component_clause,[],[f219])).
% 0.20/0.46  fof(f317,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),X2) | ~m1_pre_topc(sK3,X0) | v2_struct_0(X1) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~m1_pre_topc(X1,sK3) | ~r1_tmap_1(sK3,sK1,sK4,X2) | ~l1_pre_topc(X0)) ) | (~spl9_1 | spl9_2 | spl9_4 | ~spl9_5 | ~spl9_6 | ~spl9_17 | ~spl9_19)),
% 0.20/0.46    inference(subsumption_resolution,[],[f316,f196])).
% 0.20/0.46  fof(f316,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(sK3,X0) | v2_struct_0(X1) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~m1_pre_topc(X1,sK3) | ~r1_tmap_1(sK3,sK1,sK4,X2) | r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),X2)) ) | (~spl9_1 | spl9_2 | spl9_4 | ~spl9_5 | ~spl9_6 | ~spl9_17)),
% 0.20/0.46    inference(subsumption_resolution,[],[f315,f86])).
% 0.20/0.46  fof(f315,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,X0) | v2_struct_0(X1) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~m1_pre_topc(X1,sK3) | ~r1_tmap_1(sK3,sK1,sK4,X2) | r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),X2)) ) | (~spl9_1 | spl9_4 | ~spl9_5 | ~spl9_6 | ~spl9_17)),
% 0.20/0.46    inference(subsumption_resolution,[],[f314,f106])).
% 0.20/0.46  fof(f314,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~l1_pre_topc(sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,X0) | v2_struct_0(X1) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~m1_pre_topc(X1,sK3) | ~r1_tmap_1(sK3,sK1,sK4,X2) | r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),X2)) ) | (~spl9_1 | spl9_4 | ~spl9_5 | ~spl9_17)),
% 0.20/0.46    inference(subsumption_resolution,[],[f313,f101])).
% 0.20/0.46  fof(f313,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,X0) | v2_struct_0(X1) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~m1_pre_topc(X1,sK3) | ~r1_tmap_1(sK3,sK1,sK4,X2) | r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),X2)) ) | (~spl9_1 | spl9_4 | ~spl9_17)),
% 0.20/0.46    inference(subsumption_resolution,[],[f312,f96])).
% 0.20/0.46  fof(f312,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,X0) | v2_struct_0(X1) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~m1_pre_topc(X1,sK3) | ~r1_tmap_1(sK3,sK1,sK4,X2) | r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),X2)) ) | (~spl9_1 | ~spl9_17)),
% 0.20/0.46    inference(resolution,[],[f151,f186])).
% 0.20/0.46  fof(f151,plain,(
% 0.20/0.46    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_2(sK4,u1_struct_0(X2),u1_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~m1_subset_1(X4,u1_struct_0(X2)) | ~m1_subset_1(X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2) | ~r1_tmap_1(X2,X1,sK4,X4) | r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,sK4),X4)) ) | ~spl9_1),
% 0.20/0.46    inference(subsumption_resolution,[],[f148,f69])).
% 0.20/0.46  fof(f148,plain,(
% 0.20/0.46    ( ! [X4,X2,X0,X3,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X0) | ~v1_funct_2(sK4,u1_struct_0(X2),u1_struct_0(X1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~m1_subset_1(X4,u1_struct_0(X2)) | ~m1_subset_1(X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2) | ~r1_tmap_1(X2,X1,sK4,X4) | r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,sK4),X4)) ) | ~spl9_1),
% 0.20/0.46    inference(resolution,[],[f81,f75])).
% 0.20/0.46  fof(f75,plain,(
% 0.20/0.46    ( ! [X6,X4,X2,X0,X3,X1] : (~v1_funct_1(X4) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X0) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2) | ~r1_tmap_1(X2,X1,X4,X6) | r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)) )),
% 0.20/0.46    inference(equality_resolution,[],[f67])).
% 0.20/0.46  fof(f67,plain,(
% 0.20/0.46    ( ! [X6,X4,X2,X0,X5,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~m1_subset_1(X5,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | X5 != X6 | ~m1_pre_topc(X3,X2) | ~r1_tmap_1(X2,X1,X4,X5) | r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f26])).
% 0.20/0.46  fof(f26,plain,(
% 0.20/0.46    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | ~r1_tmap_1(X2,X1,X4,X5) | ~m1_pre_topc(X3,X2) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X2))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.46    inference(flattening,[],[f25])).
% 0.20/0.46  fof(f25,plain,(
% 0.20/0.46    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | (~r1_tmap_1(X2,X1,X4,X5) | ~m1_pre_topc(X3,X2) | X5 != X6)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X2))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.46    inference(ennf_transformation,[],[f10])).
% 0.20/0.46  fof(f10,axiom,(
% 0.20/0.46    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X2)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((r1_tmap_1(X2,X1,X4,X5) & m1_pre_topc(X3,X2) & X5 = X6) => r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)))))))))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_tmap_1)).
% 0.20/0.46  fof(f311,plain,(
% 0.20/0.46    ~spl9_12 | ~spl9_22 | spl9_28),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f310])).
% 0.20/0.46  fof(f310,plain,(
% 0.20/0.46    $false | (~spl9_12 | ~spl9_22 | spl9_28)),
% 0.20/0.46    inference(subsumption_resolution,[],[f309,f211])).
% 0.20/0.46  fof(f309,plain,(
% 0.20/0.46    ~l1_pre_topc(sK3) | (~spl9_12 | spl9_28)),
% 0.20/0.46    inference(subsumption_resolution,[],[f308,f136])).
% 0.20/0.46  fof(f308,plain,(
% 0.20/0.46    ~m1_pre_topc(sK2,sK3) | ~l1_pre_topc(sK3) | spl9_28),
% 0.20/0.46    inference(resolution,[],[f301,f57])).
% 0.20/0.46  fof(f57,plain,(
% 0.20/0.46    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f18])).
% 0.20/0.46  fof(f18,plain,(
% 0.20/0.46    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.46    inference(ennf_transformation,[],[f8])).
% 0.20/0.46  fof(f8,axiom,(
% 0.20/0.46    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).
% 0.20/0.46  fof(f301,plain,(
% 0.20/0.46    ~m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3))) | spl9_28),
% 0.20/0.46    inference(avatar_component_clause,[],[f299])).
% 0.20/0.46  fof(f305,plain,(
% 0.20/0.46    ~spl9_28 | spl9_29 | spl9_2 | ~spl9_20 | ~spl9_21 | ~spl9_22),
% 0.20/0.46    inference(avatar_split_clause,[],[f287,f210,f206,f202,f84,f303,f299])).
% 0.20/0.46  fof(f287,plain,(
% 0.20/0.46    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK3)) | ~r2_hidden(X0,u1_struct_0(sK2)) | m1_connsp_2(sK8(sK3,u1_struct_0(sK2),X0),sK3,X0) | ~m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))) ) | (spl9_2 | ~spl9_20 | ~spl9_21 | ~spl9_22)),
% 0.20/0.46    inference(resolution,[],[f286,f208])).
% 0.20/0.46  fof(f286,plain,(
% 0.20/0.46    ( ! [X2,X3] : (~v3_pre_topc(X2,sK3) | ~m1_subset_1(X3,u1_struct_0(sK3)) | ~r2_hidden(X3,X2) | m1_connsp_2(sK8(sK3,X2,X3),sK3,X3) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))) ) | (spl9_2 | ~spl9_20 | ~spl9_22)),
% 0.20/0.46    inference(subsumption_resolution,[],[f285,f211])).
% 0.20/0.46  fof(f285,plain,(
% 0.20/0.46    ( ! [X2,X3] : (~l1_pre_topc(sK3) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(X3,u1_struct_0(sK3)) | ~r2_hidden(X3,X2) | m1_connsp_2(sK8(sK3,X2,X3),sK3,X3) | ~v3_pre_topc(X2,sK3)) ) | (spl9_2 | ~spl9_20)),
% 0.20/0.46    inference(subsumption_resolution,[],[f155,f203])).
% 0.20/0.46  fof(f155,plain,(
% 0.20/0.46    ( ! [X2,X3] : (~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(X3,u1_struct_0(sK3)) | ~r2_hidden(X3,X2) | m1_connsp_2(sK8(sK3,X2,X3),sK3,X3) | ~v3_pre_topc(X2,sK3)) ) | spl9_2),
% 0.20/0.46    inference(resolution,[],[f86,f61])).
% 0.20/0.46  fof(f61,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r2_hidden(X2,X1) | m1_connsp_2(sK8(X0,X1,X2),X0,X2) | ~v3_pre_topc(X1,X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f22])).
% 0.20/0.46  fof(f262,plain,(
% 0.20/0.46    ~spl9_9 | ~spl9_14 | spl9_26),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f261])).
% 0.20/0.46  fof(f261,plain,(
% 0.20/0.46    $false | (~spl9_9 | ~spl9_14 | spl9_26)),
% 0.20/0.46    inference(subsumption_resolution,[],[f256,f121])).
% 0.20/0.46  fof(f256,plain,(
% 0.20/0.46    ~l1_pre_topc(sK0) | (~spl9_14 | spl9_26)),
% 0.20/0.46    inference(resolution,[],[f251,f146])).
% 0.20/0.46  fof(f146,plain,(
% 0.20/0.46    m1_pre_topc(sK2,sK0) | ~spl9_14),
% 0.20/0.46    inference(avatar_component_clause,[],[f144])).
% 0.20/0.46  fof(f144,plain,(
% 0.20/0.46    spl9_14 <=> m1_pre_topc(sK2,sK0)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).
% 0.20/0.46  fof(f251,plain,(
% 0.20/0.46    ( ! [X0] : (~m1_pre_topc(sK2,X0) | ~l1_pre_topc(X0)) ) | spl9_26),
% 0.20/0.46    inference(resolution,[],[f245,f56])).
% 0.20/0.46  fof(f56,plain,(
% 0.20/0.46    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f17])).
% 0.20/0.46  fof(f17,plain,(
% 0.20/0.46    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.46    inference(ennf_transformation,[],[f4])).
% 0.20/0.46  fof(f4,axiom,(
% 0.20/0.46    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.20/0.46  fof(f245,plain,(
% 0.20/0.46    ~l1_pre_topc(sK2) | spl9_26),
% 0.20/0.46    inference(avatar_component_clause,[],[f243])).
% 0.20/0.46  fof(f235,plain,(
% 0.20/0.46    ~spl9_8 | ~spl9_9 | ~spl9_13 | spl9_20),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f234])).
% 0.20/0.46  fof(f234,plain,(
% 0.20/0.46    $false | (~spl9_8 | ~spl9_9 | ~spl9_13 | spl9_20)),
% 0.20/0.46    inference(subsumption_resolution,[],[f233,f116])).
% 0.20/0.46  fof(f233,plain,(
% 0.20/0.46    ~v2_pre_topc(sK0) | (~spl9_9 | ~spl9_13 | spl9_20)),
% 0.20/0.46    inference(subsumption_resolution,[],[f230,f121])).
% 0.20/0.46  fof(f230,plain,(
% 0.20/0.46    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl9_13 | spl9_20)),
% 0.20/0.46    inference(resolution,[],[f223,f141])).
% 0.20/0.46  fof(f223,plain,(
% 0.20/0.46    ( ! [X0] : (~m1_pre_topc(sK3,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | spl9_20),
% 0.20/0.46    inference(resolution,[],[f204,f68])).
% 0.20/0.46  fof(f68,plain,(
% 0.20/0.46    ( ! [X0,X1] : (v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f28])).
% 0.20/0.46  fof(f28,plain,(
% 0.20/0.46    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.46    inference(flattening,[],[f27])).
% 0.20/0.46  fof(f27,plain,(
% 0.20/0.46    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.46    inference(ennf_transformation,[],[f2])).
% 0.20/0.46  fof(f2,axiom,(
% 0.20/0.46    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).
% 0.20/0.46  fof(f204,plain,(
% 0.20/0.46    ~v2_pre_topc(sK3) | spl9_20),
% 0.20/0.46    inference(avatar_component_clause,[],[f202])).
% 0.20/0.46  fof(f229,plain,(
% 0.20/0.46    ~spl9_9 | ~spl9_13 | spl9_22),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f228])).
% 0.20/0.46  fof(f228,plain,(
% 0.20/0.46    $false | (~spl9_9 | ~spl9_13 | spl9_22)),
% 0.20/0.46    inference(subsumption_resolution,[],[f225,f121])).
% 0.20/0.46  fof(f225,plain,(
% 0.20/0.46    ~l1_pre_topc(sK0) | (~spl9_13 | spl9_22)),
% 0.20/0.46    inference(resolution,[],[f224,f141])).
% 0.20/0.46  fof(f224,plain,(
% 0.20/0.46    ( ! [X0] : (~m1_pre_topc(sK3,X0) | ~l1_pre_topc(X0)) ) | spl9_22),
% 0.20/0.46    inference(resolution,[],[f212,f56])).
% 0.20/0.46  fof(f212,plain,(
% 0.20/0.46    ~l1_pre_topc(sK3) | spl9_22),
% 0.20/0.46    inference(avatar_component_clause,[],[f210])).
% 0.20/0.46  fof(f222,plain,(
% 0.20/0.46    spl9_23 | spl9_24 | ~spl9_10),
% 0.20/0.46    inference(avatar_split_clause,[],[f198,f124,f219,f215])).
% 0.20/0.46  fof(f198,plain,(
% 0.20/0.46    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) | r1_tmap_1(sK3,sK1,sK4,sK5) | ~spl9_10),
% 0.20/0.46    inference(forward_demodulation,[],[f35,f126])).
% 0.20/0.46  fof(f35,plain,(
% 0.20/0.46    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) | r1_tmap_1(sK3,sK1,sK4,sK5)),
% 0.20/0.46    inference(cnf_transformation,[],[f15])).
% 0.20/0.46  fof(f213,plain,(
% 0.20/0.46    ~spl9_20 | spl9_21 | ~spl9_22 | ~spl9_11 | ~spl9_12),
% 0.20/0.46    inference(avatar_split_clause,[],[f199,f134,f129,f210,f206,f202])).
% 0.20/0.46  fof(f129,plain,(
% 0.20/0.46    spl9_11 <=> v1_tsep_1(sK2,sK3)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).
% 0.20/0.46  fof(f199,plain,(
% 0.20/0.46    ~l1_pre_topc(sK3) | v3_pre_topc(u1_struct_0(sK2),sK3) | ~v2_pre_topc(sK3) | (~spl9_11 | ~spl9_12)),
% 0.20/0.46    inference(subsumption_resolution,[],[f181,f136])).
% 0.20/0.46  fof(f181,plain,(
% 0.20/0.46    ~l1_pre_topc(sK3) | v3_pre_topc(u1_struct_0(sK2),sK3) | ~v2_pre_topc(sK3) | ~m1_pre_topc(sK2,sK3) | ~spl9_11),
% 0.20/0.46    inference(subsumption_resolution,[],[f180,f57])).
% 0.20/0.46  fof(f180,plain,(
% 0.20/0.46    ~l1_pre_topc(sK3) | ~m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3))) | v3_pre_topc(u1_struct_0(sK2),sK3) | ~v2_pre_topc(sK3) | ~m1_pre_topc(sK2,sK3) | ~spl9_11),
% 0.20/0.46    inference(resolution,[],[f131,f77])).
% 0.20/0.46  fof(f77,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~v1_tsep_1(X1,X0) | ~l1_pre_topc(X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(u1_struct_0(X1),X0) | ~v2_pre_topc(X0) | ~m1_pre_topc(X1,X0)) )),
% 0.20/0.46    inference(equality_resolution,[],[f70])).
% 0.20/0.46  fof(f70,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(X1) != X2 | v3_pre_topc(X2,X0) | ~v1_tsep_1(X1,X0) | ~m1_pre_topc(X1,X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f32])).
% 0.20/0.46  fof(f32,plain,(
% 0.20/0.46    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.46    inference(flattening,[],[f31])).
% 0.20/0.46  fof(f31,plain,(
% 0.20/0.46    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.46    inference(ennf_transformation,[],[f7])).
% 0.20/0.46  fof(f7,axiom,(
% 0.20/0.46    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_tsep_1)).
% 0.20/0.46  fof(f131,plain,(
% 0.20/0.46    v1_tsep_1(sK2,sK3) | ~spl9_11),
% 0.20/0.46    inference(avatar_component_clause,[],[f129])).
% 0.20/0.46  fof(f197,plain,(
% 0.20/0.46    spl9_19),
% 0.20/0.46    inference(avatar_split_clause,[],[f42,f194])).
% 0.20/0.46  fof(f42,plain,(
% 0.20/0.46    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 0.20/0.46    inference(cnf_transformation,[],[f15])).
% 0.20/0.46  fof(f192,plain,(
% 0.20/0.46    spl9_18 | ~spl9_10 | ~spl9_15),
% 0.20/0.46    inference(avatar_split_clause,[],[f182,f171,f124,f189])).
% 0.20/0.46  fof(f171,plain,(
% 0.20/0.46    spl9_15 <=> m1_subset_1(sK6,u1_struct_0(sK2))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).
% 0.20/0.46  fof(f182,plain,(
% 0.20/0.46    m1_subset_1(sK5,u1_struct_0(sK2)) | (~spl9_10 | ~spl9_15)),
% 0.20/0.46    inference(forward_demodulation,[],[f173,f126])).
% 0.20/0.46  fof(f173,plain,(
% 0.20/0.46    m1_subset_1(sK6,u1_struct_0(sK2)) | ~spl9_15),
% 0.20/0.46    inference(avatar_component_clause,[],[f171])).
% 0.20/0.46  fof(f187,plain,(
% 0.20/0.46    spl9_17),
% 0.20/0.46    inference(avatar_split_clause,[],[f41,f184])).
% 0.20/0.46  fof(f41,plain,(
% 0.20/0.46    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))),
% 0.20/0.46    inference(cnf_transformation,[],[f15])).
% 0.20/0.46  fof(f179,plain,(
% 0.20/0.46    spl9_16),
% 0.20/0.46    inference(avatar_split_clause,[],[f39,f176])).
% 0.20/0.46  fof(f39,plain,(
% 0.20/0.46    m1_subset_1(sK5,u1_struct_0(sK3))),
% 0.20/0.46    inference(cnf_transformation,[],[f15])).
% 0.20/0.46  fof(f174,plain,(
% 0.20/0.46    spl9_15),
% 0.20/0.46    inference(avatar_split_clause,[],[f37,f171])).
% 0.20/0.46  fof(f37,plain,(
% 0.20/0.46    m1_subset_1(sK6,u1_struct_0(sK2))),
% 0.20/0.46    inference(cnf_transformation,[],[f15])).
% 0.20/0.46  fof(f147,plain,(
% 0.20/0.46    spl9_14),
% 0.20/0.46    inference(avatar_split_clause,[],[f48,f144])).
% 0.20/0.46  fof(f48,plain,(
% 0.20/0.46    m1_pre_topc(sK2,sK0)),
% 0.20/0.46    inference(cnf_transformation,[],[f15])).
% 0.20/0.46  fof(f142,plain,(
% 0.20/0.46    spl9_13),
% 0.20/0.46    inference(avatar_split_clause,[],[f46,f139])).
% 0.20/0.46  fof(f46,plain,(
% 0.20/0.46    m1_pre_topc(sK3,sK0)),
% 0.20/0.46    inference(cnf_transformation,[],[f15])).
% 0.20/0.46  fof(f137,plain,(
% 0.20/0.46    spl9_12),
% 0.20/0.46    inference(avatar_split_clause,[],[f44,f134])).
% 0.20/0.46  fof(f44,plain,(
% 0.20/0.46    m1_pre_topc(sK2,sK3)),
% 0.20/0.46    inference(cnf_transformation,[],[f15])).
% 0.20/0.46  fof(f132,plain,(
% 0.20/0.46    spl9_11),
% 0.20/0.46    inference(avatar_split_clause,[],[f43,f129])).
% 0.20/0.46  fof(f43,plain,(
% 0.20/0.46    v1_tsep_1(sK2,sK3)),
% 0.20/0.46    inference(cnf_transformation,[],[f15])).
% 0.20/0.46  fof(f127,plain,(
% 0.20/0.46    spl9_10),
% 0.20/0.46    inference(avatar_split_clause,[],[f38,f124])).
% 0.20/0.46  fof(f38,plain,(
% 0.20/0.46    sK5 = sK6),
% 0.20/0.46    inference(cnf_transformation,[],[f15])).
% 0.20/0.46  fof(f122,plain,(
% 0.20/0.46    spl9_9),
% 0.20/0.46    inference(avatar_split_clause,[],[f54,f119])).
% 0.20/0.46  fof(f54,plain,(
% 0.20/0.46    l1_pre_topc(sK0)),
% 0.20/0.46    inference(cnf_transformation,[],[f15])).
% 0.20/0.46  fof(f117,plain,(
% 0.20/0.46    spl9_8),
% 0.20/0.46    inference(avatar_split_clause,[],[f53,f114])).
% 0.20/0.46  fof(f53,plain,(
% 0.20/0.46    v2_pre_topc(sK0)),
% 0.20/0.46    inference(cnf_transformation,[],[f15])).
% 0.20/0.46  fof(f112,plain,(
% 0.20/0.46    ~spl9_7),
% 0.20/0.46    inference(avatar_split_clause,[],[f52,f109])).
% 0.20/0.46  fof(f52,plain,(
% 0.20/0.46    ~v2_struct_0(sK0)),
% 0.20/0.46    inference(cnf_transformation,[],[f15])).
% 0.20/0.46  fof(f107,plain,(
% 0.20/0.46    spl9_6),
% 0.20/0.46    inference(avatar_split_clause,[],[f51,f104])).
% 0.20/0.46  fof(f51,plain,(
% 0.20/0.46    l1_pre_topc(sK1)),
% 0.20/0.46    inference(cnf_transformation,[],[f15])).
% 0.20/0.46  fof(f102,plain,(
% 0.20/0.46    spl9_5),
% 0.20/0.46    inference(avatar_split_clause,[],[f50,f99])).
% 0.20/0.46  fof(f50,plain,(
% 0.20/0.46    v2_pre_topc(sK1)),
% 0.20/0.46    inference(cnf_transformation,[],[f15])).
% 0.20/0.46  fof(f97,plain,(
% 0.20/0.46    ~spl9_4),
% 0.20/0.46    inference(avatar_split_clause,[],[f49,f94])).
% 0.20/0.46  fof(f49,plain,(
% 0.20/0.46    ~v2_struct_0(sK1)),
% 0.20/0.46    inference(cnf_transformation,[],[f15])).
% 0.20/0.46  fof(f92,plain,(
% 0.20/0.46    ~spl9_3),
% 0.20/0.46    inference(avatar_split_clause,[],[f47,f89])).
% 0.20/0.46  fof(f47,plain,(
% 0.20/0.46    ~v2_struct_0(sK2)),
% 0.20/0.46    inference(cnf_transformation,[],[f15])).
% 0.20/0.46  fof(f87,plain,(
% 0.20/0.46    ~spl9_2),
% 0.20/0.46    inference(avatar_split_clause,[],[f45,f84])).
% 0.20/0.46  fof(f45,plain,(
% 0.20/0.46    ~v2_struct_0(sK3)),
% 0.20/0.46    inference(cnf_transformation,[],[f15])).
% 0.20/0.46  fof(f82,plain,(
% 0.20/0.46    spl9_1),
% 0.20/0.46    inference(avatar_split_clause,[],[f40,f79])).
% 0.20/0.46  fof(f40,plain,(
% 0.20/0.46    v1_funct_1(sK4)),
% 0.20/0.46    inference(cnf_transformation,[],[f15])).
% 0.20/0.46  % SZS output end Proof for theBenchmark
% 0.20/0.46  % (23175)------------------------------
% 0.20/0.46  % (23175)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (23175)Termination reason: Refutation
% 0.20/0.46  
% 0.20/0.46  % (23175)Memory used [KB]: 10874
% 0.20/0.46  % (23175)Time elapsed: 0.065 s
% 0.20/0.46  % (23175)------------------------------
% 0.20/0.46  % (23175)------------------------------
% 0.20/0.47  % (23171)Success in time 0.112 s
%------------------------------------------------------------------------------
