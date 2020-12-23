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
% DateTime   : Thu Dec  3 13:18:56 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  260 ( 501 expanded)
%              Number of leaves         :   44 ( 173 expanded)
%              Depth                    :   24
%              Number of atoms          : 1737 (3665 expanded)
%              Number of equality atoms :   19 ( 102 expanded)
%              Maximal formula depth    :   31 (   8 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f425,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f84,f89,f94,f99,f104,f109,f114,f119,f124,f129,f134,f139,f144,f149,f176,f181,f189,f194,f199,f215,f224,f231,f237,f264,f307,f314,f332,f335,f360,f367,f377,f389,f401,f424])).

fof(f424,plain,
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
    inference(avatar_contradiction_clause,[],[f423])).

fof(f423,plain,
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
    inference(subsumption_resolution,[],[f422,f113])).

fof(f113,plain,
    ( ~ v2_struct_0(sK0)
    | spl9_7 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl9_7
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f422,plain,
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
    inference(subsumption_resolution,[],[f421,f123])).

fof(f123,plain,
    ( l1_pre_topc(sK0)
    | ~ spl9_9 ),
    inference(avatar_component_clause,[],[f121])).

fof(f121,plain,
    ( spl9_9
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).

fof(f421,plain,
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
    inference(subsumption_resolution,[],[f420,f143])).

fof(f143,plain,
    ( m1_pre_topc(sK3,sK0)
    | ~ spl9_13 ),
    inference(avatar_component_clause,[],[f141])).

fof(f141,plain,
    ( spl9_13
  <=> m1_pre_topc(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).

fof(f420,plain,
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
    inference(subsumption_resolution,[],[f417,f118])).

fof(f118,plain,
    ( v2_pre_topc(sK0)
    | ~ spl9_8 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl9_8
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f417,plain,
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
    inference(resolution,[],[f409,f223])).

fof(f223,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)
    | ~ spl9_24 ),
    inference(avatar_component_clause,[],[f221])).

fof(f221,plain,
    ( spl9_24
  <=> r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_24])])).

fof(f409,plain,
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
    inference(subsumption_resolution,[],[f408,f210])).

fof(f210,plain,
    ( v3_pre_topc(u1_struct_0(sK2),sK3)
    | ~ spl9_21 ),
    inference(avatar_component_clause,[],[f208])).

fof(f208,plain,
    ( spl9_21
  <=> v3_pre_topc(u1_struct_0(sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_21])])).

fof(f408,plain,
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
    inference(subsumption_resolution,[],[f407,f302])).

fof(f302,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl9_28 ),
    inference(avatar_component_clause,[],[f301])).

fof(f301,plain,
    ( spl9_28
  <=> m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_28])])).

fof(f407,plain,
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
    inference(subsumption_resolution,[],[f406,f351])).

fof(f351,plain,
    ( r2_hidden(sK5,u1_struct_0(sK2))
    | ~ spl9_30 ),
    inference(avatar_component_clause,[],[f350])).

fof(f350,plain,
    ( spl9_30
  <=> r2_hidden(sK5,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_30])])).

fof(f406,plain,
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
    inference(subsumption_resolution,[],[f405,f180])).

fof(f180,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ spl9_16 ),
    inference(avatar_component_clause,[],[f178])).

fof(f178,plain,
    ( spl9_16
  <=> m1_subset_1(sK5,u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).

fof(f405,plain,
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
    inference(subsumption_resolution,[],[f404,f138])).

fof(f138,plain,
    ( m1_pre_topc(sK2,sK3)
    | ~ spl9_12 ),
    inference(avatar_component_clause,[],[f136])).

fof(f136,plain,
    ( spl9_12
  <=> m1_pre_topc(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).

fof(f404,plain,
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
    inference(subsumption_resolution,[],[f403,f193])).

fof(f193,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ spl9_18 ),
    inference(avatar_component_clause,[],[f191])).

fof(f191,plain,
    ( spl9_18
  <=> m1_subset_1(sK5,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).

fof(f403,plain,
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
    inference(subsumption_resolution,[],[f402,f93])).

fof(f93,plain,
    ( ~ v2_struct_0(sK2)
    | spl9_3 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl9_3
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f402,plain,
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
    inference(resolution,[],[f359,f278])).

fof(f278,plain,
    ( ! [X4,X5] :
        ( r1_tarski(sK8(sK3,X4,X5),X4)
        | ~ m1_subset_1(X5,u1_struct_0(sK3))
        | ~ r2_hidden(X5,X4)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ v3_pre_topc(X4,sK3) )
    | spl9_2
    | ~ spl9_20
    | ~ spl9_22 ),
    inference(subsumption_resolution,[],[f277,f213])).

fof(f213,plain,
    ( l1_pre_topc(sK3)
    | ~ spl9_22 ),
    inference(avatar_component_clause,[],[f212])).

fof(f212,plain,
    ( spl9_22
  <=> l1_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_22])])).

fof(f277,plain,
    ( ! [X4,X5] :
        ( ~ l1_pre_topc(sK3)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_subset_1(X5,u1_struct_0(sK3))
        | ~ r2_hidden(X5,X4)
        | r1_tarski(sK8(sK3,X4,X5),X4)
        | ~ v3_pre_topc(X4,sK3) )
    | spl9_2
    | ~ spl9_20 ),
    inference(subsumption_resolution,[],[f158,f205])).

fof(f205,plain,
    ( v2_pre_topc(sK3)
    | ~ spl9_20 ),
    inference(avatar_component_clause,[],[f204])).

fof(f204,plain,
    ( spl9_20
  <=> v2_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_20])])).

fof(f158,plain,
    ( ! [X4,X5] :
        ( ~ v2_pre_topc(sK3)
        | ~ l1_pre_topc(sK3)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_subset_1(X5,u1_struct_0(sK3))
        | ~ r2_hidden(X5,X4)
        | r1_tarski(sK8(sK3,X4,X5),X4)
        | ~ v3_pre_topc(X4,sK3) )
    | spl9_2 ),
    inference(resolution,[],[f88,f61])).

fof(f61,plain,(
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

fof(f88,plain,
    ( ~ v2_struct_0(sK3)
    | spl9_2 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl9_2
  <=> v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f359,plain,
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
    inference(avatar_component_clause,[],[f358])).

fof(f358,plain,
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

fof(f401,plain,
    ( ~ spl9_26
    | spl9_34 ),
    inference(avatar_contradiction_clause,[],[f400])).

fof(f400,plain,
    ( $false
    | ~ spl9_26
    | spl9_34 ),
    inference(subsumption_resolution,[],[f399,f246])).

fof(f246,plain,
    ( l1_pre_topc(sK2)
    | ~ spl9_26 ),
    inference(avatar_component_clause,[],[f245])).

fof(f245,plain,
    ( spl9_26
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_26])])).

fof(f399,plain,
    ( ~ l1_pre_topc(sK2)
    | spl9_34 ),
    inference(resolution,[],[f388,f54])).

fof(f54,plain,(
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

fof(f388,plain,
    ( ~ l1_struct_0(sK2)
    | spl9_34 ),
    inference(avatar_component_clause,[],[f386])).

fof(f386,plain,
    ( spl9_34
  <=> l1_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_34])])).

fof(f389,plain,
    ( ~ spl9_34
    | spl9_3
    | ~ spl9_33 ),
    inference(avatar_split_clause,[],[f383,f364,f91,f386])).

fof(f364,plain,
    ( spl9_33
  <=> v1_xboole_0(u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_33])])).

fof(f383,plain,
    ( ~ l1_struct_0(sK2)
    | spl9_3
    | ~ spl9_33 ),
    inference(subsumption_resolution,[],[f380,f93])).

fof(f380,plain,
    ( ~ l1_struct_0(sK2)
    | v2_struct_0(sK2)
    | ~ spl9_33 ),
    inference(resolution,[],[f366,f57])).

fof(f57,plain,(
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

fof(f366,plain,
    ( v1_xboole_0(u1_struct_0(sK2))
    | ~ spl9_33 ),
    inference(avatar_component_clause,[],[f364])).

fof(f377,plain,
    ( spl9_2
    | ~ spl9_16
    | ~ spl9_20
    | ~ spl9_21
    | ~ spl9_22
    | ~ spl9_28
    | ~ spl9_30
    | spl9_31 ),
    inference(avatar_contradiction_clause,[],[f376])).

fof(f376,plain,
    ( $false
    | spl9_2
    | ~ spl9_16
    | ~ spl9_20
    | ~ spl9_21
    | ~ spl9_22
    | ~ spl9_28
    | ~ spl9_30
    | spl9_31 ),
    inference(subsumption_resolution,[],[f375,f210])).

fof(f375,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK2),sK3)
    | spl9_2
    | ~ spl9_16
    | ~ spl9_20
    | ~ spl9_22
    | ~ spl9_28
    | ~ spl9_30
    | spl9_31 ),
    inference(subsumption_resolution,[],[f374,f88])).

fof(f374,plain,
    ( v2_struct_0(sK3)
    | ~ v3_pre_topc(u1_struct_0(sK2),sK3)
    | ~ spl9_16
    | ~ spl9_20
    | ~ spl9_22
    | ~ spl9_28
    | ~ spl9_30
    | spl9_31 ),
    inference(subsumption_resolution,[],[f373,f351])).

fof(f373,plain,
    ( ~ r2_hidden(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK3)
    | ~ v3_pre_topc(u1_struct_0(sK2),sK3)
    | ~ spl9_16
    | ~ spl9_20
    | ~ spl9_22
    | ~ spl9_28
    | spl9_31 ),
    inference(subsumption_resolution,[],[f372,f180])).

fof(f372,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ r2_hidden(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK3)
    | ~ v3_pre_topc(u1_struct_0(sK2),sK3)
    | ~ spl9_20
    | ~ spl9_22
    | ~ spl9_28
    | spl9_31 ),
    inference(subsumption_resolution,[],[f371,f302])).

fof(f371,plain,
    ( ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ r2_hidden(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK3)
    | ~ v3_pre_topc(u1_struct_0(sK2),sK3)
    | ~ spl9_20
    | ~ spl9_22
    | spl9_31 ),
    inference(subsumption_resolution,[],[f370,f213])).

fof(f370,plain,
    ( ~ l1_pre_topc(sK3)
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ r2_hidden(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK3)
    | ~ v3_pre_topc(u1_struct_0(sK2),sK3)
    | ~ spl9_20
    | spl9_31 ),
    inference(subsumption_resolution,[],[f368,f205])).

fof(f368,plain,
    ( ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ r2_hidden(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK3)
    | ~ v3_pre_topc(u1_struct_0(sK2),sK3)
    | spl9_31 ),
    inference(resolution,[],[f356,f59])).

fof(f59,plain,(
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

fof(f356,plain,
    ( ~ m1_subset_1(sK8(sK3,u1_struct_0(sK2),sK5),k1_zfmisc_1(u1_struct_0(sK3)))
    | spl9_31 ),
    inference(avatar_component_clause,[],[f354])).

fof(f354,plain,
    ( spl9_31
  <=> m1_subset_1(sK8(sK3,u1_struct_0(sK2),sK5),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_31])])).

fof(f367,plain,
    ( spl9_33
    | ~ spl9_18
    | spl9_30 ),
    inference(avatar_split_clause,[],[f362,f350,f191,f364])).

fof(f362,plain,
    ( v1_xboole_0(u1_struct_0(sK2))
    | ~ spl9_18
    | spl9_30 ),
    inference(subsumption_resolution,[],[f361,f193])).

fof(f361,plain,
    ( v1_xboole_0(u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | spl9_30 ),
    inference(resolution,[],[f352,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f352,plain,
    ( ~ r2_hidden(sK5,u1_struct_0(sK2))
    | spl9_30 ),
    inference(avatar_component_clause,[],[f350])).

fof(f360,plain,
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
    inference(avatar_split_clause,[],[f346,f305,f217,f196,f186,f178,f106,f101,f96,f86,f81,f358,f354,f350])).

fof(f81,plain,
    ( spl9_1
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f96,plain,
    ( spl9_4
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f101,plain,
    ( spl9_5
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f106,plain,
    ( spl9_6
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f186,plain,
    ( spl9_17
  <=> v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_17])])).

fof(f196,plain,
    ( spl9_19
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_19])])).

fof(f217,plain,
    ( spl9_23
  <=> r1_tmap_1(sK3,sK1,sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_23])])).

fof(f305,plain,
    ( spl9_29
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK3))
        | m1_connsp_2(sK8(sK3,u1_struct_0(sK2),X0),sK3,X0)
        | ~ r2_hidden(X0,u1_struct_0(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_29])])).

fof(f346,plain,
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
    inference(subsumption_resolution,[],[f345,f180])).

fof(f345,plain,
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
    inference(resolution,[],[f344,f306])).

fof(f306,plain,
    ( ! [X0] :
        ( m1_connsp_2(sK8(sK3,u1_struct_0(sK2),X0),sK3,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ r2_hidden(X0,u1_struct_0(sK2)) )
    | ~ spl9_29 ),
    inference(avatar_component_clause,[],[f305])).

fof(f344,plain,
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
    inference(subsumption_resolution,[],[f343,f180])).

fof(f343,plain,
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
    inference(subsumption_resolution,[],[f342,f198])).

fof(f198,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ spl9_19 ),
    inference(avatar_component_clause,[],[f196])).

fof(f342,plain,
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
    inference(subsumption_resolution,[],[f341,f188])).

fof(f188,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ spl9_17 ),
    inference(avatar_component_clause,[],[f186])).

fof(f341,plain,
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
    inference(subsumption_resolution,[],[f340,f88])).

fof(f340,plain,
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
    inference(subsumption_resolution,[],[f339,f108])).

fof(f108,plain,
    ( l1_pre_topc(sK1)
    | ~ spl9_6 ),
    inference(avatar_component_clause,[],[f106])).

fof(f339,plain,
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
    inference(subsumption_resolution,[],[f338,f103])).

fof(f103,plain,
    ( v2_pre_topc(sK1)
    | ~ spl9_5 ),
    inference(avatar_component_clause,[],[f101])).

fof(f338,plain,
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
    inference(subsumption_resolution,[],[f337,f98])).

fof(f98,plain,
    ( ~ v2_struct_0(sK1)
    | spl9_4 ),
    inference(avatar_component_clause,[],[f96])).

fof(f337,plain,
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
    inference(resolution,[],[f218,f154])).

fof(f154,plain,
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
    inference(subsumption_resolution,[],[f151,f68])).

fof(f68,plain,(
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

fof(f151,plain,
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
    inference(resolution,[],[f83,f76])).

fof(f76,plain,(
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
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
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

fof(f83,plain,
    ( v1_funct_1(sK4)
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f81])).

fof(f218,plain,
    ( ~ r1_tmap_1(sK3,sK1,sK4,sK5)
    | spl9_23 ),
    inference(avatar_component_clause,[],[f217])).

fof(f335,plain,
    ( ~ spl9_10
    | ~ spl9_23
    | ~ spl9_24 ),
    inference(avatar_contradiction_clause,[],[f334])).

fof(f334,plain,
    ( $false
    | ~ spl9_10
    | ~ spl9_23
    | ~ spl9_24 ),
    inference(subsumption_resolution,[],[f333,f223])).

fof(f333,plain,
    ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)
    | ~ spl9_10
    | ~ spl9_23 ),
    inference(subsumption_resolution,[],[f202,f219])).

fof(f219,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK5)
    | ~ spl9_23 ),
    inference(avatar_component_clause,[],[f217])).

fof(f202,plain,
    ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)
    | ~ r1_tmap_1(sK3,sK1,sK4,sK5)
    | ~ spl9_10 ),
    inference(forward_demodulation,[],[f35,f128])).

fof(f128,plain,
    ( sK5 = sK6
    | ~ spl9_10 ),
    inference(avatar_component_clause,[],[f126])).

fof(f126,plain,
    ( spl9_10
  <=> sK5 = sK6 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).

fof(f35,plain,
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

fof(f332,plain,
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
    inference(avatar_contradiction_clause,[],[f331])).

fof(f331,plain,
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
    inference(subsumption_resolution,[],[f330,f123])).

fof(f330,plain,
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
    inference(subsumption_resolution,[],[f329,f219])).

fof(f329,plain,
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
    inference(subsumption_resolution,[],[f328,f138])).

fof(f328,plain,
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
    inference(subsumption_resolution,[],[f327,f193])).

fof(f327,plain,
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
    inference(subsumption_resolution,[],[f326,f180])).

fof(f326,plain,
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
    inference(subsumption_resolution,[],[f325,f118])).

fof(f325,plain,
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
    inference(subsumption_resolution,[],[f324,f113])).

fof(f324,plain,
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
    inference(subsumption_resolution,[],[f323,f93])).

fof(f323,plain,
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
    inference(subsumption_resolution,[],[f322,f143])).

fof(f322,plain,
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
    inference(resolution,[],[f320,f222])).

fof(f222,plain,
    ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)
    | spl9_24 ),
    inference(avatar_component_clause,[],[f221])).

fof(f320,plain,
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
    inference(subsumption_resolution,[],[f319,f198])).

fof(f319,plain,
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
    inference(subsumption_resolution,[],[f318,f88])).

fof(f318,plain,
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
    inference(subsumption_resolution,[],[f317,f108])).

fof(f317,plain,
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
    inference(subsumption_resolution,[],[f316,f103])).

fof(f316,plain,
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
    inference(subsumption_resolution,[],[f315,f98])).

fof(f315,plain,
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
    inference(resolution,[],[f153,f188])).

fof(f153,plain,
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
    inference(subsumption_resolution,[],[f150,f68])).

fof(f150,plain,
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
    inference(resolution,[],[f83,f77])).

fof(f77,plain,(
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
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
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

fof(f314,plain,
    ( ~ spl9_12
    | ~ spl9_22
    | spl9_28 ),
    inference(avatar_contradiction_clause,[],[f313])).

fof(f313,plain,
    ( $false
    | ~ spl9_12
    | ~ spl9_22
    | spl9_28 ),
    inference(subsumption_resolution,[],[f312,f213])).

fof(f312,plain,
    ( ~ l1_pre_topc(sK3)
    | ~ spl9_12
    | spl9_28 ),
    inference(subsumption_resolution,[],[f310,f138])).

fof(f310,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | ~ l1_pre_topc(sK3)
    | spl9_28 ),
    inference(resolution,[],[f303,f56])).

fof(f56,plain,(
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

fof(f303,plain,
    ( ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
    | spl9_28 ),
    inference(avatar_component_clause,[],[f301])).

fof(f307,plain,
    ( ~ spl9_28
    | spl9_29
    | spl9_2
    | ~ spl9_20
    | ~ spl9_21
    | ~ spl9_22 ),
    inference(avatar_split_clause,[],[f289,f212,f208,f204,f86,f305,f301])).

fof(f289,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ r2_hidden(X0,u1_struct_0(sK2))
        | m1_connsp_2(sK8(sK3,u1_struct_0(sK2),X0),sK3,X0)
        | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3))) )
    | spl9_2
    | ~ spl9_20
    | ~ spl9_21
    | ~ spl9_22 ),
    inference(resolution,[],[f288,f210])).

fof(f288,plain,
    ( ! [X2,X3] :
        ( ~ v3_pre_topc(X2,sK3)
        | ~ m1_subset_1(X3,u1_struct_0(sK3))
        | ~ r2_hidden(X3,X2)
        | m1_connsp_2(sK8(sK3,X2,X3),sK3,X3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) )
    | spl9_2
    | ~ spl9_20
    | ~ spl9_22 ),
    inference(subsumption_resolution,[],[f287,f213])).

fof(f287,plain,
    ( ! [X2,X3] :
        ( ~ l1_pre_topc(sK3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_subset_1(X3,u1_struct_0(sK3))
        | ~ r2_hidden(X3,X2)
        | m1_connsp_2(sK8(sK3,X2,X3),sK3,X3)
        | ~ v3_pre_topc(X2,sK3) )
    | spl9_2
    | ~ spl9_20 ),
    inference(subsumption_resolution,[],[f157,f205])).

fof(f157,plain,
    ( ! [X2,X3] :
        ( ~ v2_pre_topc(sK3)
        | ~ l1_pre_topc(sK3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_subset_1(X3,u1_struct_0(sK3))
        | ~ r2_hidden(X3,X2)
        | m1_connsp_2(sK8(sK3,X2,X3),sK3,X3)
        | ~ v3_pre_topc(X2,sK3) )
    | spl9_2 ),
    inference(resolution,[],[f88,f60])).

fof(f60,plain,(
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

fof(f264,plain,
    ( ~ spl9_9
    | ~ spl9_14
    | spl9_26 ),
    inference(avatar_contradiction_clause,[],[f263])).

fof(f263,plain,
    ( $false
    | ~ spl9_9
    | ~ spl9_14
    | spl9_26 ),
    inference(subsumption_resolution,[],[f258,f123])).

fof(f258,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl9_14
    | spl9_26 ),
    inference(resolution,[],[f253,f148])).

fof(f148,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ spl9_14 ),
    inference(avatar_component_clause,[],[f146])).

fof(f146,plain,
    ( spl9_14
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).

fof(f253,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK2,X0)
        | ~ l1_pre_topc(X0) )
    | spl9_26 ),
    inference(resolution,[],[f247,f55])).

fof(f55,plain,(
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

fof(f247,plain,
    ( ~ l1_pre_topc(sK2)
    | spl9_26 ),
    inference(avatar_component_clause,[],[f245])).

fof(f237,plain,
    ( ~ spl9_8
    | ~ spl9_9
    | ~ spl9_13
    | spl9_20 ),
    inference(avatar_contradiction_clause,[],[f236])).

fof(f236,plain,
    ( $false
    | ~ spl9_8
    | ~ spl9_9
    | ~ spl9_13
    | spl9_20 ),
    inference(subsumption_resolution,[],[f235,f118])).

fof(f235,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ spl9_9
    | ~ spl9_13
    | spl9_20 ),
    inference(subsumption_resolution,[],[f232,f123])).

fof(f232,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl9_13
    | spl9_20 ),
    inference(resolution,[],[f225,f143])).

fof(f225,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK3,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | spl9_20 ),
    inference(resolution,[],[f206,f67])).

fof(f67,plain,(
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

fof(f206,plain,
    ( ~ v2_pre_topc(sK3)
    | spl9_20 ),
    inference(avatar_component_clause,[],[f204])).

fof(f231,plain,
    ( ~ spl9_9
    | ~ spl9_13
    | spl9_22 ),
    inference(avatar_contradiction_clause,[],[f230])).

fof(f230,plain,
    ( $false
    | ~ spl9_9
    | ~ spl9_13
    | spl9_22 ),
    inference(subsumption_resolution,[],[f227,f123])).

fof(f227,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl9_13
    | spl9_22 ),
    inference(resolution,[],[f226,f143])).

fof(f226,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK3,X0)
        | ~ l1_pre_topc(X0) )
    | spl9_22 ),
    inference(resolution,[],[f214,f55])).

fof(f214,plain,
    ( ~ l1_pre_topc(sK3)
    | spl9_22 ),
    inference(avatar_component_clause,[],[f212])).

fof(f224,plain,
    ( spl9_23
    | spl9_24
    | ~ spl9_10 ),
    inference(avatar_split_clause,[],[f200,f126,f221,f217])).

fof(f200,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)
    | r1_tmap_1(sK3,sK1,sK4,sK5)
    | ~ spl9_10 ),
    inference(forward_demodulation,[],[f34,f128])).

fof(f34,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)
    | r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f15])).

fof(f215,plain,
    ( ~ spl9_20
    | spl9_21
    | ~ spl9_22
    | ~ spl9_11
    | ~ spl9_12 ),
    inference(avatar_split_clause,[],[f201,f136,f131,f212,f208,f204])).

fof(f131,plain,
    ( spl9_11
  <=> v1_tsep_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).

fof(f201,plain,
    ( ~ l1_pre_topc(sK3)
    | v3_pre_topc(u1_struct_0(sK2),sK3)
    | ~ v2_pre_topc(sK3)
    | ~ spl9_11
    | ~ spl9_12 ),
    inference(subsumption_resolution,[],[f183,f138])).

fof(f183,plain,
    ( ~ l1_pre_topc(sK3)
    | v3_pre_topc(u1_struct_0(sK2),sK3)
    | ~ v2_pre_topc(sK3)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ spl9_11 ),
    inference(subsumption_resolution,[],[f182,f56])).

fof(f182,plain,
    ( ~ l1_pre_topc(sK3)
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
    | v3_pre_topc(u1_struct_0(sK2),sK3)
    | ~ v2_pre_topc(sK3)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ spl9_11 ),
    inference(resolution,[],[f133,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ v1_tsep_1(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(u1_struct_0(X1),X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0) ) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
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

fof(f133,plain,
    ( v1_tsep_1(sK2,sK3)
    | ~ spl9_11 ),
    inference(avatar_component_clause,[],[f131])).

fof(f199,plain,(
    spl9_19 ),
    inference(avatar_split_clause,[],[f41,f196])).

fof(f41,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f15])).

fof(f194,plain,
    ( spl9_18
    | ~ spl9_10
    | ~ spl9_15 ),
    inference(avatar_split_clause,[],[f184,f173,f126,f191])).

fof(f173,plain,
    ( spl9_15
  <=> m1_subset_1(sK6,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).

fof(f184,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ spl9_10
    | ~ spl9_15 ),
    inference(forward_demodulation,[],[f175,f128])).

fof(f175,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ spl9_15 ),
    inference(avatar_component_clause,[],[f173])).

fof(f189,plain,(
    spl9_17 ),
    inference(avatar_split_clause,[],[f40,f186])).

fof(f40,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f15])).

% (14576)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% (14573)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% (14581)Refutation not found, incomplete strategy% (14581)------------------------------
% (14581)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (14581)Termination reason: Refutation not found, incomplete strategy

% (14581)Memory used [KB]: 10618
% (14581)Time elapsed: 0.093 s
% (14581)------------------------------
% (14581)------------------------------
% (14571)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% (14569)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% (14572)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% (14579)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
fof(f181,plain,(
    spl9_16 ),
    inference(avatar_split_clause,[],[f38,f178])).

fof(f38,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f15])).

fof(f176,plain,(
    spl9_15 ),
    inference(avatar_split_clause,[],[f36,f173])).

fof(f36,plain,(
    m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f15])).

fof(f149,plain,(
    spl9_14 ),
    inference(avatar_split_clause,[],[f47,f146])).

fof(f47,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f144,plain,(
    spl9_13 ),
    inference(avatar_split_clause,[],[f45,f141])).

fof(f45,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f139,plain,(
    spl9_12 ),
    inference(avatar_split_clause,[],[f43,f136])).

fof(f43,plain,(
    m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f15])).

fof(f134,plain,(
    spl9_11 ),
    inference(avatar_split_clause,[],[f42,f131])).

fof(f42,plain,(
    v1_tsep_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f15])).

fof(f129,plain,(
    spl9_10 ),
    inference(avatar_split_clause,[],[f37,f126])).

fof(f37,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f15])).

fof(f124,plain,(
    spl9_9 ),
    inference(avatar_split_clause,[],[f53,f121])).

fof(f53,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f119,plain,(
    spl9_8 ),
    inference(avatar_split_clause,[],[f52,f116])).

fof(f52,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f114,plain,(
    ~ spl9_7 ),
    inference(avatar_split_clause,[],[f51,f111])).

fof(f51,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f109,plain,(
    spl9_6 ),
    inference(avatar_split_clause,[],[f50,f106])).

fof(f50,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f104,plain,(
    spl9_5 ),
    inference(avatar_split_clause,[],[f49,f101])).

fof(f49,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f99,plain,(
    ~ spl9_4 ),
    inference(avatar_split_clause,[],[f48,f96])).

fof(f48,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f94,plain,(
    ~ spl9_3 ),
    inference(avatar_split_clause,[],[f46,f91])).

fof(f46,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f89,plain,(
    ~ spl9_2 ),
    inference(avatar_split_clause,[],[f44,f86])).

fof(f44,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f15])).

fof(f84,plain,(
    spl9_1 ),
    inference(avatar_split_clause,[],[f39,f81])).

fof(f39,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:34:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.46  % (14564)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.48  % (14560)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.49  % (14568)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.49  % (14565)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.50  % (14574)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.50  % (14580)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.51  % (14575)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.51  % (14563)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.51  % (14578)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.51  % (14566)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.51  % (14581)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.51  % (14562)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.51  % (14567)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.51  % (14561)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.51  % (14563)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f425,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(avatar_sat_refutation,[],[f84,f89,f94,f99,f104,f109,f114,f119,f124,f129,f134,f139,f144,f149,f176,f181,f189,f194,f199,f215,f224,f231,f237,f264,f307,f314,f332,f335,f360,f367,f377,f389,f401,f424])).
% 0.22/0.51  fof(f424,plain,(
% 0.22/0.51    spl9_2 | spl9_3 | spl9_7 | ~spl9_8 | ~spl9_9 | ~spl9_12 | ~spl9_13 | ~spl9_16 | ~spl9_18 | ~spl9_20 | ~spl9_21 | ~spl9_22 | ~spl9_24 | ~spl9_28 | ~spl9_30 | ~spl9_32),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f423])).
% 0.22/0.51  fof(f423,plain,(
% 0.22/0.51    $false | (spl9_2 | spl9_3 | spl9_7 | ~spl9_8 | ~spl9_9 | ~spl9_12 | ~spl9_13 | ~spl9_16 | ~spl9_18 | ~spl9_20 | ~spl9_21 | ~spl9_22 | ~spl9_24 | ~spl9_28 | ~spl9_30 | ~spl9_32)),
% 0.22/0.51    inference(subsumption_resolution,[],[f422,f113])).
% 0.22/0.51  fof(f113,plain,(
% 0.22/0.51    ~v2_struct_0(sK0) | spl9_7),
% 0.22/0.51    inference(avatar_component_clause,[],[f111])).
% 0.22/0.51  fof(f111,plain,(
% 0.22/0.51    spl9_7 <=> v2_struct_0(sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).
% 0.22/0.51  fof(f422,plain,(
% 0.22/0.51    v2_struct_0(sK0) | (spl9_2 | spl9_3 | ~spl9_8 | ~spl9_9 | ~spl9_12 | ~spl9_13 | ~spl9_16 | ~spl9_18 | ~spl9_20 | ~spl9_21 | ~spl9_22 | ~spl9_24 | ~spl9_28 | ~spl9_30 | ~spl9_32)),
% 0.22/0.51    inference(subsumption_resolution,[],[f421,f123])).
% 0.22/0.51  fof(f123,plain,(
% 0.22/0.51    l1_pre_topc(sK0) | ~spl9_9),
% 0.22/0.51    inference(avatar_component_clause,[],[f121])).
% 0.22/0.51  fof(f121,plain,(
% 0.22/0.51    spl9_9 <=> l1_pre_topc(sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).
% 0.22/0.51  fof(f421,plain,(
% 0.22/0.51    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | (spl9_2 | spl9_3 | ~spl9_8 | ~spl9_12 | ~spl9_13 | ~spl9_16 | ~spl9_18 | ~spl9_20 | ~spl9_21 | ~spl9_22 | ~spl9_24 | ~spl9_28 | ~spl9_30 | ~spl9_32)),
% 0.22/0.51    inference(subsumption_resolution,[],[f420,f143])).
% 0.22/0.51  fof(f143,plain,(
% 0.22/0.51    m1_pre_topc(sK3,sK0) | ~spl9_13),
% 0.22/0.51    inference(avatar_component_clause,[],[f141])).
% 0.22/0.51  fof(f141,plain,(
% 0.22/0.51    spl9_13 <=> m1_pre_topc(sK3,sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).
% 0.22/0.51  fof(f420,plain,(
% 0.22/0.51    ~m1_pre_topc(sK3,sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | (spl9_2 | spl9_3 | ~spl9_8 | ~spl9_12 | ~spl9_16 | ~spl9_18 | ~spl9_20 | ~spl9_21 | ~spl9_22 | ~spl9_24 | ~spl9_28 | ~spl9_30 | ~spl9_32)),
% 0.22/0.51    inference(subsumption_resolution,[],[f417,f118])).
% 0.22/0.51  fof(f118,plain,(
% 0.22/0.51    v2_pre_topc(sK0) | ~spl9_8),
% 0.22/0.51    inference(avatar_component_clause,[],[f116])).
% 0.22/0.51  fof(f116,plain,(
% 0.22/0.51    spl9_8 <=> v2_pre_topc(sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).
% 0.22/0.51  fof(f417,plain,(
% 0.22/0.51    ~v2_pre_topc(sK0) | ~m1_pre_topc(sK3,sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | (spl9_2 | spl9_3 | ~spl9_12 | ~spl9_16 | ~spl9_18 | ~spl9_20 | ~spl9_21 | ~spl9_22 | ~spl9_24 | ~spl9_28 | ~spl9_30 | ~spl9_32)),
% 0.22/0.51    inference(resolution,[],[f409,f223])).
% 0.22/0.51  fof(f223,plain,(
% 0.22/0.51    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) | ~spl9_24),
% 0.22/0.51    inference(avatar_component_clause,[],[f221])).
% 0.22/0.51  fof(f221,plain,(
% 0.22/0.51    spl9_24 <=> r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_24])])).
% 0.22/0.51  fof(f409,plain,(
% 0.22/0.51    ( ! [X0] : (~r1_tmap_1(sK2,sK1,k3_tmap_1(X0,sK1,sK3,sK2,sK4),sK5) | ~v2_pre_topc(X0) | ~m1_pre_topc(sK3,X0) | ~l1_pre_topc(X0) | v2_struct_0(X0)) ) | (spl9_2 | spl9_3 | ~spl9_12 | ~spl9_16 | ~spl9_18 | ~spl9_20 | ~spl9_21 | ~spl9_22 | ~spl9_28 | ~spl9_30 | ~spl9_32)),
% 0.22/0.51    inference(subsumption_resolution,[],[f408,f210])).
% 0.22/0.51  fof(f210,plain,(
% 0.22/0.51    v3_pre_topc(u1_struct_0(sK2),sK3) | ~spl9_21),
% 0.22/0.51    inference(avatar_component_clause,[],[f208])).
% 0.22/0.51  fof(f208,plain,(
% 0.22/0.51    spl9_21 <=> v3_pre_topc(u1_struct_0(sK2),sK3)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_21])])).
% 0.22/0.51  fof(f408,plain,(
% 0.22/0.51    ( ! [X0] : (~v2_pre_topc(X0) | ~r1_tmap_1(sK2,sK1,k3_tmap_1(X0,sK1,sK3,sK2,sK4),sK5) | ~m1_pre_topc(sK3,X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~v3_pre_topc(u1_struct_0(sK2),sK3)) ) | (spl9_2 | spl9_3 | ~spl9_12 | ~spl9_16 | ~spl9_18 | ~spl9_20 | ~spl9_22 | ~spl9_28 | ~spl9_30 | ~spl9_32)),
% 0.22/0.51    inference(subsumption_resolution,[],[f407,f302])).
% 0.22/0.51  fof(f302,plain,(
% 0.22/0.51    m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3))) | ~spl9_28),
% 0.22/0.51    inference(avatar_component_clause,[],[f301])).
% 0.22/0.51  fof(f301,plain,(
% 0.22/0.51    spl9_28 <=> m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_28])])).
% 0.22/0.51  fof(f407,plain,(
% 0.22/0.51    ( ! [X0] : (~v2_pre_topc(X0) | ~r1_tmap_1(sK2,sK1,k3_tmap_1(X0,sK1,sK3,sK2,sK4),sK5) | ~m1_pre_topc(sK3,X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3))) | ~v3_pre_topc(u1_struct_0(sK2),sK3)) ) | (spl9_2 | spl9_3 | ~spl9_12 | ~spl9_16 | ~spl9_18 | ~spl9_20 | ~spl9_22 | ~spl9_30 | ~spl9_32)),
% 0.22/0.51    inference(subsumption_resolution,[],[f406,f351])).
% 0.22/0.51  fof(f351,plain,(
% 0.22/0.51    r2_hidden(sK5,u1_struct_0(sK2)) | ~spl9_30),
% 0.22/0.51    inference(avatar_component_clause,[],[f350])).
% 0.22/0.51  fof(f350,plain,(
% 0.22/0.51    spl9_30 <=> r2_hidden(sK5,u1_struct_0(sK2))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_30])])).
% 0.22/0.51  fof(f406,plain,(
% 0.22/0.51    ( ! [X0] : (~v2_pre_topc(X0) | ~r1_tmap_1(sK2,sK1,k3_tmap_1(X0,sK1,sK3,sK2,sK4),sK5) | ~m1_pre_topc(sK3,X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~r2_hidden(sK5,u1_struct_0(sK2)) | ~m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3))) | ~v3_pre_topc(u1_struct_0(sK2),sK3)) ) | (spl9_2 | spl9_3 | ~spl9_12 | ~spl9_16 | ~spl9_18 | ~spl9_20 | ~spl9_22 | ~spl9_32)),
% 0.22/0.51    inference(subsumption_resolution,[],[f405,f180])).
% 0.22/0.51  fof(f180,plain,(
% 0.22/0.51    m1_subset_1(sK5,u1_struct_0(sK3)) | ~spl9_16),
% 0.22/0.51    inference(avatar_component_clause,[],[f178])).
% 0.22/0.51  fof(f178,plain,(
% 0.22/0.51    spl9_16 <=> m1_subset_1(sK5,u1_struct_0(sK3))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).
% 0.22/0.51  fof(f405,plain,(
% 0.22/0.51    ( ! [X0] : (~v2_pre_topc(X0) | ~r1_tmap_1(sK2,sK1,k3_tmap_1(X0,sK1,sK3,sK2,sK4),sK5) | ~m1_pre_topc(sK3,X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~r2_hidden(sK5,u1_struct_0(sK2)) | ~m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3))) | ~v3_pre_topc(u1_struct_0(sK2),sK3)) ) | (spl9_2 | spl9_3 | ~spl9_12 | ~spl9_18 | ~spl9_20 | ~spl9_22 | ~spl9_32)),
% 0.22/0.51    inference(subsumption_resolution,[],[f404,f138])).
% 0.22/0.51  fof(f138,plain,(
% 0.22/0.51    m1_pre_topc(sK2,sK3) | ~spl9_12),
% 0.22/0.51    inference(avatar_component_clause,[],[f136])).
% 0.22/0.51  fof(f136,plain,(
% 0.22/0.51    spl9_12 <=> m1_pre_topc(sK2,sK3)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).
% 0.22/0.51  fof(f404,plain,(
% 0.22/0.51    ( ! [X0] : (~v2_pre_topc(X0) | ~r1_tmap_1(sK2,sK1,k3_tmap_1(X0,sK1,sK3,sK2,sK4),sK5) | ~m1_pre_topc(sK2,sK3) | ~m1_pre_topc(sK3,X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~r2_hidden(sK5,u1_struct_0(sK2)) | ~m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3))) | ~v3_pre_topc(u1_struct_0(sK2),sK3)) ) | (spl9_2 | spl9_3 | ~spl9_18 | ~spl9_20 | ~spl9_22 | ~spl9_32)),
% 0.22/0.51    inference(subsumption_resolution,[],[f403,f193])).
% 0.22/0.51  fof(f193,plain,(
% 0.22/0.51    m1_subset_1(sK5,u1_struct_0(sK2)) | ~spl9_18),
% 0.22/0.51    inference(avatar_component_clause,[],[f191])).
% 0.22/0.51  fof(f191,plain,(
% 0.22/0.51    spl9_18 <=> m1_subset_1(sK5,u1_struct_0(sK2))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).
% 0.22/0.51  fof(f403,plain,(
% 0.22/0.51    ( ! [X0] : (~v2_pre_topc(X0) | ~r1_tmap_1(sK2,sK1,k3_tmap_1(X0,sK1,sK3,sK2,sK4),sK5) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~m1_pre_topc(sK2,sK3) | ~m1_pre_topc(sK3,X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~r2_hidden(sK5,u1_struct_0(sK2)) | ~m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3))) | ~v3_pre_topc(u1_struct_0(sK2),sK3)) ) | (spl9_2 | spl9_3 | ~spl9_20 | ~spl9_22 | ~spl9_32)),
% 0.22/0.51    inference(subsumption_resolution,[],[f402,f93])).
% 0.22/0.51  fof(f93,plain,(
% 0.22/0.51    ~v2_struct_0(sK2) | spl9_3),
% 0.22/0.51    inference(avatar_component_clause,[],[f91])).
% 0.22/0.51  fof(f91,plain,(
% 0.22/0.51    spl9_3 <=> v2_struct_0(sK2)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 0.22/0.51  fof(f402,plain,(
% 0.22/0.51    ( ! [X0] : (~v2_pre_topc(X0) | ~r1_tmap_1(sK2,sK1,k3_tmap_1(X0,sK1,sK3,sK2,sK4),sK5) | v2_struct_0(sK2) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~m1_pre_topc(sK2,sK3) | ~m1_pre_topc(sK3,X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~r2_hidden(sK5,u1_struct_0(sK2)) | ~m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3))) | ~v3_pre_topc(u1_struct_0(sK2),sK3)) ) | (spl9_2 | ~spl9_20 | ~spl9_22 | ~spl9_32)),
% 0.22/0.51    inference(resolution,[],[f359,f278])).
% 0.22/0.51  fof(f278,plain,(
% 0.22/0.51    ( ! [X4,X5] : (r1_tarski(sK8(sK3,X4,X5),X4) | ~m1_subset_1(X5,u1_struct_0(sK3)) | ~r2_hidden(X5,X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK3))) | ~v3_pre_topc(X4,sK3)) ) | (spl9_2 | ~spl9_20 | ~spl9_22)),
% 0.22/0.51    inference(subsumption_resolution,[],[f277,f213])).
% 0.22/0.51  fof(f213,plain,(
% 0.22/0.51    l1_pre_topc(sK3) | ~spl9_22),
% 0.22/0.51    inference(avatar_component_clause,[],[f212])).
% 0.22/0.51  fof(f212,plain,(
% 0.22/0.51    spl9_22 <=> l1_pre_topc(sK3)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_22])])).
% 0.22/0.51  fof(f277,plain,(
% 0.22/0.51    ( ! [X4,X5] : (~l1_pre_topc(sK3) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(X5,u1_struct_0(sK3)) | ~r2_hidden(X5,X4) | r1_tarski(sK8(sK3,X4,X5),X4) | ~v3_pre_topc(X4,sK3)) ) | (spl9_2 | ~spl9_20)),
% 0.22/0.51    inference(subsumption_resolution,[],[f158,f205])).
% 0.22/0.51  fof(f205,plain,(
% 0.22/0.51    v2_pre_topc(sK3) | ~spl9_20),
% 0.22/0.51    inference(avatar_component_clause,[],[f204])).
% 0.22/0.51  fof(f204,plain,(
% 0.22/0.51    spl9_20 <=> v2_pre_topc(sK3)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_20])])).
% 0.22/0.51  fof(f158,plain,(
% 0.22/0.51    ( ! [X4,X5] : (~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(X5,u1_struct_0(sK3)) | ~r2_hidden(X5,X4) | r1_tarski(sK8(sK3,X4,X5),X4) | ~v3_pre_topc(X4,sK3)) ) | spl9_2),
% 0.22/0.51    inference(resolution,[],[f88,f61])).
% 0.22/0.51  fof(f61,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r2_hidden(X2,X1) | r1_tarski(sK8(X0,X1,X2),X1) | ~v3_pre_topc(X1,X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f22])).
% 0.22/0.51  fof(f22,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> ! [X2] : (? [X3] : (r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f21])).
% 0.22/0.51  fof(f21,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> ! [X2] : ((? [X3] : ((r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f6])).
% 0.22/0.51  fof(f6,axiom,(
% 0.22/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2))) & r2_hidden(X2,X1))))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_connsp_2)).
% 0.22/0.51  fof(f88,plain,(
% 0.22/0.51    ~v2_struct_0(sK3) | spl9_2),
% 0.22/0.51    inference(avatar_component_clause,[],[f86])).
% 0.22/0.51  fof(f86,plain,(
% 0.22/0.51    spl9_2 <=> v2_struct_0(sK3)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 0.22/0.51  fof(f359,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r1_tarski(sK8(sK3,u1_struct_0(sK2),sK5),u1_struct_0(X0)) | ~v2_pre_topc(X1) | ~r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5) | v2_struct_0(X0) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~m1_pre_topc(X0,sK3) | ~m1_pre_topc(sK3,X1) | ~l1_pre_topc(X1) | v2_struct_0(X1)) ) | ~spl9_32),
% 0.22/0.51    inference(avatar_component_clause,[],[f358])).
% 0.22/0.51  fof(f358,plain,(
% 0.22/0.51    spl9_32 <=> ! [X1,X0] : (v2_struct_0(X0) | ~v2_pre_topc(X1) | ~r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5) | ~r1_tarski(sK8(sK3,u1_struct_0(sK2),sK5),u1_struct_0(X0)) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~m1_pre_topc(X0,sK3) | ~m1_pre_topc(sK3,X1) | ~l1_pre_topc(X1) | v2_struct_0(X1))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_32])])).
% 0.22/0.51  fof(f401,plain,(
% 0.22/0.51    ~spl9_26 | spl9_34),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f400])).
% 0.22/0.51  fof(f400,plain,(
% 0.22/0.51    $false | (~spl9_26 | spl9_34)),
% 0.22/0.51    inference(subsumption_resolution,[],[f399,f246])).
% 0.22/0.51  fof(f246,plain,(
% 0.22/0.51    l1_pre_topc(sK2) | ~spl9_26),
% 0.22/0.51    inference(avatar_component_clause,[],[f245])).
% 0.22/0.51  fof(f245,plain,(
% 0.22/0.51    spl9_26 <=> l1_pre_topc(sK2)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_26])])).
% 0.22/0.51  fof(f399,plain,(
% 0.22/0.51    ~l1_pre_topc(sK2) | spl9_34),
% 0.22/0.51    inference(resolution,[],[f388,f54])).
% 0.22/0.51  fof(f54,plain,(
% 0.22/0.51    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f16])).
% 0.22/0.51  fof(f16,plain,(
% 0.22/0.51    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f3])).
% 0.22/0.51  fof(f3,axiom,(
% 0.22/0.51    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.22/0.51  fof(f388,plain,(
% 0.22/0.51    ~l1_struct_0(sK2) | spl9_34),
% 0.22/0.51    inference(avatar_component_clause,[],[f386])).
% 0.22/0.51  fof(f386,plain,(
% 0.22/0.51    spl9_34 <=> l1_struct_0(sK2)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_34])])).
% 0.22/0.51  fof(f389,plain,(
% 0.22/0.51    ~spl9_34 | spl9_3 | ~spl9_33),
% 0.22/0.51    inference(avatar_split_clause,[],[f383,f364,f91,f386])).
% 0.22/0.51  fof(f364,plain,(
% 0.22/0.51    spl9_33 <=> v1_xboole_0(u1_struct_0(sK2))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_33])])).
% 0.22/0.51  fof(f383,plain,(
% 0.22/0.51    ~l1_struct_0(sK2) | (spl9_3 | ~spl9_33)),
% 0.22/0.51    inference(subsumption_resolution,[],[f380,f93])).
% 0.22/0.51  fof(f380,plain,(
% 0.22/0.51    ~l1_struct_0(sK2) | v2_struct_0(sK2) | ~spl9_33),
% 0.22/0.51    inference(resolution,[],[f366,f57])).
% 0.22/0.51  fof(f57,plain,(
% 0.22/0.51    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f20])).
% 0.22/0.51  fof(f20,plain,(
% 0.22/0.51    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f19])).
% 0.22/0.51  fof(f19,plain,(
% 0.22/0.51    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f5])).
% 0.22/0.51  fof(f5,axiom,(
% 0.22/0.51    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.22/0.51  fof(f366,plain,(
% 0.22/0.51    v1_xboole_0(u1_struct_0(sK2)) | ~spl9_33),
% 0.22/0.51    inference(avatar_component_clause,[],[f364])).
% 0.22/0.51  fof(f377,plain,(
% 0.22/0.51    spl9_2 | ~spl9_16 | ~spl9_20 | ~spl9_21 | ~spl9_22 | ~spl9_28 | ~spl9_30 | spl9_31),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f376])).
% 0.22/0.51  fof(f376,plain,(
% 0.22/0.51    $false | (spl9_2 | ~spl9_16 | ~spl9_20 | ~spl9_21 | ~spl9_22 | ~spl9_28 | ~spl9_30 | spl9_31)),
% 0.22/0.51    inference(subsumption_resolution,[],[f375,f210])).
% 0.22/0.51  fof(f375,plain,(
% 0.22/0.51    ~v3_pre_topc(u1_struct_0(sK2),sK3) | (spl9_2 | ~spl9_16 | ~spl9_20 | ~spl9_22 | ~spl9_28 | ~spl9_30 | spl9_31)),
% 0.22/0.51    inference(subsumption_resolution,[],[f374,f88])).
% 0.22/0.51  fof(f374,plain,(
% 0.22/0.51    v2_struct_0(sK3) | ~v3_pre_topc(u1_struct_0(sK2),sK3) | (~spl9_16 | ~spl9_20 | ~spl9_22 | ~spl9_28 | ~spl9_30 | spl9_31)),
% 0.22/0.51    inference(subsumption_resolution,[],[f373,f351])).
% 0.22/0.51  fof(f373,plain,(
% 0.22/0.51    ~r2_hidden(sK5,u1_struct_0(sK2)) | v2_struct_0(sK3) | ~v3_pre_topc(u1_struct_0(sK2),sK3) | (~spl9_16 | ~spl9_20 | ~spl9_22 | ~spl9_28 | spl9_31)),
% 0.22/0.51    inference(subsumption_resolution,[],[f372,f180])).
% 0.22/0.51  fof(f372,plain,(
% 0.22/0.51    ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~r2_hidden(sK5,u1_struct_0(sK2)) | v2_struct_0(sK3) | ~v3_pre_topc(u1_struct_0(sK2),sK3) | (~spl9_20 | ~spl9_22 | ~spl9_28 | spl9_31)),
% 0.22/0.51    inference(subsumption_resolution,[],[f371,f302])).
% 0.22/0.51  fof(f371,plain,(
% 0.22/0.51    ~m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~r2_hidden(sK5,u1_struct_0(sK2)) | v2_struct_0(sK3) | ~v3_pre_topc(u1_struct_0(sK2),sK3) | (~spl9_20 | ~spl9_22 | spl9_31)),
% 0.22/0.51    inference(subsumption_resolution,[],[f370,f213])).
% 0.22/0.51  fof(f370,plain,(
% 0.22/0.51    ~l1_pre_topc(sK3) | ~m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~r2_hidden(sK5,u1_struct_0(sK2)) | v2_struct_0(sK3) | ~v3_pre_topc(u1_struct_0(sK2),sK3) | (~spl9_20 | spl9_31)),
% 0.22/0.51    inference(subsumption_resolution,[],[f368,f205])).
% 0.22/0.51  fof(f368,plain,(
% 0.22/0.51    ~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | ~m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~r2_hidden(sK5,u1_struct_0(sK2)) | v2_struct_0(sK3) | ~v3_pre_topc(u1_struct_0(sK2),sK3) | spl9_31),
% 0.22/0.51    inference(resolution,[],[f356,f59])).
% 0.22/0.51  fof(f59,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (m1_subset_1(sK8(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r2_hidden(X2,X1) | v2_struct_0(X0) | ~v3_pre_topc(X1,X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f22])).
% 0.22/0.51  fof(f356,plain,(
% 0.22/0.51    ~m1_subset_1(sK8(sK3,u1_struct_0(sK2),sK5),k1_zfmisc_1(u1_struct_0(sK3))) | spl9_31),
% 0.22/0.51    inference(avatar_component_clause,[],[f354])).
% 0.22/0.51  fof(f354,plain,(
% 0.22/0.51    spl9_31 <=> m1_subset_1(sK8(sK3,u1_struct_0(sK2),sK5),k1_zfmisc_1(u1_struct_0(sK3)))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_31])])).
% 0.22/0.51  fof(f367,plain,(
% 0.22/0.51    spl9_33 | ~spl9_18 | spl9_30),
% 0.22/0.51    inference(avatar_split_clause,[],[f362,f350,f191,f364])).
% 0.22/0.51  fof(f362,plain,(
% 0.22/0.51    v1_xboole_0(u1_struct_0(sK2)) | (~spl9_18 | spl9_30)),
% 0.22/0.51    inference(subsumption_resolution,[],[f361,f193])).
% 0.22/0.51  fof(f361,plain,(
% 0.22/0.51    v1_xboole_0(u1_struct_0(sK2)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | spl9_30),
% 0.22/0.51    inference(resolution,[],[f352,f74])).
% 0.22/0.51  fof(f74,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r2_hidden(X1,X0) | v1_xboole_0(X0) | ~m1_subset_1(X1,X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f33])).
% 0.22/0.51  fof(f33,plain,(
% 0.22/0.51    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f1])).
% 0.22/0.51  fof(f1,axiom,(
% 0.22/0.51    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 0.22/0.51  fof(f352,plain,(
% 0.22/0.51    ~r2_hidden(sK5,u1_struct_0(sK2)) | spl9_30),
% 0.22/0.51    inference(avatar_component_clause,[],[f350])).
% 0.22/0.51  fof(f360,plain,(
% 0.22/0.51    ~spl9_30 | ~spl9_31 | spl9_32 | ~spl9_1 | spl9_2 | spl9_4 | ~spl9_5 | ~spl9_6 | ~spl9_16 | ~spl9_17 | ~spl9_19 | spl9_23 | ~spl9_29),
% 0.22/0.51    inference(avatar_split_clause,[],[f346,f305,f217,f196,f186,f178,f106,f101,f96,f86,f81,f358,f354,f350])).
% 0.22/0.51  fof(f81,plain,(
% 0.22/0.51    spl9_1 <=> v1_funct_1(sK4)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 0.22/0.51  fof(f96,plain,(
% 0.22/0.51    spl9_4 <=> v2_struct_0(sK1)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).
% 0.22/0.51  fof(f101,plain,(
% 0.22/0.51    spl9_5 <=> v2_pre_topc(sK1)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).
% 0.22/0.51  fof(f106,plain,(
% 0.22/0.51    spl9_6 <=> l1_pre_topc(sK1)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).
% 0.22/0.51  fof(f186,plain,(
% 0.22/0.51    spl9_17 <=> v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_17])])).
% 0.22/0.51  fof(f196,plain,(
% 0.22/0.51    spl9_19 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_19])])).
% 0.22/0.51  fof(f217,plain,(
% 0.22/0.51    spl9_23 <=> r1_tmap_1(sK3,sK1,sK4,sK5)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_23])])).
% 0.22/0.51  fof(f305,plain,(
% 0.22/0.51    spl9_29 <=> ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK3)) | m1_connsp_2(sK8(sK3,u1_struct_0(sK2),X0),sK3,X0) | ~r2_hidden(X0,u1_struct_0(sK2)))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_29])])).
% 0.22/0.51  fof(f346,plain,(
% 0.22/0.51    ( ! [X0,X1] : (v2_struct_0(X0) | ~m1_pre_topc(sK3,X1) | v2_struct_0(X1) | ~m1_pre_topc(X0,sK3) | ~m1_subset_1(sK8(sK3,u1_struct_0(sK2),sK5),k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~r1_tarski(sK8(sK3,u1_struct_0(sK2),sK5),u1_struct_0(X0)) | ~l1_pre_topc(X1) | ~r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5) | ~v2_pre_topc(X1) | ~r2_hidden(sK5,u1_struct_0(sK2))) ) | (~spl9_1 | spl9_2 | spl9_4 | ~spl9_5 | ~spl9_6 | ~spl9_16 | ~spl9_17 | ~spl9_19 | spl9_23 | ~spl9_29)),
% 0.22/0.51    inference(subsumption_resolution,[],[f345,f180])).
% 0.22/0.51  fof(f345,plain,(
% 0.22/0.51    ( ! [X0,X1] : (v2_struct_0(X0) | ~m1_pre_topc(sK3,X1) | v2_struct_0(X1) | ~m1_pre_topc(X0,sK3) | ~m1_subset_1(sK8(sK3,u1_struct_0(sK2),sK5),k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~r1_tarski(sK8(sK3,u1_struct_0(sK2),sK5),u1_struct_0(X0)) | ~l1_pre_topc(X1) | ~r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5) | ~v2_pre_topc(X1) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~r2_hidden(sK5,u1_struct_0(sK2))) ) | (~spl9_1 | spl9_2 | spl9_4 | ~spl9_5 | ~spl9_6 | ~spl9_16 | ~spl9_17 | ~spl9_19 | spl9_23 | ~spl9_29)),
% 0.22/0.51    inference(resolution,[],[f344,f306])).
% 0.22/0.51  fof(f306,plain,(
% 0.22/0.51    ( ! [X0] : (m1_connsp_2(sK8(sK3,u1_struct_0(sK2),X0),sK3,X0) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~r2_hidden(X0,u1_struct_0(sK2))) ) | ~spl9_29),
% 0.22/0.51    inference(avatar_component_clause,[],[f305])).
% 0.22/0.51  fof(f344,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~m1_connsp_2(X2,sK3,sK5) | v2_struct_0(X1) | ~m1_pre_topc(sK3,X0) | v2_struct_0(X0) | ~m1_pre_topc(X1,sK3) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK5,u1_struct_0(X1)) | ~r1_tarski(X2,u1_struct_0(X1)) | ~l1_pre_topc(X0) | ~r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),sK5) | ~v2_pre_topc(X0)) ) | (~spl9_1 | spl9_2 | spl9_4 | ~spl9_5 | ~spl9_6 | ~spl9_16 | ~spl9_17 | ~spl9_19 | spl9_23)),
% 0.22/0.51    inference(subsumption_resolution,[],[f343,f180])).
% 0.22/0.51  fof(f343,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(sK3,X0) | v2_struct_0(X0) | ~m1_pre_topc(X1,sK3) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(X1)) | ~r1_tarski(X2,u1_struct_0(X1)) | ~m1_connsp_2(X2,sK3,sK5) | ~r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),sK5) | ~v2_pre_topc(X0)) ) | (~spl9_1 | spl9_2 | spl9_4 | ~spl9_5 | ~spl9_6 | ~spl9_17 | ~spl9_19 | spl9_23)),
% 0.22/0.51    inference(subsumption_resolution,[],[f342,f198])).
% 0.22/0.51  fof(f198,plain,(
% 0.22/0.51    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~spl9_19),
% 0.22/0.51    inference(avatar_component_clause,[],[f196])).
% 0.22/0.51  fof(f342,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(sK3,X0) | v2_struct_0(X0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(X1,sK3) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(X1)) | ~r1_tarski(X2,u1_struct_0(X1)) | ~m1_connsp_2(X2,sK3,sK5) | ~r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),sK5) | ~v2_pre_topc(X0)) ) | (~spl9_1 | spl9_2 | spl9_4 | ~spl9_5 | ~spl9_6 | ~spl9_17 | spl9_23)),
% 0.22/0.51    inference(subsumption_resolution,[],[f341,f188])).
% 0.22/0.51  fof(f188,plain,(
% 0.22/0.51    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~spl9_17),
% 0.22/0.51    inference(avatar_component_clause,[],[f186])).
% 0.22/0.51  fof(f341,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(sK3,X0) | v2_struct_0(X0) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(X1,sK3) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(X1)) | ~r1_tarski(X2,u1_struct_0(X1)) | ~m1_connsp_2(X2,sK3,sK5) | ~r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),sK5) | ~v2_pre_topc(X0)) ) | (~spl9_1 | spl9_2 | spl9_4 | ~spl9_5 | ~spl9_6 | spl9_23)),
% 0.22/0.51    inference(subsumption_resolution,[],[f340,f88])).
% 0.22/0.51  fof(f340,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | v2_struct_0(X1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,X0) | v2_struct_0(X0) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(X1,sK3) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(X1)) | ~r1_tarski(X2,u1_struct_0(X1)) | ~m1_connsp_2(X2,sK3,sK5) | ~r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),sK5) | ~v2_pre_topc(X0)) ) | (~spl9_1 | spl9_4 | ~spl9_5 | ~spl9_6 | spl9_23)),
% 0.22/0.51    inference(subsumption_resolution,[],[f339,f108])).
% 0.22/0.51  fof(f108,plain,(
% 0.22/0.51    l1_pre_topc(sK1) | ~spl9_6),
% 0.22/0.51    inference(avatar_component_clause,[],[f106])).
% 0.22/0.51  fof(f339,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~l1_pre_topc(sK1) | v2_struct_0(X1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,X0) | v2_struct_0(X0) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(X1,sK3) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(X1)) | ~r1_tarski(X2,u1_struct_0(X1)) | ~m1_connsp_2(X2,sK3,sK5) | ~r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),sK5) | ~v2_pre_topc(X0)) ) | (~spl9_1 | spl9_4 | ~spl9_5 | spl9_23)),
% 0.22/0.51    inference(subsumption_resolution,[],[f338,f103])).
% 0.22/0.51  fof(f103,plain,(
% 0.22/0.51    v2_pre_topc(sK1) | ~spl9_5),
% 0.22/0.51    inference(avatar_component_clause,[],[f101])).
% 0.22/0.51  fof(f338,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(X1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,X0) | v2_struct_0(X0) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(X1,sK3) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(X1)) | ~r1_tarski(X2,u1_struct_0(X1)) | ~m1_connsp_2(X2,sK3,sK5) | ~r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),sK5) | ~v2_pre_topc(X0)) ) | (~spl9_1 | spl9_4 | spl9_23)),
% 0.22/0.51    inference(subsumption_resolution,[],[f337,f98])).
% 0.22/0.51  fof(f98,plain,(
% 0.22/0.51    ~v2_struct_0(sK1) | spl9_4),
% 0.22/0.51    inference(avatar_component_clause,[],[f96])).
% 0.22/0.51  fof(f337,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(X1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,X0) | v2_struct_0(X0) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(X1,sK3) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(X1)) | ~r1_tarski(X2,u1_struct_0(X1)) | ~m1_connsp_2(X2,sK3,sK5) | ~r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),sK5) | ~v2_pre_topc(X0)) ) | (~spl9_1 | spl9_23)),
% 0.22/0.51    inference(resolution,[],[f218,f154])).
% 0.22/0.51  fof(f154,plain,(
% 0.22/0.51    ( ! [X6,X10,X8,X7,X5,X9] : (r1_tmap_1(X8,X6,sK4,X10) | ~l1_pre_topc(X5) | v2_struct_0(X6) | ~v2_pre_topc(X6) | ~l1_pre_topc(X6) | v2_struct_0(X7) | v2_struct_0(X8) | ~m1_pre_topc(X8,X5) | v2_struct_0(X5) | ~v1_funct_2(sK4,u1_struct_0(X8),u1_struct_0(X6)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(X6)))) | ~m1_pre_topc(X7,X8) | ~m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8))) | ~m1_subset_1(X10,u1_struct_0(X8)) | ~m1_subset_1(X10,u1_struct_0(X7)) | ~r1_tarski(X9,u1_struct_0(X7)) | ~m1_connsp_2(X9,X8,X10) | ~r1_tmap_1(X7,X6,k3_tmap_1(X5,X6,X8,X7,sK4),X10) | ~v2_pre_topc(X5)) ) | ~spl9_1),
% 0.22/0.51    inference(subsumption_resolution,[],[f151,f68])).
% 0.22/0.51  fof(f68,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(X2,X1) | ~v2_pre_topc(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f30])).
% 0.22/0.51  fof(f30,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.51    inference(flattening,[],[f29])).
% 0.22/0.51  fof(f29,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f9])).
% 0.22/0.51  fof(f9,axiom,(
% 0.22/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tsep_1)).
% 0.22/0.51  fof(f151,plain,(
% 0.22/0.51    ( ! [X6,X10,X8,X7,X5,X9] : (~v2_pre_topc(X5) | ~l1_pre_topc(X5) | v2_struct_0(X6) | ~v2_pre_topc(X6) | ~l1_pre_topc(X6) | v2_struct_0(X7) | ~m1_pre_topc(X7,X5) | v2_struct_0(X8) | ~m1_pre_topc(X8,X5) | v2_struct_0(X5) | ~v1_funct_2(sK4,u1_struct_0(X8),u1_struct_0(X6)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(X6)))) | ~m1_pre_topc(X7,X8) | ~m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8))) | ~m1_subset_1(X10,u1_struct_0(X8)) | ~m1_subset_1(X10,u1_struct_0(X7)) | ~r1_tarski(X9,u1_struct_0(X7)) | ~m1_connsp_2(X9,X8,X10) | ~r1_tmap_1(X7,X6,k3_tmap_1(X5,X6,X8,X7,sK4),X10) | r1_tmap_1(X8,X6,sK4,X10)) ) | ~spl9_1),
% 0.22/0.51    inference(resolution,[],[f83,f76])).
% 0.22/0.51  fof(f76,plain,(
% 0.22/0.51    ( ! [X4,X2,X0,X7,X5,X3,X1] : (~v1_funct_1(X4) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X0) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_connsp_2(X5,X3,X7) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X7)) )),
% 0.22/0.51    inference(equality_resolution,[],[f64])).
% 0.22/0.51  fof(f64,plain,(
% 0.22/0.51    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_connsp_2(X5,X3,X6) | X6 != X7 | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f24])).
% 0.22/0.51  fof(f24,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : ((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f23])).
% 0.22/0.51  fof(f23,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | (X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)))) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f11])).
% 0.22/0.51  fof(f11,axiom,(
% 0.22/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & m1_connsp_2(X5,X3,X6) & r1_tarski(X5,u1_struct_0(X2))) => (r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7))))))))))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_tmap_1)).
% 0.22/0.51  fof(f83,plain,(
% 0.22/0.51    v1_funct_1(sK4) | ~spl9_1),
% 0.22/0.51    inference(avatar_component_clause,[],[f81])).
% 0.22/0.51  fof(f218,plain,(
% 0.22/0.51    ~r1_tmap_1(sK3,sK1,sK4,sK5) | spl9_23),
% 0.22/0.51    inference(avatar_component_clause,[],[f217])).
% 0.22/0.51  fof(f335,plain,(
% 0.22/0.51    ~spl9_10 | ~spl9_23 | ~spl9_24),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f334])).
% 0.22/0.51  fof(f334,plain,(
% 0.22/0.51    $false | (~spl9_10 | ~spl9_23 | ~spl9_24)),
% 0.22/0.51    inference(subsumption_resolution,[],[f333,f223])).
% 0.22/0.51  fof(f333,plain,(
% 0.22/0.51    ~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) | (~spl9_10 | ~spl9_23)),
% 0.22/0.51    inference(subsumption_resolution,[],[f202,f219])).
% 0.22/0.51  fof(f219,plain,(
% 0.22/0.51    r1_tmap_1(sK3,sK1,sK4,sK5) | ~spl9_23),
% 0.22/0.51    inference(avatar_component_clause,[],[f217])).
% 0.22/0.51  fof(f202,plain,(
% 0.22/0.51    ~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) | ~r1_tmap_1(sK3,sK1,sK4,sK5) | ~spl9_10),
% 0.22/0.51    inference(forward_demodulation,[],[f35,f128])).
% 0.22/0.51  fof(f128,plain,(
% 0.22/0.51    sK5 = sK6 | ~spl9_10),
% 0.22/0.51    inference(avatar_component_clause,[],[f126])).
% 0.22/0.51  fof(f126,plain,(
% 0.22/0.51    spl9_10 <=> sK5 = sK6),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).
% 0.22/0.51  fof(f35,plain,(
% 0.22/0.51    ~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) | ~r1_tmap_1(sK3,sK1,sK4,sK5)),
% 0.22/0.51    inference(cnf_transformation,[],[f15])).
% 0.22/0.51  fof(f15,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((r1_tmap_1(X3,X1,X4,X5) <~> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f14])).
% 0.22/0.51  fof(f14,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : (((r1_tmap_1(X3,X1,X4,X5) <~> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) & X5 = X6) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & (m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f13])).
% 0.22/0.51  fof(f13,negated_conjecture,(
% 0.22/0.51    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => ((m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (X5 = X6 => (r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)))))))))))),
% 0.22/0.51    inference(negated_conjecture,[],[f12])).
% 0.22/0.51  fof(f12,conjecture,(
% 0.22/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => ((m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (X5 = X6 => (r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)))))))))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_tmap_1)).
% 0.22/0.51  fof(f332,plain,(
% 0.22/0.51    ~spl9_1 | spl9_2 | spl9_3 | spl9_4 | ~spl9_5 | ~spl9_6 | spl9_7 | ~spl9_8 | ~spl9_9 | ~spl9_12 | ~spl9_13 | ~spl9_16 | ~spl9_17 | ~spl9_18 | ~spl9_19 | ~spl9_23 | spl9_24),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f331])).
% 0.22/0.51  fof(f331,plain,(
% 0.22/0.51    $false | (~spl9_1 | spl9_2 | spl9_3 | spl9_4 | ~spl9_5 | ~spl9_6 | spl9_7 | ~spl9_8 | ~spl9_9 | ~spl9_12 | ~spl9_13 | ~spl9_16 | ~spl9_17 | ~spl9_18 | ~spl9_19 | ~spl9_23 | spl9_24)),
% 0.22/0.51    inference(subsumption_resolution,[],[f330,f123])).
% 0.22/0.51  fof(f330,plain,(
% 0.22/0.51    ~l1_pre_topc(sK0) | (~spl9_1 | spl9_2 | spl9_3 | spl9_4 | ~spl9_5 | ~spl9_6 | spl9_7 | ~spl9_8 | ~spl9_12 | ~spl9_13 | ~spl9_16 | ~spl9_17 | ~spl9_18 | ~spl9_19 | ~spl9_23 | spl9_24)),
% 0.22/0.51    inference(subsumption_resolution,[],[f329,f219])).
% 0.22/0.51  fof(f329,plain,(
% 0.22/0.51    ~r1_tmap_1(sK3,sK1,sK4,sK5) | ~l1_pre_topc(sK0) | (~spl9_1 | spl9_2 | spl9_3 | spl9_4 | ~spl9_5 | ~spl9_6 | spl9_7 | ~spl9_8 | ~spl9_12 | ~spl9_13 | ~spl9_16 | ~spl9_17 | ~spl9_18 | ~spl9_19 | spl9_24)),
% 0.22/0.51    inference(subsumption_resolution,[],[f328,f138])).
% 0.22/0.51  fof(f328,plain,(
% 0.22/0.51    ~m1_pre_topc(sK2,sK3) | ~r1_tmap_1(sK3,sK1,sK4,sK5) | ~l1_pre_topc(sK0) | (~spl9_1 | spl9_2 | spl9_3 | spl9_4 | ~spl9_5 | ~spl9_6 | spl9_7 | ~spl9_8 | ~spl9_13 | ~spl9_16 | ~spl9_17 | ~spl9_18 | ~spl9_19 | spl9_24)),
% 0.22/0.51    inference(subsumption_resolution,[],[f327,f193])).
% 0.22/0.51  fof(f327,plain,(
% 0.22/0.51    ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~m1_pre_topc(sK2,sK3) | ~r1_tmap_1(sK3,sK1,sK4,sK5) | ~l1_pre_topc(sK0) | (~spl9_1 | spl9_2 | spl9_3 | spl9_4 | ~spl9_5 | ~spl9_6 | spl9_7 | ~spl9_8 | ~spl9_13 | ~spl9_16 | ~spl9_17 | ~spl9_19 | spl9_24)),
% 0.22/0.51    inference(subsumption_resolution,[],[f326,f180])).
% 0.22/0.51  fof(f326,plain,(
% 0.22/0.51    ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~m1_pre_topc(sK2,sK3) | ~r1_tmap_1(sK3,sK1,sK4,sK5) | ~l1_pre_topc(sK0) | (~spl9_1 | spl9_2 | spl9_3 | spl9_4 | ~spl9_5 | ~spl9_6 | spl9_7 | ~spl9_8 | ~spl9_13 | ~spl9_17 | ~spl9_19 | spl9_24)),
% 0.22/0.51    inference(subsumption_resolution,[],[f325,f118])).
% 0.22/0.51  fof(f325,plain,(
% 0.22/0.51    ~v2_pre_topc(sK0) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~m1_pre_topc(sK2,sK3) | ~r1_tmap_1(sK3,sK1,sK4,sK5) | ~l1_pre_topc(sK0) | (~spl9_1 | spl9_2 | spl9_3 | spl9_4 | ~spl9_5 | ~spl9_6 | spl9_7 | ~spl9_13 | ~spl9_17 | ~spl9_19 | spl9_24)),
% 0.22/0.51    inference(subsumption_resolution,[],[f324,f113])).
% 0.22/0.51  fof(f324,plain,(
% 0.22/0.51    v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~m1_pre_topc(sK2,sK3) | ~r1_tmap_1(sK3,sK1,sK4,sK5) | ~l1_pre_topc(sK0) | (~spl9_1 | spl9_2 | spl9_3 | spl9_4 | ~spl9_5 | ~spl9_6 | ~spl9_13 | ~spl9_17 | ~spl9_19 | spl9_24)),
% 0.22/0.51    inference(subsumption_resolution,[],[f323,f93])).
% 0.22/0.51  fof(f323,plain,(
% 0.22/0.51    v2_struct_0(sK2) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~m1_pre_topc(sK2,sK3) | ~r1_tmap_1(sK3,sK1,sK4,sK5) | ~l1_pre_topc(sK0) | (~spl9_1 | spl9_2 | spl9_4 | ~spl9_5 | ~spl9_6 | ~spl9_13 | ~spl9_17 | ~spl9_19 | spl9_24)),
% 0.22/0.51    inference(subsumption_resolution,[],[f322,f143])).
% 0.22/0.51  fof(f322,plain,(
% 0.22/0.51    ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK2) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~m1_pre_topc(sK2,sK3) | ~r1_tmap_1(sK3,sK1,sK4,sK5) | ~l1_pre_topc(sK0) | (~spl9_1 | spl9_2 | spl9_4 | ~spl9_5 | ~spl9_6 | ~spl9_17 | ~spl9_19 | spl9_24)),
% 0.22/0.51    inference(resolution,[],[f320,f222])).
% 0.22/0.51  fof(f222,plain,(
% 0.22/0.51    ~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) | spl9_24),
% 0.22/0.51    inference(avatar_component_clause,[],[f221])).
% 0.22/0.51  fof(f320,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),X2) | ~m1_pre_topc(sK3,X0) | v2_struct_0(X1) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~m1_pre_topc(X1,sK3) | ~r1_tmap_1(sK3,sK1,sK4,X2) | ~l1_pre_topc(X0)) ) | (~spl9_1 | spl9_2 | spl9_4 | ~spl9_5 | ~spl9_6 | ~spl9_17 | ~spl9_19)),
% 0.22/0.51    inference(subsumption_resolution,[],[f319,f198])).
% 0.22/0.51  fof(f319,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(sK3,X0) | v2_struct_0(X1) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~m1_pre_topc(X1,sK3) | ~r1_tmap_1(sK3,sK1,sK4,X2) | r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),X2)) ) | (~spl9_1 | spl9_2 | spl9_4 | ~spl9_5 | ~spl9_6 | ~spl9_17)),
% 0.22/0.51    inference(subsumption_resolution,[],[f318,f88])).
% 0.22/0.51  fof(f318,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,X0) | v2_struct_0(X1) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~m1_pre_topc(X1,sK3) | ~r1_tmap_1(sK3,sK1,sK4,X2) | r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),X2)) ) | (~spl9_1 | spl9_4 | ~spl9_5 | ~spl9_6 | ~spl9_17)),
% 0.22/0.51    inference(subsumption_resolution,[],[f317,f108])).
% 0.22/0.51  fof(f317,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~l1_pre_topc(sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,X0) | v2_struct_0(X1) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~m1_pre_topc(X1,sK3) | ~r1_tmap_1(sK3,sK1,sK4,X2) | r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),X2)) ) | (~spl9_1 | spl9_4 | ~spl9_5 | ~spl9_17)),
% 0.22/0.51    inference(subsumption_resolution,[],[f316,f103])).
% 0.22/0.51  fof(f316,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,X0) | v2_struct_0(X1) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~m1_pre_topc(X1,sK3) | ~r1_tmap_1(sK3,sK1,sK4,X2) | r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),X2)) ) | (~spl9_1 | spl9_4 | ~spl9_17)),
% 0.22/0.51    inference(subsumption_resolution,[],[f315,f98])).
% 0.22/0.51  fof(f315,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,X0) | v2_struct_0(X1) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~m1_pre_topc(X1,sK3) | ~r1_tmap_1(sK3,sK1,sK4,X2) | r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),X2)) ) | (~spl9_1 | ~spl9_17)),
% 0.22/0.51    inference(resolution,[],[f153,f188])).
% 0.22/0.51  fof(f153,plain,(
% 0.22/0.51    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_2(sK4,u1_struct_0(X2),u1_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~m1_subset_1(X4,u1_struct_0(X2)) | ~m1_subset_1(X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2) | ~r1_tmap_1(X2,X1,sK4,X4) | r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,sK4),X4)) ) | ~spl9_1),
% 0.22/0.51    inference(subsumption_resolution,[],[f150,f68])).
% 0.22/0.51  fof(f150,plain,(
% 0.22/0.51    ( ! [X4,X2,X0,X3,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X0) | ~v1_funct_2(sK4,u1_struct_0(X2),u1_struct_0(X1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~m1_subset_1(X4,u1_struct_0(X2)) | ~m1_subset_1(X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2) | ~r1_tmap_1(X2,X1,sK4,X4) | r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,sK4),X4)) ) | ~spl9_1),
% 0.22/0.51    inference(resolution,[],[f83,f77])).
% 0.22/0.51  fof(f77,plain,(
% 0.22/0.51    ( ! [X6,X4,X2,X0,X3,X1] : (~v1_funct_1(X4) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X0) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2) | ~r1_tmap_1(X2,X1,X4,X6) | r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)) )),
% 0.22/0.51    inference(equality_resolution,[],[f66])).
% 0.22/0.51  fof(f66,plain,(
% 0.22/0.51    ( ! [X6,X4,X2,X0,X5,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~m1_subset_1(X5,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | X5 != X6 | ~m1_pre_topc(X3,X2) | ~r1_tmap_1(X2,X1,X4,X5) | r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f26])).
% 0.22/0.51  fof(f26,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | ~r1_tmap_1(X2,X1,X4,X5) | ~m1_pre_topc(X3,X2) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X2))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f25])).
% 0.22/0.51  fof(f25,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | (~r1_tmap_1(X2,X1,X4,X5) | ~m1_pre_topc(X3,X2) | X5 != X6)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X2))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f10])).
% 0.22/0.51  fof(f10,axiom,(
% 0.22/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X2)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((r1_tmap_1(X2,X1,X4,X5) & m1_pre_topc(X3,X2) & X5 = X6) => r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)))))))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_tmap_1)).
% 0.22/0.51  fof(f314,plain,(
% 0.22/0.51    ~spl9_12 | ~spl9_22 | spl9_28),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f313])).
% 0.22/0.51  fof(f313,plain,(
% 0.22/0.51    $false | (~spl9_12 | ~spl9_22 | spl9_28)),
% 0.22/0.51    inference(subsumption_resolution,[],[f312,f213])).
% 0.22/0.51  fof(f312,plain,(
% 0.22/0.51    ~l1_pre_topc(sK3) | (~spl9_12 | spl9_28)),
% 0.22/0.51    inference(subsumption_resolution,[],[f310,f138])).
% 0.22/0.51  fof(f310,plain,(
% 0.22/0.51    ~m1_pre_topc(sK2,sK3) | ~l1_pre_topc(sK3) | spl9_28),
% 0.22/0.51    inference(resolution,[],[f303,f56])).
% 0.22/0.51  fof(f56,plain,(
% 0.22/0.51    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f18])).
% 0.22/0.51  fof(f18,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f8])).
% 0.22/0.51  fof(f8,axiom,(
% 0.22/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).
% 0.22/0.51  fof(f303,plain,(
% 0.22/0.51    ~m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3))) | spl9_28),
% 0.22/0.51    inference(avatar_component_clause,[],[f301])).
% 0.22/0.51  fof(f307,plain,(
% 0.22/0.51    ~spl9_28 | spl9_29 | spl9_2 | ~spl9_20 | ~spl9_21 | ~spl9_22),
% 0.22/0.51    inference(avatar_split_clause,[],[f289,f212,f208,f204,f86,f305,f301])).
% 0.22/0.51  fof(f289,plain,(
% 0.22/0.51    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK3)) | ~r2_hidden(X0,u1_struct_0(sK2)) | m1_connsp_2(sK8(sK3,u1_struct_0(sK2),X0),sK3,X0) | ~m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))) ) | (spl9_2 | ~spl9_20 | ~spl9_21 | ~spl9_22)),
% 0.22/0.51    inference(resolution,[],[f288,f210])).
% 0.22/0.51  fof(f288,plain,(
% 0.22/0.51    ( ! [X2,X3] : (~v3_pre_topc(X2,sK3) | ~m1_subset_1(X3,u1_struct_0(sK3)) | ~r2_hidden(X3,X2) | m1_connsp_2(sK8(sK3,X2,X3),sK3,X3) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))) ) | (spl9_2 | ~spl9_20 | ~spl9_22)),
% 0.22/0.51    inference(subsumption_resolution,[],[f287,f213])).
% 0.22/0.51  fof(f287,plain,(
% 0.22/0.51    ( ! [X2,X3] : (~l1_pre_topc(sK3) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(X3,u1_struct_0(sK3)) | ~r2_hidden(X3,X2) | m1_connsp_2(sK8(sK3,X2,X3),sK3,X3) | ~v3_pre_topc(X2,sK3)) ) | (spl9_2 | ~spl9_20)),
% 0.22/0.51    inference(subsumption_resolution,[],[f157,f205])).
% 0.22/0.51  fof(f157,plain,(
% 0.22/0.51    ( ! [X2,X3] : (~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(X3,u1_struct_0(sK3)) | ~r2_hidden(X3,X2) | m1_connsp_2(sK8(sK3,X2,X3),sK3,X3) | ~v3_pre_topc(X2,sK3)) ) | spl9_2),
% 0.22/0.51    inference(resolution,[],[f88,f60])).
% 0.22/0.51  fof(f60,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r2_hidden(X2,X1) | m1_connsp_2(sK8(X0,X1,X2),X0,X2) | ~v3_pre_topc(X1,X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f22])).
% 0.22/0.51  fof(f264,plain,(
% 0.22/0.51    ~spl9_9 | ~spl9_14 | spl9_26),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f263])).
% 0.22/0.51  fof(f263,plain,(
% 0.22/0.51    $false | (~spl9_9 | ~spl9_14 | spl9_26)),
% 0.22/0.51    inference(subsumption_resolution,[],[f258,f123])).
% 0.22/0.51  fof(f258,plain,(
% 0.22/0.51    ~l1_pre_topc(sK0) | (~spl9_14 | spl9_26)),
% 0.22/0.51    inference(resolution,[],[f253,f148])).
% 0.22/0.51  fof(f148,plain,(
% 0.22/0.51    m1_pre_topc(sK2,sK0) | ~spl9_14),
% 0.22/0.51    inference(avatar_component_clause,[],[f146])).
% 0.22/0.51  fof(f146,plain,(
% 0.22/0.51    spl9_14 <=> m1_pre_topc(sK2,sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).
% 0.22/0.51  fof(f253,plain,(
% 0.22/0.51    ( ! [X0] : (~m1_pre_topc(sK2,X0) | ~l1_pre_topc(X0)) ) | spl9_26),
% 0.22/0.51    inference(resolution,[],[f247,f55])).
% 0.22/0.51  fof(f55,plain,(
% 0.22/0.51    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f17])).
% 0.22/0.51  fof(f17,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f4])).
% 0.22/0.51  fof(f4,axiom,(
% 0.22/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.22/0.51  fof(f247,plain,(
% 0.22/0.51    ~l1_pre_topc(sK2) | spl9_26),
% 0.22/0.51    inference(avatar_component_clause,[],[f245])).
% 0.22/0.51  fof(f237,plain,(
% 0.22/0.51    ~spl9_8 | ~spl9_9 | ~spl9_13 | spl9_20),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f236])).
% 0.22/0.51  fof(f236,plain,(
% 0.22/0.51    $false | (~spl9_8 | ~spl9_9 | ~spl9_13 | spl9_20)),
% 0.22/0.51    inference(subsumption_resolution,[],[f235,f118])).
% 0.22/0.51  fof(f235,plain,(
% 0.22/0.51    ~v2_pre_topc(sK0) | (~spl9_9 | ~spl9_13 | spl9_20)),
% 0.22/0.51    inference(subsumption_resolution,[],[f232,f123])).
% 0.22/0.51  fof(f232,plain,(
% 0.22/0.51    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl9_13 | spl9_20)),
% 0.22/0.51    inference(resolution,[],[f225,f143])).
% 0.22/0.51  fof(f225,plain,(
% 0.22/0.51    ( ! [X0] : (~m1_pre_topc(sK3,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | spl9_20),
% 0.22/0.51    inference(resolution,[],[f206,f67])).
% 0.22/0.51  fof(f67,plain,(
% 0.22/0.51    ( ! [X0,X1] : (v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f28])).
% 0.22/0.51  fof(f28,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.51    inference(flattening,[],[f27])).
% 0.22/0.51  fof(f27,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f2])).
% 0.22/0.51  fof(f2,axiom,(
% 0.22/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).
% 0.22/0.51  fof(f206,plain,(
% 0.22/0.51    ~v2_pre_topc(sK3) | spl9_20),
% 0.22/0.51    inference(avatar_component_clause,[],[f204])).
% 0.22/0.51  fof(f231,plain,(
% 0.22/0.51    ~spl9_9 | ~spl9_13 | spl9_22),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f230])).
% 0.22/0.51  fof(f230,plain,(
% 0.22/0.51    $false | (~spl9_9 | ~spl9_13 | spl9_22)),
% 0.22/0.51    inference(subsumption_resolution,[],[f227,f123])).
% 0.22/0.51  fof(f227,plain,(
% 0.22/0.51    ~l1_pre_topc(sK0) | (~spl9_13 | spl9_22)),
% 0.22/0.51    inference(resolution,[],[f226,f143])).
% 0.22/0.51  fof(f226,plain,(
% 0.22/0.51    ( ! [X0] : (~m1_pre_topc(sK3,X0) | ~l1_pre_topc(X0)) ) | spl9_22),
% 0.22/0.51    inference(resolution,[],[f214,f55])).
% 0.22/0.51  fof(f214,plain,(
% 0.22/0.51    ~l1_pre_topc(sK3) | spl9_22),
% 0.22/0.51    inference(avatar_component_clause,[],[f212])).
% 0.22/0.51  fof(f224,plain,(
% 0.22/0.51    spl9_23 | spl9_24 | ~spl9_10),
% 0.22/0.51    inference(avatar_split_clause,[],[f200,f126,f221,f217])).
% 0.22/0.51  fof(f200,plain,(
% 0.22/0.51    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) | r1_tmap_1(sK3,sK1,sK4,sK5) | ~spl9_10),
% 0.22/0.51    inference(forward_demodulation,[],[f34,f128])).
% 0.22/0.51  fof(f34,plain,(
% 0.22/0.51    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) | r1_tmap_1(sK3,sK1,sK4,sK5)),
% 0.22/0.51    inference(cnf_transformation,[],[f15])).
% 0.22/0.51  fof(f215,plain,(
% 0.22/0.51    ~spl9_20 | spl9_21 | ~spl9_22 | ~spl9_11 | ~spl9_12),
% 0.22/0.51    inference(avatar_split_clause,[],[f201,f136,f131,f212,f208,f204])).
% 0.22/0.51  fof(f131,plain,(
% 0.22/0.51    spl9_11 <=> v1_tsep_1(sK2,sK3)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).
% 0.22/0.51  fof(f201,plain,(
% 0.22/0.51    ~l1_pre_topc(sK3) | v3_pre_topc(u1_struct_0(sK2),sK3) | ~v2_pre_topc(sK3) | (~spl9_11 | ~spl9_12)),
% 0.22/0.51    inference(subsumption_resolution,[],[f183,f138])).
% 0.22/0.51  fof(f183,plain,(
% 0.22/0.51    ~l1_pre_topc(sK3) | v3_pre_topc(u1_struct_0(sK2),sK3) | ~v2_pre_topc(sK3) | ~m1_pre_topc(sK2,sK3) | ~spl9_11),
% 0.22/0.51    inference(subsumption_resolution,[],[f182,f56])).
% 0.22/0.51  fof(f182,plain,(
% 0.22/0.51    ~l1_pre_topc(sK3) | ~m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3))) | v3_pre_topc(u1_struct_0(sK2),sK3) | ~v2_pre_topc(sK3) | ~m1_pre_topc(sK2,sK3) | ~spl9_11),
% 0.22/0.51    inference(resolution,[],[f133,f79])).
% 0.22/0.51  fof(f79,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~v1_tsep_1(X1,X0) | ~l1_pre_topc(X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(u1_struct_0(X1),X0) | ~v2_pre_topc(X0) | ~m1_pre_topc(X1,X0)) )),
% 0.22/0.51    inference(equality_resolution,[],[f69])).
% 0.22/0.51  fof(f69,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(X1) != X2 | v3_pre_topc(X2,X0) | ~v1_tsep_1(X1,X0) | ~m1_pre_topc(X1,X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f32])).
% 0.22/0.51  fof(f32,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.51    inference(flattening,[],[f31])).
% 0.22/0.51  fof(f31,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f7])).
% 0.22/0.51  fof(f7,axiom,(
% 0.22/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_tsep_1)).
% 0.22/0.51  fof(f133,plain,(
% 0.22/0.51    v1_tsep_1(sK2,sK3) | ~spl9_11),
% 0.22/0.51    inference(avatar_component_clause,[],[f131])).
% 0.22/0.51  fof(f199,plain,(
% 0.22/0.51    spl9_19),
% 0.22/0.51    inference(avatar_split_clause,[],[f41,f196])).
% 0.22/0.51  fof(f41,plain,(
% 0.22/0.51    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 0.22/0.51    inference(cnf_transformation,[],[f15])).
% 0.22/0.51  fof(f194,plain,(
% 0.22/0.51    spl9_18 | ~spl9_10 | ~spl9_15),
% 0.22/0.51    inference(avatar_split_clause,[],[f184,f173,f126,f191])).
% 0.22/0.51  fof(f173,plain,(
% 0.22/0.51    spl9_15 <=> m1_subset_1(sK6,u1_struct_0(sK2))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).
% 0.22/0.51  fof(f184,plain,(
% 0.22/0.51    m1_subset_1(sK5,u1_struct_0(sK2)) | (~spl9_10 | ~spl9_15)),
% 0.22/0.51    inference(forward_demodulation,[],[f175,f128])).
% 0.22/0.51  fof(f175,plain,(
% 0.22/0.51    m1_subset_1(sK6,u1_struct_0(sK2)) | ~spl9_15),
% 0.22/0.51    inference(avatar_component_clause,[],[f173])).
% 0.22/0.51  fof(f189,plain,(
% 0.22/0.51    spl9_17),
% 0.22/0.51    inference(avatar_split_clause,[],[f40,f186])).
% 0.22/0.51  fof(f40,plain,(
% 0.22/0.51    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))),
% 0.22/0.51    inference(cnf_transformation,[],[f15])).
% 0.22/0.51  % (14576)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.52  % (14573)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  % (14581)Refutation not found, incomplete strategy% (14581)------------------------------
% 0.22/0.52  % (14581)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (14581)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (14581)Memory used [KB]: 10618
% 0.22/0.52  % (14581)Time elapsed: 0.093 s
% 0.22/0.52  % (14581)------------------------------
% 0.22/0.52  % (14581)------------------------------
% 0.22/0.52  % (14571)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.52  % (14569)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.52  % (14572)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.52  % (14579)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.53  fof(f181,plain,(
% 0.22/0.53    spl9_16),
% 0.22/0.53    inference(avatar_split_clause,[],[f38,f178])).
% 0.22/0.53  fof(f38,plain,(
% 0.22/0.53    m1_subset_1(sK5,u1_struct_0(sK3))),
% 0.22/0.53    inference(cnf_transformation,[],[f15])).
% 0.22/0.53  fof(f176,plain,(
% 0.22/0.53    spl9_15),
% 0.22/0.53    inference(avatar_split_clause,[],[f36,f173])).
% 0.22/0.53  fof(f36,plain,(
% 0.22/0.53    m1_subset_1(sK6,u1_struct_0(sK2))),
% 0.22/0.53    inference(cnf_transformation,[],[f15])).
% 0.22/0.53  fof(f149,plain,(
% 0.22/0.53    spl9_14),
% 0.22/0.53    inference(avatar_split_clause,[],[f47,f146])).
% 0.22/0.53  fof(f47,plain,(
% 0.22/0.53    m1_pre_topc(sK2,sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f15])).
% 0.22/0.53  fof(f144,plain,(
% 0.22/0.53    spl9_13),
% 0.22/0.53    inference(avatar_split_clause,[],[f45,f141])).
% 0.22/0.53  fof(f45,plain,(
% 0.22/0.53    m1_pre_topc(sK3,sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f15])).
% 0.22/0.53  fof(f139,plain,(
% 0.22/0.53    spl9_12),
% 0.22/0.53    inference(avatar_split_clause,[],[f43,f136])).
% 0.22/0.53  fof(f43,plain,(
% 0.22/0.53    m1_pre_topc(sK2,sK3)),
% 0.22/0.53    inference(cnf_transformation,[],[f15])).
% 0.22/0.53  fof(f134,plain,(
% 0.22/0.53    spl9_11),
% 0.22/0.53    inference(avatar_split_clause,[],[f42,f131])).
% 0.22/0.53  fof(f42,plain,(
% 0.22/0.53    v1_tsep_1(sK2,sK3)),
% 0.22/0.53    inference(cnf_transformation,[],[f15])).
% 0.22/0.53  fof(f129,plain,(
% 0.22/0.53    spl9_10),
% 0.22/0.53    inference(avatar_split_clause,[],[f37,f126])).
% 0.22/0.53  fof(f37,plain,(
% 0.22/0.53    sK5 = sK6),
% 0.22/0.53    inference(cnf_transformation,[],[f15])).
% 0.22/0.53  fof(f124,plain,(
% 0.22/0.53    spl9_9),
% 0.22/0.53    inference(avatar_split_clause,[],[f53,f121])).
% 0.22/0.53  fof(f53,plain,(
% 0.22/0.53    l1_pre_topc(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f15])).
% 0.22/0.53  fof(f119,plain,(
% 0.22/0.53    spl9_8),
% 0.22/0.53    inference(avatar_split_clause,[],[f52,f116])).
% 0.22/0.53  fof(f52,plain,(
% 0.22/0.53    v2_pre_topc(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f15])).
% 0.22/0.53  fof(f114,plain,(
% 0.22/0.53    ~spl9_7),
% 0.22/0.53    inference(avatar_split_clause,[],[f51,f111])).
% 0.22/0.53  fof(f51,plain,(
% 0.22/0.53    ~v2_struct_0(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f15])).
% 0.22/0.53  fof(f109,plain,(
% 0.22/0.53    spl9_6),
% 0.22/0.53    inference(avatar_split_clause,[],[f50,f106])).
% 0.22/0.53  fof(f50,plain,(
% 0.22/0.53    l1_pre_topc(sK1)),
% 0.22/0.53    inference(cnf_transformation,[],[f15])).
% 0.22/0.53  fof(f104,plain,(
% 0.22/0.53    spl9_5),
% 0.22/0.53    inference(avatar_split_clause,[],[f49,f101])).
% 0.22/0.53  fof(f49,plain,(
% 0.22/0.53    v2_pre_topc(sK1)),
% 0.22/0.53    inference(cnf_transformation,[],[f15])).
% 0.22/0.53  fof(f99,plain,(
% 0.22/0.53    ~spl9_4),
% 0.22/0.53    inference(avatar_split_clause,[],[f48,f96])).
% 0.22/0.53  fof(f48,plain,(
% 0.22/0.53    ~v2_struct_0(sK1)),
% 0.22/0.53    inference(cnf_transformation,[],[f15])).
% 0.22/0.53  fof(f94,plain,(
% 0.22/0.53    ~spl9_3),
% 0.22/0.53    inference(avatar_split_clause,[],[f46,f91])).
% 0.22/0.53  fof(f46,plain,(
% 0.22/0.53    ~v2_struct_0(sK2)),
% 0.22/0.53    inference(cnf_transformation,[],[f15])).
% 0.22/0.53  fof(f89,plain,(
% 0.22/0.53    ~spl9_2),
% 0.22/0.53    inference(avatar_split_clause,[],[f44,f86])).
% 0.22/0.53  fof(f44,plain,(
% 0.22/0.53    ~v2_struct_0(sK3)),
% 0.22/0.53    inference(cnf_transformation,[],[f15])).
% 0.22/0.53  fof(f84,plain,(
% 0.22/0.53    spl9_1),
% 0.22/0.53    inference(avatar_split_clause,[],[f39,f81])).
% 0.22/0.53  fof(f39,plain,(
% 0.22/0.53    v1_funct_1(sK4)),
% 0.22/0.53    inference(cnf_transformation,[],[f15])).
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (14563)------------------------------
% 0.22/0.53  % (14563)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (14563)Termination reason: Refutation
% 0.22/0.53  
% 0.22/0.53  % (14563)Memory used [KB]: 10874
% 0.22/0.53  % (14563)Time elapsed: 0.102 s
% 0.22/0.53  % (14563)------------------------------
% 0.22/0.53  % (14563)------------------------------
% 0.22/0.53  % (14555)Success in time 0.172 s
%------------------------------------------------------------------------------
