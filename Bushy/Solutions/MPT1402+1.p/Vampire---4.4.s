%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : connsp_2__t32_connsp_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:35:53 EDT 2019

% Result     : Theorem 1.44s
% Output     : Refutation 1.44s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 221 expanded)
%              Number of leaves         :   16 (  86 expanded)
%              Depth                    :   13
%              Number of atoms          :  490 ( 901 expanded)
%              Number of equality atoms :   18 (  43 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f373,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f97,f104,f111,f125,f132,f143,f187,f254,f262,f285,f364,f372])).

fof(f372,plain,
    ( ~ spl9_2
    | ~ spl9_4
    | spl9_9
    | ~ spl9_14
    | ~ spl9_18
    | spl9_39 ),
    inference(avatar_contradiction_clause,[],[f371])).

fof(f371,plain,
    ( $false
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_9
    | ~ spl9_14
    | ~ spl9_18
    | ~ spl9_39 ),
    inference(subsumption_resolution,[],[f370,f131])).

fof(f131,plain,
    ( ~ v4_pre_topc(k1_connsp_2(sK0,sK1),sK0)
    | ~ spl9_9 ),
    inference(avatar_component_clause,[],[f130])).

fof(f130,plain,
    ( spl9_9
  <=> ~ v4_pre_topc(k1_connsp_2(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).

fof(f370,plain,
    ( v4_pre_topc(k1_connsp_2(sK0,sK1),sK0)
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_14
    | ~ spl9_18
    | ~ spl9_39 ),
    inference(forward_demodulation,[],[f369,f186])).

fof(f186,plain,
    ( k1_connsp_2(sK0,sK1) = k6_setfam_1(u1_struct_0(sK0),sK2(sK0,sK1,k1_connsp_2(sK0,sK1)))
    | ~ spl9_14 ),
    inference(avatar_component_clause,[],[f185])).

fof(f185,plain,
    ( spl9_14
  <=> k1_connsp_2(sK0,sK1) = k6_setfam_1(u1_struct_0(sK0),sK2(sK0,sK1,k1_connsp_2(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).

fof(f369,plain,
    ( v4_pre_topc(k6_setfam_1(u1_struct_0(sK0),sK2(sK0,sK1,k1_connsp_2(sK0,sK1))),sK0)
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_18
    | ~ spl9_39 ),
    inference(subsumption_resolution,[],[f368,f103])).

fof(f103,plain,
    ( v2_pre_topc(sK0)
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl9_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f368,plain,
    ( ~ v2_pre_topc(sK0)
    | v4_pre_topc(k6_setfam_1(u1_struct_0(sK0),sK2(sK0,sK1,k1_connsp_2(sK0,sK1))),sK0)
    | ~ spl9_4
    | ~ spl9_18
    | ~ spl9_39 ),
    inference(subsumption_resolution,[],[f367,f244])).

fof(f244,plain,
    ( m1_subset_1(sK2(sK0,sK1,k1_connsp_2(sK0,sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl9_18 ),
    inference(avatar_component_clause,[],[f243])).

fof(f243,plain,
    ( spl9_18
  <=> m1_subset_1(sK2(sK0,sK1,k1_connsp_2(sK0,sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).

fof(f367,plain,
    ( ~ m1_subset_1(sK2(sK0,sK1,k1_connsp_2(sK0,sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ v2_pre_topc(sK0)
    | v4_pre_topc(k6_setfam_1(u1_struct_0(sK0),sK2(sK0,sK1,k1_connsp_2(sK0,sK1))),sK0)
    | ~ spl9_4
    | ~ spl9_39 ),
    inference(subsumption_resolution,[],[f366,f110])).

fof(f110,plain,
    ( l1_pre_topc(sK0)
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f109])).

fof(f109,plain,
    ( spl9_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f366,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK2(sK0,sK1,k1_connsp_2(sK0,sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ v2_pre_topc(sK0)
    | v4_pre_topc(k6_setfam_1(u1_struct_0(sK0),sK2(sK0,sK1,k1_connsp_2(sK0,sK1))),sK0)
    | ~ spl9_39 ),
    inference(resolution,[],[f363,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ v2_pre_topc(X0)
      | v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0)
          | ? [X2] :
              ( ~ v4_pre_topc(X2,X0)
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0)
          | ? [X2] :
              ( ~ v4_pre_topc(X2,X0)
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( r2_hidden(X2,X1)
                 => v4_pre_topc(X2,X0) ) )
           => v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t32_connsp_2.p',t44_pre_topc)).

fof(f363,plain,
    ( ~ m1_subset_1(sK5(sK0,sK2(sK0,sK1,k1_connsp_2(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl9_39 ),
    inference(avatar_component_clause,[],[f362])).

fof(f362,plain,
    ( spl9_39
  <=> ~ m1_subset_1(sK5(sK0,sK2(sK0,sK1,k1_connsp_2(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_39])])).

fof(f364,plain,
    ( ~ spl9_39
    | spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_10
    | spl9_21
    | ~ spl9_24 ),
    inference(avatar_split_clause,[],[f290,f283,f252,f141,f123,f109,f102,f95,f362])).

fof(f95,plain,
    ( spl9_1
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f123,plain,
    ( spl9_6
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f141,plain,
    ( spl9_10
  <=> m1_subset_1(k1_connsp_2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).

fof(f252,plain,
    ( spl9_21
  <=> ~ v4_pre_topc(sK5(sK0,sK2(sK0,sK1,k1_connsp_2(sK0,sK1))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_21])])).

fof(f283,plain,
    ( spl9_24
  <=> r2_hidden(sK5(sK0,sK2(sK0,sK1,k1_connsp_2(sK0,sK1))),sK2(sK0,sK1,k1_connsp_2(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_24])])).

fof(f290,plain,
    ( ~ m1_subset_1(sK5(sK0,sK2(sK0,sK1,k1_connsp_2(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_10
    | ~ spl9_21
    | ~ spl9_24 ),
    inference(subsumption_resolution,[],[f286,f255])).

fof(f255,plain,
    ( ! [X0] : ~ sP4(sK5(sK0,sK2(sK0,sK1,k1_connsp_2(sK0,sK1))),X0,sK0)
    | ~ spl9_21 ),
    inference(resolution,[],[f253,f57])).

fof(f57,plain,(
    ! [X4,X0,X1] :
      ( v4_pre_topc(X4,X0)
      | ~ sP4(X4,X1,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_connsp_2(X0,X1) = X2
              <=> ? [X3] :
                    ( k6_setfam_1(u1_struct_0(X0),X3) = X2
                    & ! [X4] :
                        ( ( r2_hidden(X4,X3)
                        <=> ( r2_hidden(X1,X4)
                            & v4_pre_topc(X4,X0)
                            & v3_pre_topc(X4,X0) ) )
                        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                    & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_connsp_2(X0,X1) = X2
              <=> ? [X3] :
                    ( k6_setfam_1(u1_struct_0(X0),X3) = X2
                    & ! [X4] :
                        ( ( r2_hidden(X4,X3)
                        <=> ( r2_hidden(X1,X4)
                            & v4_pre_topc(X4,X0)
                            & v3_pre_topc(X4,X0) ) )
                        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                    & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( k1_connsp_2(X0,X1) = X2
              <=> ? [X3] :
                    ( k6_setfam_1(u1_struct_0(X0),X3) = X2
                    & ! [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
                       => ( r2_hidden(X4,X3)
                        <=> ( r2_hidden(X1,X4)
                            & v4_pre_topc(X4,X0)
                            & v3_pre_topc(X4,X0) ) ) )
                    & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t32_connsp_2.p',d7_connsp_2)).

fof(f253,plain,
    ( ~ v4_pre_topc(sK5(sK0,sK2(sK0,sK1,k1_connsp_2(sK0,sK1))),sK0)
    | ~ spl9_21 ),
    inference(avatar_component_clause,[],[f252])).

fof(f286,plain,
    ( sP4(sK5(sK0,sK2(sK0,sK1,k1_connsp_2(sK0,sK1))),sK1,sK0)
    | ~ m1_subset_1(sK5(sK0,sK2(sK0,sK1,k1_connsp_2(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_10
    | ~ spl9_24 ),
    inference(resolution,[],[f284,f154])).

fof(f154,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK2(sK0,sK1,k1_connsp_2(sK0,sK1)))
        | sP4(X1,sK1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_10 ),
    inference(subsumption_resolution,[],[f153,f96])).

fof(f96,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f95])).

fof(f153,plain,
    ( ! [X1] :
        ( v2_struct_0(sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | sP4(X1,sK1,sK0)
        | ~ r2_hidden(X1,sK2(sK0,sK1,k1_connsp_2(sK0,sK1))) )
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_10 ),
    inference(subsumption_resolution,[],[f152,f124])).

fof(f124,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl9_6 ),
    inference(avatar_component_clause,[],[f123])).

fof(f152,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | sP4(X1,sK1,sK0)
        | ~ r2_hidden(X1,sK2(sK0,sK1,k1_connsp_2(sK0,sK1))) )
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_10 ),
    inference(subsumption_resolution,[],[f151,f110])).

fof(f151,plain,
    ( ! [X1] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | sP4(X1,sK1,sK0)
        | ~ r2_hidden(X1,sK2(sK0,sK1,k1_connsp_2(sK0,sK1))) )
    | ~ spl9_2
    | ~ spl9_10 ),
    inference(subsumption_resolution,[],[f145,f103])).

fof(f145,plain,
    ( ! [X1] :
        ( ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | sP4(X1,sK1,sK0)
        | ~ r2_hidden(X1,sK2(sK0,sK1,k1_connsp_2(sK0,sK1))) )
    | ~ spl9_10 ),
    inference(resolution,[],[f142,f89])).

fof(f89,plain,(
    ! [X4,X0,X1] :
      ( ~ m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | sP4(X4,X1,X0)
      | ~ r2_hidden(X4,sK2(X0,X1,k1_connsp_2(X0,X1))) ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X4,X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | sP4(X4,X1,X0)
      | ~ r2_hidden(X4,sK2(X0,X1,X2))
      | k1_connsp_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f142,plain,
    ( m1_subset_1(k1_connsp_2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl9_10 ),
    inference(avatar_component_clause,[],[f141])).

fof(f284,plain,
    ( r2_hidden(sK5(sK0,sK2(sK0,sK1,k1_connsp_2(sK0,sK1))),sK2(sK0,sK1,k1_connsp_2(sK0,sK1)))
    | ~ spl9_24 ),
    inference(avatar_component_clause,[],[f283])).

fof(f285,plain,
    ( spl9_24
    | ~ spl9_2
    | ~ spl9_4
    | spl9_9
    | ~ spl9_14
    | ~ spl9_18 ),
    inference(avatar_split_clause,[],[f278,f243,f185,f130,f109,f102,f283])).

fof(f278,plain,
    ( r2_hidden(sK5(sK0,sK2(sK0,sK1,k1_connsp_2(sK0,sK1))),sK2(sK0,sK1,k1_connsp_2(sK0,sK1)))
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_9
    | ~ spl9_14
    | ~ spl9_18 ),
    inference(subsumption_resolution,[],[f209,f244])).

fof(f209,plain,
    ( r2_hidden(sK5(sK0,sK2(sK0,sK1,k1_connsp_2(sK0,sK1))),sK2(sK0,sK1,k1_connsp_2(sK0,sK1)))
    | ~ m1_subset_1(sK2(sK0,sK1,k1_connsp_2(sK0,sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_9
    | ~ spl9_14 ),
    inference(subsumption_resolution,[],[f192,f131])).

fof(f192,plain,
    ( v4_pre_topc(k1_connsp_2(sK0,sK1),sK0)
    | r2_hidden(sK5(sK0,sK2(sK0,sK1,k1_connsp_2(sK0,sK1))),sK2(sK0,sK1,k1_connsp_2(sK0,sK1)))
    | ~ m1_subset_1(sK2(sK0,sK1,k1_connsp_2(sK0,sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_14 ),
    inference(superposition,[],[f117,f186])).

fof(f117,plain,
    ( ! [X1] :
        ( v4_pre_topc(k6_setfam_1(u1_struct_0(sK0),X1),sK0)
        | r2_hidden(sK5(sK0,X1),X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
    | ~ spl9_2
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f113,f103])).

fof(f113,plain,
    ( ! [X1] :
        ( ~ v2_pre_topc(sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | r2_hidden(sK5(sK0,X1),X1)
        | v4_pre_topc(k6_setfam_1(u1_struct_0(sK0),X1),sK0) )
    | ~ spl9_4 ),
    inference(resolution,[],[f110,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | r2_hidden(sK5(X0,X1),X1)
      | v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f262,plain,
    ( spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_10
    | spl9_19 ),
    inference(avatar_contradiction_clause,[],[f261])).

fof(f261,plain,
    ( $false
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_10
    | ~ spl9_19 ),
    inference(subsumption_resolution,[],[f260,f96])).

fof(f260,plain,
    ( v2_struct_0(sK0)
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_10
    | ~ spl9_19 ),
    inference(subsumption_resolution,[],[f259,f142])).

fof(f259,plain,
    ( ~ m1_subset_1(k1_connsp_2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_19 ),
    inference(subsumption_resolution,[],[f258,f124])).

fof(f258,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(k1_connsp_2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_19 ),
    inference(subsumption_resolution,[],[f257,f110])).

fof(f257,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(k1_connsp_2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl9_2
    | ~ spl9_19 ),
    inference(subsumption_resolution,[],[f256,f103])).

fof(f256,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(k1_connsp_2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl9_19 ),
    inference(resolution,[],[f247,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK2(X0,X1,k1_connsp_2(X0,X1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | k1_connsp_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f247,plain,
    ( ~ m1_subset_1(sK2(sK0,sK1,k1_connsp_2(sK0,sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl9_19 ),
    inference(avatar_component_clause,[],[f246])).

fof(f246,plain,
    ( spl9_19
  <=> ~ m1_subset_1(sK2(sK0,sK1,k1_connsp_2(sK0,sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_19])])).

fof(f254,plain,
    ( ~ spl9_19
    | ~ spl9_21
    | ~ spl9_2
    | ~ spl9_4
    | spl9_9
    | ~ spl9_14 ),
    inference(avatar_split_clause,[],[f208,f185,f130,f109,f102,f252,f246])).

fof(f208,plain,
    ( ~ v4_pre_topc(sK5(sK0,sK2(sK0,sK1,k1_connsp_2(sK0,sK1))),sK0)
    | ~ m1_subset_1(sK2(sK0,sK1,k1_connsp_2(sK0,sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_9
    | ~ spl9_14 ),
    inference(subsumption_resolution,[],[f191,f131])).

fof(f191,plain,
    ( v4_pre_topc(k1_connsp_2(sK0,sK1),sK0)
    | ~ v4_pre_topc(sK5(sK0,sK2(sK0,sK1,k1_connsp_2(sK0,sK1))),sK0)
    | ~ m1_subset_1(sK2(sK0,sK1,k1_connsp_2(sK0,sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_14 ),
    inference(superposition,[],[f118,f186])).

fof(f118,plain,
    ( ! [X2] :
        ( v4_pre_topc(k6_setfam_1(u1_struct_0(sK0),X2),sK0)
        | ~ v4_pre_topc(sK5(sK0,X2),sK0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
    | ~ spl9_2
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f114,f103])).

fof(f114,plain,
    ( ! [X2] :
        ( ~ v2_pre_topc(sK0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ v4_pre_topc(sK5(sK0,X2),sK0)
        | v4_pre_topc(k6_setfam_1(u1_struct_0(sK0),X2),sK0) )
    | ~ spl9_4 ),
    inference(resolution,[],[f110,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ v4_pre_topc(sK5(X0,X1),X0)
      | v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f187,plain,
    ( spl9_14
    | spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_10 ),
    inference(avatar_split_clause,[],[f158,f141,f123,f109,f102,f95,f185])).

fof(f158,plain,
    ( k1_connsp_2(sK0,sK1) = k6_setfam_1(u1_struct_0(sK0),sK2(sK0,sK1,k1_connsp_2(sK0,sK1)))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_10 ),
    inference(subsumption_resolution,[],[f157,f96])).

fof(f157,plain,
    ( v2_struct_0(sK0)
    | k1_connsp_2(sK0,sK1) = k6_setfam_1(u1_struct_0(sK0),sK2(sK0,sK1,k1_connsp_2(sK0,sK1)))
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_10 ),
    inference(subsumption_resolution,[],[f156,f124])).

fof(f156,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | k1_connsp_2(sK0,sK1) = k6_setfam_1(u1_struct_0(sK0),sK2(sK0,sK1,k1_connsp_2(sK0,sK1)))
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_10 ),
    inference(subsumption_resolution,[],[f155,f110])).

fof(f155,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | k1_connsp_2(sK0,sK1) = k6_setfam_1(u1_struct_0(sK0),sK2(sK0,sK1,k1_connsp_2(sK0,sK1)))
    | ~ spl9_2
    | ~ spl9_10 ),
    inference(subsumption_resolution,[],[f146,f103])).

fof(f146,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | k1_connsp_2(sK0,sK1) = k6_setfam_1(u1_struct_0(sK0),sK2(sK0,sK1,k1_connsp_2(sK0,sK1)))
    | ~ spl9_10 ),
    inference(resolution,[],[f142,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0)
      | k1_connsp_2(X0,X1) = k6_setfam_1(u1_struct_0(X0),sK2(X0,X1,k1_connsp_2(X0,X1))) ) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | k6_setfam_1(u1_struct_0(X0),sK2(X0,X1,X2)) = X2
      | k1_connsp_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f143,plain,
    ( spl9_10
    | spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_6 ),
    inference(avatar_split_clause,[],[f135,f123,f109,f102,f95,f141])).

fof(f135,plain,
    ( m1_subset_1(k1_connsp_2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_6 ),
    inference(resolution,[],[f116,f124])).

fof(f116,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | m1_subset_1(k1_connsp_2(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f115,f96])).

fof(f115,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | m1_subset_1(k1_connsp_2(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl9_2
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f112,f103])).

fof(f112,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | m1_subset_1(k1_connsp_2(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl9_4 ),
    inference(resolution,[],[f110,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t32_connsp_2.p',dt_k1_connsp_2)).

fof(f132,plain,(
    ~ spl9_9 ),
    inference(avatar_split_clause,[],[f49,f130])).

fof(f49,plain,(
    ~ v4_pre_topc(k1_connsp_2(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v4_pre_topc(k1_connsp_2(X0,X1),X0)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v4_pre_topc(k1_connsp_2(X0,X1),X0)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => v4_pre_topc(k1_connsp_2(X0,X1),X0) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => v4_pre_topc(k1_connsp_2(X0,X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t32_connsp_2.p',t32_connsp_2)).

fof(f125,plain,(
    spl9_6 ),
    inference(avatar_split_clause,[],[f48,f123])).

fof(f48,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f28])).

fof(f111,plain,(
    spl9_4 ),
    inference(avatar_split_clause,[],[f52,f109])).

fof(f52,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f104,plain,(
    spl9_2 ),
    inference(avatar_split_clause,[],[f51,f102])).

fof(f51,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f97,plain,(
    ~ spl9_1 ),
    inference(avatar_split_clause,[],[f50,f95])).

fof(f50,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
