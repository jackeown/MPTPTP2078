%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tops_2__t36_tops_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:39 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 190 expanded)
%              Number of leaves         :   18 (  70 expanded)
%              Depth                    :   14
%              Number of atoms          :  349 ( 710 expanded)
%              Number of equality atoms :   11 (  42 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f366,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f73,f78,f82,f87,f91,f95,f103,f108,f116,f147,f155,f172,f234,f365])).

fof(f365,plain,
    ( ~ spl8_0
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_14
    | ~ spl8_22
    | spl8_27
    | ~ spl8_30
    | ~ spl8_52 ),
    inference(avatar_contradiction_clause,[],[f364])).

fof(f364,plain,
    ( $false
    | ~ spl8_0
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_14
    | ~ spl8_22
    | ~ spl8_27
    | ~ spl8_30
    | ~ spl8_52 ),
    inference(subsumption_resolution,[],[f363,f154])).

fof(f154,plain,
    ( ~ v4_pre_topc(sK4(sK2,sK1),sK2)
    | ~ spl8_27 ),
    inference(avatar_component_clause,[],[f153])).

fof(f153,plain,
    ( spl8_27
  <=> ~ v4_pre_topc(sK4(sK2,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).

fof(f363,plain,
    ( v4_pre_topc(sK4(sK2,sK1),sK2)
    | ~ spl8_0
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_14
    | ~ spl8_22
    | ~ spl8_30
    | ~ spl8_52 ),
    inference(subsumption_resolution,[],[f361,f86])).

fof(f86,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl8_6
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f361,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v4_pre_topc(sK4(sK2,sK1),sK2)
    | ~ spl8_0
    | ~ spl8_8
    | ~ spl8_14
    | ~ spl8_22
    | ~ spl8_30
    | ~ spl8_52 ),
    inference(resolution,[],[f248,f171])).

fof(f171,plain,
    ( m1_subset_1(sK4(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl8_30 ),
    inference(avatar_component_clause,[],[f170])).

fof(f170,plain,
    ( spl8_30
  <=> m1_subset_1(sK4(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_30])])).

fof(f248,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK4(sK2,sK1),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_pre_topc(X0,sK0)
        | v4_pre_topc(sK4(sK2,sK1),X0) )
    | ~ spl8_0
    | ~ spl8_8
    | ~ spl8_14
    | ~ spl8_22
    | ~ spl8_52 ),
    inference(subsumption_resolution,[],[f247,f246])).

fof(f246,plain,
    ( v4_pre_topc(sK4(sK2,sK1),sK0)
    | ~ spl8_0
    | ~ spl8_8
    | ~ spl8_14
    | ~ spl8_22
    | ~ spl8_52 ),
    inference(subsumption_resolution,[],[f243,f146])).

fof(f146,plain,
    ( r2_hidden(sK4(sK2,sK1),sK1)
    | ~ spl8_22 ),
    inference(avatar_component_clause,[],[f145])).

fof(f145,plain,
    ( spl8_22
  <=> r2_hidden(sK4(sK2,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).

fof(f243,plain,
    ( ~ r2_hidden(sK4(sK2,sK1),sK1)
    | v4_pre_topc(sK4(sK2,sK1),sK0)
    | ~ spl8_0
    | ~ spl8_8
    | ~ spl8_14
    | ~ spl8_52 ),
    inference(resolution,[],[f233,f127])).

fof(f127,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X0,sK1)
        | v4_pre_topc(X0,sK0) )
    | ~ spl8_0
    | ~ spl8_8
    | ~ spl8_14 ),
    inference(subsumption_resolution,[],[f126,f90])).

fof(f90,plain,
    ( v2_tops_2(sK1,sK0)
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl8_8
  <=> v2_tops_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f126,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X0,sK1)
        | v4_pre_topc(X0,sK0)
        | ~ v2_tops_2(sK1,sK0) )
    | ~ spl8_0
    | ~ spl8_14 ),
    inference(subsumption_resolution,[],[f121,f72])).

fof(f72,plain,
    ( l1_pre_topc(sK0)
    | ~ spl8_0 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl8_0
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_0])])).

fof(f121,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X0,sK1)
        | v4_pre_topc(X0,sK0)
        | ~ v2_tops_2(sK1,sK0) )
    | ~ spl8_14 ),
    inference(resolution,[],[f107,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X2,X1)
      | v4_pre_topc(X2,X0)
      | ~ v2_tops_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_2(X1,X0)
          <=> ! [X2] :
                ( v4_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_2(X1,X0)
          <=> ! [X2] :
                ( v4_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v2_tops_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( r2_hidden(X2,X1)
                 => v4_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t36_tops_2.p',d2_tops_2)).

fof(f107,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl8_14 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl8_14
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f233,plain,
    ( m1_subset_1(sK4(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_52 ),
    inference(avatar_component_clause,[],[f232])).

fof(f232,plain,
    ( spl8_52
  <=> m1_subset_1(sK4(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_52])])).

fof(f247,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | ~ v4_pre_topc(sK4(sK2,sK1),sK0)
        | ~ m1_subset_1(sK4(sK2,sK1),k1_zfmisc_1(u1_struct_0(X0)))
        | v4_pre_topc(sK4(sK2,sK1),X0) )
    | ~ spl8_0
    | ~ spl8_52 ),
    inference(subsumption_resolution,[],[f244,f72])).

fof(f244,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ v4_pre_topc(sK4(sK2,sK1),sK0)
        | ~ m1_subset_1(sK4(sK2,sK1),k1_zfmisc_1(u1_struct_0(X0)))
        | v4_pre_topc(sK4(sK2,sK1),X0) )
    | ~ spl8_52 ),
    inference(resolution,[],[f233,f68])).

fof(f68,plain,(
    ! [X2,X0,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ v4_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | v4_pre_topc(X3,X2) ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X2,X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | X1 != X3
      | v4_pre_topc(X3,X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v4_pre_topc(X3,X2)
                  | X1 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              | ~ v4_pre_topc(X1,X0)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v4_pre_topc(X3,X2)
                  | X1 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              | ~ v4_pre_topc(X1,X0)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( v4_pre_topc(X1,X0)
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
                   => ( X1 = X3
                     => v4_pre_topc(X3,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t36_tops_2.p',t34_tops_2)).

fof(f234,plain,
    ( spl8_52
    | ~ spl8_0
    | ~ spl8_6
    | ~ spl8_30 ),
    inference(avatar_split_clause,[],[f181,f170,f85,f71,f232])).

fof(f181,plain,
    ( m1_subset_1(sK4(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_0
    | ~ spl8_6
    | ~ spl8_30 ),
    inference(resolution,[],[f99,f171])).

fof(f99,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
        | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl8_0
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f97,f72])).

fof(f97,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
        | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl8_6 ),
    inference(resolution,[],[f86,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t36_tops_2.p',t39_pre_topc)).

fof(f172,plain,
    ( spl8_30
    | spl8_11
    | ~ spl8_12
    | ~ spl8_18 ),
    inference(avatar_split_clause,[],[f138,f114,f101,f93,f170])).

fof(f93,plain,
    ( spl8_11
  <=> ~ v2_tops_2(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f101,plain,
    ( spl8_12
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f114,plain,
    ( spl8_18
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f138,plain,
    ( m1_subset_1(sK4(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl8_11
    | ~ spl8_12
    | ~ spl8_18 ),
    inference(subsumption_resolution,[],[f137,f94])).

fof(f94,plain,
    ( ~ v2_tops_2(sK1,sK2)
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f93])).

fof(f137,plain,
    ( m1_subset_1(sK4(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_tops_2(sK1,sK2)
    | ~ spl8_12
    | ~ spl8_18 ),
    inference(subsumption_resolution,[],[f133,f102])).

fof(f102,plain,
    ( l1_pre_topc(sK2)
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f101])).

fof(f133,plain,
    ( ~ l1_pre_topc(sK2)
    | m1_subset_1(sK4(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_tops_2(sK1,sK2)
    | ~ spl8_18 ),
    inference(resolution,[],[f115,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tops_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f115,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ spl8_18 ),
    inference(avatar_component_clause,[],[f114])).

fof(f155,plain,
    ( ~ spl8_27
    | spl8_11
    | ~ spl8_12
    | ~ spl8_18 ),
    inference(avatar_split_clause,[],[f142,f114,f101,f93,f153])).

fof(f142,plain,
    ( ~ v4_pre_topc(sK4(sK2,sK1),sK2)
    | ~ spl8_11
    | ~ spl8_12
    | ~ spl8_18 ),
    inference(subsumption_resolution,[],[f141,f94])).

fof(f141,plain,
    ( ~ v4_pre_topc(sK4(sK2,sK1),sK2)
    | v2_tops_2(sK1,sK2)
    | ~ spl8_12
    | ~ spl8_18 ),
    inference(subsumption_resolution,[],[f135,f102])).

fof(f135,plain,
    ( ~ l1_pre_topc(sK2)
    | ~ v4_pre_topc(sK4(sK2,sK1),sK2)
    | v2_tops_2(sK1,sK2)
    | ~ spl8_18 ),
    inference(resolution,[],[f115,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | ~ v4_pre_topc(sK4(X0,X1),X0)
      | v2_tops_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f147,plain,
    ( spl8_22
    | spl8_11
    | ~ spl8_12
    | ~ spl8_18 ),
    inference(avatar_split_clause,[],[f140,f114,f101,f93,f145])).

fof(f140,plain,
    ( r2_hidden(sK4(sK2,sK1),sK1)
    | ~ spl8_11
    | ~ spl8_12
    | ~ spl8_18 ),
    inference(subsumption_resolution,[],[f139,f94])).

fof(f139,plain,
    ( r2_hidden(sK4(sK2,sK1),sK1)
    | v2_tops_2(sK1,sK2)
    | ~ spl8_12
    | ~ spl8_18 ),
    inference(subsumption_resolution,[],[f134,f102])).

fof(f134,plain,
    ( ~ l1_pre_topc(sK2)
    | r2_hidden(sK4(sK2,sK1),sK1)
    | v2_tops_2(sK1,sK2)
    | ~ spl8_18 ),
    inference(resolution,[],[f115,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | r2_hidden(sK4(X0,X1),X1)
      | v2_tops_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f116,plain,(
    spl8_18 ),
    inference(avatar_split_clause,[],[f69,f114])).

fof(f69,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ),
    inference(forward_demodulation,[],[f44,f45])).

fof(f45,plain,(
    sK1 = sK3 ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v2_tops_2(X3,X2)
                  & X1 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) )
              & v2_tops_2(X1,X0)
              & m1_pre_topc(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v2_tops_2(X3,X2)
                  & X1 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) )
              & v2_tops_2(X1,X0)
              & m1_pre_topc(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ! [X2] :
                ( m1_pre_topc(X2,X0)
               => ( v2_tops_2(X1,X0)
                 => ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
                     => ( X1 = X3
                       => v2_tops_2(X3,X2) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( v2_tops_2(X1,X0)
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
                   => ( X1 = X3
                     => v2_tops_2(X3,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t36_tops_2.p',t36_tops_2)).

fof(f44,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f27])).

fof(f108,plain,(
    spl8_14 ),
    inference(avatar_split_clause,[],[f49,f106])).

fof(f49,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f27])).

fof(f103,plain,
    ( spl8_12
    | ~ spl8_0
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f98,f85,f71,f101])).

fof(f98,plain,
    ( l1_pre_topc(sK2)
    | ~ spl8_0
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f96,f72])).

fof(f96,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK2)
    | ~ spl8_6 ),
    inference(resolution,[],[f86,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t36_tops_2.p',dt_m1_pre_topc)).

fof(f95,plain,
    ( ~ spl8_11
    | ~ spl8_2
    | spl8_5 ),
    inference(avatar_split_clause,[],[f83,f80,f76,f93])).

fof(f76,plain,
    ( spl8_2
  <=> sK1 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f80,plain,
    ( spl8_5
  <=> ~ v2_tops_2(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f83,plain,
    ( ~ v2_tops_2(sK1,sK2)
    | ~ spl8_2
    | ~ spl8_5 ),
    inference(forward_demodulation,[],[f81,f77])).

fof(f77,plain,
    ( sK1 = sK3
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f76])).

fof(f81,plain,
    ( ~ v2_tops_2(sK3,sK2)
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f80])).

fof(f91,plain,(
    spl8_8 ),
    inference(avatar_split_clause,[],[f48,f89])).

fof(f48,plain,(
    v2_tops_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f87,plain,(
    spl8_6 ),
    inference(avatar_split_clause,[],[f47,f85])).

fof(f47,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f82,plain,(
    ~ spl8_5 ),
    inference(avatar_split_clause,[],[f46,f80])).

fof(f46,plain,(
    ~ v2_tops_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f78,plain,(
    spl8_2 ),
    inference(avatar_split_clause,[],[f45,f76])).

fof(f73,plain,(
    spl8_0 ),
    inference(avatar_split_clause,[],[f50,f71])).

fof(f50,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
