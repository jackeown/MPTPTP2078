%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : yellow19__t3_yellow19.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:53 EDT 2019

% Result     : Theorem 0.73s
% Output     : Refutation 0.73s
% Verified   : 
% Statistics : Number of formulae       :  150 ( 290 expanded)
%              Number of leaves         :   33 ( 114 expanded)
%              Depth                    :   13
%              Number of atoms          :  595 (1001 expanded)
%              Number of equality atoms :   28 (  45 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f576,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f97,f104,f111,f118,f125,f138,f139,f156,f192,f197,f221,f241,f291,f302,f331,f406,f486,f493,f575])).

fof(f575,plain,
    ( spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_10
    | spl8_13
    | ~ spl8_20
    | ~ spl8_36 ),
    inference(avatar_contradiction_clause,[],[f574])).

fof(f574,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_10
    | ~ spl8_13
    | ~ spl8_20
    | ~ spl8_36 ),
    inference(subsumption_resolution,[],[f573,f131])).

fof(f131,plain,
    ( r2_hidden(sK2,k1_yellow19(sK0,sK1))
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f130])).

fof(f130,plain,
    ( spl8_10
  <=> r2_hidden(sK2,k1_yellow19(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f573,plain,
    ( ~ r2_hidden(sK2,k1_yellow19(sK0,sK1))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_13
    | ~ spl8_20
    | ~ spl8_36 ),
    inference(forward_demodulation,[],[f572,f220])).

fof(f220,plain,
    ( k1_yellow19(sK0,sK1) = a_2_0_yellow19(sK0,sK1)
    | ~ spl8_20 ),
    inference(avatar_component_clause,[],[f219])).

fof(f219,plain,
    ( spl8_20
  <=> k1_yellow19(sK0,sK1) = a_2_0_yellow19(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).

fof(f572,plain,
    ( ~ r2_hidden(sK2,a_2_0_yellow19(sK0,sK1))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_13
    | ~ spl8_36 ),
    inference(subsumption_resolution,[],[f571,f96])).

fof(f96,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl8_1
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f571,plain,
    ( v2_struct_0(sK0)
    | ~ r2_hidden(sK2,a_2_0_yellow19(sK0,sK1))
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_13
    | ~ spl8_36 ),
    inference(subsumption_resolution,[],[f570,f117])).

fof(f117,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl8_6
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f570,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ r2_hidden(sK2,a_2_0_yellow19(sK0,sK1))
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_13
    | ~ spl8_36 ),
    inference(subsumption_resolution,[],[f569,f110])).

fof(f110,plain,
    ( l1_pre_topc(sK0)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f109])).

fof(f109,plain,
    ( spl8_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f569,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ r2_hidden(sK2,a_2_0_yellow19(sK0,sK1))
    | ~ spl8_2
    | ~ spl8_13
    | ~ spl8_36 ),
    inference(subsumption_resolution,[],[f568,f103])).

fof(f103,plain,
    ( v2_pre_topc(sK0)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl8_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f568,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ r2_hidden(sK2,a_2_0_yellow19(sK0,sK1))
    | ~ spl8_13
    | ~ spl8_36 ),
    inference(subsumption_resolution,[],[f567,f134])).

fof(f134,plain,
    ( ~ m1_connsp_2(sK2,sK0,sK1)
    | ~ spl8_13 ),
    inference(avatar_component_clause,[],[f133])).

fof(f133,plain,
    ( spl8_13
  <=> ~ m1_connsp_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f567,plain,
    ( m1_connsp_2(sK2,sK0,sK1)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ r2_hidden(sK2,a_2_0_yellow19(sK0,sK1))
    | ~ spl8_36 ),
    inference(superposition,[],[f69,f492])).

fof(f492,plain,
    ( sK2 = sK3(sK2,sK0,sK1)
    | ~ spl8_36 ),
    inference(avatar_component_clause,[],[f491])).

fof(f491,plain,
    ( spl8_36
  <=> sK2 = sK3(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_36])])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(sK3(X0,X1,X2),X1,X2)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | v2_struct_0(X1)
      | ~ r2_hidden(X0,a_2_0_yellow19(X1,X2)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_0_yellow19(X1,X2))
      <=> ? [X3] :
            ( X0 = X3
            & m1_connsp_2(X3,X1,X2) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_0_yellow19(X1,X2))
      <=> ? [X3] :
            ( X0 = X3
            & m1_connsp_2(X3,X1,X2) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X1))
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_0_yellow19(X1,X2))
      <=> ? [X3] :
            ( X0 = X3
            & m1_connsp_2(X3,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t3_yellow19.p',fraenkel_a_2_0_yellow19)).

fof(f493,plain,
    ( spl8_36
    | spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_10
    | ~ spl8_20 ),
    inference(avatar_split_clause,[],[f470,f219,f130,f116,f109,f102,f95,f491])).

fof(f470,plain,
    ( sK2 = sK3(sK2,sK0,sK1)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_10
    | ~ spl8_20 ),
    inference(resolution,[],[f227,f131])).

fof(f227,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_yellow19(sK0,sK1))
        | sK3(X0,sK0,sK1) = X0 )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_20 ),
    inference(subsumption_resolution,[],[f226,f96])).

fof(f226,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_yellow19(sK0,sK1))
        | sK3(X0,sK0,sK1) = X0
        | v2_struct_0(sK0) )
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_20 ),
    inference(subsumption_resolution,[],[f225,f117])).

fof(f225,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_yellow19(sK0,sK1))
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | sK3(X0,sK0,sK1) = X0
        | v2_struct_0(sK0) )
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_20 ),
    inference(subsumption_resolution,[],[f224,f110])).

fof(f224,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_yellow19(sK0,sK1))
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | sK3(X0,sK0,sK1) = X0
        | v2_struct_0(sK0) )
    | ~ spl8_2
    | ~ spl8_20 ),
    inference(subsumption_resolution,[],[f222,f103])).

fof(f222,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_yellow19(sK0,sK1))
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | sK3(X0,sK0,sK1) = X0
        | v2_struct_0(sK0) )
    | ~ spl8_20 ),
    inference(superposition,[],[f70,f220])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,a_2_0_yellow19(X1,X2))
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | sK3(X0,X1,X2) = X0
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f486,plain,
    ( spl8_34
    | spl8_1
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f364,f109,f102,f95,f484])).

fof(f484,plain,
    ( spl8_34
  <=> k1_yellow19(sK0,sK6(u1_struct_0(sK0))) = a_2_0_yellow19(sK0,sK6(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_34])])).

fof(f364,plain,
    ( k1_yellow19(sK0,sK6(u1_struct_0(sK0))) = a_2_0_yellow19(sK0,sK6(u1_struct_0(sK0)))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f363,f96])).

fof(f363,plain,
    ( v2_struct_0(sK0)
    | k1_yellow19(sK0,sK6(u1_struct_0(sK0))) = a_2_0_yellow19(sK0,sK6(u1_struct_0(sK0)))
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f361,f103])).

fof(f361,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | k1_yellow19(sK0,sK6(u1_struct_0(sK0))) = a_2_0_yellow19(sK0,sK6(u1_struct_0(sK0)))
    | ~ spl8_4 ),
    inference(resolution,[],[f175,f110])).

fof(f175,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | k1_yellow19(X0,sK6(u1_struct_0(X0))) = a_2_0_yellow19(X0,sK6(u1_struct_0(X0))) ) ),
    inference(resolution,[],[f83,f84])).

fof(f84,plain,(
    ! [X0] : m1_subset_1(sK6(X0),X0) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t3_yellow19.p',existence_m1_subset_1)).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | k1_yellow19(X0,X1) = a_2_0_yellow19(X0,X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_yellow19(X0,X1) = a_2_0_yellow19(X0,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_yellow19(X0,X1) = a_2_0_yellow19(X0,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
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
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k1_yellow19(X0,X1) = a_2_0_yellow19(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t3_yellow19.p',d1_yellow19)).

fof(f406,plain,
    ( spl8_32
    | spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_10 ),
    inference(avatar_split_clause,[],[f397,f130,f116,f109,f102,f95,f404])).

fof(f404,plain,
    ( spl8_32
  <=> m1_subset_1(sK2,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_32])])).

fof(f397,plain,
    ( m1_subset_1(sK2,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_10 ),
    inference(subsumption_resolution,[],[f396,f103])).

fof(f396,plain,
    ( ~ v2_pre_topc(sK0)
    | m1_subset_1(sK2,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
    | ~ spl8_1
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_10 ),
    inference(subsumption_resolution,[],[f395,f96])).

fof(f395,plain,
    ( v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | m1_subset_1(sK2,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_10 ),
    inference(subsumption_resolution,[],[f394,f117])).

fof(f394,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | m1_subset_1(sK2,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
    | ~ spl8_4
    | ~ spl8_10 ),
    inference(subsumption_resolution,[],[f382,f110])).

fof(f382,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | m1_subset_1(sK2,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
    | ~ spl8_10 ),
    inference(resolution,[],[f200,f131])).

fof(f200,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k1_yellow19(X0,X1))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | m1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) ) ),
    inference(resolution,[],[f82,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t3_yellow19.p',t4_subset)).

fof(f82,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow19(X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow19(X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow19(X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k1_yellow19(X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t3_yellow19.p',dt_k1_yellow19)).

fof(f331,plain,
    ( spl8_28
    | ~ spl8_31
    | ~ spl8_10 ),
    inference(avatar_split_clause,[],[f292,f130,f329,f323])).

fof(f323,plain,
    ( spl8_28
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).

fof(f329,plain,
    ( spl8_31
  <=> ~ m1_subset_1(k1_yellow19(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_31])])).

fof(f292,plain,
    ( ~ m1_subset_1(k1_yellow19(sK0,sK1),sK2)
    | v1_xboole_0(sK2)
    | ~ spl8_10 ),
    inference(resolution,[],[f131,f141])).

fof(f141,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f79,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t3_yellow19.p',antisymmetry_r2_hidden)).

fof(f79,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t3_yellow19.p',t2_subset)).

fof(f302,plain,
    ( ~ spl8_27
    | ~ spl8_10 ),
    inference(avatar_split_clause,[],[f193,f130,f300])).

fof(f300,plain,
    ( spl8_27
  <=> ~ r2_hidden(k1_yellow19(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).

fof(f193,plain,
    ( ~ r2_hidden(k1_yellow19(sK0,sK1),sK2)
    | ~ spl8_10 ),
    inference(resolution,[],[f131,f81])).

fof(f291,plain,
    ( spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_6
    | spl8_11
    | ~ spl8_12
    | ~ spl8_20 ),
    inference(avatar_contradiction_clause,[],[f290])).

fof(f290,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_11
    | ~ spl8_12
    | ~ spl8_20 ),
    inference(subsumption_resolution,[],[f289,f137])).

fof(f137,plain,
    ( m1_connsp_2(sK2,sK0,sK1)
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f136])).

fof(f136,plain,
    ( spl8_12
  <=> m1_connsp_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f289,plain,
    ( ~ m1_connsp_2(sK2,sK0,sK1)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_11
    | ~ spl8_20 ),
    inference(resolution,[],[f231,f128])).

fof(f128,plain,
    ( ~ r2_hidden(sK2,k1_yellow19(sK0,sK1))
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl8_11
  <=> ~ r2_hidden(sK2,k1_yellow19(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f231,plain,
    ( ! [X1] :
        ( r2_hidden(X1,k1_yellow19(sK0,sK1))
        | ~ m1_connsp_2(X1,sK0,sK1) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_20 ),
    inference(subsumption_resolution,[],[f230,f96])).

fof(f230,plain,
    ( ! [X1] :
        ( r2_hidden(X1,k1_yellow19(sK0,sK1))
        | ~ m1_connsp_2(X1,sK0,sK1)
        | v2_struct_0(sK0) )
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_20 ),
    inference(subsumption_resolution,[],[f229,f117])).

fof(f229,plain,
    ( ! [X1] :
        ( r2_hidden(X1,k1_yellow19(sK0,sK1))
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ m1_connsp_2(X1,sK0,sK1)
        | v2_struct_0(sK0) )
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_20 ),
    inference(subsumption_resolution,[],[f228,f110])).

fof(f228,plain,
    ( ! [X1] :
        ( r2_hidden(X1,k1_yellow19(sK0,sK1))
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ m1_connsp_2(X1,sK0,sK1)
        | v2_struct_0(sK0) )
    | ~ spl8_2
    | ~ spl8_20 ),
    inference(subsumption_resolution,[],[f223,f103])).

fof(f223,plain,
    ( ! [X1] :
        ( r2_hidden(X1,k1_yellow19(sK0,sK1))
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ m1_connsp_2(X1,sK0,sK1)
        | v2_struct_0(sK0) )
    | ~ spl8_20 ),
    inference(superposition,[],[f90,f220])).

fof(f90,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(X3,a_2_0_yellow19(X1,X2))
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_connsp_2(X3,X1,X2)
      | v2_struct_0(X1) ) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_connsp_2(X3,X1,X2)
      | X0 != X3
      | r2_hidden(X0,a_2_0_yellow19(X1,X2)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f241,plain,
    ( ~ spl8_23
    | spl8_24
    | ~ spl8_18 ),
    inference(avatar_split_clause,[],[f212,f190,f239,f236])).

fof(f236,plain,
    ( spl8_23
  <=> ~ v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).

fof(f239,plain,
    ( spl8_24
  <=> ! [X1] : ~ r2_hidden(X1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).

fof(f190,plain,
    ( spl8_18
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f212,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK2)
        | ~ v1_xboole_0(u1_struct_0(sK0)) )
    | ~ spl8_18 ),
    inference(resolution,[],[f191,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t3_yellow19.p',t5_subset)).

fof(f191,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_18 ),
    inference(avatar_component_clause,[],[f190])).

fof(f221,plain,
    ( spl8_20
    | spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f178,f116,f109,f102,f95,f219])).

fof(f178,plain,
    ( k1_yellow19(sK0,sK1) = a_2_0_yellow19(sK0,sK1)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f177,f96])).

fof(f177,plain,
    ( v2_struct_0(sK0)
    | k1_yellow19(sK0,sK1) = a_2_0_yellow19(sK0,sK1)
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f176,f110])).

fof(f176,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | k1_yellow19(sK0,sK1) = a_2_0_yellow19(sK0,sK1)
    | ~ spl8_2
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f174,f103])).

fof(f174,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | k1_yellow19(sK0,sK1) = a_2_0_yellow19(sK0,sK1)
    | ~ spl8_6 ),
    inference(resolution,[],[f83,f117])).

fof(f197,plain,
    ( ~ spl8_10
    | spl8_15 ),
    inference(avatar_contradiction_clause,[],[f196])).

fof(f196,plain,
    ( $false
    | ~ spl8_10
    | ~ spl8_15 ),
    inference(subsumption_resolution,[],[f194,f149])).

fof(f149,plain,
    ( ~ m1_subset_1(sK2,k1_yellow19(sK0,sK1))
    | ~ spl8_15 ),
    inference(avatar_component_clause,[],[f148])).

fof(f148,plain,
    ( spl8_15
  <=> ~ m1_subset_1(sK2,k1_yellow19(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).

fof(f194,plain,
    ( m1_subset_1(sK2,k1_yellow19(sK0,sK1))
    | ~ spl8_10 ),
    inference(resolution,[],[f131,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t3_yellow19.p',t1_subset)).

fof(f192,plain,
    ( spl8_18
    | spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_12 ),
    inference(avatar_split_clause,[],[f185,f136,f116,f109,f102,f95,f190])).

fof(f185,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_12 ),
    inference(subsumption_resolution,[],[f184,f96])).

fof(f184,plain,
    ( v2_struct_0(sK0)
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_12 ),
    inference(subsumption_resolution,[],[f183,f117])).

fof(f183,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_12 ),
    inference(subsumption_resolution,[],[f182,f110])).

fof(f182,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_2
    | ~ spl8_12 ),
    inference(subsumption_resolution,[],[f179,f103])).

fof(f179,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_12 ),
    inference(resolution,[],[f73,f137])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_connsp_2(X2,X0,X1)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0)
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t3_yellow19.p',dt_m1_connsp_2)).

fof(f156,plain,
    ( ~ spl8_15
    | spl8_16
    | spl8_11 ),
    inference(avatar_split_clause,[],[f140,f127,f154,f148])).

fof(f154,plain,
    ( spl8_16
  <=> v1_xboole_0(k1_yellow19(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f140,plain,
    ( v1_xboole_0(k1_yellow19(sK0,sK1))
    | ~ m1_subset_1(sK2,k1_yellow19(sK0,sK1))
    | ~ spl8_11 ),
    inference(resolution,[],[f79,f128])).

fof(f139,plain,
    ( ~ spl8_11
    | ~ spl8_13 ),
    inference(avatar_split_clause,[],[f64,f133,f127])).

fof(f64,plain,
    ( ~ m1_connsp_2(sK2,sK0,sK1)
    | ~ r2_hidden(sK2,k1_yellow19(sK0,sK1)) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( r2_hidden(X2,k1_yellow19(X0,X1))
            <~> m1_connsp_2(X2,X0,X1) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( r2_hidden(X2,k1_yellow19(X0,X1))
            <~> m1_connsp_2(X2,X0,X1) )
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
           => ! [X2] :
                ( r2_hidden(X2,k1_yellow19(X0,X1))
              <=> m1_connsp_2(X2,X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( r2_hidden(X2,k1_yellow19(X0,X1))
            <=> m1_connsp_2(X2,X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t3_yellow19.p',t3_yellow19)).

fof(f138,plain,
    ( spl8_10
    | spl8_12 ),
    inference(avatar_split_clause,[],[f63,f136,f130])).

fof(f63,plain,
    ( m1_connsp_2(sK2,sK0,sK1)
    | r2_hidden(sK2,k1_yellow19(sK0,sK1)) ),
    inference(cnf_transformation,[],[f38])).

fof(f125,plain,(
    spl8_8 ),
    inference(avatar_split_clause,[],[f88,f123])).

fof(f123,plain,
    ( spl8_8
  <=> l1_pre_topc(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f88,plain,(
    l1_pre_topc(sK7) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ? [X0] : l1_pre_topc(X0) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t3_yellow19.p',existence_l1_pre_topc)).

fof(f118,plain,(
    spl8_6 ),
    inference(avatar_split_clause,[],[f65,f116])).

fof(f65,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f38])).

fof(f111,plain,(
    spl8_4 ),
    inference(avatar_split_clause,[],[f68,f109])).

fof(f68,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f104,plain,(
    spl8_2 ),
    inference(avatar_split_clause,[],[f67,f102])).

fof(f67,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f97,plain,(
    ~ spl8_1 ),
    inference(avatar_split_clause,[],[f66,f95])).

fof(f66,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f38])).
%------------------------------------------------------------------------------
