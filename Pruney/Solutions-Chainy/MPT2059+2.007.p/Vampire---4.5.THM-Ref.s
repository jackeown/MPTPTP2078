%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:35 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  179 ( 498 expanded)
%              Number of leaves         :   42 ( 239 expanded)
%              Depth                    :   10
%              Number of atoms          :  948 (2849 expanded)
%              Number of equality atoms :   18 (  92 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f327,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f90,f91,f96,f101,f106,f111,f116,f121,f126,f131,f136,f144,f153,f172,f173,f179,f186,f221,f227,f247,f258,f269,f283,f287,f299,f303,f316,f322,f326])).

fof(f326,plain,
    ( ~ spl3_30
    | ~ spl3_9
    | ~ spl3_10
    | spl3_11
    | spl3_2
    | ~ spl3_16
    | ~ spl3_1
    | ~ spl3_13
    | ~ spl3_28
    | ~ spl3_36 ),
    inference(avatar_split_clause,[],[f325,f285,f244,f149,f83,f169,f87,f133,f128,f123,f255])).

fof(f255,plain,
    ( spl3_30
  <=> l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f123,plain,
    ( spl3_9
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f128,plain,
    ( spl3_10
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f133,plain,
    ( spl3_11
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f87,plain,
    ( spl3_2
  <=> r2_waybel_7(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f169,plain,
    ( spl3_16
  <=> m1_subset_1(sK2,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f83,plain,
    ( spl3_1
  <=> r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f149,plain,
    ( spl3_13
  <=> k2_struct_0(sK0) = u1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f244,plain,
    ( spl3_28
  <=> sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f285,plain,
    ( spl3_36
  <=> ! [X3,X2] :
        ( ~ r2_hidden(X2,k10_yellow_6(X3,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))
        | v2_struct_0(X3)
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | r2_waybel_7(X3,k2_yellow19(X3,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X2)
        | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),X3)
        | ~ m1_subset_1(X2,u1_struct_0(X3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).

fof(f325,plain,
    ( ~ m1_subset_1(sK2,k2_struct_0(sK0))
    | r2_waybel_7(sK0,sK1,sK2)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | ~ spl3_1
    | ~ spl3_13
    | ~ spl3_28
    | ~ spl3_36 ),
    inference(forward_demodulation,[],[f324,f151])).

fof(f151,plain,
    ( k2_struct_0(sK0) = u1_struct_0(sK0)
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f149])).

fof(f324,plain,
    ( r2_waybel_7(sK0,sK1,sK2)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl3_1
    | ~ spl3_28
    | ~ spl3_36 ),
    inference(forward_demodulation,[],[f323,f246])).

fof(f246,plain,
    ( sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ spl3_28 ),
    inference(avatar_component_clause,[],[f244])).

fof(f323,plain,
    ( v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | r2_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl3_1
    | ~ spl3_36 ),
    inference(resolution,[],[f84,f286])).

fof(f286,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(X2,k10_yellow_6(X3,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))
        | v2_struct_0(X3)
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | r2_waybel_7(X3,k2_yellow19(X3,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X2)
        | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),X3)
        | ~ m1_subset_1(X2,u1_struct_0(X3)) )
    | ~ spl3_36 ),
    inference(avatar_component_clause,[],[f285])).

fof(f84,plain,
    ( r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f83])).

fof(f322,plain,
    ( spl3_1
    | ~ spl3_2
    | ~ spl3_16
    | ~ spl3_38 ),
    inference(avatar_contradiction_clause,[],[f320])).

fof(f320,plain,
    ( $false
    | spl3_1
    | ~ spl3_2
    | ~ spl3_16
    | ~ spl3_38 ),
    inference(unit_resulting_resolution,[],[f171,f88,f85,f315])).

fof(f315,plain,
    ( ! [X0] :
        ( ~ r2_waybel_7(sK0,sK1,X0)
        | r2_hidden(X0,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))
        | ~ m1_subset_1(X0,k2_struct_0(sK0)) )
    | ~ spl3_38 ),
    inference(avatar_component_clause,[],[f314])).

fof(f314,plain,
    ( spl3_38
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k2_struct_0(sK0))
        | r2_hidden(X0,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))
        | ~ r2_waybel_7(sK0,sK1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).

fof(f85,plain,
    ( ~ r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f83])).

fof(f88,plain,
    ( r2_waybel_7(sK0,sK1,sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f87])).

fof(f171,plain,
    ( m1_subset_1(sK2,k2_struct_0(sK0))
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f169])).

fof(f316,plain,
    ( ~ spl3_30
    | ~ spl3_9
    | spl3_11
    | spl3_38
    | ~ spl3_10
    | ~ spl3_13
    | ~ spl3_28
    | ~ spl3_35 ),
    inference(avatar_split_clause,[],[f312,f281,f244,f149,f128,f314,f133,f123,f255])).

fof(f281,plain,
    ( spl3_35
  <=> ! [X1,X0] :
        ( ~ r2_waybel_7(X0,k2_yellow19(X0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X1)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | r2_hidden(X1,k10_yellow_6(X0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))
        | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).

fof(f312,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k2_struct_0(sK0))
        | ~ r2_waybel_7(sK0,sK1,X0)
        | v2_struct_0(sK0)
        | ~ l1_pre_topc(sK0)
        | r2_hidden(X0,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))
        | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) )
    | ~ spl3_10
    | ~ spl3_13
    | ~ spl3_28
    | ~ spl3_35 ),
    inference(forward_demodulation,[],[f311,f151])).

fof(f311,plain,
    ( ! [X0] :
        ( ~ r2_waybel_7(sK0,sK1,X0)
        | v2_struct_0(sK0)
        | ~ l1_pre_topc(sK0)
        | r2_hidden(X0,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))
        | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl3_10
    | ~ spl3_28
    | ~ spl3_35 ),
    inference(forward_demodulation,[],[f310,f246])).

fof(f310,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | ~ r2_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X0)
        | ~ l1_pre_topc(sK0)
        | r2_hidden(X0,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))
        | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl3_10
    | ~ spl3_35 ),
    inference(resolution,[],[f282,f130])).

fof(f130,plain,
    ( v2_pre_topc(sK0)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f128])).

fof(f282,plain,
    ( ! [X0,X1] :
        ( ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ r2_waybel_7(X0,k2_yellow19(X0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X1)
        | ~ l1_pre_topc(X0)
        | r2_hidden(X1,k10_yellow_6(X0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))
        | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0)) )
    | ~ spl3_35 ),
    inference(avatar_component_clause,[],[f281])).

fof(f303,plain,(
    spl3_37 ),
    inference(avatar_contradiction_clause,[],[f300])).

fof(f300,plain,
    ( $false
    | spl3_37 ),
    inference(unit_resulting_resolution,[],[f145,f296])).

fof(f296,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | spl3_37 ),
    inference(avatar_component_clause,[],[f294])).

fof(f294,plain,
    ( spl3_37
  <=> m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).

fof(f145,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f49,f48])).

fof(f48,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f49,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f299,plain,
    ( spl3_11
    | ~ spl3_12
    | spl3_15
    | spl3_8
    | ~ spl3_6
    | ~ spl3_5
    | ~ spl3_4
    | ~ spl3_37
    | ~ spl3_13
    | ~ spl3_34 ),
    inference(avatar_split_clause,[],[f298,f277,f149,f294,f98,f103,f108,f118,f164,f140,f133])).

fof(f140,plain,
    ( spl3_12
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f164,plain,
    ( spl3_15
  <=> v1_xboole_0(k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f118,plain,
    ( spl3_8
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f108,plain,
    ( spl3_6
  <=> v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f103,plain,
    ( spl3_5
  <=> v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f98,plain,
    ( spl3_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f277,plain,
    ( spl3_34
  <=> v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).

fof(f298,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | v1_xboole_0(sK1)
    | v1_xboole_0(k2_struct_0(sK0))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl3_13
    | ~ spl3_34 ),
    inference(forward_demodulation,[],[f291,f151])).

fof(f291,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | v1_xboole_0(sK1)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(k2_struct_0(sK0))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl3_34 ),
    inference(resolution,[],[f279,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k3_yellow19(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
      | ~ v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
      | ~ v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f57,f50,f50,f50])).

fof(f50,plain,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_yellow_1)).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k3_yellow19(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v4_orders_2(k3_yellow19(X0,X1,X2))
        & v3_orders_2(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v4_orders_2(k3_yellow19(X0,X1,X2))
        & v3_orders_2(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
        & v13_waybel_0(X2,k3_yellow_1(X1))
        & v2_waybel_0(X2,k3_yellow_1(X1))
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v4_orders_2(k3_yellow19(X0,X1,X2))
        & v3_orders_2(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_yellow19)).

fof(f279,plain,
    ( v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ spl3_34 ),
    inference(avatar_component_clause,[],[f277])).

fof(f287,plain,
    ( spl3_34
    | ~ spl3_18
    | spl3_36
    | ~ spl3_32 ),
    inference(avatar_split_clause,[],[f275,f266,f285,f183,f277])).

fof(f183,plain,
    ( spl3_18
  <=> v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f266,plain,
    ( spl3_32
  <=> v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).

fof(f275,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(X2,k10_yellow_6(X3,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))
        | ~ m1_subset_1(X2,u1_struct_0(X3))
        | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),X3)
        | r2_waybel_7(X3,k2_yellow19(X3,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X2)
        | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
        | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(X3)
        | v2_struct_0(X3) )
    | ~ spl3_32 ),
    inference(resolution,[],[f268,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ v7_waybel_0(X1)
      | ~ r2_hidden(X2,k10_yellow_6(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | r2_waybel_7(X0,k2_yellow19(X0,X1),X2)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k10_yellow_6(X0,X1))
                  | ~ r2_waybel_7(X0,k2_yellow19(X0,X1),X2) )
                & ( r2_waybel_7(X0,k2_yellow19(X0,X1),X2)
                  | ~ r2_hidden(X2,k10_yellow_6(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k10_yellow_6(X0,X1))
              <=> r2_waybel_7(X0,k2_yellow19(X0,X1),X2) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k10_yellow_6(X0,X1))
              <=> r2_waybel_7(X0,k2_yellow19(X0,X1),X2) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
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
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,k10_yellow_6(X0,X1))
              <=> r2_waybel_7(X0,k2_yellow19(X0,X1),X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_yellow19)).

fof(f268,plain,
    ( v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ spl3_32 ),
    inference(avatar_component_clause,[],[f266])).

fof(f283,plain,
    ( spl3_34
    | ~ spl3_18
    | spl3_35
    | ~ spl3_32 ),
    inference(avatar_split_clause,[],[f274,f266,f281,f183,f277])).

fof(f274,plain,
    ( ! [X0,X1] :
        ( ~ r2_waybel_7(X0,k2_yellow19(X0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X1)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0)
        | r2_hidden(X1,k10_yellow_6(X0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))
        | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
        | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl3_32 ),
    inference(resolution,[],[f268,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ v7_waybel_0(X1)
      | ~ r2_waybel_7(X0,k2_yellow19(X0,X1),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | r2_hidden(X2,k10_yellow_6(X0,X1))
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f269,plain,
    ( spl3_32
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_7
    | spl3_8
    | spl3_15
    | ~ spl3_25 ),
    inference(avatar_split_clause,[],[f263,f225,f164,f118,f113,f108,f103,f98,f266])).

fof(f113,plain,
    ( spl3_7
  <=> v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f225,plain,
    ( spl3_25
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
        | v7_waybel_0(k3_yellow19(sK0,X1,X0))
        | v1_xboole_0(X1)
        | v1_xboole_0(X0)
        | ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
        | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
        | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f263,plain,
    ( v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_7
    | spl3_8
    | spl3_15
    | ~ spl3_25 ),
    inference(unit_resulting_resolution,[],[f120,f166,f145,f105,f110,f115,f100,f226])).

fof(f226,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
        | v7_waybel_0(k3_yellow19(sK0,X1,X0))
        | v1_xboole_0(X1)
        | v1_xboole_0(X0)
        | ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
        | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
        | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) )
    | ~ spl3_25 ),
    inference(avatar_component_clause,[],[f225])).

fof(f100,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f98])).

fof(f115,plain,
    ( v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f113])).

fof(f110,plain,
    ( v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f108])).

fof(f105,plain,
    ( v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f103])).

fof(f166,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK0))
    | spl3_15 ),
    inference(avatar_component_clause,[],[f164])).

fof(f120,plain,
    ( ~ v1_xboole_0(sK1)
    | spl3_8 ),
    inference(avatar_component_clause,[],[f118])).

fof(f258,plain,
    ( spl3_30
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | spl3_8
    | spl3_15
    | ~ spl3_24 ),
    inference(avatar_split_clause,[],[f252,f219,f164,f118,f108,f103,f98,f255])).

fof(f219,plain,
    ( spl3_24
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
        | l1_waybel_0(k3_yellow19(sK0,X1,X0),sK0)
        | v1_xboole_0(X1)
        | v1_xboole_0(X0)
        | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
        | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f252,plain,
    ( l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | spl3_8
    | spl3_15
    | ~ spl3_24 ),
    inference(unit_resulting_resolution,[],[f120,f166,f145,f105,f110,f100,f220])).

fof(f220,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
        | l1_waybel_0(k3_yellow19(sK0,X1,X0),sK0)
        | v1_xboole_0(X1)
        | v1_xboole_0(X0)
        | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
        | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) )
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f219])).

fof(f247,plain,
    ( spl3_28
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_7
    | spl3_8
    | spl3_11
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f241,f140,f133,f118,f113,f108,f103,f98,f244])).

fof(f241,plain,
    ( sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_7
    | spl3_8
    | spl3_11
    | ~ spl3_12 ),
    inference(unit_resulting_resolution,[],[f135,f142,f120,f105,f110,f115,f100,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ l1_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
      | ~ v13_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
      | ~ v2_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
      | ~ v1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))))
      | v1_xboole_0(X1)
      | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f56,f50,f50,f50,f50])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          | v1_xboole_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          | v1_xboole_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
            & ~ v1_xboole_0(X1) )
         => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_yellow19)).

fof(f142,plain,
    ( l1_struct_0(sK0)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f140])).

fof(f135,plain,
    ( ~ v2_struct_0(sK0)
    | spl3_11 ),
    inference(avatar_component_clause,[],[f133])).

fof(f227,plain,
    ( spl3_11
    | spl3_25
    | ~ spl3_12
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f223,f149,f140,f225,f133])).

fof(f223,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
        | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
        | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
        | ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
        | v1_xboole_0(X0)
        | v1_xboole_0(X1)
        | v7_waybel_0(k3_yellow19(sK0,X1,X0))
        | v2_struct_0(sK0) )
    | ~ spl3_12
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f222,f151])).

fof(f222,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
        | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
        | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
        | ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
        | v1_xboole_0(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X1)
        | v7_waybel_0(k3_yellow19(sK0,X1,X0))
        | v2_struct_0(sK0) )
    | ~ spl3_12 ),
    inference(resolution,[],[f79,f142])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_struct_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
      | ~ v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
      | ~ v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
      | ~ v1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | v7_waybel_0(k3_yellow19(X0,X1,X2))
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f66,f50,f50,f50,f50])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( v7_waybel_0(k3_yellow19(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | ~ v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( v7_waybel_0(k3_yellow19(X0,X1,X2))
        & v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | ~ v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( v7_waybel_0(k3_yellow19(X0,X1,X2))
        & v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | ~ v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
        & v13_waybel_0(X2,k3_yellow_1(X1))
        & v2_waybel_0(X2,k3_yellow_1(X1))
        & v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( v7_waybel_0(k3_yellow19(X0,X1,X2))
        & v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_yellow19)).

fof(f221,plain,
    ( spl3_11
    | spl3_24
    | ~ spl3_12
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f217,f149,f140,f219,f133])).

fof(f217,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
        | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
        | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
        | v1_xboole_0(X0)
        | v1_xboole_0(X1)
        | l1_waybel_0(k3_yellow19(sK0,X1,X0),sK0)
        | v2_struct_0(sK0) )
    | ~ spl3_12
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f216,f151])).

fof(f216,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
        | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
        | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
        | v1_xboole_0(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X1)
        | l1_waybel_0(k3_yellow19(sK0,X1,X0),sK0)
        | v2_struct_0(sK0) )
    | ~ spl3_12 ),
    inference(resolution,[],[f76,f142])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_struct_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
      | ~ v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
      | ~ v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f63,f50,f50,f50])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
        & v13_waybel_0(X2,k3_yellow_1(X1))
        & v2_waybel_0(X2,k3_yellow_1(X1))
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_yellow19)).

fof(f186,plain,
    ( spl3_18
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | spl3_8
    | spl3_15
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f180,f177,f164,f118,f108,f103,f98,f183])).

fof(f177,plain,
    ( spl3_17
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
        | v4_orders_2(k3_yellow19(sK0,X1,X0))
        | v1_xboole_0(X1)
        | v1_xboole_0(X0)
        | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
        | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f180,plain,
    ( v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | spl3_8
    | spl3_15
    | ~ spl3_17 ),
    inference(unit_resulting_resolution,[],[f120,f166,f145,f105,f110,f100,f178])).

fof(f178,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
        | v4_orders_2(k3_yellow19(sK0,X1,X0))
        | v1_xboole_0(X1)
        | v1_xboole_0(X0)
        | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
        | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) )
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f177])).

% (12399)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
fof(f179,plain,
    ( spl3_11
    | spl3_17
    | ~ spl3_12
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f175,f149,f140,f177,f133])).

fof(f175,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
        | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
        | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
        | v1_xboole_0(X0)
        | v1_xboole_0(X1)
        | v4_orders_2(k3_yellow19(sK0,X1,X0))
        | v2_struct_0(sK0) )
    | ~ spl3_12
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f174,f151])).

fof(f174,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
        | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
        | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
        | v1_xboole_0(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X1)
        | v4_orders_2(k3_yellow19(sK0,X1,X0))
        | v2_struct_0(sK0) )
    | ~ spl3_12 ),
    inference(resolution,[],[f73,f142])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_struct_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
      | ~ v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
      | ~ v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | v4_orders_2(k3_yellow19(X0,X1,X2))
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f59,f50,f50,f50])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( v4_orders_2(k3_yellow19(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f173,plain,
    ( spl3_11
    | ~ spl3_12
    | ~ spl3_15
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f162,f149,f164,f140,f133])).

fof(f162,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK0))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl3_13 ),
    inference(superposition,[],[f55,f151])).

fof(f55,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f172,plain,
    ( spl3_16
    | ~ spl3_3
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f161,f149,f93,f169])).

fof(f93,plain,
    ( spl3_3
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f161,plain,
    ( m1_subset_1(sK2,k2_struct_0(sK0))
    | ~ spl3_3
    | ~ spl3_13 ),
    inference(backward_demodulation,[],[f95,f151])).

fof(f95,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f93])).

fof(f153,plain,
    ( spl3_13
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f147,f140,f149])).

fof(f147,plain,
    ( k2_struct_0(sK0) = u1_struct_0(sK0)
    | ~ spl3_12 ),
    inference(resolution,[],[f52,f142])).

fof(f52,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f144,plain,
    ( spl3_12
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f138,f123,f140])).

fof(f138,plain,
    ( l1_struct_0(sK0)
    | ~ spl3_9 ),
    inference(resolution,[],[f51,f125])).

fof(f125,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f123])).

fof(f51,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f136,plain,(
    ~ spl3_11 ),
    inference(avatar_split_clause,[],[f37,f133])).

fof(f37,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( ( ~ r2_waybel_7(sK0,sK1,sK2)
      | ~ r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) )
    & ( r2_waybel_7(sK0,sK1,sK2)
      | r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) )
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    & v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    & v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    & v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
    & ~ v1_xboole_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f31,f34,f33,f32])).

fof(f32,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ r2_waybel_7(X0,X1,X2)
                  | ~ r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1))) )
                & ( r2_waybel_7(X0,X1,X2)
                  | r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1))) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
            & ~ v1_xboole_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r2_waybel_7(sK0,X1,X2)
                | ~ r2_hidden(X2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1))) )
              & ( r2_waybel_7(sK0,X1,X2)
                | r2_hidden(X2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1))) )
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ~ r2_waybel_7(sK0,X1,X2)
              | ~ r2_hidden(X2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1))) )
            & ( r2_waybel_7(sK0,X1,X2)
              | r2_hidden(X2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1))) )
            & m1_subset_1(X2,u1_struct_0(sK0)) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
        & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0)))
        & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0)))
        & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
        & ~ v1_xboole_0(X1) )
   => ( ? [X2] :
          ( ( ~ r2_waybel_7(sK0,sK1,X2)
            | ~ r2_hidden(X2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) )
          & ( r2_waybel_7(sK0,sK1,X2)
            | r2_hidden(X2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) )
          & m1_subset_1(X2,u1_struct_0(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
      & v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
      & v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
      & v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X2] :
        ( ( ~ r2_waybel_7(sK0,sK1,X2)
          | ~ r2_hidden(X2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) )
        & ( r2_waybel_7(sK0,sK1,X2)
          | r2_hidden(X2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) )
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( ( ~ r2_waybel_7(sK0,sK1,sK2)
        | ~ r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) )
      & ( r2_waybel_7(sK0,sK1,sK2)
        | r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) )
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r2_waybel_7(X0,X1,X2)
                | ~ r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1))) )
              & ( r2_waybel_7(X0,X1,X2)
                | r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1))) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r2_waybel_7(X0,X1,X2)
                | ~ r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1))) )
              & ( r2_waybel_7(X0,X1,X2)
                | r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1))) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1)))
              <~> r2_waybel_7(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1)))
              <~> r2_waybel_7(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          & ~ v1_xboole_0(X1) )
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
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
              & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
              & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
              & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
              & ~ v1_xboole_0(X1) )
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1)))
                <=> r2_waybel_7(X0,X1,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
            & ~ v1_xboole_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1)))
              <=> r2_waybel_7(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_yellow19)).

fof(f131,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f38,f128])).

fof(f38,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f126,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f39,f123])).

fof(f39,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f121,plain,(
    ~ spl3_8 ),
    inference(avatar_split_clause,[],[f40,f118])).

fof(f40,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f116,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f70,f113])).

fof(f70,plain,(
    v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))) ),
    inference(definition_unfolding,[],[f41,f50])).

fof(f41,plain,(
    v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f35])).

fof(f111,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f69,f108])).

fof(f69,plain,(
    v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    inference(definition_unfolding,[],[f42,f50])).

fof(f42,plain,(
    v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f35])).

fof(f106,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f68,f103])).

fof(f68,plain,(
    v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    inference(definition_unfolding,[],[f43,f50])).

fof(f43,plain,(
    v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f35])).

fof(f101,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f67,f98])).

fof(f67,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) ),
    inference(definition_unfolding,[],[f44,f50])).

fof(f44,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) ),
    inference(cnf_transformation,[],[f35])).

fof(f96,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f45,f93])).

fof(f45,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f35])).

fof(f91,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f46,f87,f83])).

fof(f46,plain,
    ( r2_waybel_7(sK0,sK1,sK2)
    | r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) ),
    inference(cnf_transformation,[],[f35])).

fof(f90,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f47,f87,f83])).

fof(f47,plain,
    ( ~ r2_waybel_7(sK0,sK1,sK2)
    | ~ r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) ),
    inference(cnf_transformation,[],[f35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:39:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.45  % (12401)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.45  % (12409)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.45  % (12401)Refutation found. Thanks to Tanya!
% 0.21/0.45  % SZS status Theorem for theBenchmark
% 0.21/0.45  % SZS output start Proof for theBenchmark
% 0.21/0.46  fof(f327,plain,(
% 0.21/0.46    $false),
% 0.21/0.46    inference(avatar_sat_refutation,[],[f90,f91,f96,f101,f106,f111,f116,f121,f126,f131,f136,f144,f153,f172,f173,f179,f186,f221,f227,f247,f258,f269,f283,f287,f299,f303,f316,f322,f326])).
% 0.21/0.46  fof(f326,plain,(
% 0.21/0.46    ~spl3_30 | ~spl3_9 | ~spl3_10 | spl3_11 | spl3_2 | ~spl3_16 | ~spl3_1 | ~spl3_13 | ~spl3_28 | ~spl3_36),
% 0.21/0.46    inference(avatar_split_clause,[],[f325,f285,f244,f149,f83,f169,f87,f133,f128,f123,f255])).
% 0.21/0.46  fof(f255,plain,(
% 0.21/0.46    spl3_30 <=> l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 0.21/0.46  fof(f123,plain,(
% 0.21/0.46    spl3_9 <=> l1_pre_topc(sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.46  fof(f128,plain,(
% 0.21/0.46    spl3_10 <=> v2_pre_topc(sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.46  fof(f133,plain,(
% 0.21/0.46    spl3_11 <=> v2_struct_0(sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.46  fof(f87,plain,(
% 0.21/0.46    spl3_2 <=> r2_waybel_7(sK0,sK1,sK2)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.46  fof(f169,plain,(
% 0.21/0.46    spl3_16 <=> m1_subset_1(sK2,k2_struct_0(sK0))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.21/0.46  fof(f83,plain,(
% 0.21/0.46    spl3_1 <=> r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.46  fof(f149,plain,(
% 0.21/0.46    spl3_13 <=> k2_struct_0(sK0) = u1_struct_0(sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.21/0.46  fof(f244,plain,(
% 0.21/0.46    spl3_28 <=> sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 0.21/0.46  fof(f285,plain,(
% 0.21/0.46    spl3_36 <=> ! [X3,X2] : (~r2_hidden(X2,k10_yellow_6(X3,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) | v2_struct_0(X3) | ~v2_pre_topc(X3) | ~l1_pre_topc(X3) | r2_waybel_7(X3,k2_yellow19(X3,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X2) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),X3) | ~m1_subset_1(X2,u1_struct_0(X3)))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).
% 0.21/0.46  fof(f325,plain,(
% 0.21/0.46    ~m1_subset_1(sK2,k2_struct_0(sK0)) | r2_waybel_7(sK0,sK1,sK2) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | (~spl3_1 | ~spl3_13 | ~spl3_28 | ~spl3_36)),
% 0.21/0.46    inference(forward_demodulation,[],[f324,f151])).
% 0.21/0.46  fof(f151,plain,(
% 0.21/0.46    k2_struct_0(sK0) = u1_struct_0(sK0) | ~spl3_13),
% 0.21/0.46    inference(avatar_component_clause,[],[f149])).
% 0.21/0.46  fof(f324,plain,(
% 0.21/0.46    r2_waybel_7(sK0,sK1,sK2) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | (~spl3_1 | ~spl3_28 | ~spl3_36)),
% 0.21/0.46    inference(forward_demodulation,[],[f323,f246])).
% 0.21/0.46  fof(f246,plain,(
% 0.21/0.46    sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~spl3_28),
% 0.21/0.46    inference(avatar_component_clause,[],[f244])).
% 0.21/0.46  fof(f323,plain,(
% 0.21/0.46    v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | r2_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | (~spl3_1 | ~spl3_36)),
% 0.21/0.46    inference(resolution,[],[f84,f286])).
% 0.21/0.46  fof(f286,plain,(
% 0.21/0.46    ( ! [X2,X3] : (~r2_hidden(X2,k10_yellow_6(X3,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) | v2_struct_0(X3) | ~v2_pre_topc(X3) | ~l1_pre_topc(X3) | r2_waybel_7(X3,k2_yellow19(X3,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X2) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),X3) | ~m1_subset_1(X2,u1_struct_0(X3))) ) | ~spl3_36),
% 0.21/0.46    inference(avatar_component_clause,[],[f285])).
% 0.21/0.46  fof(f84,plain,(
% 0.21/0.46    r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) | ~spl3_1),
% 0.21/0.46    inference(avatar_component_clause,[],[f83])).
% 0.21/0.46  fof(f322,plain,(
% 0.21/0.46    spl3_1 | ~spl3_2 | ~spl3_16 | ~spl3_38),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f320])).
% 0.21/0.46  fof(f320,plain,(
% 0.21/0.46    $false | (spl3_1 | ~spl3_2 | ~spl3_16 | ~spl3_38)),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f171,f88,f85,f315])).
% 0.21/0.46  fof(f315,plain,(
% 0.21/0.46    ( ! [X0] : (~r2_waybel_7(sK0,sK1,X0) | r2_hidden(X0,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) | ~m1_subset_1(X0,k2_struct_0(sK0))) ) | ~spl3_38),
% 0.21/0.46    inference(avatar_component_clause,[],[f314])).
% 0.21/0.46  fof(f314,plain,(
% 0.21/0.46    spl3_38 <=> ! [X0] : (~m1_subset_1(X0,k2_struct_0(sK0)) | r2_hidden(X0,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) | ~r2_waybel_7(sK0,sK1,X0))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).
% 0.21/0.46  fof(f85,plain,(
% 0.21/0.46    ~r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) | spl3_1),
% 0.21/0.46    inference(avatar_component_clause,[],[f83])).
% 0.21/0.46  fof(f88,plain,(
% 0.21/0.46    r2_waybel_7(sK0,sK1,sK2) | ~spl3_2),
% 0.21/0.46    inference(avatar_component_clause,[],[f87])).
% 0.21/0.46  fof(f171,plain,(
% 0.21/0.46    m1_subset_1(sK2,k2_struct_0(sK0)) | ~spl3_16),
% 0.21/0.46    inference(avatar_component_clause,[],[f169])).
% 0.21/0.46  fof(f316,plain,(
% 0.21/0.46    ~spl3_30 | ~spl3_9 | spl3_11 | spl3_38 | ~spl3_10 | ~spl3_13 | ~spl3_28 | ~spl3_35),
% 0.21/0.46    inference(avatar_split_clause,[],[f312,f281,f244,f149,f128,f314,f133,f123,f255])).
% 0.21/0.46  fof(f281,plain,(
% 0.21/0.46    spl3_35 <=> ! [X1,X0] : (~r2_waybel_7(X0,k2_yellow19(X0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X1) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | r2_hidden(X1,k10_yellow_6(X0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).
% 0.21/0.46  fof(f312,plain,(
% 0.21/0.46    ( ! [X0] : (~m1_subset_1(X0,k2_struct_0(sK0)) | ~r2_waybel_7(sK0,sK1,X0) | v2_struct_0(sK0) | ~l1_pre_topc(sK0) | r2_hidden(X0,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)) ) | (~spl3_10 | ~spl3_13 | ~spl3_28 | ~spl3_35)),
% 0.21/0.46    inference(forward_demodulation,[],[f311,f151])).
% 0.21/0.46  fof(f311,plain,(
% 0.21/0.46    ( ! [X0] : (~r2_waybel_7(sK0,sK1,X0) | v2_struct_0(sK0) | ~l1_pre_topc(sK0) | r2_hidden(X0,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (~spl3_10 | ~spl3_28 | ~spl3_35)),
% 0.21/0.46    inference(forward_demodulation,[],[f310,f246])).
% 0.21/0.46  fof(f310,plain,(
% 0.21/0.46    ( ! [X0] : (v2_struct_0(sK0) | ~r2_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X0) | ~l1_pre_topc(sK0) | r2_hidden(X0,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (~spl3_10 | ~spl3_35)),
% 0.21/0.46    inference(resolution,[],[f282,f130])).
% 0.21/0.46  fof(f130,plain,(
% 0.21/0.46    v2_pre_topc(sK0) | ~spl3_10),
% 0.21/0.46    inference(avatar_component_clause,[],[f128])).
% 0.21/0.46  fof(f282,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~v2_pre_topc(X0) | v2_struct_0(X0) | ~r2_waybel_7(X0,k2_yellow19(X0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X1) | ~l1_pre_topc(X0) | r2_hidden(X1,k10_yellow_6(X0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) ) | ~spl3_35),
% 0.21/0.46    inference(avatar_component_clause,[],[f281])).
% 0.21/0.46  fof(f303,plain,(
% 0.21/0.46    spl3_37),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f300])).
% 0.21/0.46  fof(f300,plain,(
% 0.21/0.46    $false | spl3_37),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f145,f296])).
% 0.21/0.46  fof(f296,plain,(
% 0.21/0.46    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | spl3_37),
% 0.21/0.46    inference(avatar_component_clause,[],[f294])).
% 0.21/0.46  fof(f294,plain,(
% 0.21/0.46    spl3_37 <=> m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).
% 0.21/0.46  fof(f145,plain,(
% 0.21/0.46    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.21/0.46    inference(forward_demodulation,[],[f49,f48])).
% 0.21/0.46  fof(f48,plain,(
% 0.21/0.46    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.21/0.46    inference(cnf_transformation,[],[f1])).
% 0.21/0.46  fof(f1,axiom,(
% 0.21/0.46    ! [X0] : k2_subset_1(X0) = X0),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 0.21/0.46  fof(f49,plain,(
% 0.21/0.46    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f2])).
% 0.21/0.46  fof(f2,axiom,(
% 0.21/0.46    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.21/0.46  fof(f299,plain,(
% 0.21/0.46    spl3_11 | ~spl3_12 | spl3_15 | spl3_8 | ~spl3_6 | ~spl3_5 | ~spl3_4 | ~spl3_37 | ~spl3_13 | ~spl3_34),
% 0.21/0.46    inference(avatar_split_clause,[],[f298,f277,f149,f294,f98,f103,f108,f118,f164,f140,f133])).
% 0.21/0.46  fof(f140,plain,(
% 0.21/0.46    spl3_12 <=> l1_struct_0(sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.46  fof(f164,plain,(
% 0.21/0.46    spl3_15 <=> v1_xboole_0(k2_struct_0(sK0))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.21/0.46  fof(f118,plain,(
% 0.21/0.46    spl3_8 <=> v1_xboole_0(sK1)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.46  fof(f108,plain,(
% 0.21/0.46    spl3_6 <=> v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.46  fof(f103,plain,(
% 0.21/0.46    spl3_5 <=> v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.46  fof(f98,plain,(
% 0.21/0.46    spl3_4 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.46  fof(f277,plain,(
% 0.21/0.46    spl3_34 <=> v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).
% 0.21/0.46  fof(f298,plain,(
% 0.21/0.46    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) | ~v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | v1_xboole_0(sK1) | v1_xboole_0(k2_struct_0(sK0)) | ~l1_struct_0(sK0) | v2_struct_0(sK0) | (~spl3_13 | ~spl3_34)),
% 0.21/0.46    inference(forward_demodulation,[],[f291,f151])).
% 0.21/0.46  fof(f291,plain,(
% 0.21/0.46    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) | ~v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | v1_xboole_0(sK1) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(k2_struct_0(sK0)) | ~l1_struct_0(sK0) | v2_struct_0(sK0) | ~spl3_34),
% 0.21/0.46    inference(resolution,[],[f279,f75])).
% 0.21/0.46  fof(f75,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~v2_struct_0(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | ~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.46    inference(definition_unfolding,[],[f57,f50,f50,f50])).
% 0.21/0.46  fof(f50,plain,(
% 0.21/0.46    ( ! [X0] : (k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f6])).
% 0.21/0.46  fof(f6,axiom,(
% 0.21/0.46    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_yellow_1)).
% 0.21/0.46  fof(f57,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~v2_struct_0(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f25])).
% 0.21/0.46  fof(f25,plain,(
% 0.21/0.46    ! [X0,X1,X2] : ((v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & v4_orders_2(k3_yellow19(X0,X1,X2)) & v3_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.46    inference(flattening,[],[f24])).
% 0.21/0.46  fof(f24,plain,(
% 0.21/0.46    ! [X0,X1,X2] : ((v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & v4_orders_2(k3_yellow19(X0,X1,X2)) & v3_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f8])).
% 0.21/0.46  fof(f8,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & v4_orders_2(k3_yellow19(X0,X1,X2)) & v3_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_yellow19)).
% 0.21/0.46  fof(f279,plain,(
% 0.21/0.46    v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~spl3_34),
% 0.21/0.46    inference(avatar_component_clause,[],[f277])).
% 0.21/0.46  fof(f287,plain,(
% 0.21/0.46    spl3_34 | ~spl3_18 | spl3_36 | ~spl3_32),
% 0.21/0.46    inference(avatar_split_clause,[],[f275,f266,f285,f183,f277])).
% 0.21/0.46  fof(f183,plain,(
% 0.21/0.46    spl3_18 <=> v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.21/0.46  fof(f266,plain,(
% 0.21/0.46    spl3_32 <=> v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).
% 0.21/0.46  fof(f275,plain,(
% 0.21/0.46    ( ! [X2,X3] : (~r2_hidden(X2,k10_yellow_6(X3,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) | ~m1_subset_1(X2,u1_struct_0(X3)) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),X3) | r2_waybel_7(X3,k2_yellow19(X3,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X2) | ~v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3)) ) | ~spl3_32),
% 0.21/0.46    inference(resolution,[],[f268,f53])).
% 0.21/0.46  fof(f53,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~v7_waybel_0(X1) | ~r2_hidden(X2,k10_yellow_6(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | r2_waybel_7(X0,k2_yellow19(X0,X1),X2) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f36])).
% 0.21/0.46  fof(f36,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,k10_yellow_6(X0,X1)) | ~r2_waybel_7(X0,k2_yellow19(X0,X1),X2)) & (r2_waybel_7(X0,k2_yellow19(X0,X1),X2) | ~r2_hidden(X2,k10_yellow_6(X0,X1)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.46    inference(nnf_transformation,[],[f19])).
% 0.21/0.46  fof(f19,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k10_yellow_6(X0,X1)) <=> r2_waybel_7(X0,k2_yellow19(X0,X1),X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.46    inference(flattening,[],[f18])).
% 0.21/0.46  fof(f18,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k10_yellow_6(X0,X1)) <=> r2_waybel_7(X0,k2_yellow19(X0,X1),X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f10])).
% 0.21/0.46  fof(f10,axiom,(
% 0.21/0.46    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,k10_yellow_6(X0,X1)) <=> r2_waybel_7(X0,k2_yellow19(X0,X1),X2)))))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_yellow19)).
% 0.21/0.46  fof(f268,plain,(
% 0.21/0.46    v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~spl3_32),
% 0.21/0.46    inference(avatar_component_clause,[],[f266])).
% 0.21/0.46  fof(f283,plain,(
% 0.21/0.46    spl3_34 | ~spl3_18 | spl3_35 | ~spl3_32),
% 0.21/0.46    inference(avatar_split_clause,[],[f274,f266,f281,f183,f277])).
% 0.21/0.46  fof(f274,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~r2_waybel_7(X0,k2_yellow19(X0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0) | r2_hidden(X1,k10_yellow_6(X0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) | ~v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) ) | ~spl3_32),
% 0.21/0.46    inference(resolution,[],[f268,f54])).
% 0.21/0.46  fof(f54,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~v7_waybel_0(X1) | ~r2_waybel_7(X0,k2_yellow19(X0,X1),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | r2_hidden(X2,k10_yellow_6(X0,X1)) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f36])).
% 0.21/0.46  fof(f269,plain,(
% 0.21/0.46    spl3_32 | ~spl3_4 | ~spl3_5 | ~spl3_6 | ~spl3_7 | spl3_8 | spl3_15 | ~spl3_25),
% 0.21/0.46    inference(avatar_split_clause,[],[f263,f225,f164,f118,f113,f108,f103,f98,f266])).
% 0.21/0.46  fof(f113,plain,(
% 0.21/0.46    spl3_7 <=> v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.46  fof(f225,plain,(
% 0.21/0.46    spl3_25 <=> ! [X1,X0] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | v7_waybel_0(k3_yellow19(sK0,X1,X0)) | v1_xboole_0(X1) | v1_xboole_0(X0) | ~v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1)))) | ~v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1))) | ~v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 0.21/0.46  fof(f263,plain,(
% 0.21/0.46    v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | (~spl3_4 | ~spl3_5 | ~spl3_6 | ~spl3_7 | spl3_8 | spl3_15 | ~spl3_25)),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f120,f166,f145,f105,f110,f115,f100,f226])).
% 0.21/0.46  fof(f226,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | v7_waybel_0(k3_yellow19(sK0,X1,X0)) | v1_xboole_0(X1) | v1_xboole_0(X0) | ~v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1)))) | ~v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1))) | ~v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))) ) | ~spl3_25),
% 0.21/0.46    inference(avatar_component_clause,[],[f225])).
% 0.21/0.46  fof(f100,plain,(
% 0.21/0.46    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) | ~spl3_4),
% 0.21/0.46    inference(avatar_component_clause,[],[f98])).
% 0.21/0.46  fof(f115,plain,(
% 0.21/0.46    v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))) | ~spl3_7),
% 0.21/0.46    inference(avatar_component_clause,[],[f113])).
% 0.21/0.46  fof(f110,plain,(
% 0.21/0.46    v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~spl3_6),
% 0.21/0.46    inference(avatar_component_clause,[],[f108])).
% 0.21/0.46  fof(f105,plain,(
% 0.21/0.46    v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~spl3_5),
% 0.21/0.46    inference(avatar_component_clause,[],[f103])).
% 0.21/0.46  fof(f166,plain,(
% 0.21/0.46    ~v1_xboole_0(k2_struct_0(sK0)) | spl3_15),
% 0.21/0.46    inference(avatar_component_clause,[],[f164])).
% 0.21/0.46  fof(f120,plain,(
% 0.21/0.46    ~v1_xboole_0(sK1) | spl3_8),
% 0.21/0.46    inference(avatar_component_clause,[],[f118])).
% 0.21/0.46  fof(f258,plain,(
% 0.21/0.46    spl3_30 | ~spl3_4 | ~spl3_5 | ~spl3_6 | spl3_8 | spl3_15 | ~spl3_24),
% 0.21/0.46    inference(avatar_split_clause,[],[f252,f219,f164,f118,f108,f103,f98,f255])).
% 0.21/0.46  fof(f219,plain,(
% 0.21/0.46    spl3_24 <=> ! [X1,X0] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | l1_waybel_0(k3_yellow19(sK0,X1,X0),sK0) | v1_xboole_0(X1) | v1_xboole_0(X0) | ~v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1))) | ~v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 0.21/0.46  fof(f252,plain,(
% 0.21/0.46    l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | (~spl3_4 | ~spl3_5 | ~spl3_6 | spl3_8 | spl3_15 | ~spl3_24)),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f120,f166,f145,f105,f110,f100,f220])).
% 0.21/0.46  fof(f220,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | l1_waybel_0(k3_yellow19(sK0,X1,X0),sK0) | v1_xboole_0(X1) | v1_xboole_0(X0) | ~v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1))) | ~v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))) ) | ~spl3_24),
% 0.21/0.46    inference(avatar_component_clause,[],[f219])).
% 0.21/0.46  fof(f247,plain,(
% 0.21/0.46    spl3_28 | ~spl3_4 | ~spl3_5 | ~spl3_6 | ~spl3_7 | spl3_8 | spl3_11 | ~spl3_12),
% 0.21/0.46    inference(avatar_split_clause,[],[f241,f140,f133,f118,f113,f108,f103,f98,f244])).
% 0.21/0.46  fof(f241,plain,(
% 0.21/0.46    sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | (~spl3_4 | ~spl3_5 | ~spl3_6 | ~spl3_7 | spl3_8 | spl3_11 | ~spl3_12)),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f135,f142,f120,f105,f110,f115,f100,f71])).
% 0.21/0.46  fof(f71,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~l1_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))))) | ~v13_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0)))) | ~v2_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0)))) | ~v1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))) | v1_xboole_0(X1) | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | v2_struct_0(X0)) )),
% 0.21/0.46    inference(definition_unfolding,[],[f56,f50,f50,f50,f50])).
% 0.21/0.46  fof(f56,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f23])).
% 0.21/0.46  fof(f23,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.46    inference(flattening,[],[f22])).
% 0.21/0.46  fof(f22,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f11])).
% 0.21/0.46  fof(f11,axiom,(
% 0.21/0.46    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_yellow19)).
% 0.21/0.46  fof(f142,plain,(
% 0.21/0.46    l1_struct_0(sK0) | ~spl3_12),
% 0.21/0.46    inference(avatar_component_clause,[],[f140])).
% 0.21/0.46  fof(f135,plain,(
% 0.21/0.46    ~v2_struct_0(sK0) | spl3_11),
% 0.21/0.46    inference(avatar_component_clause,[],[f133])).
% 0.21/0.46  fof(f227,plain,(
% 0.21/0.46    spl3_11 | spl3_25 | ~spl3_12 | ~spl3_13),
% 0.21/0.46    inference(avatar_split_clause,[],[f223,f149,f140,f225,f133])).
% 0.21/0.46  fof(f223,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | ~v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1))) | ~v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1)))) | v1_xboole_0(X0) | v1_xboole_0(X1) | v7_waybel_0(k3_yellow19(sK0,X1,X0)) | v2_struct_0(sK0)) ) | (~spl3_12 | ~spl3_13)),
% 0.21/0.46    inference(forward_demodulation,[],[f222,f151])).
% 0.21/0.46  fof(f222,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | ~v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1))) | ~v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1)))) | v1_xboole_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X1) | v7_waybel_0(k3_yellow19(sK0,X1,X0)) | v2_struct_0(sK0)) ) | ~spl3_12),
% 0.21/0.46    inference(resolution,[],[f79,f142])).
% 0.21/0.46  fof(f79,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~l1_struct_0(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | ~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X1)))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | v7_waybel_0(k3_yellow19(X0,X1,X2)) | v2_struct_0(X0)) )),
% 0.21/0.46    inference(definition_unfolding,[],[f66,f50,f50,f50,f50])).
% 0.21/0.46  fof(f66,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (v7_waybel_0(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f29])).
% 0.21/0.46  fof(f29,plain,(
% 0.21/0.46    ! [X0,X1,X2] : ((v7_waybel_0(k3_yellow19(X0,X1,X2)) & v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.46    inference(flattening,[],[f28])).
% 0.21/0.46  fof(f28,plain,(
% 0.21/0.46    ! [X0,X1,X2] : ((v7_waybel_0(k3_yellow19(X0,X1,X2)) & v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f9])).
% 0.21/0.46  fof(f9,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v7_waybel_0(k3_yellow19(X0,X1,X2)) & v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_yellow19)).
% 0.21/0.46  fof(f221,plain,(
% 0.21/0.46    spl3_11 | spl3_24 | ~spl3_12 | ~spl3_13),
% 0.21/0.46    inference(avatar_split_clause,[],[f217,f149,f140,f219,f133])).
% 0.21/0.46  fof(f217,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | ~v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1))) | v1_xboole_0(X0) | v1_xboole_0(X1) | l1_waybel_0(k3_yellow19(sK0,X1,X0),sK0) | v2_struct_0(sK0)) ) | (~spl3_12 | ~spl3_13)),
% 0.21/0.46    inference(forward_demodulation,[],[f216,f151])).
% 0.21/0.46  fof(f216,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | ~v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1))) | v1_xboole_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X1) | l1_waybel_0(k3_yellow19(sK0,X1,X0),sK0) | v2_struct_0(sK0)) ) | ~spl3_12),
% 0.21/0.46    inference(resolution,[],[f76,f142])).
% 0.21/0.46  fof(f76,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~l1_struct_0(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | ~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | l1_waybel_0(k3_yellow19(X0,X1,X2),X0) | v2_struct_0(X0)) )),
% 0.21/0.46    inference(definition_unfolding,[],[f63,f50,f50,f50])).
% 0.21/0.46  fof(f63,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (l1_waybel_0(k3_yellow19(X0,X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f27])).
% 0.21/0.46  fof(f27,plain,(
% 0.21/0.46    ! [X0,X1,X2] : ((l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.46    inference(flattening,[],[f26])).
% 0.21/0.46  fof(f26,plain,(
% 0.21/0.46    ! [X0,X1,X2] : ((l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f7])).
% 0.21/0.46  fof(f7,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_yellow19)).
% 0.21/0.46  fof(f186,plain,(
% 0.21/0.46    spl3_18 | ~spl3_4 | ~spl3_5 | ~spl3_6 | spl3_8 | spl3_15 | ~spl3_17),
% 0.21/0.46    inference(avatar_split_clause,[],[f180,f177,f164,f118,f108,f103,f98,f183])).
% 0.21/0.46  fof(f177,plain,(
% 0.21/0.46    spl3_17 <=> ! [X1,X0] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | v4_orders_2(k3_yellow19(sK0,X1,X0)) | v1_xboole_0(X1) | v1_xboole_0(X0) | ~v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1))) | ~v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.21/0.46  fof(f180,plain,(
% 0.21/0.46    v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | (~spl3_4 | ~spl3_5 | ~spl3_6 | spl3_8 | spl3_15 | ~spl3_17)),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f120,f166,f145,f105,f110,f100,f178])).
% 0.21/0.46  fof(f178,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | v4_orders_2(k3_yellow19(sK0,X1,X0)) | v1_xboole_0(X1) | v1_xboole_0(X0) | ~v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1))) | ~v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))) ) | ~spl3_17),
% 0.21/0.46    inference(avatar_component_clause,[],[f177])).
% 0.21/0.46  % (12399)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.46  fof(f179,plain,(
% 0.21/0.46    spl3_11 | spl3_17 | ~spl3_12 | ~spl3_13),
% 0.21/0.46    inference(avatar_split_clause,[],[f175,f149,f140,f177,f133])).
% 0.21/0.46  fof(f175,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | ~v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1))) | v1_xboole_0(X0) | v1_xboole_0(X1) | v4_orders_2(k3_yellow19(sK0,X1,X0)) | v2_struct_0(sK0)) ) | (~spl3_12 | ~spl3_13)),
% 0.21/0.46    inference(forward_demodulation,[],[f174,f151])).
% 0.21/0.46  fof(f174,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | ~v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1))) | v1_xboole_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X1) | v4_orders_2(k3_yellow19(sK0,X1,X0)) | v2_struct_0(sK0)) ) | ~spl3_12),
% 0.21/0.46    inference(resolution,[],[f73,f142])).
% 0.21/0.46  fof(f73,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~l1_struct_0(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | ~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | v4_orders_2(k3_yellow19(X0,X1,X2)) | v2_struct_0(X0)) )),
% 0.21/0.46    inference(definition_unfolding,[],[f59,f50,f50,f50])).
% 0.21/0.46  fof(f59,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (v4_orders_2(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f25])).
% 0.21/0.46  fof(f173,plain,(
% 0.21/0.46    spl3_11 | ~spl3_12 | ~spl3_15 | ~spl3_13),
% 0.21/0.46    inference(avatar_split_clause,[],[f162,f149,f164,f140,f133])).
% 0.21/0.46  fof(f162,plain,(
% 0.21/0.46    ~v1_xboole_0(k2_struct_0(sK0)) | ~l1_struct_0(sK0) | v2_struct_0(sK0) | ~spl3_13),
% 0.21/0.46    inference(superposition,[],[f55,f151])).
% 0.21/0.46  fof(f55,plain,(
% 0.21/0.46    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f21])).
% 0.21/0.46  fof(f21,plain,(
% 0.21/0.46    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.46    inference(flattening,[],[f20])).
% 0.21/0.46  fof(f20,plain,(
% 0.21/0.46    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f5])).
% 0.21/0.46  fof(f5,axiom,(
% 0.21/0.46    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.21/0.46  fof(f172,plain,(
% 0.21/0.46    spl3_16 | ~spl3_3 | ~spl3_13),
% 0.21/0.46    inference(avatar_split_clause,[],[f161,f149,f93,f169])).
% 0.21/0.46  fof(f93,plain,(
% 0.21/0.46    spl3_3 <=> m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.46  fof(f161,plain,(
% 0.21/0.46    m1_subset_1(sK2,k2_struct_0(sK0)) | (~spl3_3 | ~spl3_13)),
% 0.21/0.46    inference(backward_demodulation,[],[f95,f151])).
% 0.21/0.46  fof(f95,plain,(
% 0.21/0.46    m1_subset_1(sK2,u1_struct_0(sK0)) | ~spl3_3),
% 0.21/0.46    inference(avatar_component_clause,[],[f93])).
% 0.21/0.46  fof(f153,plain,(
% 0.21/0.46    spl3_13 | ~spl3_12),
% 0.21/0.46    inference(avatar_split_clause,[],[f147,f140,f149])).
% 0.21/0.46  fof(f147,plain,(
% 0.21/0.46    k2_struct_0(sK0) = u1_struct_0(sK0) | ~spl3_12),
% 0.21/0.46    inference(resolution,[],[f52,f142])).
% 0.21/0.46  fof(f52,plain,(
% 0.21/0.46    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f17])).
% 0.21/0.46  fof(f17,plain,(
% 0.21/0.46    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.21/0.46    inference(ennf_transformation,[],[f3])).
% 0.21/0.46  fof(f3,axiom,(
% 0.21/0.46    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.21/0.46  fof(f144,plain,(
% 0.21/0.46    spl3_12 | ~spl3_9),
% 0.21/0.46    inference(avatar_split_clause,[],[f138,f123,f140])).
% 0.21/0.46  fof(f138,plain,(
% 0.21/0.46    l1_struct_0(sK0) | ~spl3_9),
% 0.21/0.46    inference(resolution,[],[f51,f125])).
% 0.21/0.46  fof(f125,plain,(
% 0.21/0.46    l1_pre_topc(sK0) | ~spl3_9),
% 0.21/0.46    inference(avatar_component_clause,[],[f123])).
% 0.21/0.46  fof(f51,plain,(
% 0.21/0.46    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f16])).
% 0.21/0.46  fof(f16,plain,(
% 0.21/0.46    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.46    inference(ennf_transformation,[],[f4])).
% 0.21/0.46  fof(f4,axiom,(
% 0.21/0.46    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.46  fof(f136,plain,(
% 0.21/0.46    ~spl3_11),
% 0.21/0.46    inference(avatar_split_clause,[],[f37,f133])).
% 0.21/0.46  fof(f37,plain,(
% 0.21/0.46    ~v2_struct_0(sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f35])).
% 0.21/0.46  fof(f35,plain,(
% 0.21/0.46    (((~r2_waybel_7(sK0,sK1,sK2) | ~r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))) & (r2_waybel_7(sK0,sK1,sK2) | r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))) & m1_subset_1(sK2,u1_struct_0(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) & v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) & v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) & ~v1_xboole_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f31,f34,f33,f32])).
% 0.21/0.46  fof(f32,plain,(
% 0.21/0.46    ? [X0] : (? [X1] : (? [X2] : ((~r2_waybel_7(X0,X1,X2) | ~r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1)))) & (r2_waybel_7(X0,X1,X2) | r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1)))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((~r2_waybel_7(sK0,X1,X2) | ~r2_hidden(X2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1)))) & (r2_waybel_7(sK0,X1,X2) | r2_hidden(X2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1)))) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f33,plain,(
% 0.21/0.46    ? [X1] : (? [X2] : ((~r2_waybel_7(sK0,X1,X2) | ~r2_hidden(X2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1)))) & (r2_waybel_7(sK0,X1,X2) | r2_hidden(X2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1)))) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) & ~v1_xboole_0(X1)) => (? [X2] : ((~r2_waybel_7(sK0,sK1,X2) | ~r2_hidden(X2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))) & (r2_waybel_7(sK0,sK1,X2) | r2_hidden(X2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) & v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) & v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) & ~v1_xboole_0(sK1))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f34,plain,(
% 0.21/0.46    ? [X2] : ((~r2_waybel_7(sK0,sK1,X2) | ~r2_hidden(X2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))) & (r2_waybel_7(sK0,sK1,X2) | r2_hidden(X2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))) & m1_subset_1(X2,u1_struct_0(sK0))) => ((~r2_waybel_7(sK0,sK1,sK2) | ~r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))) & (r2_waybel_7(sK0,sK1,sK2) | r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))) & m1_subset_1(sK2,u1_struct_0(sK0)))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f31,plain,(
% 0.21/0.46    ? [X0] : (? [X1] : (? [X2] : ((~r2_waybel_7(X0,X1,X2) | ~r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1)))) & (r2_waybel_7(X0,X1,X2) | r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1)))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.46    inference(flattening,[],[f30])).
% 0.21/0.46  fof(f30,plain,(
% 0.21/0.46    ? [X0] : (? [X1] : (? [X2] : (((~r2_waybel_7(X0,X1,X2) | ~r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1)))) & (r2_waybel_7(X0,X1,X2) | r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1))))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.46    inference(nnf_transformation,[],[f15])).
% 0.21/0.46  fof(f15,plain,(
% 0.21/0.46    ? [X0] : (? [X1] : (? [X2] : ((r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1))) <~> r2_waybel_7(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.46    inference(flattening,[],[f14])).
% 0.21/0.46  fof(f14,plain,(
% 0.21/0.46    ? [X0] : (? [X1] : (? [X2] : ((r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1))) <~> r2_waybel_7(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f13])).
% 0.21/0.46  fof(f13,negated_conjecture,(
% 0.21/0.46    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1))) <=> r2_waybel_7(X0,X1,X2)))))),
% 0.21/0.46    inference(negated_conjecture,[],[f12])).
% 0.21/0.46  fof(f12,conjecture,(
% 0.21/0.46    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1))) <=> r2_waybel_7(X0,X1,X2)))))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_yellow19)).
% 0.21/0.46  fof(f131,plain,(
% 0.21/0.46    spl3_10),
% 0.21/0.46    inference(avatar_split_clause,[],[f38,f128])).
% 0.21/0.46  fof(f38,plain,(
% 0.21/0.46    v2_pre_topc(sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f35])).
% 0.21/0.46  fof(f126,plain,(
% 0.21/0.46    spl3_9),
% 0.21/0.46    inference(avatar_split_clause,[],[f39,f123])).
% 0.21/0.46  fof(f39,plain,(
% 0.21/0.46    l1_pre_topc(sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f35])).
% 0.21/0.46  fof(f121,plain,(
% 0.21/0.46    ~spl3_8),
% 0.21/0.46    inference(avatar_split_clause,[],[f40,f118])).
% 0.21/0.46  fof(f40,plain,(
% 0.21/0.46    ~v1_xboole_0(sK1)),
% 0.21/0.46    inference(cnf_transformation,[],[f35])).
% 0.21/0.46  fof(f116,plain,(
% 0.21/0.46    spl3_7),
% 0.21/0.46    inference(avatar_split_clause,[],[f70,f113])).
% 0.21/0.46  fof(f70,plain,(
% 0.21/0.46    v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))),
% 0.21/0.46    inference(definition_unfolding,[],[f41,f50])).
% 0.21/0.46  fof(f41,plain,(
% 0.21/0.46    v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))),
% 0.21/0.46    inference(cnf_transformation,[],[f35])).
% 0.21/0.46  fof(f111,plain,(
% 0.21/0.46    spl3_6),
% 0.21/0.46    inference(avatar_split_clause,[],[f69,f108])).
% 0.21/0.46  fof(f69,plain,(
% 0.21/0.46    v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))),
% 0.21/0.46    inference(definition_unfolding,[],[f42,f50])).
% 0.21/0.46  fof(f42,plain,(
% 0.21/0.46    v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))),
% 0.21/0.46    inference(cnf_transformation,[],[f35])).
% 0.21/0.46  fof(f106,plain,(
% 0.21/0.46    spl3_5),
% 0.21/0.46    inference(avatar_split_clause,[],[f68,f103])).
% 0.21/0.46  fof(f68,plain,(
% 0.21/0.46    v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))),
% 0.21/0.46    inference(definition_unfolding,[],[f43,f50])).
% 0.21/0.46  fof(f43,plain,(
% 0.21/0.46    v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))),
% 0.21/0.46    inference(cnf_transformation,[],[f35])).
% 0.21/0.46  fof(f101,plain,(
% 0.21/0.46    spl3_4),
% 0.21/0.46    inference(avatar_split_clause,[],[f67,f98])).
% 0.21/0.46  fof(f67,plain,(
% 0.21/0.46    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))),
% 0.21/0.46    inference(definition_unfolding,[],[f44,f50])).
% 0.21/0.46  fof(f44,plain,(
% 0.21/0.46    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))),
% 0.21/0.46    inference(cnf_transformation,[],[f35])).
% 0.21/0.46  fof(f96,plain,(
% 0.21/0.46    spl3_3),
% 0.21/0.46    inference(avatar_split_clause,[],[f45,f93])).
% 0.21/0.46  fof(f45,plain,(
% 0.21/0.46    m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.21/0.46    inference(cnf_transformation,[],[f35])).
% 0.21/0.46  fof(f91,plain,(
% 0.21/0.46    spl3_1 | spl3_2),
% 0.21/0.46    inference(avatar_split_clause,[],[f46,f87,f83])).
% 0.21/0.46  fof(f46,plain,(
% 0.21/0.46    r2_waybel_7(sK0,sK1,sK2) | r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))),
% 0.21/0.46    inference(cnf_transformation,[],[f35])).
% 0.21/0.46  fof(f90,plain,(
% 0.21/0.46    ~spl3_1 | ~spl3_2),
% 0.21/0.46    inference(avatar_split_clause,[],[f47,f87,f83])).
% 0.21/0.46  fof(f47,plain,(
% 0.21/0.46    ~r2_waybel_7(sK0,sK1,sK2) | ~r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))),
% 0.21/0.46    inference(cnf_transformation,[],[f35])).
% 0.21/0.46  % SZS output end Proof for theBenchmark
% 0.21/0.46  % (12401)------------------------------
% 0.21/0.46  % (12401)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (12401)Termination reason: Refutation
% 0.21/0.46  
% 0.21/0.46  % (12401)Memory used [KB]: 6396
% 0.21/0.46  % (12401)Time elapsed: 0.018 s
% 0.21/0.46  % (12401)------------------------------
% 0.21/0.46  % (12401)------------------------------
% 0.21/0.46  % (12393)Success in time 0.105 s
%------------------------------------------------------------------------------
