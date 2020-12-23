%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : yellow_0__t61_yellow_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:46 EDT 2019

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  159 ( 280 expanded)
%              Number of leaves         :   36 ( 110 expanded)
%              Depth                    :    9
%              Number of atoms          :  431 (1160 expanded)
%              Number of equality atoms :   33 ( 143 expanded)
%              Maximal formula depth    :   18 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1012,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f112,f118,f122,f126,f130,f140,f144,f150,f155,f161,f166,f170,f174,f182,f186,f190,f218,f241,f269,f290,f296,f366,f685,f980,f1011])).

fof(f1011,plain,
    ( ~ spl11_10
    | ~ spl11_24
    | spl11_29
    | ~ spl11_30
    | ~ spl11_194 ),
    inference(avatar_contradiction_clause,[],[f1010])).

fof(f1010,plain,
    ( $false
    | ~ spl11_10
    | ~ spl11_24
    | ~ spl11_29
    | ~ spl11_30
    | ~ spl11_194 ),
    inference(subsumption_resolution,[],[f1009,f185])).

fof(f185,plain,
    ( ~ r1_orders_2(sK1,sK2,sK3)
    | ~ spl11_29 ),
    inference(avatar_component_clause,[],[f184])).

fof(f184,plain,
    ( spl11_29
  <=> ~ r1_orders_2(sK1,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_29])])).

fof(f1009,plain,
    ( r1_orders_2(sK1,sK2,sK3)
    | ~ spl11_10
    | ~ spl11_24
    | ~ spl11_30
    | ~ spl11_194 ),
    inference(subsumption_resolution,[],[f1008,f139])).

fof(f139,plain,
    ( l1_orders_2(sK1)
    | ~ spl11_10 ),
    inference(avatar_component_clause,[],[f138])).

fof(f138,plain,
    ( spl11_10
  <=> l1_orders_2(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_10])])).

fof(f1008,plain,
    ( ~ l1_orders_2(sK1)
    | r1_orders_2(sK1,sK2,sK3)
    | ~ spl11_24
    | ~ spl11_30
    | ~ spl11_194 ),
    inference(subsumption_resolution,[],[f1007,f173])).

fof(f173,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ spl11_24 ),
    inference(avatar_component_clause,[],[f172])).

fof(f172,plain,
    ( spl11_24
  <=> m1_subset_1(sK3,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_24])])).

fof(f1007,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | r1_orders_2(sK1,sK2,sK3)
    | ~ spl11_30
    | ~ spl11_194 ),
    inference(subsumption_resolution,[],[f995,f189])).

fof(f189,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ spl11_30 ),
    inference(avatar_component_clause,[],[f188])).

fof(f188,plain,
    ( spl11_30
  <=> m1_subset_1(sK2,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_30])])).

fof(f995,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | r1_orders_2(sK1,sK2,sK3)
    | ~ spl11_194 ),
    inference(resolution,[],[f979,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_orders_2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t61_yellow_0.p',d9_orders_2)).

fof(f979,plain,
    ( r2_hidden(k4_tarski(sK2,sK3),u1_orders_2(sK1))
    | ~ spl11_194 ),
    inference(avatar_component_clause,[],[f978])).

fof(f978,plain,
    ( spl11_194
  <=> r2_hidden(k4_tarski(sK2,sK3),u1_orders_2(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_194])])).

fof(f980,plain,
    ( spl11_194
    | ~ spl11_52
    | ~ spl11_60
    | ~ spl11_140 ),
    inference(avatar_split_clause,[],[f976,f683,f294,f267,f978])).

fof(f267,plain,
    ( spl11_52
  <=> u1_orders_2(sK1) = k1_toler_1(u1_orders_2(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_52])])).

fof(f294,plain,
    ( spl11_60
  <=> v1_relat_1(u1_orders_2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_60])])).

fof(f683,plain,
    ( spl11_140
  <=> sP7(k4_tarski(sK2,sK3),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_orders_2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_140])])).

fof(f976,plain,
    ( r2_hidden(k4_tarski(sK2,sK3),u1_orders_2(sK1))
    | ~ spl11_52
    | ~ spl11_60
    | ~ spl11_140 ),
    inference(forward_demodulation,[],[f975,f268])).

fof(f268,plain,
    ( u1_orders_2(sK1) = k1_toler_1(u1_orders_2(sK0),u1_struct_0(sK1))
    | ~ spl11_52 ),
    inference(avatar_component_clause,[],[f267])).

fof(f975,plain,
    ( r2_hidden(k4_tarski(sK2,sK3),k1_toler_1(u1_orders_2(sK0),u1_struct_0(sK1)))
    | ~ spl11_60
    | ~ spl11_140 ),
    inference(forward_demodulation,[],[f974,f305])).

fof(f305,plain,
    ( ! [X2] : k3_xboole_0(u1_orders_2(sK0),k2_zfmisc_1(X2,X2)) = k1_toler_1(u1_orders_2(sK0),X2)
    | ~ spl11_60 ),
    inference(forward_demodulation,[],[f303,f302])).

fof(f302,plain,
    ( ! [X1] : k1_toler_1(u1_orders_2(sK0),X1) = k2_wellord1(u1_orders_2(sK0),X1)
    | ~ spl11_60 ),
    inference(resolution,[],[f295,f104])).

fof(f104,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k1_toler_1(X0,X1) = k2_wellord1(X0,X1) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k1_toler_1(X0,X1) = k2_wellord1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => k1_toler_1(X0,X1) = k2_wellord1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t61_yellow_0.p',redefinition_k1_toler_1)).

fof(f295,plain,
    ( v1_relat_1(u1_orders_2(sK0))
    | ~ spl11_60 ),
    inference(avatar_component_clause,[],[f294])).

fof(f303,plain,
    ( ! [X2] : k3_xboole_0(u1_orders_2(sK0),k2_zfmisc_1(X2,X2)) = k2_wellord1(u1_orders_2(sK0),X2)
    | ~ spl11_60 ),
    inference(resolution,[],[f295,f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k3_xboole_0(X0,k2_zfmisc_1(X1,X1)) = k2_wellord1(X0,X1) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] : k3_xboole_0(X0,k2_zfmisc_1(X1,X1)) = k2_wellord1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k3_xboole_0(X0,k2_zfmisc_1(X1,X1)) = k2_wellord1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t61_yellow_0.p',d6_wellord1)).

fof(f974,plain,
    ( r2_hidden(k4_tarski(sK2,sK3),k3_xboole_0(u1_orders_2(sK0),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ spl11_140 ),
    inference(resolution,[],[f684,f107])).

fof(f107,plain,(
    ! [X0,X3,X1] :
      ( ~ sP7(X3,X1,X0)
      | r2_hidden(X3,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP7(X3,X1,X0)
      | r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t61_yellow_0.p',d4_xboole_0)).

fof(f684,plain,
    ( sP7(k4_tarski(sK2,sK3),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_orders_2(sK0))
    | ~ spl11_140 ),
    inference(avatar_component_clause,[],[f683])).

fof(f685,plain,
    ( spl11_140
    | ~ spl11_42
    | ~ spl11_78 ),
    inference(avatar_split_clause,[],[f442,f364,f239,f683])).

fof(f239,plain,
    ( spl11_42
  <=> r2_hidden(k4_tarski(sK2,sK3),u1_orders_2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_42])])).

fof(f364,plain,
    ( spl11_78
  <=> r2_hidden(k4_tarski(sK2,sK3),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_78])])).

fof(f442,plain,
    ( sP7(k4_tarski(sK2,sK3),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_orders_2(sK0))
    | ~ spl11_42
    | ~ spl11_78 ),
    inference(resolution,[],[f248,f365])).

fof(f365,plain,
    ( r2_hidden(k4_tarski(sK2,sK3),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))
    | ~ spl11_78 ),
    inference(avatar_component_clause,[],[f364])).

fof(f248,plain,
    ( ! [X1] :
        ( ~ r2_hidden(k4_tarski(sK2,sK3),X1)
        | sP7(k4_tarski(sK2,sK3),X1,u1_orders_2(sK0)) )
    | ~ spl11_42 ),
    inference(resolution,[],[f240,f74])).

fof(f74,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X1)
      | sP7(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f240,plain,
    ( r2_hidden(k4_tarski(sK2,sK3),u1_orders_2(sK0))
    | ~ spl11_42 ),
    inference(avatar_component_clause,[],[f239])).

fof(f366,plain,
    ( spl11_78
    | ~ spl11_26
    | ~ spl11_38 ),
    inference(avatar_split_clause,[],[f299,f216,f180,f364])).

fof(f180,plain,
    ( spl11_26
  <=> r2_hidden(sK2,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_26])])).

fof(f216,plain,
    ( spl11_38
  <=> r2_hidden(sK3,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_38])])).

fof(f299,plain,
    ( r2_hidden(k4_tarski(sK2,sK3),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))
    | ~ spl11_26
    | ~ spl11_38 ),
    inference(resolution,[],[f200,f217])).

fof(f217,plain,
    ( r2_hidden(sK3,u1_struct_0(sK1))
    | ~ spl11_38 ),
    inference(avatar_component_clause,[],[f216])).

fof(f200,plain,
    ( ! [X4,X3] :
        ( ~ r2_hidden(X3,X4)
        | r2_hidden(k4_tarski(sK2,X3),k2_zfmisc_1(u1_struct_0(sK1),X4)) )
    | ~ spl11_26 ),
    inference(resolution,[],[f181,f103])).

fof(f103,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X1,X3)
      | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t61_yellow_0.p',t106_zfmisc_1)).

fof(f181,plain,
    ( r2_hidden(sK2,u1_struct_0(sK1))
    | ~ spl11_26 ),
    inference(avatar_component_clause,[],[f180])).

fof(f296,plain,
    ( spl11_60
    | ~ spl11_58 ),
    inference(avatar_split_clause,[],[f291,f288,f294])).

fof(f288,plain,
    ( spl11_58
  <=> m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_58])])).

fof(f291,plain,
    ( v1_relat_1(u1_orders_2(sK0))
    | ~ spl11_58 ),
    inference(resolution,[],[f289,f98])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f38])).

fof(f38,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t61_yellow_0.p',cc1_relset_1)).

fof(f289,plain,
    ( m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ spl11_58 ),
    inference(avatar_component_clause,[],[f288])).

fof(f290,plain,
    ( spl11_58
    | ~ spl11_0 ),
    inference(avatar_split_clause,[],[f114,f110,f288])).

fof(f110,plain,
    ( spl11_0
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_0])])).

fof(f114,plain,
    ( m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ spl11_0 ),
    inference(resolution,[],[f111,f94])).

fof(f94,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t61_yellow_0.p',dt_u1_orders_2)).

fof(f111,plain,
    ( l1_orders_2(sK0)
    | ~ spl11_0 ),
    inference(avatar_component_clause,[],[f110])).

fof(f269,plain,
    ( spl11_52
    | ~ spl11_0
    | ~ spl11_6
    | ~ spl11_8 ),
    inference(avatar_split_clause,[],[f136,f128,f124,f110,f267])).

fof(f124,plain,
    ( spl11_6
  <=> v4_yellow_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_6])])).

fof(f128,plain,
    ( spl11_8
  <=> m1_yellow_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_8])])).

fof(f136,plain,
    ( u1_orders_2(sK1) = k1_toler_1(u1_orders_2(sK0),u1_struct_0(sK1))
    | ~ spl11_0
    | ~ spl11_6
    | ~ spl11_8 ),
    inference(subsumption_resolution,[],[f135,f125])).

fof(f125,plain,
    ( v4_yellow_0(sK1,sK0)
    | ~ spl11_6 ),
    inference(avatar_component_clause,[],[f124])).

fof(f135,plain,
    ( u1_orders_2(sK1) = k1_toler_1(u1_orders_2(sK0),u1_struct_0(sK1))
    | ~ v4_yellow_0(sK1,sK0)
    | ~ spl11_0
    | ~ spl11_8 ),
    inference(subsumption_resolution,[],[f133,f111])).

fof(f133,plain,
    ( ~ l1_orders_2(sK0)
    | u1_orders_2(sK1) = k1_toler_1(u1_orders_2(sK0),u1_struct_0(sK1))
    | ~ v4_yellow_0(sK1,sK0)
    | ~ spl11_8 ),
    inference(resolution,[],[f129,f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X0)
      | u1_orders_2(X1) = k1_toler_1(u1_orders_2(X0),u1_struct_0(X1))
      | ~ v4_yellow_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_yellow_0(X1,X0)
          <=> u1_orders_2(X1) = k1_toler_1(u1_orders_2(X0),u1_struct_0(X1)) )
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_yellow_0(X1,X0)
         => ( v4_yellow_0(X1,X0)
          <=> u1_orders_2(X1) = k1_toler_1(u1_orders_2(X0),u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t61_yellow_0.p',d14_yellow_0)).

fof(f129,plain,
    ( m1_yellow_0(sK1,sK0)
    | ~ spl11_8 ),
    inference(avatar_component_clause,[],[f128])).

fof(f241,plain,
    ( spl11_42
    | ~ spl11_0
    | ~ spl11_12
    | ~ spl11_20
    | ~ spl11_22 ),
    inference(avatar_split_clause,[],[f178,f168,f164,f142,f110,f239])).

fof(f142,plain,
    ( spl11_12
  <=> r1_orders_2(sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_12])])).

fof(f164,plain,
    ( spl11_20
  <=> m1_subset_1(sK3,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_20])])).

fof(f168,plain,
    ( spl11_22
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_22])])).

fof(f178,plain,
    ( r2_hidden(k4_tarski(sK2,sK3),u1_orders_2(sK0))
    | ~ spl11_0
    | ~ spl11_12
    | ~ spl11_20
    | ~ spl11_22 ),
    inference(subsumption_resolution,[],[f177,f111])).

fof(f177,plain,
    ( r2_hidden(k4_tarski(sK2,sK3),u1_orders_2(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl11_12
    | ~ spl11_20
    | ~ spl11_22 ),
    inference(subsumption_resolution,[],[f176,f165])).

fof(f165,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl11_20 ),
    inference(avatar_component_clause,[],[f164])).

fof(f176,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | r2_hidden(k4_tarski(sK2,sK3),u1_orders_2(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl11_12
    | ~ spl11_22 ),
    inference(subsumption_resolution,[],[f175,f169])).

fof(f169,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl11_22 ),
    inference(avatar_component_clause,[],[f168])).

fof(f175,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | r2_hidden(k4_tarski(sK2,sK3),u1_orders_2(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl11_12 ),
    inference(resolution,[],[f143,f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f143,plain,
    ( r1_orders_2(sK0,sK2,sK3)
    | ~ spl11_12 ),
    inference(avatar_component_clause,[],[f142])).

fof(f218,plain,
    ( spl11_38
    | ~ spl11_24
    | ~ spl11_26 ),
    inference(avatar_split_clause,[],[f201,f180,f172,f216])).

fof(f201,plain,
    ( r2_hidden(sK3,u1_struct_0(sK1))
    | ~ spl11_24
    | ~ spl11_26 ),
    inference(subsumption_resolution,[],[f193,f197])).

fof(f197,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | ~ spl11_26 ),
    inference(resolution,[],[f181,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t61_yellow_0.p',t7_boole)).

fof(f193,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | r2_hidden(sK3,u1_struct_0(sK1))
    | ~ spl11_24 ),
    inference(resolution,[],[f173,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t61_yellow_0.p',t2_subset)).

fof(f190,plain,
    ( spl11_30
    | ~ spl11_2
    | ~ spl11_18 ),
    inference(avatar_split_clause,[],[f162,f159,f116,f188])).

fof(f116,plain,
    ( spl11_2
  <=> sK2 = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f159,plain,
    ( spl11_18
  <=> m1_subset_1(sK4,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_18])])).

fof(f162,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ spl11_2
    | ~ spl11_18 ),
    inference(forward_demodulation,[],[f160,f117])).

fof(f117,plain,
    ( sK2 = sK4
    | ~ spl11_2 ),
    inference(avatar_component_clause,[],[f116])).

fof(f160,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK1))
    | ~ spl11_18 ),
    inference(avatar_component_clause,[],[f159])).

fof(f186,plain,
    ( ~ spl11_29
    | ~ spl11_2
    | ~ spl11_4
    | spl11_17 ),
    inference(avatar_split_clause,[],[f157,f153,f120,f116,f184])).

fof(f120,plain,
    ( spl11_4
  <=> sK3 = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).

fof(f153,plain,
    ( spl11_17
  <=> ~ r1_orders_2(sK1,sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_17])])).

fof(f157,plain,
    ( ~ r1_orders_2(sK1,sK2,sK3)
    | ~ spl11_2
    | ~ spl11_4
    | ~ spl11_17 ),
    inference(forward_demodulation,[],[f156,f117])).

fof(f156,plain,
    ( ~ r1_orders_2(sK1,sK4,sK3)
    | ~ spl11_4
    | ~ spl11_17 ),
    inference(forward_demodulation,[],[f154,f121])).

fof(f121,plain,
    ( sK3 = sK5
    | ~ spl11_4 ),
    inference(avatar_component_clause,[],[f120])).

fof(f154,plain,
    ( ~ r1_orders_2(sK1,sK4,sK5)
    | ~ spl11_17 ),
    inference(avatar_component_clause,[],[f153])).

fof(f182,plain,
    ( spl11_26
    | ~ spl11_2
    | ~ spl11_14 ),
    inference(avatar_split_clause,[],[f151,f148,f116,f180])).

fof(f148,plain,
    ( spl11_14
  <=> r2_hidden(sK4,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_14])])).

fof(f151,plain,
    ( r2_hidden(sK2,u1_struct_0(sK1))
    | ~ spl11_2
    | ~ spl11_14 ),
    inference(forward_demodulation,[],[f149,f117])).

fof(f149,plain,
    ( r2_hidden(sK4,u1_struct_0(sK1))
    | ~ spl11_14 ),
    inference(avatar_component_clause,[],[f148])).

fof(f174,plain,(
    spl11_24 ),
    inference(avatar_split_clause,[],[f108,f172])).

fof(f108,plain,(
    m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(forward_demodulation,[],[f61,f63])).

fof(f63,plain,(
    sK3 = sK5 ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ~ r1_orders_2(X1,X4,X5)
                          & r2_hidden(X4,u1_struct_0(X1))
                          & r1_orders_2(X0,X2,X3)
                          & X3 = X5
                          & X2 = X4
                          & m1_subset_1(X5,u1_struct_0(X1)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_yellow_0(X1,X0)
          & v4_yellow_0(X1,X0) )
      & l1_orders_2(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ~ r1_orders_2(X1,X4,X5)
                          & r2_hidden(X4,u1_struct_0(X1))
                          & r1_orders_2(X0,X2,X3)
                          & X3 = X5
                          & X2 = X4
                          & m1_subset_1(X5,u1_struct_0(X1)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_yellow_0(X1,X0)
          & v4_yellow_0(X1,X0) )
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => ! [X1] :
            ( ( m1_yellow_0(X1,X0)
              & v4_yellow_0(X1,X0) )
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X1))
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X1))
                           => ( ( r2_hidden(X4,u1_struct_0(X1))
                                & r1_orders_2(X0,X2,X3)
                                & X3 = X5
                                & X2 = X4 )
                             => r1_orders_2(X1,X4,X5) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( ( m1_yellow_0(X1,X0)
            & v4_yellow_0(X1,X0) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X1))
                         => ( ( r2_hidden(X4,u1_struct_0(X1))
                              & r1_orders_2(X0,X2,X3)
                              & X3 = X5
                              & X2 = X4 )
                           => r1_orders_2(X1,X4,X5) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t61_yellow_0.p',t61_yellow_0)).

fof(f61,plain,(
    m1_subset_1(sK5,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f41])).

fof(f170,plain,(
    spl11_22 ),
    inference(avatar_split_clause,[],[f69,f168])).

fof(f69,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f41])).

fof(f166,plain,(
    spl11_20 ),
    inference(avatar_split_clause,[],[f68,f164])).

fof(f68,plain,(
    m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f41])).

fof(f161,plain,(
    spl11_18 ),
    inference(avatar_split_clause,[],[f67,f159])).

fof(f67,plain,(
    m1_subset_1(sK4,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f41])).

fof(f155,plain,(
    ~ spl11_17 ),
    inference(avatar_split_clause,[],[f66,f153])).

fof(f66,plain,(
    ~ r1_orders_2(sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f41])).

fof(f150,plain,(
    spl11_14 ),
    inference(avatar_split_clause,[],[f65,f148])).

fof(f65,plain,(
    r2_hidden(sK4,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f41])).

fof(f144,plain,(
    spl11_12 ),
    inference(avatar_split_clause,[],[f64,f142])).

fof(f64,plain,(
    r1_orders_2(sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f41])).

fof(f140,plain,
    ( spl11_10
    | ~ spl11_0
    | ~ spl11_8 ),
    inference(avatar_split_clause,[],[f134,f128,f110,f138])).

fof(f134,plain,
    ( l1_orders_2(sK1)
    | ~ spl11_0
    | ~ spl11_8 ),
    inference(subsumption_resolution,[],[f131,f111])).

fof(f131,plain,
    ( ~ l1_orders_2(sK0)
    | l1_orders_2(sK1)
    | ~ spl11_8 ),
    inference(resolution,[],[f129,f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( ~ m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X0)
      | l1_orders_2(X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_orders_2(X1)
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_yellow_0(X1,X0)
         => l1_orders_2(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t61_yellow_0.p',dt_m1_yellow_0)).

fof(f130,plain,(
    spl11_8 ),
    inference(avatar_split_clause,[],[f71,f128])).

fof(f71,plain,(
    m1_yellow_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f126,plain,(
    spl11_6 ),
    inference(avatar_split_clause,[],[f70,f124])).

fof(f70,plain,(
    v4_yellow_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f122,plain,(
    spl11_4 ),
    inference(avatar_split_clause,[],[f63,f120])).

fof(f118,plain,(
    spl11_2 ),
    inference(avatar_split_clause,[],[f62,f116])).

fof(f62,plain,(
    sK2 = sK4 ),
    inference(cnf_transformation,[],[f41])).

fof(f112,plain,(
    spl11_0 ),
    inference(avatar_split_clause,[],[f72,f110])).

fof(f72,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f41])).
%------------------------------------------------------------------------------
