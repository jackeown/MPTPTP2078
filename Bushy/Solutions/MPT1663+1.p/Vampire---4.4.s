%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : waybel_0__t43_waybel_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:50 EDT 2019

% Result     : Theorem 2.00s
% Output     : Refutation 2.00s
% Verified   : 
% Statistics : Number of formulae       :  323 ( 715 expanded)
%              Number of leaves         :   59 ( 252 expanded)
%              Depth                    :   25
%              Number of atoms          : 1599 (3560 expanded)
%              Number of equality atoms :   35 (  97 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1243,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f174,f181,f188,f195,f202,f209,f216,f261,f276,f334,f412,f424,f427,f468,f479,f487,f538,f540,f551,f742,f772,f794,f852,f880,f937,f1047,f1057,f1064,f1127,f1198,f1202,f1215,f1238,f1242])).

fof(f1242,plain,
    ( spl17_49
    | ~ spl17_126 ),
    inference(avatar_contradiction_clause,[],[f1241])).

fof(f1241,plain,
    ( $false
    | ~ spl17_49
    | ~ spl17_126 ),
    inference(subsumption_resolution,[],[f1240,f458])).

fof(f458,plain,
    ( k1_xboole_0 != sK8(sK0,sK1)
    | ~ spl17_49 ),
    inference(avatar_component_clause,[],[f457])).

fof(f457,plain,
    ( spl17_49
  <=> k1_xboole_0 != sK8(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_49])])).

fof(f1240,plain,
    ( k1_xboole_0 = sK8(sK0,sK1)
    | ~ spl17_126 ),
    inference(resolution,[],[f1191,f114])).

fof(f114,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t43_waybel_0.p',t6_boole)).

fof(f1191,plain,
    ( v1_xboole_0(sK8(sK0,sK1))
    | ~ spl17_126 ),
    inference(avatar_component_clause,[],[f1190])).

fof(f1190,plain,
    ( spl17_126
  <=> v1_xboole_0(sK8(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_126])])).

fof(f1238,plain,
    ( spl17_59
    | ~ spl17_92
    | spl17_131 ),
    inference(avatar_contradiction_clause,[],[f1237])).

fof(f1237,plain,
    ( $false
    | ~ spl17_59
    | ~ spl17_92
    | ~ spl17_131 ),
    inference(subsumption_resolution,[],[f1236,f513])).

fof(f513,plain,
    ( ~ sP7(sK1,sK0)
    | ~ spl17_59 ),
    inference(avatar_component_clause,[],[f512])).

fof(f512,plain,
    ( spl17_59
  <=> ~ sP7(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_59])])).

fof(f1236,plain,
    ( sP7(sK1,sK0)
    | ~ spl17_92
    | ~ spl17_131 ),
    inference(subsumption_resolution,[],[f1234,f928])).

fof(f928,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl17_92 ),
    inference(avatar_component_clause,[],[f927])).

fof(f927,plain,
    ( spl17_92
  <=> r1_tarski(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_92])])).

fof(f1234,plain,
    ( ~ r1_tarski(sK1,u1_struct_0(sK0))
    | sP7(sK1,sK0)
    | ~ spl17_131 ),
    inference(resolution,[],[f1228,f126])).

fof(f126,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK8(X0,X1),k1_zfmisc_1(X1))
      | sP7(X1,X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) )
          <=> ! [X2] :
                ( ? [X3] :
                    ( r1_lattice3(X0,X2,X3)
                    & r2_hidden(X3,X1)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
                | ~ v1_finset_1(X2) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) )
          <=> ! [X2] :
                ( ? [X3] :
                    ( r1_lattice3(X0,X2,X3)
                    & r2_hidden(X3,X1)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
                | ~ v1_finset_1(X2) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v2_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) )
          <=> ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
                  & v1_finset_1(X2) )
               => ? [X3] :
                    ( r1_lattice3(X0,X2,X3)
                    & r2_hidden(X3,X1)
                    & m1_subset_1(X3,u1_struct_0(X0)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t43_waybel_0.p',t2_waybel_0)).

fof(f1228,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(sK8(sK0,sK1),k1_zfmisc_1(X2))
        | ~ r1_tarski(X2,u1_struct_0(sK0)) )
    | ~ spl17_131 ),
    inference(resolution,[],[f1218,f151])).

fof(f151,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t43_waybel_0.p',t3_subset)).

fof(f1218,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK8(sK0,sK1),X0)
        | ~ r1_tarski(X0,u1_struct_0(sK0)) )
    | ~ spl17_131 ),
    inference(resolution,[],[f1214,f154])).

fof(f154,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f79,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f78])).

fof(f78,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t43_waybel_0.p',t1_xboole_1)).

fof(f1214,plain,
    ( ~ r1_tarski(sK8(sK0,sK1),u1_struct_0(sK0))
    | ~ spl17_131 ),
    inference(avatar_component_clause,[],[f1213])).

fof(f1213,plain,
    ( spl17_131
  <=> ~ r1_tarski(sK8(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_131])])).

fof(f1215,plain,
    ( ~ spl17_131
    | spl17_129 ),
    inference(avatar_split_clause,[],[f1205,f1196,f1213])).

fof(f1196,plain,
    ( spl17_129
  <=> ~ m1_subset_1(sK8(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_129])])).

fof(f1205,plain,
    ( ~ r1_tarski(sK8(sK0,sK1),u1_struct_0(sK0))
    | ~ spl17_129 ),
    inference(resolution,[],[f1197,f150])).

fof(f150,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f1197,plain,
    ( ~ m1_subset_1(sK8(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl17_129 ),
    inference(avatar_component_clause,[],[f1196])).

fof(f1202,plain,
    ( spl17_59
    | spl17_125 ),
    inference(avatar_contradiction_clause,[],[f1201])).

fof(f1201,plain,
    ( $false
    | ~ spl17_59
    | ~ spl17_125 ),
    inference(subsumption_resolution,[],[f1199,f513])).

fof(f1199,plain,
    ( sP7(sK1,sK0)
    | ~ spl17_125 ),
    inference(resolution,[],[f1185,f125])).

fof(f125,plain,(
    ! [X0,X1] :
      ( v1_finset_1(sK8(X0,X1))
      | sP7(X1,X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f1185,plain,
    ( ~ v1_finset_1(sK8(sK0,sK1))
    | ~ spl17_125 ),
    inference(avatar_component_clause,[],[f1184])).

fof(f1184,plain,
    ( spl17_125
  <=> ~ v1_finset_1(sK8(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_125])])).

fof(f1198,plain,
    ( ~ spl17_125
    | spl17_126
    | ~ spl17_129
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8
    | ~ spl17_10
    | spl17_25
    | spl17_113 ),
    inference(avatar_split_clause,[],[f1135,f1125,f291,f207,f200,f193,f186,f179,f1196,f1190,f1184])).

fof(f179,plain,
    ( spl17_2
  <=> v3_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_2])])).

fof(f186,plain,
    ( spl17_4
  <=> v4_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_4])])).

fof(f193,plain,
    ( spl17_6
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_6])])).

fof(f200,plain,
    ( spl17_8
  <=> v2_lattice3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_8])])).

fof(f207,plain,
    ( spl17_10
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_10])])).

fof(f291,plain,
    ( spl17_25
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_25])])).

fof(f1125,plain,
    ( spl17_113
  <=> ~ r1_lattice3(sK0,sK8(sK0,sK1),k2_yellow_0(sK0,sK8(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_113])])).

fof(f1135,plain,
    ( ~ m1_subset_1(sK8(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK8(sK0,sK1))
    | ~ v1_finset_1(sK8(sK0,sK1))
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8
    | ~ spl17_10
    | ~ spl17_25
    | ~ spl17_113 ),
    inference(resolution,[],[f1126,f353])).

fof(f353,plain,
    ( ! [X0] :
        ( r1_lattice3(sK0,X0,k2_yellow_0(sK0,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X0)
        | ~ v1_finset_1(X0) )
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8
    | ~ spl17_10
    | ~ spl17_25 ),
    inference(resolution,[],[f350,f282])).

fof(f282,plain,
    ( ! [X2] :
        ( ~ r2_yellow_0(sK0,X2)
        | r1_lattice3(sK0,X2,k2_yellow_0(sK0,X2)) )
    | ~ spl17_6
    | ~ spl17_10 ),
    inference(subsumption_resolution,[],[f281,f194])).

fof(f194,plain,
    ( v5_orders_2(sK0)
    | ~ spl17_6 ),
    inference(avatar_component_clause,[],[f193])).

fof(f281,plain,
    ( ! [X2] :
        ( ~ v5_orders_2(sK0)
        | ~ r2_yellow_0(sK0,X2)
        | r1_lattice3(sK0,X2,k2_yellow_0(sK0,X2)) )
    | ~ spl17_10 ),
    inference(subsumption_resolution,[],[f278,f208])).

fof(f208,plain,
    ( l1_orders_2(sK0)
    | ~ spl17_10 ),
    inference(avatar_component_clause,[],[f207])).

fof(f278,plain,
    ( ! [X2] :
        ( ~ l1_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ r2_yellow_0(sK0,X2)
        | r1_lattice3(sK0,X2,k2_yellow_0(sK0,X2)) )
    | ~ spl17_10 ),
    inference(resolution,[],[f231,f166])).

fof(f166,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(k2_yellow_0(X0,X2),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ r2_yellow_0(X0,X2)
      | r1_lattice3(X0,X2,k2_yellow_0(X0,X2)) ) ),
    inference(equality_resolution,[],[f137])).

fof(f137,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | k2_yellow_0(X0,X2) != X1
      | ~ r2_yellow_0(X0,X2)
      | r1_lattice3(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_yellow_0(X0,X2)
                  & k2_yellow_0(X0,X2) = X1 )
                | ? [X3] :
                    ( ~ r1_orders_2(X0,X3,X1)
                    & r1_lattice3(X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r1_lattice3(X0,X2,X1) )
              & ( ( ! [X4] :
                      ( r1_orders_2(X0,X4,X1)
                      | ~ r1_lattice3(X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r1_lattice3(X0,X2,X1) )
                | ~ r2_yellow_0(X0,X2)
                | k2_yellow_0(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f61])).

fof(f61,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_yellow_0(X0,X2)
                  & k2_yellow_0(X0,X2) = X1 )
                | ? [X3] :
                    ( ~ r1_orders_2(X0,X3,X1)
                    & r1_lattice3(X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r1_lattice3(X0,X2,X1) )
              & ( ( ! [X4] :
                      ( r1_orders_2(X0,X4,X1)
                      | ~ r1_lattice3(X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r1_lattice3(X0,X2,X1) )
                | ~ r2_yellow_0(X0,X2)
                | k2_yellow_0(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r1_lattice3(X0,X2,X3)
                       => r1_orders_2(X0,X3,X1) ) )
                  & r1_lattice3(X0,X2,X1) )
               => ( r2_yellow_0(X0,X2)
                  & k2_yellow_0(X0,X2) = X1 ) )
              & ( ( r2_yellow_0(X0,X2)
                  & k2_yellow_0(X0,X2) = X1 )
               => ( ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X0))
                     => ( r1_lattice3(X0,X2,X4)
                       => r1_orders_2(X0,X4,X1) ) )
                  & r1_lattice3(X0,X2,X1) ) ) ) ) ) ),
    inference(rectify,[],[f32])).

fof(f32,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r1_lattice3(X0,X2,X3)
                       => r1_orders_2(X0,X3,X1) ) )
                  & r1_lattice3(X0,X2,X1) )
               => ( r2_yellow_0(X0,X2)
                  & k2_yellow_0(X0,X2) = X1 ) )
              & ( ( r2_yellow_0(X0,X2)
                  & k2_yellow_0(X0,X2) = X1 )
               => ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r1_lattice3(X0,X2,X3)
                       => r1_orders_2(X0,X3,X1) ) )
                  & r1_lattice3(X0,X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t43_waybel_0.p',t31_yellow_0)).

fof(f231,plain,
    ( ! [X20] : m1_subset_1(k2_yellow_0(sK0,X20),u1_struct_0(sK0))
    | ~ spl17_10 ),
    inference(resolution,[],[f208,f141])).

fof(f141,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t43_waybel_0.p',dt_k2_yellow_0)).

fof(f350,plain,
    ( ! [X8] :
        ( r2_yellow_0(sK0,X8)
        | ~ v1_finset_1(X8)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X8) )
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8
    | ~ spl17_10
    | ~ spl17_25 ),
    inference(subsumption_resolution,[],[f237,f292])).

fof(f292,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl17_25 ),
    inference(avatar_component_clause,[],[f291])).

fof(f237,plain,
    ( ! [X8] :
        ( v2_struct_0(sK0)
        | v1_xboole_0(X8)
        | ~ v1_finset_1(X8)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_yellow_0(sK0,X8) )
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8
    | ~ spl17_10 ),
    inference(subsumption_resolution,[],[f236,f201])).

fof(f201,plain,
    ( v2_lattice3(sK0)
    | ~ spl17_8 ),
    inference(avatar_component_clause,[],[f200])).

fof(f236,plain,
    ( ! [X8] :
        ( v2_struct_0(sK0)
        | v1_xboole_0(X8)
        | ~ v1_finset_1(X8)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_yellow_0(sK0,X8)
        | ~ v2_lattice3(sK0) )
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_10 ),
    inference(subsumption_resolution,[],[f235,f194])).

fof(f235,plain,
    ( ! [X8] :
        ( ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | v1_xboole_0(X8)
        | ~ v1_finset_1(X8)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_yellow_0(sK0,X8)
        | ~ v2_lattice3(sK0) )
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_10 ),
    inference(subsumption_resolution,[],[f234,f187])).

fof(f187,plain,
    ( v4_orders_2(sK0)
    | ~ spl17_4 ),
    inference(avatar_component_clause,[],[f186])).

fof(f234,plain,
    ( ! [X8] :
        ( ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | v1_xboole_0(X8)
        | ~ v1_finset_1(X8)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_yellow_0(sK0,X8)
        | ~ v2_lattice3(sK0) )
    | ~ spl17_2
    | ~ spl17_10 ),
    inference(subsumption_resolution,[],[f223,f180])).

fof(f180,plain,
    ( v3_orders_2(sK0)
    | ~ spl17_2 ),
    inference(avatar_component_clause,[],[f179])).

fof(f223,plain,
    ( ! [X8] :
        ( ~ v3_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | v1_xboole_0(X8)
        | ~ v1_finset_1(X8)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_yellow_0(sK0,X8)
        | ~ v2_lattice3(sK0) )
    | ~ spl17_10 ),
    inference(resolution,[],[f208,f116])).

fof(f116,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0)
      | v1_xboole_0(X1)
      | ~ v1_finset_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_yellow_0(X0,X1)
      | ~ v2_lattice3(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ( v2_lattice3(X0)
      <=> ! [X1] :
            ( r2_yellow_0(X0,X1)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v1_finset_1(X1)
            | v1_xboole_0(X1) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ( v2_lattice3(X0)
      <=> ! [X1] :
            ( r2_yellow_0(X0,X1)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v1_finset_1(X1)
            | v1_xboole_0(X1) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f35])).

fof(f35,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( v2_lattice3(X0)
      <=> ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_finset_1(X1)
              & ~ v1_xboole_0(X1) )
           => r2_yellow_0(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t43_waybel_0.p',t55_yellow_0)).

fof(f1126,plain,
    ( ~ r1_lattice3(sK0,sK8(sK0,sK1),k2_yellow_0(sK0,sK8(sK0,sK1)))
    | ~ spl17_113 ),
    inference(avatar_component_clause,[],[f1125])).

fof(f1127,plain,
    ( ~ spl17_113
    | ~ spl17_4
    | ~ spl17_10
    | ~ spl17_20
    | spl17_25
    | ~ spl17_50
    | spl17_59 ),
    inference(avatar_split_clause,[],[f1075,f512,f466,f291,f274,f207,f186,f1125])).

fof(f274,plain,
    ( spl17_20
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_20])])).

fof(f466,plain,
    ( spl17_50
  <=> r2_hidden(k2_yellow_0(sK0,sK8(sK0,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_50])])).

fof(f1075,plain,
    ( ~ r1_lattice3(sK0,sK8(sK0,sK1),k2_yellow_0(sK0,sK8(sK0,sK1)))
    | ~ spl17_4
    | ~ spl17_10
    | ~ spl17_20
    | ~ spl17_25
    | ~ spl17_50
    | ~ spl17_59 ),
    inference(subsumption_resolution,[],[f1074,f513])).

fof(f1074,plain,
    ( ~ r1_lattice3(sK0,sK8(sK0,sK1),k2_yellow_0(sK0,sK8(sK0,sK1)))
    | sP7(sK1,sK0)
    | ~ spl17_4
    | ~ spl17_10
    | ~ spl17_20
    | ~ spl17_25
    | ~ spl17_50 ),
    inference(subsumption_resolution,[],[f1071,f275])).

fof(f275,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl17_20 ),
    inference(avatar_component_clause,[],[f274])).

fof(f1071,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_lattice3(sK0,sK8(sK0,sK1),k2_yellow_0(sK0,sK8(sK0,sK1)))
    | sP7(sK1,sK0)
    | ~ spl17_4
    | ~ spl17_10
    | ~ spl17_25
    | ~ spl17_50 ),
    inference(resolution,[],[f467,f393])).

fof(f393,plain,
    ( ! [X2,X1] :
        ( ~ r2_hidden(X2,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_lattice3(sK0,sK8(sK0,X1),X2)
        | sP7(X1,sK0) )
    | ~ spl17_4
    | ~ spl17_10
    | ~ spl17_25 ),
    inference(subsumption_resolution,[],[f391,f153])).

fof(f153,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f39])).

fof(f39,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t43_waybel_0.p',t7_boole)).

fof(f391,plain,
    ( ! [X2,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X2,X1)
        | ~ r1_lattice3(sK0,sK8(sK0,X1),X2)
        | sP7(X1,sK0)
        | v1_xboole_0(X1) )
    | ~ spl17_4
    | ~ spl17_10
    | ~ spl17_25 ),
    inference(duplicate_literal_removal,[],[f390])).

fof(f390,plain,
    ( ! [X2,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X2,X1)
        | ~ r1_lattice3(sK0,sK8(sK0,X1),X2)
        | sP7(X1,sK0)
        | v1_xboole_0(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl17_4
    | ~ spl17_10
    | ~ spl17_25 ),
    inference(resolution,[],[f339,f340])).

fof(f340,plain,
    ( ! [X9] :
        ( ~ v2_waybel_0(X9,sK0)
        | sP7(X9,sK0)
        | v1_xboole_0(X9)
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl17_4
    | ~ spl17_10
    | ~ spl17_25 ),
    inference(subsumption_resolution,[],[f238,f292])).

fof(f238,plain,
    ( ! [X9] :
        ( v2_struct_0(sK0)
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK0)))
        | sP7(X9,sK0)
        | v1_xboole_0(X9)
        | ~ v2_waybel_0(X9,sK0) )
    | ~ spl17_4
    | ~ spl17_10 ),
    inference(subsumption_resolution,[],[f224,f187])).

fof(f224,plain,
    ( ! [X9] :
        ( ~ v4_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK0)))
        | sP7(X9,sK0)
        | v1_xboole_0(X9)
        | ~ v2_waybel_0(X9,sK0) )
    | ~ spl17_10 ),
    inference(resolution,[],[f208,f127])).

fof(f127,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | sP7(X1,X0)
      | v1_xboole_0(X1)
      | ~ v2_waybel_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f339,plain,
    ( ! [X0,X1] :
        ( v2_waybel_0(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X1,X0)
        | ~ r1_lattice3(sK0,sK8(sK0,X0),X1) )
    | ~ spl17_4
    | ~ spl17_10
    | ~ spl17_25 ),
    inference(subsumption_resolution,[],[f338,f155])).

fof(f155,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f81])).

fof(f81,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f80])).

fof(f80,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t43_waybel_0.p',t4_subset)).

fof(f338,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_waybel_0(X0,sK0)
        | ~ r2_hidden(X1,X0)
        | ~ r1_lattice3(sK0,sK8(sK0,X0),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl17_4
    | ~ spl17_10
    | ~ spl17_25 ),
    inference(resolution,[],[f335,f124])).

fof(f124,plain,(
    ! [X0,X3,X1] :
      ( sP7(X1,X0)
      | ~ r2_hidden(X3,X1)
      | ~ r1_lattice3(X0,sK8(X0,X1),X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f335,plain,
    ( ! [X11] :
        ( ~ sP7(X11,sK0)
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_waybel_0(X11,sK0) )
    | ~ spl17_4
    | ~ spl17_10
    | ~ spl17_25 ),
    inference(subsumption_resolution,[],[f240,f292])).

fof(f240,plain,
    ( ! [X11] :
        ( v2_struct_0(sK0)
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ sP7(X11,sK0)
        | v2_waybel_0(X11,sK0) )
    | ~ spl17_4
    | ~ spl17_10 ),
    inference(subsumption_resolution,[],[f226,f187])).

fof(f226,plain,
    ( ! [X11] :
        ( ~ v4_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ sP7(X11,sK0)
        | v2_waybel_0(X11,sK0) )
    | ~ spl17_10 ),
    inference(resolution,[],[f208,f129])).

fof(f129,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ sP7(X1,X0)
      | v2_waybel_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f467,plain,
    ( r2_hidden(k2_yellow_0(sK0,sK8(sK0,sK1)),sK1)
    | ~ spl17_50 ),
    inference(avatar_component_clause,[],[f466])).

fof(f1064,plain,
    ( spl17_1
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8
    | ~ spl17_10
    | ~ spl17_12
    | ~ spl17_20
    | spl17_39
    | spl17_107 ),
    inference(avatar_contradiction_clause,[],[f1063])).

fof(f1063,plain,
    ( $false
    | ~ spl17_1
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8
    | ~ spl17_10
    | ~ spl17_12
    | ~ spl17_20
    | ~ spl17_39
    | ~ spl17_107 ),
    inference(subsumption_resolution,[],[f1062,f215])).

fof(f215,plain,
    ( v13_waybel_0(sK1,sK0)
    | ~ spl17_12 ),
    inference(avatar_component_clause,[],[f214])).

fof(f214,plain,
    ( spl17_12
  <=> v13_waybel_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_12])])).

fof(f1062,plain,
    ( ~ v13_waybel_0(sK1,sK0)
    | ~ spl17_1
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8
    | ~ spl17_10
    | ~ spl17_20
    | ~ spl17_39
    | ~ spl17_107 ),
    inference(subsumption_resolution,[],[f1061,f173])).

fof(f173,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl17_1 ),
    inference(avatar_component_clause,[],[f172])).

fof(f172,plain,
    ( spl17_1
  <=> ~ v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_1])])).

fof(f1061,plain,
    ( v1_xboole_0(sK1)
    | ~ v13_waybel_0(sK1,sK0)
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8
    | ~ spl17_10
    | ~ spl17_20
    | ~ spl17_39
    | ~ spl17_107 ),
    inference(subsumption_resolution,[],[f1060,f275])).

fof(f1060,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | ~ v13_waybel_0(sK1,sK0)
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8
    | ~ spl17_10
    | ~ spl17_39
    | ~ spl17_107 ),
    inference(resolution,[],[f1056,f435])).

fof(f435,plain,
    ( ! [X1] :
        ( m1_subset_1(o_2_8_waybel_0(sK0,X1),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X1)
        | ~ v13_waybel_0(X1,sK0) )
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8
    | ~ spl17_10
    | ~ spl17_39 ),
    inference(subsumption_resolution,[],[f357,f405])).

fof(f405,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl17_39 ),
    inference(avatar_component_clause,[],[f404])).

fof(f404,plain,
    ( spl17_39
  <=> ~ v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_39])])).

fof(f357,plain,
    ( ! [X1] :
        ( ~ v13_waybel_0(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X1)
        | v1_xboole_0(u1_struct_0(sK0))
        | m1_subset_1(o_2_8_waybel_0(sK0,X1),u1_struct_0(sK0)) )
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8
    | ~ spl17_10 ),
    inference(duplicate_literal_removal,[],[f356])).

fof(f356,plain,
    ( ! [X1] :
        ( ~ v13_waybel_0(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X1)
        | v1_xboole_0(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(u1_struct_0(sK0))
        | m1_subset_1(o_2_8_waybel_0(sK0,X1),u1_struct_0(sK0)) )
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8
    | ~ spl17_10 ),
    inference(resolution,[],[f248,f145])).

fof(f145,plain,(
    ! [X2,X0,X1] :
      ( ~ m2_subset_1(X2,X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X0)
      | m1_subset_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,X0)
          | ~ m2_subset_1(X2,X0,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,X0)
          | ~ m2_subset_1(X2,X0,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X0))
        & ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ! [X2] :
          ( m2_subset_1(X2,X0,X1)
         => m1_subset_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t43_waybel_0.p',dt_m2_subset_1)).

fof(f248,plain,
    ( ! [X21] :
        ( m2_subset_1(o_2_8_waybel_0(sK0,X21),u1_struct_0(sK0),X21)
        | ~ v13_waybel_0(X21,sK0)
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X21) )
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8
    | ~ spl17_10 ),
    inference(subsumption_resolution,[],[f247,f180])).

fof(f247,plain,
    ( ! [X21] :
        ( ~ v3_orders_2(sK0)
        | v1_xboole_0(X21)
        | ~ v13_waybel_0(X21,sK0)
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(sK0)))
        | m2_subset_1(o_2_8_waybel_0(sK0,X21),u1_struct_0(sK0),X21) )
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8
    | ~ spl17_10 ),
    inference(subsumption_resolution,[],[f246,f201])).

fof(f246,plain,
    ( ! [X21] :
        ( ~ v2_lattice3(sK0)
        | ~ v3_orders_2(sK0)
        | v1_xboole_0(X21)
        | ~ v13_waybel_0(X21,sK0)
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(sK0)))
        | m2_subset_1(o_2_8_waybel_0(sK0,X21),u1_struct_0(sK0),X21) )
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_10 ),
    inference(subsumption_resolution,[],[f245,f194])).

fof(f245,plain,
    ( ! [X21] :
        ( ~ v5_orders_2(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v3_orders_2(sK0)
        | v1_xboole_0(X21)
        | ~ v13_waybel_0(X21,sK0)
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(sK0)))
        | m2_subset_1(o_2_8_waybel_0(sK0,X21),u1_struct_0(sK0),X21) )
    | ~ spl17_4
    | ~ spl17_10 ),
    inference(subsumption_resolution,[],[f232,f187])).

fof(f232,plain,
    ( ! [X21] :
        ( ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v3_orders_2(sK0)
        | v1_xboole_0(X21)
        | ~ v13_waybel_0(X21,sK0)
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(sK0)))
        | m2_subset_1(o_2_8_waybel_0(sK0,X21),u1_struct_0(sK0),X21) )
    | ~ spl17_10 ),
    inference(resolution,[],[f208,f149])).

fof(f149,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v3_orders_2(X0)
      | v1_xboole_0(X1)
      | ~ v13_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m2_subset_1(o_2_8_waybel_0(X0,X1),u1_struct_0(X0),X1) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( m2_subset_1(o_2_8_waybel_0(X0,X1),u1_struct_0(X0),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( m2_subset_1(o_2_8_waybel_0(X0,X1),u1_struct_0(X0),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & v13_waybel_0(X1,X0)
        & ~ v1_xboole_0(X1)
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => m2_subset_1(o_2_8_waybel_0(X0,X1),u1_struct_0(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t43_waybel_0.p',dt_o_2_8_waybel_0)).

fof(f1056,plain,
    ( ~ m1_subset_1(o_2_8_waybel_0(sK0,sK1),u1_struct_0(sK0))
    | ~ spl17_107 ),
    inference(avatar_component_clause,[],[f1055])).

fof(f1055,plain,
    ( spl17_107
  <=> ~ m1_subset_1(o_2_8_waybel_0(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_107])])).

fof(f1057,plain,
    ( ~ spl17_107
    | ~ spl17_10
    | spl17_105 ),
    inference(avatar_split_clause,[],[f1048,f1045,f207,f1055])).

fof(f1045,plain,
    ( spl17_105
  <=> ~ r1_lattice3(sK0,k1_xboole_0,o_2_8_waybel_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_105])])).

fof(f1048,plain,
    ( ~ m1_subset_1(o_2_8_waybel_0(sK0,sK1),u1_struct_0(sK0))
    | ~ spl17_10
    | ~ spl17_105 ),
    inference(resolution,[],[f1046,f218])).

fof(f218,plain,
    ( ! [X1] :
        ( r1_lattice3(sK0,k1_xboole_0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl17_10 ),
    inference(resolution,[],[f208,f103])).

fof(f103,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r1_lattice3(X0,k1_xboole_0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_lattice3(X0,k1_xboole_0,X1)
            & r2_lattice3(X0,k1_xboole_0,X1) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f38])).

fof(f38,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( r1_lattice3(X0,k1_xboole_0,X1)
            & r2_lattice3(X0,k1_xboole_0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t43_waybel_0.p',t6_yellow_0)).

fof(f1046,plain,
    ( ~ r1_lattice3(sK0,k1_xboole_0,o_2_8_waybel_0(sK0,sK1))
    | ~ spl17_105 ),
    inference(avatar_component_clause,[],[f1045])).

fof(f1047,plain,
    ( ~ spl17_105
    | spl17_1
    | ~ spl17_4
    | ~ spl17_10
    | ~ spl17_12
    | spl17_15
    | ~ spl17_20
    | spl17_25
    | ~ spl17_40
    | ~ spl17_48 ),
    inference(avatar_split_clause,[],[f998,f460,f410,f291,f274,f253,f214,f207,f186,f172,f1045])).

fof(f253,plain,
    ( spl17_15
  <=> ~ v2_waybel_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_15])])).

fof(f410,plain,
    ( spl17_40
  <=> ! [X0] :
        ( ~ v13_waybel_0(X0,sK0)
        | m1_subset_1(o_2_8_waybel_0(sK0,X0),X0)
        | v1_xboole_0(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_40])])).

fof(f460,plain,
    ( spl17_48
  <=> k1_xboole_0 = sK8(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_48])])).

fof(f998,plain,
    ( ~ r1_lattice3(sK0,k1_xboole_0,o_2_8_waybel_0(sK0,sK1))
    | ~ spl17_1
    | ~ spl17_4
    | ~ spl17_10
    | ~ spl17_12
    | ~ spl17_15
    | ~ spl17_20
    | ~ spl17_25
    | ~ spl17_40
    | ~ spl17_48 ),
    inference(subsumption_resolution,[],[f997,f275])).

fof(f997,plain,
    ( ~ r1_lattice3(sK0,k1_xboole_0,o_2_8_waybel_0(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl17_1
    | ~ spl17_4
    | ~ spl17_10
    | ~ spl17_12
    | ~ spl17_15
    | ~ spl17_20
    | ~ spl17_25
    | ~ spl17_40
    | ~ spl17_48 ),
    inference(subsumption_resolution,[],[f996,f173])).

fof(f996,plain,
    ( ~ r1_lattice3(sK0,k1_xboole_0,o_2_8_waybel_0(sK0,sK1))
    | v1_xboole_0(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl17_1
    | ~ spl17_4
    | ~ spl17_10
    | ~ spl17_12
    | ~ spl17_15
    | ~ spl17_20
    | ~ spl17_25
    | ~ spl17_40
    | ~ spl17_48 ),
    inference(subsumption_resolution,[],[f995,f215])).

fof(f995,plain,
    ( ~ r1_lattice3(sK0,k1_xboole_0,o_2_8_waybel_0(sK0,sK1))
    | ~ v13_waybel_0(sK1,sK0)
    | v1_xboole_0(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl17_1
    | ~ spl17_4
    | ~ spl17_10
    | ~ spl17_15
    | ~ spl17_20
    | ~ spl17_25
    | ~ spl17_40
    | ~ spl17_48 ),
    inference(resolution,[],[f978,f411])).

fof(f411,plain,
    ( ! [X0] :
        ( m1_subset_1(o_2_8_waybel_0(sK0,X0),X0)
        | ~ v13_waybel_0(X0,sK0)
        | v1_xboole_0(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl17_40 ),
    inference(avatar_component_clause,[],[f410])).

fof(f978,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,sK1)
        | ~ r1_lattice3(sK0,k1_xboole_0,X2) )
    | ~ spl17_1
    | ~ spl17_4
    | ~ spl17_10
    | ~ spl17_15
    | ~ spl17_20
    | ~ spl17_25
    | ~ spl17_48 ),
    inference(subsumption_resolution,[],[f977,f173])).

fof(f977,plain,
    ( ! [X2] :
        ( ~ r1_lattice3(sK0,k1_xboole_0,X2)
        | v1_xboole_0(sK1)
        | ~ m1_subset_1(X2,sK1) )
    | ~ spl17_4
    | ~ spl17_10
    | ~ spl17_15
    | ~ spl17_20
    | ~ spl17_25
    | ~ spl17_48 ),
    inference(resolution,[],[f975,f144])).

fof(f144,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t43_waybel_0.p',t2_subset)).

fof(f975,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK1)
        | ~ r1_lattice3(sK0,k1_xboole_0,X1) )
    | ~ spl17_4
    | ~ spl17_10
    | ~ spl17_15
    | ~ spl17_20
    | ~ spl17_25
    | ~ spl17_48 ),
    inference(forward_demodulation,[],[f886,f461])).

fof(f461,plain,
    ( k1_xboole_0 = sK8(sK0,sK1)
    | ~ spl17_48 ),
    inference(avatar_component_clause,[],[f460])).

fof(f886,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK1)
        | ~ r1_lattice3(sK0,sK8(sK0,sK1),X1) )
    | ~ spl17_4
    | ~ spl17_10
    | ~ spl17_15
    | ~ spl17_20
    | ~ spl17_25 ),
    inference(subsumption_resolution,[],[f882,f275])).

fof(f882,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X1,sK1)
        | ~ r1_lattice3(sK0,sK8(sK0,sK1),X1) )
    | ~ spl17_4
    | ~ spl17_10
    | ~ spl17_15
    | ~ spl17_25 ),
    inference(resolution,[],[f254,f339])).

fof(f254,plain,
    ( ~ v2_waybel_0(sK1,sK0)
    | ~ spl17_15 ),
    inference(avatar_component_clause,[],[f253])).

fof(f937,plain,
    ( ~ spl17_20
    | spl17_93 ),
    inference(avatar_contradiction_clause,[],[f936])).

fof(f936,plain,
    ( $false
    | ~ spl17_20
    | ~ spl17_93 ),
    inference(subsumption_resolution,[],[f935,f275])).

fof(f935,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl17_93 ),
    inference(resolution,[],[f931,f151])).

fof(f931,plain,
    ( ~ r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl17_93 ),
    inference(avatar_component_clause,[],[f930])).

fof(f930,plain,
    ( spl17_93
  <=> ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_93])])).

fof(f880,plain,
    ( ~ spl17_18
    | spl17_53 ),
    inference(avatar_contradiction_clause,[],[f879])).

fof(f879,plain,
    ( $false
    | ~ spl17_18
    | ~ spl17_53 ),
    inference(subsumption_resolution,[],[f878,f478])).

fof(f478,plain,
    ( k1_xboole_0 != sK2
    | ~ spl17_53 ),
    inference(avatar_component_clause,[],[f477])).

fof(f477,plain,
    ( spl17_53
  <=> k1_xboole_0 != sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_53])])).

fof(f878,plain,
    ( k1_xboole_0 = sK2
    | ~ spl17_18 ),
    inference(resolution,[],[f265,f114])).

fof(f265,plain,
    ( v1_xboole_0(sK2)
    | ~ spl17_18 ),
    inference(avatar_component_clause,[],[f264])).

fof(f264,plain,
    ( spl17_18
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_18])])).

fof(f852,plain,
    ( ~ spl17_4
    | ~ spl17_10
    | spl17_15
    | ~ spl17_20
    | spl17_25
    | ~ spl17_58 ),
    inference(avatar_contradiction_clause,[],[f851])).

fof(f851,plain,
    ( $false
    | ~ spl17_4
    | ~ spl17_10
    | ~ spl17_15
    | ~ spl17_20
    | ~ spl17_25
    | ~ spl17_58 ),
    inference(subsumption_resolution,[],[f795,f254])).

fof(f795,plain,
    ( v2_waybel_0(sK1,sK0)
    | ~ spl17_4
    | ~ spl17_10
    | ~ spl17_20
    | ~ spl17_25
    | ~ spl17_58 ),
    inference(subsumption_resolution,[],[f552,f275])).

fof(f552,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_waybel_0(sK1,sK0)
    | ~ spl17_4
    | ~ spl17_10
    | ~ spl17_25
    | ~ spl17_58 ),
    inference(resolution,[],[f516,f335])).

fof(f516,plain,
    ( sP7(sK1,sK0)
    | ~ spl17_58 ),
    inference(avatar_component_clause,[],[f515])).

fof(f515,plain,
    ( spl17_58
  <=> sP7(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_58])])).

fof(f794,plain,
    ( ~ spl17_20
    | ~ spl17_56
    | spl17_85 ),
    inference(avatar_contradiction_clause,[],[f793])).

fof(f793,plain,
    ( $false
    | ~ spl17_20
    | ~ spl17_56
    | ~ spl17_85 ),
    inference(subsumption_resolution,[],[f790,f275])).

fof(f790,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl17_56
    | ~ spl17_85 ),
    inference(resolution,[],[f786,f493])).

fof(f493,plain,
    ( r1_tarski(sK2,sK1)
    | ~ spl17_56 ),
    inference(avatar_component_clause,[],[f492])).

fof(f492,plain,
    ( spl17_56
  <=> r1_tarski(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_56])])).

fof(f786,plain,
    ( ! [X2] :
        ( ~ r1_tarski(sK2,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl17_85 ),
    inference(resolution,[],[f775,f151])).

fof(f775,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK0))
        | ~ r1_tarski(sK2,X0) )
    | ~ spl17_85 ),
    inference(resolution,[],[f771,f154])).

fof(f771,plain,
    ( ~ r1_tarski(sK2,u1_struct_0(sK0))
    | ~ spl17_85 ),
    inference(avatar_component_clause,[],[f770])).

fof(f770,plain,
    ( spl17_85
  <=> ~ r1_tarski(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_85])])).

fof(f772,plain,
    ( ~ spl17_85
    | spl17_79 ),
    inference(avatar_split_clause,[],[f744,f740,f770])).

fof(f740,plain,
    ( spl17_79
  <=> ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_79])])).

fof(f744,plain,
    ( ~ r1_tarski(sK2,u1_struct_0(sK0))
    | ~ spl17_79 ),
    inference(resolution,[],[f741,f150])).

fof(f741,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl17_79 ),
    inference(avatar_component_clause,[],[f740])).

fof(f742,plain,
    ( ~ spl17_79
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8
    | ~ spl17_10
    | ~ spl17_12
    | ~ spl17_16
    | spl17_19
    | ~ spl17_20
    | spl17_25
    | ~ spl17_54
    | ~ spl17_58
    | spl17_63 ),
    inference(avatar_split_clause,[],[f733,f536,f515,f485,f291,f274,f267,f259,f214,f207,f200,f193,f186,f179,f740])).

fof(f259,plain,
    ( spl17_16
  <=> v1_finset_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_16])])).

fof(f267,plain,
    ( spl17_19
  <=> ~ v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_19])])).

fof(f485,plain,
    ( spl17_54
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_54])])).

fof(f536,plain,
    ( spl17_63
  <=> ~ r2_hidden(k2_yellow_0(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_63])])).

fof(f733,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8
    | ~ spl17_10
    | ~ spl17_12
    | ~ spl17_16
    | ~ spl17_19
    | ~ spl17_20
    | ~ spl17_25
    | ~ spl17_54
    | ~ spl17_58
    | ~ spl17_63 ),
    inference(subsumption_resolution,[],[f732,f486])).

fof(f486,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK1))
    | ~ spl17_54 ),
    inference(avatar_component_clause,[],[f485])).

fof(f732,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8
    | ~ spl17_10
    | ~ spl17_12
    | ~ spl17_16
    | ~ spl17_19
    | ~ spl17_20
    | ~ spl17_25
    | ~ spl17_58
    | ~ spl17_63 ),
    inference(subsumption_resolution,[],[f731,f537])).

fof(f537,plain,
    ( ~ r2_hidden(k2_yellow_0(sK0,sK2),sK1)
    | ~ spl17_63 ),
    inference(avatar_component_clause,[],[f536])).

fof(f731,plain,
    ( r2_hidden(k2_yellow_0(sK0,sK2),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8
    | ~ spl17_10
    | ~ spl17_12
    | ~ spl17_16
    | ~ spl17_19
    | ~ spl17_20
    | ~ spl17_25
    | ~ spl17_58 ),
    inference(subsumption_resolution,[],[f728,f268])).

fof(f268,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ spl17_19 ),
    inference(avatar_component_clause,[],[f267])).

fof(f728,plain,
    ( v1_xboole_0(sK2)
    | r2_hidden(k2_yellow_0(sK0,sK2),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8
    | ~ spl17_10
    | ~ spl17_12
    | ~ spl17_16
    | ~ spl17_20
    | ~ spl17_25
    | ~ spl17_58 ),
    inference(resolution,[],[f709,f260])).

fof(f260,plain,
    ( v1_finset_1(sK2)
    | ~ spl17_16 ),
    inference(avatar_component_clause,[],[f259])).

fof(f709,plain,
    ( ! [X6] :
        ( ~ v1_finset_1(X6)
        | v1_xboole_0(X6)
        | r2_hidden(k2_yellow_0(sK0,X6),sK1)
        | ~ m1_subset_1(X6,k1_zfmisc_1(sK1))
        | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8
    | ~ spl17_10
    | ~ spl17_12
    | ~ spl17_20
    | ~ spl17_25
    | ~ spl17_58 ),
    inference(subsumption_resolution,[],[f708,f215])).

fof(f708,plain,
    ( ! [X6] :
        ( v1_xboole_0(X6)
        | ~ v1_finset_1(X6)
        | r2_hidden(k2_yellow_0(sK0,X6),sK1)
        | ~ v13_waybel_0(sK1,sK0)
        | ~ m1_subset_1(X6,k1_zfmisc_1(sK1))
        | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8
    | ~ spl17_10
    | ~ spl17_20
    | ~ spl17_25
    | ~ spl17_58 ),
    inference(subsumption_resolution,[],[f704,f275])).

fof(f704,plain,
    ( ! [X6] :
        ( v1_xboole_0(X6)
        | ~ v1_finset_1(X6)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(k2_yellow_0(sK0,X6),sK1)
        | ~ v13_waybel_0(sK1,sK0)
        | ~ m1_subset_1(X6,k1_zfmisc_1(sK1))
        | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8
    | ~ spl17_10
    | ~ spl17_25
    | ~ spl17_58 ),
    inference(resolution,[],[f661,f516])).

fof(f661,plain,
    ( ! [X4,X3] :
        ( ~ sP7(X4,sK0)
        | v1_xboole_0(X3)
        | ~ v1_finset_1(X3)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(k2_yellow_0(sK0,X3),X4)
        | ~ v13_waybel_0(X4,sK0)
        | ~ m1_subset_1(X3,k1_zfmisc_1(X4))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8
    | ~ spl17_10
    | ~ spl17_25 ),
    inference(duplicate_literal_removal,[],[f660])).

fof(f660,plain,
    ( ! [X4,X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X3)
        | ~ v1_finset_1(X3)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(k2_yellow_0(sK0,X3),X4)
        | ~ v13_waybel_0(X4,sK0)
        | ~ m1_subset_1(X3,k1_zfmisc_1(X4))
        | ~ v1_finset_1(X3)
        | ~ sP7(X4,sK0)
        | ~ m1_subset_1(X3,k1_zfmisc_1(X4))
        | ~ v1_finset_1(X3)
        | ~ sP7(X4,sK0) )
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8
    | ~ spl17_10
    | ~ spl17_25 ),
    inference(resolution,[],[f603,f123])).

fof(f123,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X2,sK9(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
      | ~ v1_finset_1(X2)
      | ~ sP7(X1,X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f603,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r1_lattice3(sK0,X0,sK9(X1,X2,X3))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X0)
        | ~ v1_finset_1(X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(k2_yellow_0(sK0,X0),X2)
        | ~ v13_waybel_0(X2,sK0)
        | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
        | ~ v1_finset_1(X3)
        | ~ sP7(X2,X1) )
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8
    | ~ spl17_10
    | ~ spl17_25 ),
    inference(resolution,[],[f584,f122])).

fof(f122,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK9(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
      | ~ v1_finset_1(X2)
      | ~ sP7(X1,X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f584,plain,
    ( ! [X6,X4,X5] :
        ( ~ r2_hidden(X5,X6)
        | ~ v1_finset_1(X4)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X4)
        | ~ r1_lattice3(sK0,X4,X5)
        | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(k2_yellow_0(sK0,X4),X6)
        | ~ v13_waybel_0(X6,sK0) )
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8
    | ~ spl17_10
    | ~ spl17_25 ),
    inference(subsumption_resolution,[],[f583,f155])).

fof(f583,plain,
    ( ! [X6,X4,X5] :
        ( ~ r1_lattice3(sK0,X4,X5)
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ v1_finset_1(X4)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X4)
        | ~ r2_hidden(X5,X6)
        | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(k2_yellow_0(sK0,X4),X6)
        | ~ v13_waybel_0(X6,sK0) )
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8
    | ~ spl17_10
    | ~ spl17_25 ),
    inference(subsumption_resolution,[],[f580,f231])).

fof(f580,plain,
    ( ! [X6,X4,X5] :
        ( ~ r1_lattice3(sK0,X4,X5)
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ v1_finset_1(X4)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X4)
        | ~ m1_subset_1(k2_yellow_0(sK0,X4),u1_struct_0(sK0))
        | ~ r2_hidden(X5,X6)
        | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(k2_yellow_0(sK0,X4),X6)
        | ~ v13_waybel_0(X6,sK0) )
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8
    | ~ spl17_10
    | ~ spl17_25 ),
    inference(resolution,[],[f388,f233])).

fof(f233,plain,
    ( ! [X6,X7,X5] :
        ( ~ r1_orders_2(sK0,X6,X7)
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | ~ r2_hidden(X6,X5)
        | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X7,X5)
        | ~ v13_waybel_0(X5,sK0) )
    | ~ spl17_10 ),
    inference(subsumption_resolution,[],[f222,f155])).

fof(f222,plain,
    ( ! [X6,X7,X5] :
        ( ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | ~ r2_hidden(X6,X5)
        | ~ r1_orders_2(sK0,X6,X7)
        | r2_hidden(X7,X5)
        | ~ v13_waybel_0(X5,sK0) )
    | ~ spl17_10 ),
    inference(resolution,[],[f208,f108])).

fof(f108,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_hidden(X2,X1)
      | ~ r1_orders_2(X0,X2,X3)
      | r2_hidden(X3,X1)
      | ~ v13_waybel_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v13_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r1_orders_2(X0,X2,X3)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v13_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r1_orders_2(X0,X2,X3)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v13_waybel_0(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( ( r1_orders_2(X0,X2,X3)
                        & r2_hidden(X2,X1) )
                     => r2_hidden(X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t43_waybel_0.p',d20_waybel_0)).

fof(f388,plain,
    ( ! [X0,X1] :
        ( r1_orders_2(sK0,X0,k2_yellow_0(sK0,X1))
        | ~ r1_lattice3(sK0,X1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v1_finset_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X1) )
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8
    | ~ spl17_10
    | ~ spl17_25 ),
    inference(resolution,[],[f280,f350])).

fof(f280,plain,
    ( ! [X0,X1] :
        ( ~ r2_yellow_0(sK0,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,X0,X1)
        | r1_orders_2(sK0,X1,k2_yellow_0(sK0,X0)) )
    | ~ spl17_6
    | ~ spl17_10 ),
    inference(subsumption_resolution,[],[f279,f194])).

fof(f279,plain,
    ( ! [X0,X1] :
        ( ~ v5_orders_2(sK0)
        | ~ r2_yellow_0(sK0,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,X0,X1)
        | r1_orders_2(sK0,X1,k2_yellow_0(sK0,X0)) )
    | ~ spl17_10 ),
    inference(subsumption_resolution,[],[f277,f208])).

fof(f277,plain,
    ( ! [X0,X1] :
        ( ~ l1_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ r2_yellow_0(sK0,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,X0,X1)
        | r1_orders_2(sK0,X1,k2_yellow_0(sK0,X0)) )
    | ~ spl17_10 ),
    inference(resolution,[],[f231,f167])).

fof(f167,plain,(
    ! [X4,X2,X0] :
      ( ~ m1_subset_1(k2_yellow_0(X0,X2),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ r2_yellow_0(X0,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_lattice3(X0,X2,X4)
      | r1_orders_2(X0,X4,k2_yellow_0(X0,X2)) ) ),
    inference(equality_resolution,[],[f130])).

fof(f130,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | k2_yellow_0(X0,X2) != X1
      | ~ r2_yellow_0(X0,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_lattice3(X0,X2,X4)
      | r1_orders_2(X0,X4,X1) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f551,plain,
    ( spl17_1
    | ~ spl17_4
    | ~ spl17_10
    | ~ spl17_14
    | ~ spl17_20
    | spl17_25
    | spl17_59 ),
    inference(avatar_contradiction_clause,[],[f550])).

fof(f550,plain,
    ( $false
    | ~ spl17_1
    | ~ spl17_4
    | ~ spl17_10
    | ~ spl17_14
    | ~ spl17_20
    | ~ spl17_25
    | ~ spl17_59 ),
    inference(subsumption_resolution,[],[f526,f513])).

fof(f526,plain,
    ( sP7(sK1,sK0)
    | ~ spl17_1
    | ~ spl17_4
    | ~ spl17_10
    | ~ spl17_14
    | ~ spl17_20
    | ~ spl17_25 ),
    inference(subsumption_resolution,[],[f525,f275])).

fof(f525,plain,
    ( sP7(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl17_1
    | ~ spl17_4
    | ~ spl17_10
    | ~ spl17_14
    | ~ spl17_25 ),
    inference(subsumption_resolution,[],[f524,f173])).

fof(f524,plain,
    ( sP7(sK1,sK0)
    | v1_xboole_0(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl17_4
    | ~ spl17_10
    | ~ spl17_14
    | ~ spl17_25 ),
    inference(resolution,[],[f251,f340])).

fof(f251,plain,
    ( v2_waybel_0(sK1,sK0)
    | ~ spl17_14 ),
    inference(avatar_component_clause,[],[f250])).

fof(f250,plain,
    ( spl17_14
  <=> v2_waybel_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_14])])).

fof(f540,plain,
    ( ~ spl17_54
    | spl17_57 ),
    inference(avatar_contradiction_clause,[],[f539])).

fof(f539,plain,
    ( $false
    | ~ spl17_54
    | ~ spl17_57 ),
    inference(subsumption_resolution,[],[f500,f486])).

fof(f500,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK1))
    | ~ spl17_57 ),
    inference(resolution,[],[f496,f151])).

fof(f496,plain,
    ( ~ r1_tarski(sK2,sK1)
    | ~ spl17_57 ),
    inference(avatar_component_clause,[],[f495])).

fof(f495,plain,
    ( spl17_57
  <=> ~ r1_tarski(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_57])])).

fof(f538,plain,
    ( ~ spl17_63
    | ~ spl17_14 ),
    inference(avatar_split_clause,[],[f530,f250,f536])).

fof(f530,plain,
    ( ~ r2_hidden(k2_yellow_0(sK0,sK2),sK1)
    | ~ spl17_14 ),
    inference(subsumption_resolution,[],[f86,f251])).

fof(f86,plain,
    ( ~ r2_hidden(k2_yellow_0(sK0,sK2),sK1)
    | ~ v2_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_waybel_0(X1,X0)
          <~> ! [X2] :
                ( r2_hidden(k2_yellow_0(X0,X2),X1)
                | k1_xboole_0 = X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
                | ~ v1_finset_1(X2) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_waybel_0(X1,X0)
          <~> ! [X2] :
                ( r2_hidden(k2_yellow_0(X0,X2),X1)
                | k1_xboole_0 = X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
                | ~ v1_finset_1(X2) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v2_lattice3(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v13_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) )
           => ( v2_waybel_0(X1,X0)
            <=> ! [X2] :
                  ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
                    & v1_finset_1(X2) )
                 => ( k1_xboole_0 != X2
                   => r2_hidden(k2_yellow_0(X0,X2),X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v13_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
         => ( v2_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
                  & v1_finset_1(X2) )
               => ( k1_xboole_0 != X2
                 => r2_hidden(k2_yellow_0(X0,X2),X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t43_waybel_0.p',t43_waybel_0)).

fof(f487,plain,
    ( spl17_54
    | ~ spl17_14 ),
    inference(avatar_split_clause,[],[f480,f250,f485])).

fof(f480,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK1))
    | ~ spl17_14 ),
    inference(subsumption_resolution,[],[f84,f251])).

fof(f84,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK1))
    | ~ v2_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f479,plain,
    ( ~ spl17_53
    | ~ spl17_14 ),
    inference(avatar_split_clause,[],[f472,f250,f477])).

fof(f472,plain,
    ( k1_xboole_0 != sK2
    | ~ spl17_14 ),
    inference(subsumption_resolution,[],[f85,f251])).

fof(f85,plain,
    ( k1_xboole_0 != sK2
    | ~ v2_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f468,plain,
    ( spl17_48
    | spl17_50
    | ~ spl17_4
    | ~ spl17_10
    | spl17_15
    | ~ spl17_20
    | spl17_25 ),
    inference(avatar_split_clause,[],[f386,f291,f274,f253,f207,f186,f466,f460])).

fof(f386,plain,
    ( r2_hidden(k2_yellow_0(sK0,sK8(sK0,sK1)),sK1)
    | k1_xboole_0 = sK8(sK0,sK1)
    | ~ spl17_4
    | ~ spl17_10
    | ~ spl17_15
    | ~ spl17_20
    | ~ spl17_25 ),
    inference(subsumption_resolution,[],[f385,f254])).

fof(f385,plain,
    ( r2_hidden(k2_yellow_0(sK0,sK8(sK0,sK1)),sK1)
    | k1_xboole_0 = sK8(sK0,sK1)
    | v2_waybel_0(sK1,sK0)
    | ~ spl17_4
    | ~ spl17_10
    | ~ spl17_15
    | ~ spl17_20
    | ~ spl17_25 ),
    inference(subsumption_resolution,[],[f383,f275])).

fof(f383,plain,
    ( r2_hidden(k2_yellow_0(sK0,sK8(sK0,sK1)),sK1)
    | k1_xboole_0 = sK8(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_waybel_0(sK1,sK0)
    | ~ spl17_4
    | ~ spl17_10
    | ~ spl17_15
    | ~ spl17_25 ),
    inference(resolution,[],[f361,f335])).

fof(f361,plain,
    ( ! [X0] :
        ( sP7(sK1,X0)
        | r2_hidden(k2_yellow_0(sK0,sK8(X0,sK1)),sK1)
        | k1_xboole_0 = sK8(X0,sK1) )
    | ~ spl17_15 ),
    inference(duplicate_literal_removal,[],[f359])).

fof(f359,plain,
    ( ! [X0] :
        ( k1_xboole_0 = sK8(X0,sK1)
        | r2_hidden(k2_yellow_0(sK0,sK8(X0,sK1)),sK1)
        | sP7(sK1,X0)
        | sP7(sK1,X0) )
    | ~ spl17_15 ),
    inference(resolution,[],[f286,f126])).

fof(f286,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(sK8(X2,X3),k1_zfmisc_1(sK1))
        | k1_xboole_0 = sK8(X2,X3)
        | r2_hidden(k2_yellow_0(sK0,sK8(X2,X3)),sK1)
        | sP7(X3,X2) )
    | ~ spl17_15 ),
    inference(resolution,[],[f283,f125])).

fof(f283,plain,
    ( ! [X2] :
        ( ~ v1_finset_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(sK1))
        | k1_xboole_0 = X2
        | r2_hidden(k2_yellow_0(sK0,X2),sK1) )
    | ~ spl17_15 ),
    inference(subsumption_resolution,[],[f87,f254])).

fof(f87,plain,(
    ! [X2] :
      ( ~ v1_finset_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(sK1))
      | k1_xboole_0 = X2
      | r2_hidden(k2_yellow_0(sK0,X2),sK1)
      | v2_waybel_0(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f427,plain,
    ( ~ spl17_10
    | spl17_43 ),
    inference(avatar_contradiction_clause,[],[f426])).

fof(f426,plain,
    ( $false
    | ~ spl17_10
    | ~ spl17_43 ),
    inference(subsumption_resolution,[],[f425,f208])).

fof(f425,plain,
    ( ~ l1_orders_2(sK0)
    | ~ spl17_43 ),
    inference(resolution,[],[f423,f98])).

fof(f98,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t43_waybel_0.p',dt_l1_orders_2)).

fof(f423,plain,
    ( ~ l1_struct_0(sK0)
    | ~ spl17_43 ),
    inference(avatar_component_clause,[],[f422])).

fof(f422,plain,
    ( spl17_43
  <=> ~ l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_43])])).

fof(f424,plain,
    ( ~ spl17_43
    | spl17_25
    | ~ spl17_38 ),
    inference(avatar_split_clause,[],[f416,f407,f291,f422])).

fof(f407,plain,
    ( spl17_38
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_38])])).

fof(f416,plain,
    ( ~ l1_struct_0(sK0)
    | ~ spl17_25
    | ~ spl17_38 ),
    inference(subsumption_resolution,[],[f413,f292])).

fof(f413,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl17_38 ),
    inference(resolution,[],[f408,f115])).

fof(f115,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t43_waybel_0.p',fc2_struct_0)).

fof(f408,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl17_38 ),
    inference(avatar_component_clause,[],[f407])).

fof(f412,plain,
    ( spl17_38
    | spl17_40
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8
    | ~ spl17_10 ),
    inference(avatar_split_clause,[],[f358,f207,f200,f193,f186,f179,f410,f407])).

fof(f358,plain,
    ( ! [X0] :
        ( ~ v13_waybel_0(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X0)
        | m1_subset_1(o_2_8_waybel_0(sK0,X0),X0)
        | v1_xboole_0(u1_struct_0(sK0)) )
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8
    | ~ spl17_10 ),
    inference(duplicate_literal_removal,[],[f355])).

fof(f355,plain,
    ( ! [X0] :
        ( ~ v13_waybel_0(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X0)
        | v1_xboole_0(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | m1_subset_1(o_2_8_waybel_0(sK0,X0),X0)
        | v1_xboole_0(u1_struct_0(sK0)) )
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8
    | ~ spl17_10 ),
    inference(resolution,[],[f248,f147])).

fof(f147,plain,(
    ! [X2,X0,X1] :
      ( ~ m2_subset_1(X2,X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | m1_subset_1(X2,X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m2_subset_1(X2,X0,X1)
        <=> m1_subset_1(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m2_subset_1(X2,X0,X1)
        <=> m1_subset_1(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X0))
        & ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ! [X2] :
          ( m2_subset_1(X2,X0,X1)
        <=> m1_subset_1(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t43_waybel_0.p',redefinition_m2_subset_1)).

fof(f334,plain,
    ( ~ spl17_8
    | ~ spl17_10
    | ~ spl17_24 ),
    inference(avatar_contradiction_clause,[],[f333])).

fof(f333,plain,
    ( $false
    | ~ spl17_8
    | ~ spl17_10
    | ~ spl17_24 ),
    inference(subsumption_resolution,[],[f332,f208])).

fof(f332,plain,
    ( ~ l1_orders_2(sK0)
    | ~ spl17_8
    | ~ spl17_24 ),
    inference(subsumption_resolution,[],[f331,f201])).

fof(f331,plain,
    ( ~ v2_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | ~ spl17_24 ),
    inference(resolution,[],[f295,f99])).

fof(f99,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v2_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t43_waybel_0.p',cc2_lattice3)).

fof(f295,plain,
    ( v2_struct_0(sK0)
    | ~ spl17_24 ),
    inference(avatar_component_clause,[],[f294])).

fof(f294,plain,
    ( spl17_24
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_24])])).

fof(f276,plain,(
    spl17_20 ),
    inference(avatar_split_clause,[],[f90,f274])).

fof(f90,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f43])).

fof(f261,plain,
    ( ~ spl17_15
    | spl17_16 ),
    inference(avatar_split_clause,[],[f83,f259,f253])).

fof(f83,plain,
    ( v1_finset_1(sK2)
    | ~ v2_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f216,plain,(
    spl17_12 ),
    inference(avatar_split_clause,[],[f89,f214])).

fof(f89,plain,(
    v13_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f209,plain,(
    spl17_10 ),
    inference(avatar_split_clause,[],[f95,f207])).

fof(f95,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f202,plain,(
    spl17_8 ),
    inference(avatar_split_clause,[],[f94,f200])).

fof(f94,plain,(
    v2_lattice3(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f195,plain,(
    spl17_6 ),
    inference(avatar_split_clause,[],[f93,f193])).

fof(f93,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f188,plain,(
    spl17_4 ),
    inference(avatar_split_clause,[],[f92,f186])).

fof(f92,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f181,plain,(
    spl17_2 ),
    inference(avatar_split_clause,[],[f91,f179])).

fof(f91,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f174,plain,(
    ~ spl17_1 ),
    inference(avatar_split_clause,[],[f88,f172])).

fof(f88,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f43])).
%------------------------------------------------------------------------------
