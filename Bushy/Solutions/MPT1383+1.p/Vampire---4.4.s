%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : connsp_2__t8_connsp_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:35:54 EDT 2019

% Result     : Theorem 0.20s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :  517 (1544 expanded)
%              Number of leaves         :  146 ( 705 expanded)
%              Depth                    :   12
%              Number of atoms          : 1707 (5844 expanded)
%              Number of equality atoms :    7 (  15 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1383,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f134,f141,f148,f155,f162,f169,f182,f189,f196,f207,f214,f222,f236,f246,f255,f264,f273,f287,f297,f304,f312,f322,f332,f351,f358,f368,f375,f384,f399,f422,f429,f433,f435,f437,f453,f462,f475,f492,f534,f568,f590,f597,f608,f617,f620,f638,f649,f668,f680,f685,f687,f710,f717,f739,f758,f769,f785,f794,f801,f808,f815,f828,f835,f842,f876,f883,f893,f900,f924,f937,f981,f989,f996,f1005,f1012,f1023,f1037,f1046,f1053,f1062,f1071,f1079,f1086,f1095,f1102,f1109,f1116,f1123,f1134,f1143,f1154,f1169,f1176,f1183,f1190,f1197,f1204,f1230,f1237,f1258,f1265,f1274,f1285,f1292,f1300,f1307,f1314,f1321,f1335,f1350,f1380,f1382])).

fof(f1382,plain,
    ( spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_8
    | ~ spl10_10
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_18
    | ~ spl10_26 ),
    inference(avatar_contradiction_clause,[],[f1381])).

fof(f1381,plain,
    ( $false
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_18
    | ~ spl10_26 ),
    inference(subsumption_resolution,[],[f1365,f1371])).

fof(f1371,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_18
    | ~ spl10_26 ),
    inference(unit_resulting_resolution,[],[f140,f147,f195,f188,f181,f168,f235,f112])).

fof(f112,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ r2_hidden(X1,X3)
      | ~ r1_tarski(X3,X2)
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | r2_hidden(X1,k1_tops_1(X0,X2)) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f79,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_hidden(X1,k1_tops_1(X0,X2))
              | ! [X3] :
                  ( ~ r2_hidden(X1,X3)
                  | ~ r1_tarski(X3,X2)
                  | ~ v3_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ( r2_hidden(X1,sK6(X0,X1,X2))
                & r1_tarski(sK6(X0,X1,X2),X2)
                & v3_pre_topc(sK6(X0,X1,X2),X0)
                & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ r2_hidden(X1,k1_tops_1(X0,X2)) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f77,f78])).

fof(f78,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X1,X4)
          & r1_tarski(X4,X2)
          & v3_pre_topc(X4,X0)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( r2_hidden(X1,sK6(X0,X1,X2))
        & r1_tarski(sK6(X0,X1,X2),X2)
        & v3_pre_topc(sK6(X0,X1,X2),X0)
        & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f77,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_hidden(X1,k1_tops_1(X0,X2))
              | ! [X3] :
                  ( ~ r2_hidden(X1,X3)
                  | ~ r1_tarski(X3,X2)
                  | ~ v3_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ? [X4] :
                  ( r2_hidden(X1,X4)
                  & r1_tarski(X4,X2)
                  & v3_pre_topc(X4,X0)
                  & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ r2_hidden(X1,k1_tops_1(X0,X2)) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(rectify,[],[f76])).

fof(f76,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_hidden(X1,k1_tops_1(X0,X2))
              | ! [X3] :
                  ( ~ r2_hidden(X1,X3)
                  | ~ r1_tarski(X3,X2)
                  | ~ v3_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ? [X3] :
                  ( r2_hidden(X1,X3)
                  & r1_tarski(X3,X2)
                  & v3_pre_topc(X3,X0)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ r2_hidden(X1,k1_tops_1(X0,X2)) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_hidden(X1,k1_tops_1(X0,X2))
          <=> ? [X3] :
                ( r2_hidden(X1,X3)
                & r1_tarski(X3,X2)
                & v3_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_hidden(X1,k1_tops_1(X0,X2))
          <=> ? [X3] :
                ( r2_hidden(X1,X3)
                & r1_tarski(X3,X2)
                & v3_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1,X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
         => ( r2_hidden(X1,k1_tops_1(X0,X2))
          <=> ? [X3] :
                ( r2_hidden(X1,X3)
                & r1_tarski(X3,X2)
                & v3_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t8_connsp_2.p',t54_tops_1)).

fof(f235,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl10_26 ),
    inference(avatar_component_clause,[],[f234])).

fof(f234,plain,
    ( spl10_26
  <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_26])])).

fof(f168,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl10_10 ),
    inference(avatar_component_clause,[],[f167])).

fof(f167,plain,
    ( spl10_10
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).

fof(f181,plain,
    ( v3_pre_topc(sK3,sK0)
    | ~ spl10_14 ),
    inference(avatar_component_clause,[],[f180])).

fof(f180,plain,
    ( spl10_14
  <=> v3_pre_topc(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_14])])).

fof(f188,plain,
    ( r1_tarski(sK3,sK2)
    | ~ spl10_16 ),
    inference(avatar_component_clause,[],[f187])).

fof(f187,plain,
    ( spl10_16
  <=> r1_tarski(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_16])])).

fof(f195,plain,
    ( r2_hidden(sK1,sK3)
    | ~ spl10_18 ),
    inference(avatar_component_clause,[],[f194])).

fof(f194,plain,
    ( spl10_18
  <=> r2_hidden(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_18])])).

fof(f147,plain,
    ( l1_pre_topc(sK0)
    | ~ spl10_4 ),
    inference(avatar_component_clause,[],[f146])).

fof(f146,plain,
    ( spl10_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f140,plain,
    ( v2_pre_topc(sK0)
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f139])).

fof(f139,plain,
    ( spl10_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f1365,plain,
    ( ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13 ),
    inference(unit_resulting_resolution,[],[f133,f140,f147,f161,f168,f172,f99])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | m1_connsp_2(X2,X0,X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_connsp_2(X2,X0,X1)
                  | ~ r2_hidden(X1,k1_tops_1(X0,X2)) )
                & ( r2_hidden(X1,k1_tops_1(X0,X2))
                  | ~ m1_connsp_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) )
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
             => ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t8_connsp_2.p',d1_connsp_2)).

fof(f172,plain,
    ( ~ m1_connsp_2(sK2,sK0,sK1)
    | ~ spl10_13 ),
    inference(avatar_component_clause,[],[f171])).

fof(f171,plain,
    ( spl10_13
  <=> ~ m1_connsp_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_13])])).

fof(f161,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl10_8 ),
    inference(avatar_component_clause,[],[f160])).

fof(f160,plain,
    ( spl10_8
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).

fof(f133,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f132])).

fof(f132,plain,
    ( spl10_1
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f1380,plain,
    ( ~ spl10_2
    | ~ spl10_4
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_18
    | ~ spl10_26
    | spl10_125 ),
    inference(avatar_contradiction_clause,[],[f1379])).

fof(f1379,plain,
    ( $false
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_18
    | ~ spl10_26
    | ~ spl10_125 ),
    inference(subsumption_resolution,[],[f1371,f889])).

fof(f889,plain,
    ( ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ spl10_125 ),
    inference(avatar_component_clause,[],[f888])).

fof(f888,plain,
    ( spl10_125
  <=> ~ r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_125])])).

fof(f1350,plain,
    ( ~ spl10_2
    | ~ spl10_4
    | ~ spl10_10
    | ~ spl10_64
    | ~ spl10_124
    | ~ spl10_202
    | ~ spl10_204
    | ~ spl10_206 ),
    inference(avatar_contradiction_clause,[],[f1349])).

fof(f1349,plain,
    ( $false
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_10
    | ~ spl10_64
    | ~ spl10_124
    | ~ spl10_202
    | ~ spl10_204
    | ~ spl10_206 ),
    inference(subsumption_resolution,[],[f1348,f1306])).

fof(f1306,plain,
    ( r1_tarski(sK6(sK0,sK1,sK2),sK2)
    | ~ spl10_204 ),
    inference(avatar_component_clause,[],[f1305])).

fof(f1305,plain,
    ( spl10_204
  <=> r1_tarski(sK6(sK0,sK1,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_204])])).

fof(f1348,plain,
    ( ~ r1_tarski(sK6(sK0,sK1,sK2),sK2)
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_10
    | ~ spl10_64
    | ~ spl10_124
    | ~ spl10_202
    | ~ spl10_206 ),
    inference(subsumption_resolution,[],[f1347,f1313])).

fof(f1313,plain,
    ( v3_pre_topc(sK6(sK0,sK1,sK2),sK0)
    | ~ spl10_206 ),
    inference(avatar_component_clause,[],[f1312])).

fof(f1312,plain,
    ( spl10_206
  <=> v3_pre_topc(sK6(sK0,sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_206])])).

fof(f1347,plain,
    ( ~ v3_pre_topc(sK6(sK0,sK1,sK2),sK0)
    | ~ r1_tarski(sK6(sK0,sK1,sK2),sK2)
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_10
    | ~ spl10_64
    | ~ spl10_124
    | ~ spl10_202 ),
    inference(subsumption_resolution,[],[f1342,f902])).

fof(f902,plain,
    ( m1_subset_1(sK6(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_10
    | ~ spl10_124 ),
    inference(unit_resulting_resolution,[],[f140,f147,f168,f892,f108])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f892,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ spl10_124 ),
    inference(avatar_component_clause,[],[f891])).

fof(f891,plain,
    ( spl10_124
  <=> r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_124])])).

fof(f1342,plain,
    ( ~ m1_subset_1(sK6(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_pre_topc(sK6(sK0,sK1,sK2),sK0)
    | ~ r1_tarski(sK6(sK0,sK1,sK2),sK2)
    | ~ spl10_64
    | ~ spl10_202 ),
    inference(resolution,[],[f1299,f432])).

fof(f432,plain,
    ( ! [X3] :
        ( ~ r2_hidden(sK1,X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X3,sK0)
        | ~ r1_tarski(X3,sK2) )
    | ~ spl10_64 ),
    inference(avatar_component_clause,[],[f431])).

fof(f431,plain,
    ( spl10_64
  <=> ! [X3] :
        ( ~ r2_hidden(sK1,X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X3,sK0)
        | ~ r1_tarski(X3,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_64])])).

fof(f1299,plain,
    ( r2_hidden(sK1,sK6(sK0,sK1,sK2))
    | ~ spl10_202 ),
    inference(avatar_component_clause,[],[f1298])).

fof(f1298,plain,
    ( spl10_202
  <=> r2_hidden(sK1,sK6(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_202])])).

fof(f1335,plain,
    ( ~ spl10_211
    | ~ spl10_74
    | ~ spl10_124 ),
    inference(avatar_split_clause,[],[f907,f891,f532,f1333])).

fof(f1333,plain,
    ( spl10_211
  <=> ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_211])])).

fof(f532,plain,
    ( spl10_74
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_74])])).

fof(f907,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(k1_xboole_0))
    | ~ spl10_74
    | ~ spl10_124 ),
    inference(unit_resulting_resolution,[],[f533,f892,f126])).

fof(f126,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t8_connsp_2.p',t5_subset)).

fof(f533,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl10_74 ),
    inference(avatar_component_clause,[],[f532])).

fof(f1321,plain,
    ( ~ spl10_209
    | spl10_69
    | ~ spl10_124 ),
    inference(avatar_split_clause,[],[f906,f891,f457,f1319])).

fof(f1319,plain,
    ( spl10_209
  <=> ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_209])])).

fof(f457,plain,
    ( spl10_69
  <=> ~ m1_subset_1(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_69])])).

fof(f906,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(sK3))
    | ~ spl10_69
    | ~ spl10_124 ),
    inference(unit_resulting_resolution,[],[f458,f892,f125])).

fof(f125,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t8_connsp_2.p',t4_subset)).

fof(f458,plain,
    ( ~ m1_subset_1(sK1,sK3)
    | ~ spl10_69 ),
    inference(avatar_component_clause,[],[f457])).

fof(f1314,plain,
    ( spl10_206
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_10
    | ~ spl10_124 ),
    inference(avatar_split_clause,[],[f905,f891,f167,f146,f139,f1312])).

fof(f905,plain,
    ( v3_pre_topc(sK6(sK0,sK1,sK2),sK0)
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_10
    | ~ spl10_124 ),
    inference(unit_resulting_resolution,[],[f140,f147,f168,f892,f109])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(sK6(X0,X1,X2),X0)
      | ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f1307,plain,
    ( spl10_204
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_10
    | ~ spl10_124 ),
    inference(avatar_split_clause,[],[f904,f891,f167,f146,f139,f1305])).

fof(f904,plain,
    ( r1_tarski(sK6(sK0,sK1,sK2),sK2)
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_10
    | ~ spl10_124 ),
    inference(unit_resulting_resolution,[],[f140,f147,f168,f892,f110])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(sK6(X0,X1,X2),X2)
      | ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f1300,plain,
    ( spl10_202
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_10
    | ~ spl10_124 ),
    inference(avatar_split_clause,[],[f903,f891,f167,f146,f139,f1298])).

fof(f903,plain,
    ( r2_hidden(sK1,sK6(sK0,sK1,sK2))
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_10
    | ~ spl10_124 ),
    inference(unit_resulting_resolution,[],[f140,f147,f168,f892,f111])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | r2_hidden(X1,sK6(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f1292,plain,
    ( spl10_200
    | spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_12 ),
    inference(avatar_split_clause,[],[f998,f174,f167,f160,f146,f139,f132,f1290])).

fof(f1290,plain,
    ( spl10_200
  <=> m1_connsp_2(sK4(sK0,sK1,sK2),sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_200])])).

fof(f174,plain,
    ( spl10_12
  <=> m1_connsp_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).

fof(f998,plain,
    ( m1_connsp_2(sK4(sK0,sK1,sK2),sK0,sK1)
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_12 ),
    inference(unit_resulting_resolution,[],[f133,f140,f147,f161,f175,f168,f102])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(sK4(X0,X1,X2),X0,X1)
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(sK4(X0,X1,X2),X2)
                & v3_pre_topc(sK4(X0,X1,X2),X0)
                & m1_connsp_2(sK4(X0,X1,X2),X0,X1)
                & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
                & ~ v1_xboole_0(sK4(X0,X1,X2)) )
              | ~ m1_connsp_2(X2,X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f39,f72])).

fof(f72,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( r1_tarski(X3,X2)
          & v3_pre_topc(X3,X0)
          & m1_connsp_2(X3,X0,X1)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X3) )
     => ( r1_tarski(sK4(X0,X1,X2),X2)
        & v3_pre_topc(sK4(X0,X1,X2),X0)
        & m1_connsp_2(sK4(X0,X1,X2),X0,X1)
        & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(sK4(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( r1_tarski(X3,X2)
                  & v3_pre_topc(X3,X0)
                  & m1_connsp_2(X3,X0,X1)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                  & ~ v1_xboole_0(X3) )
              | ~ m1_connsp_2(X2,X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( r1_tarski(X3,X2)
                  & v3_pre_topc(X3,X0)
                  & m1_connsp_2(X3,X0,X1)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                  & ~ v1_xboole_0(X3) )
              | ~ m1_connsp_2(X2,X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ~ ( ! [X3] :
                      ( ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                        & ~ v1_xboole_0(X3) )
                     => ~ ( r1_tarski(X3,X2)
                          & v3_pre_topc(X3,X0)
                          & m1_connsp_2(X3,X0,X1) ) )
                  & m1_connsp_2(X2,X0,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t8_connsp_2.p',t7_connsp_2)).

fof(f175,plain,
    ( m1_connsp_2(sK2,sK0,sK1)
    | ~ spl10_12 ),
    inference(avatar_component_clause,[],[f174])).

fof(f1285,plain,
    ( ~ spl10_199
    | spl10_197 ),
    inference(avatar_split_clause,[],[f1277,f1272,f1283])).

fof(f1283,plain,
    ( spl10_199
  <=> ~ r2_hidden(sK2,k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_199])])).

fof(f1272,plain,
    ( spl10_197
  <=> ~ m1_subset_1(sK2,k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_197])])).

fof(f1277,plain,
    ( ~ r2_hidden(sK2,k1_zfmisc_1(sK2))
    | ~ spl10_197 ),
    inference(unit_resulting_resolution,[],[f1273,f115])).

fof(f115,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t8_connsp_2.p',t1_subset)).

fof(f1273,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK2))
    | ~ spl10_197 ),
    inference(avatar_component_clause,[],[f1272])).

fof(f1274,plain,
    ( ~ spl10_197
    | spl10_191 ),
    inference(avatar_split_clause,[],[f1266,f1250,f1272])).

fof(f1250,plain,
    ( spl10_191
  <=> ~ r1_tarski(sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_191])])).

fof(f1266,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK2))
    | ~ spl10_191 ),
    inference(unit_resulting_resolution,[],[f1251,f121])).

fof(f121,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t8_connsp_2.p',t3_subset)).

fof(f1251,plain,
    ( ~ r1_tarski(sK2,sK2)
    | ~ spl10_191 ),
    inference(avatar_component_clause,[],[f1250])).

fof(f1265,plain,
    ( spl10_194
    | ~ spl10_4
    | ~ spl10_10 ),
    inference(avatar_split_clause,[],[f333,f167,f146,f1263])).

fof(f1263,plain,
    ( spl10_194
  <=> m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_194])])).

fof(f333,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl10_4
    | ~ spl10_10 ),
    inference(unit_resulting_resolution,[],[f147,f168,f119])).

fof(f119,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t8_connsp_2.p',dt_k1_tops_1)).

fof(f1258,plain,
    ( ~ spl10_191
    | ~ spl10_193
    | ~ spl10_10
    | ~ spl10_64
    | ~ spl10_88 ),
    inference(avatar_split_clause,[],[f778,f647,f431,f167,f1256,f1250])).

fof(f1256,plain,
    ( spl10_193
  <=> ~ v3_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_193])])).

fof(f647,plain,
    ( spl10_88
  <=> r2_hidden(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_88])])).

fof(f778,plain,
    ( ~ v3_pre_topc(sK2,sK0)
    | ~ r1_tarski(sK2,sK2)
    | ~ spl10_10
    | ~ spl10_64
    | ~ spl10_88 ),
    inference(subsumption_resolution,[],[f777,f168])).

fof(f777,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_pre_topc(sK2,sK0)
    | ~ r1_tarski(sK2,sK2)
    | ~ spl10_64
    | ~ spl10_88 ),
    inference(resolution,[],[f432,f648])).

fof(f648,plain,
    ( r2_hidden(sK1,sK2)
    | ~ spl10_88 ),
    inference(avatar_component_clause,[],[f647])).

fof(f1237,plain,
    ( ~ spl10_189
    | ~ spl10_184 ),
    inference(avatar_split_clause,[],[f1216,f1202,f1235])).

fof(f1235,plain,
    ( spl10_189
  <=> ~ r2_hidden(u1_struct_0(sK0),sK7(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_189])])).

fof(f1202,plain,
    ( spl10_184
  <=> r2_hidden(sK7(sK3),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_184])])).

fof(f1216,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK7(sK3))
    | ~ spl10_184 ),
    inference(unit_resulting_resolution,[],[f1203,f114])).

fof(f114,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t8_connsp_2.p',antisymmetry_r2_hidden)).

fof(f1203,plain,
    ( r2_hidden(sK7(sK3),u1_struct_0(sK0))
    | ~ spl10_184 ),
    inference(avatar_component_clause,[],[f1202])).

fof(f1230,plain,
    ( ~ spl10_187
    | ~ spl10_180 ),
    inference(avatar_split_clause,[],[f1206,f1188,f1228])).

fof(f1228,plain,
    ( spl10_187
  <=> ~ r2_hidden(u1_struct_0(sK0),sK7(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_187])])).

fof(f1188,plain,
    ( spl10_180
  <=> r2_hidden(sK7(sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_180])])).

fof(f1206,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK7(sK2))
    | ~ spl10_180 ),
    inference(unit_resulting_resolution,[],[f1189,f114])).

fof(f1189,plain,
    ( r2_hidden(sK7(sK2),u1_struct_0(sK0))
    | ~ spl10_180 ),
    inference(avatar_component_clause,[],[f1188])).

fof(f1204,plain,
    ( spl10_184
    | spl10_45
    | ~ spl10_166 ),
    inference(avatar_split_clause,[],[f1162,f1121,f320,f1202])).

fof(f320,plain,
    ( spl10_45
  <=> ~ v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_45])])).

fof(f1121,plain,
    ( spl10_166
  <=> m1_subset_1(sK7(sK3),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_166])])).

fof(f1162,plain,
    ( r2_hidden(sK7(sK3),u1_struct_0(sK0))
    | ~ spl10_45
    | ~ spl10_166 ),
    inference(unit_resulting_resolution,[],[f321,f1122,f116])).

fof(f116,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t8_connsp_2.p',t2_subset)).

fof(f1122,plain,
    ( m1_subset_1(sK7(sK3),u1_struct_0(sK0))
    | ~ spl10_166 ),
    inference(avatar_component_clause,[],[f1121])).

fof(f321,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl10_45 ),
    inference(avatar_component_clause,[],[f320])).

fof(f1197,plain,
    ( ~ spl10_183
    | spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | spl10_27
    | ~ spl10_166 ),
    inference(avatar_split_clause,[],[f1160,f1121,f231,f146,f139,f132,f1195])).

fof(f1195,plain,
    ( spl10_183
  <=> ~ m1_connsp_2(sK3,sK0,sK7(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_183])])).

fof(f231,plain,
    ( spl10_27
  <=> ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_27])])).

fof(f1160,plain,
    ( ~ m1_connsp_2(sK3,sK0,sK7(sK3))
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_27
    | ~ spl10_166 ),
    inference(unit_resulting_resolution,[],[f133,f140,f147,f232,f1122,f117])).

fof(f117,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t8_connsp_2.p',dt_m1_connsp_2)).

fof(f232,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl10_27 ),
    inference(avatar_component_clause,[],[f231])).

fof(f1190,plain,
    ( spl10_180
    | spl10_45
    | ~ spl10_164 ),
    inference(avatar_split_clause,[],[f1159,f1114,f320,f1188])).

fof(f1114,plain,
    ( spl10_164
  <=> m1_subset_1(sK7(sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_164])])).

fof(f1159,plain,
    ( r2_hidden(sK7(sK2),u1_struct_0(sK0))
    | ~ spl10_45
    | ~ spl10_164 ),
    inference(unit_resulting_resolution,[],[f321,f1115,f116])).

fof(f1115,plain,
    ( m1_subset_1(sK7(sK2),u1_struct_0(sK0))
    | ~ spl10_164 ),
    inference(avatar_component_clause,[],[f1114])).

fof(f1183,plain,
    ( ~ spl10_179
    | spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | spl10_27
    | ~ spl10_164 ),
    inference(avatar_split_clause,[],[f1157,f1114,f231,f146,f139,f132,f1181])).

fof(f1181,plain,
    ( spl10_179
  <=> ~ m1_connsp_2(sK3,sK0,sK7(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_179])])).

fof(f1157,plain,
    ( ~ m1_connsp_2(sK3,sK0,sK7(sK2))
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_27
    | ~ spl10_164 ),
    inference(unit_resulting_resolution,[],[f133,f140,f147,f232,f1115,f117])).

fof(f1176,plain,
    ( ~ spl10_177
    | spl10_161 ),
    inference(avatar_split_clause,[],[f1146,f1100,f1174])).

fof(f1174,plain,
    ( spl10_177
  <=> ~ r2_hidden(u1_struct_0(sK0),k1_zfmisc_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_177])])).

fof(f1100,plain,
    ( spl10_161
  <=> ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_161])])).

fof(f1146,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),k1_zfmisc_1(sK3))
    | ~ spl10_161 ),
    inference(unit_resulting_resolution,[],[f1101,f115])).

fof(f1101,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(sK3))
    | ~ spl10_161 ),
    inference(avatar_component_clause,[],[f1100])).

fof(f1169,plain,
    ( ~ spl10_175
    | spl10_159 ),
    inference(avatar_split_clause,[],[f1126,f1093,f1167])).

fof(f1167,plain,
    ( spl10_175
  <=> ~ r2_hidden(u1_struct_0(sK0),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_175])])).

fof(f1093,plain,
    ( spl10_159
  <=> ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_159])])).

fof(f1126,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl10_159 ),
    inference(unit_resulting_resolution,[],[f1094,f115])).

fof(f1094,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl10_159 ),
    inference(avatar_component_clause,[],[f1093])).

fof(f1154,plain,
    ( ~ spl10_173
    | spl10_161 ),
    inference(avatar_split_clause,[],[f1144,f1100,f1152])).

fof(f1152,plain,
    ( spl10_173
  <=> ~ r1_tarski(u1_struct_0(sK0),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_173])])).

fof(f1144,plain,
    ( ~ r1_tarski(u1_struct_0(sK0),sK3)
    | ~ spl10_161 ),
    inference(unit_resulting_resolution,[],[f1101,f122])).

fof(f122,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f84])).

fof(f1143,plain,
    ( spl10_170
    | spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_12 ),
    inference(avatar_split_clause,[],[f982,f174,f167,f160,f146,f139,f132,f1141])).

fof(f1141,plain,
    ( spl10_170
  <=> r1_tarski(sK4(sK0,sK1,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_170])])).

fof(f982,plain,
    ( r1_tarski(sK4(sK0,sK1,sK2),sK2)
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_12 ),
    inference(unit_resulting_resolution,[],[f133,f140,f147,f161,f175,f168,f104])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(sK4(X0,X1,X2),X2)
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f1134,plain,
    ( ~ spl10_169
    | spl10_159 ),
    inference(avatar_split_clause,[],[f1124,f1093,f1132])).

fof(f1132,plain,
    ( spl10_169
  <=> ~ r1_tarski(u1_struct_0(sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_169])])).

fof(f1124,plain,
    ( ~ r1_tarski(u1_struct_0(sK0),k1_xboole_0)
    | ~ spl10_159 ),
    inference(unit_resulting_resolution,[],[f1094,f122])).

fof(f1123,plain,
    ( spl10_166
    | ~ spl10_10
    | ~ spl10_116 ),
    inference(avatar_split_clause,[],[f854,f833,f167,f1121])).

fof(f833,plain,
    ( spl10_116
  <=> r2_hidden(sK7(sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_116])])).

fof(f854,plain,
    ( m1_subset_1(sK7(sK3),u1_struct_0(sK0))
    | ~ spl10_10
    | ~ spl10_116 ),
    inference(unit_resulting_resolution,[],[f168,f834,f125])).

fof(f834,plain,
    ( r2_hidden(sK7(sK3),sK2)
    | ~ spl10_116 ),
    inference(avatar_component_clause,[],[f833])).

fof(f1116,plain,
    ( spl10_164
    | ~ spl10_10
    | ~ spl10_114 ),
    inference(avatar_split_clause,[],[f843,f826,f167,f1114])).

fof(f826,plain,
    ( spl10_114
  <=> r2_hidden(sK7(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_114])])).

fof(f843,plain,
    ( m1_subset_1(sK7(sK2),u1_struct_0(sK0))
    | ~ spl10_10
    | ~ spl10_114 ),
    inference(unit_resulting_resolution,[],[f168,f827,f125])).

fof(f827,plain,
    ( r2_hidden(sK7(sK2),sK2)
    | ~ spl10_114 ),
    inference(avatar_component_clause,[],[f826])).

fof(f1109,plain,
    ( spl10_162
    | spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_12 ),
    inference(avatar_split_clause,[],[f927,f174,f167,f160,f146,f139,f132,f1107])).

fof(f1107,plain,
    ( spl10_162
  <=> v3_pre_topc(sK4(sK0,sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_162])])).

fof(f927,plain,
    ( v3_pre_topc(sK4(sK0,sK1,sK2),sK0)
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_12 ),
    inference(unit_resulting_resolution,[],[f133,f140,f147,f161,f175,f168,f103])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(sK4(X0,X1,X2),X0)
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f1102,plain,
    ( ~ spl10_161
    | ~ spl10_46
    | spl10_69 ),
    inference(avatar_split_clause,[],[f689,f457,f330,f1100])).

fof(f330,plain,
    ( spl10_46
  <=> r2_hidden(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_46])])).

fof(f689,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(sK3))
    | ~ spl10_46
    | ~ spl10_69 ),
    inference(unit_resulting_resolution,[],[f331,f458,f125])).

fof(f331,plain,
    ( r2_hidden(sK1,u1_struct_0(sK0))
    | ~ spl10_46 ),
    inference(avatar_component_clause,[],[f330])).

fof(f1095,plain,
    ( ~ spl10_159
    | ~ spl10_46
    | ~ spl10_74 ),
    inference(avatar_split_clause,[],[f573,f532,f330,f1093])).

fof(f573,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl10_46
    | ~ spl10_74 ),
    inference(unit_resulting_resolution,[],[f331,f533,f126])).

fof(f1086,plain,
    ( ~ spl10_157
    | spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | spl10_27 ),
    inference(avatar_split_clause,[],[f742,f231,f146,f139,f132,f1084])).

fof(f1084,plain,
    ( spl10_157
  <=> ~ m1_connsp_2(sK3,sK0,sK7(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_157])])).

fof(f742,plain,
    ( ~ m1_connsp_2(sK3,sK0,sK7(u1_struct_0(sK0)))
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_27 ),
    inference(unit_resulting_resolution,[],[f133,f140,f147,f113,f232,f117])).

fof(f113,plain,(
    ! [X0] : m1_subset_1(sK7(X0),X0) ),
    inference(cnf_transformation,[],[f81])).

fof(f81,plain,(
    ! [X0] : m1_subset_1(sK7(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f16,f80])).

fof(f80,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK7(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f16,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t8_connsp_2.p',existence_m1_subset_1)).

fof(f1079,plain,
    ( spl10_154
    | ~ spl10_146 ),
    inference(avatar_split_clause,[],[f1064,f1044,f1077])).

fof(f1077,plain,
    ( spl10_154
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_154])])).

fof(f1044,plain,
    ( spl10_146
  <=> k1_xboole_0 = sK7(k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_146])])).

fof(f1064,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl10_146 ),
    inference(superposition,[],[f113,f1045])).

fof(f1045,plain,
    ( k1_xboole_0 = sK7(k1_zfmisc_1(k1_xboole_0))
    | ~ spl10_146 ),
    inference(avatar_component_clause,[],[f1044])).

fof(f1071,plain,
    ( spl10_152
    | ~ spl10_146 ),
    inference(avatar_split_clause,[],[f1063,f1044,f1069])).

fof(f1069,plain,
    ( spl10_152
  <=> r1_tarski(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_152])])).

fof(f1063,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl10_146 ),
    inference(superposition,[],[f198,f1045])).

fof(f198,plain,(
    ! [X0] : r1_tarski(sK7(k1_zfmisc_1(X0)),X0) ),
    inference(unit_resulting_resolution,[],[f113,f121])).

fof(f1062,plain,
    ( ~ spl10_151
    | spl10_141 ),
    inference(avatar_split_clause,[],[f1029,f1010,f1060])).

fof(f1060,plain,
    ( spl10_151
  <=> ~ r2_hidden(k1_zfmisc_1(sK2),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_151])])).

fof(f1010,plain,
    ( spl10_141
  <=> ~ m1_subset_1(k1_zfmisc_1(sK2),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_141])])).

fof(f1029,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK2),k1_zfmisc_1(k1_xboole_0))
    | ~ spl10_141 ),
    inference(unit_resulting_resolution,[],[f1011,f115])).

fof(f1011,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(sK2),k1_zfmisc_1(k1_xboole_0))
    | ~ spl10_141 ),
    inference(avatar_component_clause,[],[f1010])).

fof(f1053,plain,
    ( ~ spl10_149
    | spl10_139 ),
    inference(avatar_split_clause,[],[f1015,f1003,f1051])).

fof(f1051,plain,
    ( spl10_149
  <=> ~ r2_hidden(sK5(sK0),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_149])])).

fof(f1003,plain,
    ( spl10_139
  <=> ~ m1_subset_1(sK5(sK0),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_139])])).

fof(f1015,plain,
    ( ~ r2_hidden(sK5(sK0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl10_139 ),
    inference(unit_resulting_resolution,[],[f1004,f115])).

fof(f1004,plain,
    ( ~ m1_subset_1(sK5(sK0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl10_139 ),
    inference(avatar_component_clause,[],[f1003])).

fof(f1046,plain,
    ( spl10_146
    | ~ spl10_130 ),
    inference(avatar_split_clause,[],[f954,f935,f1044])).

fof(f935,plain,
    ( spl10_130
  <=> v1_xboole_0(sK7(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_130])])).

fof(f954,plain,
    ( k1_xboole_0 = sK7(k1_zfmisc_1(k1_xboole_0))
    | ~ spl10_130 ),
    inference(unit_resulting_resolution,[],[f936,f97])).

fof(f97,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t8_connsp_2.p',t6_boole)).

fof(f936,plain,
    ( v1_xboole_0(sK7(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl10_130 ),
    inference(avatar_component_clause,[],[f935])).

fof(f1037,plain,
    ( ~ spl10_145
    | spl10_141 ),
    inference(avatar_split_clause,[],[f1027,f1010,f1035])).

fof(f1035,plain,
    ( spl10_145
  <=> ~ r1_tarski(k1_zfmisc_1(sK2),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_145])])).

fof(f1027,plain,
    ( ~ r1_tarski(k1_zfmisc_1(sK2),k1_xboole_0)
    | ~ spl10_141 ),
    inference(unit_resulting_resolution,[],[f1011,f122])).

fof(f1023,plain,
    ( ~ spl10_143
    | spl10_139 ),
    inference(avatar_split_clause,[],[f1013,f1003,f1021])).

fof(f1021,plain,
    ( spl10_143
  <=> ~ r1_tarski(sK5(sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_143])])).

fof(f1013,plain,
    ( ~ r1_tarski(sK5(sK0),k1_xboole_0)
    | ~ spl10_139 ),
    inference(unit_resulting_resolution,[],[f1004,f122])).

fof(f1012,plain,
    ( ~ spl10_141
    | ~ spl10_24
    | ~ spl10_74 ),
    inference(avatar_split_clause,[],[f724,f532,f217,f1010])).

fof(f217,plain,
    ( spl10_24
  <=> r2_hidden(sK3,k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_24])])).

fof(f724,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(sK2),k1_zfmisc_1(k1_xboole_0))
    | ~ spl10_24
    | ~ spl10_74 ),
    inference(unit_resulting_resolution,[],[f533,f218,f126])).

fof(f218,plain,
    ( r2_hidden(sK3,k1_zfmisc_1(sK2))
    | ~ spl10_24 ),
    inference(avatar_component_clause,[],[f217])).

fof(f1005,plain,
    ( ~ spl10_139
    | ~ spl10_34
    | ~ spl10_74 ),
    inference(avatar_split_clause,[],[f569,f532,f271,f1003])).

fof(f271,plain,
    ( spl10_34
  <=> r2_hidden(sK7(sK5(sK0)),sK5(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_34])])).

fof(f569,plain,
    ( ~ m1_subset_1(sK5(sK0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl10_34
    | ~ spl10_74 ),
    inference(unit_resulting_resolution,[],[f272,f533,f126])).

fof(f272,plain,
    ( r2_hidden(sK7(sK5(sK0)),sK5(sK0))
    | ~ spl10_34 ),
    inference(avatar_component_clause,[],[f271])).

fof(f996,plain,
    ( ~ spl10_137
    | ~ spl10_124 ),
    inference(avatar_split_clause,[],[f910,f891,f994])).

fof(f994,plain,
    ( spl10_137
  <=> ~ r2_hidden(k1_tops_1(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_137])])).

fof(f910,plain,
    ( ~ r2_hidden(k1_tops_1(sK0,sK2),sK1)
    | ~ spl10_124 ),
    inference(unit_resulting_resolution,[],[f892,f114])).

fof(f989,plain,
    ( spl10_134
    | ~ spl10_124 ),
    inference(avatar_split_clause,[],[f908,f891,f987])).

fof(f987,plain,
    ( spl10_134
  <=> m1_subset_1(sK1,k1_tops_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_134])])).

fof(f908,plain,
    ( m1_subset_1(sK1,k1_tops_1(sK0,sK2))
    | ~ spl10_124 ),
    inference(unit_resulting_resolution,[],[f892,f115])).

fof(f981,plain,
    ( ~ spl10_133
    | spl10_69 ),
    inference(avatar_split_clause,[],[f690,f457,f979])).

fof(f979,plain,
    ( spl10_133
  <=> ~ r2_hidden(sK1,sK7(k1_zfmisc_1(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_133])])).

fof(f690,plain,
    ( ~ r2_hidden(sK1,sK7(k1_zfmisc_1(sK3)))
    | ~ spl10_69 ),
    inference(unit_resulting_resolution,[],[f113,f458,f125])).

fof(f937,plain,
    ( spl10_130
    | ~ spl10_74 ),
    inference(avatar_split_clause,[],[f930,f532,f935])).

fof(f930,plain,
    ( v1_xboole_0(sK7(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl10_74 ),
    inference(unit_resulting_resolution,[],[f113,f574,f116])).

fof(f574,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK7(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl10_74 ),
    inference(unit_resulting_resolution,[],[f113,f533,f126])).

fof(f924,plain,
    ( ~ spl10_129
    | ~ spl10_124 ),
    inference(avatar_split_clause,[],[f911,f891,f922])).

fof(f922,plain,
    ( spl10_129
  <=> ~ v1_xboole_0(k1_tops_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_129])])).

fof(f911,plain,
    ( ~ v1_xboole_0(k1_tops_1(sK0,sK2))
    | ~ spl10_124 ),
    inference(unit_resulting_resolution,[],[f892,f124])).

fof(f124,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t8_connsp_2.p',t7_boole)).

fof(f900,plain,
    ( ~ spl10_127
    | spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_12 ),
    inference(avatar_split_clause,[],[f884,f174,f167,f160,f146,f139,f132,f898])).

fof(f898,plain,
    ( spl10_127
  <=> ~ v1_xboole_0(sK4(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_127])])).

fof(f884,plain,
    ( ~ v1_xboole_0(sK4(sK0,sK1,sK2))
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_12 ),
    inference(unit_resulting_resolution,[],[f133,f140,f147,f161,f175,f168,f100])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(sK4(X0,X1,X2))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f893,plain,
    ( spl10_124
    | spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_12 ),
    inference(avatar_split_clause,[],[f818,f174,f167,f160,f146,f139,f132,f891])).

fof(f818,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_12 ),
    inference(unit_resulting_resolution,[],[f133,f140,f147,f175,f161,f168,f98])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | r2_hidden(X1,k1_tops_1(X0,X2))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f883,plain,
    ( ~ spl10_123
    | ~ spl10_116 ),
    inference(avatar_split_clause,[],[f859,f833,f881])).

fof(f881,plain,
    ( spl10_123
  <=> ~ r2_hidden(sK2,sK7(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_123])])).

fof(f859,plain,
    ( ~ r2_hidden(sK2,sK7(sK3))
    | ~ spl10_116 ),
    inference(unit_resulting_resolution,[],[f834,f114])).

fof(f876,plain,
    ( ~ spl10_121
    | ~ spl10_114 ),
    inference(avatar_split_clause,[],[f848,f826,f874])).

fof(f874,plain,
    ( spl10_121
  <=> ~ r2_hidden(sK2,sK7(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_121])])).

fof(f848,plain,
    ( ~ r2_hidden(sK2,sK7(sK2))
    | ~ spl10_114 ),
    inference(unit_resulting_resolution,[],[f827,f114])).

fof(f842,plain,
    ( ~ spl10_119
    | spl10_67
    | spl10_109 ),
    inference(avatar_split_clause,[],[f817,f799,f451,f840])).

fof(f840,plain,
    ( spl10_119
  <=> ~ m1_subset_1(k1_zfmisc_1(sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_119])])).

fof(f451,plain,
    ( spl10_67
  <=> ~ v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_67])])).

fof(f799,plain,
    ( spl10_109
  <=> ~ r2_hidden(k1_zfmisc_1(sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_109])])).

fof(f817,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(sK2),sK3)
    | ~ spl10_67
    | ~ spl10_109 ),
    inference(unit_resulting_resolution,[],[f452,f800,f116])).

fof(f800,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK2),sK3)
    | ~ spl10_109 ),
    inference(avatar_component_clause,[],[f799])).

fof(f452,plain,
    ( ~ v1_xboole_0(sK3)
    | ~ spl10_67 ),
    inference(avatar_component_clause,[],[f451])).

fof(f835,plain,
    ( spl10_116
    | spl10_93
    | ~ spl10_106 ),
    inference(avatar_split_clause,[],[f816,f792,f678,f833])).

fof(f678,plain,
    ( spl10_93
  <=> ~ v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_93])])).

fof(f792,plain,
    ( spl10_106
  <=> m1_subset_1(sK7(sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_106])])).

fof(f816,plain,
    ( r2_hidden(sK7(sK3),sK2)
    | ~ spl10_93
    | ~ spl10_106 ),
    inference(unit_resulting_resolution,[],[f679,f793,f116])).

fof(f793,plain,
    ( m1_subset_1(sK7(sK3),sK2)
    | ~ spl10_106 ),
    inference(avatar_component_clause,[],[f792])).

fof(f679,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ spl10_93 ),
    inference(avatar_component_clause,[],[f678])).

fof(f828,plain,
    ( spl10_114
    | spl10_93 ),
    inference(avatar_split_clause,[],[f681,f678,f826])).

fof(f681,plain,
    ( r2_hidden(sK7(sK2),sK2)
    | ~ spl10_93 ),
    inference(unit_resulting_resolution,[],[f113,f679,f116])).

fof(f815,plain,
    ( ~ spl10_113
    | spl10_101 ),
    inference(avatar_split_clause,[],[f774,f756,f813])).

fof(f813,plain,
    ( spl10_113
  <=> ~ r2_hidden(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_113])])).

fof(f756,plain,
    ( spl10_101
  <=> ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_101])])).

fof(f774,plain,
    ( ~ r2_hidden(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl10_101 ),
    inference(unit_resulting_resolution,[],[f757,f115])).

fof(f757,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl10_101 ),
    inference(avatar_component_clause,[],[f756])).

fof(f808,plain,
    ( ~ spl10_111
    | spl10_99 ),
    inference(avatar_split_clause,[],[f761,f737,f806])).

fof(f806,plain,
    ( spl10_111
  <=> ~ r2_hidden(sK2,k1_zfmisc_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_111])])).

fof(f737,plain,
    ( spl10_99
  <=> ~ m1_subset_1(sK2,k1_zfmisc_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_99])])).

fof(f761,plain,
    ( ~ r2_hidden(sK2,k1_zfmisc_1(sK3))
    | ~ spl10_99 ),
    inference(unit_resulting_resolution,[],[f738,f115])).

fof(f738,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK3))
    | ~ spl10_99 ),
    inference(avatar_component_clause,[],[f737])).

fof(f801,plain,
    ( ~ spl10_109
    | ~ spl10_24 ),
    inference(avatar_split_clause,[],[f727,f217,f799])).

fof(f727,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK2),sK3)
    | ~ spl10_24 ),
    inference(unit_resulting_resolution,[],[f218,f114])).

fof(f794,plain,
    ( spl10_106
    | ~ spl10_20
    | ~ spl10_72 ),
    inference(avatar_split_clause,[],[f669,f490,f202,f792])).

fof(f202,plain,
    ( spl10_20
  <=> m1_subset_1(sK3,k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_20])])).

fof(f490,plain,
    ( spl10_72
  <=> r2_hidden(sK7(sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_72])])).

fof(f669,plain,
    ( m1_subset_1(sK7(sK3),sK2)
    | ~ spl10_20
    | ~ spl10_72 ),
    inference(unit_resulting_resolution,[],[f491,f203,f125])).

fof(f203,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK2))
    | ~ spl10_20 ),
    inference(avatar_component_clause,[],[f202])).

fof(f491,plain,
    ( r2_hidden(sK7(sK3),sK3)
    | ~ spl10_72 ),
    inference(avatar_component_clause,[],[f490])).

fof(f785,plain,
    ( ~ spl10_105
    | spl10_101 ),
    inference(avatar_split_clause,[],[f772,f756,f783])).

fof(f783,plain,
    ( spl10_105
  <=> ~ r1_tarski(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_105])])).

fof(f772,plain,
    ( ~ r1_tarski(sK2,k1_xboole_0)
    | ~ spl10_101 ),
    inference(unit_resulting_resolution,[],[f757,f122])).

fof(f769,plain,
    ( ~ spl10_103
    | spl10_99 ),
    inference(avatar_split_clause,[],[f759,f737,f767])).

fof(f767,plain,
    ( spl10_103
  <=> ~ r1_tarski(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_103])])).

fof(f759,plain,
    ( ~ r1_tarski(sK2,sK3)
    | ~ spl10_99 ),
    inference(unit_resulting_resolution,[],[f738,f122])).

fof(f758,plain,
    ( ~ spl10_101
    | ~ spl10_74
    | ~ spl10_88 ),
    inference(avatar_split_clause,[],[f694,f647,f532,f756])).

fof(f694,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl10_74
    | ~ spl10_88 ),
    inference(unit_resulting_resolution,[],[f533,f648,f126])).

fof(f739,plain,
    ( ~ spl10_99
    | spl10_69
    | ~ spl10_88 ),
    inference(avatar_split_clause,[],[f692,f647,f457,f737])).

fof(f692,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK3))
    | ~ spl10_69
    | ~ spl10_88 ),
    inference(unit_resulting_resolution,[],[f458,f648,f125])).

fof(f717,plain,
    ( ~ spl10_97
    | ~ spl10_88 ),
    inference(avatar_split_clause,[],[f698,f647,f715])).

fof(f715,plain,
    ( spl10_97
  <=> ~ r2_hidden(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_97])])).

fof(f698,plain,
    ( ~ r2_hidden(sK2,sK1)
    | ~ spl10_88 ),
    inference(unit_resulting_resolution,[],[f648,f114])).

fof(f710,plain,
    ( spl10_94
    | ~ spl10_88 ),
    inference(avatar_split_clause,[],[f696,f647,f708])).

fof(f708,plain,
    ( spl10_94
  <=> m1_subset_1(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_94])])).

fof(f696,plain,
    ( m1_subset_1(sK1,sK2)
    | ~ spl10_88 ),
    inference(unit_resulting_resolution,[],[f648,f115])).

fof(f687,plain,
    ( spl10_19
    | spl10_67
    | ~ spl10_68 ),
    inference(avatar_contradiction_clause,[],[f686])).

fof(f686,plain,
    ( $false
    | ~ spl10_19
    | ~ spl10_67
    | ~ spl10_68 ),
    inference(subsumption_resolution,[],[f192,f660])).

fof(f660,plain,
    ( r2_hidden(sK1,sK3)
    | ~ spl10_67
    | ~ spl10_68 ),
    inference(unit_resulting_resolution,[],[f452,f461,f116])).

fof(f461,plain,
    ( m1_subset_1(sK1,sK3)
    | ~ spl10_68 ),
    inference(avatar_component_clause,[],[f460])).

fof(f460,plain,
    ( spl10_68
  <=> m1_subset_1(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_68])])).

fof(f192,plain,
    ( ~ r2_hidden(sK1,sK3)
    | ~ spl10_19 ),
    inference(avatar_component_clause,[],[f191])).

fof(f191,plain,
    ( spl10_19
  <=> ~ r2_hidden(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_19])])).

fof(f685,plain,
    ( ~ spl10_18
    | ~ spl10_20
    | spl10_89
    | spl10_93 ),
    inference(avatar_contradiction_clause,[],[f684])).

fof(f684,plain,
    ( $false
    | ~ spl10_18
    | ~ spl10_20
    | ~ spl10_89
    | ~ spl10_93 ),
    inference(subsumption_resolution,[],[f682,f670])).

fof(f670,plain,
    ( m1_subset_1(sK1,sK2)
    | ~ spl10_18
    | ~ spl10_20 ),
    inference(unit_resulting_resolution,[],[f195,f203,f125])).

fof(f682,plain,
    ( ~ m1_subset_1(sK1,sK2)
    | ~ spl10_89
    | ~ spl10_93 ),
    inference(unit_resulting_resolution,[],[f645,f679,f116])).

fof(f645,plain,
    ( ~ r2_hidden(sK1,sK2)
    | ~ spl10_89 ),
    inference(avatar_component_clause,[],[f644])).

fof(f644,plain,
    ( spl10_89
  <=> ~ r2_hidden(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_89])])).

fof(f680,plain,
    ( ~ spl10_93
    | ~ spl10_20
    | ~ spl10_72 ),
    inference(avatar_split_clause,[],[f671,f490,f202,f678])).

fof(f671,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ spl10_20
    | ~ spl10_72 ),
    inference(unit_resulting_resolution,[],[f491,f203,f126])).

fof(f668,plain,
    ( ~ spl10_91
    | ~ spl10_18 ),
    inference(avatar_split_clause,[],[f654,f194,f666])).

fof(f666,plain,
    ( spl10_91
  <=> ~ r2_hidden(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_91])])).

fof(f654,plain,
    ( ~ r2_hidden(sK3,sK1)
    | ~ spl10_18 ),
    inference(unit_resulting_resolution,[],[f195,f114])).

fof(f649,plain,
    ( spl10_88
    | spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_12 ),
    inference(avatar_split_clause,[],[f639,f174,f167,f160,f146,f139,f132,f647])).

fof(f639,plain,
    ( r2_hidden(sK1,sK2)
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_12 ),
    inference(unit_resulting_resolution,[],[f133,f140,f147,f161,f175,f168,f105])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_connsp_2(X1,X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | r2_hidden(X2,X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,X1)
              | ~ m1_connsp_2(X1,X0,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,X1)
              | ~ m1_connsp_2(X1,X0,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( m1_connsp_2(X1,X0,X2)
               => r2_hidden(X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t8_connsp_2.p',t6_connsp_2)).

fof(f638,plain,
    ( ~ spl10_87
    | spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_8
    | spl10_27 ),
    inference(avatar_split_clause,[],[f621,f231,f160,f146,f139,f132,f636])).

fof(f636,plain,
    ( spl10_87
  <=> ~ m1_connsp_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_87])])).

fof(f621,plain,
    ( ~ m1_connsp_2(sK3,sK0,sK1)
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_8
    | ~ spl10_27 ),
    inference(unit_resulting_resolution,[],[f133,f140,f147,f161,f232,f117])).

fof(f620,plain,
    ( ~ spl10_27
    | spl10_29 ),
    inference(avatar_split_clause,[],[f248,f244,f231])).

fof(f244,plain,
    ( spl10_29
  <=> ~ r1_tarski(sK3,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_29])])).

fof(f248,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl10_29 ),
    inference(resolution,[],[f245,f121])).

fof(f245,plain,
    ( ~ r1_tarski(sK3,u1_struct_0(sK0))
    | ~ spl10_29 ),
    inference(avatar_component_clause,[],[f244])).

fof(f617,plain,
    ( ~ spl10_85
    | spl10_81 ),
    inference(avatar_split_clause,[],[f600,f595,f615])).

fof(f615,plain,
    ( spl10_85
  <=> ~ r2_hidden(sK3,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_85])])).

fof(f595,plain,
    ( spl10_81
  <=> ~ m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_81])])).

fof(f600,plain,
    ( ~ r2_hidden(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ spl10_81 ),
    inference(unit_resulting_resolution,[],[f596,f115])).

fof(f596,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ spl10_81 ),
    inference(avatar_component_clause,[],[f595])).

fof(f608,plain,
    ( ~ spl10_83
    | spl10_81 ),
    inference(avatar_split_clause,[],[f598,f595,f606])).

fof(f606,plain,
    ( spl10_83
  <=> ~ r1_tarski(sK3,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_83])])).

fof(f598,plain,
    ( ~ r1_tarski(sK3,k1_xboole_0)
    | ~ spl10_81 ),
    inference(unit_resulting_resolution,[],[f596,f122])).

fof(f597,plain,
    ( ~ spl10_81
    | ~ spl10_72
    | ~ spl10_74 ),
    inference(avatar_split_clause,[],[f572,f532,f490,f595])).

fof(f572,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ spl10_72
    | ~ spl10_74 ),
    inference(unit_resulting_resolution,[],[f491,f533,f126])).

fof(f590,plain,
    ( ~ spl10_79
    | ~ spl10_72 ),
    inference(avatar_split_clause,[],[f556,f490,f588])).

fof(f588,plain,
    ( spl10_79
  <=> ~ r2_hidden(sK3,sK7(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_79])])).

fof(f556,plain,
    ( ~ r2_hidden(sK3,sK7(sK3))
    | ~ spl10_72 ),
    inference(unit_resulting_resolution,[],[f491,f114])).

fof(f568,plain,
    ( spl10_76
    | spl10_75 ),
    inference(avatar_split_clause,[],[f537,f529,f566])).

fof(f566,plain,
    ( spl10_76
  <=> r2_hidden(sK7(k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_76])])).

fof(f529,plain,
    ( spl10_75
  <=> ~ v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_75])])).

fof(f537,plain,
    ( r2_hidden(sK7(k1_xboole_0),k1_xboole_0)
    | ~ spl10_75 ),
    inference(unit_resulting_resolution,[],[f113,f530,f116])).

fof(f530,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl10_75 ),
    inference(avatar_component_clause,[],[f529])).

fof(f534,plain,
    ( spl10_74
    | ~ spl10_66 ),
    inference(avatar_split_clause,[],[f515,f448,f532])).

fof(f448,plain,
    ( spl10_66
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_66])])).

fof(f515,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl10_66 ),
    inference(backward_demodulation,[],[f501,f449])).

fof(f449,plain,
    ( v1_xboole_0(sK3)
    | ~ spl10_66 ),
    inference(avatar_component_clause,[],[f448])).

fof(f501,plain,
    ( k1_xboole_0 = sK3
    | ~ spl10_66 ),
    inference(unit_resulting_resolution,[],[f449,f97])).

fof(f492,plain,
    ( spl10_72
    | spl10_67 ),
    inference(avatar_split_clause,[],[f454,f451,f490])).

fof(f454,plain,
    ( r2_hidden(sK7(sK3),sK3)
    | ~ spl10_67 ),
    inference(unit_resulting_resolution,[],[f113,f452,f116])).

fof(f475,plain,
    ( spl10_70
    | ~ spl10_20
    | spl10_25 ),
    inference(avatar_split_clause,[],[f468,f220,f202,f473])).

fof(f473,plain,
    ( spl10_70
  <=> v1_xboole_0(k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_70])])).

fof(f220,plain,
    ( spl10_25
  <=> ~ r2_hidden(sK3,k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_25])])).

fof(f468,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK2))
    | ~ spl10_20
    | ~ spl10_25 ),
    inference(unit_resulting_resolution,[],[f221,f203,f116])).

fof(f221,plain,
    ( ~ r2_hidden(sK3,k1_zfmisc_1(sK2))
    | ~ spl10_25 ),
    inference(avatar_component_clause,[],[f220])).

fof(f462,plain,
    ( spl10_68
    | ~ spl10_18 ),
    inference(avatar_split_clause,[],[f439,f194,f460])).

fof(f439,plain,
    ( m1_subset_1(sK1,sK3)
    | ~ spl10_18 ),
    inference(unit_resulting_resolution,[],[f195,f115])).

fof(f453,plain,
    ( ~ spl10_67
    | ~ spl10_18 ),
    inference(avatar_split_clause,[],[f442,f194,f451])).

fof(f442,plain,
    ( ~ v1_xboole_0(sK3)
    | ~ spl10_18 ),
    inference(unit_resulting_resolution,[],[f195,f124])).

fof(f437,plain,
    ( ~ spl10_16
    | spl10_21 ),
    inference(avatar_contradiction_clause,[],[f436])).

fof(f436,plain,
    ( $false
    | ~ spl10_16
    | ~ spl10_21 ),
    inference(subsumption_resolution,[],[f188,f225])).

fof(f225,plain,
    ( ~ r1_tarski(sK3,sK2)
    | ~ spl10_21 ),
    inference(resolution,[],[f122,f206])).

fof(f206,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK2))
    | ~ spl10_21 ),
    inference(avatar_component_clause,[],[f205])).

fof(f205,plain,
    ( spl10_21
  <=> ~ m1_subset_1(sK3,k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_21])])).

fof(f435,plain,
    ( ~ spl10_26
    | spl10_29 ),
    inference(avatar_contradiction_clause,[],[f434])).

fof(f434,plain,
    ( $false
    | ~ spl10_26
    | ~ spl10_29 ),
    inference(subsumption_resolution,[],[f235,f248])).

fof(f433,plain,
    ( ~ spl10_13
    | spl10_64 ),
    inference(avatar_split_clause,[],[f96,f431,f171])).

fof(f96,plain,(
    ! [X3] :
      ( ~ r2_hidden(sK1,X3)
      | ~ r1_tarski(X3,sK2)
      | ~ v3_pre_topc(X3,sK0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_connsp_2(sK2,sK0,sK1) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,
    ( ( ! [X3] :
          ( ~ r2_hidden(sK1,X3)
          | ~ r1_tarski(X3,sK2)
          | ~ v3_pre_topc(X3,sK0)
          | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
      | ~ m1_connsp_2(sK2,sK0,sK1) )
    & ( ( r2_hidden(sK1,sK3)
        & r1_tarski(sK3,sK2)
        & v3_pre_topc(sK3,sK0)
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) )
      | m1_connsp_2(sK2,sK0,sK1) )
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f65,f69,f68,f67,f66])).

fof(f66,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ! [X3] :
                      ( ~ r2_hidden(X1,X3)
                      | ~ r1_tarski(X3,X2)
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ m1_connsp_2(X2,X0,X1) )
                & ( ? [X4] :
                      ( r2_hidden(X1,X4)
                      & r1_tarski(X4,X2)
                      & v3_pre_topc(X4,X0)
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | m1_connsp_2(X2,X0,X1) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ! [X3] :
                    ( ~ r2_hidden(X1,X3)
                    | ~ r1_tarski(X3,X2)
                    | ~ v3_pre_topc(X3,sK0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
                | ~ m1_connsp_2(X2,sK0,X1) )
              & ( ? [X4] :
                    ( r2_hidden(X1,X4)
                    & r1_tarski(X4,X2)
                    & v3_pre_topc(X4,sK0)
                    & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
                | m1_connsp_2(X2,sK0,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f67,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ! [X3] :
                    ( ~ r2_hidden(X1,X3)
                    | ~ r1_tarski(X3,X2)
                    | ~ v3_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ m1_connsp_2(X2,X0,X1) )
              & ( ? [X4] :
                    ( r2_hidden(X1,X4)
                    & r1_tarski(X4,X2)
                    & v3_pre_topc(X4,X0)
                    & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                | m1_connsp_2(X2,X0,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(sK1,X3)
                  | ~ r1_tarski(X3,X2)
                  | ~ v3_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_connsp_2(X2,X0,sK1) )
            & ( ? [X4] :
                  ( r2_hidden(sK1,X4)
                  & r1_tarski(X4,X2)
                  & v3_pre_topc(X4,X0)
                  & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
              | m1_connsp_2(X2,X0,sK1) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK1,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( ~ r2_hidden(X1,X3)
                | ~ r1_tarski(X3,X2)
                | ~ v3_pre_topc(X3,X0)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ m1_connsp_2(X2,X0,X1) )
          & ( ? [X4] :
                ( r2_hidden(X1,X4)
                & r1_tarski(X4,X2)
                & v3_pre_topc(X4,X0)
                & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
            | m1_connsp_2(X2,X0,X1) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( ! [X3] :
              ( ~ r2_hidden(X1,X3)
              | ~ r1_tarski(X3,sK2)
              | ~ v3_pre_topc(X3,X0)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_connsp_2(sK2,X0,X1) )
        & ( ? [X4] :
              ( r2_hidden(X1,X4)
              & r1_tarski(X4,sK2)
              & v3_pre_topc(X4,X0)
              & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
          | m1_connsp_2(sK2,X0,X1) )
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ? [X4] :
          ( r2_hidden(X1,X4)
          & r1_tarski(X4,X2)
          & v3_pre_topc(X4,X0)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( r2_hidden(X1,sK3)
        & r1_tarski(sK3,X2)
        & v3_pre_topc(sK3,X0)
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ! [X3] :
                    ( ~ r2_hidden(X1,X3)
                    | ~ r1_tarski(X3,X2)
                    | ~ v3_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ m1_connsp_2(X2,X0,X1) )
              & ( ? [X4] :
                    ( r2_hidden(X1,X4)
                    & r1_tarski(X4,X2)
                    & v3_pre_topc(X4,X0)
                    & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                | m1_connsp_2(X2,X0,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(rectify,[],[f64])).

fof(f64,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ! [X3] :
                    ( ~ r2_hidden(X1,X3)
                    | ~ r1_tarski(X3,X2)
                    | ~ v3_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ m1_connsp_2(X2,X0,X1) )
              & ( ? [X3] :
                    ( r2_hidden(X1,X3)
                    & r1_tarski(X3,X2)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | m1_connsp_2(X2,X0,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f63])).

fof(f63,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ! [X3] :
                    ( ~ r2_hidden(X1,X3)
                    | ~ r1_tarski(X3,X2)
                    | ~ v3_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ m1_connsp_2(X2,X0,X1) )
              & ( ? [X3] :
                    ( r2_hidden(X1,X3)
                    & r1_tarski(X3,X2)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | m1_connsp_2(X2,X0,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <~> ? [X3] :
                    ( r2_hidden(X1,X3)
                    & r1_tarski(X3,X2)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <~> ? [X3] :
                    ( r2_hidden(X1,X3)
                    & r1_tarski(X3,X2)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
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
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( m1_connsp_2(X2,X0,X1)
                <=> ? [X3] :
                      ( r2_hidden(X1,X3)
                      & r1_tarski(X3,X2)
                      & v3_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m1_connsp_2(X2,X0,X1)
              <=> ? [X3] :
                    ( r2_hidden(X1,X3)
                    & r1_tarski(X3,X2)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t8_connsp_2.p',t8_connsp_2)).

fof(f429,plain,
    ( ~ spl10_63
    | ~ spl10_58 ),
    inference(avatar_split_clause,[],[f410,f397,f427])).

fof(f427,plain,
    ( spl10_63
  <=> ~ r2_hidden(u1_struct_0(sK0),sK7(sK5(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_63])])).

fof(f397,plain,
    ( spl10_58
  <=> r2_hidden(sK7(sK5(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_58])])).

fof(f410,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK7(sK5(sK0)))
    | ~ spl10_58 ),
    inference(unit_resulting_resolution,[],[f398,f114])).

fof(f398,plain,
    ( r2_hidden(sK7(sK5(sK0)),u1_struct_0(sK0))
    | ~ spl10_58 ),
    inference(avatar_component_clause,[],[f397])).

fof(f422,plain,
    ( ~ spl10_61
    | ~ spl10_56 ),
    inference(avatar_split_clause,[],[f402,f382,f420])).

fof(f420,plain,
    ( spl10_61
  <=> ~ r2_hidden(u1_struct_0(sK0),sK7(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_61])])).

fof(f382,plain,
    ( spl10_56
  <=> r2_hidden(sK7(u1_struct_0(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_56])])).

fof(f402,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK7(u1_struct_0(sK0)))
    | ~ spl10_56 ),
    inference(unit_resulting_resolution,[],[f383,f114])).

fof(f383,plain,
    ( r2_hidden(sK7(u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl10_56 ),
    inference(avatar_component_clause,[],[f382])).

fof(f399,plain,
    ( spl10_58
    | spl10_45
    | ~ spl10_54 ),
    inference(avatar_split_clause,[],[f377,f373,f320,f397])).

fof(f373,plain,
    ( spl10_54
  <=> m1_subset_1(sK7(sK5(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_54])])).

fof(f377,plain,
    ( r2_hidden(sK7(sK5(sK0)),u1_struct_0(sK0))
    | ~ spl10_45
    | ~ spl10_54 ),
    inference(unit_resulting_resolution,[],[f321,f374,f116])).

fof(f374,plain,
    ( m1_subset_1(sK7(sK5(sK0)),u1_struct_0(sK0))
    | ~ spl10_54 ),
    inference(avatar_component_clause,[],[f373])).

fof(f384,plain,
    ( spl10_56
    | spl10_45 ),
    inference(avatar_split_clause,[],[f324,f320,f382])).

fof(f324,plain,
    ( r2_hidden(sK7(u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl10_45 ),
    inference(unit_resulting_resolution,[],[f113,f321,f116])).

fof(f375,plain,
    ( spl10_54
    | ~ spl10_34
    | ~ spl10_42 ),
    inference(avatar_split_clause,[],[f313,f310,f271,f373])).

fof(f310,plain,
    ( spl10_42
  <=> m1_subset_1(sK5(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_42])])).

fof(f313,plain,
    ( m1_subset_1(sK7(sK5(sK0)),u1_struct_0(sK0))
    | ~ spl10_34
    | ~ spl10_42 ),
    inference(unit_resulting_resolution,[],[f272,f311,f125])).

fof(f311,plain,
    ( m1_subset_1(sK5(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl10_42 ),
    inference(avatar_component_clause,[],[f310])).

fof(f368,plain,
    ( spl10_52
    | spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_8 ),
    inference(avatar_split_clause,[],[f360,f160,f146,f139,f132,f366])).

fof(f366,plain,
    ( spl10_52
  <=> m1_connsp_2(sK8(sK0,sK1),sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_52])])).

fof(f360,plain,
    ( m1_connsp_2(sK8(sK0,sK1),sK0,sK1)
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_8 ),
    inference(unit_resulting_resolution,[],[f133,f140,f147,f161,f118])).

fof(f118,plain,(
    ! [X0,X1] :
      ( m1_connsp_2(sK8(X0,X1),X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( m1_connsp_2(sK8(X0,X1),X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f53,f82])).

fof(f82,plain,(
    ! [X1,X0] :
      ( ? [X2] : m1_connsp_2(X2,X0,X1)
     => m1_connsp_2(sK8(X0,X1),X0,X1) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ? [X2] : m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ? [X2] : m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X2] : m1_connsp_2(X2,X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t8_connsp_2.p',existence_m1_connsp_2)).

fof(f358,plain,
    ( spl10_50
    | ~ spl10_42 ),
    inference(avatar_split_clause,[],[f315,f310,f356])).

fof(f356,plain,
    ( spl10_50
  <=> r1_tarski(sK5(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_50])])).

fof(f315,plain,
    ( r1_tarski(sK5(sK0),u1_struct_0(sK0))
    | ~ spl10_42 ),
    inference(unit_resulting_resolution,[],[f311,f121])).

fof(f351,plain,
    ( ~ spl10_49
    | ~ spl10_46 ),
    inference(avatar_split_clause,[],[f339,f330,f349])).

fof(f349,plain,
    ( spl10_49
  <=> ~ r2_hidden(u1_struct_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_49])])).

fof(f339,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK1)
    | ~ spl10_46 ),
    inference(unit_resulting_resolution,[],[f331,f114])).

fof(f332,plain,
    ( spl10_46
    | ~ spl10_8
    | spl10_45 ),
    inference(avatar_split_clause,[],[f323,f320,f160,f330])).

fof(f323,plain,
    ( r2_hidden(sK1,u1_struct_0(sK0))
    | ~ spl10_8
    | ~ spl10_45 ),
    inference(unit_resulting_resolution,[],[f161,f321,f116])).

fof(f322,plain,
    ( ~ spl10_45
    | ~ spl10_34
    | ~ spl10_42 ),
    inference(avatar_split_clause,[],[f314,f310,f271,f320])).

fof(f314,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl10_34
    | ~ spl10_42 ),
    inference(unit_resulting_resolution,[],[f272,f311,f126])).

fof(f312,plain,
    ( spl10_42
    | spl10_1
    | ~ spl10_2
    | ~ spl10_4 ),
    inference(avatar_split_clause,[],[f305,f146,f139,f132,f310])).

fof(f305,plain,
    ( m1_subset_1(sK5(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_4 ),
    inference(unit_resulting_resolution,[],[f133,f140,f147,f106])).

fof(f106,plain,(
    ! [X0] :
      ( m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f75,plain,(
    ! [X0] :
      ( ( ~ v1_xboole_0(sK5(X0))
        & m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f43,f74])).

fof(f74,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v1_xboole_0(sK5(X0))
        & m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    inference(pure_predicate_removal,[],[f29])).

fof(f29,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( ~ v2_tops_1(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t8_connsp_2.p',rc6_tops_1)).

fof(f304,plain,
    ( ~ spl10_41
    | spl10_27 ),
    inference(avatar_split_clause,[],[f289,f231,f302])).

fof(f302,plain,
    ( spl10_41
  <=> ~ r2_hidden(sK3,sK7(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_41])])).

fof(f289,plain,
    ( ~ r2_hidden(sK3,sK7(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))
    | ~ spl10_27 ),
    inference(unit_resulting_resolution,[],[f232,f113,f125])).

fof(f297,plain,
    ( ~ spl10_39
    | spl10_21 ),
    inference(avatar_split_clause,[],[f288,f205,f295])).

fof(f295,plain,
    ( spl10_39
  <=> ~ r2_hidden(sK3,sK7(k1_zfmisc_1(k1_zfmisc_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_39])])).

fof(f288,plain,
    ( ~ r2_hidden(sK3,sK7(k1_zfmisc_1(k1_zfmisc_1(sK2))))
    | ~ spl10_21 ),
    inference(unit_resulting_resolution,[],[f206,f113,f125])).

fof(f287,plain,
    ( ~ spl10_37
    | ~ spl10_34 ),
    inference(avatar_split_clause,[],[f276,f271,f285])).

fof(f285,plain,
    ( spl10_37
  <=> ~ r2_hidden(sK5(sK0),sK7(sK5(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_37])])).

fof(f276,plain,
    ( ~ r2_hidden(sK5(sK0),sK7(sK5(sK0)))
    | ~ spl10_34 ),
    inference(unit_resulting_resolution,[],[f272,f114])).

fof(f273,plain,
    ( spl10_34
    | spl10_33 ),
    inference(avatar_split_clause,[],[f265,f262,f271])).

fof(f262,plain,
    ( spl10_33
  <=> ~ v1_xboole_0(sK5(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_33])])).

fof(f265,plain,
    ( r2_hidden(sK7(sK5(sK0)),sK5(sK0))
    | ~ spl10_33 ),
    inference(unit_resulting_resolution,[],[f113,f263,f116])).

fof(f263,plain,
    ( ~ v1_xboole_0(sK5(sK0))
    | ~ spl10_33 ),
    inference(avatar_component_clause,[],[f262])).

fof(f264,plain,
    ( ~ spl10_33
    | spl10_1
    | ~ spl10_2
    | ~ spl10_4 ),
    inference(avatar_split_clause,[],[f256,f146,f139,f132,f262])).

fof(f256,plain,
    ( ~ v1_xboole_0(sK5(sK0))
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_4 ),
    inference(unit_resulting_resolution,[],[f133,f140,f147,f107])).

fof(f107,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(sK5(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f255,plain,
    ( ~ spl10_31
    | spl10_27 ),
    inference(avatar_split_clause,[],[f238,f231,f253])).

fof(f253,plain,
    ( spl10_31
  <=> ~ r2_hidden(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_31])])).

fof(f238,plain,
    ( ~ r2_hidden(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl10_27 ),
    inference(unit_resulting_resolution,[],[f232,f115])).

fof(f246,plain,
    ( ~ spl10_29
    | spl10_27 ),
    inference(avatar_split_clause,[],[f237,f231,f244])).

fof(f237,plain,
    ( ~ r1_tarski(sK3,u1_struct_0(sK0))
    | ~ spl10_27 ),
    inference(unit_resulting_resolution,[],[f232,f122])).

fof(f236,plain,
    ( spl10_12
    | spl10_26 ),
    inference(avatar_split_clause,[],[f92,f234,f174])).

fof(f92,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_connsp_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f70])).

fof(f222,plain,
    ( ~ spl10_25
    | spl10_21 ),
    inference(avatar_split_clause,[],[f215,f205,f220])).

fof(f215,plain,
    ( ~ r2_hidden(sK3,k1_zfmisc_1(sK2))
    | ~ spl10_21 ),
    inference(unit_resulting_resolution,[],[f206,f115])).

fof(f214,plain,
    ( spl10_22
    | ~ spl10_10 ),
    inference(avatar_split_clause,[],[f199,f167,f212])).

fof(f212,plain,
    ( spl10_22
  <=> r1_tarski(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_22])])).

fof(f199,plain,
    ( r1_tarski(sK2,u1_struct_0(sK0))
    | ~ spl10_10 ),
    inference(unit_resulting_resolution,[],[f168,f121])).

fof(f207,plain,
    ( ~ spl10_21
    | spl10_17 ),
    inference(avatar_split_clause,[],[f197,f184,f205])).

fof(f184,plain,
    ( spl10_17
  <=> ~ r1_tarski(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_17])])).

fof(f197,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK2))
    | ~ spl10_17 ),
    inference(unit_resulting_resolution,[],[f185,f121])).

fof(f185,plain,
    ( ~ r1_tarski(sK3,sK2)
    | ~ spl10_17 ),
    inference(avatar_component_clause,[],[f184])).

fof(f196,plain,
    ( spl10_12
    | spl10_18 ),
    inference(avatar_split_clause,[],[f95,f194,f174])).

fof(f95,plain,
    ( r2_hidden(sK1,sK3)
    | m1_connsp_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f70])).

fof(f189,plain,
    ( spl10_12
    | spl10_16 ),
    inference(avatar_split_clause,[],[f94,f187,f174])).

fof(f94,plain,
    ( r1_tarski(sK3,sK2)
    | m1_connsp_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f70])).

fof(f182,plain,
    ( spl10_12
    | spl10_14 ),
    inference(avatar_split_clause,[],[f93,f180,f174])).

fof(f93,plain,
    ( v3_pre_topc(sK3,sK0)
    | m1_connsp_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f70])).

fof(f169,plain,(
    spl10_10 ),
    inference(avatar_split_clause,[],[f91,f167])).

fof(f91,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f70])).

fof(f162,plain,(
    spl10_8 ),
    inference(avatar_split_clause,[],[f90,f160])).

fof(f90,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f70])).

fof(f155,plain,(
    spl10_6 ),
    inference(avatar_split_clause,[],[f127,f153])).

fof(f153,plain,
    ( spl10_6
  <=> l1_pre_topc(sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f127,plain,(
    l1_pre_topc(sK9) ),
    inference(cnf_transformation,[],[f86])).

fof(f86,plain,(
    l1_pre_topc(sK9) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f13,f85])).

fof(f85,plain,
    ( ? [X0] : l1_pre_topc(X0)
   => l1_pre_topc(sK9) ),
    introduced(choice_axiom,[])).

fof(f13,axiom,(
    ? [X0] : l1_pre_topc(X0) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t8_connsp_2.p',existence_l1_pre_topc)).

fof(f148,plain,(
    spl10_4 ),
    inference(avatar_split_clause,[],[f89,f146])).

fof(f89,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f70])).

fof(f141,plain,(
    spl10_2 ),
    inference(avatar_split_clause,[],[f88,f139])).

fof(f88,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f70])).

fof(f134,plain,(
    ~ spl10_1 ),
    inference(avatar_split_clause,[],[f87,f132])).

fof(f87,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f70])).
%------------------------------------------------------------------------------
