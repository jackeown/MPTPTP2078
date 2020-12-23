%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : pre_topc__t58_pre_topc.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:45 EDT 2019

% Result     : Theorem 0.92s
% Output     : Refutation 0.92s
% Verified   : 
% Statistics : Number of formulae       :  598 (2416 expanded)
%              Number of leaves         :   82 ( 946 expanded)
%              Depth                    :   23
%              Number of atoms          : 3176 (10105 expanded)
%              Number of equality atoms :  140 ( 886 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :   13 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1287,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f83,f90,f97,f104,f148,f161,f174,f190,f212,f215,f235,f250,f257,f300,f320,f327,f342,f345,f360,f372,f375,f440,f475,f498,f504,f524,f564,f588,f595,f610,f621,f628,f922,f941,f960,f969,f993,f1000,f1006,f1007,f1020,f1027,f1034,f1041,f1050,f1057,f1064,f1065,f1066,f1073,f1080,f1081,f1089,f1090,f1091,f1095,f1102,f1110,f1111,f1115,f1116,f1117,f1118,f1119,f1120,f1127,f1129,f1142,f1143,f1150,f1158,f1159,f1166,f1167,f1174,f1182,f1185,f1192,f1193,f1194,f1267,f1268,f1281,f1286])).

fof(f1286,plain,
    ( ~ spl5_4
    | ~ spl5_12
    | ~ spl5_22
    | ~ spl5_26
    | ~ spl5_48
    | ~ spl5_50
    | spl5_119 ),
    inference(avatar_contradiction_clause,[],[f1285])).

fof(f1285,plain,
    ( $false
    | ~ spl5_4
    | ~ spl5_12
    | ~ spl5_22
    | ~ spl5_26
    | ~ spl5_48
    | ~ spl5_50
    | ~ spl5_119 ),
    inference(subsumption_resolution,[],[f1284,f488])).

fof(f488,plain,
    ( r1_tarski(sK1(sK0),u1_pre_topc(sK0))
    | ~ spl5_48 ),
    inference(avatar_component_clause,[],[f487])).

fof(f487,plain,
    ( spl5_48
  <=> r1_tarski(sK1(sK0),u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_48])])).

fof(f1284,plain,
    ( ~ r1_tarski(sK1(sK0),u1_pre_topc(sK0))
    | ~ spl5_4
    | ~ spl5_12
    | ~ spl5_22
    | ~ spl5_26
    | ~ spl5_50
    | ~ spl5_119 ),
    inference(subsumption_resolution,[],[f1282,f494])).

fof(f494,plain,
    ( m1_subset_1(sK1(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl5_50 ),
    inference(avatar_component_clause,[],[f493])).

fof(f493,plain,
    ( spl5_50
  <=> m1_subset_1(sK1(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_50])])).

fof(f1282,plain,
    ( ~ m1_subset_1(sK1(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ r1_tarski(sK1(sK0),u1_pre_topc(sK0))
    | ~ spl5_4
    | ~ spl5_12
    | ~ spl5_22
    | ~ spl5_26
    | ~ spl5_119 ),
    inference(resolution,[],[f1280,f313])).

fof(f313,plain,
    ( ! [X2] :
        ( r2_hidden(k5_setfam_1(u1_struct_0(sK0),X2),u1_pre_topc(sK0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ r1_tarski(X2,u1_pre_topc(sK0)) )
    | ~ spl5_4
    | ~ spl5_12
    | ~ spl5_22
    | ~ spl5_26 ),
    inference(forward_demodulation,[],[f308,f303])).

fof(f303,plain,
    ( u1_struct_0(sK0) = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl5_26 ),
    inference(equality_resolution,[],[f299])).

fof(f299,plain,
    ( ! [X6,X7] :
        ( g1_pre_topc(X6,X7) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
        | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X6 )
    | ~ spl5_26 ),
    inference(avatar_component_clause,[],[f298])).

fof(f298,plain,
    ( spl5_26
  <=> ! [X7,X6] :
        ( g1_pre_topc(X6,X7) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
        | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X6 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f308,plain,
    ( ! [X2] :
        ( r2_hidden(k5_setfam_1(u1_struct_0(sK0),X2),u1_pre_topc(sK0))
        | ~ r1_tarski(X2,u1_pre_topc(sK0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) )
    | ~ spl5_4
    | ~ spl5_12
    | ~ spl5_22
    | ~ spl5_26 ),
    inference(backward_demodulation,[],[f303,f290])).

fof(f290,plain,
    ( ! [X2] :
        ( ~ r1_tarski(X2,u1_pre_topc(sK0))
        | r2_hidden(k5_setfam_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X2),u1_pre_topc(sK0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) )
    | ~ spl5_4
    | ~ spl5_12
    | ~ spl5_22 ),
    inference(forward_demodulation,[],[f289,f249])).

fof(f249,plain,
    ( u1_pre_topc(sK0) = u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl5_22 ),
    inference(avatar_component_clause,[],[f248])).

fof(f248,plain,
    ( spl5_22
  <=> u1_pre_topc(sK0) = u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f289,plain,
    ( ! [X2] :
        ( r2_hidden(k5_setfam_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X2),u1_pre_topc(sK0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
        | ~ r1_tarski(X2,u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) )
    | ~ spl5_4
    | ~ spl5_12
    | ~ spl5_22 ),
    inference(subsumption_resolution,[],[f288,f96])).

fof(f96,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl5_4
  <=> v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f288,plain,
    ( ! [X2] :
        ( r2_hidden(k5_setfam_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X2),u1_pre_topc(sK0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
        | ~ r1_tarski(X2,u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
        | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
    | ~ spl5_12
    | ~ spl5_22 ),
    inference(subsumption_resolution,[],[f275,f164])).

fof(f164,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f163])).

fof(f163,plain,
    ( spl5_12
  <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f275,plain,
    ( ! [X2] :
        ( r2_hidden(k5_setfam_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X2),u1_pre_topc(sK0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
        | ~ r1_tarski(X2,u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
        | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
    | ~ spl5_22 ),
    inference(superposition,[],[f67,f249])).

fof(f67,plain,(
    ! [X0,X3] :
      ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ r1_tarski(X3,u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( ! [X2] :
                  ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                  | ~ r2_hidden(X2,u1_pre_topc(X0))
                  | ~ r2_hidden(X1,u1_pre_topc(X0))
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( ! [X2] :
                  ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                  | ~ r2_hidden(X2,u1_pre_topc(X0))
                  | ~ r2_hidden(X1,u1_pre_topc(X0))
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r2_hidden(X2,u1_pre_topc(X0))
                      & r2_hidden(X1,u1_pre_topc(X0)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) ) ) )
          & ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( r1_tarski(X3,u1_pre_topc(X0))
               => r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) ) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) ) ) ),
    inference(rectify,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r2_hidden(X2,u1_pre_topc(X0))
                      & r2_hidden(X1,u1_pre_topc(X0)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) ) ) )
          & ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( r1_tarski(X1,u1_pre_topc(X0))
               => r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) ) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t58_pre_topc.p',d1_pre_topc)).

fof(f1280,plain,
    ( ~ r2_hidden(k5_setfam_1(u1_struct_0(sK0),sK1(sK0)),u1_pre_topc(sK0))
    | ~ spl5_119 ),
    inference(avatar_component_clause,[],[f1279])).

fof(f1279,plain,
    ( spl5_119
  <=> ~ r2_hidden(k5_setfam_1(u1_struct_0(sK0),sK1(sK0)),u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_119])])).

fof(f1281,plain,
    ( ~ spl5_119
    | ~ spl5_107
    | ~ spl5_0
    | spl5_3
    | ~ spl5_4
    | ~ spl5_12
    | ~ spl5_22
    | ~ spl5_26
    | ~ spl5_30
    | ~ spl5_46
    | ~ spl5_74
    | ~ spl5_108 ),
    inference(avatar_split_clause,[],[f1274,f1137,f998,f484,f325,f298,f248,f163,f95,f88,f81,f1134,f1279])).

fof(f1134,plain,
    ( spl5_107
  <=> ~ m1_subset_1(sK3(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_107])])).

fof(f81,plain,
    ( spl5_0
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_0])])).

fof(f88,plain,
    ( spl5_3
  <=> ~ v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f325,plain,
    ( spl5_30
  <=> r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

fof(f484,plain,
    ( spl5_46
  <=> r2_hidden(sK3(sK0),u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_46])])).

fof(f998,plain,
    ( spl5_74
  <=> r2_hidden(sK2(sK0),u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_74])])).

fof(f1137,plain,
    ( spl5_108
  <=> m1_subset_1(sK2(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_108])])).

fof(f1274,plain,
    ( ~ m1_subset_1(sK3(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(sK0),sK1(sK0)),u1_pre_topc(sK0))
    | ~ spl5_0
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_12
    | ~ spl5_22
    | ~ spl5_26
    | ~ spl5_30
    | ~ spl5_46
    | ~ spl5_74
    | ~ spl5_108 ),
    inference(subsumption_resolution,[],[f1273,f89])).

fof(f89,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f88])).

fof(f1273,plain,
    ( ~ m1_subset_1(sK3(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(sK0),sK1(sK0)),u1_pre_topc(sK0))
    | v2_pre_topc(sK0)
    | ~ spl5_0
    | ~ spl5_4
    | ~ spl5_12
    | ~ spl5_22
    | ~ spl5_26
    | ~ spl5_30
    | ~ spl5_46
    | ~ spl5_74
    | ~ spl5_108 ),
    inference(subsumption_resolution,[],[f1272,f82])).

fof(f82,plain,
    ( l1_pre_topc(sK0)
    | ~ spl5_0 ),
    inference(avatar_component_clause,[],[f81])).

fof(f1272,plain,
    ( ~ m1_subset_1(sK3(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(sK0),sK1(sK0)),u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK0)
    | v2_pre_topc(sK0)
    | ~ spl5_4
    | ~ spl5_12
    | ~ spl5_22
    | ~ spl5_26
    | ~ spl5_30
    | ~ spl5_46
    | ~ spl5_74
    | ~ spl5_108 ),
    inference(subsumption_resolution,[],[f1271,f326])).

fof(f326,plain,
    ( r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | ~ spl5_30 ),
    inference(avatar_component_clause,[],[f325])).

fof(f1271,plain,
    ( ~ m1_subset_1(sK3(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(sK0),sK1(sK0)),u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK0)
    | v2_pre_topc(sK0)
    | ~ spl5_4
    | ~ spl5_12
    | ~ spl5_22
    | ~ spl5_26
    | ~ spl5_46
    | ~ spl5_74
    | ~ spl5_108 ),
    inference(subsumption_resolution,[],[f1270,f999])).

fof(f999,plain,
    ( r2_hidden(sK2(sK0),u1_pre_topc(sK0))
    | ~ spl5_74 ),
    inference(avatar_component_clause,[],[f998])).

fof(f1270,plain,
    ( ~ m1_subset_1(sK3(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK2(sK0),u1_pre_topc(sK0))
    | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(sK0),sK1(sK0)),u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK0)
    | v2_pre_topc(sK0)
    | ~ spl5_4
    | ~ spl5_12
    | ~ spl5_22
    | ~ spl5_26
    | ~ spl5_46
    | ~ spl5_108 ),
    inference(subsumption_resolution,[],[f1269,f485])).

fof(f485,plain,
    ( r2_hidden(sK3(sK0),u1_pre_topc(sK0))
    | ~ spl5_46 ),
    inference(avatar_component_clause,[],[f484])).

fof(f1269,plain,
    ( ~ m1_subset_1(sK3(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK3(sK0),u1_pre_topc(sK0))
    | ~ r2_hidden(sK2(sK0),u1_pre_topc(sK0))
    | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(sK0),sK1(sK0)),u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK0)
    | v2_pre_topc(sK0)
    | ~ spl5_4
    | ~ spl5_12
    | ~ spl5_22
    | ~ spl5_26
    | ~ spl5_108 ),
    inference(subsumption_resolution,[],[f942,f1138])).

fof(f1138,plain,
    ( m1_subset_1(sK2(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_108 ),
    inference(avatar_component_clause,[],[f1137])).

fof(f942,plain,
    ( ~ m1_subset_1(sK2(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK3(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK3(sK0),u1_pre_topc(sK0))
    | ~ r2_hidden(sK2(sK0),u1_pre_topc(sK0))
    | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(sK0),sK1(sK0)),u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK0)
    | v2_pre_topc(sK0)
    | ~ spl5_4
    | ~ spl5_12
    | ~ spl5_22
    | ~ spl5_26 ),
    inference(resolution,[],[f312,f62])).

fof(f62,plain,(
    ! [X0] :
      ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),sK2(X0),sK3(X0)),u1_pre_topc(X0))
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK1(X0)),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f312,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k9_subset_1(u1_struct_0(sK0),X0,X1),u1_pre_topc(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X1,u1_pre_topc(sK0))
        | ~ r2_hidden(X0,u1_pre_topc(sK0)) )
    | ~ spl5_4
    | ~ spl5_12
    | ~ spl5_22
    | ~ spl5_26 ),
    inference(forward_demodulation,[],[f311,f303])).

fof(f311,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(k9_subset_1(u1_struct_0(sK0),X0,X1),u1_pre_topc(sK0))
        | ~ r2_hidden(X1,u1_pre_topc(sK0))
        | ~ r2_hidden(X0,u1_pre_topc(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) )
    | ~ spl5_4
    | ~ spl5_12
    | ~ spl5_22
    | ~ spl5_26 ),
    inference(forward_demodulation,[],[f307,f303])).

fof(f307,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k9_subset_1(u1_struct_0(sK0),X0,X1),u1_pre_topc(sK0))
        | ~ r2_hidden(X1,u1_pre_topc(sK0))
        | ~ r2_hidden(X0,u1_pre_topc(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) )
    | ~ spl5_4
    | ~ spl5_12
    | ~ spl5_22
    | ~ spl5_26 ),
    inference(backward_demodulation,[],[f303,f287])).

fof(f287,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,u1_pre_topc(sK0))
        | ~ r2_hidden(X0,u1_pre_topc(sK0))
        | r2_hidden(k9_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X0,X1),u1_pre_topc(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) )
    | ~ spl5_4
    | ~ spl5_12
    | ~ spl5_22 ),
    inference(forward_demodulation,[],[f286,f249])).

fof(f286,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,u1_pre_topc(sK0))
        | r2_hidden(k9_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X0,X1),u1_pre_topc(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
        | ~ r2_hidden(X1,u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) )
    | ~ spl5_4
    | ~ spl5_12
    | ~ spl5_22 ),
    inference(forward_demodulation,[],[f285,f249])).

fof(f285,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k9_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X0,X1),u1_pre_topc(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
        | ~ r2_hidden(X0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
        | ~ r2_hidden(X1,u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) )
    | ~ spl5_4
    | ~ spl5_12
    | ~ spl5_22 ),
    inference(subsumption_resolution,[],[f284,f96])).

fof(f284,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k9_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X0,X1),u1_pre_topc(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
        | ~ r2_hidden(X0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
        | ~ r2_hidden(X1,u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
        | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
    | ~ spl5_12
    | ~ spl5_22 ),
    inference(subsumption_resolution,[],[f273,f164])).

fof(f273,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k9_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X0,X1),u1_pre_topc(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
        | ~ r2_hidden(X0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
        | ~ r2_hidden(X1,u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
        | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
    | ~ spl5_22 ),
    inference(superposition,[],[f63,f249])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | ~ r2_hidden(X2,u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f1268,plain,
    ( spl5_106
    | ~ spl5_49
    | ~ spl5_51
    | ~ spl5_0
    | spl5_3
    | ~ spl5_4
    | ~ spl5_12
    | ~ spl5_22
    | ~ spl5_26
    | ~ spl5_30 ),
    inference(avatar_split_clause,[],[f450,f325,f298,f248,f163,f95,f88,f81,f496,f490,f1131])).

fof(f1131,plain,
    ( spl5_106
  <=> m1_subset_1(sK3(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_106])])).

fof(f490,plain,
    ( spl5_49
  <=> ~ r1_tarski(sK1(sK0),u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_49])])).

fof(f496,plain,
    ( spl5_51
  <=> ~ m1_subset_1(sK1(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_51])])).

fof(f450,plain,
    ( ~ m1_subset_1(sK1(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ r1_tarski(sK1(sK0),u1_pre_topc(sK0))
    | m1_subset_1(sK3(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_0
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_12
    | ~ spl5_22
    | ~ spl5_26
    | ~ spl5_30 ),
    inference(subsumption_resolution,[],[f449,f89])).

fof(f449,plain,
    ( ~ m1_subset_1(sK1(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ r1_tarski(sK1(sK0),u1_pre_topc(sK0))
    | m1_subset_1(sK3(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_pre_topc(sK0)
    | ~ spl5_0
    | ~ spl5_4
    | ~ spl5_12
    | ~ spl5_22
    | ~ spl5_26
    | ~ spl5_30 ),
    inference(subsumption_resolution,[],[f448,f82])).

fof(f448,plain,
    ( ~ m1_subset_1(sK1(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ r1_tarski(sK1(sK0),u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK0)
    | m1_subset_1(sK3(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_pre_topc(sK0)
    | ~ spl5_4
    | ~ spl5_12
    | ~ spl5_22
    | ~ spl5_26
    | ~ spl5_30 ),
    inference(subsumption_resolution,[],[f442,f326])).

fof(f442,plain,
    ( ~ m1_subset_1(sK1(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ r1_tarski(sK1(sK0),u1_pre_topc(sK0))
    | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK0)
    | m1_subset_1(sK3(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_pre_topc(sK0)
    | ~ spl5_4
    | ~ spl5_12
    | ~ spl5_22
    | ~ spl5_26 ),
    inference(resolution,[],[f313,f59])).

fof(f59,plain,(
    ! [X0] :
      ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK1(X0)),u1_pre_topc(X0))
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f1267,plain,
    ( spl5_108
    | ~ spl5_49
    | ~ spl5_51
    | ~ spl5_0
    | spl5_3
    | ~ spl5_4
    | ~ spl5_12
    | ~ spl5_22
    | ~ spl5_26
    | ~ spl5_30 ),
    inference(avatar_split_clause,[],[f447,f325,f298,f248,f163,f95,f88,f81,f496,f490,f1137])).

fof(f447,plain,
    ( ~ m1_subset_1(sK1(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ r1_tarski(sK1(sK0),u1_pre_topc(sK0))
    | m1_subset_1(sK2(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_0
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_12
    | ~ spl5_22
    | ~ spl5_26
    | ~ spl5_30 ),
    inference(subsumption_resolution,[],[f446,f89])).

fof(f446,plain,
    ( ~ m1_subset_1(sK1(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ r1_tarski(sK1(sK0),u1_pre_topc(sK0))
    | m1_subset_1(sK2(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_pre_topc(sK0)
    | ~ spl5_0
    | ~ spl5_4
    | ~ spl5_12
    | ~ spl5_22
    | ~ spl5_26
    | ~ spl5_30 ),
    inference(subsumption_resolution,[],[f445,f82])).

fof(f445,plain,
    ( ~ m1_subset_1(sK1(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ r1_tarski(sK1(sK0),u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK0)
    | m1_subset_1(sK2(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_pre_topc(sK0)
    | ~ spl5_4
    | ~ spl5_12
    | ~ spl5_22
    | ~ spl5_26
    | ~ spl5_30 ),
    inference(subsumption_resolution,[],[f441,f326])).

fof(f441,plain,
    ( ~ m1_subset_1(sK1(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ r1_tarski(sK1(sK0),u1_pre_topc(sK0))
    | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK0)
    | m1_subset_1(sK2(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_pre_topc(sK0)
    | ~ spl5_4
    | ~ spl5_12
    | ~ spl5_22
    | ~ spl5_26 ),
    inference(resolution,[],[f313,f64])).

fof(f64,plain,(
    ! [X0] :
      ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK1(X0)),u1_pre_topc(X0))
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f1194,plain,
    ( spl5_70
    | spl5_80
    | spl5_116
    | ~ spl5_73
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(avatar_split_clause,[],[f934,f626,f619,f331,f988,f1190,f1018,f982])).

fof(f982,plain,
    ( spl5_70
  <=> v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_70])])).

fof(f1018,plain,
    ( spl5_80
  <=> r2_hidden(sK2(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_80])])).

fof(f1190,plain,
    ( spl5_116
  <=> g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))))))) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_116])])).

fof(f988,plain,
    ( spl5_73
  <=> ~ r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_73])])).

fof(f331,plain,
    ( spl5_32
  <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).

fof(f619,plain,
    ( spl5_62
  <=> u1_pre_topc(sK4) = u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_62])])).

fof(f626,plain,
    ( spl5_64
  <=> u1_struct_0(sK4) = u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_64])])).

fof(f934,plain,
    ( ~ r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4))
    | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))))))) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))))))))
    | r2_hidden(sK2(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(sK4))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(forward_demodulation,[],[f933,f627])).

fof(f627,plain,
    ( u1_struct_0(sK4) = u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_64 ),
    inference(avatar_component_clause,[],[f626])).

fof(f933,plain,
    ( ~ r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(sK4))
    | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))))))) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))))))))
    | r2_hidden(sK2(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(sK4))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(forward_demodulation,[],[f932,f620])).

fof(f620,plain,
    ( u1_pre_topc(sK4) = u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_62 ),
    inference(avatar_component_clause,[],[f619])).

fof(f932,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))))))) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))))))))
    | r2_hidden(sK2(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(sK4))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(forward_demodulation,[],[f931,f627])).

fof(f931,plain,
    ( r2_hidden(sK2(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(sK4))
    | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))))))) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))))))))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ spl5_32
    | ~ spl5_62 ),
    inference(subsumption_resolution,[],[f930,f332])).

fof(f332,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_32 ),
    inference(avatar_component_clause,[],[f331])).

fof(f930,plain,
    ( r2_hidden(sK2(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(sK4))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))))))) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))))))))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ spl5_62 ),
    inference(superposition,[],[f531,f620])).

fof(f531,plain,(
    ! [X2] :
      ( r2_hidden(sK2(X2),u1_pre_topc(X2))
      | ~ l1_pre_topc(X2)
      | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X2),sK1(X2))),u1_pre_topc(g1_pre_topc(u1_struct_0(X2),sK1(X2))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X2),sK1(X2))),u1_pre_topc(g1_pre_topc(u1_struct_0(X2),sK1(X2))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X2),sK1(X2))),u1_pre_topc(g1_pre_topc(u1_struct_0(X2),sK1(X2))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X2),sK1(X2))),u1_pre_topc(g1_pre_topc(u1_struct_0(X2),sK1(X2)))))))) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X2),sK1(X2))),u1_pre_topc(g1_pre_topc(u1_struct_0(X2),sK1(X2))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X2),sK1(X2))),u1_pre_topc(g1_pre_topc(u1_struct_0(X2),sK1(X2))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X2),sK1(X2))),u1_pre_topc(g1_pre_topc(u1_struct_0(X2),sK1(X2))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X2),sK1(X2))),u1_pre_topc(g1_pre_topc(u1_struct_0(X2),sK1(X2))))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X2),sK1(X2))),u1_pre_topc(g1_pre_topc(u1_struct_0(X2),sK1(X2))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X2),sK1(X2))),u1_pre_topc(g1_pre_topc(u1_struct_0(X2),sK1(X2))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X2),sK1(X2))),u1_pre_topc(g1_pre_topc(u1_struct_0(X2),sK1(X2))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X2),sK1(X2))),u1_pre_topc(g1_pre_topc(u1_struct_0(X2),sK1(X2))))))))))
      | v2_pre_topc(X2)
      | ~ r2_hidden(u1_struct_0(X2),u1_pre_topc(X2)) ) ),
    inference(resolution,[],[f183,f111])).

fof(f111,plain,(
    ! [X0] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(X0),sK1(X0)))
      | ~ l1_pre_topc(X0)
      | r2_hidden(sK2(X0),u1_pre_topc(X0))
      | v2_pre_topc(X0)
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) ),
    inference(resolution,[],[f52,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | l1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t58_pre_topc.p',dt_g1_pre_topc)).

fof(f52,plain,(
    ! [X0] :
      ( m1_subset_1(sK1(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | r2_hidden(sK2(X0),u1_pre_topc(X0))
      | v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f183,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))))) ) ),
    inference(resolution,[],[f139,f105])).

fof(f105,plain,(
    ! [X0] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f74,f72])).

fof(f74,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t58_pre_topc.p',dt_u1_pre_topc)).

fof(f139,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))) ) ),
    inference(resolution,[],[f110,f105])).

fof(f110,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) ) ),
    inference(subsumption_resolution,[],[f109,f105])).

fof(f109,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) ) ),
    inference(resolution,[],[f106,f73])).

fof(f73,plain,(
    ! [X0] :
      ( ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t58_pre_topc.p',abstractness_v1_pre_topc)).

fof(f106,plain,(
    ! [X1] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f74,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | v1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f1193,plain,
    ( spl5_48
    | ~ spl5_0
    | spl5_3
    | ~ spl5_30
    | spl5_109 ),
    inference(avatar_split_clause,[],[f1184,f1140,f325,f88,f81,f487])).

fof(f1140,plain,
    ( spl5_109
  <=> ~ m1_subset_1(sK2(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_109])])).

fof(f1184,plain,
    ( r1_tarski(sK1(sK0),u1_pre_topc(sK0))
    | ~ spl5_0
    | ~ spl5_3
    | ~ spl5_30
    | ~ spl5_109 ),
    inference(subsumption_resolution,[],[f1183,f89])).

fof(f1183,plain,
    ( r1_tarski(sK1(sK0),u1_pre_topc(sK0))
    | v2_pre_topc(sK0)
    | ~ spl5_0
    | ~ spl5_30
    | ~ spl5_109 ),
    inference(subsumption_resolution,[],[f1178,f82])).

fof(f1178,plain,
    ( r1_tarski(sK1(sK0),u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK0)
    | v2_pre_topc(sK0)
    | ~ spl5_30
    | ~ spl5_109 ),
    inference(subsumption_resolution,[],[f1177,f326])).

fof(f1177,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | r1_tarski(sK1(sK0),u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK0)
    | v2_pre_topc(sK0)
    | ~ spl5_109 ),
    inference(resolution,[],[f1141,f65])).

fof(f65,plain,(
    ! [X0] :
      ( m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | r1_tarski(sK1(X0),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f1141,plain,
    ( ~ m1_subset_1(sK2(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_109 ),
    inference(avatar_component_clause,[],[f1140])).

fof(f1192,plain,
    ( spl5_70
    | spl5_82
    | spl5_116
    | ~ spl5_73
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(avatar_split_clause,[],[f928,f626,f619,f331,f988,f1190,f1025,f982])).

fof(f1025,plain,
    ( spl5_82
  <=> r2_hidden(sK3(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_82])])).

fof(f928,plain,
    ( ~ r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4))
    | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))))))) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))))))))
    | r2_hidden(sK3(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(sK4))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(forward_demodulation,[],[f927,f627])).

fof(f927,plain,
    ( ~ r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(sK4))
    | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))))))) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))))))))
    | r2_hidden(sK3(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(sK4))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(forward_demodulation,[],[f926,f620])).

fof(f926,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))))))) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))))))))
    | r2_hidden(sK3(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(sK4))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(forward_demodulation,[],[f925,f627])).

fof(f925,plain,
    ( r2_hidden(sK3(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(sK4))
    | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))))))) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))))))))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ spl5_32
    | ~ spl5_62 ),
    inference(subsumption_resolution,[],[f924,f332])).

fof(f924,plain,
    ( r2_hidden(sK3(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(sK4))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))))))) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))))))))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ spl5_62 ),
    inference(superposition,[],[f530,f620])).

fof(f530,plain,(
    ! [X1] :
      ( r2_hidden(sK3(X1),u1_pre_topc(X1))
      | ~ l1_pre_topc(X1)
      | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X1),sK1(X1))),u1_pre_topc(g1_pre_topc(u1_struct_0(X1),sK1(X1))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X1),sK1(X1))),u1_pre_topc(g1_pre_topc(u1_struct_0(X1),sK1(X1))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X1),sK1(X1))),u1_pre_topc(g1_pre_topc(u1_struct_0(X1),sK1(X1))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X1),sK1(X1))),u1_pre_topc(g1_pre_topc(u1_struct_0(X1),sK1(X1)))))))) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X1),sK1(X1))),u1_pre_topc(g1_pre_topc(u1_struct_0(X1),sK1(X1))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X1),sK1(X1))),u1_pre_topc(g1_pre_topc(u1_struct_0(X1),sK1(X1))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X1),sK1(X1))),u1_pre_topc(g1_pre_topc(u1_struct_0(X1),sK1(X1))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X1),sK1(X1))),u1_pre_topc(g1_pre_topc(u1_struct_0(X1),sK1(X1))))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X1),sK1(X1))),u1_pre_topc(g1_pre_topc(u1_struct_0(X1),sK1(X1))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X1),sK1(X1))),u1_pre_topc(g1_pre_topc(u1_struct_0(X1),sK1(X1))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X1),sK1(X1))),u1_pre_topc(g1_pre_topc(u1_struct_0(X1),sK1(X1))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X1),sK1(X1))),u1_pre_topc(g1_pre_topc(u1_struct_0(X1),sK1(X1))))))))))
      | v2_pre_topc(X1)
      | ~ r2_hidden(u1_struct_0(X1),u1_pre_topc(X1)) ) ),
    inference(resolution,[],[f183,f113])).

fof(f113,plain,(
    ! [X0] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(X0),sK1(X0)))
      | ~ l1_pre_topc(X0)
      | r2_hidden(sK3(X0),u1_pre_topc(X0))
      | v2_pre_topc(X0)
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) ),
    inference(resolution,[],[f53,f72])).

fof(f53,plain,(
    ! [X0] :
      ( m1_subset_1(sK1(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | r2_hidden(sK3(X0),u1_pre_topc(X0))
      | v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f1185,plain,
    ( spl5_70
    | spl5_80
    | spl5_114
    | ~ spl5_73
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(avatar_split_clause,[],[f738,f626,f619,f331,f988,f1172,f1018,f982])).

fof(f1172,plain,
    ( spl5_114
  <=> g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))))) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_114])])).

fof(f738,plain,
    ( ~ r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4))
    | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))))) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))))))
    | r2_hidden(sK2(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(sK4))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(forward_demodulation,[],[f737,f627])).

fof(f737,plain,
    ( ~ r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(sK4))
    | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))))) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))))))
    | r2_hidden(sK2(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(sK4))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(forward_demodulation,[],[f736,f620])).

fof(f736,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))))) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))))))
    | r2_hidden(sK2(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(sK4))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(forward_demodulation,[],[f735,f627])).

fof(f735,plain,
    ( r2_hidden(sK2(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(sK4))
    | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))))) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))))))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ spl5_32
    | ~ spl5_62 ),
    inference(subsumption_resolution,[],[f652,f332])).

fof(f652,plain,
    ( r2_hidden(sK2(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(sK4))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))))) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))))))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ spl5_62 ),
    inference(superposition,[],[f185,f620])).

fof(f185,plain,(
    ! [X2] :
      ( r2_hidden(sK2(X2),u1_pre_topc(X2))
      | ~ l1_pre_topc(X2)
      | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X2),sK1(X2))),u1_pre_topc(g1_pre_topc(u1_struct_0(X2),sK1(X2))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X2),sK1(X2))),u1_pre_topc(g1_pre_topc(u1_struct_0(X2),sK1(X2)))))) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X2),sK1(X2))),u1_pre_topc(g1_pre_topc(u1_struct_0(X2),sK1(X2))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X2),sK1(X2))),u1_pre_topc(g1_pre_topc(u1_struct_0(X2),sK1(X2))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X2),sK1(X2))),u1_pre_topc(g1_pre_topc(u1_struct_0(X2),sK1(X2))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X2),sK1(X2))),u1_pre_topc(g1_pre_topc(u1_struct_0(X2),sK1(X2))))))))
      | v2_pre_topc(X2)
      | ~ r2_hidden(u1_struct_0(X2),u1_pre_topc(X2)) ) ),
    inference(resolution,[],[f139,f111])).

fof(f1182,plain,
    ( ~ spl5_0
    | spl5_3
    | ~ spl5_30
    | spl5_49
    | spl5_109 ),
    inference(avatar_contradiction_clause,[],[f1181])).

fof(f1181,plain,
    ( $false
    | ~ spl5_0
    | ~ spl5_3
    | ~ spl5_30
    | ~ spl5_49
    | ~ spl5_109 ),
    inference(subsumption_resolution,[],[f1180,f89])).

fof(f1180,plain,
    ( v2_pre_topc(sK0)
    | ~ spl5_0
    | ~ spl5_30
    | ~ spl5_49
    | ~ spl5_109 ),
    inference(subsumption_resolution,[],[f1179,f82])).

fof(f1179,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_pre_topc(sK0)
    | ~ spl5_30
    | ~ spl5_49
    | ~ spl5_109 ),
    inference(subsumption_resolution,[],[f1178,f491])).

fof(f491,plain,
    ( ~ r1_tarski(sK1(sK0),u1_pre_topc(sK0))
    | ~ spl5_49 ),
    inference(avatar_component_clause,[],[f490])).

fof(f1174,plain,
    ( spl5_70
    | spl5_82
    | spl5_114
    | ~ spl5_73
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(avatar_split_clause,[],[f734,f626,f619,f331,f988,f1172,f1025,f982])).

fof(f734,plain,
    ( ~ r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4))
    | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))))) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))))))
    | r2_hidden(sK3(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(sK4))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(forward_demodulation,[],[f733,f627])).

fof(f733,plain,
    ( ~ r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(sK4))
    | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))))) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))))))
    | r2_hidden(sK3(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(sK4))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(forward_demodulation,[],[f732,f620])).

fof(f732,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))))) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))))))
    | r2_hidden(sK3(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(sK4))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(forward_demodulation,[],[f731,f627])).

fof(f731,plain,
    ( r2_hidden(sK3(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(sK4))
    | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))))) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))))))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ spl5_32
    | ~ spl5_62 ),
    inference(subsumption_resolution,[],[f651,f332])).

fof(f651,plain,
    ( r2_hidden(sK3(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(sK4))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))))) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))))))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ spl5_62 ),
    inference(superposition,[],[f184,f620])).

fof(f184,plain,(
    ! [X1] :
      ( r2_hidden(sK3(X1),u1_pre_topc(X1))
      | ~ l1_pre_topc(X1)
      | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X1),sK1(X1))),u1_pre_topc(g1_pre_topc(u1_struct_0(X1),sK1(X1))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X1),sK1(X1))),u1_pre_topc(g1_pre_topc(u1_struct_0(X1),sK1(X1)))))) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X1),sK1(X1))),u1_pre_topc(g1_pre_topc(u1_struct_0(X1),sK1(X1))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X1),sK1(X1))),u1_pre_topc(g1_pre_topc(u1_struct_0(X1),sK1(X1))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X1),sK1(X1))),u1_pre_topc(g1_pre_topc(u1_struct_0(X1),sK1(X1))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X1),sK1(X1))),u1_pre_topc(g1_pre_topc(u1_struct_0(X1),sK1(X1))))))))
      | v2_pre_topc(X1)
      | ~ r2_hidden(u1_struct_0(X1),u1_pre_topc(X1)) ) ),
    inference(resolution,[],[f139,f113])).

fof(f1167,plain,
    ( spl5_70
    | spl5_80
    | spl5_112
    | ~ spl5_73
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(avatar_split_clause,[],[f730,f626,f619,f331,f988,f1164,f1018,f982])).

fof(f1164,plain,
    ( spl5_112
  <=> g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_112])])).

fof(f730,plain,
    ( ~ r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4))
    | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))))
    | r2_hidden(sK2(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(sK4))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(forward_demodulation,[],[f729,f627])).

fof(f729,plain,
    ( ~ r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(sK4))
    | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))))
    | r2_hidden(sK2(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(sK4))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(forward_demodulation,[],[f728,f620])).

fof(f728,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))))
    | r2_hidden(sK2(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(sK4))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(forward_demodulation,[],[f727,f627])).

fof(f727,plain,
    ( r2_hidden(sK2(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(sK4))
    | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ spl5_32
    | ~ spl5_62 ),
    inference(subsumption_resolution,[],[f650,f332])).

fof(f650,plain,
    ( r2_hidden(sK2(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(sK4))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ spl5_62 ),
    inference(superposition,[],[f141,f620])).

fof(f141,plain,(
    ! [X2] :
      ( r2_hidden(sK2(X2),u1_pre_topc(X2))
      | ~ l1_pre_topc(X2)
      | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X2),sK1(X2))),u1_pre_topc(g1_pre_topc(u1_struct_0(X2),sK1(X2)))) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X2),sK1(X2))),u1_pre_topc(g1_pre_topc(u1_struct_0(X2),sK1(X2))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X2),sK1(X2))),u1_pre_topc(g1_pre_topc(u1_struct_0(X2),sK1(X2))))))
      | v2_pre_topc(X2)
      | ~ r2_hidden(u1_struct_0(X2),u1_pre_topc(X2)) ) ),
    inference(resolution,[],[f110,f111])).

fof(f1166,plain,
    ( spl5_70
    | spl5_82
    | spl5_112
    | ~ spl5_73
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(avatar_split_clause,[],[f726,f626,f619,f331,f988,f1164,f1025,f982])).

fof(f726,plain,
    ( ~ r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4))
    | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))))
    | r2_hidden(sK3(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(sK4))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(forward_demodulation,[],[f725,f627])).

fof(f725,plain,
    ( ~ r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(sK4))
    | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))))
    | r2_hidden(sK3(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(sK4))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(forward_demodulation,[],[f724,f620])).

fof(f724,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))))
    | r2_hidden(sK3(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(sK4))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(forward_demodulation,[],[f723,f627])).

fof(f723,plain,
    ( r2_hidden(sK3(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(sK4))
    | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ spl5_32
    | ~ spl5_62 ),
    inference(subsumption_resolution,[],[f649,f332])).

fof(f649,plain,
    ( r2_hidden(sK3(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(sK4))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ spl5_62 ),
    inference(superposition,[],[f140,f620])).

fof(f140,plain,(
    ! [X1] :
      ( r2_hidden(sK3(X1),u1_pre_topc(X1))
      | ~ l1_pre_topc(X1)
      | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X1),sK1(X1))),u1_pre_topc(g1_pre_topc(u1_struct_0(X1),sK1(X1)))) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X1),sK1(X1))),u1_pre_topc(g1_pre_topc(u1_struct_0(X1),sK1(X1))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X1),sK1(X1))),u1_pre_topc(g1_pre_topc(u1_struct_0(X1),sK1(X1))))))
      | v2_pre_topc(X1)
      | ~ r2_hidden(u1_struct_0(X1),u1_pre_topc(X1)) ) ),
    inference(resolution,[],[f110,f113])).

fof(f1159,plain,
    ( spl5_70
    | spl5_82
    | ~ spl5_73
    | spl5_110
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(avatar_split_clause,[],[f722,f626,f619,f331,f1148,f988,f1025,f982])).

fof(f1148,plain,
    ( spl5_110
  <=> g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_110])])).

fof(f722,plain,
    ( g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))
    | ~ r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4))
    | r2_hidden(sK3(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(sK4))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(forward_demodulation,[],[f721,f627])).

fof(f721,plain,
    ( ~ r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4))
    | r2_hidden(sK3(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(sK4))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(forward_demodulation,[],[f720,f627])).

fof(f720,plain,
    ( ~ r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(sK4))
    | r2_hidden(sK3(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(sK4))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))
    | ~ spl5_32
    | ~ spl5_62 ),
    inference(forward_demodulation,[],[f719,f620])).

fof(f719,plain,
    ( r2_hidden(sK3(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(sK4))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))
    | ~ spl5_32
    | ~ spl5_62 ),
    inference(subsumption_resolution,[],[f648,f332])).

fof(f648,plain,
    ( r2_hidden(sK3(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(sK4))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))
    | ~ spl5_62 ),
    inference(superposition,[],[f130,f620])).

fof(f130,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | v2_pre_topc(X0)
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | g1_pre_topc(u1_struct_0(X0),sK1(X0)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),sK1(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),sK1(X0)))) ) ),
    inference(subsumption_resolution,[],[f129,f113])).

fof(f129,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | r2_hidden(sK3(X0),u1_pre_topc(X0))
      | v2_pre_topc(X0)
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),sK1(X0)))
      | g1_pre_topc(u1_struct_0(X0),sK1(X0)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),sK1(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),sK1(X0)))) ) ),
    inference(resolution,[],[f114,f73])).

fof(f114,plain,(
    ! [X1] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(X1),sK1(X1)))
      | ~ l1_pre_topc(X1)
      | r2_hidden(sK3(X1),u1_pre_topc(X1))
      | v2_pre_topc(X1)
      | ~ r2_hidden(u1_struct_0(X1),u1_pre_topc(X1)) ) ),
    inference(resolution,[],[f53,f71])).

fof(f1158,plain,
    ( ~ spl5_0
    | spl5_3
    | ~ spl5_30
    | spl5_49
    | spl5_107 ),
    inference(avatar_contradiction_clause,[],[f1157])).

fof(f1157,plain,
    ( $false
    | ~ spl5_0
    | ~ spl5_3
    | ~ spl5_30
    | ~ spl5_49
    | ~ spl5_107 ),
    inference(subsumption_resolution,[],[f1156,f89])).

fof(f1156,plain,
    ( v2_pre_topc(sK0)
    | ~ spl5_0
    | ~ spl5_30
    | ~ spl5_49
    | ~ spl5_107 ),
    inference(subsumption_resolution,[],[f1155,f82])).

fof(f1155,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_pre_topc(sK0)
    | ~ spl5_30
    | ~ spl5_49
    | ~ spl5_107 ),
    inference(subsumption_resolution,[],[f1154,f491])).

fof(f1154,plain,
    ( r1_tarski(sK1(sK0),u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK0)
    | v2_pre_topc(sK0)
    | ~ spl5_30
    | ~ spl5_107 ),
    inference(subsumption_resolution,[],[f1153,f326])).

fof(f1153,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | r1_tarski(sK1(sK0),u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK0)
    | v2_pre_topc(sK0)
    | ~ spl5_107 ),
    inference(resolution,[],[f1135,f55])).

fof(f55,plain,(
    ! [X0] :
      ( m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | r1_tarski(sK1(X0),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f1135,plain,
    ( ~ m1_subset_1(sK3(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_107 ),
    inference(avatar_component_clause,[],[f1134])).

fof(f1150,plain,
    ( spl5_70
    | spl5_80
    | ~ spl5_73
    | spl5_110
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(avatar_split_clause,[],[f718,f626,f619,f331,f1148,f988,f1018,f982])).

fof(f718,plain,
    ( g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))
    | ~ r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4))
    | r2_hidden(sK2(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(sK4))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(forward_demodulation,[],[f717,f627])).

fof(f717,plain,
    ( ~ r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4))
    | r2_hidden(sK2(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(sK4))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(forward_demodulation,[],[f716,f627])).

fof(f716,plain,
    ( ~ r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(sK4))
    | r2_hidden(sK2(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(sK4))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))
    | ~ spl5_32
    | ~ spl5_62 ),
    inference(forward_demodulation,[],[f715,f620])).

fof(f715,plain,
    ( r2_hidden(sK2(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(sK4))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))
    | ~ spl5_32
    | ~ spl5_62 ),
    inference(subsumption_resolution,[],[f647,f332])).

fof(f647,plain,
    ( r2_hidden(sK2(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(sK4))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))
    | ~ spl5_62 ),
    inference(superposition,[],[f122,f620])).

fof(f122,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | v2_pre_topc(X0)
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | g1_pre_topc(u1_struct_0(X0),sK1(X0)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),sK1(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),sK1(X0)))) ) ),
    inference(subsumption_resolution,[],[f121,f111])).

fof(f121,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | r2_hidden(sK2(X0),u1_pre_topc(X0))
      | v2_pre_topc(X0)
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),sK1(X0)))
      | g1_pre_topc(u1_struct_0(X0),sK1(X0)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),sK1(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),sK1(X0)))) ) ),
    inference(resolution,[],[f112,f73])).

fof(f112,plain,(
    ! [X1] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(X1),sK1(X1)))
      | ~ l1_pre_topc(X1)
      | r2_hidden(sK2(X1),u1_pre_topc(X1))
      | v2_pre_topc(X1)
      | ~ r2_hidden(u1_struct_0(X1),u1_pre_topc(X1)) ) ),
    inference(resolution,[],[f52,f71])).

fof(f1143,plain,
    ( spl5_70
    | ~ spl5_105
    | ~ spl5_73
    | ~ spl5_99
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(avatar_split_clause,[],[f691,f626,f619,f331,f1100,f988,f1125,f982])).

fof(f1125,plain,
    ( spl5_105
  <=> ~ r2_hidden(k9_subset_1(u1_struct_0(sK4),sK2(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK3(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),u1_pre_topc(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_105])])).

fof(f1100,plain,
    ( spl5_99
  <=> ~ r2_hidden(k5_setfam_1(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),u1_pre_topc(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_99])])).

fof(f691,plain,
    ( ~ r2_hidden(k5_setfam_1(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),u1_pre_topc(sK4))
    | ~ r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4))
    | ~ r2_hidden(k9_subset_1(u1_struct_0(sK4),sK2(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK3(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),u1_pre_topc(sK4))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(forward_demodulation,[],[f690,f627])).

fof(f690,plain,
    ( ~ r2_hidden(k5_setfam_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),u1_pre_topc(sK4))
    | ~ r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4))
    | ~ r2_hidden(k9_subset_1(u1_struct_0(sK4),sK2(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK3(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),u1_pre_topc(sK4))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(forward_demodulation,[],[f689,f620])).

fof(f689,plain,
    ( ~ r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4))
    | ~ r2_hidden(k9_subset_1(u1_struct_0(sK4),sK2(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK3(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),u1_pre_topc(sK4))
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(forward_demodulation,[],[f688,f627])).

fof(f688,plain,
    ( ~ r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(sK4))
    | ~ r2_hidden(k9_subset_1(u1_struct_0(sK4),sK2(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK3(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),u1_pre_topc(sK4))
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(forward_demodulation,[],[f687,f620])).

fof(f687,plain,
    ( ~ r2_hidden(k9_subset_1(u1_struct_0(sK4),sK2(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK3(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),u1_pre_topc(sK4))
    | ~ r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(forward_demodulation,[],[f686,f627])).

fof(f686,plain,
    ( ~ r2_hidden(k9_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK2(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK3(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),u1_pre_topc(sK4))
    | ~ r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_32
    | ~ spl5_62 ),
    inference(subsumption_resolution,[],[f639,f332])).

fof(f639,plain,
    ( ~ r2_hidden(k9_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK2(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK3(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),u1_pre_topc(sK4))
    | ~ r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_62 ),
    inference(superposition,[],[f62,f620])).

fof(f1142,plain,
    ( ~ spl5_47
    | ~ spl5_107
    | ~ spl5_109
    | ~ spl5_0
    | spl5_3
    | ~ spl5_4
    | ~ spl5_12
    | ~ spl5_22
    | ~ spl5_26
    | ~ spl5_30
    | spl5_49 ),
    inference(avatar_split_clause,[],[f974,f490,f325,f298,f248,f163,f95,f88,f81,f1140,f1134,f481])).

fof(f481,plain,
    ( spl5_47
  <=> ~ r2_hidden(sK3(sK0),u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_47])])).

fof(f974,plain,
    ( ~ m1_subset_1(sK2(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK3(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK3(sK0),u1_pre_topc(sK0))
    | ~ spl5_0
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_12
    | ~ spl5_22
    | ~ spl5_26
    | ~ spl5_30
    | ~ spl5_49 ),
    inference(global_subsumption,[],[f567,f973])).

fof(f973,plain,
    ( ~ m1_subset_1(sK2(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK3(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK3(sK0),u1_pre_topc(sK0))
    | ~ r2_hidden(sK2(sK0),u1_pre_topc(sK0))
    | ~ spl5_0
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_12
    | ~ spl5_22
    | ~ spl5_26
    | ~ spl5_30
    | ~ spl5_49 ),
    inference(subsumption_resolution,[],[f972,f89])).

fof(f972,plain,
    ( ~ m1_subset_1(sK2(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK3(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK3(sK0),u1_pre_topc(sK0))
    | ~ r2_hidden(sK2(sK0),u1_pre_topc(sK0))
    | v2_pre_topc(sK0)
    | ~ spl5_0
    | ~ spl5_4
    | ~ spl5_12
    | ~ spl5_22
    | ~ spl5_26
    | ~ spl5_30
    | ~ spl5_49 ),
    inference(subsumption_resolution,[],[f971,f82])).

fof(f971,plain,
    ( ~ m1_subset_1(sK2(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK3(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK3(sK0),u1_pre_topc(sK0))
    | ~ r2_hidden(sK2(sK0),u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK0)
    | v2_pre_topc(sK0)
    | ~ spl5_4
    | ~ spl5_12
    | ~ spl5_22
    | ~ spl5_26
    | ~ spl5_30
    | ~ spl5_49 ),
    inference(subsumption_resolution,[],[f970,f491])).

fof(f970,plain,
    ( ~ m1_subset_1(sK2(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK3(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK3(sK0),u1_pre_topc(sK0))
    | ~ r2_hidden(sK2(sK0),u1_pre_topc(sK0))
    | r1_tarski(sK1(sK0),u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK0)
    | v2_pre_topc(sK0)
    | ~ spl5_4
    | ~ spl5_12
    | ~ spl5_22
    | ~ spl5_26
    | ~ spl5_30 ),
    inference(subsumption_resolution,[],[f944,f326])).

fof(f944,plain,
    ( ~ m1_subset_1(sK2(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK3(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK3(sK0),u1_pre_topc(sK0))
    | ~ r2_hidden(sK2(sK0),u1_pre_topc(sK0))
    | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | r1_tarski(sK1(sK0),u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK0)
    | v2_pre_topc(sK0)
    | ~ spl5_4
    | ~ spl5_12
    | ~ spl5_22
    | ~ spl5_26 ),
    inference(resolution,[],[f312,f58])).

fof(f58,plain,(
    ! [X0] :
      ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),sK2(X0),sK3(X0)),u1_pre_topc(X0))
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | r1_tarski(sK1(X0),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f567,plain,
    ( r2_hidden(sK2(sK0),u1_pre_topc(sK0))
    | ~ spl5_0
    | ~ spl5_3
    | ~ spl5_30
    | ~ spl5_49 ),
    inference(subsumption_resolution,[],[f566,f89])).

fof(f566,plain,
    ( r2_hidden(sK2(sK0),u1_pre_topc(sK0))
    | v2_pre_topc(sK0)
    | ~ spl5_0
    | ~ spl5_30
    | ~ spl5_49 ),
    inference(subsumption_resolution,[],[f565,f82])).

fof(f565,plain,
    ( ~ l1_pre_topc(sK0)
    | r2_hidden(sK2(sK0),u1_pre_topc(sK0))
    | v2_pre_topc(sK0)
    | ~ spl5_30
    | ~ spl5_49 ),
    inference(subsumption_resolution,[],[f559,f326])).

fof(f559,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK0)
    | r2_hidden(sK2(sK0),u1_pre_topc(sK0))
    | v2_pre_topc(sK0)
    | ~ spl5_49 ),
    inference(resolution,[],[f491,f56])).

fof(f56,plain,(
    ! [X0] :
      ( r1_tarski(sK1(X0),u1_pre_topc(X0))
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | r2_hidden(sK2(X0),u1_pre_topc(X0))
      | v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f1129,plain,
    ( spl5_70
    | ~ spl5_105
    | ~ spl5_73
    | spl5_96
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(avatar_split_clause,[],[f657,f626,f619,f331,f1078,f988,f1125,f982])).

fof(f1078,plain,
    ( spl5_96
  <=> m1_subset_1(sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_96])])).

fof(f657,plain,
    ( m1_subset_1(sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4))
    | ~ r2_hidden(k9_subset_1(u1_struct_0(sK4),sK2(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK3(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),u1_pre_topc(sK4))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(forward_demodulation,[],[f656,f627])).

fof(f656,plain,
    ( ~ r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4))
    | ~ r2_hidden(k9_subset_1(u1_struct_0(sK4),sK2(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK3(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),u1_pre_topc(sK4))
    | m1_subset_1(sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(forward_demodulation,[],[f655,f627])).

fof(f655,plain,
    ( ~ r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(sK4))
    | ~ r2_hidden(k9_subset_1(u1_struct_0(sK4),sK2(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK3(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),u1_pre_topc(sK4))
    | m1_subset_1(sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(forward_demodulation,[],[f654,f620])).

fof(f654,plain,
    ( ~ r2_hidden(k9_subset_1(u1_struct_0(sK4),sK2(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK3(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),u1_pre_topc(sK4))
    | ~ r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | m1_subset_1(sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(forward_demodulation,[],[f653,f627])).

fof(f653,plain,
    ( ~ r2_hidden(k9_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK2(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK3(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),u1_pre_topc(sK4))
    | ~ r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | m1_subset_1(sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_32
    | ~ spl5_62 ),
    inference(subsumption_resolution,[],[f632,f332])).

fof(f632,plain,
    ( ~ r2_hidden(k9_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK2(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK3(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),u1_pre_topc(sK4))
    | ~ r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | m1_subset_1(sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_62 ),
    inference(superposition,[],[f54,f620])).

fof(f54,plain,(
    ! [X0] :
      ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),sK2(X0),sK3(X0)),u1_pre_topc(X0))
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | m1_subset_1(sK1(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f1127,plain,
    ( spl5_70
    | ~ spl5_105
    | ~ spl5_73
    | spl5_78
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(avatar_split_clause,[],[f670,f626,f619,f331,f1012,f988,f1125,f982])).

fof(f1012,plain,
    ( spl5_78
  <=> r1_tarski(sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_78])])).

fof(f670,plain,
    ( r1_tarski(sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(sK4))
    | ~ r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4))
    | ~ r2_hidden(k9_subset_1(u1_struct_0(sK4),sK2(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK3(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),u1_pre_topc(sK4))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(forward_demodulation,[],[f669,f620])).

fof(f669,plain,
    ( ~ r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4))
    | ~ r2_hidden(k9_subset_1(u1_struct_0(sK4),sK2(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK3(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),u1_pre_topc(sK4))
    | r1_tarski(sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(forward_demodulation,[],[f668,f627])).

fof(f668,plain,
    ( ~ r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(sK4))
    | ~ r2_hidden(k9_subset_1(u1_struct_0(sK4),sK2(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK3(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),u1_pre_topc(sK4))
    | r1_tarski(sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(forward_demodulation,[],[f667,f620])).

fof(f667,plain,
    ( ~ r2_hidden(k9_subset_1(u1_struct_0(sK4),sK2(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK3(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),u1_pre_topc(sK4))
    | ~ r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | r1_tarski(sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(forward_demodulation,[],[f666,f627])).

fof(f666,plain,
    ( ~ r2_hidden(k9_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK2(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK3(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),u1_pre_topc(sK4))
    | ~ r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | r1_tarski(sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_32
    | ~ spl5_62 ),
    inference(subsumption_resolution,[],[f635,f332])).

fof(f635,plain,
    ( ~ r2_hidden(k9_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK2(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK3(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),u1_pre_topc(sK4))
    | ~ r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | r1_tarski(sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_62 ),
    inference(superposition,[],[f58,f620])).

fof(f1120,plain,
    ( spl5_74
    | ~ spl5_49
    | ~ spl5_51
    | ~ spl5_0
    | spl5_3
    | ~ spl5_4
    | ~ spl5_12
    | ~ spl5_22
    | ~ spl5_26
    | ~ spl5_30 ),
    inference(avatar_split_clause,[],[f456,f325,f298,f248,f163,f95,f88,f81,f496,f490,f998])).

fof(f456,plain,
    ( ~ m1_subset_1(sK1(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ r1_tarski(sK1(sK0),u1_pre_topc(sK0))
    | r2_hidden(sK2(sK0),u1_pre_topc(sK0))
    | ~ spl5_0
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_12
    | ~ spl5_22
    | ~ spl5_26
    | ~ spl5_30 ),
    inference(subsumption_resolution,[],[f455,f89])).

fof(f455,plain,
    ( ~ m1_subset_1(sK1(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ r1_tarski(sK1(sK0),u1_pre_topc(sK0))
    | r2_hidden(sK2(sK0),u1_pre_topc(sK0))
    | v2_pre_topc(sK0)
    | ~ spl5_0
    | ~ spl5_4
    | ~ spl5_12
    | ~ spl5_22
    | ~ spl5_26
    | ~ spl5_30 ),
    inference(subsumption_resolution,[],[f454,f82])).

fof(f454,plain,
    ( ~ m1_subset_1(sK1(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ r1_tarski(sK1(sK0),u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK0)
    | r2_hidden(sK2(sK0),u1_pre_topc(sK0))
    | v2_pre_topc(sK0)
    | ~ spl5_4
    | ~ spl5_12
    | ~ spl5_22
    | ~ spl5_26
    | ~ spl5_30 ),
    inference(subsumption_resolution,[],[f444,f326])).

fof(f444,plain,
    ( ~ m1_subset_1(sK1(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ r1_tarski(sK1(sK0),u1_pre_topc(sK0))
    | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK0)
    | r2_hidden(sK2(sK0),u1_pre_topc(sK0))
    | v2_pre_topc(sK0)
    | ~ spl5_4
    | ~ spl5_12
    | ~ spl5_22
    | ~ spl5_26 ),
    inference(resolution,[],[f313,f60])).

fof(f60,plain,(
    ! [X0] :
      ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK1(X0)),u1_pre_topc(X0))
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | r2_hidden(sK2(X0),u1_pre_topc(X0))
      | v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f1119,plain,
    ( spl5_70
    | ~ spl5_99
    | ~ spl5_73
    | spl5_86
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(avatar_split_clause,[],[f702,f626,f619,f331,f1039,f988,f1100,f982])).

fof(f1039,plain,
    ( spl5_86
  <=> m1_subset_1(sK2(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),k1_zfmisc_1(u1_struct_0(sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_86])])).

fof(f702,plain,
    ( m1_subset_1(sK2(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4))
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),u1_pre_topc(sK4))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(forward_demodulation,[],[f701,f627])).

fof(f701,plain,
    ( ~ r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4))
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),u1_pre_topc(sK4))
    | m1_subset_1(sK2(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(forward_demodulation,[],[f700,f627])).

fof(f700,plain,
    ( ~ r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(sK4))
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),u1_pre_topc(sK4))
    | m1_subset_1(sK2(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(forward_demodulation,[],[f699,f620])).

fof(f699,plain,
    ( ~ r2_hidden(k5_setfam_1(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),u1_pre_topc(sK4))
    | ~ r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | m1_subset_1(sK2(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(forward_demodulation,[],[f698,f627])).

fof(f698,plain,
    ( ~ r2_hidden(k5_setfam_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),u1_pre_topc(sK4))
    | ~ r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | m1_subset_1(sK2(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_32
    | ~ spl5_62 ),
    inference(subsumption_resolution,[],[f641,f332])).

fof(f641,plain,
    ( ~ r2_hidden(k5_setfam_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),u1_pre_topc(sK4))
    | ~ r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | m1_subset_1(sK2(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_62 ),
    inference(superposition,[],[f64,f620])).

fof(f1118,plain,
    ( spl5_70
    | ~ spl5_99
    | ~ spl5_73
    | spl5_84
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(avatar_split_clause,[],[f675,f626,f619,f331,f1032,f988,f1100,f982])).

fof(f1032,plain,
    ( spl5_84
  <=> m1_subset_1(sK3(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),k1_zfmisc_1(u1_struct_0(sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_84])])).

fof(f675,plain,
    ( m1_subset_1(sK3(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4))
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),u1_pre_topc(sK4))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(forward_demodulation,[],[f674,f627])).

fof(f674,plain,
    ( ~ r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4))
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),u1_pre_topc(sK4))
    | m1_subset_1(sK3(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(forward_demodulation,[],[f673,f627])).

fof(f673,plain,
    ( ~ r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(sK4))
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),u1_pre_topc(sK4))
    | m1_subset_1(sK3(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(forward_demodulation,[],[f672,f620])).

fof(f672,plain,
    ( ~ r2_hidden(k5_setfam_1(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),u1_pre_topc(sK4))
    | ~ r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | m1_subset_1(sK3(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(forward_demodulation,[],[f671,f627])).

fof(f671,plain,
    ( ~ r2_hidden(k5_setfam_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),u1_pre_topc(sK4))
    | ~ r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | m1_subset_1(sK3(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_32
    | ~ spl5_62 ),
    inference(subsumption_resolution,[],[f636,f332])).

fof(f636,plain,
    ( ~ r2_hidden(k5_setfam_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),u1_pre_topc(sK4))
    | ~ r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | m1_subset_1(sK3(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_62 ),
    inference(superposition,[],[f59,f620])).

fof(f1117,plain,
    ( spl5_70
    | spl5_96
    | ~ spl5_73
    | spl5_86
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(avatar_split_clause,[],[f832,f626,f619,f331,f1039,f988,f1078,f982])).

fof(f832,plain,
    ( m1_subset_1(sK2(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4))
    | m1_subset_1(sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(forward_demodulation,[],[f831,f627])).

fof(f831,plain,
    ( ~ r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4))
    | m1_subset_1(sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | m1_subset_1(sK2(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(forward_demodulation,[],[f830,f627])).

fof(f830,plain,
    ( ~ r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(sK4))
    | m1_subset_1(sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | m1_subset_1(sK2(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(forward_demodulation,[],[f829,f620])).

fof(f829,plain,
    ( m1_subset_1(sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | m1_subset_1(sK2(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_32
    | ~ spl5_64 ),
    inference(subsumption_resolution,[],[f753,f332])).

fof(f753,plain,
    ( m1_subset_1(sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | m1_subset_1(sK2(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_64 ),
    inference(superposition,[],[f66,f627])).

fof(f66,plain,(
    ! [X0] :
      ( m1_subset_1(sK1(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f1116,plain,
    ( spl5_70
    | spl5_96
    | ~ spl5_73
    | spl5_84
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(avatar_split_clause,[],[f770,f626,f619,f331,f1032,f988,f1078,f982])).

fof(f770,plain,
    ( m1_subset_1(sK3(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4))
    | m1_subset_1(sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(forward_demodulation,[],[f769,f627])).

fof(f769,plain,
    ( ~ r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4))
    | m1_subset_1(sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | m1_subset_1(sK3(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(forward_demodulation,[],[f768,f627])).

fof(f768,plain,
    ( ~ r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(sK4))
    | m1_subset_1(sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | m1_subset_1(sK3(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(forward_demodulation,[],[f767,f620])).

fof(f767,plain,
    ( m1_subset_1(sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | m1_subset_1(sK3(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_32
    | ~ spl5_64 ),
    inference(subsumption_resolution,[],[f740,f332])).

fof(f740,plain,
    ( m1_subset_1(sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | m1_subset_1(sK3(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_64 ),
    inference(superposition,[],[f51,f627])).

fof(f51,plain,(
    ! [X0] :
      ( m1_subset_1(sK1(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f1115,plain,
    ( ~ spl5_71
    | spl5_102
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(avatar_split_clause,[],[f697,f626,f619,f331,f1113,f985])).

fof(f985,plain,
    ( spl5_71
  <=> ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_71])])).

fof(f1113,plain,
    ( spl5_102
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X1,u1_pre_topc(sK4))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
        | ~ r2_hidden(X0,u1_pre_topc(sK4))
        | r2_hidden(k9_subset_1(u1_struct_0(sK4),X0,X1),u1_pre_topc(sK4))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_102])])).

fof(f697,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,u1_pre_topc(sK4))
        | ~ r2_hidden(X0,u1_pre_topc(sK4))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
        | r2_hidden(k9_subset_1(u1_struct_0(sK4),X0,X1),u1_pre_topc(sK4))
        | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) )
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(forward_demodulation,[],[f696,f620])).

fof(f696,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,u1_pre_topc(sK4))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
        | r2_hidden(k9_subset_1(u1_struct_0(sK4),X0,X1),u1_pre_topc(sK4))
        | ~ r2_hidden(X1,u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
        | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) )
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(forward_demodulation,[],[f695,f620])).

fof(f695,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
        | r2_hidden(k9_subset_1(u1_struct_0(sK4),X0,X1),u1_pre_topc(sK4))
        | ~ r2_hidden(X0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
        | ~ r2_hidden(X1,u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
        | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) )
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(forward_demodulation,[],[f694,f627])).

fof(f694,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
        | r2_hidden(k9_subset_1(u1_struct_0(sK4),X0,X1),u1_pre_topc(sK4))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))
        | ~ r2_hidden(X0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
        | ~ r2_hidden(X1,u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
        | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) )
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(forward_demodulation,[],[f693,f627])).

fof(f693,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k9_subset_1(u1_struct_0(sK4),X0,X1),u1_pre_topc(sK4))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))
        | ~ r2_hidden(X0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
        | ~ r2_hidden(X1,u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
        | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) )
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(forward_demodulation,[],[f692,f627])).

fof(f692,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k9_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),X0,X1),u1_pre_topc(sK4))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))
        | ~ r2_hidden(X0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
        | ~ r2_hidden(X1,u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
        | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) )
    | ~ spl5_32
    | ~ spl5_62 ),
    inference(subsumption_resolution,[],[f640,f332])).

fof(f640,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k9_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),X0,X1),u1_pre_topc(sK4))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))
        | ~ r2_hidden(X0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
        | ~ r2_hidden(X1,u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
        | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
        | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) )
    | ~ spl5_62 ),
    inference(superposition,[],[f63,f620])).

fof(f1111,plain,
    ( spl5_70
    | ~ spl5_99
    | ~ spl5_73
    | spl5_82
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(avatar_split_clause,[],[f685,f626,f619,f331,f1025,f988,f1100,f982])).

fof(f685,plain,
    ( r2_hidden(sK3(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(sK4))
    | ~ r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4))
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),u1_pre_topc(sK4))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(forward_demodulation,[],[f684,f620])).

fof(f684,plain,
    ( ~ r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4))
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),u1_pre_topc(sK4))
    | r2_hidden(sK3(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(forward_demodulation,[],[f683,f627])).

fof(f683,plain,
    ( ~ r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(sK4))
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),u1_pre_topc(sK4))
    | r2_hidden(sK3(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(forward_demodulation,[],[f682,f620])).

fof(f682,plain,
    ( ~ r2_hidden(k5_setfam_1(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),u1_pre_topc(sK4))
    | ~ r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | r2_hidden(sK3(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(forward_demodulation,[],[f681,f627])).

fof(f681,plain,
    ( ~ r2_hidden(k5_setfam_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),u1_pre_topc(sK4))
    | ~ r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | r2_hidden(sK3(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_32
    | ~ spl5_62 ),
    inference(subsumption_resolution,[],[f638,f332])).

fof(f638,plain,
    ( ~ r2_hidden(k5_setfam_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),u1_pre_topc(sK4))
    | ~ r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | r2_hidden(sK3(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_62 ),
    inference(superposition,[],[f61,f620])).

fof(f61,plain,(
    ! [X0] :
      ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK1(X0)),u1_pre_topc(X0))
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | r2_hidden(sK3(X0),u1_pre_topc(X0))
      | v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f1110,plain,
    ( ~ spl5_101
    | ~ spl5_6
    | spl5_73 ),
    inference(avatar_split_clause,[],[f1002,f988,f102,f1108])).

fof(f1108,plain,
    ( spl5_101
  <=> ~ v2_pre_topc(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_101])])).

fof(f102,plain,
    ( spl5_6
  <=> l1_pre_topc(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f1002,plain,
    ( ~ v2_pre_topc(sK4)
    | ~ spl5_6
    | ~ spl5_73 ),
    inference(subsumption_resolution,[],[f1001,f103])).

fof(f103,plain,
    ( l1_pre_topc(sK4)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f102])).

fof(f1001,plain,
    ( ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | ~ spl5_73 ),
    inference(resolution,[],[f989,f68])).

fof(f68,plain,(
    ! [X0] :
      ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f989,plain,
    ( ~ r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4))
    | ~ spl5_73 ),
    inference(avatar_component_clause,[],[f988])).

fof(f1102,plain,
    ( spl5_70
    | ~ spl5_99
    | ~ spl5_73
    | spl5_80
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(avatar_split_clause,[],[f680,f626,f619,f331,f1018,f988,f1100,f982])).

fof(f680,plain,
    ( r2_hidden(sK2(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(sK4))
    | ~ r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4))
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),u1_pre_topc(sK4))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(forward_demodulation,[],[f679,f620])).

fof(f679,plain,
    ( ~ r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4))
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),u1_pre_topc(sK4))
    | r2_hidden(sK2(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(forward_demodulation,[],[f678,f627])).

fof(f678,plain,
    ( ~ r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(sK4))
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),u1_pre_topc(sK4))
    | r2_hidden(sK2(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(forward_demodulation,[],[f677,f620])).

fof(f677,plain,
    ( ~ r2_hidden(k5_setfam_1(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),u1_pre_topc(sK4))
    | ~ r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | r2_hidden(sK2(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(forward_demodulation,[],[f676,f627])).

fof(f676,plain,
    ( ~ r2_hidden(k5_setfam_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),u1_pre_topc(sK4))
    | ~ r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | r2_hidden(sK2(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_32
    | ~ spl5_62 ),
    inference(subsumption_resolution,[],[f637,f332])).

fof(f637,plain,
    ( ~ r2_hidden(k5_setfam_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),u1_pre_topc(sK4))
    | ~ r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | r2_hidden(sK2(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_62 ),
    inference(superposition,[],[f60,f620])).

fof(f1095,plain,
    ( spl5_70
    | spl5_86
    | ~ spl5_73
    | spl5_90
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(avatar_split_clause,[],[f876,f626,f619,f331,f1055,f988,f1039,f982])).

fof(f1055,plain,
    ( spl5_90
  <=> v1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_90])])).

fof(f876,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))
    | ~ r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4))
    | m1_subset_1(sK2(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),k1_zfmisc_1(u1_struct_0(sK4)))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(forward_demodulation,[],[f875,f627])).

fof(f875,plain,
    ( ~ r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4))
    | m1_subset_1(sK2(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),k1_zfmisc_1(u1_struct_0(sK4)))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | v1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(forward_demodulation,[],[f874,f627])).

fof(f874,plain,
    ( ~ r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(sK4))
    | m1_subset_1(sK2(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),k1_zfmisc_1(u1_struct_0(sK4)))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | v1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(forward_demodulation,[],[f873,f620])).

fof(f873,plain,
    ( m1_subset_1(sK2(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | v1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))
    | ~ spl5_32
    | ~ spl5_64 ),
    inference(subsumption_resolution,[],[f766,f332])).

fof(f766,plain,
    ( m1_subset_1(sK2(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | v1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))
    | ~ spl5_64 ),
    inference(superposition,[],[f124,f627])).

fof(f124,plain,(
    ! [X1] :
      ( m1_subset_1(sK2(X1),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))
      | v2_pre_topc(X1)
      | v1_pre_topc(g1_pre_topc(u1_struct_0(X1),sK1(X1))) ) ),
    inference(resolution,[],[f66,f71])).

fof(f1091,plain,
    ( spl5_70
    | spl5_86
    | ~ spl5_73
    | spl5_88
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(avatar_split_clause,[],[f872,f626,f619,f331,f1048,f988,f1039,f982])).

fof(f1048,plain,
    ( spl5_88
  <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_88])])).

fof(f872,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))
    | ~ r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4))
    | m1_subset_1(sK2(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),k1_zfmisc_1(u1_struct_0(sK4)))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(forward_demodulation,[],[f871,f627])).

fof(f871,plain,
    ( ~ r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4))
    | m1_subset_1(sK2(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),k1_zfmisc_1(u1_struct_0(sK4)))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(forward_demodulation,[],[f870,f627])).

fof(f870,plain,
    ( ~ r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(sK4))
    | m1_subset_1(sK2(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),k1_zfmisc_1(u1_struct_0(sK4)))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(forward_demodulation,[],[f869,f620])).

fof(f869,plain,
    ( m1_subset_1(sK2(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))
    | ~ spl5_32
    | ~ spl5_64 ),
    inference(subsumption_resolution,[],[f765,f332])).

fof(f765,plain,
    ( m1_subset_1(sK2(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))
    | ~ spl5_64 ),
    inference(superposition,[],[f123,f627])).

fof(f123,plain,(
    ! [X0] :
      ( m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | v2_pre_topc(X0)
      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),sK1(X0))) ) ),
    inference(resolution,[],[f66,f72])).

fof(f1090,plain,
    ( spl5_70
    | spl5_84
    | ~ spl5_73
    | spl5_90
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(avatar_split_clause,[],[f868,f626,f619,f331,f1055,f988,f1032,f982])).

fof(f868,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))
    | ~ r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4))
    | m1_subset_1(sK3(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),k1_zfmisc_1(u1_struct_0(sK4)))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(forward_demodulation,[],[f867,f627])).

fof(f867,plain,
    ( ~ r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4))
    | m1_subset_1(sK3(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),k1_zfmisc_1(u1_struct_0(sK4)))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | v1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(forward_demodulation,[],[f866,f627])).

fof(f866,plain,
    ( ~ r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(sK4))
    | m1_subset_1(sK3(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),k1_zfmisc_1(u1_struct_0(sK4)))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | v1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(forward_demodulation,[],[f865,f620])).

fof(f865,plain,
    ( m1_subset_1(sK3(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | v1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))
    | ~ spl5_32
    | ~ spl5_64 ),
    inference(subsumption_resolution,[],[f764,f332])).

fof(f764,plain,
    ( m1_subset_1(sK3(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | v1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))
    | ~ spl5_64 ),
    inference(superposition,[],[f116,f627])).

fof(f116,plain,(
    ! [X1] :
      ( m1_subset_1(sK3(X1),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))
      | v2_pre_topc(X1)
      | v1_pre_topc(g1_pre_topc(u1_struct_0(X1),sK1(X1))) ) ),
    inference(resolution,[],[f51,f71])).

fof(f1089,plain,
    ( spl5_70
    | spl5_84
    | ~ spl5_73
    | spl5_88
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(avatar_split_clause,[],[f864,f626,f619,f331,f1048,f988,f1032,f982])).

fof(f864,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))
    | ~ r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4))
    | m1_subset_1(sK3(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),k1_zfmisc_1(u1_struct_0(sK4)))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(forward_demodulation,[],[f863,f627])).

fof(f863,plain,
    ( ~ r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4))
    | m1_subset_1(sK3(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),k1_zfmisc_1(u1_struct_0(sK4)))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(forward_demodulation,[],[f862,f627])).

fof(f862,plain,
    ( ~ r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(sK4))
    | m1_subset_1(sK3(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),k1_zfmisc_1(u1_struct_0(sK4)))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(forward_demodulation,[],[f861,f620])).

fof(f861,plain,
    ( m1_subset_1(sK3(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))
    | ~ spl5_32
    | ~ spl5_64 ),
    inference(subsumption_resolution,[],[f763,f332])).

fof(f763,plain,
    ( m1_subset_1(sK3(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))
    | ~ spl5_64 ),
    inference(superposition,[],[f115,f627])).

fof(f115,plain,(
    ! [X0] :
      ( m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | v2_pre_topc(X0)
      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),sK1(X0))) ) ),
    inference(resolution,[],[f51,f72])).

fof(f1081,plain,
    ( spl5_70
    | spl5_96
    | ~ spl5_73
    | spl5_82
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(avatar_split_clause,[],[f778,f626,f619,f331,f1025,f988,f1078,f982])).

fof(f778,plain,
    ( r2_hidden(sK3(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(sK4))
    | ~ r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4))
    | m1_subset_1(sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(forward_demodulation,[],[f777,f620])).

fof(f777,plain,
    ( ~ r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4))
    | m1_subset_1(sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | r2_hidden(sK3(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(forward_demodulation,[],[f776,f627])).

fof(f776,plain,
    ( ~ r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(sK4))
    | m1_subset_1(sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | r2_hidden(sK3(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(forward_demodulation,[],[f775,f620])).

fof(f775,plain,
    ( m1_subset_1(sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | r2_hidden(sK3(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_32
    | ~ spl5_64 ),
    inference(subsumption_resolution,[],[f742,f332])).

fof(f742,plain,
    ( m1_subset_1(sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | r2_hidden(sK3(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_64 ),
    inference(superposition,[],[f53,f627])).

fof(f1080,plain,
    ( spl5_70
    | spl5_96
    | ~ spl5_73
    | spl5_80
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(avatar_split_clause,[],[f774,f626,f619,f331,f1018,f988,f1078,f982])).

fof(f774,plain,
    ( r2_hidden(sK2(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(sK4))
    | ~ r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4))
    | m1_subset_1(sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(forward_demodulation,[],[f773,f620])).

fof(f773,plain,
    ( ~ r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4))
    | m1_subset_1(sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | r2_hidden(sK2(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(forward_demodulation,[],[f772,f627])).

fof(f772,plain,
    ( ~ r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(sK4))
    | m1_subset_1(sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | r2_hidden(sK2(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(forward_demodulation,[],[f771,f620])).

fof(f771,plain,
    ( m1_subset_1(sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | r2_hidden(sK2(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_32
    | ~ spl5_64 ),
    inference(subsumption_resolution,[],[f741,f332])).

fof(f741,plain,
    ( m1_subset_1(sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | r2_hidden(sK2(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_64 ),
    inference(superposition,[],[f52,f627])).

fof(f1073,plain,
    ( spl5_94
    | ~ spl5_50 ),
    inference(avatar_split_clause,[],[f1043,f493,f1071])).

fof(f1071,plain,
    ( spl5_94
  <=> v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),sK1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_94])])).

fof(f1043,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),sK1(sK0)))
    | ~ spl5_50 ),
    inference(resolution,[],[f494,f71])).

fof(f1066,plain,
    ( spl5_70
    | spl5_90
    | spl5_82
    | ~ spl5_73
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(avatar_split_clause,[],[f860,f626,f619,f331,f988,f1025,f1055,f982])).

fof(f860,plain,
    ( ~ r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4))
    | r2_hidden(sK3(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(sK4))
    | v1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(forward_demodulation,[],[f859,f627])).

fof(f859,plain,
    ( ~ r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(sK4))
    | r2_hidden(sK3(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(sK4))
    | v1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(forward_demodulation,[],[f858,f620])).

fof(f858,plain,
    ( r2_hidden(sK3(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(sK4))
    | v1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(forward_demodulation,[],[f857,f620])).

fof(f857,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))
    | r2_hidden(sK3(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ spl5_32
    | ~ spl5_64 ),
    inference(subsumption_resolution,[],[f762,f332])).

fof(f762,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | r2_hidden(sK3(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ spl5_64 ),
    inference(superposition,[],[f114,f627])).

fof(f1065,plain,
    ( spl5_70
    | spl5_88
    | spl5_82
    | ~ spl5_73
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(avatar_split_clause,[],[f856,f626,f619,f331,f988,f1025,f1048,f982])).

fof(f856,plain,
    ( ~ r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4))
    | r2_hidden(sK3(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(sK4))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(forward_demodulation,[],[f855,f627])).

fof(f855,plain,
    ( ~ r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(sK4))
    | r2_hidden(sK3(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(sK4))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(forward_demodulation,[],[f854,f620])).

fof(f854,plain,
    ( r2_hidden(sK3(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(sK4))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(forward_demodulation,[],[f853,f620])).

fof(f853,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))
    | r2_hidden(sK3(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ spl5_32
    | ~ spl5_64 ),
    inference(subsumption_resolution,[],[f761,f332])).

fof(f761,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | r2_hidden(sK3(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ spl5_64 ),
    inference(superposition,[],[f113,f627])).

fof(f1064,plain,
    ( spl5_92
    | ~ spl5_50 ),
    inference(avatar_split_clause,[],[f1042,f493,f1062])).

fof(f1062,plain,
    ( spl5_92
  <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),sK1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_92])])).

fof(f1042,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),sK1(sK0)))
    | ~ spl5_50 ),
    inference(resolution,[],[f494,f72])).

fof(f1057,plain,
    ( spl5_70
    | spl5_90
    | spl5_80
    | ~ spl5_73
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(avatar_split_clause,[],[f852,f626,f619,f331,f988,f1018,f1055,f982])).

fof(f852,plain,
    ( ~ r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4))
    | r2_hidden(sK2(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(sK4))
    | v1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(forward_demodulation,[],[f851,f627])).

fof(f851,plain,
    ( ~ r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(sK4))
    | r2_hidden(sK2(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(sK4))
    | v1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(forward_demodulation,[],[f850,f620])).

fof(f850,plain,
    ( r2_hidden(sK2(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(sK4))
    | v1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(forward_demodulation,[],[f849,f620])).

fof(f849,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))
    | r2_hidden(sK2(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ spl5_32
    | ~ spl5_64 ),
    inference(subsumption_resolution,[],[f760,f332])).

fof(f760,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | r2_hidden(sK2(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ spl5_64 ),
    inference(superposition,[],[f112,f627])).

fof(f1050,plain,
    ( spl5_70
    | spl5_88
    | spl5_80
    | ~ spl5_73
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(avatar_split_clause,[],[f848,f626,f619,f331,f988,f1018,f1048,f982])).

fof(f848,plain,
    ( ~ r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4))
    | r2_hidden(sK2(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(sK4))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(forward_demodulation,[],[f847,f627])).

fof(f847,plain,
    ( ~ r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(sK4))
    | r2_hidden(sK2(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(sK4))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(forward_demodulation,[],[f846,f620])).

fof(f846,plain,
    ( r2_hidden(sK2(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(sK4))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(forward_demodulation,[],[f845,f620])).

fof(f845,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))
    | r2_hidden(sK2(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ spl5_32
    | ~ spl5_64 ),
    inference(subsumption_resolution,[],[f759,f332])).

fof(f759,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | r2_hidden(sK2(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ spl5_64 ),
    inference(superposition,[],[f111,f627])).

fof(f1041,plain,
    ( spl5_70
    | spl5_86
    | ~ spl5_73
    | spl5_78
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(avatar_split_clause,[],[f828,f626,f619,f331,f1012,f988,f1039,f982])).

fof(f828,plain,
    ( r1_tarski(sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(sK4))
    | ~ r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4))
    | m1_subset_1(sK2(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),k1_zfmisc_1(u1_struct_0(sK4)))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(forward_demodulation,[],[f827,f620])).

fof(f827,plain,
    ( ~ r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4))
    | m1_subset_1(sK2(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),k1_zfmisc_1(u1_struct_0(sK4)))
    | r1_tarski(sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(forward_demodulation,[],[f826,f627])).

fof(f826,plain,
    ( ~ r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(sK4))
    | m1_subset_1(sK2(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),k1_zfmisc_1(u1_struct_0(sK4)))
    | r1_tarski(sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(forward_demodulation,[],[f825,f620])).

fof(f825,plain,
    ( m1_subset_1(sK2(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | r1_tarski(sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_32
    | ~ spl5_64 ),
    inference(subsumption_resolution,[],[f752,f332])).

fof(f752,plain,
    ( m1_subset_1(sK2(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | r1_tarski(sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_64 ),
    inference(superposition,[],[f65,f627])).

fof(f1034,plain,
    ( spl5_70
    | spl5_84
    | ~ spl5_73
    | spl5_78
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(avatar_split_clause,[],[f787,f626,f619,f331,f1012,f988,f1032,f982])).

fof(f787,plain,
    ( r1_tarski(sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(sK4))
    | ~ r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4))
    | m1_subset_1(sK3(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),k1_zfmisc_1(u1_struct_0(sK4)))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(forward_demodulation,[],[f786,f620])).

fof(f786,plain,
    ( ~ r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4))
    | m1_subset_1(sK3(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),k1_zfmisc_1(u1_struct_0(sK4)))
    | r1_tarski(sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(forward_demodulation,[],[f785,f627])).

fof(f785,plain,
    ( ~ r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(sK4))
    | m1_subset_1(sK3(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),k1_zfmisc_1(u1_struct_0(sK4)))
    | r1_tarski(sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(forward_demodulation,[],[f784,f620])).

fof(f784,plain,
    ( m1_subset_1(sK3(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | r1_tarski(sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_32
    | ~ spl5_64 ),
    inference(subsumption_resolution,[],[f744,f332])).

fof(f744,plain,
    ( m1_subset_1(sK3(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | r1_tarski(sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_64 ),
    inference(superposition,[],[f55,f627])).

fof(f1027,plain,
    ( spl5_70
    | spl5_78
    | ~ spl5_73
    | spl5_82
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(avatar_split_clause,[],[f665,f626,f619,f331,f1025,f988,f1012,f982])).

fof(f665,plain,
    ( r2_hidden(sK3(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(sK4))
    | ~ r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4))
    | r1_tarski(sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(sK4))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(forward_demodulation,[],[f664,f620])).

fof(f664,plain,
    ( ~ r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4))
    | r1_tarski(sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(sK4))
    | r2_hidden(sK3(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(forward_demodulation,[],[f663,f627])).

fof(f663,plain,
    ( ~ r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(sK4))
    | r1_tarski(sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(sK4))
    | r2_hidden(sK3(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_32
    | ~ spl5_62 ),
    inference(forward_demodulation,[],[f662,f620])).

fof(f662,plain,
    ( r1_tarski(sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(sK4))
    | ~ r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | r2_hidden(sK3(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_32
    | ~ spl5_62 ),
    inference(subsumption_resolution,[],[f634,f332])).

fof(f634,plain,
    ( r1_tarski(sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(sK4))
    | ~ r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | r2_hidden(sK3(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_62 ),
    inference(superposition,[],[f57,f620])).

fof(f57,plain,(
    ! [X0] :
      ( r1_tarski(sK1(X0),u1_pre_topc(X0))
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | r2_hidden(sK3(X0),u1_pre_topc(X0))
      | v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f1020,plain,
    ( spl5_70
    | spl5_78
    | ~ spl5_73
    | spl5_80
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(avatar_split_clause,[],[f661,f626,f619,f331,f1018,f988,f1012,f982])).

fof(f661,plain,
    ( r2_hidden(sK2(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(sK4))
    | ~ r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4))
    | r1_tarski(sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(sK4))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(forward_demodulation,[],[f660,f620])).

fof(f660,plain,
    ( ~ r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4))
    | r1_tarski(sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(sK4))
    | r2_hidden(sK2(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(forward_demodulation,[],[f659,f627])).

fof(f659,plain,
    ( ~ r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(sK4))
    | r1_tarski(sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(sK4))
    | r2_hidden(sK2(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_32
    | ~ spl5_62 ),
    inference(forward_demodulation,[],[f658,f620])).

fof(f658,plain,
    ( r1_tarski(sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(sK4))
    | ~ r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | r2_hidden(sK2(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_32
    | ~ spl5_62 ),
    inference(subsumption_resolution,[],[f633,f332])).

fof(f633,plain,
    ( r1_tarski(sK1(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(sK4))
    | ~ r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | r2_hidden(sK2(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_62 ),
    inference(superposition,[],[f56,f620])).

fof(f1007,plain,
    ( spl5_46
    | ~ spl5_0
    | spl5_3
    | ~ spl5_30
    | spl5_49 ),
    inference(avatar_split_clause,[],[f980,f490,f325,f88,f81,f484])).

fof(f980,plain,
    ( r2_hidden(sK3(sK0),u1_pre_topc(sK0))
    | ~ spl5_0
    | ~ spl5_3
    | ~ spl5_30
    | ~ spl5_49 ),
    inference(subsumption_resolution,[],[f979,f89])).

fof(f979,plain,
    ( r2_hidden(sK3(sK0),u1_pre_topc(sK0))
    | v2_pre_topc(sK0)
    | ~ spl5_0
    | ~ spl5_30
    | ~ spl5_49 ),
    inference(subsumption_resolution,[],[f978,f82])).

fof(f978,plain,
    ( ~ l1_pre_topc(sK0)
    | r2_hidden(sK3(sK0),u1_pre_topc(sK0))
    | v2_pre_topc(sK0)
    | ~ spl5_30
    | ~ spl5_49 ),
    inference(subsumption_resolution,[],[f629,f326])).

fof(f629,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK0)
    | r2_hidden(sK3(sK0),u1_pre_topc(sK0))
    | v2_pre_topc(sK0)
    | ~ spl5_49 ),
    inference(resolution,[],[f491,f57])).

fof(f1006,plain,
    ( ~ spl5_71
    | spl5_76
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(avatar_split_clause,[],[f706,f626,f619,f331,f1004,f985])).

fof(f1004,plain,
    ( spl5_76
  <=> ! [X2] :
        ( ~ r1_tarski(X2,u1_pre_topc(sK4))
        | r2_hidden(k5_setfam_1(u1_struct_0(sK4),X2),u1_pre_topc(sK4))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_76])])).

fof(f706,plain,
    ( ! [X2] :
        ( ~ r1_tarski(X2,u1_pre_topc(sK4))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
        | r2_hidden(k5_setfam_1(u1_struct_0(sK4),X2),u1_pre_topc(sK4))
        | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) )
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(forward_demodulation,[],[f705,f620])).

fof(f705,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
        | r2_hidden(k5_setfam_1(u1_struct_0(sK4),X2),u1_pre_topc(sK4))
        | ~ r1_tarski(X2,u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
        | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) )
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(forward_demodulation,[],[f704,f627])).

fof(f704,plain,
    ( ! [X2] :
        ( r2_hidden(k5_setfam_1(u1_struct_0(sK4),X2),u1_pre_topc(sK4))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))
        | ~ r1_tarski(X2,u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
        | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) )
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(forward_demodulation,[],[f703,f627])).

fof(f703,plain,
    ( ! [X2] :
        ( r2_hidden(k5_setfam_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),X2),u1_pre_topc(sK4))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))
        | ~ r1_tarski(X2,u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
        | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) )
    | ~ spl5_32
    | ~ spl5_62 ),
    inference(subsumption_resolution,[],[f642,f332])).

fof(f642,plain,
    ( ! [X2] :
        ( r2_hidden(k5_setfam_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),X2),u1_pre_topc(sK4))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))
        | ~ r1_tarski(X2,u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
        | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
        | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) )
    | ~ spl5_62 ),
    inference(superposition,[],[f67,f620])).

fof(f1000,plain,
    ( spl5_74
    | ~ spl5_0
    | spl5_3
    | ~ spl5_30
    | spl5_49 ),
    inference(avatar_split_clause,[],[f977,f490,f325,f88,f81,f998])).

fof(f977,plain,
    ( r2_hidden(sK2(sK0),u1_pre_topc(sK0))
    | ~ spl5_0
    | ~ spl5_3
    | ~ spl5_30
    | ~ spl5_49 ),
    inference(subsumption_resolution,[],[f976,f89])).

fof(f976,plain,
    ( r2_hidden(sK2(sK0),u1_pre_topc(sK0))
    | v2_pre_topc(sK0)
    | ~ spl5_0
    | ~ spl5_30
    | ~ spl5_49 ),
    inference(subsumption_resolution,[],[f975,f82])).

fof(f975,plain,
    ( ~ l1_pre_topc(sK0)
    | r2_hidden(sK2(sK0),u1_pre_topc(sK0))
    | v2_pre_topc(sK0)
    | ~ spl5_30
    | ~ spl5_49 ),
    inference(subsumption_resolution,[],[f630,f326])).

fof(f630,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK0)
    | r2_hidden(sK2(sK0),u1_pre_topc(sK0))
    | v2_pre_topc(sK0)
    | ~ spl5_49 ),
    inference(resolution,[],[f491,f56])).

fof(f993,plain,
    ( ~ spl5_71
    | spl5_72
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(avatar_split_clause,[],[f708,f626,f619,f331,f991,f985])).

fof(f991,plain,
    ( spl5_72
  <=> r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_72])])).

fof(f708,plain,
    ( r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_32
    | ~ spl5_62
    | ~ spl5_64 ),
    inference(forward_demodulation,[],[f707,f627])).

fof(f707,plain,
    ( r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(sK4))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_32
    | ~ spl5_62 ),
    inference(subsumption_resolution,[],[f643,f332])).

fof(f643,plain,
    ( r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(sK4))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_62 ),
    inference(superposition,[],[f68,f620])).

fof(f969,plain,
    ( ~ spl5_0
    | spl5_3
    | ~ spl5_4
    | ~ spl5_12
    | ~ spl5_22
    | ~ spl5_26
    | ~ spl5_30
    | spl5_49
    | spl5_51 ),
    inference(avatar_contradiction_clause,[],[f968])).

fof(f968,plain,
    ( $false
    | ~ spl5_0
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_12
    | ~ spl5_22
    | ~ spl5_26
    | ~ spl5_30
    | ~ spl5_49
    | ~ spl5_51 ),
    inference(subsumption_resolution,[],[f967,f89])).

fof(f967,plain,
    ( v2_pre_topc(sK0)
    | ~ spl5_0
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_12
    | ~ spl5_22
    | ~ spl5_26
    | ~ spl5_30
    | ~ spl5_49
    | ~ spl5_51 ),
    inference(subsumption_resolution,[],[f966,f82])).

fof(f966,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_pre_topc(sK0)
    | ~ spl5_0
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_12
    | ~ spl5_22
    | ~ spl5_26
    | ~ spl5_30
    | ~ spl5_49
    | ~ spl5_51 ),
    inference(subsumption_resolution,[],[f965,f491])).

fof(f965,plain,
    ( r1_tarski(sK1(sK0),u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK0)
    | v2_pre_topc(sK0)
    | ~ spl5_0
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_12
    | ~ spl5_22
    | ~ spl5_26
    | ~ spl5_30
    | ~ spl5_51 ),
    inference(subsumption_resolution,[],[f964,f326])).

fof(f964,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | r1_tarski(sK1(sK0),u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK0)
    | v2_pre_topc(sK0)
    | ~ spl5_0
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_12
    | ~ spl5_22
    | ~ spl5_26
    | ~ spl5_30
    | ~ spl5_51 ),
    inference(subsumption_resolution,[],[f963,f613])).

fof(f613,plain,
    ( r2_hidden(sK2(sK0),u1_pre_topc(sK0))
    | ~ spl5_0
    | ~ spl5_3
    | ~ spl5_30
    | ~ spl5_51 ),
    inference(subsumption_resolution,[],[f612,f89])).

fof(f612,plain,
    ( r2_hidden(sK2(sK0),u1_pre_topc(sK0))
    | v2_pre_topc(sK0)
    | ~ spl5_0
    | ~ spl5_30
    | ~ spl5_51 ),
    inference(subsumption_resolution,[],[f611,f82])).

fof(f611,plain,
    ( ~ l1_pre_topc(sK0)
    | r2_hidden(sK2(sK0),u1_pre_topc(sK0))
    | v2_pre_topc(sK0)
    | ~ spl5_30
    | ~ spl5_51 ),
    inference(subsumption_resolution,[],[f599,f326])).

fof(f599,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK0)
    | r2_hidden(sK2(sK0),u1_pre_topc(sK0))
    | v2_pre_topc(sK0)
    | ~ spl5_51 ),
    inference(resolution,[],[f497,f52])).

fof(f497,plain,
    ( ~ m1_subset_1(sK1(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl5_51 ),
    inference(avatar_component_clause,[],[f496])).

fof(f963,plain,
    ( ~ r2_hidden(sK2(sK0),u1_pre_topc(sK0))
    | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | r1_tarski(sK1(sK0),u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK0)
    | v2_pre_topc(sK0)
    | ~ spl5_0
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_12
    | ~ spl5_22
    | ~ spl5_26
    | ~ spl5_30
    | ~ spl5_51 ),
    inference(subsumption_resolution,[],[f962,f614])).

fof(f614,plain,
    ( r2_hidden(sK3(sK0),u1_pre_topc(sK0))
    | ~ spl5_0
    | ~ spl5_3
    | ~ spl5_30
    | ~ spl5_51 ),
    inference(subsumption_resolution,[],[f607,f89])).

fof(f607,plain,
    ( r2_hidden(sK3(sK0),u1_pre_topc(sK0))
    | v2_pre_topc(sK0)
    | ~ spl5_0
    | ~ spl5_30
    | ~ spl5_51 ),
    inference(subsumption_resolution,[],[f606,f82])).

fof(f606,plain,
    ( ~ l1_pre_topc(sK0)
    | r2_hidden(sK3(sK0),u1_pre_topc(sK0))
    | v2_pre_topc(sK0)
    | ~ spl5_30
    | ~ spl5_51 ),
    inference(subsumption_resolution,[],[f598,f326])).

fof(f598,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK0)
    | r2_hidden(sK3(sK0),u1_pre_topc(sK0))
    | v2_pre_topc(sK0)
    | ~ spl5_51 ),
    inference(resolution,[],[f497,f53])).

fof(f962,plain,
    ( ~ r2_hidden(sK3(sK0),u1_pre_topc(sK0))
    | ~ r2_hidden(sK2(sK0),u1_pre_topc(sK0))
    | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | r1_tarski(sK1(sK0),u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK0)
    | v2_pre_topc(sK0)
    | ~ spl5_0
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_12
    | ~ spl5_22
    | ~ spl5_26
    | ~ spl5_30
    | ~ spl5_51 ),
    inference(subsumption_resolution,[],[f961,f605])).

fof(f605,plain,
    ( m1_subset_1(sK3(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_0
    | ~ spl5_3
    | ~ spl5_30
    | ~ spl5_51 ),
    inference(subsumption_resolution,[],[f604,f89])).

fof(f604,plain,
    ( m1_subset_1(sK3(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_pre_topc(sK0)
    | ~ spl5_0
    | ~ spl5_30
    | ~ spl5_51 ),
    inference(subsumption_resolution,[],[f603,f82])).

fof(f603,plain,
    ( ~ l1_pre_topc(sK0)
    | m1_subset_1(sK3(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_pre_topc(sK0)
    | ~ spl5_30
    | ~ spl5_51 ),
    inference(subsumption_resolution,[],[f597,f326])).

fof(f597,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK0)
    | m1_subset_1(sK3(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_pre_topc(sK0)
    | ~ spl5_51 ),
    inference(resolution,[],[f497,f51])).

fof(f961,plain,
    ( ~ m1_subset_1(sK3(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK3(sK0),u1_pre_topc(sK0))
    | ~ r2_hidden(sK2(sK0),u1_pre_topc(sK0))
    | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | r1_tarski(sK1(sK0),u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK0)
    | v2_pre_topc(sK0)
    | ~ spl5_0
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_12
    | ~ spl5_22
    | ~ spl5_26
    | ~ spl5_30
    | ~ spl5_51 ),
    inference(subsumption_resolution,[],[f944,f602])).

fof(f602,plain,
    ( m1_subset_1(sK2(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_0
    | ~ spl5_3
    | ~ spl5_30
    | ~ spl5_51 ),
    inference(subsumption_resolution,[],[f601,f89])).

fof(f601,plain,
    ( m1_subset_1(sK2(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_pre_topc(sK0)
    | ~ spl5_0
    | ~ spl5_30
    | ~ spl5_51 ),
    inference(subsumption_resolution,[],[f600,f82])).

fof(f600,plain,
    ( ~ l1_pre_topc(sK0)
    | m1_subset_1(sK2(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_pre_topc(sK0)
    | ~ spl5_30
    | ~ spl5_51 ),
    inference(subsumption_resolution,[],[f596,f326])).

fof(f596,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK0)
    | m1_subset_1(sK2(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_pre_topc(sK0)
    | ~ spl5_51 ),
    inference(resolution,[],[f497,f66])).

fof(f960,plain,
    ( ~ spl5_0
    | spl5_3
    | ~ spl5_4
    | ~ spl5_12
    | ~ spl5_22
    | ~ spl5_26
    | ~ spl5_30
    | spl5_51 ),
    inference(avatar_contradiction_clause,[],[f959])).

fof(f959,plain,
    ( $false
    | ~ spl5_0
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_12
    | ~ spl5_22
    | ~ spl5_26
    | ~ spl5_30
    | ~ spl5_51 ),
    inference(subsumption_resolution,[],[f958,f89])).

fof(f958,plain,
    ( v2_pre_topc(sK0)
    | ~ spl5_0
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_12
    | ~ spl5_22
    | ~ spl5_26
    | ~ spl5_30
    | ~ spl5_51 ),
    inference(subsumption_resolution,[],[f957,f82])).

fof(f957,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_pre_topc(sK0)
    | ~ spl5_0
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_12
    | ~ spl5_22
    | ~ spl5_26
    | ~ spl5_30
    | ~ spl5_51 ),
    inference(subsumption_resolution,[],[f956,f497])).

fof(f956,plain,
    ( m1_subset_1(sK1(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK0)
    | v2_pre_topc(sK0)
    | ~ spl5_0
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_12
    | ~ spl5_22
    | ~ spl5_26
    | ~ spl5_30
    | ~ spl5_51 ),
    inference(subsumption_resolution,[],[f955,f326])).

fof(f955,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | m1_subset_1(sK1(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK0)
    | v2_pre_topc(sK0)
    | ~ spl5_0
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_12
    | ~ spl5_22
    | ~ spl5_26
    | ~ spl5_30
    | ~ spl5_51 ),
    inference(subsumption_resolution,[],[f954,f613])).

fof(f954,plain,
    ( ~ r2_hidden(sK2(sK0),u1_pre_topc(sK0))
    | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | m1_subset_1(sK1(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK0)
    | v2_pre_topc(sK0)
    | ~ spl5_0
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_12
    | ~ spl5_22
    | ~ spl5_26
    | ~ spl5_30
    | ~ spl5_51 ),
    inference(subsumption_resolution,[],[f953,f614])).

fof(f953,plain,
    ( ~ r2_hidden(sK3(sK0),u1_pre_topc(sK0))
    | ~ r2_hidden(sK2(sK0),u1_pre_topc(sK0))
    | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | m1_subset_1(sK1(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK0)
    | v2_pre_topc(sK0)
    | ~ spl5_0
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_12
    | ~ spl5_22
    | ~ spl5_26
    | ~ spl5_30
    | ~ spl5_51 ),
    inference(subsumption_resolution,[],[f952,f605])).

fof(f952,plain,
    ( ~ m1_subset_1(sK3(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK3(sK0),u1_pre_topc(sK0))
    | ~ r2_hidden(sK2(sK0),u1_pre_topc(sK0))
    | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | m1_subset_1(sK1(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK0)
    | v2_pre_topc(sK0)
    | ~ spl5_0
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_12
    | ~ spl5_22
    | ~ spl5_26
    | ~ spl5_30
    | ~ spl5_51 ),
    inference(subsumption_resolution,[],[f943,f602])).

fof(f943,plain,
    ( ~ m1_subset_1(sK2(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK3(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK3(sK0),u1_pre_topc(sK0))
    | ~ r2_hidden(sK2(sK0),u1_pre_topc(sK0))
    | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | m1_subset_1(sK1(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK0)
    | v2_pre_topc(sK0)
    | ~ spl5_4
    | ~ spl5_12
    | ~ spl5_22
    | ~ spl5_26 ),
    inference(resolution,[],[f312,f54])).

fof(f941,plain,
    ( ~ spl5_69
    | spl5_61
    | ~ spl5_64 ),
    inference(avatar_split_clause,[],[f739,f626,f590,f939])).

fof(f939,plain,
    ( spl5_69
  <=> u1_struct_0(sK0) != u1_struct_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_69])])).

fof(f590,plain,
    ( spl5_61
  <=> u1_struct_0(sK0) != u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_61])])).

fof(f739,plain,
    ( u1_struct_0(sK0) != u1_struct_0(sK4)
    | ~ spl5_61
    | ~ spl5_64 ),
    inference(superposition,[],[f591,f627])).

fof(f591,plain,
    ( u1_struct_0(sK0) != u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_61 ),
    inference(avatar_component_clause,[],[f590])).

fof(f922,plain,
    ( ~ spl5_67
    | spl5_59
    | ~ spl5_62 ),
    inference(avatar_split_clause,[],[f631,f619,f583,f920])).

fof(f920,plain,
    ( spl5_67
  <=> u1_pre_topc(sK0) != u1_pre_topc(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_67])])).

fof(f583,plain,
    ( spl5_59
  <=> u1_pre_topc(sK0) != u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_59])])).

fof(f631,plain,
    ( u1_pre_topc(sK0) != u1_pre_topc(sK4)
    | ~ spl5_59
    | ~ spl5_62 ),
    inference(superposition,[],[f584,f620])).

fof(f584,plain,
    ( u1_pre_topc(sK0) != u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_59 ),
    inference(avatar_component_clause,[],[f583])).

fof(f628,plain,
    ( spl5_64
    | ~ spl5_52 ),
    inference(avatar_split_clause,[],[f506,f502,f626])).

fof(f502,plain,
    ( spl5_52
  <=> ! [X7,X6] :
        ( g1_pre_topc(X6,X7) != g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))
        | u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = X6 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_52])])).

fof(f506,plain,
    ( u1_struct_0(sK4) = u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_52 ),
    inference(equality_resolution,[],[f503])).

fof(f503,plain,
    ( ! [X6,X7] :
        ( g1_pre_topc(X6,X7) != g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))
        | u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = X6 )
    | ~ spl5_52 ),
    inference(avatar_component_clause,[],[f502])).

fof(f621,plain,
    ( spl5_62
    | ~ spl5_40 ),
    inference(avatar_split_clause,[],[f429,f370,f619])).

fof(f370,plain,
    ( spl5_40
  <=> ! [X3,X2] :
        ( g1_pre_topc(X2,X3) != g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))
        | u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = X3 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_40])])).

fof(f429,plain,
    ( u1_pre_topc(sK4) = u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_40 ),
    inference(equality_resolution,[],[f371])).

fof(f371,plain,
    ( ! [X2,X3] :
        ( g1_pre_topc(X2,X3) != g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))
        | u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = X3 )
    | ~ spl5_40 ),
    inference(avatar_component_clause,[],[f370])).

fof(f610,plain,
    ( ~ spl5_0
    | spl5_3
    | ~ spl5_30
    | spl5_47
    | spl5_51 ),
    inference(avatar_contradiction_clause,[],[f609])).

fof(f609,plain,
    ( $false
    | ~ spl5_0
    | ~ spl5_3
    | ~ spl5_30
    | ~ spl5_47
    | ~ spl5_51 ),
    inference(subsumption_resolution,[],[f608,f89])).

fof(f608,plain,
    ( v2_pre_topc(sK0)
    | ~ spl5_0
    | ~ spl5_30
    | ~ spl5_47
    | ~ spl5_51 ),
    inference(subsumption_resolution,[],[f607,f482])).

fof(f482,plain,
    ( ~ r2_hidden(sK3(sK0),u1_pre_topc(sK0))
    | ~ spl5_47 ),
    inference(avatar_component_clause,[],[f481])).

fof(f595,plain,
    ( ~ spl5_57
    | spl5_60
    | ~ spl5_10
    | ~ spl5_26 ),
    inference(avatar_split_clause,[],[f310,f298,f159,f593,f580])).

fof(f580,plain,
    ( spl5_57
  <=> g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_57])])).

fof(f593,plain,
    ( spl5_60
  <=> u1_struct_0(sK0) = u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_60])])).

fof(f159,plain,
    ( spl5_10
  <=> g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f310,plain,
    ( u1_struct_0(sK0) = u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))
    | ~ spl5_10
    | ~ spl5_26 ),
    inference(backward_demodulation,[],[f303,f301])).

fof(f301,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_10
    | ~ spl5_26 ),
    inference(superposition,[],[f299,f160])).

fof(f160,plain,
    ( g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f159])).

fof(f588,plain,
    ( ~ spl5_57
    | spl5_58
    | ~ spl5_10
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f228,f210,f159,f586,f580])).

fof(f586,plain,
    ( spl5_58
  <=> u1_pre_topc(sK0) = u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_58])])).

fof(f210,plain,
    ( spl5_18
  <=> ! [X3,X2] :
        ( g1_pre_topc(X2,X3) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
        | u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X3 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f228,plain,
    ( u1_pre_topc(sK0) = u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))
    | ~ spl5_10
    | ~ spl5_18 ),
    inference(backward_demodulation,[],[f222,f221])).

fof(f221,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))
    | u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_10
    | ~ spl5_18 ),
    inference(superposition,[],[f211,f160])).

fof(f211,plain,
    ( ! [X2,X3] :
        ( g1_pre_topc(X2,X3) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
        | u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X3 )
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f210])).

fof(f222,plain,
    ( u1_pre_topc(sK0) = u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl5_18 ),
    inference(equality_resolution,[],[f211])).

fof(f564,plain,
    ( ~ spl5_0
    | spl5_3
    | ~ spl5_30
    | spl5_47
    | spl5_49 ),
    inference(avatar_contradiction_clause,[],[f563])).

fof(f563,plain,
    ( $false
    | ~ spl5_0
    | ~ spl5_3
    | ~ spl5_30
    | ~ spl5_47
    | ~ spl5_49 ),
    inference(subsumption_resolution,[],[f562,f89])).

fof(f562,plain,
    ( v2_pre_topc(sK0)
    | ~ spl5_0
    | ~ spl5_30
    | ~ spl5_47
    | ~ spl5_49 ),
    inference(subsumption_resolution,[],[f561,f482])).

fof(f561,plain,
    ( r2_hidden(sK3(sK0),u1_pre_topc(sK0))
    | v2_pre_topc(sK0)
    | ~ spl5_0
    | ~ spl5_30
    | ~ spl5_49 ),
    inference(subsumption_resolution,[],[f560,f82])).

fof(f560,plain,
    ( ~ l1_pre_topc(sK0)
    | r2_hidden(sK3(sK0),u1_pre_topc(sK0))
    | v2_pre_topc(sK0)
    | ~ spl5_30
    | ~ spl5_49 ),
    inference(subsumption_resolution,[],[f558,f326])).

fof(f558,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK0)
    | r2_hidden(sK3(sK0),u1_pre_topc(sK0))
    | v2_pre_topc(sK0)
    | ~ spl5_49 ),
    inference(resolution,[],[f491,f57])).

fof(f524,plain,
    ( spl5_54
    | ~ spl5_44
    | ~ spl5_52 ),
    inference(avatar_split_clause,[],[f508,f502,f473,f522])).

fof(f522,plain,
    ( spl5_54
  <=> m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_54])])).

fof(f473,plain,
    ( spl5_44
  <=> m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_44])])).

fof(f508,plain,
    ( m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ spl5_44
    | ~ spl5_52 ),
    inference(backward_demodulation,[],[f506,f474])).

fof(f474,plain,
    ( m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))
    | ~ spl5_44 ),
    inference(avatar_component_clause,[],[f473])).

fof(f504,plain,
    ( spl5_52
    | ~ spl5_45
    | ~ spl5_10
    | ~ spl5_40 ),
    inference(avatar_split_clause,[],[f432,f370,f159,f470,f502])).

fof(f470,plain,
    ( spl5_45
  <=> ~ m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_45])])).

fof(f432,plain,
    ( ! [X6,X7] :
        ( ~ m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))
        | g1_pre_topc(X6,X7) != g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))
        | u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = X6 )
    | ~ spl5_10
    | ~ spl5_40 ),
    inference(backward_demodulation,[],[f429,f180])).

fof(f180,plain,
    ( ! [X6,X7] :
        ( g1_pre_topc(X6,X7) != g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))
        | ~ m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))
        | u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = X6 )
    | ~ spl5_10 ),
    inference(superposition,[],[f69,f160])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t58_pre_topc.p',free_g1_pre_topc)).

fof(f498,plain,
    ( spl5_46
    | ~ spl5_49
    | ~ spl5_51
    | ~ spl5_0
    | spl5_3
    | ~ spl5_4
    | ~ spl5_12
    | ~ spl5_22
    | ~ spl5_26
    | ~ spl5_30 ),
    inference(avatar_split_clause,[],[f453,f325,f298,f248,f163,f95,f88,f81,f496,f490,f484])).

fof(f453,plain,
    ( ~ m1_subset_1(sK1(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ r1_tarski(sK1(sK0),u1_pre_topc(sK0))
    | r2_hidden(sK3(sK0),u1_pre_topc(sK0))
    | ~ spl5_0
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_12
    | ~ spl5_22
    | ~ spl5_26
    | ~ spl5_30 ),
    inference(subsumption_resolution,[],[f452,f89])).

fof(f452,plain,
    ( ~ m1_subset_1(sK1(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ r1_tarski(sK1(sK0),u1_pre_topc(sK0))
    | r2_hidden(sK3(sK0),u1_pre_topc(sK0))
    | v2_pre_topc(sK0)
    | ~ spl5_0
    | ~ spl5_4
    | ~ spl5_12
    | ~ spl5_22
    | ~ spl5_26
    | ~ spl5_30 ),
    inference(subsumption_resolution,[],[f451,f82])).

fof(f451,plain,
    ( ~ m1_subset_1(sK1(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ r1_tarski(sK1(sK0),u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK0)
    | r2_hidden(sK3(sK0),u1_pre_topc(sK0))
    | v2_pre_topc(sK0)
    | ~ spl5_4
    | ~ spl5_12
    | ~ spl5_22
    | ~ spl5_26
    | ~ spl5_30 ),
    inference(subsumption_resolution,[],[f443,f326])).

fof(f443,plain,
    ( ~ m1_subset_1(sK1(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ r1_tarski(sK1(sK0),u1_pre_topc(sK0))
    | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK0)
    | r2_hidden(sK3(sK0),u1_pre_topc(sK0))
    | v2_pre_topc(sK0)
    | ~ spl5_4
    | ~ spl5_12
    | ~ spl5_22
    | ~ spl5_26 ),
    inference(resolution,[],[f313,f61])).

fof(f475,plain,
    ( spl5_44
    | ~ spl5_38
    | ~ spl5_40 ),
    inference(avatar_split_clause,[],[f433,f370,f364,f473])).

fof(f364,plain,
    ( spl5_38
  <=> m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).

fof(f433,plain,
    ( m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))
    | ~ spl5_38
    | ~ spl5_40 ),
    inference(backward_demodulation,[],[f429,f365])).

fof(f365,plain,
    ( m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))
    | ~ spl5_38 ),
    inference(avatar_component_clause,[],[f364])).

fof(f440,plain,
    ( spl5_42
    | ~ spl5_10
    | ~ spl5_40 ),
    inference(avatar_split_clause,[],[f430,f370,f159,f438])).

fof(f438,plain,
    ( spl5_42
  <=> g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_42])])).

fof(f430,plain,
    ( g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(sK4))
    | ~ spl5_10
    | ~ spl5_40 ),
    inference(backward_demodulation,[],[f429,f160])).

fof(f375,plain,
    ( ~ spl5_32
    | spl5_39 ),
    inference(avatar_contradiction_clause,[],[f374])).

fof(f374,plain,
    ( $false
    | ~ spl5_32
    | ~ spl5_39 ),
    inference(subsumption_resolution,[],[f373,f332])).

fof(f373,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_39 ),
    inference(resolution,[],[f368,f74])).

fof(f368,plain,
    ( ~ m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))
    | ~ spl5_39 ),
    inference(avatar_component_clause,[],[f367])).

fof(f367,plain,
    ( spl5_39
  <=> ~ m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_39])])).

fof(f372,plain,
    ( ~ spl5_39
    | spl5_40
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f178,f159,f370,f367])).

fof(f178,plain,
    ( ! [X2,X3] :
        ( g1_pre_topc(X2,X3) != g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))
        | ~ m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))
        | u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = X3 )
    | ~ spl5_10 ),
    inference(superposition,[],[f70,f160])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | X1 = X3 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f360,plain,
    ( spl5_36
    | ~ spl5_26 ),
    inference(avatar_split_clause,[],[f303,f298,f358])).

fof(f358,plain,
    ( spl5_36
  <=> u1_struct_0(sK0) = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).

fof(f345,plain,
    ( ~ spl5_6
    | spl5_33 ),
    inference(avatar_contradiction_clause,[],[f344])).

fof(f344,plain,
    ( $false
    | ~ spl5_6
    | ~ spl5_33 ),
    inference(subsumption_resolution,[],[f343,f103])).

fof(f343,plain,
    ( ~ l1_pre_topc(sK4)
    | ~ spl5_33 ),
    inference(resolution,[],[f335,f105])).

fof(f335,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_33 ),
    inference(avatar_component_clause,[],[f334])).

fof(f334,plain,
    ( spl5_33
  <=> ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).

fof(f342,plain,
    ( ~ spl5_33
    | spl5_34
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f175,f159,f340,f334])).

fof(f340,plain,
    ( spl5_34
  <=> v1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).

fof(f175,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl5_10 ),
    inference(superposition,[],[f106,f160])).

fof(f327,plain,
    ( spl5_30
    | ~ spl5_4
    | ~ spl5_12
    | ~ spl5_22
    | ~ spl5_26 ),
    inference(avatar_split_clause,[],[f309,f298,f248,f163,f95,f325])).

fof(f309,plain,
    ( r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | ~ spl5_4
    | ~ spl5_12
    | ~ spl5_22
    | ~ spl5_26 ),
    inference(backward_demodulation,[],[f303,f292])).

fof(f292,plain,
    ( r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(sK0))
    | ~ spl5_4
    | ~ spl5_12
    | ~ spl5_22 ),
    inference(subsumption_resolution,[],[f291,f96])).

fof(f291,plain,
    ( r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(sK0))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl5_12
    | ~ spl5_22 ),
    inference(subsumption_resolution,[],[f276,f164])).

fof(f276,plain,
    ( r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(sK0))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl5_22 ),
    inference(superposition,[],[f68,f249])).

fof(f320,plain,
    ( spl5_28
    | ~ spl5_24
    | ~ spl5_26 ),
    inference(avatar_split_clause,[],[f306,f298,f255,f318])).

fof(f318,plain,
    ( spl5_28
  <=> m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).

fof(f255,plain,
    ( spl5_24
  <=> m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f306,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl5_24
    | ~ spl5_26 ),
    inference(backward_demodulation,[],[f303,f256])).

fof(f256,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
    | ~ spl5_24 ),
    inference(avatar_component_clause,[],[f255])).

fof(f300,plain,
    ( spl5_26
    | ~ spl5_25
    | ~ spl5_8
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f225,f210,f146,f252,f298])).

fof(f252,plain,
    ( spl5_25
  <=> ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f146,plain,
    ( spl5_8
  <=> g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f225,plain,
    ( ! [X6,X7] :
        ( ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
        | g1_pre_topc(X6,X7) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
        | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X6 )
    | ~ spl5_8
    | ~ spl5_18 ),
    inference(backward_demodulation,[],[f222,f154])).

fof(f154,plain,
    ( ! [X6,X7] :
        ( g1_pre_topc(X6,X7) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
        | ~ m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
        | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X6 )
    | ~ spl5_8 ),
    inference(superposition,[],[f69,f147])).

fof(f147,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f146])).

fof(f257,plain,
    ( spl5_24
    | ~ spl5_16
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f227,f210,f204,f255])).

fof(f204,plain,
    ( spl5_16
  <=> m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f227,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
    | ~ spl5_16
    | ~ spl5_18 ),
    inference(backward_demodulation,[],[f222,f205])).

fof(f205,plain,
    ( m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f204])).

fof(f250,plain,
    ( spl5_22
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f222,f210,f248])).

fof(f235,plain,
    ( spl5_20
    | ~ spl5_8
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f223,f210,f146,f233])).

fof(f233,plain,
    ( spl5_20
  <=> g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f223,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(sK0))
    | ~ spl5_8
    | ~ spl5_18 ),
    inference(backward_demodulation,[],[f222,f147])).

fof(f215,plain,
    ( ~ spl5_12
    | spl5_17 ),
    inference(avatar_contradiction_clause,[],[f214])).

fof(f214,plain,
    ( $false
    | ~ spl5_12
    | ~ spl5_17 ),
    inference(subsumption_resolution,[],[f213,f164])).

fof(f213,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl5_17 ),
    inference(resolution,[],[f208,f74])).

fof(f208,plain,
    ( ~ m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
    | ~ spl5_17 ),
    inference(avatar_component_clause,[],[f207])).

fof(f207,plain,
    ( spl5_17
  <=> ~ m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f212,plain,
    ( ~ spl5_17
    | spl5_18
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f152,f146,f210,f207])).

fof(f152,plain,
    ( ! [X2,X3] :
        ( g1_pre_topc(X2,X3) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
        | ~ m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
        | u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X3 )
    | ~ spl5_8 ),
    inference(superposition,[],[f70,f147])).

fof(f190,plain,
    ( ~ spl5_0
    | spl5_13 ),
    inference(avatar_contradiction_clause,[],[f189])).

fof(f189,plain,
    ( $false
    | ~ spl5_0
    | ~ spl5_13 ),
    inference(subsumption_resolution,[],[f188,f82])).

fof(f188,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl5_13 ),
    inference(resolution,[],[f167,f105])).

fof(f167,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f166])).

fof(f166,plain,
    ( spl5_13
  <=> ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f174,plain,
    ( ~ spl5_13
    | spl5_14
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f149,f146,f172,f166])).

fof(f172,plain,
    ( spl5_14
  <=> v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f149,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl5_8 ),
    inference(superposition,[],[f106,f147])).

fof(f161,plain,
    ( spl5_10
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f138,f102,f159])).

fof(f138,plain,
    ( g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ spl5_6 ),
    inference(resolution,[],[f110,f103])).

fof(f148,plain,
    ( spl5_8
    | ~ spl5_0 ),
    inference(avatar_split_clause,[],[f137,f81,f146])).

fof(f137,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl5_0 ),
    inference(resolution,[],[f110,f82])).

fof(f104,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f75,f102])).

fof(f75,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ? [X0] : l1_pre_topc(X0) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t58_pre_topc.p',existence_l1_pre_topc)).

fof(f97,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f49,f95])).

fof(f49,plain,(
    v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ? [X0] :
      ( ~ v2_pre_topc(X0)
      & v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ? [X0] :
      ( ~ v2_pre_topc(X0)
      & v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
         => v2_pre_topc(X0) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
       => v2_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t58_pre_topc.p',t58_pre_topc)).

fof(f90,plain,(
    ~ spl5_3 ),
    inference(avatar_split_clause,[],[f50,f88])).

fof(f50,plain,(
    ~ v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f83,plain,(
    spl5_0 ),
    inference(avatar_split_clause,[],[f48,f81])).

fof(f48,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f39])).
%------------------------------------------------------------------------------
