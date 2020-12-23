%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1726+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:25 EST 2020

% Result     : Theorem 4.66s
% Output     : Refutation 5.02s
% Verified   : 
% Statistics : Number of formulae       :  641 (2166 expanded)
%              Number of leaves         :  177 (1105 expanded)
%              Depth                    :    9
%              Number of atoms          : 4570 (15582 expanded)
%              Number of equality atoms :    4 (  48 expanded)
%              Maximal formula depth    :   20 (   9 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1534,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f87,f96,f101,f106,f111,f116,f121,f126,f131,f136,f141,f146,f151,f156,f161,f166,f173,f178,f195,f196,f197,f206,f207,f208,f214,f220,f226,f232,f239,f253,f261,f263,f308,f312,f314,f316,f328,f332,f336,f337,f343,f349,f350,f352,f358,f372,f376,f389,f395,f399,f401,f414,f418,f422,f429,f433,f440,f465,f469,f473,f483,f501,f506,f510,f514,f527,f540,f544,f548,f555,f559,f564,f577,f581,f586,f594,f598,f603,f616,f629,f633,f646,f650,f651,f664,f668,f675,f679,f706,f710,f714,f715,f741,f745,f749,f770,f774,f778,f792,f796,f823,f827,f850,f854,f858,f859,f901,f905,f909,f927,f934,f949,f965,f969,f974,f987,f1021,f1022,f1046,f1050,f1054,f1059,f1125,f1129,f1133,f1134,f1135,f1136,f1165,f1171,f1172,f1173,f1174,f1175,f1208,f1212,f1216,f1220,f1224,f1261,f1262,f1283,f1287,f1307,f1311,f1315,f1332,f1374,f1378,f1421,f1426,f1443,f1454,f1458,f1477,f1481,f1485,f1493,f1497,f1502,f1511,f1515,f1519,f1523,f1524,f1528,f1532,f1533])).

fof(f1533,plain,
    ( spl7_17
    | ~ spl7_16
    | ~ spl7_15
    | spl7_10
    | ~ spl7_9
    | spl7_12
    | ~ spl7_11
    | spl7_8
    | ~ spl7_7
    | spl7_152
    | ~ spl7_5
    | ~ spl7_77 ),
    inference(avatar_split_clause,[],[f1444,f583,f98,f1499,f108,f113,f128,f133,f118,f123,f148,f153,f158])).

fof(f158,plain,
    ( spl7_17
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f153,plain,
    ( spl7_16
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f148,plain,
    ( spl7_15
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f123,plain,
    ( spl7_10
  <=> v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f118,plain,
    ( spl7_9
  <=> m1_pre_topc(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f133,plain,
    ( spl7_12
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f128,plain,
    ( spl7_11
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f113,plain,
    ( spl7_8
  <=> v2_struct_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f108,plain,
    ( spl7_7
  <=> m1_pre_topc(sK4,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f1499,plain,
    ( spl7_152
  <=> r1_tsep_1(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_152])])).

fof(f98,plain,
    ( spl7_5
  <=> m1_pre_topc(sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f583,plain,
    ( spl7_77
  <=> r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_77])])).

fof(f1444,plain,
    ( ~ m1_pre_topc(sK3,sK4)
    | r1_tsep_1(sK3,sK2)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl7_77 ),
    inference(resolution,[],[f63,f585])).

fof(f585,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),sK3)
    | ~ spl7_77 ),
    inference(avatar_component_clause,[],[f583])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tsep_1(k2_tsep_1(X0,X2,X3),X1)
      | ~ m1_pre_topc(X1,X3)
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( ( ~ r1_tsep_1(k2_tsep_1(X0,X3,X1),X2)
                        & ~ r1_tsep_1(k2_tsep_1(X0,X1,X3),X2) )
                      | ~ m1_pre_topc(X2,X3) )
                    & ( ( ~ r1_tsep_1(k2_tsep_1(X0,X2,X3),X1)
                        & ~ r1_tsep_1(k2_tsep_1(X0,X3,X2),X1) )
                      | ~ m1_pre_topc(X1,X3) ) )
                  | r1_tsep_1(X1,X2)
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( ( ~ r1_tsep_1(k2_tsep_1(X0,X3,X1),X2)
                        & ~ r1_tsep_1(k2_tsep_1(X0,X1,X3),X2) )
                      | ~ m1_pre_topc(X2,X3) )
                    & ( ( ~ r1_tsep_1(k2_tsep_1(X0,X2,X3),X1)
                        & ~ r1_tsep_1(k2_tsep_1(X0,X3,X2),X1) )
                      | ~ m1_pre_topc(X1,X3) ) )
                  | r1_tsep_1(X1,X2)
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
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
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ( ~ r1_tsep_1(X1,X2)
                   => ( ( m1_pre_topc(X2,X3)
                       => ( ~ r1_tsep_1(k2_tsep_1(X0,X3,X1),X2)
                          & ~ r1_tsep_1(k2_tsep_1(X0,X1,X3),X2) ) )
                      & ( m1_pre_topc(X1,X3)
                       => ( ~ r1_tsep_1(k2_tsep_1(X0,X2,X3),X1)
                          & ~ r1_tsep_1(k2_tsep_1(X0,X3,X2),X1) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_tmap_1)).

fof(f1532,plain,
    ( spl7_17
    | ~ spl7_16
    | ~ spl7_15
    | spl7_12
    | ~ spl7_11
    | spl7_8
    | ~ spl7_7
    | spl7_158
    | ~ spl7_125 ),
    inference(avatar_split_clause,[],[f1450,f1123,f1530,f108,f113,f128,f133,f148,f153,f158])).

fof(f1530,plain,
    ( spl7_158
  <=> ! [X0] :
        ( ~ m1_pre_topc(X0,sK4)
        | ~ m1_pre_topc(X0,sK3)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | r1_tsep_1(X0,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_158])])).

fof(f1123,plain,
    ( spl7_125
  <=> ! [X0] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK3)
        | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X0)
        | ~ m1_pre_topc(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_125])])).

fof(f1450,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK4)
        | r1_tsep_1(X0,sK2)
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(X0,sK3) )
    | ~ spl7_125 ),
    inference(duplicate_literal_removal,[],[f1445])).

fof(f1445,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK4)
        | r1_tsep_1(X0,sK2)
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(X0,sK3)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0) )
    | ~ spl7_125 ),
    inference(resolution,[],[f63,f1124])).

fof(f1124,plain,
    ( ! [X0] :
        ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X0)
        | ~ m1_pre_topc(X0,sK3)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0) )
    | ~ spl7_125 ),
    inference(avatar_component_clause,[],[f1123])).

fof(f1528,plain,
    ( spl7_17
    | ~ spl7_16
    | ~ spl7_15
    | spl7_12
    | ~ spl7_11
    | spl7_8
    | ~ spl7_7
    | spl7_157
    | ~ spl7_92 ),
    inference(avatar_split_clause,[],[f1449,f704,f1526,f108,f113,f128,f133,f148,f153,f158])).

fof(f1526,plain,
    ( spl7_157
  <=> ! [X1] :
        ( ~ m1_pre_topc(X1,sK4)
        | ~ m1_pre_topc(X1,sK1)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | r1_tsep_1(X1,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_157])])).

fof(f704,plain,
    ( spl7_92
  <=> ! [X0] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK1)
        | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X0)
        | ~ m1_pre_topc(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_92])])).

fof(f1449,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(X1,sK4)
        | r1_tsep_1(X1,sK2)
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(X1,sK1) )
    | ~ spl7_92 ),
    inference(duplicate_literal_removal,[],[f1446])).

fof(f1446,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(X1,sK4)
        | r1_tsep_1(X1,sK2)
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(X1,sK1)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0) )
    | ~ spl7_92 ),
    inference(resolution,[],[f63,f705])).

fof(f705,plain,
    ( ! [X0] :
        ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X0)
        | ~ m1_pre_topc(X0,sK1)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0) )
    | ~ spl7_92 ),
    inference(avatar_component_clause,[],[f704])).

fof(f1524,plain,
    ( ~ spl7_28
    | ~ spl7_25
    | spl7_1
    | ~ spl7_152 ),
    inference(avatar_split_clause,[],[f1507,f1499,f80,f211,f229])).

fof(f229,plain,
    ( spl7_28
  <=> l1_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).

fof(f211,plain,
    ( spl7_25
  <=> l1_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).

fof(f80,plain,
    ( spl7_1
  <=> r1_tsep_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f1507,plain,
    ( r1_tsep_1(sK2,sK3)
    | ~ l1_struct_0(sK2)
    | ~ l1_struct_0(sK3)
    | ~ spl7_152 ),
    inference(resolution,[],[f1501,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ r1_tsep_1(X0,X1)
      | r1_tsep_1(X1,X0)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( l1_struct_0(X1)
        & l1_struct_0(X0) )
     => ( r1_tsep_1(X0,X1)
       => r1_tsep_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

fof(f1501,plain,
    ( r1_tsep_1(sK3,sK2)
    | ~ spl7_152 ),
    inference(avatar_component_clause,[],[f1499])).

fof(f1523,plain,
    ( spl7_10
    | spl7_12
    | spl7_156
    | ~ spl7_152 ),
    inference(avatar_split_clause,[],[f1506,f1499,f1521,f133,f123])).

fof(f1521,plain,
    ( spl7_156
  <=> ! [X7,X6] :
        ( r1_tsep_1(X6,sK2)
        | v2_struct_0(X7)
        | ~ v2_pre_topc(X7)
        | ~ l1_pre_topc(X7)
        | v2_struct_0(X6)
        | ~ m1_pre_topc(X6,X7)
        | ~ m1_pre_topc(sK2,X7)
        | ~ m1_pre_topc(sK3,X7)
        | ~ m1_pre_topc(X6,sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_156])])).

fof(f1506,plain,
    ( ! [X6,X7] :
        ( r1_tsep_1(X6,sK2)
        | ~ m1_pre_topc(X6,sK3)
        | ~ m1_pre_topc(sK2,X7)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(sK3,X7)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(X6,X7)
        | v2_struct_0(X6)
        | ~ l1_pre_topc(X7)
        | ~ v2_pre_topc(X7)
        | v2_struct_0(X7) )
    | ~ spl7_152 ),
    inference(resolution,[],[f1501,f66])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tsep_1(X2,X3)
      | r1_tsep_1(X1,X3)
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ~ r1_tsep_1(X3,X2)
                    & ~ r1_tsep_1(X2,X3) )
                  | ( r1_tsep_1(X3,X1)
                    & r1_tsep_1(X1,X3) )
                  | ~ m1_pre_topc(X1,X2)
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
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
                  ( ( ~ r1_tsep_1(X3,X2)
                    & ~ r1_tsep_1(X2,X3) )
                  | ( r1_tsep_1(X3,X1)
                    & r1_tsep_1(X1,X3) )
                  | ~ m1_pre_topc(X1,X2)
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
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
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ( m1_pre_topc(X1,X2)
                   => ( ( ~ r1_tsep_1(X3,X2)
                        & ~ r1_tsep_1(X2,X3) )
                      | ( r1_tsep_1(X3,X1)
                        & r1_tsep_1(X1,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_tmap_1)).

fof(f1519,plain,
    ( spl7_10
    | spl7_12
    | spl7_155
    | ~ spl7_152 ),
    inference(avatar_split_clause,[],[f1505,f1499,f1517,f133,f123])).

fof(f1517,plain,
    ( spl7_155
  <=> ! [X5,X4] :
        ( r1_tsep_1(sK2,X4)
        | v2_struct_0(X5)
        | ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X5)
        | v2_struct_0(X4)
        | ~ m1_pre_topc(X4,X5)
        | ~ m1_pre_topc(sK2,X5)
        | ~ m1_pre_topc(sK3,X5)
        | ~ m1_pre_topc(X4,sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_155])])).

fof(f1505,plain,
    ( ! [X4,X5] :
        ( r1_tsep_1(sK2,X4)
        | ~ m1_pre_topc(X4,sK3)
        | ~ m1_pre_topc(sK2,X5)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(sK3,X5)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(X4,X5)
        | v2_struct_0(X4)
        | ~ l1_pre_topc(X5)
        | ~ v2_pre_topc(X5)
        | v2_struct_0(X5) )
    | ~ spl7_152 ),
    inference(resolution,[],[f1501,f67])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tsep_1(X2,X3)
      | r1_tsep_1(X3,X1)
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f1515,plain,
    ( spl7_12
    | spl7_10
    | spl7_154
    | ~ spl7_152 ),
    inference(avatar_split_clause,[],[f1504,f1499,f1513,f123,f133])).

fof(f1513,plain,
    ( spl7_154
  <=> ! [X3,X2] :
        ( r1_tsep_1(X2,sK3)
        | v2_struct_0(X3)
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X3)
        | ~ m1_pre_topc(sK3,X3)
        | ~ m1_pre_topc(sK2,X3)
        | ~ m1_pre_topc(X2,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_154])])).

fof(f1504,plain,
    ( ! [X2,X3] :
        ( r1_tsep_1(X2,sK3)
        | ~ m1_pre_topc(X2,sK2)
        | ~ m1_pre_topc(sK3,X3)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK2,X3)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(X2,X3)
        | v2_struct_0(X2)
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(X3)
        | v2_struct_0(X3) )
    | ~ spl7_152 ),
    inference(resolution,[],[f1501,f68])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tsep_1(X3,X2)
      | r1_tsep_1(X1,X3)
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f1511,plain,
    ( spl7_12
    | spl7_10
    | spl7_153
    | ~ spl7_152 ),
    inference(avatar_split_clause,[],[f1503,f1499,f1509,f123,f133])).

fof(f1509,plain,
    ( spl7_153
  <=> ! [X1,X0] :
        ( r1_tsep_1(sK3,X0)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,X1)
        | ~ m1_pre_topc(sK3,X1)
        | ~ m1_pre_topc(sK2,X1)
        | ~ m1_pre_topc(X0,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_153])])).

fof(f1503,plain,
    ( ! [X0,X1] :
        ( r1_tsep_1(sK3,X0)
        | ~ m1_pre_topc(X0,sK2)
        | ~ m1_pre_topc(sK3,X1)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK2,X1)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(X0,X1)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl7_152 ),
    inference(resolution,[],[f1501,f69])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tsep_1(X3,X2)
      | r1_tsep_1(X3,X1)
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f1502,plain,
    ( ~ spl7_9
    | spl7_152
    | spl7_10
    | ~ spl7_5
    | ~ spl7_147 ),
    inference(avatar_split_clause,[],[f1488,f1475,f98,f123,f1499,f118])).

fof(f1475,plain,
    ( spl7_147
  <=> ! [X0] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK4)
        | r1_tsep_1(X0,sK2)
        | ~ m1_pre_topc(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_147])])).

fof(f1488,plain,
    ( v2_struct_0(sK3)
    | r1_tsep_1(sK3,sK2)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ spl7_5
    | ~ spl7_147 ),
    inference(resolution,[],[f1476,f100])).

fof(f100,plain,
    ( m1_pre_topc(sK3,sK4)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f98])).

fof(f1476,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK4)
        | v2_struct_0(X0)
        | r1_tsep_1(X0,sK2)
        | ~ m1_pre_topc(X0,sK0) )
    | ~ spl7_147 ),
    inference(avatar_component_clause,[],[f1475])).

fof(f1497,plain,
    ( spl7_8
    | ~ spl7_23
    | spl7_151
    | ~ spl7_147 ),
    inference(avatar_split_clause,[],[f1487,f1475,f1495,f199,f113])).

fof(f199,plain,
    ( spl7_23
  <=> l1_pre_topc(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).

fof(f1495,plain,
    ( spl7_151
  <=> ! [X3,X2] :
        ( v2_struct_0(k2_tsep_1(sK4,X2,X3))
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,sK4)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,sK4)
        | ~ m1_pre_topc(k2_tsep_1(sK4,X2,X3),sK0)
        | r1_tsep_1(k2_tsep_1(sK4,X2,X3),sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_151])])).

fof(f1487,plain,
    ( ! [X2,X3] :
        ( v2_struct_0(k2_tsep_1(sK4,X2,X3))
        | r1_tsep_1(k2_tsep_1(sK4,X2,X3),sK2)
        | ~ m1_pre_topc(k2_tsep_1(sK4,X2,X3),sK0)
        | ~ m1_pre_topc(X3,sK4)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X2,sK4)
        | v2_struct_0(X2)
        | ~ l1_pre_topc(sK4)
        | v2_struct_0(sK4) )
    | ~ spl7_147 ),
    inference(resolution,[],[f1476,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k2_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k2_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k2_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tsep_1)).

fof(f1493,plain,
    ( spl7_8
    | ~ spl7_23
    | spl7_150
    | ~ spl7_147 ),
    inference(avatar_split_clause,[],[f1486,f1475,f1491,f199,f113])).

fof(f1491,plain,
    ( spl7_150
  <=> ! [X1,X0] :
        ( v2_struct_0(k1_tsep_1(sK4,X0,X1))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK4)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK4)
        | ~ m1_pre_topc(k1_tsep_1(sK4,X0,X1),sK0)
        | r1_tsep_1(k1_tsep_1(sK4,X0,X1),sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_150])])).

fof(f1486,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(k1_tsep_1(sK4,X0,X1))
        | r1_tsep_1(k1_tsep_1(sK4,X0,X1),sK2)
        | ~ m1_pre_topc(k1_tsep_1(sK4,X0,X1),sK0)
        | ~ m1_pre_topc(X1,sK4)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X0,sK4)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK4)
        | v2_struct_0(sK4) )
    | ~ spl7_147 ),
    inference(resolution,[],[f1476,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tsep_1)).

fof(f1485,plain,
    ( spl7_8
    | spl7_149
    | ~ spl7_42 ),
    inference(avatar_split_clause,[],[f1473,f347,f1483,f113])).

fof(f1483,plain,
    ( spl7_149
  <=> ! [X5,X4,X6] :
        ( v2_struct_0(k1_tsep_1(X4,X5,sK4))
        | v2_struct_0(X4)
        | ~ v2_pre_topc(X4)
        | ~ l1_pre_topc(X4)
        | ~ m1_pre_topc(sK4,X4)
        | v2_struct_0(X5)
        | ~ m1_pre_topc(X5,X4)
        | ~ m1_pre_topc(X6,sK4)
        | r1_tsep_1(X6,sK2)
        | ~ m1_pre_topc(sK2,k1_tsep_1(X4,X5,sK4))
        | ~ m1_pre_topc(X6,k1_tsep_1(X4,X5,sK4))
        | v2_struct_0(X6)
        | ~ l1_pre_topc(k1_tsep_1(X4,X5,sK4))
        | ~ v2_pre_topc(k1_tsep_1(X4,X5,sK4)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_149])])).

fof(f347,plain,
    ( spl7_42
  <=> ! [X1,X0] :
        ( r1_tsep_1(X0,sK2)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,X1)
        | ~ m1_pre_topc(sK2,X1)
        | ~ m1_pre_topc(sK4,X1)
        | ~ m1_pre_topc(X0,sK4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_42])])).

fof(f1473,plain,
    ( ! [X6,X4,X5] :
        ( v2_struct_0(k1_tsep_1(X4,X5,sK4))
        | ~ v2_pre_topc(k1_tsep_1(X4,X5,sK4))
        | ~ l1_pre_topc(k1_tsep_1(X4,X5,sK4))
        | v2_struct_0(X6)
        | ~ m1_pre_topc(X6,k1_tsep_1(X4,X5,sK4))
        | ~ m1_pre_topc(sK2,k1_tsep_1(X4,X5,sK4))
        | r1_tsep_1(X6,sK2)
        | ~ m1_pre_topc(X6,sK4)
        | ~ m1_pre_topc(X5,X4)
        | v2_struct_0(X5)
        | ~ m1_pre_topc(sK4,X4)
        | v2_struct_0(sK4)
        | ~ l1_pre_topc(X4)
        | ~ v2_pre_topc(X4)
        | v2_struct_0(X4) )
    | ~ spl7_42 ),
    inference(resolution,[],[f348,f289])).

fof(f289,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X1,k1_tsep_1(X0,X2,X1))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f266])).

fof(f266,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X1,k1_tsep_1(X0,X2,X1))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(superposition,[],[f61,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k1_tsep_1)).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X1,k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X1,k1_tsep_1(X0,X1,X2))
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X1,k1_tsep_1(X0,X1,X2))
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_tsep_1)).

fof(f348,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(sK4,X1)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,X1)
        | ~ m1_pre_topc(sK2,X1)
        | r1_tsep_1(X0,sK2)
        | ~ m1_pre_topc(X0,sK4) )
    | ~ spl7_42 ),
    inference(avatar_component_clause,[],[f347])).

fof(f1481,plain,
    ( spl7_8
    | spl7_148
    | ~ spl7_42 ),
    inference(avatar_split_clause,[],[f1472,f347,f1479,f113])).

fof(f1479,plain,
    ( spl7_148
  <=> ! [X1,X3,X2] :
        ( v2_struct_0(k1_tsep_1(X1,sK4,X2))
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ m1_pre_topc(sK4,X1)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X1)
        | ~ m1_pre_topc(X3,sK4)
        | r1_tsep_1(X3,sK2)
        | ~ m1_pre_topc(sK2,k1_tsep_1(X1,sK4,X2))
        | ~ m1_pre_topc(X3,k1_tsep_1(X1,sK4,X2))
        | v2_struct_0(X3)
        | ~ l1_pre_topc(k1_tsep_1(X1,sK4,X2))
        | ~ v2_pre_topc(k1_tsep_1(X1,sK4,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_148])])).

fof(f1472,plain,
    ( ! [X2,X3,X1] :
        ( v2_struct_0(k1_tsep_1(X1,sK4,X2))
        | ~ v2_pre_topc(k1_tsep_1(X1,sK4,X2))
        | ~ l1_pre_topc(k1_tsep_1(X1,sK4,X2))
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,k1_tsep_1(X1,sK4,X2))
        | ~ m1_pre_topc(sK2,k1_tsep_1(X1,sK4,X2))
        | r1_tsep_1(X3,sK2)
        | ~ m1_pre_topc(X3,sK4)
        | ~ m1_pre_topc(X2,X1)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(sK4,X1)
        | v2_struct_0(sK4)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl7_42 ),
    inference(resolution,[],[f348,f61])).

fof(f1477,plain,
    ( ~ spl7_11
    | spl7_147
    | ~ spl7_15
    | ~ spl7_16
    | spl7_17
    | ~ spl7_7
    | ~ spl7_42 ),
    inference(avatar_split_clause,[],[f1471,f347,f108,f158,f153,f148,f1475,f128])).

fof(f1471,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(sK2,sK0)
        | r1_tsep_1(X0,sK2)
        | ~ m1_pre_topc(X0,sK4) )
    | ~ spl7_7
    | ~ spl7_42 ),
    inference(resolution,[],[f348,f110])).

fof(f110,plain,
    ( m1_pre_topc(sK4,sK0)
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f108])).

fof(f1458,plain,
    ( spl7_33
    | spl7_146
    | ~ spl7_108 ),
    inference(avatar_split_clause,[],[f1448,f899,f1456,f298])).

fof(f298,plain,
    ( spl7_33
  <=> v2_struct_0(k2_tsep_1(sK0,sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_33])])).

fof(f1456,plain,
    ( spl7_146
  <=> ! [X5,X7,X6] :
        ( ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X5)
        | ~ m1_pre_topc(k2_tsep_1(X7,X6,X5),sK0)
        | v2_struct_0(k2_tsep_1(X7,X6,X5))
        | ~ m1_pre_topc(k2_tsep_1(X7,X6,X5),sK1)
        | v2_struct_0(X7)
        | ~ v2_pre_topc(X7)
        | ~ l1_pre_topc(X7)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X7)
        | v2_struct_0(X6)
        | v2_struct_0(X5)
        | ~ m1_pre_topc(X5,X7)
        | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X6)
        | ~ m1_pre_topc(X6,X7) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_146])])).

fof(f899,plain,
    ( spl7_108
  <=> ! [X0] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK1)
        | r1_tsep_1(X0,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_108])])).

fof(f1448,plain,
    ( ! [X6,X7,X5] :
        ( ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X5)
        | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X6)
        | ~ m1_pre_topc(X5,X7)
        | v2_struct_0(X5)
        | ~ m1_pre_topc(X6,X7)
        | v2_struct_0(X6)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X7)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ l1_pre_topc(X7)
        | ~ v2_pre_topc(X7)
        | v2_struct_0(X7)
        | ~ m1_pre_topc(k2_tsep_1(X7,X6,X5),sK1)
        | v2_struct_0(k2_tsep_1(X7,X6,X5))
        | ~ m1_pre_topc(k2_tsep_1(X7,X6,X5),sK0) )
    | ~ spl7_108 ),
    inference(resolution,[],[f63,f900])).

fof(f900,plain,
    ( ! [X0] :
        ( r1_tsep_1(X0,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X0,sK1)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0) )
    | ~ spl7_108 ),
    inference(avatar_component_clause,[],[f899])).

fof(f1454,plain,
    ( spl7_33
    | spl7_145
    | ~ spl7_133 ),
    inference(avatar_split_clause,[],[f1447,f1222,f1452,f298])).

fof(f1452,plain,
    ( spl7_145
  <=> ! [X3,X2,X4] :
        ( ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X2)
        | v2_struct_0(k2_tsep_1(X4,X3,X2))
        | ~ m1_pre_topc(k2_tsep_1(X4,X3,X2),sK0)
        | ~ m1_pre_topc(k2_tsep_1(X4,X3,X2),sK3)
        | ~ l1_struct_0(k2_tsep_1(X4,X3,X2))
        | v2_struct_0(X4)
        | ~ v2_pre_topc(X4)
        | ~ l1_pre_topc(X4)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X4)
        | v2_struct_0(X3)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X4)
        | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X3)
        | ~ m1_pre_topc(X3,X4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_145])])).

fof(f1222,plain,
    ( spl7_133
  <=> ! [X12] :
        ( ~ m1_pre_topc(X12,sK3)
        | ~ l1_struct_0(X12)
        | r1_tsep_1(X12,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X12,sK0)
        | v2_struct_0(X12) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_133])])).

fof(f1447,plain,
    ( ! [X4,X2,X3] :
        ( ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X2)
        | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X3)
        | ~ m1_pre_topc(X2,X4)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X3,X4)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X4)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ l1_pre_topc(X4)
        | ~ v2_pre_topc(X4)
        | v2_struct_0(X4)
        | ~ l1_struct_0(k2_tsep_1(X4,X3,X2))
        | ~ m1_pre_topc(k2_tsep_1(X4,X3,X2),sK3)
        | ~ m1_pre_topc(k2_tsep_1(X4,X3,X2),sK0)
        | v2_struct_0(k2_tsep_1(X4,X3,X2)) )
    | ~ spl7_133 ),
    inference(resolution,[],[f63,f1223])).

fof(f1223,plain,
    ( ! [X12] :
        ( r1_tsep_1(X12,k2_tsep_1(sK0,sK2,sK4))
        | ~ l1_struct_0(X12)
        | ~ m1_pre_topc(X12,sK3)
        | ~ m1_pre_topc(X12,sK0)
        | v2_struct_0(X12) )
    | ~ spl7_133 ),
    inference(avatar_component_clause,[],[f1222])).

fof(f1443,plain,
    ( spl7_33
    | spl7_144
    | ~ spl7_133 ),
    inference(avatar_split_clause,[],[f1433,f1222,f1441,f298])).

fof(f1441,plain,
    ( spl7_144
  <=> ! [X13,X15,X14] :
        ( ~ l1_struct_0(k2_tsep_1(X13,X14,X15))
        | v2_struct_0(X13)
        | ~ v2_pre_topc(X13)
        | ~ l1_pre_topc(X13)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X13)
        | v2_struct_0(X15)
        | ~ m1_pre_topc(X15,X13)
        | v2_struct_0(X14)
        | ~ m1_pre_topc(X14,X13)
        | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X15)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X14)
        | v2_struct_0(k2_tsep_1(X13,X14,X15))
        | ~ m1_pre_topc(k2_tsep_1(X13,X14,X15),sK0)
        | ~ m1_pre_topc(k2_tsep_1(X13,X14,X15),sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_144])])).

fof(f1433,plain,
    ( ! [X14,X15,X13] :
        ( ~ l1_struct_0(k2_tsep_1(X13,X14,X15))
        | ~ m1_pre_topc(k2_tsep_1(X13,X14,X15),sK3)
        | ~ m1_pre_topc(k2_tsep_1(X13,X14,X15),sK0)
        | v2_struct_0(k2_tsep_1(X13,X14,X15))
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X14)
        | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X15)
        | ~ m1_pre_topc(X14,X13)
        | v2_struct_0(X14)
        | ~ m1_pre_topc(X15,X13)
        | v2_struct_0(X15)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X13)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ l1_pre_topc(X13)
        | ~ v2_pre_topc(X13)
        | v2_struct_0(X13) )
    | ~ spl7_133 ),
    inference(resolution,[],[f1223,f62])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tsep_1(k2_tsep_1(X0,X3,X2),X1)
      | ~ m1_pre_topc(X1,X3)
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f1426,plain,
    ( ~ spl7_37
    | spl7_34
    | ~ spl7_143
    | spl7_4
    | ~ spl7_125 ),
    inference(avatar_split_clause,[],[f1406,f1123,f93,f1423,f302,f322])).

fof(f322,plain,
    ( spl7_37
  <=> m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_37])])).

fof(f302,plain,
    ( spl7_34
  <=> v2_struct_0(k1_tsep_1(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_34])])).

fof(f1423,plain,
    ( spl7_143
  <=> m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_143])])).

fof(f93,plain,
    ( spl7_4
  <=> r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),k1_tsep_1(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f1406,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK3)
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK3))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
    | spl7_4
    | ~ spl7_125 ),
    inference(resolution,[],[f1124,f94])).

fof(f94,plain,
    ( ~ r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),k1_tsep_1(sK0,sK1,sK3))
    | spl7_4 ),
    inference(avatar_component_clause,[],[f93])).

fof(f1421,plain,
    ( ~ spl7_13
    | spl7_14
    | ~ spl7_142
    | spl7_74
    | ~ spl7_125 ),
    inference(avatar_split_clause,[],[f1405,f1123,f561,f1418,f143,f138])).

fof(f138,plain,
    ( spl7_13
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f143,plain,
    ( spl7_14
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f1418,plain,
    ( spl7_142
  <=> m1_pre_topc(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_142])])).

fof(f561,plain,
    ( spl7_74
  <=> r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_74])])).

fof(f1405,plain,
    ( ~ m1_pre_topc(sK1,sK3)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | spl7_74
    | ~ spl7_125 ),
    inference(resolution,[],[f1124,f562])).

fof(f562,plain,
    ( ~ r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),sK1)
    | spl7_74 ),
    inference(avatar_component_clause,[],[f561])).

fof(f1378,plain,
    ( spl7_8
    | ~ spl7_23
    | spl7_141
    | ~ spl7_137 ),
    inference(avatar_split_clause,[],[f1368,f1305,f1376,f199,f113])).

fof(f1376,plain,
    ( spl7_141
  <=> ! [X3,X2] :
        ( v2_struct_0(k2_tsep_1(sK4,X2,X3))
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,sK4)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,sK4)
        | ~ m1_pre_topc(k2_tsep_1(sK4,X2,X3),sK0)
        | r1_tsep_1(k2_tsep_1(sK4,X2,X3),sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_141])])).

fof(f1305,plain,
    ( spl7_137
  <=> ! [X0] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK4)
        | r1_tsep_1(X0,sK1)
        | ~ m1_pre_topc(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_137])])).

fof(f1368,plain,
    ( ! [X2,X3] :
        ( v2_struct_0(k2_tsep_1(sK4,X2,X3))
        | r1_tsep_1(k2_tsep_1(sK4,X2,X3),sK1)
        | ~ m1_pre_topc(k2_tsep_1(sK4,X2,X3),sK0)
        | ~ m1_pre_topc(X3,sK4)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X2,sK4)
        | v2_struct_0(X2)
        | ~ l1_pre_topc(sK4)
        | v2_struct_0(sK4) )
    | ~ spl7_137 ),
    inference(resolution,[],[f1306,f77])).

fof(f1306,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK4)
        | v2_struct_0(X0)
        | r1_tsep_1(X0,sK1)
        | ~ m1_pre_topc(X0,sK0) )
    | ~ spl7_137 ),
    inference(avatar_component_clause,[],[f1305])).

fof(f1374,plain,
    ( spl7_8
    | ~ spl7_23
    | spl7_140
    | ~ spl7_137 ),
    inference(avatar_split_clause,[],[f1367,f1305,f1372,f199,f113])).

fof(f1372,plain,
    ( spl7_140
  <=> ! [X1,X0] :
        ( v2_struct_0(k1_tsep_1(sK4,X0,X1))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK4)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK4)
        | ~ m1_pre_topc(k1_tsep_1(sK4,X0,X1),sK0)
        | r1_tsep_1(k1_tsep_1(sK4,X0,X1),sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_140])])).

fof(f1367,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(k1_tsep_1(sK4,X0,X1))
        | r1_tsep_1(k1_tsep_1(sK4,X0,X1),sK1)
        | ~ m1_pre_topc(k1_tsep_1(sK4,X0,X1),sK0)
        | ~ m1_pre_topc(X1,sK4)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X0,sK4)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK4)
        | v2_struct_0(sK4) )
    | ~ spl7_137 ),
    inference(resolution,[],[f1306,f74])).

fof(f1332,plain,
    ( spl7_17
    | ~ spl7_16
    | ~ spl7_15
    | spl7_14
    | ~ spl7_13
    | spl7_8
    | ~ spl7_7
    | spl7_12
    | ~ spl7_11
    | spl7_80
    | ~ spl7_6
    | ~ spl7_74 ),
    inference(avatar_split_clause,[],[f1326,f561,f103,f600,f128,f133,f108,f113,f138,f143,f148,f153,f158])).

fof(f600,plain,
    ( spl7_80
  <=> r1_tsep_1(sK1,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_80])])).

fof(f103,plain,
    ( spl7_6
  <=> m1_pre_topc(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f1326,plain,
    ( ~ m1_pre_topc(sK1,sK2)
    | r1_tsep_1(sK1,sK4)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl7_74 ),
    inference(resolution,[],[f563,f62])).

fof(f563,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),sK1)
    | ~ spl7_74 ),
    inference(avatar_component_clause,[],[f561])).

fof(f1315,plain,
    ( spl7_8
    | spl7_139
    | ~ spl7_91 ),
    inference(avatar_split_clause,[],[f1303,f677,f1313,f113])).

fof(f1313,plain,
    ( spl7_139
  <=> ! [X5,X4,X6] :
        ( v2_struct_0(k1_tsep_1(X4,X5,sK4))
        | v2_struct_0(X4)
        | ~ v2_pre_topc(X4)
        | ~ l1_pre_topc(X4)
        | ~ m1_pre_topc(sK4,X4)
        | v2_struct_0(X5)
        | ~ m1_pre_topc(X5,X4)
        | ~ m1_pre_topc(X6,sK4)
        | r1_tsep_1(X6,sK1)
        | ~ m1_pre_topc(sK1,k1_tsep_1(X4,X5,sK4))
        | ~ m1_pre_topc(X6,k1_tsep_1(X4,X5,sK4))
        | v2_struct_0(X6)
        | ~ l1_pre_topc(k1_tsep_1(X4,X5,sK4))
        | ~ v2_pre_topc(k1_tsep_1(X4,X5,sK4)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_139])])).

fof(f677,plain,
    ( spl7_91
  <=> ! [X3,X2] :
        ( r1_tsep_1(X2,sK1)
        | v2_struct_0(X3)
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X3)
        | ~ m1_pre_topc(sK1,X3)
        | ~ m1_pre_topc(sK4,X3)
        | ~ m1_pre_topc(X2,sK4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_91])])).

fof(f1303,plain,
    ( ! [X6,X4,X5] :
        ( v2_struct_0(k1_tsep_1(X4,X5,sK4))
        | ~ v2_pre_topc(k1_tsep_1(X4,X5,sK4))
        | ~ l1_pre_topc(k1_tsep_1(X4,X5,sK4))
        | v2_struct_0(X6)
        | ~ m1_pre_topc(X6,k1_tsep_1(X4,X5,sK4))
        | ~ m1_pre_topc(sK1,k1_tsep_1(X4,X5,sK4))
        | r1_tsep_1(X6,sK1)
        | ~ m1_pre_topc(X6,sK4)
        | ~ m1_pre_topc(X5,X4)
        | v2_struct_0(X5)
        | ~ m1_pre_topc(sK4,X4)
        | v2_struct_0(sK4)
        | ~ l1_pre_topc(X4)
        | ~ v2_pre_topc(X4)
        | v2_struct_0(X4) )
    | ~ spl7_91 ),
    inference(resolution,[],[f678,f289])).

fof(f678,plain,
    ( ! [X2,X3] :
        ( ~ m1_pre_topc(sK4,X3)
        | v2_struct_0(X3)
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X3)
        | ~ m1_pre_topc(sK1,X3)
        | r1_tsep_1(X2,sK1)
        | ~ m1_pre_topc(X2,sK4) )
    | ~ spl7_91 ),
    inference(avatar_component_clause,[],[f677])).

fof(f1311,plain,
    ( spl7_8
    | spl7_138
    | ~ spl7_91 ),
    inference(avatar_split_clause,[],[f1302,f677,f1309,f113])).

fof(f1309,plain,
    ( spl7_138
  <=> ! [X1,X3,X2] :
        ( v2_struct_0(k1_tsep_1(X1,sK4,X2))
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ m1_pre_topc(sK4,X1)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X1)
        | ~ m1_pre_topc(X3,sK4)
        | r1_tsep_1(X3,sK1)
        | ~ m1_pre_topc(sK1,k1_tsep_1(X1,sK4,X2))
        | ~ m1_pre_topc(X3,k1_tsep_1(X1,sK4,X2))
        | v2_struct_0(X3)
        | ~ l1_pre_topc(k1_tsep_1(X1,sK4,X2))
        | ~ v2_pre_topc(k1_tsep_1(X1,sK4,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_138])])).

fof(f1302,plain,
    ( ! [X2,X3,X1] :
        ( v2_struct_0(k1_tsep_1(X1,sK4,X2))
        | ~ v2_pre_topc(k1_tsep_1(X1,sK4,X2))
        | ~ l1_pre_topc(k1_tsep_1(X1,sK4,X2))
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,k1_tsep_1(X1,sK4,X2))
        | ~ m1_pre_topc(sK1,k1_tsep_1(X1,sK4,X2))
        | r1_tsep_1(X3,sK1)
        | ~ m1_pre_topc(X3,sK4)
        | ~ m1_pre_topc(X2,X1)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(sK4,X1)
        | v2_struct_0(sK4)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl7_91 ),
    inference(resolution,[],[f678,f61])).

fof(f1307,plain,
    ( ~ spl7_13
    | spl7_137
    | ~ spl7_15
    | ~ spl7_16
    | spl7_17
    | ~ spl7_7
    | ~ spl7_91 ),
    inference(avatar_split_clause,[],[f1301,f677,f108,f158,f153,f148,f1305,f138])).

fof(f1301,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(sK1,sK0)
        | r1_tsep_1(X0,sK1)
        | ~ m1_pre_topc(X0,sK4) )
    | ~ spl7_7
    | ~ spl7_91 ),
    inference(resolution,[],[f678,f110])).

fof(f1287,plain,
    ( spl7_33
    | spl7_136
    | ~ spl7_108 ),
    inference(avatar_split_clause,[],[f1278,f899,f1285,f298])).

fof(f1285,plain,
    ( spl7_136
  <=> ! [X5,X4,X6] :
        ( ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X4)
        | ~ m1_pre_topc(k2_tsep_1(X6,X4,X5),sK0)
        | v2_struct_0(k2_tsep_1(X6,X4,X5))
        | ~ m1_pre_topc(k2_tsep_1(X6,X4,X5),sK1)
        | v2_struct_0(X6)
        | ~ v2_pre_topc(X6)
        | ~ l1_pre_topc(X6)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X6)
        | v2_struct_0(X5)
        | v2_struct_0(X4)
        | ~ m1_pre_topc(X4,X6)
        | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X5)
        | ~ m1_pre_topc(X5,X6) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_136])])).

fof(f1278,plain,
    ( ! [X6,X4,X5] :
        ( ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X4)
        | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X5)
        | ~ m1_pre_topc(X4,X6)
        | v2_struct_0(X4)
        | ~ m1_pre_topc(X5,X6)
        | v2_struct_0(X5)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X6)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ l1_pre_topc(X6)
        | ~ v2_pre_topc(X6)
        | v2_struct_0(X6)
        | ~ m1_pre_topc(k2_tsep_1(X6,X4,X5),sK1)
        | v2_struct_0(k2_tsep_1(X6,X4,X5))
        | ~ m1_pre_topc(k2_tsep_1(X6,X4,X5),sK0) )
    | ~ spl7_108 ),
    inference(resolution,[],[f62,f900])).

fof(f1283,plain,
    ( spl7_33
    | spl7_135
    | ~ spl7_100 ),
    inference(avatar_split_clause,[],[f1277,f776,f1281,f298])).

fof(f1281,plain,
    ( spl7_135
  <=> ! [X1,X3,X2] :
        ( ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X1)
        | v2_struct_0(k2_tsep_1(X3,X1,X2))
        | ~ m1_pre_topc(k2_tsep_1(X3,X1,X2),sK0)
        | ~ m1_pre_topc(k2_tsep_1(X3,X1,X2),sK1)
        | ~ l1_struct_0(k2_tsep_1(X3,X1,X2))
        | v2_struct_0(X3)
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X3)
        | v2_struct_0(X2)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X3)
        | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X2)
        | ~ m1_pre_topc(X2,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_135])])).

fof(f776,plain,
    ( spl7_100
  <=> ! [X6] :
        ( ~ m1_pre_topc(X6,sK1)
        | ~ l1_struct_0(X6)
        | r1_tsep_1(X6,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X6,sK0)
        | v2_struct_0(X6) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_100])])).

fof(f1277,plain,
    ( ! [X2,X3,X1] :
        ( ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X1)
        | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X2)
        | ~ m1_pre_topc(X1,X3)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X2,X3)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X3)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(X3)
        | v2_struct_0(X3)
        | ~ l1_struct_0(k2_tsep_1(X3,X1,X2))
        | ~ m1_pre_topc(k2_tsep_1(X3,X1,X2),sK1)
        | ~ m1_pre_topc(k2_tsep_1(X3,X1,X2),sK0)
        | v2_struct_0(k2_tsep_1(X3,X1,X2)) )
    | ~ spl7_100 ),
    inference(resolution,[],[f62,f777])).

fof(f777,plain,
    ( ! [X6] :
        ( r1_tsep_1(X6,k2_tsep_1(sK0,sK2,sK4))
        | ~ l1_struct_0(X6)
        | ~ m1_pre_topc(X6,sK1)
        | ~ m1_pre_topc(X6,sK0)
        | v2_struct_0(X6) )
    | ~ spl7_100 ),
    inference(avatar_component_clause,[],[f776])).

fof(f1262,plain,
    ( ~ spl7_9
    | spl7_10
    | ~ spl7_134
    | spl7_63
    | ~ spl7_108 ),
    inference(avatar_split_clause,[],[f1256,f899,f503,f1258,f123,f118])).

fof(f1258,plain,
    ( spl7_134
  <=> m1_pre_topc(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_134])])).

fof(f503,plain,
    ( spl7_63
  <=> r1_tsep_1(sK3,k2_tsep_1(sK0,sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_63])])).

fof(f1256,plain,
    ( ~ m1_pre_topc(sK3,sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | spl7_63
    | ~ spl7_108 ),
    inference(resolution,[],[f504,f900])).

fof(f504,plain,
    ( ~ r1_tsep_1(sK3,k2_tsep_1(sK0,sK2,sK4))
    | spl7_63 ),
    inference(avatar_component_clause,[],[f503])).

fof(f1261,plain,
    ( spl7_10
    | ~ spl7_9
    | ~ spl7_134
    | ~ spl7_28
    | spl7_63
    | ~ spl7_100 ),
    inference(avatar_split_clause,[],[f1255,f776,f503,f229,f1258,f118,f123])).

fof(f1255,plain,
    ( ~ l1_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK1)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | spl7_63
    | ~ spl7_100 ),
    inference(resolution,[],[f504,f777])).

fof(f1224,plain,
    ( ~ spl7_30
    | spl7_133
    | ~ spl7_125 ),
    inference(avatar_split_clause,[],[f1200,f1123,f1222,f242])).

fof(f242,plain,
    ( spl7_30
  <=> l1_struct_0(k2_tsep_1(sK0,sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).

fof(f1200,plain,
    ( ! [X12] :
        ( ~ m1_pre_topc(X12,sK3)
        | v2_struct_0(X12)
        | ~ m1_pre_topc(X12,sK0)
        | r1_tsep_1(X12,k2_tsep_1(sK0,sK2,sK4))
        | ~ l1_struct_0(X12)
        | ~ l1_struct_0(k2_tsep_1(sK0,sK2,sK4)) )
    | ~ spl7_125 ),
    inference(resolution,[],[f1124,f70])).

fof(f1220,plain,
    ( spl7_33
    | spl7_132
    | ~ spl7_125 ),
    inference(avatar_split_clause,[],[f1201,f1123,f1218,f298])).

fof(f1218,plain,
    ( spl7_132
  <=> ! [X9,X11,X10] :
        ( ~ m1_pre_topc(X9,sK3)
        | v2_struct_0(X11)
        | ~ v2_pre_topc(X11)
        | ~ l1_pre_topc(X11)
        | v2_struct_0(X10)
        | ~ m1_pre_topc(X10,X11)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X11)
        | ~ m1_pre_topc(X9,X11)
        | ~ m1_pre_topc(X10,k2_tsep_1(sK0,sK2,sK4))
        | r1_tsep_1(X10,X9)
        | ~ m1_pre_topc(X9,sK0)
        | v2_struct_0(X9) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_132])])).

fof(f1201,plain,
    ( ! [X10,X11,X9] :
        ( ~ m1_pre_topc(X9,sK3)
        | v2_struct_0(X9)
        | ~ m1_pre_topc(X9,sK0)
        | r1_tsep_1(X10,X9)
        | ~ m1_pre_topc(X10,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X9,X11)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X11)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X10,X11)
        | v2_struct_0(X10)
        | ~ l1_pre_topc(X11)
        | ~ v2_pre_topc(X11)
        | v2_struct_0(X11) )
    | ~ spl7_125 ),
    inference(duplicate_literal_removal,[],[f1199])).

fof(f1199,plain,
    ( ! [X10,X11,X9] :
        ( ~ m1_pre_topc(X9,sK3)
        | v2_struct_0(X9)
        | ~ m1_pre_topc(X9,sK0)
        | r1_tsep_1(X10,X9)
        | ~ m1_pre_topc(X10,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X9,X11)
        | v2_struct_0(X9)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X11)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X10,X11)
        | v2_struct_0(X10)
        | ~ l1_pre_topc(X11)
        | ~ v2_pre_topc(X11)
        | v2_struct_0(X11) )
    | ~ spl7_125 ),
    inference(resolution,[],[f1124,f66])).

fof(f1216,plain,
    ( spl7_33
    | spl7_131
    | ~ spl7_125 ),
    inference(avatar_split_clause,[],[f1202,f1123,f1214,f298])).

fof(f1214,plain,
    ( spl7_131
  <=> ! [X7,X8,X6] :
        ( ~ m1_pre_topc(X6,sK3)
        | v2_struct_0(X8)
        | ~ v2_pre_topc(X8)
        | ~ l1_pre_topc(X8)
        | v2_struct_0(X7)
        | ~ m1_pre_topc(X7,X8)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X8)
        | ~ m1_pre_topc(X6,X8)
        | ~ m1_pre_topc(X7,k2_tsep_1(sK0,sK2,sK4))
        | r1_tsep_1(X6,X7)
        | ~ m1_pre_topc(X6,sK0)
        | v2_struct_0(X6) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_131])])).

fof(f1202,plain,
    ( ! [X6,X8,X7] :
        ( ~ m1_pre_topc(X6,sK3)
        | v2_struct_0(X6)
        | ~ m1_pre_topc(X6,sK0)
        | r1_tsep_1(X6,X7)
        | ~ m1_pre_topc(X7,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X6,X8)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X8)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X7,X8)
        | v2_struct_0(X7)
        | ~ l1_pre_topc(X8)
        | ~ v2_pre_topc(X8)
        | v2_struct_0(X8) )
    | ~ spl7_125 ),
    inference(duplicate_literal_removal,[],[f1198])).

fof(f1198,plain,
    ( ! [X6,X8,X7] :
        ( ~ m1_pre_topc(X6,sK3)
        | v2_struct_0(X6)
        | ~ m1_pre_topc(X6,sK0)
        | r1_tsep_1(X6,X7)
        | ~ m1_pre_topc(X7,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X6,X8)
        | v2_struct_0(X6)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X8)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X7,X8)
        | v2_struct_0(X7)
        | ~ l1_pre_topc(X8)
        | ~ v2_pre_topc(X8)
        | v2_struct_0(X8) )
    | ~ spl7_125 ),
    inference(resolution,[],[f1124,f67])).

fof(f1212,plain,
    ( spl7_33
    | spl7_130
    | ~ spl7_125 ),
    inference(avatar_split_clause,[],[f1203,f1123,f1210,f298])).

fof(f1210,plain,
    ( spl7_130
  <=> ! [X3,X5,X4] :
        ( ~ m1_pre_topc(X3,sK3)
        | v2_struct_0(X5)
        | ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X5)
        | v2_struct_0(X4)
        | ~ m1_pre_topc(X4,X5)
        | ~ m1_pre_topc(X3,X5)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X5)
        | r1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X4,X3)
        | ~ m1_pre_topc(X3,sK0)
        | v2_struct_0(X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_130])])).

fof(f1203,plain,
    ( ! [X4,X5,X3] :
        ( ~ m1_pre_topc(X3,sK3)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,sK0)
        | r1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X4,X3)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X5)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X3,X5)
        | ~ m1_pre_topc(X4,X5)
        | v2_struct_0(X4)
        | ~ l1_pre_topc(X5)
        | ~ v2_pre_topc(X5)
        | v2_struct_0(X5) )
    | ~ spl7_125 ),
    inference(duplicate_literal_removal,[],[f1197])).

fof(f1197,plain,
    ( ! [X4,X5,X3] :
        ( ~ m1_pre_topc(X3,sK3)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,sK0)
        | r1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X4,X3)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X5)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X3,X5)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X4,X5)
        | v2_struct_0(X4)
        | ~ l1_pre_topc(X5)
        | ~ v2_pre_topc(X5)
        | v2_struct_0(X5) )
    | ~ spl7_125 ),
    inference(resolution,[],[f1124,f68])).

fof(f1208,plain,
    ( spl7_33
    | spl7_129
    | ~ spl7_125 ),
    inference(avatar_split_clause,[],[f1204,f1123,f1206,f298])).

fof(f1206,plain,
    ( spl7_129
  <=> ! [X1,X0,X2] :
        ( ~ m1_pre_topc(X0,sK3)
        | v2_struct_0(X2)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X2)
        | ~ m1_pre_topc(X0,X2)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X2)
        | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X1)
        | ~ m1_pre_topc(X1,X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_129])])).

fof(f1204,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_pre_topc(X0,sK3)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X1)
        | ~ m1_pre_topc(X1,X0)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X2)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X0,X2)
        | ~ m1_pre_topc(X1,X2)
        | v2_struct_0(X1)
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2)
        | v2_struct_0(X2) )
    | ~ spl7_125 ),
    inference(duplicate_literal_removal,[],[f1196])).

fof(f1196,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_pre_topc(X0,sK3)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X1)
        | ~ m1_pre_topc(X1,X0)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X2)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X0,X2)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X1,X2)
        | v2_struct_0(X1)
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2)
        | v2_struct_0(X2) )
    | ~ spl7_125 ),
    inference(resolution,[],[f1124,f69])).

fof(f1175,plain,
    ( ~ spl7_28
    | ~ spl7_26
    | spl7_116
    | ~ spl7_124 ),
    inference(avatar_split_clause,[],[f1170,f1056,f971,f217,f229])).

fof(f217,plain,
    ( spl7_26
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).

fof(f971,plain,
    ( spl7_116
  <=> r1_tsep_1(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_116])])).

fof(f1056,plain,
    ( spl7_124
  <=> r1_tsep_1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_124])])).

fof(f1170,plain,
    ( r1_tsep_1(sK1,sK3)
    | ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK3)
    | ~ spl7_124 ),
    inference(resolution,[],[f1058,f70])).

fof(f1058,plain,
    ( r1_tsep_1(sK3,sK1)
    | ~ spl7_124 ),
    inference(avatar_component_clause,[],[f1056])).

fof(f1174,plain,
    ( spl7_10
    | spl7_14
    | spl7_121
    | ~ spl7_124 ),
    inference(avatar_split_clause,[],[f1169,f1056,f1044,f143,f123])).

fof(f1044,plain,
    ( spl7_121
  <=> ! [X1,X0] :
        ( r1_tsep_1(X0,sK1)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,X1)
        | ~ m1_pre_topc(sK1,X1)
        | ~ m1_pre_topc(sK3,X1)
        | ~ m1_pre_topc(X0,sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_121])])).

fof(f1169,plain,
    ( ! [X6,X7] :
        ( r1_tsep_1(X6,sK1)
        | ~ m1_pre_topc(X6,sK3)
        | ~ m1_pre_topc(sK1,X7)
        | v2_struct_0(sK1)
        | ~ m1_pre_topc(sK3,X7)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(X6,X7)
        | v2_struct_0(X6)
        | ~ l1_pre_topc(X7)
        | ~ v2_pre_topc(X7)
        | v2_struct_0(X7) )
    | ~ spl7_124 ),
    inference(resolution,[],[f1058,f66])).

fof(f1173,plain,
    ( spl7_10
    | spl7_14
    | spl7_128
    | ~ spl7_124 ),
    inference(avatar_split_clause,[],[f1168,f1056,f1163,f143,f123])).

fof(f1163,plain,
    ( spl7_128
  <=> ! [X1,X0] :
        ( r1_tsep_1(sK1,X0)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,X1)
        | ~ m1_pre_topc(sK1,X1)
        | ~ m1_pre_topc(sK3,X1)
        | ~ m1_pre_topc(X0,sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_128])])).

fof(f1168,plain,
    ( ! [X4,X5] :
        ( r1_tsep_1(sK1,X4)
        | ~ m1_pre_topc(X4,sK3)
        | ~ m1_pre_topc(sK1,X5)
        | v2_struct_0(sK1)
        | ~ m1_pre_topc(sK3,X5)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(X4,X5)
        | v2_struct_0(X4)
        | ~ l1_pre_topc(X5)
        | ~ v2_pre_topc(X5)
        | v2_struct_0(X5) )
    | ~ spl7_124 ),
    inference(resolution,[],[f1058,f67])).

fof(f1172,plain,
    ( spl7_14
    | spl7_10
    | spl7_123
    | ~ spl7_124 ),
    inference(avatar_split_clause,[],[f1167,f1056,f1052,f123,f143])).

fof(f1052,plain,
    ( spl7_123
  <=> ! [X5,X4] :
        ( r1_tsep_1(X4,sK3)
        | v2_struct_0(X5)
        | ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X5)
        | v2_struct_0(X4)
        | ~ m1_pre_topc(X4,X5)
        | ~ m1_pre_topc(sK3,X5)
        | ~ m1_pre_topc(sK1,X5)
        | ~ m1_pre_topc(X4,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_123])])).

fof(f1167,plain,
    ( ! [X2,X3] :
        ( r1_tsep_1(X2,sK3)
        | ~ m1_pre_topc(X2,sK1)
        | ~ m1_pre_topc(sK3,X3)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK1,X3)
        | v2_struct_0(sK1)
        | ~ m1_pre_topc(X2,X3)
        | v2_struct_0(X2)
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(X3)
        | v2_struct_0(X3) )
    | ~ spl7_124 ),
    inference(resolution,[],[f1058,f68])).

fof(f1171,plain,
    ( spl7_14
    | spl7_10
    | spl7_122
    | ~ spl7_124 ),
    inference(avatar_split_clause,[],[f1166,f1056,f1048,f123,f143])).

fof(f1048,plain,
    ( spl7_122
  <=> ! [X3,X2] :
        ( r1_tsep_1(sK3,X2)
        | v2_struct_0(X3)
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X3)
        | ~ m1_pre_topc(sK3,X3)
        | ~ m1_pre_topc(sK1,X3)
        | ~ m1_pre_topc(X2,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_122])])).

fof(f1166,plain,
    ( ! [X0,X1] :
        ( r1_tsep_1(sK3,X0)
        | ~ m1_pre_topc(X0,sK1)
        | ~ m1_pre_topc(sK3,X1)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK1,X1)
        | v2_struct_0(sK1)
        | ~ m1_pre_topc(X0,X1)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl7_124 ),
    inference(resolution,[],[f1058,f69])).

fof(f1165,plain,
    ( spl7_10
    | spl7_14
    | spl7_128
    | ~ spl7_116 ),
    inference(avatar_split_clause,[],[f1157,f971,f1163,f143,f123])).

fof(f1157,plain,
    ( ! [X0,X1] :
        ( r1_tsep_1(sK1,X0)
        | ~ m1_pre_topc(X0,sK3)
        | ~ m1_pre_topc(sK1,X1)
        | v2_struct_0(sK1)
        | ~ m1_pre_topc(sK3,X1)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(X0,X1)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl7_116 ),
    inference(resolution,[],[f973,f69])).

fof(f973,plain,
    ( r1_tsep_1(sK1,sK3)
    | ~ spl7_116 ),
    inference(avatar_component_clause,[],[f971])).

fof(f1136,plain,
    ( spl7_10
    | spl7_33
    | spl7_76
    | ~ spl7_77 ),
    inference(avatar_split_clause,[],[f938,f583,f579,f298,f123])).

fof(f579,plain,
    ( spl7_76
  <=> ! [X3,X2] :
        ( r1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4))
        | v2_struct_0(X3)
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X3)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X3)
        | ~ m1_pre_topc(sK3,X3)
        | ~ m1_pre_topc(X2,sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_76])])).

fof(f938,plain,
    ( ! [X6,X7] :
        ( r1_tsep_1(X6,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X6,sK3)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X7)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(sK3,X7)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(X6,X7)
        | v2_struct_0(X6)
        | ~ l1_pre_topc(X7)
        | ~ v2_pre_topc(X7)
        | v2_struct_0(X7) )
    | ~ spl7_77 ),
    inference(resolution,[],[f68,f585])).

fof(f1135,plain,
    ( spl7_10
    | spl7_33
    | spl7_75
    | ~ spl7_77 ),
    inference(avatar_split_clause,[],[f1108,f583,f575,f298,f123])).

fof(f575,plain,
    ( spl7_75
  <=> ! [X1,X0] :
        ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X0)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,X1)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X1)
        | ~ m1_pre_topc(sK3,X1)
        | ~ m1_pre_topc(X0,sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_75])])).

fof(f1108,plain,
    ( ! [X15,X16] :
        ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X15)
        | ~ m1_pre_topc(X15,sK3)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X16)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(sK3,X16)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(X15,X16)
        | v2_struct_0(X15)
        | ~ l1_pre_topc(X16)
        | ~ v2_pre_topc(X16)
        | v2_struct_0(X16) )
    | ~ spl7_77 ),
    inference(resolution,[],[f69,f585])).

fof(f1134,plain,
    ( ~ spl7_30
    | ~ spl7_28
    | spl7_63
    | ~ spl7_77 ),
    inference(avatar_split_clause,[],[f685,f583,f503,f229,f242])).

fof(f685,plain,
    ( r1_tsep_1(sK3,k2_tsep_1(sK0,sK2,sK4))
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(k2_tsep_1(sK0,sK2,sK4))
    | ~ spl7_77 ),
    inference(resolution,[],[f585,f70])).

fof(f1133,plain,
    ( spl7_33
    | spl7_127
    | ~ spl7_75 ),
    inference(avatar_split_clause,[],[f1120,f575,f1131,f298])).

fof(f1131,plain,
    ( spl7_127
  <=> ! [X5,X4,X6] :
        ( v2_struct_0(k1_tsep_1(X4,X5,k2_tsep_1(sK0,sK2,sK4)))
        | v2_struct_0(X4)
        | ~ v2_pre_topc(X4)
        | ~ l1_pre_topc(X4)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X4)
        | v2_struct_0(X5)
        | ~ m1_pre_topc(X5,X4)
        | ~ m1_pre_topc(X6,sK3)
        | ~ m1_pre_topc(sK3,k1_tsep_1(X4,X5,k2_tsep_1(sK0,sK2,sK4)))
        | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X6)
        | ~ m1_pre_topc(X6,k1_tsep_1(X4,X5,k2_tsep_1(sK0,sK2,sK4)))
        | v2_struct_0(X6)
        | ~ l1_pre_topc(k1_tsep_1(X4,X5,k2_tsep_1(sK0,sK2,sK4)))
        | ~ v2_pre_topc(k1_tsep_1(X4,X5,k2_tsep_1(sK0,sK2,sK4))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_127])])).

fof(f1120,plain,
    ( ! [X6,X4,X5] :
        ( v2_struct_0(k1_tsep_1(X4,X5,k2_tsep_1(sK0,sK2,sK4)))
        | ~ v2_pre_topc(k1_tsep_1(X4,X5,k2_tsep_1(sK0,sK2,sK4)))
        | ~ l1_pre_topc(k1_tsep_1(X4,X5,k2_tsep_1(sK0,sK2,sK4)))
        | v2_struct_0(X6)
        | ~ m1_pre_topc(X6,k1_tsep_1(X4,X5,k2_tsep_1(sK0,sK2,sK4)))
        | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X6)
        | ~ m1_pre_topc(sK3,k1_tsep_1(X4,X5,k2_tsep_1(sK0,sK2,sK4)))
        | ~ m1_pre_topc(X6,sK3)
        | ~ m1_pre_topc(X5,X4)
        | v2_struct_0(X5)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X4)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ l1_pre_topc(X4)
        | ~ v2_pre_topc(X4)
        | v2_struct_0(X4) )
    | ~ spl7_75 ),
    inference(resolution,[],[f576,f289])).

fof(f576,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X1)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,X1)
        | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X0)
        | ~ m1_pre_topc(sK3,X1)
        | ~ m1_pre_topc(X0,sK3) )
    | ~ spl7_75 ),
    inference(avatar_component_clause,[],[f575])).

fof(f1129,plain,
    ( spl7_33
    | spl7_126
    | ~ spl7_75 ),
    inference(avatar_split_clause,[],[f1119,f575,f1127,f298])).

fof(f1127,plain,
    ( spl7_126
  <=> ! [X1,X3,X2] :
        ( v2_struct_0(k1_tsep_1(X1,k2_tsep_1(sK0,sK2,sK4),X2))
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X1)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X1)
        | ~ m1_pre_topc(X3,sK3)
        | ~ m1_pre_topc(sK3,k1_tsep_1(X1,k2_tsep_1(sK0,sK2,sK4),X2))
        | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X3)
        | ~ m1_pre_topc(X3,k1_tsep_1(X1,k2_tsep_1(sK0,sK2,sK4),X2))
        | v2_struct_0(X3)
        | ~ l1_pre_topc(k1_tsep_1(X1,k2_tsep_1(sK0,sK2,sK4),X2))
        | ~ v2_pre_topc(k1_tsep_1(X1,k2_tsep_1(sK0,sK2,sK4),X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_126])])).

fof(f1119,plain,
    ( ! [X2,X3,X1] :
        ( v2_struct_0(k1_tsep_1(X1,k2_tsep_1(sK0,sK2,sK4),X2))
        | ~ v2_pre_topc(k1_tsep_1(X1,k2_tsep_1(sK0,sK2,sK4),X2))
        | ~ l1_pre_topc(k1_tsep_1(X1,k2_tsep_1(sK0,sK2,sK4),X2))
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,k1_tsep_1(X1,k2_tsep_1(sK0,sK2,sK4),X2))
        | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X3)
        | ~ m1_pre_topc(sK3,k1_tsep_1(X1,k2_tsep_1(sK0,sK2,sK4),X2))
        | ~ m1_pre_topc(X3,sK3)
        | ~ m1_pre_topc(X2,X1)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X1)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl7_75 ),
    inference(resolution,[],[f576,f61])).

fof(f1125,plain,
    ( spl7_12
    | ~ spl7_11
    | spl7_8
    | ~ spl7_7
    | ~ spl7_9
    | spl7_125
    | ~ spl7_15
    | ~ spl7_16
    | spl7_17
    | ~ spl7_75 ),
    inference(avatar_split_clause,[],[f1121,f575,f158,f153,f148,f1123,f118,f108,f113,f128,f133])).

fof(f1121,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X0)
        | ~ m1_pre_topc(sK3,sK0)
        | ~ m1_pre_topc(X0,sK3)
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2) )
    | ~ spl7_75 ),
    inference(duplicate_literal_removal,[],[f1118])).

fof(f1118,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X0)
        | ~ m1_pre_topc(sK3,sK0)
        | ~ m1_pre_topc(X0,sK3)
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl7_75 ),
    inference(resolution,[],[f576,f77])).

fof(f1059,plain,
    ( ~ spl7_26
    | ~ spl7_28
    | spl7_124
    | ~ spl7_116 ),
    inference(avatar_split_clause,[],[f1042,f971,f1056,f229,f217])).

fof(f1042,plain,
    ( r1_tsep_1(sK3,sK1)
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK1)
    | ~ spl7_116 ),
    inference(resolution,[],[f973,f70])).

fof(f1054,plain,
    ( spl7_14
    | spl7_10
    | spl7_123
    | ~ spl7_116 ),
    inference(avatar_split_clause,[],[f1041,f971,f1052,f123,f143])).

fof(f1041,plain,
    ( ! [X4,X5] :
        ( r1_tsep_1(X4,sK3)
        | ~ m1_pre_topc(X4,sK1)
        | ~ m1_pre_topc(sK3,X5)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK1,X5)
        | v2_struct_0(sK1)
        | ~ m1_pre_topc(X4,X5)
        | v2_struct_0(X4)
        | ~ l1_pre_topc(X5)
        | ~ v2_pre_topc(X5)
        | v2_struct_0(X5) )
    | ~ spl7_116 ),
    inference(resolution,[],[f973,f66])).

fof(f1050,plain,
    ( spl7_14
    | spl7_10
    | spl7_122
    | ~ spl7_116 ),
    inference(avatar_split_clause,[],[f1040,f971,f1048,f123,f143])).

fof(f1040,plain,
    ( ! [X2,X3] :
        ( r1_tsep_1(sK3,X2)
        | ~ m1_pre_topc(X2,sK1)
        | ~ m1_pre_topc(sK3,X3)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK1,X3)
        | v2_struct_0(sK1)
        | ~ m1_pre_topc(X2,X3)
        | v2_struct_0(X2)
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(X3)
        | v2_struct_0(X3) )
    | ~ spl7_116 ),
    inference(resolution,[],[f973,f67])).

fof(f1046,plain,
    ( spl7_10
    | spl7_14
    | spl7_121
    | ~ spl7_116 ),
    inference(avatar_split_clause,[],[f1039,f971,f1044,f143,f123])).

fof(f1039,plain,
    ( ! [X0,X1] :
        ( r1_tsep_1(X0,sK1)
        | ~ m1_pre_topc(X0,sK3)
        | ~ m1_pre_topc(sK1,X1)
        | v2_struct_0(sK1)
        | ~ m1_pre_topc(sK3,X1)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(X0,X1)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl7_116 ),
    inference(resolution,[],[f973,f68])).

fof(f1022,plain,
    ( ~ spl7_30
    | spl7_100
    | ~ spl7_92 ),
    inference(avatar_split_clause,[],[f1007,f704,f776,f242])).

fof(f1007,plain,
    ( ! [X9] :
        ( ~ m1_pre_topc(X9,sK1)
        | v2_struct_0(X9)
        | ~ m1_pre_topc(X9,sK0)
        | r1_tsep_1(X9,k2_tsep_1(sK0,sK2,sK4))
        | ~ l1_struct_0(X9)
        | ~ l1_struct_0(k2_tsep_1(sK0,sK2,sK4)) )
    | ~ spl7_92 ),
    inference(resolution,[],[f705,f70])).

fof(f1021,plain,
    ( spl7_33
    | spl7_120
    | ~ spl7_108 ),
    inference(avatar_split_clause,[],[f1016,f899,f1019,f298])).

fof(f1019,plain,
    ( spl7_120
  <=> ! [X3,X5,X4] :
        ( ~ m1_pre_topc(X3,sK1)
        | v2_struct_0(X5)
        | ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X5)
        | v2_struct_0(X4)
        | ~ m1_pre_topc(X4,X5)
        | ~ m1_pre_topc(X3,X5)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X5)
        | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X4)
        | ~ m1_pre_topc(X4,X3)
        | ~ m1_pre_topc(X3,sK0)
        | v2_struct_0(X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_120])])).

fof(f1016,plain,
    ( ! [X4,X5,X3] :
        ( ~ m1_pre_topc(X3,sK1)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,sK0)
        | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X4)
        | ~ m1_pre_topc(X4,X3)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X5)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X3,X5)
        | ~ m1_pre_topc(X4,X5)
        | v2_struct_0(X4)
        | ~ l1_pre_topc(X5)
        | ~ v2_pre_topc(X5)
        | v2_struct_0(X5) )
    | ~ spl7_108 ),
    inference(duplicate_literal_removal,[],[f1012])).

fof(f1012,plain,
    ( ! [X4,X5,X3] :
        ( ~ m1_pre_topc(X3,sK1)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,sK0)
        | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X4)
        | ~ m1_pre_topc(X4,X3)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X5)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X3,X5)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X4,X5)
        | v2_struct_0(X4)
        | ~ l1_pre_topc(X5)
        | ~ v2_pre_topc(X5)
        | v2_struct_0(X5) )
    | ~ spl7_108 ),
    inference(resolution,[],[f900,f67])).

fof(f987,plain,
    ( ~ spl7_23
    | ~ spl7_117
    | spl7_118
    | spl7_119
    | ~ spl7_105 ),
    inference(avatar_split_clause,[],[f961,f848,f984,f980,f976,f199])).

fof(f976,plain,
    ( spl7_117
  <=> m1_pre_topc(sK5(sK4),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_117])])).

fof(f980,plain,
    ( spl7_118
  <=> r1_tsep_1(sK1,sK5(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_118])])).

fof(f984,plain,
    ( spl7_119
  <=> v2_struct_0(sK5(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_119])])).

fof(f848,plain,
    ( spl7_105
  <=> ! [X0] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK4)
        | r1_tsep_1(sK1,X0)
        | ~ m1_pre_topc(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_105])])).

fof(f961,plain,
    ( v2_struct_0(sK5(sK4))
    | r1_tsep_1(sK1,sK5(sK4))
    | ~ m1_pre_topc(sK5(sK4),sK0)
    | ~ l1_pre_topc(sK4)
    | ~ spl7_105 ),
    inference(resolution,[],[f849,f60])).

fof(f60,plain,(
    ! [X0] :
      ( m1_pre_topc(sK5(X0),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( m1_pre_topc(sK5(X0),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f18,f39])).

fof(f39,plain,(
    ! [X0] :
      ( ? [X1] : m1_pre_topc(X1,X0)
     => m1_pre_topc(sK5(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0] :
      ( ? [X1] : m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ? [X1] : m1_pre_topc(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_pre_topc)).

fof(f849,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK4)
        | v2_struct_0(X0)
        | r1_tsep_1(sK1,X0)
        | ~ m1_pre_topc(X0,sK0) )
    | ~ spl7_105 ),
    inference(avatar_component_clause,[],[f848])).

fof(f974,plain,
    ( ~ spl7_9
    | spl7_116
    | spl7_10
    | ~ spl7_5
    | ~ spl7_105 ),
    inference(avatar_split_clause,[],[f960,f848,f98,f123,f971,f118])).

fof(f960,plain,
    ( v2_struct_0(sK3)
    | r1_tsep_1(sK1,sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ spl7_5
    | ~ spl7_105 ),
    inference(resolution,[],[f849,f100])).

fof(f969,plain,
    ( spl7_8
    | ~ spl7_23
    | spl7_115
    | ~ spl7_105 ),
    inference(avatar_split_clause,[],[f959,f848,f967,f199,f113])).

fof(f967,plain,
    ( spl7_115
  <=> ! [X3,X2] :
        ( v2_struct_0(k2_tsep_1(sK4,X2,X3))
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,sK4)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,sK4)
        | ~ m1_pre_topc(k2_tsep_1(sK4,X2,X3),sK0)
        | r1_tsep_1(sK1,k2_tsep_1(sK4,X2,X3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_115])])).

fof(f959,plain,
    ( ! [X2,X3] :
        ( v2_struct_0(k2_tsep_1(sK4,X2,X3))
        | r1_tsep_1(sK1,k2_tsep_1(sK4,X2,X3))
        | ~ m1_pre_topc(k2_tsep_1(sK4,X2,X3),sK0)
        | ~ m1_pre_topc(X3,sK4)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X2,sK4)
        | v2_struct_0(X2)
        | ~ l1_pre_topc(sK4)
        | v2_struct_0(sK4) )
    | ~ spl7_105 ),
    inference(resolution,[],[f849,f77])).

fof(f965,plain,
    ( spl7_8
    | ~ spl7_23
    | spl7_114
    | ~ spl7_105 ),
    inference(avatar_split_clause,[],[f958,f848,f963,f199,f113])).

fof(f963,plain,
    ( spl7_114
  <=> ! [X1,X0] :
        ( v2_struct_0(k1_tsep_1(sK4,X0,X1))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK4)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK4)
        | ~ m1_pre_topc(k1_tsep_1(sK4,X0,X1),sK0)
        | r1_tsep_1(sK1,k1_tsep_1(sK4,X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_114])])).

fof(f958,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(k1_tsep_1(sK4,X0,X1))
        | r1_tsep_1(sK1,k1_tsep_1(sK4,X0,X1))
        | ~ m1_pre_topc(k1_tsep_1(sK4,X0,X1),sK0)
        | ~ m1_pre_topc(X1,sK4)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X0,sK4)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK4)
        | v2_struct_0(sK4) )
    | ~ spl7_105 ),
    inference(resolution,[],[f849,f74])).

fof(f949,plain,
    ( spl7_33
    | spl7_113
    | ~ spl7_92 ),
    inference(avatar_split_clause,[],[f944,f704,f947,f298])).

fof(f947,plain,
    ( spl7_113
  <=> ! [X3,X5,X4] :
        ( r1_tsep_1(X3,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X4,sK0)
        | ~ m1_pre_topc(X4,sK1)
        | v2_struct_0(X5)
        | ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X5)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,X5)
        | v2_struct_0(X4)
        | ~ m1_pre_topc(X4,X5)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X5)
        | ~ m1_pre_topc(X3,X4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_113])])).

fof(f944,plain,
    ( ! [X4,X5,X3] :
        ( r1_tsep_1(X3,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X3,X4)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X5)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X4,X5)
        | v2_struct_0(X4)
        | ~ m1_pre_topc(X3,X5)
        | v2_struct_0(X3)
        | ~ l1_pre_topc(X5)
        | ~ v2_pre_topc(X5)
        | v2_struct_0(X5)
        | ~ m1_pre_topc(X4,sK1)
        | ~ m1_pre_topc(X4,sK0) )
    | ~ spl7_92 ),
    inference(duplicate_literal_removal,[],[f937])).

fof(f937,plain,
    ( ! [X4,X5,X3] :
        ( r1_tsep_1(X3,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X3,X4)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X5)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X4,X5)
        | v2_struct_0(X4)
        | ~ m1_pre_topc(X3,X5)
        | v2_struct_0(X3)
        | ~ l1_pre_topc(X5)
        | ~ v2_pre_topc(X5)
        | v2_struct_0(X5)
        | ~ m1_pre_topc(X4,sK1)
        | v2_struct_0(X4)
        | ~ m1_pre_topc(X4,sK0) )
    | ~ spl7_92 ),
    inference(resolution,[],[f68,f705])).

fof(f934,plain,
    ( ~ spl7_37
    | spl7_34
    | ~ spl7_112
    | spl7_4
    | ~ spl7_92 ),
    inference(avatar_split_clause,[],[f929,f704,f93,f931,f302,f322])).

fof(f931,plain,
    ( spl7_112
  <=> m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_112])])).

fof(f929,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK1)
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK3))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
    | spl7_4
    | ~ spl7_92 ),
    inference(resolution,[],[f94,f705])).

fof(f927,plain,
    ( spl7_14
    | ~ spl7_13
    | ~ spl7_111
    | ~ spl7_26
    | spl7_62
    | ~ spl7_100 ),
    inference(avatar_split_clause,[],[f922,f776,f498,f217,f924,f138,f143])).

fof(f924,plain,
    ( spl7_111
  <=> m1_pre_topc(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_111])])).

fof(f498,plain,
    ( spl7_62
  <=> r1_tsep_1(sK1,k2_tsep_1(sK0,sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_62])])).

fof(f922,plain,
    ( ~ l1_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | spl7_62
    | ~ spl7_100 ),
    inference(resolution,[],[f499,f777])).

fof(f499,plain,
    ( ~ r1_tsep_1(sK1,k2_tsep_1(sK0,sK2,sK4))
    | spl7_62 ),
    inference(avatar_component_clause,[],[f498])).

fof(f909,plain,
    ( spl7_33
    | spl7_110
    | ~ spl7_73 ),
    inference(avatar_split_clause,[],[f896,f557,f907,f298])).

fof(f907,plain,
    ( spl7_110
  <=> ! [X5,X4,X6] :
        ( v2_struct_0(k1_tsep_1(X4,X5,k2_tsep_1(sK0,sK2,sK4)))
        | v2_struct_0(X4)
        | ~ v2_pre_topc(X4)
        | ~ l1_pre_topc(X4)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X4)
        | v2_struct_0(X5)
        | ~ m1_pre_topc(X5,X4)
        | ~ m1_pre_topc(X6,sK1)
        | ~ m1_pre_topc(sK1,k1_tsep_1(X4,X5,k2_tsep_1(sK0,sK2,sK4)))
        | r1_tsep_1(X6,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X6,k1_tsep_1(X4,X5,k2_tsep_1(sK0,sK2,sK4)))
        | v2_struct_0(X6)
        | ~ l1_pre_topc(k1_tsep_1(X4,X5,k2_tsep_1(sK0,sK2,sK4)))
        | ~ v2_pre_topc(k1_tsep_1(X4,X5,k2_tsep_1(sK0,sK2,sK4))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_110])])).

fof(f557,plain,
    ( spl7_73
  <=> ! [X3,X2] :
        ( r1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4))
        | v2_struct_0(X3)
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X3)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X3)
        | ~ m1_pre_topc(sK1,X3)
        | ~ m1_pre_topc(X2,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_73])])).

fof(f896,plain,
    ( ! [X6,X4,X5] :
        ( v2_struct_0(k1_tsep_1(X4,X5,k2_tsep_1(sK0,sK2,sK4)))
        | ~ v2_pre_topc(k1_tsep_1(X4,X5,k2_tsep_1(sK0,sK2,sK4)))
        | ~ l1_pre_topc(k1_tsep_1(X4,X5,k2_tsep_1(sK0,sK2,sK4)))
        | v2_struct_0(X6)
        | ~ m1_pre_topc(X6,k1_tsep_1(X4,X5,k2_tsep_1(sK0,sK2,sK4)))
        | r1_tsep_1(X6,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(sK1,k1_tsep_1(X4,X5,k2_tsep_1(sK0,sK2,sK4)))
        | ~ m1_pre_topc(X6,sK1)
        | ~ m1_pre_topc(X5,X4)
        | v2_struct_0(X5)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X4)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ l1_pre_topc(X4)
        | ~ v2_pre_topc(X4)
        | v2_struct_0(X4) )
    | ~ spl7_73 ),
    inference(resolution,[],[f558,f289])).

fof(f558,plain,
    ( ! [X2,X3] :
        ( ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X3)
        | v2_struct_0(X3)
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X3)
        | r1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(sK1,X3)
        | ~ m1_pre_topc(X2,sK1) )
    | ~ spl7_73 ),
    inference(avatar_component_clause,[],[f557])).

fof(f905,plain,
    ( spl7_33
    | spl7_109
    | ~ spl7_73 ),
    inference(avatar_split_clause,[],[f895,f557,f903,f298])).

fof(f903,plain,
    ( spl7_109
  <=> ! [X1,X3,X2] :
        ( v2_struct_0(k1_tsep_1(X1,k2_tsep_1(sK0,sK2,sK4),X2))
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X1)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X1)
        | ~ m1_pre_topc(X3,sK1)
        | ~ m1_pre_topc(sK1,k1_tsep_1(X1,k2_tsep_1(sK0,sK2,sK4),X2))
        | r1_tsep_1(X3,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X3,k1_tsep_1(X1,k2_tsep_1(sK0,sK2,sK4),X2))
        | v2_struct_0(X3)
        | ~ l1_pre_topc(k1_tsep_1(X1,k2_tsep_1(sK0,sK2,sK4),X2))
        | ~ v2_pre_topc(k1_tsep_1(X1,k2_tsep_1(sK0,sK2,sK4),X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_109])])).

fof(f895,plain,
    ( ! [X2,X3,X1] :
        ( v2_struct_0(k1_tsep_1(X1,k2_tsep_1(sK0,sK2,sK4),X2))
        | ~ v2_pre_topc(k1_tsep_1(X1,k2_tsep_1(sK0,sK2,sK4),X2))
        | ~ l1_pre_topc(k1_tsep_1(X1,k2_tsep_1(sK0,sK2,sK4),X2))
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,k1_tsep_1(X1,k2_tsep_1(sK0,sK2,sK4),X2))
        | r1_tsep_1(X3,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(sK1,k1_tsep_1(X1,k2_tsep_1(sK0,sK2,sK4),X2))
        | ~ m1_pre_topc(X3,sK1)
        | ~ m1_pre_topc(X2,X1)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X1)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl7_73 ),
    inference(resolution,[],[f558,f61])).

fof(f901,plain,
    ( spl7_12
    | ~ spl7_11
    | spl7_8
    | ~ spl7_7
    | ~ spl7_13
    | spl7_108
    | ~ spl7_15
    | ~ spl7_16
    | spl7_17
    | ~ spl7_73 ),
    inference(avatar_split_clause,[],[f897,f557,f158,f153,f148,f899,f138,f108,f113,f128,f133])).

fof(f897,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | r1_tsep_1(X0,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(sK1,sK0)
        | ~ m1_pre_topc(X0,sK1)
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2) )
    | ~ spl7_73 ),
    inference(duplicate_literal_removal,[],[f894])).

fof(f894,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | r1_tsep_1(X0,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(sK1,sK0)
        | ~ m1_pre_topc(X0,sK1)
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl7_73 ),
    inference(resolution,[],[f558,f77])).

fof(f859,plain,
    ( ~ spl7_13
    | spl7_2
    | spl7_14
    | ~ spl7_6
    | ~ spl7_95 ),
    inference(avatar_split_clause,[],[f836,f739,f103,f143,f84,f138])).

fof(f84,plain,
    ( spl7_2
  <=> r1_tsep_1(sK4,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f739,plain,
    ( spl7_95
  <=> ! [X0] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK2)
        | r1_tsep_1(sK4,X0)
        | ~ m1_pre_topc(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_95])])).

fof(f836,plain,
    ( v2_struct_0(sK1)
    | r1_tsep_1(sK4,sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ spl7_6
    | ~ spl7_95 ),
    inference(resolution,[],[f740,f105])).

fof(f105,plain,
    ( m1_pre_topc(sK1,sK2)
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f103])).

fof(f740,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK2)
        | v2_struct_0(X0)
        | r1_tsep_1(sK4,X0)
        | ~ m1_pre_topc(X0,sK0) )
    | ~ spl7_95 ),
    inference(avatar_component_clause,[],[f739])).

fof(f858,plain,
    ( spl7_8
    | spl7_107
    | ~ spl7_90 ),
    inference(avatar_split_clause,[],[f846,f673,f856,f113])).

fof(f856,plain,
    ( spl7_107
  <=> ! [X5,X4,X6] :
        ( v2_struct_0(k1_tsep_1(X4,X5,sK4))
        | v2_struct_0(X4)
        | ~ v2_pre_topc(X4)
        | ~ l1_pre_topc(X4)
        | ~ m1_pre_topc(sK4,X4)
        | v2_struct_0(X5)
        | ~ m1_pre_topc(X5,X4)
        | ~ m1_pre_topc(X6,sK4)
        | r1_tsep_1(sK1,X6)
        | ~ m1_pre_topc(sK1,k1_tsep_1(X4,X5,sK4))
        | ~ m1_pre_topc(X6,k1_tsep_1(X4,X5,sK4))
        | v2_struct_0(X6)
        | ~ l1_pre_topc(k1_tsep_1(X4,X5,sK4))
        | ~ v2_pre_topc(k1_tsep_1(X4,X5,sK4)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_107])])).

fof(f673,plain,
    ( spl7_90
  <=> ! [X1,X0] :
        ( r1_tsep_1(sK1,X0)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,X1)
        | ~ m1_pre_topc(sK1,X1)
        | ~ m1_pre_topc(sK4,X1)
        | ~ m1_pre_topc(X0,sK4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_90])])).

fof(f846,plain,
    ( ! [X6,X4,X5] :
        ( v2_struct_0(k1_tsep_1(X4,X5,sK4))
        | ~ v2_pre_topc(k1_tsep_1(X4,X5,sK4))
        | ~ l1_pre_topc(k1_tsep_1(X4,X5,sK4))
        | v2_struct_0(X6)
        | ~ m1_pre_topc(X6,k1_tsep_1(X4,X5,sK4))
        | ~ m1_pre_topc(sK1,k1_tsep_1(X4,X5,sK4))
        | r1_tsep_1(sK1,X6)
        | ~ m1_pre_topc(X6,sK4)
        | ~ m1_pre_topc(X5,X4)
        | v2_struct_0(X5)
        | ~ m1_pre_topc(sK4,X4)
        | v2_struct_0(sK4)
        | ~ l1_pre_topc(X4)
        | ~ v2_pre_topc(X4)
        | v2_struct_0(X4) )
    | ~ spl7_90 ),
    inference(resolution,[],[f674,f289])).

fof(f674,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(sK4,X1)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,X1)
        | ~ m1_pre_topc(sK1,X1)
        | r1_tsep_1(sK1,X0)
        | ~ m1_pre_topc(X0,sK4) )
    | ~ spl7_90 ),
    inference(avatar_component_clause,[],[f673])).

fof(f854,plain,
    ( spl7_8
    | spl7_106
    | ~ spl7_90 ),
    inference(avatar_split_clause,[],[f845,f673,f852,f113])).

fof(f852,plain,
    ( spl7_106
  <=> ! [X1,X3,X2] :
        ( v2_struct_0(k1_tsep_1(X1,sK4,X2))
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ m1_pre_topc(sK4,X1)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X1)
        | ~ m1_pre_topc(X3,sK4)
        | r1_tsep_1(sK1,X3)
        | ~ m1_pre_topc(sK1,k1_tsep_1(X1,sK4,X2))
        | ~ m1_pre_topc(X3,k1_tsep_1(X1,sK4,X2))
        | v2_struct_0(X3)
        | ~ l1_pre_topc(k1_tsep_1(X1,sK4,X2))
        | ~ v2_pre_topc(k1_tsep_1(X1,sK4,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_106])])).

fof(f845,plain,
    ( ! [X2,X3,X1] :
        ( v2_struct_0(k1_tsep_1(X1,sK4,X2))
        | ~ v2_pre_topc(k1_tsep_1(X1,sK4,X2))
        | ~ l1_pre_topc(k1_tsep_1(X1,sK4,X2))
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,k1_tsep_1(X1,sK4,X2))
        | ~ m1_pre_topc(sK1,k1_tsep_1(X1,sK4,X2))
        | r1_tsep_1(sK1,X3)
        | ~ m1_pre_topc(X3,sK4)
        | ~ m1_pre_topc(X2,X1)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(sK4,X1)
        | v2_struct_0(sK4)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl7_90 ),
    inference(resolution,[],[f674,f61])).

fof(f850,plain,
    ( ~ spl7_13
    | spl7_105
    | ~ spl7_15
    | ~ spl7_16
    | spl7_17
    | ~ spl7_7
    | ~ spl7_90 ),
    inference(avatar_split_clause,[],[f844,f673,f108,f158,f153,f148,f848,f138])).

fof(f844,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(sK1,sK0)
        | r1_tsep_1(sK1,X0)
        | ~ m1_pre_topc(X0,sK4) )
    | ~ spl7_7
    | ~ spl7_90 ),
    inference(resolution,[],[f674,f110])).

fof(f827,plain,
    ( spl7_33
    | spl7_104
    | ~ spl7_100 ),
    inference(avatar_split_clause,[],[f818,f776,f825,f298])).

fof(f825,plain,
    ( spl7_104
  <=> ! [X3,X5,X4] :
        ( ~ l1_struct_0(X3)
        | v2_struct_0(X5)
        | ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X5)
        | v2_struct_0(X4)
        | ~ m1_pre_topc(X4,X5)
        | ~ m1_pre_topc(X3,X5)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X5)
        | r1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X4,X3)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,sK0)
        | ~ m1_pre_topc(X3,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_104])])).

fof(f818,plain,
    ( ! [X4,X5,X3] :
        ( ~ l1_struct_0(X3)
        | ~ m1_pre_topc(X3,sK1)
        | ~ m1_pre_topc(X3,sK0)
        | v2_struct_0(X3)
        | r1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X4,X3)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X5)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X3,X5)
        | ~ m1_pre_topc(X4,X5)
        | v2_struct_0(X4)
        | ~ l1_pre_topc(X5)
        | ~ v2_pre_topc(X5)
        | v2_struct_0(X5) )
    | ~ spl7_100 ),
    inference(duplicate_literal_removal,[],[f815])).

fof(f815,plain,
    ( ! [X4,X5,X3] :
        ( ~ l1_struct_0(X3)
        | ~ m1_pre_topc(X3,sK1)
        | ~ m1_pre_topc(X3,sK0)
        | v2_struct_0(X3)
        | r1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X4,X3)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X5)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X3,X5)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X4,X5)
        | v2_struct_0(X4)
        | ~ l1_pre_topc(X5)
        | ~ v2_pre_topc(X5)
        | v2_struct_0(X5) )
    | ~ spl7_100 ),
    inference(resolution,[],[f777,f66])).

fof(f823,plain,
    ( spl7_33
    | spl7_103
    | ~ spl7_100 ),
    inference(avatar_split_clause,[],[f819,f776,f821,f298])).

fof(f821,plain,
    ( spl7_103
  <=> ! [X1,X0,X2] :
        ( ~ l1_struct_0(X0)
        | v2_struct_0(X2)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X2)
        | ~ m1_pre_topc(X0,X2)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X2)
        | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X1)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_103])])).

fof(f819,plain,
    ( ! [X2,X0,X1] :
        ( ~ l1_struct_0(X0)
        | ~ m1_pre_topc(X0,sK1)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X1)
        | ~ m1_pre_topc(X1,X0)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X2)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X0,X2)
        | ~ m1_pre_topc(X1,X2)
        | v2_struct_0(X1)
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2)
        | v2_struct_0(X2) )
    | ~ spl7_100 ),
    inference(duplicate_literal_removal,[],[f814])).

fof(f814,plain,
    ( ! [X2,X0,X1] :
        ( ~ l1_struct_0(X0)
        | ~ m1_pre_topc(X0,sK1)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X1)
        | ~ m1_pre_topc(X1,X0)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X2)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X0,X2)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X1,X2)
        | v2_struct_0(X1)
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2)
        | v2_struct_0(X2) )
    | ~ spl7_100 ),
    inference(resolution,[],[f777,f67])).

fof(f796,plain,
    ( spl7_12
    | ~ spl7_21
    | spl7_102
    | ~ spl7_95 ),
    inference(avatar_split_clause,[],[f786,f739,f794,f188,f133])).

fof(f188,plain,
    ( spl7_21
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).

fof(f794,plain,
    ( spl7_102
  <=> ! [X3,X2] :
        ( v2_struct_0(k2_tsep_1(sK2,X2,X3))
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,sK2)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,sK2)
        | ~ m1_pre_topc(k2_tsep_1(sK2,X2,X3),sK0)
        | r1_tsep_1(sK4,k2_tsep_1(sK2,X2,X3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_102])])).

fof(f786,plain,
    ( ! [X2,X3] :
        ( v2_struct_0(k2_tsep_1(sK2,X2,X3))
        | r1_tsep_1(sK4,k2_tsep_1(sK2,X2,X3))
        | ~ m1_pre_topc(k2_tsep_1(sK2,X2,X3),sK0)
        | ~ m1_pre_topc(X3,sK2)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X2,sK2)
        | v2_struct_0(X2)
        | ~ l1_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | ~ spl7_95 ),
    inference(resolution,[],[f740,f77])).

fof(f792,plain,
    ( spl7_12
    | ~ spl7_21
    | spl7_101
    | ~ spl7_95 ),
    inference(avatar_split_clause,[],[f785,f739,f790,f188,f133])).

fof(f790,plain,
    ( spl7_101
  <=> ! [X1,X0] :
        ( v2_struct_0(k1_tsep_1(sK2,X0,X1))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK2)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK2)
        | ~ m1_pre_topc(k1_tsep_1(sK2,X0,X1),sK0)
        | r1_tsep_1(sK4,k1_tsep_1(sK2,X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_101])])).

fof(f785,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(k1_tsep_1(sK2,X0,X1))
        | r1_tsep_1(sK4,k1_tsep_1(sK2,X0,X1))
        | ~ m1_pre_topc(k1_tsep_1(sK2,X0,X1),sK0)
        | ~ m1_pre_topc(X1,sK2)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X0,sK2)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | ~ spl7_95 ),
    inference(resolution,[],[f740,f74])).

fof(f778,plain,
    ( ~ spl7_30
    | spl7_100
    | ~ spl7_92 ),
    inference(avatar_split_clause,[],[f764,f704,f776,f242])).

fof(f764,plain,
    ( ! [X6] :
        ( ~ m1_pre_topc(X6,sK1)
        | v2_struct_0(X6)
        | ~ m1_pre_topc(X6,sK0)
        | r1_tsep_1(X6,k2_tsep_1(sK0,sK2,sK4))
        | ~ l1_struct_0(X6)
        | ~ l1_struct_0(k2_tsep_1(sK0,sK2,sK4)) )
    | ~ spl7_92 ),
    inference(resolution,[],[f705,f70])).

fof(f774,plain,
    ( spl7_33
    | spl7_99
    | ~ spl7_92 ),
    inference(avatar_split_clause,[],[f765,f704,f772,f298])).

fof(f772,plain,
    ( spl7_99
  <=> ! [X3,X5,X4] :
        ( ~ m1_pre_topc(X3,sK1)
        | v2_struct_0(X5)
        | ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X5)
        | v2_struct_0(X4)
        | ~ m1_pre_topc(X4,X5)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X5)
        | ~ m1_pre_topc(X3,X5)
        | ~ m1_pre_topc(X4,k2_tsep_1(sK0,sK2,sK4))
        | r1_tsep_1(X4,X3)
        | ~ m1_pre_topc(X3,sK0)
        | v2_struct_0(X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_99])])).

fof(f765,plain,
    ( ! [X4,X5,X3] :
        ( ~ m1_pre_topc(X3,sK1)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,sK0)
        | r1_tsep_1(X4,X3)
        | ~ m1_pre_topc(X4,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X3,X5)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X5)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X4,X5)
        | v2_struct_0(X4)
        | ~ l1_pre_topc(X5)
        | ~ v2_pre_topc(X5)
        | v2_struct_0(X5) )
    | ~ spl7_92 ),
    inference(duplicate_literal_removal,[],[f763])).

fof(f763,plain,
    ( ! [X4,X5,X3] :
        ( ~ m1_pre_topc(X3,sK1)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,sK0)
        | r1_tsep_1(X4,X3)
        | ~ m1_pre_topc(X4,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X3,X5)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X5)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X4,X5)
        | v2_struct_0(X4)
        | ~ l1_pre_topc(X5)
        | ~ v2_pre_topc(X5)
        | v2_struct_0(X5) )
    | ~ spl7_92 ),
    inference(resolution,[],[f705,f66])).

fof(f770,plain,
    ( spl7_33
    | spl7_98
    | ~ spl7_92 ),
    inference(avatar_split_clause,[],[f766,f704,f768,f298])).

fof(f768,plain,
    ( spl7_98
  <=> ! [X1,X0,X2] :
        ( ~ m1_pre_topc(X0,sK1)
        | v2_struct_0(X2)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X2)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X2)
        | ~ m1_pre_topc(X0,X2)
        | ~ m1_pre_topc(X1,k2_tsep_1(sK0,sK2,sK4))
        | r1_tsep_1(X0,X1)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_98])])).

fof(f766,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_pre_topc(X0,sK1)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | r1_tsep_1(X0,X1)
        | ~ m1_pre_topc(X1,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X0,X2)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X2)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X1,X2)
        | v2_struct_0(X1)
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2)
        | v2_struct_0(X2) )
    | ~ spl7_92 ),
    inference(duplicate_literal_removal,[],[f762])).

fof(f762,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_pre_topc(X0,sK1)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | r1_tsep_1(X0,X1)
        | ~ m1_pre_topc(X1,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X0,X2)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X2)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X1,X2)
        | v2_struct_0(X1)
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2)
        | v2_struct_0(X2) )
    | ~ spl7_92 ),
    inference(resolution,[],[f705,f67])).

fof(f749,plain,
    ( spl7_8
    | spl7_97
    | ~ spl7_57 ),
    inference(avatar_split_clause,[],[f737,f438,f747,f113])).

fof(f747,plain,
    ( spl7_97
  <=> ! [X5,X4,X6] :
        ( v2_struct_0(k1_tsep_1(X4,X5,sK4))
        | v2_struct_0(X4)
        | ~ v2_pre_topc(X4)
        | ~ l1_pre_topc(X4)
        | ~ m1_pre_topc(sK4,X4)
        | v2_struct_0(X5)
        | ~ m1_pre_topc(X5,X4)
        | ~ m1_pre_topc(X6,sK2)
        | ~ m1_pre_topc(sK2,k1_tsep_1(X4,X5,sK4))
        | r1_tsep_1(sK4,X6)
        | ~ m1_pre_topc(X6,k1_tsep_1(X4,X5,sK4))
        | v2_struct_0(X6)
        | ~ l1_pre_topc(k1_tsep_1(X4,X5,sK4))
        | ~ v2_pre_topc(k1_tsep_1(X4,X5,sK4)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_97])])).

fof(f438,plain,
    ( spl7_57
  <=> ! [X1,X0] :
        ( r1_tsep_1(sK4,X0)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,X1)
        | ~ m1_pre_topc(sK4,X1)
        | ~ m1_pre_topc(sK2,X1)
        | ~ m1_pre_topc(X0,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_57])])).

fof(f737,plain,
    ( ! [X6,X4,X5] :
        ( v2_struct_0(k1_tsep_1(X4,X5,sK4))
        | ~ v2_pre_topc(k1_tsep_1(X4,X5,sK4))
        | ~ l1_pre_topc(k1_tsep_1(X4,X5,sK4))
        | v2_struct_0(X6)
        | ~ m1_pre_topc(X6,k1_tsep_1(X4,X5,sK4))
        | r1_tsep_1(sK4,X6)
        | ~ m1_pre_topc(sK2,k1_tsep_1(X4,X5,sK4))
        | ~ m1_pre_topc(X6,sK2)
        | ~ m1_pre_topc(X5,X4)
        | v2_struct_0(X5)
        | ~ m1_pre_topc(sK4,X4)
        | v2_struct_0(sK4)
        | ~ l1_pre_topc(X4)
        | ~ v2_pre_topc(X4)
        | v2_struct_0(X4) )
    | ~ spl7_57 ),
    inference(resolution,[],[f439,f289])).

fof(f439,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(sK4,X1)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,X1)
        | r1_tsep_1(sK4,X0)
        | ~ m1_pre_topc(sK2,X1)
        | ~ m1_pre_topc(X0,sK2) )
    | ~ spl7_57 ),
    inference(avatar_component_clause,[],[f438])).

fof(f745,plain,
    ( spl7_8
    | spl7_96
    | ~ spl7_57 ),
    inference(avatar_split_clause,[],[f736,f438,f743,f113])).

fof(f743,plain,
    ( spl7_96
  <=> ! [X1,X3,X2] :
        ( v2_struct_0(k1_tsep_1(X1,sK4,X2))
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ m1_pre_topc(sK4,X1)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X1)
        | ~ m1_pre_topc(X3,sK2)
        | ~ m1_pre_topc(sK2,k1_tsep_1(X1,sK4,X2))
        | r1_tsep_1(sK4,X3)
        | ~ m1_pre_topc(X3,k1_tsep_1(X1,sK4,X2))
        | v2_struct_0(X3)
        | ~ l1_pre_topc(k1_tsep_1(X1,sK4,X2))
        | ~ v2_pre_topc(k1_tsep_1(X1,sK4,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_96])])).

fof(f736,plain,
    ( ! [X2,X3,X1] :
        ( v2_struct_0(k1_tsep_1(X1,sK4,X2))
        | ~ v2_pre_topc(k1_tsep_1(X1,sK4,X2))
        | ~ l1_pre_topc(k1_tsep_1(X1,sK4,X2))
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,k1_tsep_1(X1,sK4,X2))
        | r1_tsep_1(sK4,X3)
        | ~ m1_pre_topc(sK2,k1_tsep_1(X1,sK4,X2))
        | ~ m1_pre_topc(X3,sK2)
        | ~ m1_pre_topc(X2,X1)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(sK4,X1)
        | v2_struct_0(sK4)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl7_57 ),
    inference(resolution,[],[f439,f61])).

fof(f741,plain,
    ( ~ spl7_11
    | spl7_95
    | ~ spl7_15
    | ~ spl7_16
    | spl7_17
    | ~ spl7_7
    | ~ spl7_57 ),
    inference(avatar_split_clause,[],[f735,f438,f108,f158,f153,f148,f739,f128])).

fof(f735,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | r1_tsep_1(sK4,X0)
        | ~ m1_pre_topc(sK2,sK0)
        | ~ m1_pre_topc(X0,sK2) )
    | ~ spl7_7
    | ~ spl7_57 ),
    inference(resolution,[],[f439,f110])).

fof(f715,plain,
    ( ~ spl7_30
    | ~ spl7_26
    | spl7_62
    | ~ spl7_74 ),
    inference(avatar_split_clause,[],[f657,f561,f498,f217,f242])).

fof(f657,plain,
    ( r1_tsep_1(sK1,k2_tsep_1(sK0,sK2,sK4))
    | ~ l1_struct_0(sK1)
    | ~ l1_struct_0(k2_tsep_1(sK0,sK2,sK4))
    | ~ spl7_74 ),
    inference(resolution,[],[f563,f70])).

fof(f714,plain,
    ( spl7_33
    | spl7_94
    | ~ spl7_72 ),
    inference(avatar_split_clause,[],[f701,f553,f712,f298])).

fof(f712,plain,
    ( spl7_94
  <=> ! [X5,X4,X6] :
        ( v2_struct_0(k1_tsep_1(X4,X5,k2_tsep_1(sK0,sK2,sK4)))
        | v2_struct_0(X4)
        | ~ v2_pre_topc(X4)
        | ~ l1_pre_topc(X4)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X4)
        | v2_struct_0(X5)
        | ~ m1_pre_topc(X5,X4)
        | ~ m1_pre_topc(X6,sK1)
        | ~ m1_pre_topc(sK1,k1_tsep_1(X4,X5,k2_tsep_1(sK0,sK2,sK4)))
        | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X6)
        | ~ m1_pre_topc(X6,k1_tsep_1(X4,X5,k2_tsep_1(sK0,sK2,sK4)))
        | v2_struct_0(X6)
        | ~ l1_pre_topc(k1_tsep_1(X4,X5,k2_tsep_1(sK0,sK2,sK4)))
        | ~ v2_pre_topc(k1_tsep_1(X4,X5,k2_tsep_1(sK0,sK2,sK4))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_94])])).

fof(f553,plain,
    ( spl7_72
  <=> ! [X1,X0] :
        ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X0)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,X1)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X1)
        | ~ m1_pre_topc(sK1,X1)
        | ~ m1_pre_topc(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_72])])).

fof(f701,plain,
    ( ! [X6,X4,X5] :
        ( v2_struct_0(k1_tsep_1(X4,X5,k2_tsep_1(sK0,sK2,sK4)))
        | ~ v2_pre_topc(k1_tsep_1(X4,X5,k2_tsep_1(sK0,sK2,sK4)))
        | ~ l1_pre_topc(k1_tsep_1(X4,X5,k2_tsep_1(sK0,sK2,sK4)))
        | v2_struct_0(X6)
        | ~ m1_pre_topc(X6,k1_tsep_1(X4,X5,k2_tsep_1(sK0,sK2,sK4)))
        | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X6)
        | ~ m1_pre_topc(sK1,k1_tsep_1(X4,X5,k2_tsep_1(sK0,sK2,sK4)))
        | ~ m1_pre_topc(X6,sK1)
        | ~ m1_pre_topc(X5,X4)
        | v2_struct_0(X5)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X4)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ l1_pre_topc(X4)
        | ~ v2_pre_topc(X4)
        | v2_struct_0(X4) )
    | ~ spl7_72 ),
    inference(resolution,[],[f554,f289])).

fof(f554,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X1)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,X1)
        | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X0)
        | ~ m1_pre_topc(sK1,X1)
        | ~ m1_pre_topc(X0,sK1) )
    | ~ spl7_72 ),
    inference(avatar_component_clause,[],[f553])).

fof(f710,plain,
    ( spl7_33
    | spl7_93
    | ~ spl7_72 ),
    inference(avatar_split_clause,[],[f700,f553,f708,f298])).

fof(f708,plain,
    ( spl7_93
  <=> ! [X1,X3,X2] :
        ( v2_struct_0(k1_tsep_1(X1,k2_tsep_1(sK0,sK2,sK4),X2))
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X1)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X1)
        | ~ m1_pre_topc(X3,sK1)
        | ~ m1_pre_topc(sK1,k1_tsep_1(X1,k2_tsep_1(sK0,sK2,sK4),X2))
        | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X3)
        | ~ m1_pre_topc(X3,k1_tsep_1(X1,k2_tsep_1(sK0,sK2,sK4),X2))
        | v2_struct_0(X3)
        | ~ l1_pre_topc(k1_tsep_1(X1,k2_tsep_1(sK0,sK2,sK4),X2))
        | ~ v2_pre_topc(k1_tsep_1(X1,k2_tsep_1(sK0,sK2,sK4),X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_93])])).

fof(f700,plain,
    ( ! [X2,X3,X1] :
        ( v2_struct_0(k1_tsep_1(X1,k2_tsep_1(sK0,sK2,sK4),X2))
        | ~ v2_pre_topc(k1_tsep_1(X1,k2_tsep_1(sK0,sK2,sK4),X2))
        | ~ l1_pre_topc(k1_tsep_1(X1,k2_tsep_1(sK0,sK2,sK4),X2))
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,k1_tsep_1(X1,k2_tsep_1(sK0,sK2,sK4),X2))
        | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X3)
        | ~ m1_pre_topc(sK1,k1_tsep_1(X1,k2_tsep_1(sK0,sK2,sK4),X2))
        | ~ m1_pre_topc(X3,sK1)
        | ~ m1_pre_topc(X2,X1)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X1)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl7_72 ),
    inference(resolution,[],[f554,f61])).

fof(f706,plain,
    ( spl7_12
    | ~ spl7_11
    | spl7_8
    | ~ spl7_7
    | ~ spl7_13
    | spl7_92
    | ~ spl7_15
    | ~ spl7_16
    | spl7_17
    | ~ spl7_72 ),
    inference(avatar_split_clause,[],[f702,f553,f158,f153,f148,f704,f138,f108,f113,f128,f133])).

fof(f702,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X0)
        | ~ m1_pre_topc(sK1,sK0)
        | ~ m1_pre_topc(X0,sK1)
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2) )
    | ~ spl7_72 ),
    inference(duplicate_literal_removal,[],[f699])).

fof(f699,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X0)
        | ~ m1_pre_topc(sK1,sK0)
        | ~ m1_pre_topc(X0,sK1)
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl7_72 ),
    inference(resolution,[],[f554,f77])).

fof(f679,plain,
    ( spl7_8
    | spl7_14
    | spl7_91
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f670,f84,f677,f143,f113])).

fof(f670,plain,
    ( ! [X2,X3] :
        ( r1_tsep_1(X2,sK1)
        | ~ m1_pre_topc(X2,sK4)
        | ~ m1_pre_topc(sK1,X3)
        | v2_struct_0(sK1)
        | ~ m1_pre_topc(sK4,X3)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(X2,X3)
        | v2_struct_0(X2)
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(X3)
        | v2_struct_0(X3) )
    | ~ spl7_2 ),
    inference(resolution,[],[f85,f66])).

fof(f85,plain,
    ( r1_tsep_1(sK4,sK1)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f84])).

fof(f675,plain,
    ( spl7_8
    | spl7_14
    | spl7_90
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f669,f84,f673,f143,f113])).

fof(f669,plain,
    ( ! [X0,X1] :
        ( r1_tsep_1(sK1,X0)
        | ~ m1_pre_topc(X0,sK4)
        | ~ m1_pre_topc(sK1,X1)
        | v2_struct_0(sK1)
        | ~ m1_pre_topc(sK4,X1)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(X0,X1)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl7_2 ),
    inference(resolution,[],[f85,f67])).

fof(f668,plain,
    ( spl7_33
    | spl7_10
    | spl7_89
    | ~ spl7_77 ),
    inference(avatar_split_clause,[],[f659,f583,f666,f123,f298])).

fof(f666,plain,
    ( spl7_89
  <=> ! [X3,X2] :
        ( r1_tsep_1(X2,sK3)
        | v2_struct_0(X3)
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X3)
        | ~ m1_pre_topc(sK3,X3)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X3)
        | ~ m1_pre_topc(X2,k2_tsep_1(sK0,sK2,sK4)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_89])])).

fof(f659,plain,
    ( ! [X2,X3] :
        ( r1_tsep_1(X2,sK3)
        | ~ m1_pre_topc(X2,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(sK3,X3)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X3)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X2,X3)
        | v2_struct_0(X2)
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(X3)
        | v2_struct_0(X3) )
    | ~ spl7_77 ),
    inference(resolution,[],[f585,f66])).

fof(f664,plain,
    ( spl7_33
    | spl7_10
    | spl7_88
    | ~ spl7_77 ),
    inference(avatar_split_clause,[],[f658,f583,f662,f123,f298])).

fof(f662,plain,
    ( spl7_88
  <=> ! [X1,X0] :
        ( r1_tsep_1(sK3,X0)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,X1)
        | ~ m1_pre_topc(sK3,X1)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X1)
        | ~ m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_88])])).

fof(f658,plain,
    ( ! [X0,X1] :
        ( r1_tsep_1(sK3,X0)
        | ~ m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(sK3,X1)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X1)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X0,X1)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl7_77 ),
    inference(resolution,[],[f585,f67])).

fof(f651,plain,
    ( ~ spl7_26
    | ~ spl7_27
    | spl7_2
    | ~ spl7_80 ),
    inference(avatar_split_clause,[],[f642,f600,f84,f223,f217])).

fof(f223,plain,
    ( spl7_27
  <=> l1_struct_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).

fof(f642,plain,
    ( r1_tsep_1(sK4,sK1)
    | ~ l1_struct_0(sK4)
    | ~ l1_struct_0(sK1)
    | ~ spl7_80 ),
    inference(resolution,[],[f602,f70])).

fof(f602,plain,
    ( r1_tsep_1(sK1,sK4)
    | ~ spl7_80 ),
    inference(avatar_component_clause,[],[f600])).

fof(f650,plain,
    ( spl7_14
    | spl7_8
    | spl7_87
    | ~ spl7_80 ),
    inference(avatar_split_clause,[],[f641,f600,f648,f113,f143])).

fof(f648,plain,
    ( spl7_87
  <=> ! [X3,X2] :
        ( r1_tsep_1(X2,sK4)
        | v2_struct_0(X3)
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X3)
        | ~ m1_pre_topc(sK4,X3)
        | ~ m1_pre_topc(sK1,X3)
        | ~ m1_pre_topc(X2,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_87])])).

fof(f641,plain,
    ( ! [X2,X3] :
        ( r1_tsep_1(X2,sK4)
        | ~ m1_pre_topc(X2,sK1)
        | ~ m1_pre_topc(sK4,X3)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK1,X3)
        | v2_struct_0(sK1)
        | ~ m1_pre_topc(X2,X3)
        | v2_struct_0(X2)
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(X3)
        | v2_struct_0(X3) )
    | ~ spl7_80 ),
    inference(resolution,[],[f602,f66])).

fof(f646,plain,
    ( spl7_14
    | spl7_8
    | spl7_86
    | ~ spl7_80 ),
    inference(avatar_split_clause,[],[f640,f600,f644,f113,f143])).

fof(f644,plain,
    ( spl7_86
  <=> ! [X1,X0] :
        ( r1_tsep_1(sK4,X0)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,X1)
        | ~ m1_pre_topc(sK4,X1)
        | ~ m1_pre_topc(sK1,X1)
        | ~ m1_pre_topc(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_86])])).

fof(f640,plain,
    ( ! [X0,X1] :
        ( r1_tsep_1(sK4,X0)
        | ~ m1_pre_topc(X0,sK1)
        | ~ m1_pre_topc(sK4,X1)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK1,X1)
        | v2_struct_0(sK1)
        | ~ m1_pre_topc(X0,X1)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl7_80 ),
    inference(resolution,[],[f602,f67])).

fof(f633,plain,
    ( spl7_33
    | spl7_14
    | spl7_85
    | ~ spl7_74 ),
    inference(avatar_split_clause,[],[f624,f561,f631,f143,f298])).

fof(f631,plain,
    ( spl7_85
  <=> ! [X3,X2] :
        ( r1_tsep_1(X2,sK1)
        | v2_struct_0(X3)
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X3)
        | ~ m1_pre_topc(sK1,X3)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X3)
        | ~ m1_pre_topc(X2,k2_tsep_1(sK0,sK2,sK4)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_85])])).

fof(f624,plain,
    ( ! [X2,X3] :
        ( r1_tsep_1(X2,sK1)
        | ~ m1_pre_topc(X2,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(sK1,X3)
        | v2_struct_0(sK1)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X3)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X2,X3)
        | v2_struct_0(X2)
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(X3)
        | v2_struct_0(X3) )
    | ~ spl7_74 ),
    inference(resolution,[],[f563,f66])).

fof(f629,plain,
    ( spl7_33
    | spl7_14
    | spl7_84
    | ~ spl7_74 ),
    inference(avatar_split_clause,[],[f623,f561,f627,f143,f298])).

fof(f627,plain,
    ( spl7_84
  <=> ! [X1,X0] :
        ( r1_tsep_1(sK1,X0)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,X1)
        | ~ m1_pre_topc(sK1,X1)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X1)
        | ~ m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_84])])).

fof(f623,plain,
    ( ! [X0,X1] :
        ( r1_tsep_1(sK1,X0)
        | ~ m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(sK1,X1)
        | v2_struct_0(sK1)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X1)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X0,X1)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl7_74 ),
    inference(resolution,[],[f563,f67])).

fof(f616,plain,
    ( ~ spl7_21
    | ~ spl7_81
    | spl7_82
    | spl7_83
    | ~ spl7_69 ),
    inference(avatar_split_clause,[],[f590,f538,f613,f609,f605,f188])).

fof(f605,plain,
    ( spl7_81
  <=> m1_pre_topc(sK5(sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_81])])).

fof(f609,plain,
    ( spl7_82
  <=> r1_tsep_1(sK5(sK2),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_82])])).

fof(f613,plain,
    ( spl7_83
  <=> v2_struct_0(sK5(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_83])])).

fof(f538,plain,
    ( spl7_69
  <=> ! [X0] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK2)
        | r1_tsep_1(X0,sK4)
        | ~ m1_pre_topc(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_69])])).

fof(f590,plain,
    ( v2_struct_0(sK5(sK2))
    | r1_tsep_1(sK5(sK2),sK4)
    | ~ m1_pre_topc(sK5(sK2),sK0)
    | ~ l1_pre_topc(sK2)
    | ~ spl7_69 ),
    inference(resolution,[],[f539,f60])).

fof(f539,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK2)
        | v2_struct_0(X0)
        | r1_tsep_1(X0,sK4)
        | ~ m1_pre_topc(X0,sK0) )
    | ~ spl7_69 ),
    inference(avatar_component_clause,[],[f538])).

fof(f603,plain,
    ( ~ spl7_13
    | spl7_80
    | spl7_14
    | ~ spl7_6
    | ~ spl7_69 ),
    inference(avatar_split_clause,[],[f589,f538,f103,f143,f600,f138])).

fof(f589,plain,
    ( v2_struct_0(sK1)
    | r1_tsep_1(sK1,sK4)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ spl7_6
    | ~ spl7_69 ),
    inference(resolution,[],[f539,f105])).

fof(f598,plain,
    ( spl7_12
    | ~ spl7_21
    | spl7_79
    | ~ spl7_69 ),
    inference(avatar_split_clause,[],[f588,f538,f596,f188,f133])).

fof(f596,plain,
    ( spl7_79
  <=> ! [X3,X2] :
        ( v2_struct_0(k2_tsep_1(sK2,X2,X3))
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,sK2)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,sK2)
        | ~ m1_pre_topc(k2_tsep_1(sK2,X2,X3),sK0)
        | r1_tsep_1(k2_tsep_1(sK2,X2,X3),sK4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_79])])).

fof(f588,plain,
    ( ! [X2,X3] :
        ( v2_struct_0(k2_tsep_1(sK2,X2,X3))
        | r1_tsep_1(k2_tsep_1(sK2,X2,X3),sK4)
        | ~ m1_pre_topc(k2_tsep_1(sK2,X2,X3),sK0)
        | ~ m1_pre_topc(X3,sK2)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X2,sK2)
        | v2_struct_0(X2)
        | ~ l1_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | ~ spl7_69 ),
    inference(resolution,[],[f539,f77])).

fof(f594,plain,
    ( spl7_12
    | ~ spl7_21
    | spl7_78
    | ~ spl7_69 ),
    inference(avatar_split_clause,[],[f587,f538,f592,f188,f133])).

fof(f592,plain,
    ( spl7_78
  <=> ! [X1,X0] :
        ( v2_struct_0(k1_tsep_1(sK2,X0,X1))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK2)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK2)
        | ~ m1_pre_topc(k1_tsep_1(sK2,X0,X1),sK0)
        | r1_tsep_1(k1_tsep_1(sK2,X0,X1),sK4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_78])])).

fof(f587,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(k1_tsep_1(sK2,X0,X1))
        | r1_tsep_1(k1_tsep_1(sK2,X0,X1),sK4)
        | ~ m1_pre_topc(k1_tsep_1(sK2,X0,X1),sK0)
        | ~ m1_pre_topc(X1,sK2)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X0,sK2)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | ~ spl7_69 ),
    inference(resolution,[],[f539,f74])).

fof(f586,plain,
    ( ~ spl7_28
    | ~ spl7_30
    | spl7_77
    | ~ spl7_63 ),
    inference(avatar_split_clause,[],[f573,f503,f583,f242,f229])).

fof(f573,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),sK3)
    | ~ l1_struct_0(k2_tsep_1(sK0,sK2,sK4))
    | ~ l1_struct_0(sK3)
    | ~ spl7_63 ),
    inference(resolution,[],[f505,f70])).

fof(f505,plain,
    ( r1_tsep_1(sK3,k2_tsep_1(sK0,sK2,sK4))
    | ~ spl7_63 ),
    inference(avatar_component_clause,[],[f503])).

fof(f581,plain,
    ( spl7_10
    | spl7_33
    | spl7_76
    | ~ spl7_63 ),
    inference(avatar_split_clause,[],[f572,f503,f579,f298,f123])).

fof(f572,plain,
    ( ! [X2,X3] :
        ( r1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X2,sK3)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X3)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(sK3,X3)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(X2,X3)
        | v2_struct_0(X2)
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(X3)
        | v2_struct_0(X3) )
    | ~ spl7_63 ),
    inference(resolution,[],[f505,f66])).

fof(f577,plain,
    ( spl7_10
    | spl7_33
    | spl7_75
    | ~ spl7_63 ),
    inference(avatar_split_clause,[],[f571,f503,f575,f298,f123])).

fof(f571,plain,
    ( ! [X0,X1] :
        ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X0)
        | ~ m1_pre_topc(X0,sK3)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X1)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(sK3,X1)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(X0,X1)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl7_63 ),
    inference(resolution,[],[f505,f67])).

fof(f564,plain,
    ( ~ spl7_26
    | ~ spl7_30
    | spl7_74
    | ~ spl7_62 ),
    inference(avatar_split_clause,[],[f551,f498,f561,f242,f217])).

fof(f551,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),sK1)
    | ~ l1_struct_0(k2_tsep_1(sK0,sK2,sK4))
    | ~ l1_struct_0(sK1)
    | ~ spl7_62 ),
    inference(resolution,[],[f500,f70])).

fof(f500,plain,
    ( r1_tsep_1(sK1,k2_tsep_1(sK0,sK2,sK4))
    | ~ spl7_62 ),
    inference(avatar_component_clause,[],[f498])).

fof(f559,plain,
    ( spl7_14
    | spl7_33
    | spl7_73
    | ~ spl7_62 ),
    inference(avatar_split_clause,[],[f550,f498,f557,f298,f143])).

fof(f550,plain,
    ( ! [X2,X3] :
        ( r1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X2,sK1)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X3)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(sK1,X3)
        | v2_struct_0(sK1)
        | ~ m1_pre_topc(X2,X3)
        | v2_struct_0(X2)
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(X3)
        | v2_struct_0(X3) )
    | ~ spl7_62 ),
    inference(resolution,[],[f500,f66])).

fof(f555,plain,
    ( spl7_14
    | spl7_33
    | spl7_72
    | ~ spl7_62 ),
    inference(avatar_split_clause,[],[f549,f498,f553,f298,f143])).

fof(f549,plain,
    ( ! [X0,X1] :
        ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X0)
        | ~ m1_pre_topc(X0,sK1)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X1)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(sK1,X1)
        | v2_struct_0(sK1)
        | ~ m1_pre_topc(X0,X1)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl7_62 ),
    inference(resolution,[],[f500,f67])).

fof(f548,plain,
    ( spl7_8
    | spl7_71
    | ~ spl7_41 ),
    inference(avatar_split_clause,[],[f536,f341,f546,f113])).

fof(f546,plain,
    ( spl7_71
  <=> ! [X5,X4,X6] :
        ( v2_struct_0(k1_tsep_1(X4,X5,sK4))
        | v2_struct_0(X4)
        | ~ v2_pre_topc(X4)
        | ~ l1_pre_topc(X4)
        | ~ m1_pre_topc(sK4,X4)
        | v2_struct_0(X5)
        | ~ m1_pre_topc(X5,X4)
        | ~ m1_pre_topc(X6,sK2)
        | ~ m1_pre_topc(sK2,k1_tsep_1(X4,X5,sK4))
        | r1_tsep_1(X6,sK4)
        | ~ m1_pre_topc(X6,k1_tsep_1(X4,X5,sK4))
        | v2_struct_0(X6)
        | ~ l1_pre_topc(k1_tsep_1(X4,X5,sK4))
        | ~ v2_pre_topc(k1_tsep_1(X4,X5,sK4)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_71])])).

fof(f341,plain,
    ( spl7_41
  <=> ! [X1,X0] :
        ( r1_tsep_1(X0,sK4)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,X1)
        | ~ m1_pre_topc(sK4,X1)
        | ~ m1_pre_topc(sK2,X1)
        | ~ m1_pre_topc(X0,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_41])])).

fof(f536,plain,
    ( ! [X6,X4,X5] :
        ( v2_struct_0(k1_tsep_1(X4,X5,sK4))
        | ~ v2_pre_topc(k1_tsep_1(X4,X5,sK4))
        | ~ l1_pre_topc(k1_tsep_1(X4,X5,sK4))
        | v2_struct_0(X6)
        | ~ m1_pre_topc(X6,k1_tsep_1(X4,X5,sK4))
        | r1_tsep_1(X6,sK4)
        | ~ m1_pre_topc(sK2,k1_tsep_1(X4,X5,sK4))
        | ~ m1_pre_topc(X6,sK2)
        | ~ m1_pre_topc(X5,X4)
        | v2_struct_0(X5)
        | ~ m1_pre_topc(sK4,X4)
        | v2_struct_0(sK4)
        | ~ l1_pre_topc(X4)
        | ~ v2_pre_topc(X4)
        | v2_struct_0(X4) )
    | ~ spl7_41 ),
    inference(resolution,[],[f342,f289])).

fof(f342,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(sK4,X1)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,X1)
        | r1_tsep_1(X0,sK4)
        | ~ m1_pre_topc(sK2,X1)
        | ~ m1_pre_topc(X0,sK2) )
    | ~ spl7_41 ),
    inference(avatar_component_clause,[],[f341])).

fof(f544,plain,
    ( spl7_8
    | spl7_70
    | ~ spl7_41 ),
    inference(avatar_split_clause,[],[f535,f341,f542,f113])).

fof(f542,plain,
    ( spl7_70
  <=> ! [X1,X3,X2] :
        ( v2_struct_0(k1_tsep_1(X1,sK4,X2))
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ m1_pre_topc(sK4,X1)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X1)
        | ~ m1_pre_topc(X3,sK2)
        | ~ m1_pre_topc(sK2,k1_tsep_1(X1,sK4,X2))
        | r1_tsep_1(X3,sK4)
        | ~ m1_pre_topc(X3,k1_tsep_1(X1,sK4,X2))
        | v2_struct_0(X3)
        | ~ l1_pre_topc(k1_tsep_1(X1,sK4,X2))
        | ~ v2_pre_topc(k1_tsep_1(X1,sK4,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_70])])).

fof(f535,plain,
    ( ! [X2,X3,X1] :
        ( v2_struct_0(k1_tsep_1(X1,sK4,X2))
        | ~ v2_pre_topc(k1_tsep_1(X1,sK4,X2))
        | ~ l1_pre_topc(k1_tsep_1(X1,sK4,X2))
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,k1_tsep_1(X1,sK4,X2))
        | r1_tsep_1(X3,sK4)
        | ~ m1_pre_topc(sK2,k1_tsep_1(X1,sK4,X2))
        | ~ m1_pre_topc(X3,sK2)
        | ~ m1_pre_topc(X2,X1)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(sK4,X1)
        | v2_struct_0(sK4)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl7_41 ),
    inference(resolution,[],[f342,f61])).

fof(f540,plain,
    ( ~ spl7_11
    | spl7_69
    | ~ spl7_15
    | ~ spl7_16
    | spl7_17
    | ~ spl7_7
    | ~ spl7_41 ),
    inference(avatar_split_clause,[],[f534,f341,f108,f158,f153,f148,f538,f128])).

fof(f534,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | r1_tsep_1(X0,sK4)
        | ~ m1_pre_topc(sK2,sK0)
        | ~ m1_pre_topc(X0,sK2) )
    | ~ spl7_7
    | ~ spl7_41 ),
    inference(resolution,[],[f342,f110])).

fof(f527,plain,
    ( ~ spl7_43
    | ~ spl7_66
    | spl7_67
    | spl7_68
    | ~ spl7_58 ),
    inference(avatar_split_clause,[],[f494,f463,f524,f520,f516,f355])).

fof(f355,plain,
    ( spl7_43
  <=> l1_pre_topc(k1_tsep_1(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_43])])).

fof(f516,plain,
    ( spl7_66
  <=> m1_pre_topc(sK5(k1_tsep_1(sK0,sK1,sK3)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_66])])).

fof(f520,plain,
    ( spl7_67
  <=> r1_tsep_1(sK5(k1_tsep_1(sK0,sK1,sK3)),k2_tsep_1(sK0,sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_67])])).

fof(f524,plain,
    ( spl7_68
  <=> v2_struct_0(sK5(k1_tsep_1(sK0,sK1,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_68])])).

fof(f463,plain,
    ( spl7_58
  <=> ! [X0] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X0,k1_tsep_1(sK0,sK1,sK3))
        | r1_tsep_1(X0,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_58])])).

fof(f494,plain,
    ( v2_struct_0(sK5(k1_tsep_1(sK0,sK1,sK3)))
    | r1_tsep_1(sK5(k1_tsep_1(sK0,sK1,sK3)),k2_tsep_1(sK0,sK2,sK4))
    | ~ m1_pre_topc(sK5(k1_tsep_1(sK0,sK1,sK3)),sK0)
    | ~ l1_pre_topc(k1_tsep_1(sK0,sK1,sK3))
    | ~ spl7_58 ),
    inference(resolution,[],[f464,f60])).

fof(f464,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,k1_tsep_1(sK0,sK1,sK3))
        | v2_struct_0(X0)
        | r1_tsep_1(X0,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X0,sK0) )
    | ~ spl7_58 ),
    inference(avatar_component_clause,[],[f463])).

fof(f514,plain,
    ( spl7_34
    | ~ spl7_43
    | spl7_65
    | ~ spl7_58 ),
    inference(avatar_split_clause,[],[f493,f463,f512,f355,f302])).

fof(f512,plain,
    ( spl7_65
  <=> ! [X3,X2] :
        ( v2_struct_0(k2_tsep_1(k1_tsep_1(sK0,sK1,sK3),X2,X3))
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,k1_tsep_1(sK0,sK1,sK3))
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,k1_tsep_1(sK0,sK1,sK3))
        | ~ m1_pre_topc(k2_tsep_1(k1_tsep_1(sK0,sK1,sK3),X2,X3),sK0)
        | r1_tsep_1(k2_tsep_1(k1_tsep_1(sK0,sK1,sK3),X2,X3),k2_tsep_1(sK0,sK2,sK4)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_65])])).

fof(f493,plain,
    ( ! [X2,X3] :
        ( v2_struct_0(k2_tsep_1(k1_tsep_1(sK0,sK1,sK3),X2,X3))
        | r1_tsep_1(k2_tsep_1(k1_tsep_1(sK0,sK1,sK3),X2,X3),k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(k2_tsep_1(k1_tsep_1(sK0,sK1,sK3),X2,X3),sK0)
        | ~ m1_pre_topc(X3,k1_tsep_1(sK0,sK1,sK3))
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X2,k1_tsep_1(sK0,sK1,sK3))
        | v2_struct_0(X2)
        | ~ l1_pre_topc(k1_tsep_1(sK0,sK1,sK3))
        | v2_struct_0(k1_tsep_1(sK0,sK1,sK3)) )
    | ~ spl7_58 ),
    inference(resolution,[],[f464,f77])).

fof(f510,plain,
    ( spl7_34
    | ~ spl7_43
    | spl7_64
    | ~ spl7_58 ),
    inference(avatar_split_clause,[],[f492,f463,f508,f355,f302])).

fof(f508,plain,
    ( spl7_64
  <=> ! [X1,X0] :
        ( v2_struct_0(k1_tsep_1(k1_tsep_1(sK0,sK1,sK3),X0,X1))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,k1_tsep_1(sK0,sK1,sK3))
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,k1_tsep_1(sK0,sK1,sK3))
        | ~ m1_pre_topc(k1_tsep_1(k1_tsep_1(sK0,sK1,sK3),X0,X1),sK0)
        | r1_tsep_1(k1_tsep_1(k1_tsep_1(sK0,sK1,sK3),X0,X1),k2_tsep_1(sK0,sK2,sK4)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_64])])).

fof(f492,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(k1_tsep_1(k1_tsep_1(sK0,sK1,sK3),X0,X1))
        | r1_tsep_1(k1_tsep_1(k1_tsep_1(sK0,sK1,sK3),X0,X1),k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(k1_tsep_1(k1_tsep_1(sK0,sK1,sK3),X0,X1),sK0)
        | ~ m1_pre_topc(X1,k1_tsep_1(sK0,sK1,sK3))
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X0,k1_tsep_1(sK0,sK1,sK3))
        | v2_struct_0(X0)
        | ~ l1_pre_topc(k1_tsep_1(sK0,sK1,sK3))
        | v2_struct_0(k1_tsep_1(sK0,sK1,sK3)) )
    | ~ spl7_58 ),
    inference(resolution,[],[f464,f74])).

fof(f506,plain,
    ( spl7_17
    | ~ spl7_16
    | ~ spl7_15
    | spl7_14
    | ~ spl7_13
    | ~ spl7_9
    | spl7_63
    | spl7_10
    | ~ spl7_58 ),
    inference(avatar_split_clause,[],[f495,f463,f123,f503,f118,f138,f143,f148,f153,f158])).

fof(f495,plain,
    ( v2_struct_0(sK3)
    | r1_tsep_1(sK3,k2_tsep_1(sK0,sK2,sK4))
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl7_58 ),
    inference(duplicate_literal_removal,[],[f491])).

fof(f491,plain,
    ( v2_struct_0(sK3)
    | r1_tsep_1(sK3,k2_tsep_1(sK0,sK2,sK4))
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl7_58 ),
    inference(resolution,[],[f464,f289])).

fof(f501,plain,
    ( spl7_17
    | ~ spl7_16
    | ~ spl7_15
    | spl7_10
    | ~ spl7_9
    | ~ spl7_13
    | spl7_62
    | spl7_14
    | ~ spl7_58 ),
    inference(avatar_split_clause,[],[f496,f463,f143,f498,f138,f118,f123,f148,f153,f158])).

fof(f496,plain,
    ( v2_struct_0(sK1)
    | r1_tsep_1(sK1,k2_tsep_1(sK0,sK2,sK4))
    | ~ m1_pre_topc(sK1,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl7_58 ),
    inference(duplicate_literal_removal,[],[f490])).

fof(f490,plain,
    ( v2_struct_0(sK1)
    | r1_tsep_1(sK1,k2_tsep_1(sK0,sK2,sK4))
    | ~ m1_pre_topc(sK1,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl7_58 ),
    inference(resolution,[],[f464,f61])).

fof(f483,plain,
    ( spl7_8
    | spl7_12
    | spl7_61
    | ~ spl7_29 ),
    inference(avatar_split_clause,[],[f477,f236,f481,f133,f113])).

fof(f481,plain,
    ( spl7_61
  <=> ! [X1,X0] :
        ( r1_tsep_1(sK2,X0)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,X1)
        | ~ m1_pre_topc(sK2,X1)
        | ~ m1_pre_topc(sK4,X1)
        | ~ m1_pre_topc(X0,sK4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_61])])).

fof(f236,plain,
    ( spl7_29
  <=> r1_tsep_1(sK4,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_29])])).

fof(f477,plain,
    ( ! [X0,X1] :
        ( r1_tsep_1(sK2,X0)
        | ~ m1_pre_topc(X0,sK4)
        | ~ m1_pre_topc(sK2,X1)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(sK4,X1)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(X0,X1)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl7_29 ),
    inference(resolution,[],[f238,f67])).

fof(f238,plain,
    ( r1_tsep_1(sK4,sK2)
    | ~ spl7_29 ),
    inference(avatar_component_clause,[],[f236])).

fof(f473,plain,
    ( spl7_33
    | spl7_60
    | ~ spl7_36 ),
    inference(avatar_split_clause,[],[f460,f310,f471,f298])).

fof(f471,plain,
    ( spl7_60
  <=> ! [X5,X4,X6] :
        ( v2_struct_0(k1_tsep_1(X4,X5,k2_tsep_1(sK0,sK2,sK4)))
        | v2_struct_0(X4)
        | ~ v2_pre_topc(X4)
        | ~ l1_pre_topc(X4)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X4)
        | v2_struct_0(X5)
        | ~ m1_pre_topc(X5,X4)
        | ~ m1_pre_topc(X6,k1_tsep_1(sK0,sK1,sK3))
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(X4,X5,k2_tsep_1(sK0,sK2,sK4)))
        | r1_tsep_1(X6,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X6,k1_tsep_1(X4,X5,k2_tsep_1(sK0,sK2,sK4)))
        | v2_struct_0(X6)
        | ~ l1_pre_topc(k1_tsep_1(X4,X5,k2_tsep_1(sK0,sK2,sK4)))
        | ~ v2_pre_topc(k1_tsep_1(X4,X5,k2_tsep_1(sK0,sK2,sK4))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_60])])).

fof(f310,plain,
    ( spl7_36
  <=> ! [X3,X2] :
        ( r1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4))
        | v2_struct_0(X3)
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X3)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X3)
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),X3)
        | ~ m1_pre_topc(X2,k1_tsep_1(sK0,sK1,sK3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_36])])).

fof(f460,plain,
    ( ! [X6,X4,X5] :
        ( v2_struct_0(k1_tsep_1(X4,X5,k2_tsep_1(sK0,sK2,sK4)))
        | ~ v2_pre_topc(k1_tsep_1(X4,X5,k2_tsep_1(sK0,sK2,sK4)))
        | ~ l1_pre_topc(k1_tsep_1(X4,X5,k2_tsep_1(sK0,sK2,sK4)))
        | v2_struct_0(X6)
        | ~ m1_pre_topc(X6,k1_tsep_1(X4,X5,k2_tsep_1(sK0,sK2,sK4)))
        | r1_tsep_1(X6,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(X4,X5,k2_tsep_1(sK0,sK2,sK4)))
        | ~ m1_pre_topc(X6,k1_tsep_1(sK0,sK1,sK3))
        | ~ m1_pre_topc(X5,X4)
        | v2_struct_0(X5)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X4)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ l1_pre_topc(X4)
        | ~ v2_pre_topc(X4)
        | v2_struct_0(X4) )
    | ~ spl7_36 ),
    inference(resolution,[],[f311,f289])).

fof(f311,plain,
    ( ! [X2,X3] :
        ( ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X3)
        | v2_struct_0(X3)
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X3)
        | r1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),X3)
        | ~ m1_pre_topc(X2,k1_tsep_1(sK0,sK1,sK3)) )
    | ~ spl7_36 ),
    inference(avatar_component_clause,[],[f310])).

fof(f469,plain,
    ( spl7_33
    | spl7_59
    | ~ spl7_36 ),
    inference(avatar_split_clause,[],[f459,f310,f467,f298])).

fof(f467,plain,
    ( spl7_59
  <=> ! [X1,X3,X2] :
        ( v2_struct_0(k1_tsep_1(X1,k2_tsep_1(sK0,sK2,sK4),X2))
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X1)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X1)
        | ~ m1_pre_topc(X3,k1_tsep_1(sK0,sK1,sK3))
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(X1,k2_tsep_1(sK0,sK2,sK4),X2))
        | r1_tsep_1(X3,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X3,k1_tsep_1(X1,k2_tsep_1(sK0,sK2,sK4),X2))
        | v2_struct_0(X3)
        | ~ l1_pre_topc(k1_tsep_1(X1,k2_tsep_1(sK0,sK2,sK4),X2))
        | ~ v2_pre_topc(k1_tsep_1(X1,k2_tsep_1(sK0,sK2,sK4),X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_59])])).

fof(f459,plain,
    ( ! [X2,X3,X1] :
        ( v2_struct_0(k1_tsep_1(X1,k2_tsep_1(sK0,sK2,sK4),X2))
        | ~ v2_pre_topc(k1_tsep_1(X1,k2_tsep_1(sK0,sK2,sK4),X2))
        | ~ l1_pre_topc(k1_tsep_1(X1,k2_tsep_1(sK0,sK2,sK4),X2))
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,k1_tsep_1(X1,k2_tsep_1(sK0,sK2,sK4),X2))
        | r1_tsep_1(X3,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(X1,k2_tsep_1(sK0,sK2,sK4),X2))
        | ~ m1_pre_topc(X3,k1_tsep_1(sK0,sK1,sK3))
        | ~ m1_pre_topc(X2,X1)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X1)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl7_36 ),
    inference(resolution,[],[f311,f61])).

fof(f465,plain,
    ( spl7_12
    | ~ spl7_11
    | spl7_8
    | ~ spl7_7
    | ~ spl7_37
    | spl7_58
    | ~ spl7_15
    | ~ spl7_16
    | spl7_17
    | ~ spl7_36 ),
    inference(avatar_split_clause,[],[f461,f310,f158,f153,f148,f463,f322,f108,f113,f128,f133])).

fof(f461,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | r1_tsep_1(X0,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
        | ~ m1_pre_topc(X0,k1_tsep_1(sK0,sK1,sK3))
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2) )
    | ~ spl7_36 ),
    inference(duplicate_literal_removal,[],[f458])).

fof(f458,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | r1_tsep_1(X0,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
        | ~ m1_pre_topc(X0,k1_tsep_1(sK0,sK1,sK3))
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl7_36 ),
    inference(resolution,[],[f311,f77])).

fof(f440,plain,
    ( spl7_12
    | spl7_8
    | spl7_57
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f434,f89,f438,f113,f133])).

fof(f89,plain,
    ( spl7_3
  <=> r1_tsep_1(sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f434,plain,
    ( ! [X0,X1] :
        ( r1_tsep_1(sK4,X0)
        | ~ m1_pre_topc(X0,sK2)
        | ~ m1_pre_topc(sK4,X1)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK2,X1)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(X0,X1)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl7_3 ),
    inference(resolution,[],[f91,f67])).

fof(f91,plain,
    ( r1_tsep_1(sK2,sK4)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f89])).

fof(f433,plain,
    ( spl7_33
    | ~ spl7_44
    | spl7_56
    | ~ spl7_52 ),
    inference(avatar_split_clause,[],[f424,f412,f431,f366,f298])).

fof(f366,plain,
    ( spl7_44
  <=> l1_pre_topc(k2_tsep_1(sK0,sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_44])])).

fof(f431,plain,
    ( spl7_56
  <=> ! [X3,X2] :
        ( v2_struct_0(k2_tsep_1(k2_tsep_1(sK0,sK2,sK4),X2,X3))
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,k2_tsep_1(sK0,sK2,sK4))
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(k2_tsep_1(k2_tsep_1(sK0,sK2,sK4),X2,X3),sK0)
        | r1_tsep_1(k1_tsep_1(sK0,sK1,sK3),k2_tsep_1(k2_tsep_1(sK0,sK2,sK4),X2,X3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_56])])).

fof(f412,plain,
    ( spl7_52
  <=> ! [X0] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4))
        | r1_tsep_1(k1_tsep_1(sK0,sK1,sK3),X0)
        | ~ m1_pre_topc(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_52])])).

fof(f424,plain,
    ( ! [X2,X3] :
        ( v2_struct_0(k2_tsep_1(k2_tsep_1(sK0,sK2,sK4),X2,X3))
        | r1_tsep_1(k1_tsep_1(sK0,sK1,sK3),k2_tsep_1(k2_tsep_1(sK0,sK2,sK4),X2,X3))
        | ~ m1_pre_topc(k2_tsep_1(k2_tsep_1(sK0,sK2,sK4),X2,X3),sK0)
        | ~ m1_pre_topc(X3,k2_tsep_1(sK0,sK2,sK4))
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X2,k2_tsep_1(sK0,sK2,sK4))
        | v2_struct_0(X2)
        | ~ l1_pre_topc(k2_tsep_1(sK0,sK2,sK4))
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4)) )
    | ~ spl7_52 ),
    inference(resolution,[],[f413,f77])).

fof(f413,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4))
        | v2_struct_0(X0)
        | r1_tsep_1(k1_tsep_1(sK0,sK1,sK3),X0)
        | ~ m1_pre_topc(X0,sK0) )
    | ~ spl7_52 ),
    inference(avatar_component_clause,[],[f412])).

fof(f429,plain,
    ( spl7_33
    | ~ spl7_44
    | spl7_55
    | ~ spl7_52 ),
    inference(avatar_split_clause,[],[f423,f412,f427,f366,f298])).

fof(f427,plain,
    ( spl7_55
  <=> ! [X1,X0] :
        ( v2_struct_0(k1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X0,X1))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4))
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(k1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X0,X1),sK0)
        | r1_tsep_1(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_55])])).

fof(f423,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(k1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X0,X1))
        | r1_tsep_1(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X0,X1))
        | ~ m1_pre_topc(k1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X0,X1),sK0)
        | ~ m1_pre_topc(X1,k2_tsep_1(sK0,sK2,sK4))
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4))
        | v2_struct_0(X0)
        | ~ l1_pre_topc(k2_tsep_1(sK0,sK2,sK4))
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4)) )
    | ~ spl7_52 ),
    inference(resolution,[],[f413,f74])).

fof(f422,plain,
    ( spl7_33
    | spl7_54
    | ~ spl7_51 ),
    inference(avatar_split_clause,[],[f409,f397,f420,f298])).

fof(f420,plain,
    ( spl7_54
  <=> ! [X5,X4,X6] :
        ( v2_struct_0(k1_tsep_1(X4,X5,k2_tsep_1(sK0,sK2,sK4)))
        | v2_struct_0(X4)
        | ~ v2_pre_topc(X4)
        | ~ l1_pre_topc(X4)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X4)
        | v2_struct_0(X5)
        | ~ m1_pre_topc(X5,X4)
        | ~ m1_pre_topc(X6,k2_tsep_1(sK0,sK2,sK4))
        | r1_tsep_1(k1_tsep_1(sK0,sK1,sK3),X6)
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(X4,X5,k2_tsep_1(sK0,sK2,sK4)))
        | ~ m1_pre_topc(X6,k1_tsep_1(X4,X5,k2_tsep_1(sK0,sK2,sK4)))
        | v2_struct_0(X6)
        | ~ l1_pre_topc(k1_tsep_1(X4,X5,k2_tsep_1(sK0,sK2,sK4)))
        | ~ v2_pre_topc(k1_tsep_1(X4,X5,k2_tsep_1(sK0,sK2,sK4))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_54])])).

fof(f397,plain,
    ( spl7_51
  <=> ! [X3,X2] :
        ( r1_tsep_1(k1_tsep_1(sK0,sK1,sK3),X2)
        | v2_struct_0(X3)
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X3)
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),X3)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X3)
        | ~ m1_pre_topc(X2,k2_tsep_1(sK0,sK2,sK4)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_51])])).

fof(f409,plain,
    ( ! [X6,X4,X5] :
        ( v2_struct_0(k1_tsep_1(X4,X5,k2_tsep_1(sK0,sK2,sK4)))
        | ~ v2_pre_topc(k1_tsep_1(X4,X5,k2_tsep_1(sK0,sK2,sK4)))
        | ~ l1_pre_topc(k1_tsep_1(X4,X5,k2_tsep_1(sK0,sK2,sK4)))
        | v2_struct_0(X6)
        | ~ m1_pre_topc(X6,k1_tsep_1(X4,X5,k2_tsep_1(sK0,sK2,sK4)))
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(X4,X5,k2_tsep_1(sK0,sK2,sK4)))
        | r1_tsep_1(k1_tsep_1(sK0,sK1,sK3),X6)
        | ~ m1_pre_topc(X6,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X5,X4)
        | v2_struct_0(X5)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X4)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ l1_pre_topc(X4)
        | ~ v2_pre_topc(X4)
        | v2_struct_0(X4) )
    | ~ spl7_51 ),
    inference(resolution,[],[f398,f289])).

fof(f398,plain,
    ( ! [X2,X3] :
        ( ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X3)
        | v2_struct_0(X3)
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X3)
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),X3)
        | r1_tsep_1(k1_tsep_1(sK0,sK1,sK3),X2)
        | ~ m1_pre_topc(X2,k2_tsep_1(sK0,sK2,sK4)) )
    | ~ spl7_51 ),
    inference(avatar_component_clause,[],[f397])).

fof(f418,plain,
    ( spl7_33
    | spl7_53
    | ~ spl7_51 ),
    inference(avatar_split_clause,[],[f408,f397,f416,f298])).

fof(f416,plain,
    ( spl7_53
  <=> ! [X1,X3,X2] :
        ( v2_struct_0(k1_tsep_1(X1,k2_tsep_1(sK0,sK2,sK4),X2))
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X1)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X1)
        | ~ m1_pre_topc(X3,k2_tsep_1(sK0,sK2,sK4))
        | r1_tsep_1(k1_tsep_1(sK0,sK1,sK3),X3)
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(X1,k2_tsep_1(sK0,sK2,sK4),X2))
        | ~ m1_pre_topc(X3,k1_tsep_1(X1,k2_tsep_1(sK0,sK2,sK4),X2))
        | v2_struct_0(X3)
        | ~ l1_pre_topc(k1_tsep_1(X1,k2_tsep_1(sK0,sK2,sK4),X2))
        | ~ v2_pre_topc(k1_tsep_1(X1,k2_tsep_1(sK0,sK2,sK4),X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_53])])).

fof(f408,plain,
    ( ! [X2,X3,X1] :
        ( v2_struct_0(k1_tsep_1(X1,k2_tsep_1(sK0,sK2,sK4),X2))
        | ~ v2_pre_topc(k1_tsep_1(X1,k2_tsep_1(sK0,sK2,sK4),X2))
        | ~ l1_pre_topc(k1_tsep_1(X1,k2_tsep_1(sK0,sK2,sK4),X2))
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,k1_tsep_1(X1,k2_tsep_1(sK0,sK2,sK4),X2))
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(X1,k2_tsep_1(sK0,sK2,sK4),X2))
        | r1_tsep_1(k1_tsep_1(sK0,sK1,sK3),X3)
        | ~ m1_pre_topc(X3,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X2,X1)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X1)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl7_51 ),
    inference(resolution,[],[f398,f61])).

fof(f414,plain,
    ( spl7_12
    | ~ spl7_11
    | spl7_8
    | ~ spl7_7
    | ~ spl7_37
    | spl7_52
    | ~ spl7_15
    | ~ spl7_16
    | spl7_17
    | ~ spl7_51 ),
    inference(avatar_split_clause,[],[f410,f397,f158,f153,f148,f412,f322,f108,f113,f128,f133])).

fof(f410,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
        | r1_tsep_1(k1_tsep_1(sK0,sK1,sK3),X0)
        | ~ m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2) )
    | ~ spl7_51 ),
    inference(duplicate_literal_removal,[],[f407])).

fof(f407,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
        | r1_tsep_1(k1_tsep_1(sK0,sK1,sK3),X0)
        | ~ m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl7_51 ),
    inference(resolution,[],[f398,f77])).

fof(f401,plain,
    ( ~ spl7_7
    | spl7_17
    | ~ spl7_15
    | spl7_12
    | ~ spl7_11
    | spl7_8
    | spl7_44 ),
    inference(avatar_split_clause,[],[f400,f366,f113,f128,f133,f148,f158,f108])).

fof(f400,plain,
    ( v2_struct_0(sK4)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(sK4,sK0)
    | spl7_44 ),
    inference(resolution,[],[f368,f258])).

fof(f258,plain,(
    ! [X2,X0,X1] :
      ( l1_pre_topc(k2_tsep_1(X1,X2,X0))
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X2,X1)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f257])).

fof(f257,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X0,X1)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X2,X1)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X1)
      | l1_pre_topc(k2_tsep_1(X1,X2,X0))
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f77,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f368,plain,
    ( ~ l1_pre_topc(k2_tsep_1(sK0,sK2,sK4))
    | spl7_44 ),
    inference(avatar_component_clause,[],[f366])).

fof(f399,plain,
    ( spl7_33
    | spl7_34
    | spl7_51
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f391,f93,f397,f302,f298])).

fof(f391,plain,
    ( ! [X2,X3] :
        ( r1_tsep_1(k1_tsep_1(sK0,sK1,sK3),X2)
        | ~ m1_pre_topc(X2,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),X3)
        | v2_struct_0(k1_tsep_1(sK0,sK1,sK3))
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X3)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X2,X3)
        | v2_struct_0(X2)
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(X3)
        | v2_struct_0(X3) )
    | ~ spl7_4 ),
    inference(resolution,[],[f67,f95])).

fof(f95,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),k1_tsep_1(sK0,sK1,sK3))
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f93])).

fof(f395,plain,
    ( spl7_34
    | spl7_33
    | spl7_50
    | ~ spl7_32 ),
    inference(avatar_split_clause,[],[f390,f250,f393,f298,f302])).

fof(f393,plain,
    ( spl7_50
  <=> ! [X1,X0] :
        ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X0)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,X1)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X1)
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),X1)
        | ~ m1_pre_topc(X0,k1_tsep_1(sK0,sK1,sK3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_50])])).

fof(f250,plain,
    ( spl7_32
  <=> r1_tsep_1(k1_tsep_1(sK0,sK1,sK3),k2_tsep_1(sK0,sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_32])])).

fof(f390,plain,
    ( ! [X0,X1] :
        ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X0)
        | ~ m1_pre_topc(X0,k1_tsep_1(sK0,sK1,sK3))
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X1)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),X1)
        | v2_struct_0(k1_tsep_1(sK0,sK1,sK3))
        | ~ m1_pre_topc(X0,X1)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl7_32 ),
    inference(resolution,[],[f67,f252])).

fof(f252,plain,
    ( r1_tsep_1(k1_tsep_1(sK0,sK1,sK3),k2_tsep_1(sK0,sK2,sK4))
    | ~ spl7_32 ),
    inference(avatar_component_clause,[],[f250])).

fof(f389,plain,
    ( ~ spl7_44
    | ~ spl7_47
    | spl7_48
    | spl7_49
    | ~ spl7_38 ),
    inference(avatar_split_clause,[],[f364,f326,f386,f382,f378,f366])).

fof(f378,plain,
    ( spl7_47
  <=> m1_pre_topc(sK5(k2_tsep_1(sK0,sK2,sK4)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_47])])).

fof(f382,plain,
    ( spl7_48
  <=> r1_tsep_1(sK5(k2_tsep_1(sK0,sK2,sK4)),k1_tsep_1(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_48])])).

fof(f386,plain,
    ( spl7_49
  <=> v2_struct_0(sK5(k2_tsep_1(sK0,sK2,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_49])])).

fof(f326,plain,
    ( spl7_38
  <=> ! [X0] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4))
        | r1_tsep_1(X0,k1_tsep_1(sK0,sK1,sK3))
        | ~ m1_pre_topc(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_38])])).

fof(f364,plain,
    ( v2_struct_0(sK5(k2_tsep_1(sK0,sK2,sK4)))
    | r1_tsep_1(sK5(k2_tsep_1(sK0,sK2,sK4)),k1_tsep_1(sK0,sK1,sK3))
    | ~ m1_pre_topc(sK5(k2_tsep_1(sK0,sK2,sK4)),sK0)
    | ~ l1_pre_topc(k2_tsep_1(sK0,sK2,sK4))
    | ~ spl7_38 ),
    inference(resolution,[],[f327,f60])).

fof(f327,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4))
        | v2_struct_0(X0)
        | r1_tsep_1(X0,k1_tsep_1(sK0,sK1,sK3))
        | ~ m1_pre_topc(X0,sK0) )
    | ~ spl7_38 ),
    inference(avatar_component_clause,[],[f326])).

fof(f376,plain,
    ( spl7_33
    | ~ spl7_44
    | spl7_46
    | ~ spl7_38 ),
    inference(avatar_split_clause,[],[f363,f326,f374,f366,f298])).

fof(f374,plain,
    ( spl7_46
  <=> ! [X3,X2] :
        ( v2_struct_0(k2_tsep_1(k2_tsep_1(sK0,sK2,sK4),X2,X3))
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,k2_tsep_1(sK0,sK2,sK4))
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(k2_tsep_1(k2_tsep_1(sK0,sK2,sK4),X2,X3),sK0)
        | r1_tsep_1(k2_tsep_1(k2_tsep_1(sK0,sK2,sK4),X2,X3),k1_tsep_1(sK0,sK1,sK3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_46])])).

fof(f363,plain,
    ( ! [X2,X3] :
        ( v2_struct_0(k2_tsep_1(k2_tsep_1(sK0,sK2,sK4),X2,X3))
        | r1_tsep_1(k2_tsep_1(k2_tsep_1(sK0,sK2,sK4),X2,X3),k1_tsep_1(sK0,sK1,sK3))
        | ~ m1_pre_topc(k2_tsep_1(k2_tsep_1(sK0,sK2,sK4),X2,X3),sK0)
        | ~ m1_pre_topc(X3,k2_tsep_1(sK0,sK2,sK4))
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X2,k2_tsep_1(sK0,sK2,sK4))
        | v2_struct_0(X2)
        | ~ l1_pre_topc(k2_tsep_1(sK0,sK2,sK4))
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4)) )
    | ~ spl7_38 ),
    inference(resolution,[],[f327,f77])).

fof(f372,plain,
    ( spl7_33
    | ~ spl7_44
    | spl7_45
    | ~ spl7_38 ),
    inference(avatar_split_clause,[],[f362,f326,f370,f366,f298])).

fof(f370,plain,
    ( spl7_45
  <=> ! [X1,X0] :
        ( v2_struct_0(k1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X0,X1))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4))
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(k1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X0,X1),sK0)
        | r1_tsep_1(k1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X0,X1),k1_tsep_1(sK0,sK1,sK3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_45])])).

fof(f362,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(k1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X0,X1))
        | r1_tsep_1(k1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X0,X1),k1_tsep_1(sK0,sK1,sK3))
        | ~ m1_pre_topc(k1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X0,X1),sK0)
        | ~ m1_pre_topc(X1,k2_tsep_1(sK0,sK2,sK4))
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4))
        | v2_struct_0(X0)
        | ~ l1_pre_topc(k2_tsep_1(sK0,sK2,sK4))
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4)) )
    | ~ spl7_38 ),
    inference(resolution,[],[f327,f74])).

fof(f358,plain,
    ( ~ spl7_15
    | spl7_43
    | ~ spl7_37 ),
    inference(avatar_split_clause,[],[f353,f322,f355,f148])).

fof(f353,plain,
    ( l1_pre_topc(k1_tsep_1(sK0,sK1,sK3))
    | ~ l1_pre_topc(sK0)
    | ~ spl7_37 ),
    inference(resolution,[],[f323,f59])).

fof(f323,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
    | ~ spl7_37 ),
    inference(avatar_component_clause,[],[f322])).

fof(f352,plain,
    ( spl7_17
    | ~ spl7_15
    | spl7_14
    | ~ spl7_13
    | spl7_10
    | ~ spl7_9
    | spl7_37 ),
    inference(avatar_split_clause,[],[f351,f322,f118,f123,f138,f143,f148,f158])).

fof(f351,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl7_37 ),
    inference(resolution,[],[f324,f74])).

fof(f324,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
    | spl7_37 ),
    inference(avatar_component_clause,[],[f322])).

fof(f350,plain,
    ( ~ spl7_27
    | ~ spl7_25
    | spl7_3
    | ~ spl7_29 ),
    inference(avatar_split_clause,[],[f345,f236,f89,f211,f223])).

fof(f345,plain,
    ( r1_tsep_1(sK2,sK4)
    | ~ l1_struct_0(sK2)
    | ~ l1_struct_0(sK4)
    | ~ spl7_29 ),
    inference(resolution,[],[f238,f70])).

fof(f349,plain,
    ( spl7_8
    | spl7_12
    | spl7_42
    | ~ spl7_29 ),
    inference(avatar_split_clause,[],[f344,f236,f347,f133,f113])).

fof(f344,plain,
    ( ! [X0,X1] :
        ( r1_tsep_1(X0,sK2)
        | ~ m1_pre_topc(X0,sK4)
        | ~ m1_pre_topc(sK2,X1)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(sK4,X1)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(X0,X1)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl7_29 ),
    inference(resolution,[],[f238,f66])).

fof(f343,plain,
    ( spl7_12
    | spl7_8
    | spl7_41
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f338,f89,f341,f113,f133])).

fof(f338,plain,
    ( ! [X0,X1] :
        ( r1_tsep_1(X0,sK4)
        | ~ m1_pre_topc(X0,sK2)
        | ~ m1_pre_topc(sK4,X1)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK2,X1)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(X0,X1)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl7_3 ),
    inference(resolution,[],[f91,f66])).

fof(f337,plain,
    ( ~ spl7_31
    | ~ spl7_30
    | spl7_4
    | ~ spl7_32 ),
    inference(avatar_split_clause,[],[f264,f250,f93,f242,f246])).

fof(f246,plain,
    ( spl7_31
  <=> l1_struct_0(k1_tsep_1(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).

fof(f264,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),k1_tsep_1(sK0,sK1,sK3))
    | ~ l1_struct_0(k2_tsep_1(sK0,sK2,sK4))
    | ~ l1_struct_0(k1_tsep_1(sK0,sK1,sK3))
    | ~ spl7_32 ),
    inference(resolution,[],[f252,f70])).

fof(f336,plain,
    ( spl7_33
    | spl7_40
    | ~ spl7_35 ),
    inference(avatar_split_clause,[],[f319,f306,f334,f298])).

fof(f334,plain,
    ( spl7_40
  <=> ! [X5,X4,X6] :
        ( v2_struct_0(k1_tsep_1(X4,X5,k2_tsep_1(sK0,sK2,sK4)))
        | v2_struct_0(X4)
        | ~ v2_pre_topc(X4)
        | ~ l1_pre_topc(X4)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X4)
        | v2_struct_0(X5)
        | ~ m1_pre_topc(X5,X4)
        | ~ m1_pre_topc(X6,k2_tsep_1(sK0,sK2,sK4))
        | r1_tsep_1(X6,k1_tsep_1(sK0,sK1,sK3))
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(X4,X5,k2_tsep_1(sK0,sK2,sK4)))
        | ~ m1_pre_topc(X6,k1_tsep_1(X4,X5,k2_tsep_1(sK0,sK2,sK4)))
        | v2_struct_0(X6)
        | ~ l1_pre_topc(k1_tsep_1(X4,X5,k2_tsep_1(sK0,sK2,sK4)))
        | ~ v2_pre_topc(k1_tsep_1(X4,X5,k2_tsep_1(sK0,sK2,sK4))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_40])])).

% (11161)Refutation not found, incomplete strategy% (11161)------------------------------
% (11161)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (11161)Termination reason: Refutation not found, incomplete strategy

% (11161)Memory used [KB]: 2174
% (11161)Time elapsed: 0.610 s
% (11161)------------------------------
% (11161)------------------------------
fof(f306,plain,
    ( spl7_35
  <=> ! [X1,X0] :
        ( r1_tsep_1(X0,k1_tsep_1(sK0,sK1,sK3))
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,X1)
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),X1)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X1)
        | ~ m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_35])])).

fof(f319,plain,
    ( ! [X6,X4,X5] :
        ( v2_struct_0(k1_tsep_1(X4,X5,k2_tsep_1(sK0,sK2,sK4)))
        | ~ v2_pre_topc(k1_tsep_1(X4,X5,k2_tsep_1(sK0,sK2,sK4)))
        | ~ l1_pre_topc(k1_tsep_1(X4,X5,k2_tsep_1(sK0,sK2,sK4)))
        | v2_struct_0(X6)
        | ~ m1_pre_topc(X6,k1_tsep_1(X4,X5,k2_tsep_1(sK0,sK2,sK4)))
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(X4,X5,k2_tsep_1(sK0,sK2,sK4)))
        | r1_tsep_1(X6,k1_tsep_1(sK0,sK1,sK3))
        | ~ m1_pre_topc(X6,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X5,X4)
        | v2_struct_0(X5)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X4)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ l1_pre_topc(X4)
        | ~ v2_pre_topc(X4)
        | v2_struct_0(X4) )
    | ~ spl7_35 ),
    inference(resolution,[],[f307,f289])).

fof(f307,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X1)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,X1)
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),X1)
        | r1_tsep_1(X0,k1_tsep_1(sK0,sK1,sK3))
        | ~ m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4)) )
    | ~ spl7_35 ),
    inference(avatar_component_clause,[],[f306])).

fof(f332,plain,
    ( spl7_33
    | spl7_39
    | ~ spl7_35 ),
    inference(avatar_split_clause,[],[f318,f306,f330,f298])).

fof(f330,plain,
    ( spl7_39
  <=> ! [X1,X3,X2] :
        ( v2_struct_0(k1_tsep_1(X1,k2_tsep_1(sK0,sK2,sK4),X2))
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X1)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X1)
        | ~ m1_pre_topc(X3,k2_tsep_1(sK0,sK2,sK4))
        | r1_tsep_1(X3,k1_tsep_1(sK0,sK1,sK3))
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(X1,k2_tsep_1(sK0,sK2,sK4),X2))
        | ~ m1_pre_topc(X3,k1_tsep_1(X1,k2_tsep_1(sK0,sK2,sK4),X2))
        | v2_struct_0(X3)
        | ~ l1_pre_topc(k1_tsep_1(X1,k2_tsep_1(sK0,sK2,sK4),X2))
        | ~ v2_pre_topc(k1_tsep_1(X1,k2_tsep_1(sK0,sK2,sK4),X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_39])])).

fof(f318,plain,
    ( ! [X2,X3,X1] :
        ( v2_struct_0(k1_tsep_1(X1,k2_tsep_1(sK0,sK2,sK4),X2))
        | ~ v2_pre_topc(k1_tsep_1(X1,k2_tsep_1(sK0,sK2,sK4),X2))
        | ~ l1_pre_topc(k1_tsep_1(X1,k2_tsep_1(sK0,sK2,sK4),X2))
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,k1_tsep_1(X1,k2_tsep_1(sK0,sK2,sK4),X2))
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(X1,k2_tsep_1(sK0,sK2,sK4),X2))
        | r1_tsep_1(X3,k1_tsep_1(sK0,sK1,sK3))
        | ~ m1_pre_topc(X3,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X2,X1)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X1)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl7_35 ),
    inference(resolution,[],[f307,f61])).

fof(f328,plain,
    ( spl7_12
    | ~ spl7_11
    | spl7_8
    | ~ spl7_7
    | ~ spl7_37
    | spl7_38
    | ~ spl7_15
    | ~ spl7_16
    | spl7_17
    | ~ spl7_35 ),
    inference(avatar_split_clause,[],[f320,f306,f158,f153,f148,f326,f322,f108,f113,f128,f133])).

fof(f320,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
        | r1_tsep_1(X0,k1_tsep_1(sK0,sK1,sK3))
        | ~ m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2) )
    | ~ spl7_35 ),
    inference(duplicate_literal_removal,[],[f317])).

fof(f317,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
        | r1_tsep_1(X0,k1_tsep_1(sK0,sK1,sK3))
        | ~ m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl7_35 ),
    inference(resolution,[],[f307,f77])).

fof(f316,plain,
    ( spl7_17
    | ~ spl7_15
    | spl7_14
    | ~ spl7_13
    | spl7_10
    | ~ spl7_9
    | ~ spl7_34 ),
    inference(avatar_split_clause,[],[f315,f302,f118,f123,f138,f143,f148,f158])).

fof(f315,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl7_34 ),
    inference(resolution,[],[f304,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f304,plain,
    ( v2_struct_0(k1_tsep_1(sK0,sK1,sK3))
    | ~ spl7_34 ),
    inference(avatar_component_clause,[],[f302])).

fof(f314,plain,
    ( spl7_17
    | ~ spl7_15
    | spl7_12
    | ~ spl7_11
    | spl7_8
    | ~ spl7_7
    | ~ spl7_33 ),
    inference(avatar_split_clause,[],[f313,f298,f108,f113,f128,f133,f148,f158])).

fof(f313,plain,
    ( ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl7_33 ),
    inference(resolution,[],[f300,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k2_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f300,plain,
    ( v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
    | ~ spl7_33 ),
    inference(avatar_component_clause,[],[f298])).

fof(f312,plain,
    ( spl7_34
    | spl7_33
    | spl7_36
    | ~ spl7_32 ),
    inference(avatar_split_clause,[],[f296,f250,f310,f298,f302])).

fof(f296,plain,
    ( ! [X2,X3] :
        ( r1_tsep_1(X2,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X2,k1_tsep_1(sK0,sK1,sK3))
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X3)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),X3)
        | v2_struct_0(k1_tsep_1(sK0,sK1,sK3))
        | ~ m1_pre_topc(X2,X3)
        | v2_struct_0(X2)
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(X3)
        | v2_struct_0(X3) )
    | ~ spl7_32 ),
    inference(resolution,[],[f66,f252])).

fof(f308,plain,
    ( spl7_33
    | spl7_34
    | spl7_35
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f295,f93,f306,f302,f298])).

fof(f295,plain,
    ( ! [X0,X1] :
        ( r1_tsep_1(X0,k1_tsep_1(sK0,sK1,sK3))
        | ~ m1_pre_topc(X0,k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),X1)
        | v2_struct_0(k1_tsep_1(sK0,sK1,sK3))
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),X1)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
        | ~ m1_pre_topc(X0,X1)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl7_4 ),
    inference(resolution,[],[f66,f95])).

fof(f263,plain,
    ( spl7_10
    | ~ spl7_9
    | spl7_17
    | ~ spl7_15
    | spl7_14
    | ~ spl7_13
    | spl7_31 ),
    inference(avatar_split_clause,[],[f262,f246,f138,f143,f148,f158,f118,f123])).

fof(f262,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | spl7_31 ),
    inference(resolution,[],[f248,f256])).

fof(f256,plain,(
    ! [X2,X0,X1] :
      ( l1_struct_0(k1_tsep_1(X2,X1,X0))
      | ~ m1_pre_topc(X1,X2)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X0,X2)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f255,f58])).

fof(f58,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f255,plain,(
    ! [X2,X0,X1] :
      ( l1_pre_topc(k1_tsep_1(X1,X2,X0))
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X2,X1)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f254])).

fof(f254,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X0,X1)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X2,X1)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X1)
      | l1_pre_topc(k1_tsep_1(X1,X2,X0))
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f74,f59])).

fof(f248,plain,
    ( ~ l1_struct_0(k1_tsep_1(sK0,sK1,sK3))
    | spl7_31 ),
    inference(avatar_component_clause,[],[f246])).

fof(f261,plain,
    ( spl7_8
    | ~ spl7_7
    | spl7_17
    | ~ spl7_15
    | spl7_12
    | ~ spl7_11
    | spl7_30 ),
    inference(avatar_split_clause,[],[f260,f242,f128,f133,f148,f158,f108,f113])).

fof(f260,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK4)
    | spl7_30 ),
    inference(resolution,[],[f259,f244])).

fof(f244,plain,
    ( ~ l1_struct_0(k2_tsep_1(sK0,sK2,sK4))
    | spl7_30 ),
    inference(avatar_component_clause,[],[f242])).

fof(f259,plain,(
    ! [X2,X0,X1] :
      ( l1_struct_0(k2_tsep_1(X2,X1,X0))
      | ~ m1_pre_topc(X1,X2)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X0,X2)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f258,f58])).

fof(f253,plain,
    ( ~ spl7_30
    | ~ spl7_31
    | spl7_32
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f240,f93,f250,f246,f242])).

fof(f240,plain,
    ( r1_tsep_1(k1_tsep_1(sK0,sK1,sK3),k2_tsep_1(sK0,sK2,sK4))
    | ~ l1_struct_0(k1_tsep_1(sK0,sK1,sK3))
    | ~ l1_struct_0(k2_tsep_1(sK0,sK2,sK4))
    | ~ spl7_4 ),
    inference(resolution,[],[f95,f70])).

fof(f239,plain,
    ( ~ spl7_25
    | ~ spl7_27
    | spl7_29
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f234,f89,f236,f223,f211])).

fof(f234,plain,
    ( r1_tsep_1(sK4,sK2)
    | ~ l1_struct_0(sK4)
    | ~ l1_struct_0(sK2)
    | ~ spl7_3 ),
    inference(resolution,[],[f70,f91])).

fof(f232,plain,
    ( spl7_28
    | ~ spl7_24 ),
    inference(avatar_split_clause,[],[f227,f203,f229])).

fof(f203,plain,
    ( spl7_24
  <=> l1_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).

fof(f227,plain,
    ( l1_struct_0(sK3)
    | ~ spl7_24 ),
    inference(resolution,[],[f205,f58])).

fof(f205,plain,
    ( l1_pre_topc(sK3)
    | ~ spl7_24 ),
    inference(avatar_component_clause,[],[f203])).

fof(f226,plain,
    ( spl7_27
    | ~ spl7_23 ),
    inference(avatar_split_clause,[],[f221,f199,f223])).

fof(f221,plain,
    ( l1_struct_0(sK4)
    | ~ spl7_23 ),
    inference(resolution,[],[f200,f58])).

fof(f200,plain,
    ( l1_pre_topc(sK4)
    | ~ spl7_23 ),
    inference(avatar_component_clause,[],[f199])).

fof(f220,plain,
    ( spl7_26
    | ~ spl7_22 ),
    inference(avatar_split_clause,[],[f215,f192,f217])).

fof(f192,plain,
    ( spl7_22
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).

fof(f215,plain,
    ( l1_struct_0(sK1)
    | ~ spl7_22 ),
    inference(resolution,[],[f194,f58])).

fof(f194,plain,
    ( l1_pre_topc(sK1)
    | ~ spl7_22 ),
    inference(avatar_component_clause,[],[f192])).

fof(f214,plain,
    ( spl7_25
    | ~ spl7_21 ),
    inference(avatar_split_clause,[],[f209,f188,f211])).

fof(f209,plain,
    ( l1_struct_0(sK2)
    | ~ spl7_21 ),
    inference(resolution,[],[f189,f58])).

fof(f189,plain,
    ( l1_pre_topc(sK2)
    | ~ spl7_21 ),
    inference(avatar_component_clause,[],[f188])).

fof(f208,plain,
    ( ~ spl7_15
    | spl7_23
    | ~ spl7_7 ),
    inference(avatar_split_clause,[],[f184,f108,f199,f148])).

fof(f184,plain,
    ( l1_pre_topc(sK4)
    | ~ l1_pre_topc(sK0)
    | ~ spl7_7 ),
    inference(resolution,[],[f59,f110])).

fof(f207,plain,
    ( ~ spl7_15
    | spl7_24
    | ~ spl7_9 ),
    inference(avatar_split_clause,[],[f183,f118,f203,f148])).

fof(f183,plain,
    ( l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK0)
    | ~ spl7_9 ),
    inference(resolution,[],[f59,f120])).

fof(f120,plain,
    ( m1_pre_topc(sK3,sK0)
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f118])).

fof(f206,plain,
    ( ~ spl7_23
    | spl7_24
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f182,f98,f203,f199])).

fof(f182,plain,
    ( l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK4)
    | ~ spl7_5 ),
    inference(resolution,[],[f59,f100])).

fof(f197,plain,
    ( ~ spl7_15
    | spl7_21
    | ~ spl7_11 ),
    inference(avatar_split_clause,[],[f181,f128,f188,f148])).

fof(f181,plain,
    ( l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ spl7_11 ),
    inference(resolution,[],[f59,f130])).

fof(f130,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f128])).

fof(f196,plain,
    ( ~ spl7_15
    | spl7_22
    | ~ spl7_13 ),
    inference(avatar_split_clause,[],[f180,f138,f192,f148])).

fof(f180,plain,
    ( l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl7_13 ),
    inference(resolution,[],[f59,f140])).

fof(f140,plain,
    ( m1_pre_topc(sK1,sK0)
    | ~ spl7_13 ),
    inference(avatar_component_clause,[],[f138])).

fof(f195,plain,
    ( ~ spl7_21
    | spl7_22
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f179,f103,f192,f188])).

fof(f179,plain,
    ( l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK2)
    | ~ spl7_6 ),
    inference(resolution,[],[f59,f105])).

fof(f178,plain,
    ( spl7_20
    | ~ spl7_18 ),
    inference(avatar_split_clause,[],[f168,f163,f175])).

fof(f175,plain,
    ( spl7_20
  <=> l1_struct_0(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f163,plain,
    ( spl7_18
  <=> l1_pre_topc(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f168,plain,
    ( l1_struct_0(sK6)
    | ~ spl7_18 ),
    inference(resolution,[],[f58,f165])).

fof(f165,plain,
    ( l1_pre_topc(sK6)
    | ~ spl7_18 ),
    inference(avatar_component_clause,[],[f163])).

fof(f173,plain,
    ( spl7_19
    | ~ spl7_15 ),
    inference(avatar_split_clause,[],[f167,f148,f170])).

fof(f170,plain,
    ( spl7_19
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f167,plain,
    ( l1_struct_0(sK0)
    | ~ spl7_15 ),
    inference(resolution,[],[f58,f150])).

fof(f150,plain,
    ( l1_pre_topc(sK0)
    | ~ spl7_15 ),
    inference(avatar_component_clause,[],[f148])).

fof(f166,plain,(
    spl7_18 ),
    inference(avatar_split_clause,[],[f78,f163])).

fof(f78,plain,(
    l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    l1_pre_topc(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f6,f41])).

fof(f41,plain,
    ( ? [X0] : l1_pre_topc(X0)
   => l1_pre_topc(sK6) ),
    introduced(choice_axiom,[])).

fof(f6,axiom,(
    ? [X0] : l1_pre_topc(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_l1_pre_topc)).

fof(f161,plain,(
    ~ spl7_17 ),
    inference(avatar_split_clause,[],[f43,f158])).

fof(f43,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,
    ( ( ~ r1_tsep_1(sK4,sK1)
      | ~ r1_tsep_1(sK2,sK3) )
    & ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),k1_tsep_1(sK0,sK1,sK3))
      | r1_tsep_1(sK2,sK4) )
    & m1_pre_topc(sK3,sK4)
    & m1_pre_topc(sK1,sK2)
    & m1_pre_topc(sK4,sK0)
    & ~ v2_struct_0(sK4)
    & m1_pre_topc(sK3,sK0)
    & ~ v2_struct_0(sK3)
    & m1_pre_topc(sK2,sK0)
    & ~ v2_struct_0(sK2)
    & m1_pre_topc(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f15,f37,f36,f35,f34,f33])).

fof(f33,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ( ~ r1_tsep_1(X4,X1)
                          | ~ r1_tsep_1(X2,X3) )
                        & ( r1_tsep_1(k2_tsep_1(X0,X2,X4),k1_tsep_1(X0,X1,X3))
                          | r1_tsep_1(X2,X4) )
                        & m1_pre_topc(X3,X4)
                        & m1_pre_topc(X1,X2)
                        & m1_pre_topc(X4,X0)
                        & ~ v2_struct_0(X4) )
                    & m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                & m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ~ r1_tsep_1(X4,X1)
                        | ~ r1_tsep_1(X2,X3) )
                      & ( r1_tsep_1(k2_tsep_1(sK0,X2,X4),k1_tsep_1(sK0,X1,X3))
                        | r1_tsep_1(X2,X4) )
                      & m1_pre_topc(X3,X4)
                      & m1_pre_topc(X1,X2)
                      & m1_pre_topc(X4,sK0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,sK0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,sK0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ( ~ r1_tsep_1(X4,X1)
                      | ~ r1_tsep_1(X2,X3) )
                    & ( r1_tsep_1(k2_tsep_1(sK0,X2,X4),k1_tsep_1(sK0,X1,X3))
                      | r1_tsep_1(X2,X4) )
                    & m1_pre_topc(X3,X4)
                    & m1_pre_topc(X1,X2)
                    & m1_pre_topc(X4,sK0)
                    & ~ v2_struct_0(X4) )
                & m1_pre_topc(X3,sK0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,sK0)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(X1,sK0)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ( ~ r1_tsep_1(X4,sK1)
                    | ~ r1_tsep_1(X2,X3) )
                  & ( r1_tsep_1(k2_tsep_1(sK0,X2,X4),k1_tsep_1(sK0,sK1,X3))
                    | r1_tsep_1(X2,X4) )
                  & m1_pre_topc(X3,X4)
                  & m1_pre_topc(sK1,X2)
                  & m1_pre_topc(X4,sK0)
                  & ~ v2_struct_0(X4) )
              & m1_pre_topc(X3,sK0)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,sK0)
          & ~ v2_struct_0(X2) )
      & m1_pre_topc(sK1,sK0)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ( ~ r1_tsep_1(X4,sK1)
                  | ~ r1_tsep_1(X2,X3) )
                & ( r1_tsep_1(k2_tsep_1(sK0,X2,X4),k1_tsep_1(sK0,sK1,X3))
                  | r1_tsep_1(X2,X4) )
                & m1_pre_topc(X3,X4)
                & m1_pre_topc(sK1,X2)
                & m1_pre_topc(X4,sK0)
                & ~ v2_struct_0(X4) )
            & m1_pre_topc(X3,sK0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(X2,sK0)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ( ~ r1_tsep_1(X4,sK1)
                | ~ r1_tsep_1(sK2,X3) )
              & ( r1_tsep_1(k2_tsep_1(sK0,sK2,X4),k1_tsep_1(sK0,sK1,X3))
                | r1_tsep_1(sK2,X4) )
              & m1_pre_topc(X3,X4)
              & m1_pre_topc(sK1,sK2)
              & m1_pre_topc(X4,sK0)
              & ~ v2_struct_0(X4) )
          & m1_pre_topc(X3,sK0)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK2,sK0)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ( ~ r1_tsep_1(X4,sK1)
              | ~ r1_tsep_1(sK2,X3) )
            & ( r1_tsep_1(k2_tsep_1(sK0,sK2,X4),k1_tsep_1(sK0,sK1,X3))
              | r1_tsep_1(sK2,X4) )
            & m1_pre_topc(X3,X4)
            & m1_pre_topc(sK1,sK2)
            & m1_pre_topc(X4,sK0)
            & ~ v2_struct_0(X4) )
        & m1_pre_topc(X3,sK0)
        & ~ v2_struct_0(X3) )
   => ( ? [X4] :
          ( ( ~ r1_tsep_1(X4,sK1)
            | ~ r1_tsep_1(sK2,sK3) )
          & ( r1_tsep_1(k2_tsep_1(sK0,sK2,X4),k1_tsep_1(sK0,sK1,sK3))
            | r1_tsep_1(sK2,X4) )
          & m1_pre_topc(sK3,X4)
          & m1_pre_topc(sK1,sK2)
          & m1_pre_topc(X4,sK0)
          & ~ v2_struct_0(X4) )
      & m1_pre_topc(sK3,sK0)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X4] :
        ( ( ~ r1_tsep_1(X4,sK1)
          | ~ r1_tsep_1(sK2,sK3) )
        & ( r1_tsep_1(k2_tsep_1(sK0,sK2,X4),k1_tsep_1(sK0,sK1,sK3))
          | r1_tsep_1(sK2,X4) )
        & m1_pre_topc(sK3,X4)
        & m1_pre_topc(sK1,sK2)
        & m1_pre_topc(X4,sK0)
        & ~ v2_struct_0(X4) )
   => ( ( ~ r1_tsep_1(sK4,sK1)
        | ~ r1_tsep_1(sK2,sK3) )
      & ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),k1_tsep_1(sK0,sK1,sK3))
        | r1_tsep_1(sK2,sK4) )
      & m1_pre_topc(sK3,sK4)
      & m1_pre_topc(sK1,sK2)
      & m1_pre_topc(sK4,sK0)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ~ r1_tsep_1(X4,X1)
                        | ~ r1_tsep_1(X2,X3) )
                      & ( r1_tsep_1(k2_tsep_1(X0,X2,X4),k1_tsep_1(X0,X1,X3))
                        | r1_tsep_1(X2,X4) )
                      & m1_pre_topc(X3,X4)
                      & m1_pre_topc(X1,X2)
                      & m1_pre_topc(X4,X0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
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
                      ( ( ~ r1_tsep_1(X4,X1)
                        | ~ r1_tsep_1(X2,X3) )
                      & ( r1_tsep_1(k2_tsep_1(X0,X2,X4),k1_tsep_1(X0,X1,X3))
                        | r1_tsep_1(X2,X4) )
                      & m1_pre_topc(X3,X4)
                      & m1_pre_topc(X1,X2)
                      & m1_pre_topc(X4,X0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
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
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ! [X4] :
                        ( ( m1_pre_topc(X4,X0)
                          & ~ v2_struct_0(X4) )
                       => ( ( m1_pre_topc(X3,X4)
                            & m1_pre_topc(X1,X2) )
                         => ( ( r1_tsep_1(X4,X1)
                              & r1_tsep_1(X2,X3) )
                            | ( ~ r1_tsep_1(k2_tsep_1(X0,X2,X4),k1_tsep_1(X0,X1,X3))
                              & ~ r1_tsep_1(X2,X4) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_pre_topc(X4,X0)
                        & ~ v2_struct_0(X4) )
                     => ( ( m1_pre_topc(X3,X4)
                          & m1_pre_topc(X1,X2) )
                       => ( ( r1_tsep_1(X4,X1)
                            & r1_tsep_1(X2,X3) )
                          | ( ~ r1_tsep_1(k2_tsep_1(X0,X2,X4),k1_tsep_1(X0,X1,X3))
                            & ~ r1_tsep_1(X2,X4) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tmap_1)).

fof(f156,plain,(
    spl7_16 ),
    inference(avatar_split_clause,[],[f44,f153])).

fof(f44,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f151,plain,(
    spl7_15 ),
    inference(avatar_split_clause,[],[f45,f148])).

fof(f45,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f146,plain,(
    ~ spl7_14 ),
    inference(avatar_split_clause,[],[f46,f143])).

fof(f46,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f141,plain,(
    spl7_13 ),
    inference(avatar_split_clause,[],[f47,f138])).

fof(f47,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f136,plain,(
    ~ spl7_12 ),
    inference(avatar_split_clause,[],[f48,f133])).

fof(f48,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f131,plain,(
    spl7_11 ),
    inference(avatar_split_clause,[],[f49,f128])).

fof(f49,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f126,plain,(
    ~ spl7_10 ),
    inference(avatar_split_clause,[],[f50,f123])).

fof(f50,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f38])).

fof(f121,plain,(
    spl7_9 ),
    inference(avatar_split_clause,[],[f51,f118])).

fof(f51,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f116,plain,(
    ~ spl7_8 ),
    inference(avatar_split_clause,[],[f52,f113])).

fof(f52,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f38])).

fof(f111,plain,(
    spl7_7 ),
    inference(avatar_split_clause,[],[f53,f108])).

fof(f53,plain,(
    m1_pre_topc(sK4,sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f106,plain,(
    spl7_6 ),
    inference(avatar_split_clause,[],[f54,f103])).

fof(f54,plain,(
    m1_pre_topc(sK1,sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f101,plain,(
    spl7_5 ),
    inference(avatar_split_clause,[],[f55,f98])).

fof(f55,plain,(
    m1_pre_topc(sK3,sK4) ),
    inference(cnf_transformation,[],[f38])).

fof(f96,plain,
    ( spl7_3
    | spl7_4 ),
    inference(avatar_split_clause,[],[f56,f93,f89])).

fof(f56,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),k1_tsep_1(sK0,sK1,sK3))
    | r1_tsep_1(sK2,sK4) ),
    inference(cnf_transformation,[],[f38])).

fof(f87,plain,
    ( ~ spl7_1
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f57,f84,f80])).

fof(f57,plain,
    ( ~ r1_tsep_1(sK4,sK1)
    | ~ r1_tsep_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f38])).

%------------------------------------------------------------------------------
