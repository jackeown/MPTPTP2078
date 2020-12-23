%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:28 EST 2020

% Result     : Theorem 2.54s
% Output     : Refutation 3.22s
% Verified   : 
% Statistics : Number of formulae       :  470 (1302 expanded)
%              Number of leaves         :   87 ( 515 expanded)
%              Depth                    :   31
%              Number of atoms          : 2935 (7853 expanded)
%              Number of equality atoms :  140 ( 605 expanded)
%              Maximal formula depth    :   22 (   7 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3669,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f132,f137,f142,f147,f152,f157,f162,f167,f173,f191,f204,f218,f225,f230,f247,f292,f302,f319,f324,f338,f343,f363,f370,f391,f440,f563,f651,f678,f697,f700,f701,f839,f844,f965,f1002,f1081,f1086,f1171,f1216,f1388,f1634,f1957,f2010,f2011,f2039,f2059,f2161,f2167,f2509,f2511,f2625,f2837,f2915,f2984,f3140,f3177,f3181,f3288,f3338,f3342,f3343,f3344,f3459,f3471,f3664])).

fof(f3664,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_16
    | ~ spl4_29
    | ~ spl4_78
    | ~ spl4_127
    | spl4_129
    | ~ spl4_131 ),
    inference(avatar_contradiction_clause,[],[f3663])).

fof(f3663,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_16
    | ~ spl4_29
    | ~ spl4_78
    | ~ spl4_127
    | spl4_129
    | ~ spl4_131 ),
    inference(subsumption_resolution,[],[f3634,f78])).

fof(f78,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f3634,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_16
    | ~ spl4_29
    | ~ spl4_78
    | ~ spl4_127
    | spl4_129
    | ~ spl4_131 ),
    inference(unit_resulting_resolution,[],[f131,f136,f246,f1108,f3287,f78,f3458,f3470,f2971])).

fof(f2971,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))),k1_xboole_0)))
        | ~ v5_pre_topc(X2,X3,sK1)
        | ~ v1_funct_2(X2,u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))),k1_xboole_0)
        | v5_pre_topc(X2,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)),sK1)
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),k1_xboole_0)))
        | ~ v1_funct_2(X2,u1_struct_0(X3),k1_xboole_0)
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(X3) )
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_29 ),
    inference(subsumption_resolution,[],[f2970,f141])).

fof(f141,plain,
    ( v2_pre_topc(sK1)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f139])).

fof(f139,plain,
    ( spl4_3
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f2970,plain,
    ( ! [X2,X3] :
        ( ~ v1_funct_2(X2,u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))),k1_xboole_0)
        | ~ v5_pre_topc(X2,X3,sK1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))),k1_xboole_0)))
        | v5_pre_topc(X2,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)),sK1)
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),k1_xboole_0)))
        | ~ v1_funct_2(X2,u1_struct_0(X3),k1_xboole_0)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(X3) )
    | ~ spl4_4
    | ~ spl4_29 ),
    inference(subsumption_resolution,[],[f2951,f146])).

fof(f146,plain,
    ( l1_pre_topc(sK1)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f144])).

fof(f144,plain,
    ( spl4_4
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f2951,plain,
    ( ! [X2,X3] :
        ( ~ v1_funct_2(X2,u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))),k1_xboole_0)
        | ~ v5_pre_topc(X2,X3,sK1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))),k1_xboole_0)))
        | v5_pre_topc(X2,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)),sK1)
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),k1_xboole_0)))
        | ~ v1_funct_2(X2,u1_struct_0(X3),k1_xboole_0)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(X3) )
    | ~ spl4_29 ),
    inference(superposition,[],[f120,f386])).

fof(f386,plain,
    ( k1_xboole_0 = u1_struct_0(sK1)
    | ~ spl4_29 ),
    inference(avatar_component_clause,[],[f384])).

fof(f384,plain,
    ( spl4_29
  <=> k1_xboole_0 = u1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).

fof(f120,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v5_pre_topc(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f111])).

fof(f111,plain,(
    ! [X0,X3,X1] :
      ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | ~ v5_pre_topc(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f86])).

fof(f86,plain,(
    ! [X2,X0,X3,X1] :
      ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | ~ v5_pre_topc(X2,X0,X1)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v5_pre_topc(X2,X0,X1)
                      | ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) )
                    & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
                      | ~ v5_pre_topc(X2,X0,X1) ) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                  | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                  | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                  | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                    & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                    & v1_funct_1(X3) )
                 => ( X2 = X3
                   => ( v5_pre_topc(X2,X0,X1)
                    <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_pre_topc)).

fof(f3470,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)
    | ~ spl4_131 ),
    inference(avatar_component_clause,[],[f3468])).

fof(f3468,plain,
    ( spl4_131
  <=> v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_131])])).

fof(f3458,plain,
    ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | spl4_129 ),
    inference(avatar_component_clause,[],[f3456])).

fof(f3456,plain,
    ( spl4_129
  <=> v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_129])])).

fof(f3287,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ spl4_127 ),
    inference(avatar_component_clause,[],[f3285])).

fof(f3285,plain,
    ( spl4_127
  <=> v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_127])])).

fof(f1108,plain,
    ( v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ spl4_78 ),
    inference(avatar_component_clause,[],[f1107])).

fof(f1107,plain,
    ( spl4_78
  <=> v5_pre_topc(k1_xboole_0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_78])])).

fof(f246,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f244])).

fof(f244,plain,
    ( spl4_16
  <=> v1_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f136,plain,
    ( l1_pre_topc(sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f134])).

fof(f134,plain,
    ( spl4_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f131,plain,
    ( v2_pre_topc(sK0)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f129])).

fof(f129,plain,
    ( spl4_1
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f3471,plain,
    ( spl4_131
    | ~ spl4_29
    | ~ spl4_41
    | ~ spl4_63 ),
    inference(avatar_split_clause,[],[f3383,f978,f640,f384,f3468])).

fof(f640,plain,
    ( spl4_41
  <=> v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).

fof(f978,plain,
    ( spl4_63
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_63])])).

fof(f3383,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)
    | ~ spl4_29
    | ~ spl4_41
    | ~ spl4_63 ),
    inference(forward_demodulation,[],[f3382,f980])).

fof(f980,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_63 ),
    inference(avatar_component_clause,[],[f978])).

fof(f3382,plain,
    ( v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)
    | ~ spl4_29
    | ~ spl4_41 ),
    inference(forward_demodulation,[],[f641,f386])).

fof(f641,plain,
    ( v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ spl4_41 ),
    inference(avatar_component_clause,[],[f640])).

fof(f3459,plain,
    ( ~ spl4_129
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_11
    | spl4_13
    | ~ spl4_15
    | ~ spl4_20
    | ~ spl4_27
    | ~ spl4_29
    | ~ spl4_41
    | ~ spl4_63 ),
    inference(avatar_split_clause,[],[f3428,f978,f640,f384,f367,f316,f227,f215,f201,f154,f149,f144,f139,f3456])).

fof(f149,plain,
    ( spl4_5
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f154,plain,
    ( spl4_6
  <=> sK2 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f201,plain,
    ( spl4_11
  <=> v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f215,plain,
    ( spl4_13
  <=> v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f227,plain,
    ( spl4_15
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f316,plain,
    ( spl4_20
  <=> v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f367,plain,
    ( spl4_27
  <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f3428,plain,
    ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_11
    | spl4_13
    | ~ spl4_15
    | ~ spl4_20
    | ~ spl4_27
    | ~ spl4_29
    | ~ spl4_41
    | ~ spl4_63 ),
    inference(subsumption_resolution,[],[f3427,f3383])).

fof(f3427,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_11
    | spl4_13
    | ~ spl4_15
    | ~ spl4_20
    | ~ spl4_27
    | ~ spl4_29
    | ~ spl4_63 ),
    inference(forward_demodulation,[],[f3426,f980])).

fof(f3426,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_11
    | spl4_13
    | ~ spl4_15
    | ~ spl4_20
    | ~ spl4_27
    | ~ spl4_29
    | ~ spl4_63 ),
    inference(forward_demodulation,[],[f3425,f386])).

fof(f3425,plain,
    ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_11
    | spl4_13
    | ~ spl4_15
    | ~ spl4_20
    | ~ spl4_27
    | ~ spl4_29
    | ~ spl4_63 ),
    inference(subsumption_resolution,[],[f3424,f78])).

fof(f3424,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)))
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_11
    | spl4_13
    | ~ spl4_15
    | ~ spl4_20
    | ~ spl4_27
    | ~ spl4_29
    | ~ spl4_63 ),
    inference(forward_demodulation,[],[f3423,f980])).

fof(f3423,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)))
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_11
    | spl4_13
    | ~ spl4_15
    | ~ spl4_20
    | ~ spl4_27
    | ~ spl4_29
    | ~ spl4_63 ),
    inference(forward_demodulation,[],[f3422,f386])).

fof(f3422,plain,
    ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_11
    | spl4_13
    | ~ spl4_15
    | ~ spl4_20
    | ~ spl4_27
    | ~ spl4_29
    | ~ spl4_63 ),
    inference(subsumption_resolution,[],[f3421,f3413])).

fof(f3413,plain,
    ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl4_6
    | spl4_13
    | ~ spl4_29
    | ~ spl4_63 ),
    inference(forward_demodulation,[],[f3412,f980])).

fof(f3412,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl4_6
    | spl4_13
    | ~ spl4_29 ),
    inference(forward_demodulation,[],[f3411,f156])).

fof(f156,plain,
    ( sK2 = sK3
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f154])).

fof(f3411,plain,
    ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | spl4_13
    | ~ spl4_29 ),
    inference(forward_demodulation,[],[f216,f386])).

fof(f216,plain,
    ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl4_13 ),
    inference(avatar_component_clause,[],[f215])).

fof(f3421,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_11
    | ~ spl4_15
    | ~ spl4_20
    | ~ spl4_27
    | ~ spl4_29
    | ~ spl4_63 ),
    inference(forward_demodulation,[],[f3420,f980])).

fof(f3420,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_11
    | ~ spl4_15
    | ~ spl4_20
    | ~ spl4_27
    | ~ spl4_29
    | ~ spl4_63 ),
    inference(forward_demodulation,[],[f3419,f386])).

fof(f3419,plain,
    ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_11
    | ~ spl4_15
    | ~ spl4_20
    | ~ spl4_27
    | ~ spl4_63 ),
    inference(forward_demodulation,[],[f1456,f980])).

fof(f1456,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_11
    | ~ spl4_15
    | ~ spl4_20
    | ~ spl4_27 ),
    inference(subsumption_resolution,[],[f1455,f318])).

fof(f318,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f316])).

fof(f1455,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_11
    | ~ spl4_15
    | ~ spl4_27 ),
    inference(subsumption_resolution,[],[f1454,f369])).

fof(f369,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl4_27 ),
    inference(avatar_component_clause,[],[f367])).

fof(f1454,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_11
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f1453,f141])).

fof(f1453,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_11
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f1452,f146])).

fof(f1452,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl4_5
    | ~ spl4_11
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f1451,f151])).

fof(f151,plain,
    ( v1_funct_1(sK2)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f149])).

fof(f1451,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl4_11
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f278,f229])).

fof(f229,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f227])).

fof(f278,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl4_11 ),
    inference(resolution,[],[f122,f203])).

fof(f203,plain,
    ( v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f201])).

fof(f122,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v5_pre_topc(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f109])).

fof(f109,plain,(
    ! [X0,X3,X1] :
      ( v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ v5_pre_topc(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f84])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] :
      ( v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ v5_pre_topc(X2,X0,X1)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v5_pre_topc(X2,X0,X1)
                      | ~ v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
                    & ( v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                      | ~ v5_pre_topc(X2,X0,X1) ) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                    & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                    & v1_funct_1(X3) )
                 => ( X2 = X3
                   => ( v5_pre_topc(X2,X0,X1)
                    <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_pre_topc)).

fof(f3344,plain,
    ( k1_xboole_0 != u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | k1_xboole_0 != u1_struct_0(sK1)
    | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f3343,plain,
    ( k1_xboole_0 != u1_struct_0(sK1)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != k1_relat_1(sK2)
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f3342,plain,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != k1_relat_1(sK2)
    | k1_xboole_0 != u1_struct_0(sK1)
    | v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f3338,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_8
    | ~ spl4_9
    | spl4_12
    | ~ spl4_29
    | ~ spl4_39
    | ~ spl4_43
    | ~ spl4_63
    | ~ spl4_76
    | ~ spl4_102 ),
    inference(avatar_contradiction_clause,[],[f3337])).

fof(f3337,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_8
    | ~ spl4_9
    | spl4_12
    | ~ spl4_29
    | ~ spl4_39
    | ~ spl4_43
    | ~ spl4_63
    | ~ spl4_76
    | ~ spl4_102 ),
    inference(subsumption_resolution,[],[f3336,f78])).

fof(f3336,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_8
    | ~ spl4_9
    | spl4_12
    | ~ spl4_29
    | ~ spl4_39
    | ~ spl4_43
    | ~ spl4_63
    | ~ spl4_76
    | ~ spl4_102 ),
    inference(forward_demodulation,[],[f3335,f980])).

fof(f3335,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_8
    | ~ spl4_9
    | spl4_12
    | ~ spl4_29
    | ~ spl4_39
    | ~ spl4_43
    | ~ spl4_63
    | ~ spl4_76
    | ~ spl4_102 ),
    inference(forward_demodulation,[],[f3334,f386])).

fof(f3334,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_8
    | ~ spl4_9
    | spl4_12
    | ~ spl4_29
    | ~ spl4_39
    | ~ spl4_43
    | ~ spl4_63
    | ~ spl4_76
    | ~ spl4_102 ),
    inference(subsumption_resolution,[],[f3333,f1085])).

fof(f1085,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl4_76 ),
    inference(avatar_component_clause,[],[f1083])).

fof(f1083,plain,
    ( spl4_76
  <=> v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_76])])).

fof(f3333,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_8
    | ~ spl4_9
    | spl4_12
    | ~ spl4_29
    | ~ spl4_39
    | ~ spl4_43
    | ~ spl4_63
    | ~ spl4_102 ),
    inference(forward_demodulation,[],[f3332,f980])).

fof(f3332,plain,
    ( ~ v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_8
    | ~ spl4_9
    | spl4_12
    | ~ spl4_29
    | ~ spl4_39
    | ~ spl4_43
    | ~ spl4_63
    | ~ spl4_102 ),
    inference(forward_demodulation,[],[f3331,f386])).

fof(f3331,plain,
    ( ~ v1_funct_2(sK2,k1_xboole_0,u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_8
    | ~ spl4_9
    | spl4_12
    | ~ spl4_39
    | ~ spl4_43
    | ~ spl4_63
    | ~ spl4_102 ),
    inference(subsumption_resolution,[],[f3330,f141])).

fof(f3330,plain,
    ( ~ v1_funct_2(sK2,k1_xboole_0,u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))))
    | ~ v2_pre_topc(sK1)
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_8
    | ~ spl4_9
    | spl4_12
    | ~ spl4_39
    | ~ spl4_43
    | ~ spl4_63
    | ~ spl4_102 ),
    inference(subsumption_resolution,[],[f3329,f146])).

fof(f3329,plain,
    ( ~ v1_funct_2(sK2,k1_xboole_0,u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_5
    | ~ spl4_8
    | ~ spl4_9
    | spl4_12
    | ~ spl4_39
    | ~ spl4_43
    | ~ spl4_63
    | ~ spl4_102 ),
    inference(subsumption_resolution,[],[f3328,f166])).

fof(f166,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f164])).

fof(f164,plain,
    ( spl4_8
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f3328,plain,
    ( ~ v1_funct_2(sK2,k1_xboole_0,u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_5
    | ~ spl4_9
    | spl4_12
    | ~ spl4_39
    | ~ spl4_43
    | ~ spl4_63
    | ~ spl4_102 ),
    inference(subsumption_resolution,[],[f3327,f172])).

fof(f172,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f170])).

fof(f170,plain,
    ( spl4_9
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f3327,plain,
    ( ~ v1_funct_2(sK2,k1_xboole_0,u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_5
    | spl4_12
    | ~ spl4_39
    | ~ spl4_43
    | ~ spl4_63
    | ~ spl4_102 ),
    inference(subsumption_resolution,[],[f3326,f151])).

fof(f3326,plain,
    ( ~ v1_funct_2(sK2,k1_xboole_0,u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl4_1
    | ~ spl4_2
    | spl4_12
    | ~ spl4_39
    | ~ spl4_43
    | ~ spl4_63
    | ~ spl4_102 ),
    inference(subsumption_resolution,[],[f3325,f212])).

fof(f212,plain,
    ( ~ v5_pre_topc(sK2,sK0,sK1)
    | spl4_12 ),
    inference(avatar_component_clause,[],[f211])).

fof(f211,plain,
    ( spl4_12
  <=> v5_pre_topc(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f3325,plain,
    ( ~ v1_funct_2(sK2,k1_xboole_0,u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))))
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_39
    | ~ spl4_43
    | ~ spl4_63
    | ~ spl4_102 ),
    inference(resolution,[],[f3023,f650])).

fof(f650,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl4_43 ),
    inference(avatar_component_clause,[],[f648])).

fof(f648,plain,
    ( spl4_43
  <=> v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).

fof(f3023,plain,
    ( ! [X4,X5] :
        ( ~ v5_pre_topc(X4,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X5)
        | ~ v1_funct_2(X4,k1_xboole_0,u1_struct_0(X5))
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X5))))
        | v5_pre_topc(X4,sK0,X5)
        | ~ v1_funct_1(X4)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X5))))
        | ~ v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X5))
        | ~ l1_pre_topc(X5)
        | ~ v2_pre_topc(X5) )
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_39
    | ~ spl4_63
    | ~ spl4_102 ),
    inference(forward_demodulation,[],[f3022,f1387])).

fof(f1387,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl4_102 ),
    inference(avatar_component_clause,[],[f1385])).

fof(f1385,plain,
    ( spl4_102
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_102])])).

fof(f3022,plain,
    ( ! [X4,X5] :
        ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),u1_struct_0(X5))))
        | ~ v1_funct_2(X4,k1_xboole_0,u1_struct_0(X5))
        | ~ v5_pre_topc(X4,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X5)
        | v5_pre_topc(X4,sK0,X5)
        | ~ v1_funct_1(X4)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X5))))
        | ~ v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X5))
        | ~ l1_pre_topc(X5)
        | ~ v2_pre_topc(X5) )
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_39
    | ~ spl4_63
    | ~ spl4_102 ),
    inference(forward_demodulation,[],[f3021,f980])).

fof(f3021,plain,
    ( ! [X4,X5] :
        ( ~ v1_funct_2(X4,k1_xboole_0,u1_struct_0(X5))
        | ~ v5_pre_topc(X4,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X5)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X5))))
        | v5_pre_topc(X4,sK0,X5)
        | ~ v1_funct_1(X4)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X5))))
        | ~ v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X5))
        | ~ l1_pre_topc(X5)
        | ~ v2_pre_topc(X5) )
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_39
    | ~ spl4_63
    | ~ spl4_102 ),
    inference(forward_demodulation,[],[f3020,f1387])).

fof(f3020,plain,
    ( ! [X4,X5] :
        ( ~ v1_funct_2(X4,k1_relat_1(k1_xboole_0),u1_struct_0(X5))
        | ~ v5_pre_topc(X4,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X5)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X5))))
        | v5_pre_topc(X4,sK0,X5)
        | ~ v1_funct_1(X4)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X5))))
        | ~ v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X5))
        | ~ l1_pre_topc(X5)
        | ~ v2_pre_topc(X5) )
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_39
    | ~ spl4_63 ),
    inference(forward_demodulation,[],[f3019,f980])).

fof(f3019,plain,
    ( ! [X4,X5] :
        ( ~ v1_funct_2(X4,k1_relat_1(sK2),u1_struct_0(X5))
        | ~ v5_pre_topc(X4,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X5)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X5))))
        | v5_pre_topc(X4,sK0,X5)
        | ~ v1_funct_1(X4)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X5))))
        | ~ v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X5))
        | ~ l1_pre_topc(X5)
        | ~ v2_pre_topc(X5) )
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_39 ),
    inference(subsumption_resolution,[],[f3018,f131])).

fof(f3018,plain,
    ( ! [X4,X5] :
        ( ~ v1_funct_2(X4,k1_relat_1(sK2),u1_struct_0(X5))
        | ~ v5_pre_topc(X4,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X5)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X5))))
        | v5_pre_topc(X4,sK0,X5)
        | ~ v1_funct_1(X4)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X5))))
        | ~ v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X5))
        | ~ l1_pre_topc(X5)
        | ~ v2_pre_topc(X5)
        | ~ v2_pre_topc(sK0) )
    | ~ spl4_2
    | ~ spl4_39 ),
    inference(subsumption_resolution,[],[f2993,f136])).

fof(f2993,plain,
    ( ! [X4,X5] :
        ( ~ v1_funct_2(X4,k1_relat_1(sK2),u1_struct_0(X5))
        | ~ v5_pre_topc(X4,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X5)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X5))))
        | v5_pre_topc(X4,sK0,X5)
        | ~ v1_funct_1(X4)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X5))))
        | ~ v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X5))
        | ~ l1_pre_topc(X5)
        | ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl4_39 ),
    inference(superposition,[],[f121,f562])).

fof(f562,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK2)
    | ~ spl4_39 ),
    inference(avatar_component_clause,[],[f560])).

fof(f560,plain,
    ( spl4_39
  <=> u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).

fof(f121,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | v5_pre_topc(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f110])).

fof(f110,plain,(
    ! [X0,X3,X1] :
      ( v5_pre_topc(X3,X0,X1)
      | ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f87])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f3288,plain,
    ( spl4_127
    | ~ spl4_8
    | ~ spl4_29
    | ~ spl4_63 ),
    inference(avatar_split_clause,[],[f2959,f978,f384,f164,f3285])).

fof(f2959,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ spl4_8
    | ~ spl4_29
    | ~ spl4_63 ),
    inference(forward_demodulation,[],[f2923,f980])).

fof(f2923,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0)
    | ~ spl4_8
    | ~ spl4_29 ),
    inference(superposition,[],[f166,f386])).

fof(f3181,plain,
    ( ~ spl4_29
    | spl4_46
    | ~ spl4_63 ),
    inference(avatar_contradiction_clause,[],[f3180])).

fof(f3180,plain,
    ( $false
    | ~ spl4_29
    | spl4_46
    | ~ spl4_63 ),
    inference(subsumption_resolution,[],[f3179,f78])).

fof(f3179,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
    | ~ spl4_29
    | spl4_46
    | ~ spl4_63 ),
    inference(forward_demodulation,[],[f3178,f980])).

fof(f3178,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
    | ~ spl4_29
    | spl4_46 ),
    inference(forward_demodulation,[],[f673,f386])).

fof(f673,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | spl4_46 ),
    inference(avatar_component_clause,[],[f671])).

fof(f671,plain,
    ( spl4_46
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).

fof(f3177,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_8
    | ~ spl4_9
    | spl4_12
    | ~ spl4_29
    | ~ spl4_45
    | ~ spl4_47
    | ~ spl4_63 ),
    inference(avatar_contradiction_clause,[],[f3176])).

fof(f3176,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_8
    | ~ spl4_9
    | spl4_12
    | ~ spl4_29
    | ~ spl4_45
    | ~ spl4_47
    | ~ spl4_63 ),
    inference(subsumption_resolution,[],[f3175,f78])).

fof(f3175,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_8
    | ~ spl4_9
    | spl4_12
    | ~ spl4_29
    | ~ spl4_45
    | ~ spl4_47
    | ~ spl4_63 ),
    inference(forward_demodulation,[],[f3174,f980])).

fof(f3174,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_8
    | ~ spl4_9
    | spl4_12
    | ~ spl4_29
    | ~ spl4_45
    | ~ spl4_47 ),
    inference(forward_demodulation,[],[f3118,f386])).

fof(f3118,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_8
    | ~ spl4_9
    | spl4_12
    | ~ spl4_45
    | ~ spl4_47 ),
    inference(unit_resulting_resolution,[],[f131,f136,f141,f146,f151,f212,f166,f172,f677,f668,f123])).

fof(f123,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | v5_pre_topc(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f108])).

fof(f108,plain,(
    ! [X0,X3,X1] :
      ( v5_pre_topc(X3,X0,X1)
      | ~ v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
    ! [X2,X0,X3,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | ~ v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f668,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl4_45 ),
    inference(avatar_component_clause,[],[f667])).

fof(f667,plain,
    ( spl4_45
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_45])])).

fof(f677,plain,
    ( v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl4_47 ),
    inference(avatar_component_clause,[],[f675])).

fof(f675,plain,
    ( spl4_47
  <=> v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_47])])).

fof(f3140,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_8
    | ~ spl4_9
    | spl4_12
    | ~ spl4_45
    | ~ spl4_46
    | ~ spl4_47 ),
    inference(avatar_contradiction_clause,[],[f3139])).

fof(f3139,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_8
    | ~ spl4_9
    | spl4_12
    | ~ spl4_45
    | ~ spl4_46
    | ~ spl4_47 ),
    inference(subsumption_resolution,[],[f3138,f131])).

fof(f3138,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_8
    | ~ spl4_9
    | spl4_12
    | ~ spl4_45
    | ~ spl4_46
    | ~ spl4_47 ),
    inference(subsumption_resolution,[],[f3137,f136])).

fof(f3137,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_8
    | ~ spl4_9
    | spl4_12
    | ~ spl4_45
    | ~ spl4_46
    | ~ spl4_47 ),
    inference(subsumption_resolution,[],[f3136,f141])).

fof(f3136,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_8
    | ~ spl4_9
    | spl4_12
    | ~ spl4_45
    | ~ spl4_46
    | ~ spl4_47 ),
    inference(subsumption_resolution,[],[f3135,f146])).

fof(f3135,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl4_5
    | ~ spl4_8
    | ~ spl4_9
    | spl4_12
    | ~ spl4_45
    | ~ spl4_46
    | ~ spl4_47 ),
    inference(subsumption_resolution,[],[f3134,f166])).

fof(f3134,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl4_5
    | ~ spl4_9
    | spl4_12
    | ~ spl4_45
    | ~ spl4_46
    | ~ spl4_47 ),
    inference(subsumption_resolution,[],[f3133,f172])).

fof(f3133,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl4_5
    | spl4_12
    | ~ spl4_45
    | ~ spl4_46
    | ~ spl4_47 ),
    inference(subsumption_resolution,[],[f3132,f151])).

fof(f3132,plain,
    ( ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | spl4_12
    | ~ spl4_45
    | ~ spl4_46
    | ~ spl4_47 ),
    inference(subsumption_resolution,[],[f3131,f212])).

fof(f3131,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl4_45
    | ~ spl4_46
    | ~ spl4_47 ),
    inference(subsumption_resolution,[],[f3130,f672])).

fof(f672,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ spl4_46 ),
    inference(avatar_component_clause,[],[f671])).

fof(f3130,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl4_45
    | ~ spl4_47 ),
    inference(subsumption_resolution,[],[f3120,f677])).

fof(f3120,plain,
    ( ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl4_45 ),
    inference(resolution,[],[f668,f123])).

fof(f2984,plain,
    ( spl4_37
    | ~ spl4_5
    | ~ spl4_8
    | ~ spl4_9
    | spl4_86 ),
    inference(avatar_split_clause,[],[f2882,f1168,f170,f164,f149,f551])).

fof(f551,plain,
    ( spl4_37
  <=> v1_xboole_0(u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).

fof(f1168,plain,
    ( spl4_86
  <=> v1_partfun1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_86])])).

fof(f2882,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | ~ spl4_5
    | ~ spl4_8
    | ~ spl4_9
    | spl4_86 ),
    inference(subsumption_resolution,[],[f535,f1170])).

fof(f1170,plain,
    ( ~ v1_partfun1(sK2,u1_struct_0(sK0))
    | spl4_86 ),
    inference(avatar_component_clause,[],[f1168])).

fof(f535,plain,
    ( v1_partfun1(sK2,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ spl4_5
    | ~ spl4_8
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f533,f172])).

fof(f533,plain,
    ( v1_partfun1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ spl4_5
    | ~ spl4_8 ),
    inference(resolution,[],[f256,f166])).

fof(f256,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(sK2,X0,X1)
        | v1_partfun1(sK2,X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_xboole_0(X1) )
    | ~ spl4_5 ),
    inference(resolution,[],[f89,f151])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | v1_partfun1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f2915,plain,
    ( spl4_14
    | ~ spl4_6
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f2864,f215,f154,f221])).

fof(f221,plain,
    ( spl4_14
  <=> v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f2864,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl4_6
    | ~ spl4_13 ),
    inference(forward_demodulation,[],[f217,f156])).

fof(f217,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f215])).

fof(f2837,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | spl4_12
    | ~ spl4_26
    | ~ spl4_30
    | ~ spl4_32
    | ~ spl4_47
    | ~ spl4_57
    | ~ spl4_68 ),
    inference(avatar_contradiction_clause,[],[f2836])).

fof(f2836,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | spl4_12
    | ~ spl4_26
    | ~ spl4_30
    | ~ spl4_32
    | ~ spl4_47
    | ~ spl4_57
    | ~ spl4_68 ),
    inference(subsumption_resolution,[],[f2835,f677])).

fof(f2835,plain,
    ( ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | spl4_12
    | ~ spl4_26
    | ~ spl4_30
    | ~ spl4_32
    | ~ spl4_57
    | ~ spl4_68 ),
    inference(unit_resulting_resolution,[],[f141,f146,f151,f1001,f362,f843,f439,f212,f491])).

fof(f491,plain,
    ( ! [X12,X13] :
        ( ~ v5_pre_topc(X12,sK0,g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13)))
        | ~ v1_funct_2(X12,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13))))
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13))))))
        | v5_pre_topc(X12,sK0,X13)
        | ~ v1_funct_1(X12)
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X13))))
        | ~ v1_funct_2(X12,k1_relat_1(sK2),u1_struct_0(X13))
        | ~ l1_pre_topc(X13)
        | ~ v2_pre_topc(X13) )
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f490,f131])).

fof(f490,plain,
    ( ! [X12,X13] :
        ( ~ v1_funct_2(X12,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13))))
        | ~ v5_pre_topc(X12,sK0,g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13)))
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13))))))
        | v5_pre_topc(X12,sK0,X13)
        | ~ v1_funct_1(X12)
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X13))))
        | ~ v1_funct_2(X12,k1_relat_1(sK2),u1_struct_0(X13))
        | ~ l1_pre_topc(X13)
        | ~ v2_pre_topc(X13)
        | ~ v2_pre_topc(sK0) )
    | ~ spl4_2
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f476,f136])).

fof(f476,plain,
    ( ! [X12,X13] :
        ( ~ v1_funct_2(X12,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13))))
        | ~ v5_pre_topc(X12,sK0,g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13)))
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13))))))
        | v5_pre_topc(X12,sK0,X13)
        | ~ v1_funct_1(X12)
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X13))))
        | ~ v1_funct_2(X12,k1_relat_1(sK2),u1_struct_0(X13))
        | ~ l1_pre_topc(X13)
        | ~ v2_pre_topc(X13)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl4_30 ),
    inference(superposition,[],[f123,f390])).

fof(f390,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK2)
    | ~ spl4_30 ),
    inference(avatar_component_clause,[],[f388])).

fof(f388,plain,
    ( spl4_30
  <=> u1_struct_0(sK0) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f439,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ spl4_32 ),
    inference(avatar_component_clause,[],[f437])).

fof(f437,plain,
    ( spl4_32
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f843,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl4_57 ),
    inference(avatar_component_clause,[],[f841])).

fof(f841,plain,
    ( spl4_57
  <=> v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_57])])).

fof(f362,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))))
    | ~ spl4_26 ),
    inference(avatar_component_clause,[],[f360])).

fof(f360,plain,
    ( spl4_26
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f1001,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))
    | ~ spl4_68 ),
    inference(avatar_component_clause,[],[f999])).

fof(f999,plain,
    ( spl4_68
  <=> v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_68])])).

fof(f2625,plain,
    ( u1_struct_0(sK0) != k1_relat_1(sK2)
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f2511,plain,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | k1_xboole_0 != u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | u1_struct_0(sK0) != k1_relat_1(sK2)
    | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f2509,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_12
    | ~ spl4_26
    | ~ spl4_30
    | ~ spl4_32
    | ~ spl4_57
    | ~ spl4_63
    | ~ spl4_68
    | spl4_112 ),
    inference(avatar_contradiction_clause,[],[f2508])).

fof(f2508,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_12
    | ~ spl4_26
    | ~ spl4_30
    | ~ spl4_32
    | ~ spl4_57
    | ~ spl4_63
    | ~ spl4_68
    | spl4_112 ),
    inference(subsumption_resolution,[],[f2507,f2166])).

fof(f2166,plain,
    ( ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl4_112 ),
    inference(avatar_component_clause,[],[f2164])).

fof(f2164,plain,
    ( spl4_112
  <=> v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_112])])).

fof(f2507,plain,
    ( v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_12
    | ~ spl4_26
    | ~ spl4_30
    | ~ spl4_32
    | ~ spl4_57
    | ~ spl4_63
    | ~ spl4_68 ),
    inference(forward_demodulation,[],[f2506,f980])).

fof(f2506,plain,
    ( v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_12
    | ~ spl4_26
    | ~ spl4_30
    | ~ spl4_32
    | ~ spl4_57
    | ~ spl4_68 ),
    inference(subsumption_resolution,[],[f2505,f141])).

fof(f2505,plain,
    ( v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK1)
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_12
    | ~ spl4_26
    | ~ spl4_30
    | ~ spl4_32
    | ~ spl4_57
    | ~ spl4_68 ),
    inference(subsumption_resolution,[],[f2504,f146])).

fof(f2504,plain,
    ( v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_5
    | ~ spl4_12
    | ~ spl4_26
    | ~ spl4_30
    | ~ spl4_32
    | ~ spl4_57
    | ~ spl4_68 ),
    inference(subsumption_resolution,[],[f2503,f1001])).

fof(f2503,plain,
    ( v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_5
    | ~ spl4_12
    | ~ spl4_26
    | ~ spl4_30
    | ~ spl4_32
    | ~ spl4_57 ),
    inference(subsumption_resolution,[],[f2502,f362])).

fof(f2502,plain,
    ( v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_5
    | ~ spl4_12
    | ~ spl4_30
    | ~ spl4_32
    | ~ spl4_57 ),
    inference(subsumption_resolution,[],[f2501,f151])).

fof(f2501,plain,
    ( v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_12
    | ~ spl4_30
    | ~ spl4_32
    | ~ spl4_57 ),
    inference(subsumption_resolution,[],[f2500,f439])).

fof(f2500,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_12
    | ~ spl4_30
    | ~ spl4_57 ),
    inference(subsumption_resolution,[],[f2482,f843])).

fof(f2482,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_12
    | ~ spl4_30 ),
    inference(resolution,[],[f487,f213])).

fof(f213,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f211])).

fof(f487,plain,
    ( ! [X8,X9] :
        ( ~ v5_pre_topc(X8,sK0,X9)
        | ~ v1_funct_2(X8,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(X9),u1_pre_topc(X9))))
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(X9),u1_pre_topc(X9))))))
        | v5_pre_topc(X8,sK0,g1_pre_topc(u1_struct_0(X9),u1_pre_topc(X9)))
        | ~ v1_funct_1(X8)
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X9))))
        | ~ v1_funct_2(X8,k1_relat_1(sK2),u1_struct_0(X9))
        | ~ l1_pre_topc(X9)
        | ~ v2_pre_topc(X9) )
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f486,f131])).

fof(f486,plain,
    ( ! [X8,X9] :
        ( ~ v1_funct_2(X8,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(X9),u1_pre_topc(X9))))
        | ~ v5_pre_topc(X8,sK0,X9)
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(X9),u1_pre_topc(X9))))))
        | v5_pre_topc(X8,sK0,g1_pre_topc(u1_struct_0(X9),u1_pre_topc(X9)))
        | ~ v1_funct_1(X8)
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X9))))
        | ~ v1_funct_2(X8,k1_relat_1(sK2),u1_struct_0(X9))
        | ~ l1_pre_topc(X9)
        | ~ v2_pre_topc(X9)
        | ~ v2_pre_topc(sK0) )
    | ~ spl4_2
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f474,f136])).

fof(f474,plain,
    ( ! [X8,X9] :
        ( ~ v1_funct_2(X8,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(X9),u1_pre_topc(X9))))
        | ~ v5_pre_topc(X8,sK0,X9)
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(X9),u1_pre_topc(X9))))))
        | v5_pre_topc(X8,sK0,g1_pre_topc(u1_struct_0(X9),u1_pre_topc(X9)))
        | ~ v1_funct_1(X8)
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X9))))
        | ~ v1_funct_2(X8,k1_relat_1(sK2),u1_struct_0(X9))
        | ~ l1_pre_topc(X9)
        | ~ v2_pre_topc(X9)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl4_30 ),
    inference(superposition,[],[f122,f390])).

fof(f2167,plain,
    ( ~ spl4_112
    | spl4_47
    | ~ spl4_63 ),
    inference(avatar_split_clause,[],[f2162,f978,f675,f2164])).

fof(f2162,plain,
    ( ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl4_47
    | ~ spl4_63 ),
    inference(forward_demodulation,[],[f676,f980])).

fof(f676,plain,
    ( ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl4_47 ),
    inference(avatar_component_clause,[],[f675])).

fof(f2161,plain,
    ( ~ spl4_47
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_5
    | ~ spl4_11
    | ~ spl4_15
    | ~ spl4_21
    | ~ spl4_30
    | ~ spl4_32
    | ~ spl4_57
    | ~ spl4_62
    | spl4_91 ),
    inference(avatar_split_clause,[],[f2064,f1213,f962,f841,f437,f388,f321,f227,f201,f149,f134,f129,f675])).

fof(f321,plain,
    ( spl4_21
  <=> v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f962,plain,
    ( spl4_62
  <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_62])])).

fof(f1213,plain,
    ( spl4_91
  <=> v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_91])])).

fof(f2064,plain,
    ( ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_5
    | ~ spl4_11
    | ~ spl4_15
    | ~ spl4_21
    | ~ spl4_30
    | ~ spl4_32
    | ~ spl4_57
    | ~ spl4_62
    | spl4_91 ),
    inference(subsumption_resolution,[],[f2063,f1214])).

fof(f1214,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl4_91 ),
    inference(avatar_component_clause,[],[f1213])).

fof(f2063,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_5
    | ~ spl4_11
    | ~ spl4_15
    | ~ spl4_21
    | ~ spl4_30
    | ~ spl4_32
    | ~ spl4_57
    | ~ spl4_62 ),
    inference(subsumption_resolution,[],[f2016,f843])).

fof(f2016,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_5
    | ~ spl4_11
    | ~ spl4_15
    | ~ spl4_21
    | ~ spl4_30
    | ~ spl4_32
    | ~ spl4_62 ),
    inference(forward_demodulation,[],[f2015,f390])).

fof(f2015,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_5
    | ~ spl4_11
    | ~ spl4_15
    | ~ spl4_21
    | ~ spl4_30
    | ~ spl4_32
    | ~ spl4_62 ),
    inference(subsumption_resolution,[],[f2014,f439])).

fof(f2014,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_5
    | ~ spl4_11
    | ~ spl4_15
    | ~ spl4_21
    | ~ spl4_30
    | ~ spl4_62 ),
    inference(forward_demodulation,[],[f2013,f390])).

fof(f2013,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_5
    | ~ spl4_11
    | ~ spl4_15
    | ~ spl4_21
    | ~ spl4_30
    | ~ spl4_62 ),
    inference(forward_demodulation,[],[f1905,f390])).

fof(f1905,plain,
    ( ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_5
    | ~ spl4_11
    | ~ spl4_15
    | ~ spl4_21
    | ~ spl4_62 ),
    inference(subsumption_resolution,[],[f1502,f964])).

fof(f964,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl4_62 ),
    inference(avatar_component_clause,[],[f962])).

fof(f1502,plain,
    ( ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_5
    | ~ spl4_11
    | ~ spl4_15
    | ~ spl4_21 ),
    inference(subsumption_resolution,[],[f1501,f131])).

fof(f1501,plain,
    ( ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK0)
    | ~ spl4_2
    | ~ spl4_5
    | ~ spl4_11
    | ~ spl4_15
    | ~ spl4_21 ),
    inference(subsumption_resolution,[],[f1500,f136])).

fof(f1500,plain,
    ( ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl4_5
    | ~ spl4_11
    | ~ spl4_15
    | ~ spl4_21 ),
    inference(subsumption_resolution,[],[f1499,f323])).

fof(f323,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f321])).

fof(f1499,plain,
    ( ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl4_5
    | ~ spl4_11
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f1498,f151])).

fof(f1498,plain,
    ( ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl4_11
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f265,f229])).

fof(f265,plain,
    ( ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl4_11 ),
    inference(resolution,[],[f120,f203])).

fof(f2059,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_20
    | ~ spl4_26
    | ~ spl4_27
    | ~ spl4_30
    | ~ spl4_39
    | ~ spl4_44
    | ~ spl4_68
    | spl4_91 ),
    inference(avatar_contradiction_clause,[],[f2058])).

fof(f2058,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_20
    | ~ spl4_26
    | ~ spl4_27
    | ~ spl4_30
    | ~ spl4_39
    | ~ spl4_44
    | ~ spl4_68
    | spl4_91 ),
    inference(subsumption_resolution,[],[f2057,f362])).

fof(f2057,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_20
    | ~ spl4_26
    | ~ spl4_27
    | ~ spl4_30
    | ~ spl4_39
    | ~ spl4_44
    | ~ spl4_68
    | spl4_91 ),
    inference(forward_demodulation,[],[f2056,f1868])).

fof(f1868,plain,
    ( k1_relat_1(sK2) = u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ spl4_30
    | ~ spl4_39 ),
    inference(forward_demodulation,[],[f562,f390])).

fof(f2056,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_20
    | ~ spl4_26
    | ~ spl4_27
    | ~ spl4_30
    | ~ spl4_39
    | ~ spl4_44
    | ~ spl4_68
    | spl4_91 ),
    inference(subsumption_resolution,[],[f2055,f141])).

fof(f2055,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v2_pre_topc(sK1)
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_20
    | ~ spl4_26
    | ~ spl4_27
    | ~ spl4_30
    | ~ spl4_39
    | ~ spl4_44
    | ~ spl4_68
    | spl4_91 ),
    inference(subsumption_resolution,[],[f2054,f146])).

fof(f2054,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_20
    | ~ spl4_26
    | ~ spl4_27
    | ~ spl4_30
    | ~ spl4_39
    | ~ spl4_44
    | ~ spl4_68
    | spl4_91 ),
    inference(subsumption_resolution,[],[f2053,f1001])).

fof(f2053,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_20
    | ~ spl4_26
    | ~ spl4_27
    | ~ spl4_30
    | ~ spl4_39
    | ~ spl4_44
    | spl4_91 ),
    inference(subsumption_resolution,[],[f2052,f362])).

fof(f2052,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_20
    | ~ spl4_26
    | ~ spl4_27
    | ~ spl4_30
    | ~ spl4_39
    | ~ spl4_44
    | spl4_91 ),
    inference(subsumption_resolution,[],[f2051,f151])).

fof(f2051,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_20
    | ~ spl4_26
    | ~ spl4_27
    | ~ spl4_30
    | ~ spl4_39
    | ~ spl4_44
    | spl4_91 ),
    inference(subsumption_resolution,[],[f2050,f2047])).

fof(f2047,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1)
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_11
    | ~ spl4_15
    | ~ spl4_20
    | ~ spl4_26
    | ~ spl4_27
    | ~ spl4_30
    | ~ spl4_39
    | ~ spl4_44
    | spl4_91 ),
    inference(subsumption_resolution,[],[f2046,f655])).

fof(f655,plain,
    ( v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ spl4_44 ),
    inference(avatar_component_clause,[],[f654])).

fof(f654,plain,
    ( spl4_44
  <=> v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).

fof(f2046,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1)
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_11
    | ~ spl4_15
    | ~ spl4_20
    | ~ spl4_26
    | ~ spl4_27
    | ~ spl4_30
    | ~ spl4_39
    | spl4_91 ),
    inference(forward_demodulation,[],[f2045,f390])).

fof(f2045,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_11
    | ~ spl4_15
    | ~ spl4_20
    | ~ spl4_26
    | ~ spl4_27
    | ~ spl4_30
    | ~ spl4_39
    | spl4_91 ),
    inference(subsumption_resolution,[],[f2044,f362])).

fof(f2044,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))))
    | ~ v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_11
    | ~ spl4_15
    | ~ spl4_20
    | ~ spl4_27
    | ~ spl4_30
    | ~ spl4_39
    | spl4_91 ),
    inference(forward_demodulation,[],[f2043,f1868])).

fof(f2043,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_11
    | ~ spl4_15
    | ~ spl4_20
    | ~ spl4_27
    | ~ spl4_30
    | spl4_91 ),
    inference(forward_demodulation,[],[f2042,f390])).

fof(f2042,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_11
    | ~ spl4_15
    | ~ spl4_20
    | ~ spl4_27
    | ~ spl4_30
    | spl4_91 ),
    inference(subsumption_resolution,[],[f2041,f1214])).

fof(f2041,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_11
    | ~ spl4_15
    | ~ spl4_20
    | ~ spl4_27
    | ~ spl4_30 ),
    inference(forward_demodulation,[],[f1457,f390])).

fof(f1457,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1)
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_11
    | ~ spl4_15
    | ~ spl4_20
    | ~ spl4_27
    | ~ spl4_30 ),
    inference(forward_demodulation,[],[f1456,f390])).

fof(f2050,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_12
    | ~ spl4_30
    | ~ spl4_44 ),
    inference(subsumption_resolution,[],[f2049,f655])).

fof(f2049,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_12
    | ~ spl4_30 ),
    inference(resolution,[],[f213,f479])).

fof(f479,plain,
    ( ! [X0,X1] :
        ( ~ v5_pre_topc(X0,sK0,X1)
        | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X1))))
        | v5_pre_topc(X0,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X1)
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X1))))
        | ~ v1_funct_2(X0,k1_relat_1(sK2),u1_struct_0(X1))
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1) )
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f478,f131])).

fof(f478,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X1))
        | ~ v5_pre_topc(X0,sK0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X1))))
        | v5_pre_topc(X0,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X1)
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X1))))
        | ~ v1_funct_2(X0,k1_relat_1(sK2),u1_struct_0(X1))
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | ~ v2_pre_topc(sK0) )
    | ~ spl4_2
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f470,f136])).

fof(f470,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X1))
        | ~ v5_pre_topc(X0,sK0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X1))))
        | v5_pre_topc(X0,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X1)
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X1))))
        | ~ v1_funct_2(X0,k1_relat_1(sK2),u1_struct_0(X1))
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl4_30 ),
    inference(superposition,[],[f120,f390])).

fof(f2039,plain,
    ( sK2 != sK3
    | u1_struct_0(sK0) != k1_relat_1(sK2)
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f2011,plain,
    ( u1_struct_0(sK0) != k1_relat_1(sK2)
    | k1_xboole_0 != u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),k1_xboole_0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f2010,plain,
    ( ~ spl4_7
    | spl4_56
    | ~ spl4_59 ),
    inference(avatar_contradiction_clause,[],[f2009])).

fof(f2009,plain,
    ( $false
    | ~ spl4_7
    | spl4_56
    | ~ spl4_59 ),
    inference(subsumption_resolution,[],[f837,f908])).

fof(f908,plain,
    ( v1_xboole_0(sK2)
    | ~ spl4_7
    | ~ spl4_59 ),
    inference(resolution,[],[f899,f209])).

fof(f209,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
        | v1_xboole_0(X0) )
    | ~ spl4_7 ),
    inference(resolution,[],[f90,f161])).

fof(f161,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f159])).

fof(f159,plain,
    ( spl4_7
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

fof(f899,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),k1_xboole_0)))
    | ~ spl4_59 ),
    inference(avatar_component_clause,[],[f897])).

fof(f897,plain,
    ( spl4_59
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_59])])).

fof(f837,plain,
    ( ~ v1_xboole_0(sK2)
    | spl4_56 ),
    inference(avatar_component_clause,[],[f836])).

fof(f836,plain,
    ( spl4_56
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_56])])).

fof(f1957,plain,
    ( ~ spl4_7
    | ~ spl4_19
    | ~ spl4_56
    | spl4_63 ),
    inference(avatar_contradiction_clause,[],[f1956])).

fof(f1956,plain,
    ( $false
    | ~ spl4_7
    | ~ spl4_19
    | ~ spl4_56
    | spl4_63 ),
    inference(subsumption_resolution,[],[f979,f932])).

fof(f932,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_7
    | ~ spl4_19
    | ~ spl4_56 ),
    inference(forward_demodulation,[],[f923,f307])).

fof(f307,plain,
    ( k1_xboole_0 = k6_partfun1(k1_xboole_0)
    | ~ spl4_7
    | ~ spl4_19 ),
    inference(unit_resulting_resolution,[],[f161,f301,f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | X0 = X1
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

fof(f301,plain,
    ( v1_xboole_0(k6_partfun1(k1_xboole_0))
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f299])).

fof(f299,plain,
    ( spl4_19
  <=> v1_xboole_0(k6_partfun1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f923,plain,
    ( sK2 = k6_partfun1(k1_xboole_0)
    | ~ spl4_19
    | ~ spl4_56 ),
    inference(unit_resulting_resolution,[],[f301,f838,f97])).

fof(f838,plain,
    ( v1_xboole_0(sK2)
    | ~ spl4_56 ),
    inference(avatar_component_clause,[],[f836])).

fof(f979,plain,
    ( k1_xboole_0 != sK2
    | spl4_63 ),
    inference(avatar_component_clause,[],[f978])).

fof(f1634,plain,
    ( spl4_78
    | ~ spl4_12
    | ~ spl4_63 ),
    inference(avatar_split_clause,[],[f1496,f978,f211,f1107])).

fof(f1496,plain,
    ( v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ spl4_12
    | ~ spl4_63 ),
    inference(forward_demodulation,[],[f213,f980])).

fof(f1388,plain,
    ( spl4_102
    | ~ spl4_75 ),
    inference(avatar_split_clause,[],[f1136,f1078,f1385])).

fof(f1078,plain,
    ( spl4_75
  <=> k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_75])])).

fof(f1136,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl4_75 ),
    inference(superposition,[],[f326,f1080])).

fof(f1080,plain,
    ( k1_xboole_0 = k6_partfun1(k1_xboole_0)
    | ~ spl4_75 ),
    inference(avatar_component_clause,[],[f1078])).

fof(f326,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(unit_resulting_resolution,[],[f178,f79,f196,f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | ~ v1_partfun1(X1,X0)
      | k1_relat_1(X1) = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

fof(f196,plain,(
    ! [X0] : v4_relat_1(k6_partfun1(X0),X0) ),
    inference(unit_resulting_resolution,[],[f80,f100])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f80,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f79,plain,(
    ! [X0] : v1_partfun1(k6_partfun1(X0),X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f178,plain,(
    ! [X0] : v1_relat_1(k6_partfun1(X0)) ),
    inference(unit_resulting_resolution,[],[f80,f98])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f1216,plain,
    ( spl4_91
    | ~ spl4_14
    | ~ spl4_30 ),
    inference(avatar_split_clause,[],[f461,f388,f221,f1213])).

fof(f461,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl4_14
    | ~ spl4_30 ),
    inference(superposition,[],[f223,f390])).

fof(f223,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f221])).

fof(f1171,plain,
    ( spl4_30
    | ~ spl4_86
    | ~ spl4_10
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f294,f289,f188,f1168,f388])).

fof(f188,plain,
    ( spl4_10
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f289,plain,
    ( spl4_18
  <=> v4_relat_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f294,plain,
    ( ~ v1_partfun1(sK2,u1_struct_0(sK0))
    | u1_struct_0(sK0) = k1_relat_1(sK2)
    | ~ spl4_10
    | ~ spl4_18 ),
    inference(subsumption_resolution,[],[f293,f190])).

fof(f190,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f188])).

fof(f293,plain,
    ( ~ v1_partfun1(sK2,u1_struct_0(sK0))
    | u1_struct_0(sK0) = k1_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_18 ),
    inference(resolution,[],[f291,f92])).

fof(f291,plain,
    ( v4_relat_1(sK2,u1_struct_0(sK0))
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f289])).

fof(f1086,plain,
    ( spl4_76
    | ~ spl4_7
    | ~ spl4_19 ),
    inference(avatar_split_clause,[],[f514,f299,f159,f1083])).

fof(f514,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl4_7
    | ~ spl4_19 ),
    inference(forward_demodulation,[],[f513,f307])).

fof(f513,plain,(
    v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f512,f80])).

fof(f512,plain,
    ( v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(subsumption_resolution,[],[f510,f326])).

fof(f510,plain,
    ( k1_xboole_0 != k1_relat_1(k6_partfun1(k1_xboole_0))
    | v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(superposition,[],[f118,f238])).

fof(f238,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = k1_relset_1(X0,X0,k6_partfun1(X0)) ),
    inference(unit_resulting_resolution,[],[f80,f99])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f118,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f104])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(f1081,plain,
    ( spl4_75
    | ~ spl4_7
    | ~ spl4_19 ),
    inference(avatar_split_clause,[],[f307,f299,f159,f1078])).

fof(f1002,plain,
    ( spl4_68
    | ~ spl4_8
    | ~ spl4_30 ),
    inference(avatar_split_clause,[],[f458,f388,f164,f999])).

fof(f458,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))
    | ~ spl4_8
    | ~ spl4_30 ),
    inference(superposition,[],[f166,f390])).

fof(f965,plain,
    ( spl4_62
    | ~ spl4_24 ),
    inference(avatar_split_clause,[],[f347,f340,f962])).

fof(f340,plain,
    ( spl4_24
  <=> m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f347,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl4_24 ),
    inference(unit_resulting_resolution,[],[f342,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | l1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => l1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_pre_topc)).

fof(f342,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f340])).

fof(f844,plain,
    ( spl4_57
    | ~ spl4_30
    | ~ spl4_45 ),
    inference(avatar_split_clause,[],[f718,f667,f388,f841])).

fof(f718,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl4_30
    | ~ spl4_45 ),
    inference(forward_demodulation,[],[f668,f390])).

fof(f839,plain,
    ( spl4_56
    | ~ spl4_26
    | ~ spl4_37 ),
    inference(avatar_split_clause,[],[f778,f551,f360,f836])).

fof(f778,plain,
    ( v1_xboole_0(sK2)
    | ~ spl4_26
    | ~ spl4_37 ),
    inference(unit_resulting_resolution,[],[f362,f552,f90])).

fof(f552,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | ~ spl4_37 ),
    inference(avatar_component_clause,[],[f551])).

fof(f701,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != k1_relat_1(sK2)
    | u1_struct_0(sK0) != k1_relat_1(sK2)
    | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f700,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != k1_relat_1(sK2)
    | u1_struct_0(sK0) != k1_relat_1(sK2)
    | v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f697,plain,
    ( k1_xboole_0 != u1_struct_0(sK1)
    | k1_xboole_0 != u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f678,plain,
    ( ~ spl4_45
    | ~ spl4_46
    | spl4_47
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_11
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_24 ),
    inference(avatar_split_clause,[],[f349,f340,f227,f221,f201,f149,f144,f139,f134,f129,f675,f671,f667])).

fof(f349,plain,
    ( v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_11
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_24 ),
    inference(subsumption_resolution,[],[f277,f347])).

fof(f277,plain,
    ( v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_11
    | ~ spl4_14
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f276,f131])).

fof(f276,plain,
    ( v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK0)
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_11
    | ~ spl4_14
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f275,f136])).

fof(f275,plain,
    ( v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_11
    | ~ spl4_14
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f274,f206])).

fof(f206,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f141,f146,f83])).

fof(f83,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ),
    inference(pure_predicate_removal,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_pre_topc)).

fof(f274,plain,
    ( v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl4_5
    | ~ spl4_11
    | ~ spl4_14
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f273,f151])).

fof(f273,plain,
    ( v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl4_11
    | ~ spl4_14
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f272,f229])).

fof(f272,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl4_11
    | ~ spl4_14 ),
    inference(subsumption_resolution,[],[f271,f223])).

fof(f271,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl4_11 ),
    inference(resolution,[],[f121,f203])).

fof(f651,plain,
    ( ~ spl4_41
    | ~ spl4_42
    | spl4_43
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_11
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_23 ),
    inference(avatar_split_clause,[],[f346,f335,f227,f221,f201,f149,f144,f139,f134,f129,f648,f644,f640])).

fof(f644,plain,
    ( spl4_42
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).

fof(f335,plain,
    ( spl4_23
  <=> m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f346,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_11
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_23 ),
    inference(subsumption_resolution,[],[f285,f344])).

fof(f344,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl4_23 ),
    inference(unit_resulting_resolution,[],[f337,f91])).

fof(f337,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl4_23 ),
    inference(avatar_component_clause,[],[f335])).

fof(f285,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_11
    | ~ spl4_14
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f284,f205])).

fof(f205,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f131,f136,f83])).

fof(f284,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_11
    | ~ spl4_14
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f283,f141])).

fof(f283,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_11
    | ~ spl4_14
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f282,f146])).

fof(f282,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl4_5
    | ~ spl4_11
    | ~ spl4_14
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f281,f151])).

fof(f281,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl4_11
    | ~ spl4_14
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f280,f229])).

fof(f280,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl4_11
    | ~ spl4_14 ),
    inference(subsumption_resolution,[],[f279,f223])).

fof(f279,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl4_11 ),
    inference(resolution,[],[f123,f203])).

fof(f563,plain,
    ( spl4_38
    | spl4_39
    | ~ spl4_11
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f264,f227,f201,f560,f556])).

fof(f556,plain,
    ( spl4_38
  <=> k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).

fof(f264,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK2)
    | k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl4_11
    | ~ spl4_15 ),
    inference(forward_demodulation,[],[f263,f237])).

fof(f237,plain,
    ( k1_relat_1(sK2) = k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2)
    | ~ spl4_15 ),
    inference(unit_resulting_resolution,[],[f229,f99])).

fof(f263,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2)
    | k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl4_11
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f259,f229])).

fof(f259,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2)
    | k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ spl4_11 ),
    inference(resolution,[],[f101,f203])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) = X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f440,plain,
    ( spl4_32
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f250,f227,f437])).

fof(f250,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ spl4_15 ),
    inference(unit_resulting_resolution,[],[f113,f229,f107])).

fof(f107,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(k1_relat_1(X3),X1)
      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => ( r1_tarski(k1_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).

fof(f113,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f391,plain,
    ( spl4_29
    | spl4_30
    | ~ spl4_8
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f262,f170,f164,f388,f384])).

fof(f262,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK2)
    | k1_xboole_0 = u1_struct_0(sK1)
    | ~ spl4_8
    | ~ spl4_9 ),
    inference(forward_demodulation,[],[f261,f236])).

fof(f236,plain,
    ( k1_relat_1(sK2) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl4_9 ),
    inference(unit_resulting_resolution,[],[f172,f99])).

fof(f261,plain,
    ( u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k1_xboole_0 = u1_struct_0(sK1)
    | ~ spl4_8
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f258,f172])).

fof(f258,plain,
    ( u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k1_xboole_0 = u1_struct_0(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl4_8 ),
    inference(resolution,[],[f101,f166])).

fof(f370,plain,
    ( spl4_27
    | ~ spl4_23 ),
    inference(avatar_split_clause,[],[f344,f335,f367])).

fof(f363,plain,
    ( spl4_26
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f249,f170,f360])).

fof(f249,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))))
    | ~ spl4_9 ),
    inference(unit_resulting_resolution,[],[f113,f172,f107])).

fof(f343,plain,
    ( spl4_24
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f183,f144,f340])).

fof(f183,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f146,f82])).

fof(f82,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f338,plain,
    ( spl4_23
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f182,f134,f335])).

fof(f182,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f136,f82])).

fof(f324,plain,
    ( spl4_21
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f206,f144,f139,f321])).

fof(f319,plain,
    ( spl4_20
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f205,f134,f129,f316])).

fof(f302,plain,
    ( spl4_19
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f208,f159,f299])).

fof(f208,plain,
    ( v1_xboole_0(k6_partfun1(k1_xboole_0))
    | ~ spl4_7 ),
    inference(unit_resulting_resolution,[],[f161,f80,f90])).

fof(f292,plain,
    ( spl4_18
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f195,f170,f289])).

fof(f195,plain,
    ( v4_relat_1(sK2,u1_struct_0(sK0))
    | ~ spl4_9 ),
    inference(unit_resulting_resolution,[],[f172,f100])).

fof(f247,plain,
    ( spl4_16
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f168,f159,f244])).

fof(f168,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl4_7 ),
    inference(unit_resulting_resolution,[],[f161,f81])).

fof(f81,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_funct_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_1)).

fof(f230,plain,(
    spl4_15 ),
    inference(avatar_split_clause,[],[f124,f227])).

fof(f124,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    inference(forward_demodulation,[],[f73,f74])).

fof(f74,plain,(
    sK2 = sK3 ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,
    ( ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
      | ~ v5_pre_topc(sK2,sK0,sK1) )
    & ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
      | v5_pre_topc(sK2,sK0,sK1) )
    & sK2 = sK3
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    & v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f52,f56,f55,f54,f53])).

fof(f53,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                      | ~ v5_pre_topc(X2,X0,X1) )
                    & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                      | v5_pre_topc(X2,X0,X1) )
                    & X2 = X3
                    & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                    & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                    & v1_funct_1(X3) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_pre_topc(X1)
            & v2_pre_topc(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | ~ v5_pre_topc(X2,sK0,X1) )
                  & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | v5_pre_topc(X2,sK0,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                  | ~ v5_pre_topc(X2,sK0,X1) )
                & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                  | v5_pre_topc(X2,sK0,X1) )
                & X2 = X3
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                & v1_funct_1(X3) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
            & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
            & v1_funct_1(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
                | ~ v5_pre_topc(X2,sK0,sK1) )
              & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
                | v5_pre_topc(X2,sK0,sK1) )
              & X2 = X3
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
              & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
              & v1_funct_1(X3) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
          & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
          & v1_funct_1(X2) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
              | ~ v5_pre_topc(X2,sK0,sK1) )
            & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
              | v5_pre_topc(X2,sK0,sK1) )
            & X2 = X3
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
            & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
            | ~ v5_pre_topc(sK2,sK0,sK1) )
          & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
            | v5_pre_topc(sK2,sK0,sK1) )
          & sK2 = X3
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
          & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,
    ( ? [X3] :
        ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
          | ~ v5_pre_topc(sK2,sK0,sK1) )
        & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
          | v5_pre_topc(sK2,sK0,sK1) )
        & sK2 = X3
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
        & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
        & v1_funct_1(X3) )
   => ( ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ v5_pre_topc(sK2,sK0,sK1) )
      & ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | v5_pre_topc(sK2,sK0,sK1) )
      & sK2 = sK3
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
      & v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | ~ v5_pre_topc(X2,X0,X1) )
                  & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | v5_pre_topc(X2,X0,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | ~ v5_pre_topc(X2,X0,X1) )
                  & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | v5_pre_topc(X2,X0,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                      & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                      & v1_funct_1(X3) )
                   => ( X2 = X3
                     => ( v5_pre_topc(X2,X0,X1)
                      <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                    & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                    & v1_funct_1(X3) )
                 => ( X2 = X3
                   => ( v5_pre_topc(X2,X0,X1)
                    <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_pre_topc)).

fof(f73,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    inference(cnf_transformation,[],[f57])).

fof(f225,plain,
    ( ~ spl4_12
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f76,f215,f211])).

fof(f76,plain,
    ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f57])).

fof(f218,plain,
    ( spl4_12
    | spl4_13 ),
    inference(avatar_split_clause,[],[f75,f215,f211])).

fof(f75,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f57])).

fof(f204,plain,(
    spl4_11 ),
    inference(avatar_split_clause,[],[f125,f201])).

fof(f125,plain,(
    v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    inference(forward_demodulation,[],[f72,f74])).

fof(f72,plain,(
    v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    inference(cnf_transformation,[],[f57])).

fof(f191,plain,
    ( spl4_10
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f177,f170,f188])).

fof(f177,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_9 ),
    inference(unit_resulting_resolution,[],[f172,f98])).

fof(f173,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f70,f170])).

fof(f70,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f57])).

fof(f167,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f69,f164])).

fof(f69,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f57])).

fof(f162,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f77,f159])).

fof(f77,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f157,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f74,f154])).

fof(f152,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f126,f149])).

fof(f126,plain,(
    v1_funct_1(sK2) ),
    inference(forward_demodulation,[],[f71,f74])).

fof(f71,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f57])).

fof(f147,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f67,f144])).

fof(f67,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f57])).

fof(f142,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f66,f139])).

fof(f66,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f57])).

fof(f137,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f65,f134])).

fof(f65,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f57])).

fof(f132,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f64,f129])).

fof(f64,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f57])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:02:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.47  % (6108)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.48  % (6124)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.49  % (6109)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.50  % (6110)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.50  % (6110)Refutation not found, incomplete strategy% (6110)------------------------------
% 0.20/0.50  % (6110)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (6110)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (6110)Memory used [KB]: 10746
% 0.20/0.50  % (6110)Time elapsed: 0.094 s
% 0.20/0.50  % (6110)------------------------------
% 0.20/0.50  % (6110)------------------------------
% 0.20/0.51  % (6118)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.51  % (6119)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.20/0.51  % (6125)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.51  % (6112)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.51  % (6113)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.20/0.51  % (6126)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.51  % (6116)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.52  % (6104)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.52  % (6104)Refutation not found, incomplete strategy% (6104)------------------------------
% 0.20/0.52  % (6104)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (6130)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.24/0.52  % (6115)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.24/0.52  % (6107)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 1.24/0.52  % (6120)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.24/0.52  % (6104)Termination reason: Refutation not found, incomplete strategy
% 1.24/0.52  
% 1.24/0.52  % (6104)Memory used [KB]: 10618
% 1.24/0.52  % (6104)Time elapsed: 0.105 s
% 1.24/0.52  % (6104)------------------------------
% 1.24/0.52  % (6104)------------------------------
% 1.24/0.52  % (6129)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.24/0.52  % (6117)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.24/0.53  % (6123)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.24/0.53  % (6114)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.24/0.53  % (6128)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.24/0.53  % (6106)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.39/0.54  % (6105)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 1.39/0.54  % (6117)Refutation not found, incomplete strategy% (6117)------------------------------
% 1.39/0.54  % (6117)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.54  % (6117)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.54  
% 1.39/0.54  % (6117)Memory used [KB]: 6268
% 1.39/0.54  % (6117)Time elapsed: 0.132 s
% 1.39/0.54  % (6117)------------------------------
% 1.39/0.54  % (6117)------------------------------
% 1.39/0.54  % (6111)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.39/0.55  % (6121)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.39/0.55  % (6122)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.39/0.57  % (6105)Refutation not found, incomplete strategy% (6105)------------------------------
% 1.39/0.57  % (6105)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.57  % (6105)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.57  
% 1.39/0.57  % (6105)Memory used [KB]: 11129
% 1.39/0.57  % (6105)Time elapsed: 0.164 s
% 1.39/0.57  % (6105)------------------------------
% 1.39/0.57  % (6105)------------------------------
% 2.07/0.67  % (6113)Refutation not found, incomplete strategy% (6113)------------------------------
% 2.07/0.67  % (6113)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.07/0.67  % (6113)Termination reason: Refutation not found, incomplete strategy
% 2.07/0.67  
% 2.07/0.67  % (6113)Memory used [KB]: 6268
% 2.07/0.67  % (6113)Time elapsed: 0.248 s
% 2.07/0.67  % (6113)------------------------------
% 2.07/0.67  % (6113)------------------------------
% 2.54/0.74  % (6128)Refutation found. Thanks to Tanya!
% 2.54/0.74  % SZS status Theorem for theBenchmark
% 2.54/0.75  % SZS output start Proof for theBenchmark
% 2.54/0.75  fof(f3669,plain,(
% 2.54/0.75    $false),
% 2.54/0.75    inference(avatar_sat_refutation,[],[f132,f137,f142,f147,f152,f157,f162,f167,f173,f191,f204,f218,f225,f230,f247,f292,f302,f319,f324,f338,f343,f363,f370,f391,f440,f563,f651,f678,f697,f700,f701,f839,f844,f965,f1002,f1081,f1086,f1171,f1216,f1388,f1634,f1957,f2010,f2011,f2039,f2059,f2161,f2167,f2509,f2511,f2625,f2837,f2915,f2984,f3140,f3177,f3181,f3288,f3338,f3342,f3343,f3344,f3459,f3471,f3664])).
% 2.54/0.75  fof(f3664,plain,(
% 2.54/0.75    ~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_16 | ~spl4_29 | ~spl4_78 | ~spl4_127 | spl4_129 | ~spl4_131),
% 2.54/0.75    inference(avatar_contradiction_clause,[],[f3663])).
% 2.54/0.75  fof(f3663,plain,(
% 2.54/0.75    $false | (~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_16 | ~spl4_29 | ~spl4_78 | ~spl4_127 | spl4_129 | ~spl4_131)),
% 2.54/0.75    inference(subsumption_resolution,[],[f3634,f78])).
% 2.54/0.75  fof(f78,plain,(
% 2.54/0.75    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.54/0.75    inference(cnf_transformation,[],[f4])).
% 2.54/0.75  fof(f4,axiom,(
% 2.54/0.75    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.54/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 2.54/0.75  fof(f3634,plain,(
% 2.54/0.75    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0))) | (~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_16 | ~spl4_29 | ~spl4_78 | ~spl4_127 | spl4_129 | ~spl4_131)),
% 2.54/0.75    inference(unit_resulting_resolution,[],[f131,f136,f246,f1108,f3287,f78,f3458,f3470,f2971])).
% 2.54/0.75  fof(f2971,plain,(
% 2.54/0.75    ( ! [X2,X3] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))),k1_xboole_0))) | ~v5_pre_topc(X2,X3,sK1) | ~v1_funct_2(X2,u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))),k1_xboole_0) | v5_pre_topc(X2,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)),sK1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),k1_xboole_0))) | ~v1_funct_2(X2,u1_struct_0(X3),k1_xboole_0) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3)) ) | (~spl4_3 | ~spl4_4 | ~spl4_29)),
% 2.54/0.75    inference(subsumption_resolution,[],[f2970,f141])).
% 2.54/0.75  fof(f141,plain,(
% 2.54/0.75    v2_pre_topc(sK1) | ~spl4_3),
% 2.54/0.75    inference(avatar_component_clause,[],[f139])).
% 2.54/0.75  fof(f139,plain,(
% 2.54/0.75    spl4_3 <=> v2_pre_topc(sK1)),
% 2.54/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 2.54/0.75  fof(f2970,plain,(
% 2.54/0.75    ( ! [X2,X3] : (~v1_funct_2(X2,u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))),k1_xboole_0) | ~v5_pre_topc(X2,X3,sK1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))),k1_xboole_0))) | v5_pre_topc(X2,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)),sK1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),k1_xboole_0))) | ~v1_funct_2(X2,u1_struct_0(X3),k1_xboole_0) | ~v2_pre_topc(sK1) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3)) ) | (~spl4_4 | ~spl4_29)),
% 2.54/0.75    inference(subsumption_resolution,[],[f2951,f146])).
% 2.54/0.75  fof(f146,plain,(
% 2.54/0.75    l1_pre_topc(sK1) | ~spl4_4),
% 2.54/0.75    inference(avatar_component_clause,[],[f144])).
% 2.54/0.75  fof(f144,plain,(
% 2.54/0.75    spl4_4 <=> l1_pre_topc(sK1)),
% 2.54/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 2.54/0.75  fof(f2951,plain,(
% 2.54/0.75    ( ! [X2,X3] : (~v1_funct_2(X2,u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))),k1_xboole_0) | ~v5_pre_topc(X2,X3,sK1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))),k1_xboole_0))) | v5_pre_topc(X2,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)),sK1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),k1_xboole_0))) | ~v1_funct_2(X2,u1_struct_0(X3),k1_xboole_0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3)) ) | ~spl4_29),
% 2.54/0.75    inference(superposition,[],[f120,f386])).
% 2.54/0.75  fof(f386,plain,(
% 2.54/0.75    k1_xboole_0 = u1_struct_0(sK1) | ~spl4_29),
% 2.54/0.75    inference(avatar_component_clause,[],[f384])).
% 2.54/0.75  fof(f384,plain,(
% 2.54/0.75    spl4_29 <=> k1_xboole_0 = u1_struct_0(sK1)),
% 2.54/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).
% 2.54/0.75  fof(f120,plain,(
% 2.54/0.75    ( ! [X0,X3,X1] : (~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v5_pre_topc(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.54/0.75    inference(duplicate_literal_removal,[],[f111])).
% 2.54/0.75  fof(f111,plain,(
% 2.54/0.75    ( ! [X0,X3,X1] : (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.54/0.75    inference(equality_resolution,[],[f86])).
% 2.54/0.75  fof(f86,plain,(
% 2.54/0.75    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.54/0.75    inference(cnf_transformation,[],[f59])).
% 2.54/0.75  fof(f59,plain,(
% 2.54/0.75    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.54/0.75    inference(nnf_transformation,[],[f36])).
% 2.54/0.75  fof(f36,plain,(
% 2.54/0.75    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.54/0.75    inference(flattening,[],[f35])).
% 2.54/0.75  fof(f35,plain,(
% 2.54/0.75    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) | X2 != X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.54/0.75    inference(ennf_transformation,[],[f19])).
% 2.54/0.75  fof(f19,axiom,(
% 2.54/0.75    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)))))))),
% 2.54/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_pre_topc)).
% 2.54/0.75  fof(f3470,plain,(
% 2.54/0.75    v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) | ~spl4_131),
% 2.54/0.75    inference(avatar_component_clause,[],[f3468])).
% 2.54/0.75  fof(f3468,plain,(
% 2.54/0.75    spl4_131 <=> v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)),
% 2.54/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_131])])).
% 2.54/0.75  fof(f3458,plain,(
% 2.54/0.75    ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | spl4_129),
% 2.54/0.75    inference(avatar_component_clause,[],[f3456])).
% 2.54/0.75  fof(f3456,plain,(
% 2.54/0.75    spl4_129 <=> v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)),
% 2.54/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_129])])).
% 2.54/0.75  fof(f3287,plain,(
% 2.54/0.75    v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | ~spl4_127),
% 2.54/0.75    inference(avatar_component_clause,[],[f3285])).
% 2.54/0.75  fof(f3285,plain,(
% 2.54/0.75    spl4_127 <=> v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)),
% 2.54/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_127])])).
% 2.54/0.75  fof(f1108,plain,(
% 2.54/0.75    v5_pre_topc(k1_xboole_0,sK0,sK1) | ~spl4_78),
% 2.54/0.75    inference(avatar_component_clause,[],[f1107])).
% 2.54/0.75  fof(f1107,plain,(
% 2.54/0.75    spl4_78 <=> v5_pre_topc(k1_xboole_0,sK0,sK1)),
% 2.54/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_78])])).
% 2.54/0.75  fof(f246,plain,(
% 2.54/0.75    v1_funct_1(k1_xboole_0) | ~spl4_16),
% 2.54/0.75    inference(avatar_component_clause,[],[f244])).
% 2.54/0.75  fof(f244,plain,(
% 2.54/0.75    spl4_16 <=> v1_funct_1(k1_xboole_0)),
% 2.54/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 2.54/0.75  fof(f136,plain,(
% 2.54/0.75    l1_pre_topc(sK0) | ~spl4_2),
% 2.54/0.75    inference(avatar_component_clause,[],[f134])).
% 2.54/0.75  fof(f134,plain,(
% 2.54/0.75    spl4_2 <=> l1_pre_topc(sK0)),
% 2.54/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 2.54/0.75  fof(f131,plain,(
% 2.54/0.75    v2_pre_topc(sK0) | ~spl4_1),
% 2.54/0.75    inference(avatar_component_clause,[],[f129])).
% 2.54/0.75  fof(f129,plain,(
% 2.54/0.75    spl4_1 <=> v2_pre_topc(sK0)),
% 2.54/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 2.54/0.75  fof(f3471,plain,(
% 2.54/0.75    spl4_131 | ~spl4_29 | ~spl4_41 | ~spl4_63),
% 2.54/0.75    inference(avatar_split_clause,[],[f3383,f978,f640,f384,f3468])).
% 2.54/0.75  fof(f640,plain,(
% 2.54/0.75    spl4_41 <=> v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))),
% 2.54/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).
% 2.54/0.75  fof(f978,plain,(
% 2.54/0.75    spl4_63 <=> k1_xboole_0 = sK2),
% 2.54/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_63])])).
% 2.54/0.75  fof(f3383,plain,(
% 2.54/0.75    v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) | (~spl4_29 | ~spl4_41 | ~spl4_63)),
% 2.54/0.75    inference(forward_demodulation,[],[f3382,f980])).
% 2.54/0.75  fof(f980,plain,(
% 2.54/0.75    k1_xboole_0 = sK2 | ~spl4_63),
% 2.54/0.75    inference(avatar_component_clause,[],[f978])).
% 2.54/0.75  fof(f3382,plain,(
% 2.54/0.75    v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) | (~spl4_29 | ~spl4_41)),
% 2.54/0.75    inference(forward_demodulation,[],[f641,f386])).
% 2.54/0.75  fof(f641,plain,(
% 2.54/0.75    v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~spl4_41),
% 2.54/0.75    inference(avatar_component_clause,[],[f640])).
% 2.54/0.75  fof(f3459,plain,(
% 2.54/0.75    ~spl4_129 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_6 | ~spl4_11 | spl4_13 | ~spl4_15 | ~spl4_20 | ~spl4_27 | ~spl4_29 | ~spl4_41 | ~spl4_63),
% 2.54/0.75    inference(avatar_split_clause,[],[f3428,f978,f640,f384,f367,f316,f227,f215,f201,f154,f149,f144,f139,f3456])).
% 2.54/0.75  fof(f149,plain,(
% 2.54/0.75    spl4_5 <=> v1_funct_1(sK2)),
% 2.54/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 2.54/0.75  fof(f154,plain,(
% 2.54/0.75    spl4_6 <=> sK2 = sK3),
% 2.54/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 2.54/0.75  fof(f201,plain,(
% 2.54/0.75    spl4_11 <=> v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 2.54/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 2.54/0.75  fof(f215,plain,(
% 2.54/0.75    spl4_13 <=> v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 2.54/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 2.54/0.75  fof(f227,plain,(
% 2.54/0.75    spl4_15 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))),
% 2.54/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 2.54/0.75  fof(f316,plain,(
% 2.54/0.75    spl4_20 <=> v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 2.54/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 2.54/0.75  fof(f367,plain,(
% 2.54/0.75    spl4_27 <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 2.54/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).
% 2.54/0.75  fof(f3428,plain,(
% 2.54/0.75    ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | (~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_6 | ~spl4_11 | spl4_13 | ~spl4_15 | ~spl4_20 | ~spl4_27 | ~spl4_29 | ~spl4_41 | ~spl4_63)),
% 2.54/0.75    inference(subsumption_resolution,[],[f3427,f3383])).
% 2.54/0.75  fof(f3427,plain,(
% 2.54/0.75    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | (~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_6 | ~spl4_11 | spl4_13 | ~spl4_15 | ~spl4_20 | ~spl4_27 | ~spl4_29 | ~spl4_63)),
% 2.54/0.75    inference(forward_demodulation,[],[f3426,f980])).
% 2.54/0.75  fof(f3426,plain,(
% 2.54/0.75    ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | (~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_6 | ~spl4_11 | spl4_13 | ~spl4_15 | ~spl4_20 | ~spl4_27 | ~spl4_29 | ~spl4_63)),
% 2.54/0.75    inference(forward_demodulation,[],[f3425,f386])).
% 2.54/0.75  fof(f3425,plain,(
% 2.54/0.75    ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | (~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_6 | ~spl4_11 | spl4_13 | ~spl4_15 | ~spl4_20 | ~spl4_27 | ~spl4_29 | ~spl4_63)),
% 2.54/0.75    inference(subsumption_resolution,[],[f3424,f78])).
% 2.54/0.75  fof(f3424,plain,(
% 2.54/0.75    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0))) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | (~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_6 | ~spl4_11 | spl4_13 | ~spl4_15 | ~spl4_20 | ~spl4_27 | ~spl4_29 | ~spl4_63)),
% 2.54/0.75    inference(forward_demodulation,[],[f3423,f980])).
% 2.54/0.75  fof(f3423,plain,(
% 2.54/0.75    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0))) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | (~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_6 | ~spl4_11 | spl4_13 | ~spl4_15 | ~spl4_20 | ~spl4_27 | ~spl4_29 | ~spl4_63)),
% 2.54/0.75    inference(forward_demodulation,[],[f3422,f386])).
% 2.54/0.75  fof(f3422,plain,(
% 2.54/0.75    ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | (~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_6 | ~spl4_11 | spl4_13 | ~spl4_15 | ~spl4_20 | ~spl4_27 | ~spl4_29 | ~spl4_63)),
% 2.54/0.75    inference(subsumption_resolution,[],[f3421,f3413])).
% 2.54/0.75  fof(f3413,plain,(
% 2.54/0.75    ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl4_6 | spl4_13 | ~spl4_29 | ~spl4_63)),
% 2.54/0.75    inference(forward_demodulation,[],[f3412,f980])).
% 2.54/0.75  fof(f3412,plain,(
% 2.54/0.75    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl4_6 | spl4_13 | ~spl4_29)),
% 2.54/0.75    inference(forward_demodulation,[],[f3411,f156])).
% 2.54/0.75  fof(f156,plain,(
% 2.54/0.75    sK2 = sK3 | ~spl4_6),
% 2.54/0.75    inference(avatar_component_clause,[],[f154])).
% 2.54/0.75  fof(f3411,plain,(
% 2.54/0.75    ~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (spl4_13 | ~spl4_29)),
% 2.54/0.75    inference(forward_demodulation,[],[f216,f386])).
% 2.54/0.75  fof(f216,plain,(
% 2.54/0.75    ~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | spl4_13),
% 2.54/0.75    inference(avatar_component_clause,[],[f215])).
% 2.54/0.75  fof(f3421,plain,(
% 2.54/0.75    v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | (~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_11 | ~spl4_15 | ~spl4_20 | ~spl4_27 | ~spl4_29 | ~spl4_63)),
% 2.54/0.75    inference(forward_demodulation,[],[f3420,f980])).
% 2.54/0.75  fof(f3420,plain,(
% 2.54/0.75    v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | (~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_11 | ~spl4_15 | ~spl4_20 | ~spl4_27 | ~spl4_29 | ~spl4_63)),
% 2.54/0.75    inference(forward_demodulation,[],[f3419,f386])).
% 2.54/0.75  fof(f3419,plain,(
% 2.54/0.75    ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | (~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_11 | ~spl4_15 | ~spl4_20 | ~spl4_27 | ~spl4_63)),
% 2.54/0.75    inference(forward_demodulation,[],[f1456,f980])).
% 2.54/0.75  fof(f1456,plain,(
% 2.54/0.75    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | (~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_11 | ~spl4_15 | ~spl4_20 | ~spl4_27)),
% 2.54/0.75    inference(subsumption_resolution,[],[f1455,f318])).
% 2.54/0.75  fof(f318,plain,(
% 2.54/0.75    v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~spl4_20),
% 2.54/0.75    inference(avatar_component_clause,[],[f316])).
% 2.54/0.75  fof(f1455,plain,(
% 2.54/0.75    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_11 | ~spl4_15 | ~spl4_27)),
% 2.54/0.75    inference(subsumption_resolution,[],[f1454,f369])).
% 2.54/0.75  fof(f369,plain,(
% 2.54/0.75    l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~spl4_27),
% 2.54/0.75    inference(avatar_component_clause,[],[f367])).
% 2.54/0.75  fof(f1454,plain,(
% 2.54/0.75    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_11 | ~spl4_15)),
% 2.54/0.75    inference(subsumption_resolution,[],[f1453,f141])).
% 2.54/0.75  fof(f1453,plain,(
% 2.54/0.75    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v2_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl4_4 | ~spl4_5 | ~spl4_11 | ~spl4_15)),
% 2.54/0.75    inference(subsumption_resolution,[],[f1452,f146])).
% 2.54/0.75  fof(f1452,plain,(
% 2.54/0.75    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl4_5 | ~spl4_11 | ~spl4_15)),
% 2.54/0.75    inference(subsumption_resolution,[],[f1451,f151])).
% 2.54/0.75  fof(f151,plain,(
% 2.54/0.75    v1_funct_1(sK2) | ~spl4_5),
% 2.54/0.75    inference(avatar_component_clause,[],[f149])).
% 2.54/0.75  fof(f1451,plain,(
% 2.54/0.75    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl4_11 | ~spl4_15)),
% 2.54/0.75    inference(subsumption_resolution,[],[f278,f229])).
% 2.54/0.75  fof(f229,plain,(
% 2.54/0.75    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~spl4_15),
% 2.54/0.75    inference(avatar_component_clause,[],[f227])).
% 2.54/0.75  fof(f278,plain,(
% 2.54/0.75    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~spl4_11),
% 2.54/0.75    inference(resolution,[],[f122,f203])).
% 2.54/0.75  fof(f203,plain,(
% 2.54/0.75    v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~spl4_11),
% 2.54/0.75    inference(avatar_component_clause,[],[f201])).
% 3.14/0.76  fof(f122,plain,(
% 3.14/0.76    ( ! [X0,X3,X1] : (~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v5_pre_topc(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.14/0.76    inference(duplicate_literal_removal,[],[f109])).
% 3.14/0.76  fof(f109,plain,(
% 3.14/0.76    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.14/0.76    inference(equality_resolution,[],[f84])).
% 3.14/0.76  fof(f84,plain,(
% 3.14/0.76    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.14/0.76    inference(cnf_transformation,[],[f58])).
% 3.14/0.76  fof(f58,plain,(
% 3.14/0.76    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.14/0.76    inference(nnf_transformation,[],[f34])).
% 3.14/0.76  fof(f34,plain,(
% 3.14/0.76    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.14/0.76    inference(flattening,[],[f33])).
% 3.14/0.76  fof(f33,plain,(
% 3.14/0.76    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | X2 != X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.14/0.76    inference(ennf_transformation,[],[f20])).
% 3.14/0.76  fof(f20,axiom,(
% 3.14/0.76    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 3.14/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_pre_topc)).
% 3.14/0.76  fof(f3344,plain,(
% 3.14/0.76    k1_xboole_0 != u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | k1_xboole_0 != u1_struct_0(sK1) | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 3.14/0.76    introduced(theory_tautology_sat_conflict,[])).
% 3.14/0.76  fof(f3343,plain,(
% 3.14/0.76    k1_xboole_0 != u1_struct_0(sK1) | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != k1_relat_1(sK2) | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))))),
% 3.14/0.76    introduced(theory_tautology_sat_conflict,[])).
% 3.14/0.76  fof(f3342,plain,(
% 3.14/0.76    k1_xboole_0 != sK2 | k1_xboole_0 != k1_relat_1(k1_xboole_0) | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != k1_relat_1(sK2) | k1_xboole_0 != u1_struct_0(sK1) | v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 3.14/0.76    introduced(theory_tautology_sat_conflict,[])).
% 3.14/0.76  fof(f3338,plain,(
% 3.14/0.76    ~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_8 | ~spl4_9 | spl4_12 | ~spl4_29 | ~spl4_39 | ~spl4_43 | ~spl4_63 | ~spl4_76 | ~spl4_102),
% 3.14/0.76    inference(avatar_contradiction_clause,[],[f3337])).
% 3.14/0.76  fof(f3337,plain,(
% 3.14/0.76    $false | (~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_8 | ~spl4_9 | spl4_12 | ~spl4_29 | ~spl4_39 | ~spl4_43 | ~spl4_63 | ~spl4_76 | ~spl4_102)),
% 3.14/0.76    inference(subsumption_resolution,[],[f3336,f78])).
% 3.14/0.76  fof(f3336,plain,(
% 3.14/0.76    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_8 | ~spl4_9 | spl4_12 | ~spl4_29 | ~spl4_39 | ~spl4_43 | ~spl4_63 | ~spl4_76 | ~spl4_102)),
% 3.14/0.76    inference(forward_demodulation,[],[f3335,f980])).
% 3.14/0.76  fof(f3335,plain,(
% 3.14/0.76    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_8 | ~spl4_9 | spl4_12 | ~spl4_29 | ~spl4_39 | ~spl4_43 | ~spl4_63 | ~spl4_76 | ~spl4_102)),
% 3.14/0.76    inference(forward_demodulation,[],[f3334,f386])).
% 3.14/0.76  fof(f3334,plain,(
% 3.14/0.76    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))) | (~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_8 | ~spl4_9 | spl4_12 | ~spl4_29 | ~spl4_39 | ~spl4_43 | ~spl4_63 | ~spl4_76 | ~spl4_102)),
% 3.14/0.76    inference(subsumption_resolution,[],[f3333,f1085])).
% 3.14/0.76  fof(f1085,plain,(
% 3.14/0.76    v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~spl4_76),
% 3.14/0.76    inference(avatar_component_clause,[],[f1083])).
% 3.14/0.76  fof(f1083,plain,(
% 3.14/0.76    spl4_76 <=> v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 3.14/0.76    introduced(avatar_definition,[new_symbols(naming,[spl4_76])])).
% 3.14/0.76  fof(f3333,plain,(
% 3.14/0.76    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))) | (~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_8 | ~spl4_9 | spl4_12 | ~spl4_29 | ~spl4_39 | ~spl4_43 | ~spl4_63 | ~spl4_102)),
% 3.14/0.76    inference(forward_demodulation,[],[f3332,f980])).
% 3.14/0.76  fof(f3332,plain,(
% 3.14/0.76    ~v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))) | (~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_8 | ~spl4_9 | spl4_12 | ~spl4_29 | ~spl4_39 | ~spl4_43 | ~spl4_63 | ~spl4_102)),
% 3.14/0.76    inference(forward_demodulation,[],[f3331,f386])).
% 3.14/0.76  fof(f3331,plain,(
% 3.14/0.76    ~v1_funct_2(sK2,k1_xboole_0,u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))) | (~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_8 | ~spl4_9 | spl4_12 | ~spl4_39 | ~spl4_43 | ~spl4_63 | ~spl4_102)),
% 3.14/0.76    inference(subsumption_resolution,[],[f3330,f141])).
% 3.14/0.76  fof(f3330,plain,(
% 3.14/0.76    ~v1_funct_2(sK2,k1_xboole_0,u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))) | ~v2_pre_topc(sK1) | (~spl4_1 | ~spl4_2 | ~spl4_4 | ~spl4_5 | ~spl4_8 | ~spl4_9 | spl4_12 | ~spl4_39 | ~spl4_43 | ~spl4_63 | ~spl4_102)),
% 3.14/0.76    inference(subsumption_resolution,[],[f3329,f146])).
% 3.14/0.76  fof(f3329,plain,(
% 3.14/0.76    ~v1_funct_2(sK2,k1_xboole_0,u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | (~spl4_1 | ~spl4_2 | ~spl4_5 | ~spl4_8 | ~spl4_9 | spl4_12 | ~spl4_39 | ~spl4_43 | ~spl4_63 | ~spl4_102)),
% 3.14/0.76    inference(subsumption_resolution,[],[f3328,f166])).
% 3.14/0.76  fof(f166,plain,(
% 3.14/0.76    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~spl4_8),
% 3.14/0.76    inference(avatar_component_clause,[],[f164])).
% 3.14/0.76  fof(f164,plain,(
% 3.14/0.76    spl4_8 <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 3.14/0.76    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 3.14/0.76  fof(f3328,plain,(
% 3.14/0.76    ~v1_funct_2(sK2,k1_xboole_0,u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | (~spl4_1 | ~spl4_2 | ~spl4_5 | ~spl4_9 | spl4_12 | ~spl4_39 | ~spl4_43 | ~spl4_63 | ~spl4_102)),
% 3.14/0.76    inference(subsumption_resolution,[],[f3327,f172])).
% 3.14/0.76  fof(f172,plain,(
% 3.14/0.76    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~spl4_9),
% 3.14/0.76    inference(avatar_component_clause,[],[f170])).
% 3.14/0.76  fof(f170,plain,(
% 3.14/0.76    spl4_9 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 3.14/0.76    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 3.14/0.76  fof(f3327,plain,(
% 3.14/0.76    ~v1_funct_2(sK2,k1_xboole_0,u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | (~spl4_1 | ~spl4_2 | ~spl4_5 | spl4_12 | ~spl4_39 | ~spl4_43 | ~spl4_63 | ~spl4_102)),
% 3.14/0.76    inference(subsumption_resolution,[],[f3326,f151])).
% 3.14/0.76  fof(f3326,plain,(
% 3.14/0.76    ~v1_funct_2(sK2,k1_xboole_0,u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | (~spl4_1 | ~spl4_2 | spl4_12 | ~spl4_39 | ~spl4_43 | ~spl4_63 | ~spl4_102)),
% 3.14/0.76    inference(subsumption_resolution,[],[f3325,f212])).
% 3.14/0.76  fof(f212,plain,(
% 3.14/0.76    ~v5_pre_topc(sK2,sK0,sK1) | spl4_12),
% 3.14/0.76    inference(avatar_component_clause,[],[f211])).
% 3.14/0.76  fof(f211,plain,(
% 3.14/0.76    spl4_12 <=> v5_pre_topc(sK2,sK0,sK1)),
% 3.14/0.76    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 3.14/0.76  fof(f3325,plain,(
% 3.14/0.76    ~v1_funct_2(sK2,k1_xboole_0,u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))) | v5_pre_topc(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | (~spl4_1 | ~spl4_2 | ~spl4_39 | ~spl4_43 | ~spl4_63 | ~spl4_102)),
% 3.14/0.76    inference(resolution,[],[f3023,f650])).
% 3.14/0.76  fof(f650,plain,(
% 3.14/0.76    v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~spl4_43),
% 3.14/0.76    inference(avatar_component_clause,[],[f648])).
% 3.14/0.76  fof(f648,plain,(
% 3.14/0.76    spl4_43 <=> v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)),
% 3.14/0.76    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).
% 3.14/0.76  fof(f3023,plain,(
% 3.14/0.76    ( ! [X4,X5] : (~v5_pre_topc(X4,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X5) | ~v1_funct_2(X4,k1_xboole_0,u1_struct_0(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X5)))) | v5_pre_topc(X4,sK0,X5) | ~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X5)))) | ~v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X5)) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5)) ) | (~spl4_1 | ~spl4_2 | ~spl4_39 | ~spl4_63 | ~spl4_102)),
% 3.14/0.76    inference(forward_demodulation,[],[f3022,f1387])).
% 3.14/0.76  fof(f1387,plain,(
% 3.14/0.76    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl4_102),
% 3.14/0.76    inference(avatar_component_clause,[],[f1385])).
% 3.14/0.76  fof(f1385,plain,(
% 3.14/0.76    spl4_102 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 3.14/0.76    introduced(avatar_definition,[new_symbols(naming,[spl4_102])])).
% 3.14/0.76  fof(f3022,plain,(
% 3.14/0.76    ( ! [X4,X5] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),u1_struct_0(X5)))) | ~v1_funct_2(X4,k1_xboole_0,u1_struct_0(X5)) | ~v5_pre_topc(X4,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X5) | v5_pre_topc(X4,sK0,X5) | ~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X5)))) | ~v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X5)) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5)) ) | (~spl4_1 | ~spl4_2 | ~spl4_39 | ~spl4_63 | ~spl4_102)),
% 3.14/0.76    inference(forward_demodulation,[],[f3021,f980])).
% 3.14/0.76  fof(f3021,plain,(
% 3.14/0.76    ( ! [X4,X5] : (~v1_funct_2(X4,k1_xboole_0,u1_struct_0(X5)) | ~v5_pre_topc(X4,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X5)))) | v5_pre_topc(X4,sK0,X5) | ~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X5)))) | ~v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X5)) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5)) ) | (~spl4_1 | ~spl4_2 | ~spl4_39 | ~spl4_63 | ~spl4_102)),
% 3.14/0.76    inference(forward_demodulation,[],[f3020,f1387])).
% 3.14/0.76  fof(f3020,plain,(
% 3.14/0.76    ( ! [X4,X5] : (~v1_funct_2(X4,k1_relat_1(k1_xboole_0),u1_struct_0(X5)) | ~v5_pre_topc(X4,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X5)))) | v5_pre_topc(X4,sK0,X5) | ~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X5)))) | ~v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X5)) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5)) ) | (~spl4_1 | ~spl4_2 | ~spl4_39 | ~spl4_63)),
% 3.14/0.76    inference(forward_demodulation,[],[f3019,f980])).
% 3.14/0.76  fof(f3019,plain,(
% 3.14/0.76    ( ! [X4,X5] : (~v1_funct_2(X4,k1_relat_1(sK2),u1_struct_0(X5)) | ~v5_pre_topc(X4,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X5)))) | v5_pre_topc(X4,sK0,X5) | ~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X5)))) | ~v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X5)) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5)) ) | (~spl4_1 | ~spl4_2 | ~spl4_39)),
% 3.14/0.76    inference(subsumption_resolution,[],[f3018,f131])).
% 3.14/0.76  fof(f3018,plain,(
% 3.14/0.76    ( ! [X4,X5] : (~v1_funct_2(X4,k1_relat_1(sK2),u1_struct_0(X5)) | ~v5_pre_topc(X4,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X5)))) | v5_pre_topc(X4,sK0,X5) | ~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X5)))) | ~v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X5)) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5) | ~v2_pre_topc(sK0)) ) | (~spl4_2 | ~spl4_39)),
% 3.14/0.76    inference(subsumption_resolution,[],[f2993,f136])).
% 3.14/0.76  fof(f2993,plain,(
% 3.14/0.76    ( ! [X4,X5] : (~v1_funct_2(X4,k1_relat_1(sK2),u1_struct_0(X5)) | ~v5_pre_topc(X4,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X5)))) | v5_pre_topc(X4,sK0,X5) | ~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X5)))) | ~v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X5)) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)) ) | ~spl4_39),
% 3.14/0.76    inference(superposition,[],[f121,f562])).
% 3.14/0.76  fof(f562,plain,(
% 3.14/0.76    u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK2) | ~spl4_39),
% 3.14/0.76    inference(avatar_component_clause,[],[f560])).
% 3.14/0.76  fof(f560,plain,(
% 3.14/0.76    spl4_39 <=> u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK2)),
% 3.14/0.76    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).
% 3.14/0.76  fof(f121,plain,(
% 3.14/0.76    ( ! [X0,X3,X1] : (~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | v5_pre_topc(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.14/0.76    inference(duplicate_literal_removal,[],[f110])).
% 3.14/0.76  fof(f110,plain,(
% 3.14/0.76    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.14/0.76    inference(equality_resolution,[],[f87])).
% 3.14/0.76  fof(f87,plain,(
% 3.14/0.76    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.14/0.76    inference(cnf_transformation,[],[f59])).
% 3.14/0.76  fof(f3288,plain,(
% 3.14/0.76    spl4_127 | ~spl4_8 | ~spl4_29 | ~spl4_63),
% 3.14/0.76    inference(avatar_split_clause,[],[f2959,f978,f384,f164,f3285])).
% 3.14/0.76  fof(f2959,plain,(
% 3.14/0.76    v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | (~spl4_8 | ~spl4_29 | ~spl4_63)),
% 3.14/0.76    inference(forward_demodulation,[],[f2923,f980])).
% 3.14/0.76  fof(f2923,plain,(
% 3.14/0.76    v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0) | (~spl4_8 | ~spl4_29)),
% 3.14/0.76    inference(superposition,[],[f166,f386])).
% 3.14/0.76  fof(f3181,plain,(
% 3.14/0.76    ~spl4_29 | spl4_46 | ~spl4_63),
% 3.14/0.76    inference(avatar_contradiction_clause,[],[f3180])).
% 3.14/0.76  fof(f3180,plain,(
% 3.14/0.76    $false | (~spl4_29 | spl4_46 | ~spl4_63)),
% 3.14/0.76    inference(subsumption_resolution,[],[f3179,f78])).
% 3.14/0.76  fof(f3179,plain,(
% 3.14/0.76    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | (~spl4_29 | spl4_46 | ~spl4_63)),
% 3.14/0.76    inference(forward_demodulation,[],[f3178,f980])).
% 3.14/0.76  fof(f3178,plain,(
% 3.14/0.76    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | (~spl4_29 | spl4_46)),
% 3.14/0.76    inference(forward_demodulation,[],[f673,f386])).
% 3.14/0.76  fof(f673,plain,(
% 3.14/0.76    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | spl4_46),
% 3.14/0.76    inference(avatar_component_clause,[],[f671])).
% 3.14/0.76  fof(f671,plain,(
% 3.14/0.76    spl4_46 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))),
% 3.14/0.76    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).
% 3.14/0.76  fof(f3177,plain,(
% 3.14/0.76    ~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_8 | ~spl4_9 | spl4_12 | ~spl4_29 | ~spl4_45 | ~spl4_47 | ~spl4_63),
% 3.14/0.76    inference(avatar_contradiction_clause,[],[f3176])).
% 3.14/0.76  fof(f3176,plain,(
% 3.14/0.76    $false | (~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_8 | ~spl4_9 | spl4_12 | ~spl4_29 | ~spl4_45 | ~spl4_47 | ~spl4_63)),
% 3.14/0.76    inference(subsumption_resolution,[],[f3175,f78])).
% 3.14/0.76  fof(f3175,plain,(
% 3.14/0.76    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | (~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_8 | ~spl4_9 | spl4_12 | ~spl4_29 | ~spl4_45 | ~spl4_47 | ~spl4_63)),
% 3.14/0.76    inference(forward_demodulation,[],[f3174,f980])).
% 3.14/0.76  fof(f3174,plain,(
% 3.14/0.76    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | (~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_8 | ~spl4_9 | spl4_12 | ~spl4_29 | ~spl4_45 | ~spl4_47)),
% 3.14/0.76    inference(forward_demodulation,[],[f3118,f386])).
% 3.14/0.76  fof(f3118,plain,(
% 3.14/0.76    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | (~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_8 | ~spl4_9 | spl4_12 | ~spl4_45 | ~spl4_47)),
% 3.14/0.76    inference(unit_resulting_resolution,[],[f131,f136,f141,f146,f151,f212,f166,f172,f677,f668,f123])).
% 3.14/0.76  fof(f123,plain,(
% 3.14/0.76    ( ! [X0,X3,X1] : (~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | v5_pre_topc(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.14/0.76    inference(duplicate_literal_removal,[],[f108])).
% 3.14/0.76  fof(f108,plain,(
% 3.14/0.76    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.14/0.76    inference(equality_resolution,[],[f85])).
% 3.14/0.76  fof(f85,plain,(
% 3.14/0.76    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.14/0.76    inference(cnf_transformation,[],[f58])).
% 3.14/0.76  fof(f668,plain,(
% 3.14/0.76    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~spl4_45),
% 3.14/0.76    inference(avatar_component_clause,[],[f667])).
% 3.14/0.76  fof(f667,plain,(
% 3.14/0.76    spl4_45 <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 3.14/0.76    introduced(avatar_definition,[new_symbols(naming,[spl4_45])])).
% 3.14/0.76  fof(f677,plain,(
% 3.14/0.76    v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~spl4_47),
% 3.14/0.76    inference(avatar_component_clause,[],[f675])).
% 3.14/0.76  fof(f675,plain,(
% 3.14/0.76    spl4_47 <=> v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 3.14/0.76    introduced(avatar_definition,[new_symbols(naming,[spl4_47])])).
% 3.14/0.76  fof(f3140,plain,(
% 3.14/0.76    ~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_8 | ~spl4_9 | spl4_12 | ~spl4_45 | ~spl4_46 | ~spl4_47),
% 3.14/0.76    inference(avatar_contradiction_clause,[],[f3139])).
% 3.14/0.76  fof(f3139,plain,(
% 3.14/0.76    $false | (~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_8 | ~spl4_9 | spl4_12 | ~spl4_45 | ~spl4_46 | ~spl4_47)),
% 3.14/0.76    inference(subsumption_resolution,[],[f3138,f131])).
% 3.14/0.76  fof(f3138,plain,(
% 3.14/0.76    ~v2_pre_topc(sK0) | (~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_8 | ~spl4_9 | spl4_12 | ~spl4_45 | ~spl4_46 | ~spl4_47)),
% 3.14/0.76    inference(subsumption_resolution,[],[f3137,f136])).
% 3.14/0.76  fof(f3137,plain,(
% 3.14/0.76    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_8 | ~spl4_9 | spl4_12 | ~spl4_45 | ~spl4_46 | ~spl4_47)),
% 3.14/0.76    inference(subsumption_resolution,[],[f3136,f141])).
% 3.14/0.76  fof(f3136,plain,(
% 3.14/0.76    ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl4_4 | ~spl4_5 | ~spl4_8 | ~spl4_9 | spl4_12 | ~spl4_45 | ~spl4_46 | ~spl4_47)),
% 3.14/0.76    inference(subsumption_resolution,[],[f3135,f146])).
% 3.14/0.76  fof(f3135,plain,(
% 3.14/0.76    ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl4_5 | ~spl4_8 | ~spl4_9 | spl4_12 | ~spl4_45 | ~spl4_46 | ~spl4_47)),
% 3.14/0.76    inference(subsumption_resolution,[],[f3134,f166])).
% 3.14/0.76  fof(f3134,plain,(
% 3.14/0.76    ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl4_5 | ~spl4_9 | spl4_12 | ~spl4_45 | ~spl4_46 | ~spl4_47)),
% 3.14/0.76    inference(subsumption_resolution,[],[f3133,f172])).
% 3.14/0.76  fof(f3133,plain,(
% 3.14/0.76    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl4_5 | spl4_12 | ~spl4_45 | ~spl4_46 | ~spl4_47)),
% 3.14/0.76    inference(subsumption_resolution,[],[f3132,f151])).
% 3.14/0.76  fof(f3132,plain,(
% 3.14/0.76    ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (spl4_12 | ~spl4_45 | ~spl4_46 | ~spl4_47)),
% 3.14/0.76    inference(subsumption_resolution,[],[f3131,f212])).
% 3.14/0.76  fof(f3131,plain,(
% 3.14/0.76    v5_pre_topc(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl4_45 | ~spl4_46 | ~spl4_47)),
% 3.14/0.76    inference(subsumption_resolution,[],[f3130,f672])).
% 3.14/0.76  fof(f672,plain,(
% 3.14/0.76    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~spl4_46),
% 3.14/0.76    inference(avatar_component_clause,[],[f671])).
% 3.14/0.76  fof(f3130,plain,(
% 3.14/0.76    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | v5_pre_topc(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl4_45 | ~spl4_47)),
% 3.14/0.76    inference(subsumption_resolution,[],[f3120,f677])).
% 3.14/0.76  fof(f3120,plain,(
% 3.14/0.76    ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | v5_pre_topc(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~spl4_45),
% 3.14/0.76    inference(resolution,[],[f668,f123])).
% 3.14/0.76  fof(f2984,plain,(
% 3.14/0.76    spl4_37 | ~spl4_5 | ~spl4_8 | ~spl4_9 | spl4_86),
% 3.14/0.76    inference(avatar_split_clause,[],[f2882,f1168,f170,f164,f149,f551])).
% 3.14/0.76  fof(f551,plain,(
% 3.14/0.76    spl4_37 <=> v1_xboole_0(u1_struct_0(sK1))),
% 3.14/0.76    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).
% 3.14/0.76  fof(f1168,plain,(
% 3.14/0.76    spl4_86 <=> v1_partfun1(sK2,u1_struct_0(sK0))),
% 3.14/0.76    introduced(avatar_definition,[new_symbols(naming,[spl4_86])])).
% 3.14/0.76  fof(f2882,plain,(
% 3.14/0.76    v1_xboole_0(u1_struct_0(sK1)) | (~spl4_5 | ~spl4_8 | ~spl4_9 | spl4_86)),
% 3.14/0.76    inference(subsumption_resolution,[],[f535,f1170])).
% 3.14/0.76  fof(f1170,plain,(
% 3.14/0.76    ~v1_partfun1(sK2,u1_struct_0(sK0)) | spl4_86),
% 3.14/0.76    inference(avatar_component_clause,[],[f1168])).
% 3.14/0.76  fof(f535,plain,(
% 3.14/0.76    v1_partfun1(sK2,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK1)) | (~spl4_5 | ~spl4_8 | ~spl4_9)),
% 3.14/0.76    inference(subsumption_resolution,[],[f533,f172])).
% 3.14/0.76  fof(f533,plain,(
% 3.14/0.76    v1_partfun1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v1_xboole_0(u1_struct_0(sK1)) | (~spl4_5 | ~spl4_8)),
% 3.14/0.76    inference(resolution,[],[f256,f166])).
% 3.14/0.76  fof(f256,plain,(
% 3.14/0.76    ( ! [X0,X1] : (~v1_funct_2(sK2,X0,X1) | v1_partfun1(sK2,X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) ) | ~spl4_5),
% 3.14/0.76    inference(resolution,[],[f89,f151])).
% 3.14/0.76  fof(f89,plain,(
% 3.14/0.76    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 3.14/0.76    inference(cnf_transformation,[],[f38])).
% 3.14/0.76  fof(f38,plain,(
% 3.14/0.76    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 3.14/0.76    inference(flattening,[],[f37])).
% 3.14/0.76  fof(f37,plain,(
% 3.14/0.76    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 3.14/0.76    inference(ennf_transformation,[],[f12])).
% 3.14/0.76  fof(f12,axiom,(
% 3.14/0.76    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 3.14/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).
% 3.14/0.76  fof(f2915,plain,(
% 3.14/0.76    spl4_14 | ~spl4_6 | ~spl4_13),
% 3.14/0.76    inference(avatar_split_clause,[],[f2864,f215,f154,f221])).
% 3.14/0.76  fof(f221,plain,(
% 3.14/0.76    spl4_14 <=> v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 3.14/0.76    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 3.14/0.76  fof(f2864,plain,(
% 3.14/0.76    v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl4_6 | ~spl4_13)),
% 3.14/0.76    inference(forward_demodulation,[],[f217,f156])).
% 3.14/0.76  fof(f217,plain,(
% 3.14/0.76    v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~spl4_13),
% 3.14/0.76    inference(avatar_component_clause,[],[f215])).
% 3.14/0.76  fof(f2837,plain,(
% 3.14/0.76    ~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | spl4_12 | ~spl4_26 | ~spl4_30 | ~spl4_32 | ~spl4_47 | ~spl4_57 | ~spl4_68),
% 3.14/0.76    inference(avatar_contradiction_clause,[],[f2836])).
% 3.14/0.76  fof(f2836,plain,(
% 3.14/0.76    $false | (~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | spl4_12 | ~spl4_26 | ~spl4_30 | ~spl4_32 | ~spl4_47 | ~spl4_57 | ~spl4_68)),
% 3.14/0.76    inference(subsumption_resolution,[],[f2835,f677])).
% 3.14/0.76  fof(f2835,plain,(
% 3.14/0.76    ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | spl4_12 | ~spl4_26 | ~spl4_30 | ~spl4_32 | ~spl4_57 | ~spl4_68)),
% 3.14/0.76    inference(unit_resulting_resolution,[],[f141,f146,f151,f1001,f362,f843,f439,f212,f491])).
% 3.14/0.76  fof(f491,plain,(
% 3.14/0.76    ( ! [X12,X13] : (~v5_pre_topc(X12,sK0,g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13))) | ~v1_funct_2(X12,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13)))) | ~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13)))))) | v5_pre_topc(X12,sK0,X13) | ~v1_funct_1(X12) | ~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X13)))) | ~v1_funct_2(X12,k1_relat_1(sK2),u1_struct_0(X13)) | ~l1_pre_topc(X13) | ~v2_pre_topc(X13)) ) | (~spl4_1 | ~spl4_2 | ~spl4_30)),
% 3.14/0.76    inference(subsumption_resolution,[],[f490,f131])).
% 3.14/0.76  fof(f490,plain,(
% 3.14/0.76    ( ! [X12,X13] : (~v1_funct_2(X12,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13)))) | ~v5_pre_topc(X12,sK0,g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13))) | ~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13)))))) | v5_pre_topc(X12,sK0,X13) | ~v1_funct_1(X12) | ~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X13)))) | ~v1_funct_2(X12,k1_relat_1(sK2),u1_struct_0(X13)) | ~l1_pre_topc(X13) | ~v2_pre_topc(X13) | ~v2_pre_topc(sK0)) ) | (~spl4_2 | ~spl4_30)),
% 3.14/0.76    inference(subsumption_resolution,[],[f476,f136])).
% 3.14/0.76  fof(f476,plain,(
% 3.14/0.76    ( ! [X12,X13] : (~v1_funct_2(X12,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13)))) | ~v5_pre_topc(X12,sK0,g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13))) | ~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13)))))) | v5_pre_topc(X12,sK0,X13) | ~v1_funct_1(X12) | ~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X13)))) | ~v1_funct_2(X12,k1_relat_1(sK2),u1_struct_0(X13)) | ~l1_pre_topc(X13) | ~v2_pre_topc(X13) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)) ) | ~spl4_30),
% 3.14/0.76    inference(superposition,[],[f123,f390])).
% 3.14/0.76  fof(f390,plain,(
% 3.14/0.76    u1_struct_0(sK0) = k1_relat_1(sK2) | ~spl4_30),
% 3.14/0.76    inference(avatar_component_clause,[],[f388])).
% 3.14/0.76  fof(f388,plain,(
% 3.14/0.76    spl4_30 <=> u1_struct_0(sK0) = k1_relat_1(sK2)),
% 3.14/0.76    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).
% 3.14/0.76  fof(f439,plain,(
% 3.14/0.76    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~spl4_32),
% 3.14/0.76    inference(avatar_component_clause,[],[f437])).
% 3.14/0.76  fof(f437,plain,(
% 3.14/0.76    spl4_32 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))),
% 3.14/0.76    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).
% 3.14/0.76  fof(f843,plain,(
% 3.14/0.76    v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~spl4_57),
% 3.14/0.76    inference(avatar_component_clause,[],[f841])).
% 3.14/0.76  fof(f841,plain,(
% 3.14/0.76    spl4_57 <=> v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 3.14/0.76    introduced(avatar_definition,[new_symbols(naming,[spl4_57])])).
% 3.14/0.76  fof(f362,plain,(
% 3.14/0.76    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))) | ~spl4_26),
% 3.14/0.76    inference(avatar_component_clause,[],[f360])).
% 3.14/0.76  fof(f360,plain,(
% 3.14/0.76    spl4_26 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))))),
% 3.14/0.76    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 3.14/0.76  fof(f1001,plain,(
% 3.14/0.76    v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) | ~spl4_68),
% 3.14/0.76    inference(avatar_component_clause,[],[f999])).
% 3.14/0.76  fof(f999,plain,(
% 3.14/0.76    spl4_68 <=> v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))),
% 3.14/0.76    introduced(avatar_definition,[new_symbols(naming,[spl4_68])])).
% 3.14/0.76  fof(f2625,plain,(
% 3.14/0.76    u1_struct_0(sK0) != k1_relat_1(sK2) | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))),
% 3.14/0.76    introduced(theory_tautology_sat_conflict,[])).
% 3.14/0.76  fof(f2511,plain,(
% 3.14/0.76    k1_xboole_0 != sK2 | k1_xboole_0 != k1_relat_1(k1_xboole_0) | k1_xboole_0 != u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | u1_struct_0(sK0) != k1_relat_1(sK2) | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 3.14/0.76    introduced(theory_tautology_sat_conflict,[])).
% 3.14/0.76  fof(f2509,plain,(
% 3.14/0.76    ~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_12 | ~spl4_26 | ~spl4_30 | ~spl4_32 | ~spl4_57 | ~spl4_63 | ~spl4_68 | spl4_112),
% 3.14/0.76    inference(avatar_contradiction_clause,[],[f2508])).
% 3.14/0.76  fof(f2508,plain,(
% 3.14/0.76    $false | (~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_12 | ~spl4_26 | ~spl4_30 | ~spl4_32 | ~spl4_57 | ~spl4_63 | ~spl4_68 | spl4_112)),
% 3.14/0.76    inference(subsumption_resolution,[],[f2507,f2166])).
% 3.14/0.76  fof(f2166,plain,(
% 3.14/0.76    ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | spl4_112),
% 3.14/0.76    inference(avatar_component_clause,[],[f2164])).
% 3.14/0.76  fof(f2164,plain,(
% 3.14/0.76    spl4_112 <=> v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 3.14/0.76    introduced(avatar_definition,[new_symbols(naming,[spl4_112])])).
% 3.14/0.76  fof(f2507,plain,(
% 3.14/0.76    v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_12 | ~spl4_26 | ~spl4_30 | ~spl4_32 | ~spl4_57 | ~spl4_63 | ~spl4_68)),
% 3.14/0.76    inference(forward_demodulation,[],[f2506,f980])).
% 3.14/0.76  fof(f2506,plain,(
% 3.14/0.76    v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_12 | ~spl4_26 | ~spl4_30 | ~spl4_32 | ~spl4_57 | ~spl4_68)),
% 3.14/0.76    inference(subsumption_resolution,[],[f2505,f141])).
% 3.14/0.76  fof(f2505,plain,(
% 3.14/0.76    v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(sK1) | (~spl4_1 | ~spl4_2 | ~spl4_4 | ~spl4_5 | ~spl4_12 | ~spl4_26 | ~spl4_30 | ~spl4_32 | ~spl4_57 | ~spl4_68)),
% 3.14/0.76    inference(subsumption_resolution,[],[f2504,f146])).
% 3.14/0.76  fof(f2504,plain,(
% 3.14/0.76    v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | (~spl4_1 | ~spl4_2 | ~spl4_5 | ~spl4_12 | ~spl4_26 | ~spl4_30 | ~spl4_32 | ~spl4_57 | ~spl4_68)),
% 3.14/0.76    inference(subsumption_resolution,[],[f2503,f1001])).
% 3.14/0.76  fof(f2503,plain,(
% 3.14/0.76    v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | (~spl4_1 | ~spl4_2 | ~spl4_5 | ~spl4_12 | ~spl4_26 | ~spl4_30 | ~spl4_32 | ~spl4_57)),
% 3.14/0.76    inference(subsumption_resolution,[],[f2502,f362])).
% 3.14/0.76  fof(f2502,plain,(
% 3.14/0.76    v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | (~spl4_1 | ~spl4_2 | ~spl4_5 | ~spl4_12 | ~spl4_30 | ~spl4_32 | ~spl4_57)),
% 3.14/0.76    inference(subsumption_resolution,[],[f2501,f151])).
% 3.14/0.76  fof(f2501,plain,(
% 3.14/0.76    v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | (~spl4_1 | ~spl4_2 | ~spl4_12 | ~spl4_30 | ~spl4_32 | ~spl4_57)),
% 3.14/0.76    inference(subsumption_resolution,[],[f2500,f439])).
% 3.14/0.76  fof(f2500,plain,(
% 3.14/0.76    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | (~spl4_1 | ~spl4_2 | ~spl4_12 | ~spl4_30 | ~spl4_57)),
% 3.14/0.76    inference(subsumption_resolution,[],[f2482,f843])).
% 3.14/0.76  fof(f2482,plain,(
% 3.14/0.76    ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | (~spl4_1 | ~spl4_2 | ~spl4_12 | ~spl4_30)),
% 3.14/0.76    inference(resolution,[],[f487,f213])).
% 3.14/0.76  fof(f213,plain,(
% 3.14/0.76    v5_pre_topc(sK2,sK0,sK1) | ~spl4_12),
% 3.14/0.76    inference(avatar_component_clause,[],[f211])).
% 3.14/0.76  fof(f487,plain,(
% 3.14/0.76    ( ! [X8,X9] : (~v5_pre_topc(X8,sK0,X9) | ~v1_funct_2(X8,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(X9),u1_pre_topc(X9)))) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(X9),u1_pre_topc(X9)))))) | v5_pre_topc(X8,sK0,g1_pre_topc(u1_struct_0(X9),u1_pre_topc(X9))) | ~v1_funct_1(X8) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X9)))) | ~v1_funct_2(X8,k1_relat_1(sK2),u1_struct_0(X9)) | ~l1_pre_topc(X9) | ~v2_pre_topc(X9)) ) | (~spl4_1 | ~spl4_2 | ~spl4_30)),
% 3.14/0.76    inference(subsumption_resolution,[],[f486,f131])).
% 3.14/0.76  fof(f486,plain,(
% 3.14/0.76    ( ! [X8,X9] : (~v1_funct_2(X8,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(X9),u1_pre_topc(X9)))) | ~v5_pre_topc(X8,sK0,X9) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(X9),u1_pre_topc(X9)))))) | v5_pre_topc(X8,sK0,g1_pre_topc(u1_struct_0(X9),u1_pre_topc(X9))) | ~v1_funct_1(X8) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X9)))) | ~v1_funct_2(X8,k1_relat_1(sK2),u1_struct_0(X9)) | ~l1_pre_topc(X9) | ~v2_pre_topc(X9) | ~v2_pre_topc(sK0)) ) | (~spl4_2 | ~spl4_30)),
% 3.14/0.76    inference(subsumption_resolution,[],[f474,f136])).
% 3.14/0.76  fof(f474,plain,(
% 3.14/0.76    ( ! [X8,X9] : (~v1_funct_2(X8,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(X9),u1_pre_topc(X9)))) | ~v5_pre_topc(X8,sK0,X9) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(X9),u1_pre_topc(X9)))))) | v5_pre_topc(X8,sK0,g1_pre_topc(u1_struct_0(X9),u1_pre_topc(X9))) | ~v1_funct_1(X8) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X9)))) | ~v1_funct_2(X8,k1_relat_1(sK2),u1_struct_0(X9)) | ~l1_pre_topc(X9) | ~v2_pre_topc(X9) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)) ) | ~spl4_30),
% 3.14/0.76    inference(superposition,[],[f122,f390])).
% 3.14/0.76  fof(f2167,plain,(
% 3.14/0.76    ~spl4_112 | spl4_47 | ~spl4_63),
% 3.14/0.76    inference(avatar_split_clause,[],[f2162,f978,f675,f2164])).
% 3.14/0.76  fof(f2162,plain,(
% 3.14/0.76    ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (spl4_47 | ~spl4_63)),
% 3.14/0.76    inference(forward_demodulation,[],[f676,f980])).
% 3.14/0.76  fof(f676,plain,(
% 3.14/0.76    ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | spl4_47),
% 3.14/0.76    inference(avatar_component_clause,[],[f675])).
% 3.14/0.76  fof(f2161,plain,(
% 3.14/0.76    ~spl4_47 | ~spl4_1 | ~spl4_2 | ~spl4_5 | ~spl4_11 | ~spl4_15 | ~spl4_21 | ~spl4_30 | ~spl4_32 | ~spl4_57 | ~spl4_62 | spl4_91),
% 3.14/0.76    inference(avatar_split_clause,[],[f2064,f1213,f962,f841,f437,f388,f321,f227,f201,f149,f134,f129,f675])).
% 3.14/0.76  fof(f321,plain,(
% 3.14/0.76    spl4_21 <=> v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 3.14/0.76    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 3.14/0.76  fof(f962,plain,(
% 3.14/0.76    spl4_62 <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 3.14/0.76    introduced(avatar_definition,[new_symbols(naming,[spl4_62])])).
% 3.14/0.76  fof(f1213,plain,(
% 3.14/0.76    spl4_91 <=> v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 3.14/0.76    introduced(avatar_definition,[new_symbols(naming,[spl4_91])])).
% 3.14/0.76  fof(f2064,plain,(
% 3.14/0.76    ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl4_1 | ~spl4_2 | ~spl4_5 | ~spl4_11 | ~spl4_15 | ~spl4_21 | ~spl4_30 | ~spl4_32 | ~spl4_57 | ~spl4_62 | spl4_91)),
% 3.14/0.76    inference(subsumption_resolution,[],[f2063,f1214])).
% 3.14/0.76  fof(f1214,plain,(
% 3.14/0.76    ~v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | spl4_91),
% 3.14/0.76    inference(avatar_component_clause,[],[f1213])).
% 3.14/0.76  fof(f2063,plain,(
% 3.14/0.76    v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl4_1 | ~spl4_2 | ~spl4_5 | ~spl4_11 | ~spl4_15 | ~spl4_21 | ~spl4_30 | ~spl4_32 | ~spl4_57 | ~spl4_62)),
% 3.14/0.76    inference(subsumption_resolution,[],[f2016,f843])).
% 3.14/0.76  fof(f2016,plain,(
% 3.14/0.76    ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl4_1 | ~spl4_2 | ~spl4_5 | ~spl4_11 | ~spl4_15 | ~spl4_21 | ~spl4_30 | ~spl4_32 | ~spl4_62)),
% 3.14/0.76    inference(forward_demodulation,[],[f2015,f390])).
% 3.14/0.76  fof(f2015,plain,(
% 3.14/0.76    v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl4_1 | ~spl4_2 | ~spl4_5 | ~spl4_11 | ~spl4_15 | ~spl4_21 | ~spl4_30 | ~spl4_32 | ~spl4_62)),
% 3.14/0.76    inference(subsumption_resolution,[],[f2014,f439])).
% 3.14/0.76  fof(f2014,plain,(
% 3.14/0.76    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl4_1 | ~spl4_2 | ~spl4_5 | ~spl4_11 | ~spl4_15 | ~spl4_21 | ~spl4_30 | ~spl4_62)),
% 3.14/0.76    inference(forward_demodulation,[],[f2013,f390])).
% 3.14/0.76  fof(f2013,plain,(
% 3.14/0.76    v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl4_1 | ~spl4_2 | ~spl4_5 | ~spl4_11 | ~spl4_15 | ~spl4_21 | ~spl4_30 | ~spl4_62)),
% 3.14/0.76    inference(forward_demodulation,[],[f1905,f390])).
% 3.14/0.76  fof(f1905,plain,(
% 3.14/0.76    ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl4_1 | ~spl4_2 | ~spl4_5 | ~spl4_11 | ~spl4_15 | ~spl4_21 | ~spl4_62)),
% 3.14/0.76    inference(subsumption_resolution,[],[f1502,f964])).
% 3.14/0.76  fof(f964,plain,(
% 3.14/0.76    l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~spl4_62),
% 3.14/0.76    inference(avatar_component_clause,[],[f962])).
% 3.14/0.76  fof(f1502,plain,(
% 3.14/0.76    ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl4_1 | ~spl4_2 | ~spl4_5 | ~spl4_11 | ~spl4_15 | ~spl4_21)),
% 3.14/0.76    inference(subsumption_resolution,[],[f1501,f131])).
% 3.14/0.76  fof(f1501,plain,(
% 3.14/0.76    ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(sK0) | (~spl4_2 | ~spl4_5 | ~spl4_11 | ~spl4_15 | ~spl4_21)),
% 3.14/0.76    inference(subsumption_resolution,[],[f1500,f136])).
% 3.14/0.76  fof(f1500,plain,(
% 3.14/0.76    ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl4_5 | ~spl4_11 | ~spl4_15 | ~spl4_21)),
% 3.14/0.76    inference(subsumption_resolution,[],[f1499,f323])).
% 3.14/0.76  fof(f323,plain,(
% 3.14/0.76    v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~spl4_21),
% 3.14/0.76    inference(avatar_component_clause,[],[f321])).
% 3.14/0.76  fof(f1499,plain,(
% 3.14/0.76    ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl4_5 | ~spl4_11 | ~spl4_15)),
% 3.14/0.76    inference(subsumption_resolution,[],[f1498,f151])).
% 3.14/0.76  fof(f1498,plain,(
% 3.14/0.76    ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl4_11 | ~spl4_15)),
% 3.14/0.76    inference(subsumption_resolution,[],[f265,f229])).
% 3.14/0.76  fof(f265,plain,(
% 3.14/0.76    ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~spl4_11),
% 3.14/0.76    inference(resolution,[],[f120,f203])).
% 3.14/0.76  fof(f2059,plain,(
% 3.14/0.76    ~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_11 | ~spl4_12 | ~spl4_15 | ~spl4_20 | ~spl4_26 | ~spl4_27 | ~spl4_30 | ~spl4_39 | ~spl4_44 | ~spl4_68 | spl4_91),
% 3.14/0.76    inference(avatar_contradiction_clause,[],[f2058])).
% 3.14/0.76  fof(f2058,plain,(
% 3.14/0.76    $false | (~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_11 | ~spl4_12 | ~spl4_15 | ~spl4_20 | ~spl4_26 | ~spl4_27 | ~spl4_30 | ~spl4_39 | ~spl4_44 | ~spl4_68 | spl4_91)),
% 3.14/0.76    inference(subsumption_resolution,[],[f2057,f362])).
% 3.14/0.76  fof(f2057,plain,(
% 3.14/0.76    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))) | (~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_11 | ~spl4_12 | ~spl4_15 | ~spl4_20 | ~spl4_26 | ~spl4_27 | ~spl4_30 | ~spl4_39 | ~spl4_44 | ~spl4_68 | spl4_91)),
% 3.14/0.76    inference(forward_demodulation,[],[f2056,f1868])).
% 3.14/0.76  fof(f1868,plain,(
% 3.14/0.76    k1_relat_1(sK2) = u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | (~spl4_30 | ~spl4_39)),
% 3.14/0.76    inference(forward_demodulation,[],[f562,f390])).
% 3.14/0.76  fof(f2056,plain,(
% 3.14/0.76    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | (~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_11 | ~spl4_12 | ~spl4_15 | ~spl4_20 | ~spl4_26 | ~spl4_27 | ~spl4_30 | ~spl4_39 | ~spl4_44 | ~spl4_68 | spl4_91)),
% 3.14/0.76    inference(subsumption_resolution,[],[f2055,f141])).
% 3.14/0.76  fof(f2055,plain,(
% 3.14/0.76    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v2_pre_topc(sK1) | (~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_11 | ~spl4_12 | ~spl4_15 | ~spl4_20 | ~spl4_26 | ~spl4_27 | ~spl4_30 | ~spl4_39 | ~spl4_44 | ~spl4_68 | spl4_91)),
% 3.14/0.76    inference(subsumption_resolution,[],[f2054,f146])).
% 3.14/0.76  fof(f2054,plain,(
% 3.14/0.76    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | (~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_11 | ~spl4_12 | ~spl4_15 | ~spl4_20 | ~spl4_26 | ~spl4_27 | ~spl4_30 | ~spl4_39 | ~spl4_44 | ~spl4_68 | spl4_91)),
% 3.14/0.76    inference(subsumption_resolution,[],[f2053,f1001])).
% 3.14/0.76  fof(f2053,plain,(
% 3.14/0.76    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | (~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_11 | ~spl4_12 | ~spl4_15 | ~spl4_20 | ~spl4_26 | ~spl4_27 | ~spl4_30 | ~spl4_39 | ~spl4_44 | spl4_91)),
% 3.14/0.76    inference(subsumption_resolution,[],[f2052,f362])).
% 3.14/0.76  fof(f2052,plain,(
% 3.14/0.76    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | (~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_11 | ~spl4_12 | ~spl4_15 | ~spl4_20 | ~spl4_26 | ~spl4_27 | ~spl4_30 | ~spl4_39 | ~spl4_44 | spl4_91)),
% 3.14/0.76    inference(subsumption_resolution,[],[f2051,f151])).
% 3.14/0.76  fof(f2051,plain,(
% 3.14/0.76    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | (~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_11 | ~spl4_12 | ~spl4_15 | ~spl4_20 | ~spl4_26 | ~spl4_27 | ~spl4_30 | ~spl4_39 | ~spl4_44 | spl4_91)),
% 3.14/0.76    inference(subsumption_resolution,[],[f2050,f2047])).
% 3.14/0.76  fof(f2047,plain,(
% 3.14/0.76    ~v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1) | (~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_11 | ~spl4_15 | ~spl4_20 | ~spl4_26 | ~spl4_27 | ~spl4_30 | ~spl4_39 | ~spl4_44 | spl4_91)),
% 3.14/0.76    inference(subsumption_resolution,[],[f2046,f655])).
% 3.14/0.76  fof(f655,plain,(
% 3.14/0.76    v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~spl4_44),
% 3.14/0.76    inference(avatar_component_clause,[],[f654])).
% 3.14/0.76  fof(f654,plain,(
% 3.14/0.76    spl4_44 <=> v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))),
% 3.14/0.76    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).
% 3.14/0.76  fof(f2046,plain,(
% 3.14/0.76    ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1) | (~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_11 | ~spl4_15 | ~spl4_20 | ~spl4_26 | ~spl4_27 | ~spl4_30 | ~spl4_39 | spl4_91)),
% 3.14/0.76    inference(forward_demodulation,[],[f2045,f390])).
% 3.14/0.76  fof(f2045,plain,(
% 3.14/0.76    ~v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | (~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_11 | ~spl4_15 | ~spl4_20 | ~spl4_26 | ~spl4_27 | ~spl4_30 | ~spl4_39 | spl4_91)),
% 3.14/0.76    inference(subsumption_resolution,[],[f2044,f362])).
% 3.14/0.76  fof(f2044,plain,(
% 3.14/0.76    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))) | ~v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | (~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_11 | ~spl4_15 | ~spl4_20 | ~spl4_27 | ~spl4_30 | ~spl4_39 | spl4_91)),
% 3.14/0.76    inference(forward_demodulation,[],[f2043,f1868])).
% 3.14/0.76  fof(f2043,plain,(
% 3.14/0.76    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | (~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_11 | ~spl4_15 | ~spl4_20 | ~spl4_27 | ~spl4_30 | spl4_91)),
% 3.14/0.76    inference(forward_demodulation,[],[f2042,f390])).
% 3.14/0.76  fof(f2042,plain,(
% 3.14/0.76    ~v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | (~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_11 | ~spl4_15 | ~spl4_20 | ~spl4_27 | ~spl4_30 | spl4_91)),
% 3.14/0.76    inference(subsumption_resolution,[],[f2041,f1214])).
% 3.14/0.76  fof(f2041,plain,(
% 3.14/0.76    v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | (~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_11 | ~spl4_15 | ~spl4_20 | ~spl4_27 | ~spl4_30)),
% 3.14/0.76    inference(forward_demodulation,[],[f1457,f390])).
% 3.14/0.76  fof(f1457,plain,(
% 3.14/0.76    ~v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | (~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_11 | ~spl4_15 | ~spl4_20 | ~spl4_27 | ~spl4_30)),
% 3.14/0.76    inference(forward_demodulation,[],[f1456,f390])).
% 3.14/0.76  fof(f2050,plain,(
% 3.14/0.76    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | (~spl4_1 | ~spl4_2 | ~spl4_12 | ~spl4_30 | ~spl4_44)),
% 3.14/0.76    inference(subsumption_resolution,[],[f2049,f655])).
% 3.14/0.76  fof(f2049,plain,(
% 3.14/0.76    ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | (~spl4_1 | ~spl4_2 | ~spl4_12 | ~spl4_30)),
% 3.14/0.76    inference(resolution,[],[f213,f479])).
% 3.14/0.76  fof(f479,plain,(
% 3.14/0.76    ( ! [X0,X1] : (~v5_pre_topc(X0,sK0,X1) | ~v1_funct_2(X0,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X1)))) | v5_pre_topc(X0,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X1) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X1)))) | ~v1_funct_2(X0,k1_relat_1(sK2),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) ) | (~spl4_1 | ~spl4_2 | ~spl4_30)),
% 3.14/0.76    inference(subsumption_resolution,[],[f478,f131])).
% 3.14/0.76  fof(f478,plain,(
% 3.14/0.76    ( ! [X0,X1] : (~v1_funct_2(X0,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X1)) | ~v5_pre_topc(X0,sK0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X1)))) | v5_pre_topc(X0,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X1) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X1)))) | ~v1_funct_2(X0,k1_relat_1(sK2),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~v2_pre_topc(sK0)) ) | (~spl4_2 | ~spl4_30)),
% 3.14/0.76    inference(subsumption_resolution,[],[f470,f136])).
% 3.14/0.76  fof(f470,plain,(
% 3.14/0.76    ( ! [X0,X1] : (~v1_funct_2(X0,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X1)) | ~v5_pre_topc(X0,sK0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X1)))) | v5_pre_topc(X0,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X1) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X1)))) | ~v1_funct_2(X0,k1_relat_1(sK2),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)) ) | ~spl4_30),
% 3.14/0.76    inference(superposition,[],[f120,f390])).
% 3.14/0.76  fof(f2039,plain,(
% 3.14/0.76    sK2 != sK3 | u1_struct_0(sK0) != k1_relat_1(sK2) | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 3.14/0.76    introduced(theory_tautology_sat_conflict,[])).
% 3.14/0.76  fof(f2011,plain,(
% 3.14/0.76    u1_struct_0(sK0) != k1_relat_1(sK2) | k1_xboole_0 != u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),k1_xboole_0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))),
% 3.14/0.76    introduced(theory_tautology_sat_conflict,[])).
% 3.14/0.76  fof(f2010,plain,(
% 3.14/0.76    ~spl4_7 | spl4_56 | ~spl4_59),
% 3.14/0.76    inference(avatar_contradiction_clause,[],[f2009])).
% 3.14/0.76  fof(f2009,plain,(
% 3.14/0.76    $false | (~spl4_7 | spl4_56 | ~spl4_59)),
% 3.14/0.76    inference(subsumption_resolution,[],[f837,f908])).
% 3.14/0.76  fof(f908,plain,(
% 3.14/0.76    v1_xboole_0(sK2) | (~spl4_7 | ~spl4_59)),
% 3.14/0.76    inference(resolution,[],[f899,f209])).
% 3.14/0.76  fof(f209,plain,(
% 3.14/0.76    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) | v1_xboole_0(X0)) ) | ~spl4_7),
% 3.14/0.76    inference(resolution,[],[f90,f161])).
% 3.14/0.76  fof(f161,plain,(
% 3.14/0.76    v1_xboole_0(k1_xboole_0) | ~spl4_7),
% 3.14/0.76    inference(avatar_component_clause,[],[f159])).
% 3.14/0.76  fof(f159,plain,(
% 3.14/0.76    spl4_7 <=> v1_xboole_0(k1_xboole_0)),
% 3.14/0.76    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 3.14/0.76  fof(f90,plain,(
% 3.14/0.76    ( ! [X2,X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | v1_xboole_0(X2)) )),
% 3.14/0.76    inference(cnf_transformation,[],[f39])).
% 3.14/0.76  fof(f39,plain,(
% 3.14/0.76    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 3.14/0.76    inference(ennf_transformation,[],[f9])).
% 3.14/0.76  fof(f9,axiom,(
% 3.14/0.76    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 3.14/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).
% 3.14/0.76  fof(f899,plain,(
% 3.14/0.76    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),k1_xboole_0))) | ~spl4_59),
% 3.14/0.76    inference(avatar_component_clause,[],[f897])).
% 3.14/0.76  fof(f897,plain,(
% 3.14/0.76    spl4_59 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),k1_xboole_0)))),
% 3.14/0.76    introduced(avatar_definition,[new_symbols(naming,[spl4_59])])).
% 3.14/0.76  fof(f837,plain,(
% 3.14/0.76    ~v1_xboole_0(sK2) | spl4_56),
% 3.14/0.76    inference(avatar_component_clause,[],[f836])).
% 3.14/0.76  fof(f836,plain,(
% 3.14/0.76    spl4_56 <=> v1_xboole_0(sK2)),
% 3.14/0.76    introduced(avatar_definition,[new_symbols(naming,[spl4_56])])).
% 3.14/0.76  fof(f1957,plain,(
% 3.14/0.76    ~spl4_7 | ~spl4_19 | ~spl4_56 | spl4_63),
% 3.14/0.76    inference(avatar_contradiction_clause,[],[f1956])).
% 3.14/0.76  fof(f1956,plain,(
% 3.14/0.76    $false | (~spl4_7 | ~spl4_19 | ~spl4_56 | spl4_63)),
% 3.14/0.76    inference(subsumption_resolution,[],[f979,f932])).
% 3.14/0.76  fof(f932,plain,(
% 3.14/0.76    k1_xboole_0 = sK2 | (~spl4_7 | ~spl4_19 | ~spl4_56)),
% 3.14/0.76    inference(forward_demodulation,[],[f923,f307])).
% 3.14/0.76  fof(f307,plain,(
% 3.14/0.76    k1_xboole_0 = k6_partfun1(k1_xboole_0) | (~spl4_7 | ~spl4_19)),
% 3.14/0.76    inference(unit_resulting_resolution,[],[f161,f301,f97])).
% 3.14/0.76  fof(f97,plain,(
% 3.14/0.76    ( ! [X0,X1] : (~v1_xboole_0(X0) | X0 = X1 | ~v1_xboole_0(X1)) )),
% 3.14/0.76    inference(cnf_transformation,[],[f43])).
% 3.14/0.76  fof(f43,plain,(
% 3.14/0.76    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 3.14/0.76    inference(ennf_transformation,[],[f3])).
% 3.14/0.76  fof(f3,axiom,(
% 3.14/0.76    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 3.14/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).
% 3.14/0.76  fof(f301,plain,(
% 3.14/0.76    v1_xboole_0(k6_partfun1(k1_xboole_0)) | ~spl4_19),
% 3.14/0.76    inference(avatar_component_clause,[],[f299])).
% 3.14/0.76  fof(f299,plain,(
% 3.14/0.76    spl4_19 <=> v1_xboole_0(k6_partfun1(k1_xboole_0))),
% 3.14/0.76    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 3.14/0.76  fof(f923,plain,(
% 3.14/0.76    sK2 = k6_partfun1(k1_xboole_0) | (~spl4_19 | ~spl4_56)),
% 3.14/0.76    inference(unit_resulting_resolution,[],[f301,f838,f97])).
% 3.14/0.76  fof(f838,plain,(
% 3.14/0.76    v1_xboole_0(sK2) | ~spl4_56),
% 3.14/0.76    inference(avatar_component_clause,[],[f836])).
% 3.14/0.76  fof(f979,plain,(
% 3.14/0.76    k1_xboole_0 != sK2 | spl4_63),
% 3.14/0.76    inference(avatar_component_clause,[],[f978])).
% 3.14/0.76  fof(f1634,plain,(
% 3.14/0.76    spl4_78 | ~spl4_12 | ~spl4_63),
% 3.14/0.76    inference(avatar_split_clause,[],[f1496,f978,f211,f1107])).
% 3.14/0.76  fof(f1496,plain,(
% 3.14/0.76    v5_pre_topc(k1_xboole_0,sK0,sK1) | (~spl4_12 | ~spl4_63)),
% 3.14/0.76    inference(forward_demodulation,[],[f213,f980])).
% 3.14/0.76  fof(f1388,plain,(
% 3.14/0.76    spl4_102 | ~spl4_75),
% 3.14/0.76    inference(avatar_split_clause,[],[f1136,f1078,f1385])).
% 3.14/0.76  fof(f1078,plain,(
% 3.14/0.76    spl4_75 <=> k1_xboole_0 = k6_partfun1(k1_xboole_0)),
% 3.14/0.76    introduced(avatar_definition,[new_symbols(naming,[spl4_75])])).
% 3.14/0.76  fof(f1136,plain,(
% 3.14/0.76    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl4_75),
% 3.14/0.76    inference(superposition,[],[f326,f1080])).
% 3.14/0.76  fof(f1080,plain,(
% 3.14/0.76    k1_xboole_0 = k6_partfun1(k1_xboole_0) | ~spl4_75),
% 3.14/0.76    inference(avatar_component_clause,[],[f1078])).
% 3.14/0.76  fof(f326,plain,(
% 3.14/0.76    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 3.14/0.76    inference(unit_resulting_resolution,[],[f178,f79,f196,f92])).
% 3.14/0.76  fof(f92,plain,(
% 3.14/0.76    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | ~v1_partfun1(X1,X0) | k1_relat_1(X1) = X0 | ~v1_relat_1(X1)) )),
% 3.14/0.76    inference(cnf_transformation,[],[f60])).
% 3.14/0.76  fof(f60,plain,(
% 3.14/0.76    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.14/0.76    inference(nnf_transformation,[],[f42])).
% 3.14/0.76  fof(f42,plain,(
% 3.14/0.76    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.14/0.76    inference(flattening,[],[f41])).
% 3.14/0.76  fof(f41,plain,(
% 3.14/0.76    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.14/0.76    inference(ennf_transformation,[],[f14])).
% 3.14/0.76  fof(f14,axiom,(
% 3.14/0.76    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 3.14/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).
% 3.14/0.76  fof(f196,plain,(
% 3.14/0.76    ( ! [X0] : (v4_relat_1(k6_partfun1(X0),X0)) )),
% 3.14/0.76    inference(unit_resulting_resolution,[],[f80,f100])).
% 3.14/0.76  fof(f100,plain,(
% 3.14/0.76    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 3.14/0.76    inference(cnf_transformation,[],[f46])).
% 3.14/0.76  fof(f46,plain,(
% 3.14/0.76    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.14/0.76    inference(ennf_transformation,[],[f25])).
% 3.14/0.76  fof(f25,plain,(
% 3.14/0.76    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 3.14/0.76    inference(pure_predicate_removal,[],[f8])).
% 3.14/0.76  fof(f8,axiom,(
% 3.14/0.76    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.14/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 3.14/0.76  fof(f80,plain,(
% 3.14/0.76    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.14/0.76    inference(cnf_transformation,[],[f15])).
% 3.14/0.76  fof(f15,axiom,(
% 3.14/0.76    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 3.14/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 3.14/0.76  fof(f79,plain,(
% 3.14/0.76    ( ! [X0] : (v1_partfun1(k6_partfun1(X0),X0)) )),
% 3.14/0.76    inference(cnf_transformation,[],[f15])).
% 3.14/0.76  fof(f178,plain,(
% 3.14/0.76    ( ! [X0] : (v1_relat_1(k6_partfun1(X0))) )),
% 3.14/0.76    inference(unit_resulting_resolution,[],[f80,f98])).
% 3.14/0.76  fof(f98,plain,(
% 3.14/0.76    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 3.14/0.76    inference(cnf_transformation,[],[f44])).
% 3.14/0.76  fof(f44,plain,(
% 3.14/0.76    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.14/0.76    inference(ennf_transformation,[],[f7])).
% 3.14/0.76  fof(f7,axiom,(
% 3.14/0.76    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.14/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 3.14/0.76  fof(f1216,plain,(
% 3.14/0.76    spl4_91 | ~spl4_14 | ~spl4_30),
% 3.14/0.76    inference(avatar_split_clause,[],[f461,f388,f221,f1213])).
% 3.14/0.76  fof(f461,plain,(
% 3.14/0.76    v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl4_14 | ~spl4_30)),
% 3.14/0.76    inference(superposition,[],[f223,f390])).
% 3.14/0.76  fof(f223,plain,(
% 3.14/0.76    v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~spl4_14),
% 3.14/0.76    inference(avatar_component_clause,[],[f221])).
% 3.14/0.76  fof(f1171,plain,(
% 3.14/0.76    spl4_30 | ~spl4_86 | ~spl4_10 | ~spl4_18),
% 3.14/0.76    inference(avatar_split_clause,[],[f294,f289,f188,f1168,f388])).
% 3.14/0.76  fof(f188,plain,(
% 3.14/0.76    spl4_10 <=> v1_relat_1(sK2)),
% 3.14/0.76    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 3.14/0.76  fof(f289,plain,(
% 3.14/0.76    spl4_18 <=> v4_relat_1(sK2,u1_struct_0(sK0))),
% 3.14/0.76    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 3.14/0.76  fof(f294,plain,(
% 3.14/0.76    ~v1_partfun1(sK2,u1_struct_0(sK0)) | u1_struct_0(sK0) = k1_relat_1(sK2) | (~spl4_10 | ~spl4_18)),
% 3.14/0.76    inference(subsumption_resolution,[],[f293,f190])).
% 3.14/0.76  fof(f190,plain,(
% 3.14/0.76    v1_relat_1(sK2) | ~spl4_10),
% 3.14/0.76    inference(avatar_component_clause,[],[f188])).
% 3.14/0.76  fof(f293,plain,(
% 3.14/0.76    ~v1_partfun1(sK2,u1_struct_0(sK0)) | u1_struct_0(sK0) = k1_relat_1(sK2) | ~v1_relat_1(sK2) | ~spl4_18),
% 3.14/0.76    inference(resolution,[],[f291,f92])).
% 3.14/0.76  fof(f291,plain,(
% 3.14/0.76    v4_relat_1(sK2,u1_struct_0(sK0)) | ~spl4_18),
% 3.14/0.76    inference(avatar_component_clause,[],[f289])).
% 3.14/0.76  fof(f1086,plain,(
% 3.14/0.76    spl4_76 | ~spl4_7 | ~spl4_19),
% 3.14/0.76    inference(avatar_split_clause,[],[f514,f299,f159,f1083])).
% 3.14/0.76  fof(f514,plain,(
% 3.14/0.76    v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl4_7 | ~spl4_19)),
% 3.14/0.76    inference(forward_demodulation,[],[f513,f307])).
% 3.14/0.76  fof(f513,plain,(
% 3.14/0.76    v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0)),
% 3.14/0.76    inference(subsumption_resolution,[],[f512,f80])).
% 3.14/0.76  fof(f512,plain,(
% 3.14/0.76    v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0) | ~m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 3.14/0.76    inference(subsumption_resolution,[],[f510,f326])).
% 3.14/0.76  fof(f510,plain,(
% 3.14/0.76    k1_xboole_0 != k1_relat_1(k6_partfun1(k1_xboole_0)) | v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0) | ~m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 3.14/0.76    inference(superposition,[],[f118,f238])).
% 3.14/0.76  fof(f238,plain,(
% 3.14/0.76    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = k1_relset_1(X0,X0,k6_partfun1(X0))) )),
% 3.14/0.76    inference(unit_resulting_resolution,[],[f80,f99])).
% 3.14/0.76  fof(f99,plain,(
% 3.14/0.76    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 3.14/0.76    inference(cnf_transformation,[],[f45])).
% 3.14/0.76  fof(f45,plain,(
% 3.14/0.76    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.14/0.76    inference(ennf_transformation,[],[f10])).
% 3.14/0.76  fof(f10,axiom,(
% 3.14/0.76    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 3.14/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 3.14/0.76  fof(f118,plain,(
% 3.14/0.76    ( ! [X2,X1] : (k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 3.14/0.76    inference(equality_resolution,[],[f104])).
% 3.14/0.76  fof(f104,plain,(
% 3.14/0.76    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.14/0.76    inference(cnf_transformation,[],[f63])).
% 3.14/0.76  fof(f63,plain,(
% 3.14/0.76    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.14/0.76    inference(nnf_transformation,[],[f48])).
% 3.14/0.76  fof(f48,plain,(
% 3.14/0.76    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.14/0.76    inference(flattening,[],[f47])).
% 3.14/0.76  fof(f47,plain,(
% 3.14/0.76    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.14/0.76    inference(ennf_transformation,[],[f13])).
% 3.14/0.76  fof(f13,axiom,(
% 3.14/0.76    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.14/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 3.14/0.76  fof(f1081,plain,(
% 3.14/0.76    spl4_75 | ~spl4_7 | ~spl4_19),
% 3.14/0.76    inference(avatar_split_clause,[],[f307,f299,f159,f1078])).
% 3.14/0.76  fof(f1002,plain,(
% 3.14/0.76    spl4_68 | ~spl4_8 | ~spl4_30),
% 3.14/0.76    inference(avatar_split_clause,[],[f458,f388,f164,f999])).
% 3.14/0.76  fof(f458,plain,(
% 3.14/0.76    v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) | (~spl4_8 | ~spl4_30)),
% 3.14/0.76    inference(superposition,[],[f166,f390])).
% 3.14/0.76  fof(f965,plain,(
% 3.14/0.76    spl4_62 | ~spl4_24),
% 3.14/0.76    inference(avatar_split_clause,[],[f347,f340,f962])).
% 3.14/0.76  fof(f340,plain,(
% 3.14/0.76    spl4_24 <=> m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))),
% 3.14/0.76    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 3.14/0.76  fof(f347,plain,(
% 3.14/0.76    l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~spl4_24),
% 3.14/0.76    inference(unit_resulting_resolution,[],[f342,f91])).
% 3.14/0.76  fof(f91,plain,(
% 3.14/0.76    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | l1_pre_topc(g1_pre_topc(X0,X1))) )),
% 3.14/0.76    inference(cnf_transformation,[],[f40])).
% 3.14/0.76  fof(f40,plain,(
% 3.14/0.76    ! [X0,X1] : (l1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 3.14/0.76    inference(ennf_transformation,[],[f24])).
% 3.14/0.76  fof(f24,plain,(
% 3.14/0.76    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => l1_pre_topc(g1_pre_topc(X0,X1)))),
% 3.14/0.76    inference(pure_predicate_removal,[],[f16])).
% 3.14/0.76  fof(f16,axiom,(
% 3.14/0.76    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))))),
% 3.14/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_pre_topc)).
% 3.14/0.76  fof(f342,plain,(
% 3.14/0.76    m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) | ~spl4_24),
% 3.14/0.76    inference(avatar_component_clause,[],[f340])).
% 3.14/0.76  fof(f844,plain,(
% 3.14/0.76    spl4_57 | ~spl4_30 | ~spl4_45),
% 3.14/0.76    inference(avatar_split_clause,[],[f718,f667,f388,f841])).
% 3.14/0.76  fof(f718,plain,(
% 3.14/0.76    v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl4_30 | ~spl4_45)),
% 3.14/0.76    inference(forward_demodulation,[],[f668,f390])).
% 3.14/0.76  fof(f839,plain,(
% 3.14/0.76    spl4_56 | ~spl4_26 | ~spl4_37),
% 3.14/0.76    inference(avatar_split_clause,[],[f778,f551,f360,f836])).
% 3.14/0.76  fof(f778,plain,(
% 3.14/0.76    v1_xboole_0(sK2) | (~spl4_26 | ~spl4_37)),
% 3.14/0.76    inference(unit_resulting_resolution,[],[f362,f552,f90])).
% 3.14/0.76  fof(f552,plain,(
% 3.14/0.76    v1_xboole_0(u1_struct_0(sK1)) | ~spl4_37),
% 3.14/0.76    inference(avatar_component_clause,[],[f551])).
% 3.14/0.76  fof(f701,plain,(
% 3.14/0.76    u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != k1_relat_1(sK2) | u1_struct_0(sK0) != k1_relat_1(sK2) | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 3.14/0.76    introduced(theory_tautology_sat_conflict,[])).
% 3.14/0.76  fof(f700,plain,(
% 3.14/0.76    u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != k1_relat_1(sK2) | u1_struct_0(sK0) != k1_relat_1(sK2) | v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 3.14/0.76    introduced(theory_tautology_sat_conflict,[])).
% 3.14/0.76  fof(f697,plain,(
% 3.14/0.76    k1_xboole_0 != u1_struct_0(sK1) | k1_xboole_0 != u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 3.14/0.76    introduced(theory_tautology_sat_conflict,[])).
% 3.14/0.76  fof(f678,plain,(
% 3.14/0.76    ~spl4_45 | ~spl4_46 | spl4_47 | ~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_11 | ~spl4_14 | ~spl4_15 | ~spl4_24),
% 3.14/0.76    inference(avatar_split_clause,[],[f349,f340,f227,f221,f201,f149,f144,f139,f134,f129,f675,f671,f667])).
% 3.14/0.76  fof(f349,plain,(
% 3.14/0.76    v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_11 | ~spl4_14 | ~spl4_15 | ~spl4_24)),
% 3.14/0.76    inference(subsumption_resolution,[],[f277,f347])).
% 3.14/0.76  fof(f277,plain,(
% 3.14/0.76    v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_11 | ~spl4_14 | ~spl4_15)),
% 3.14/0.76    inference(subsumption_resolution,[],[f276,f131])).
% 3.14/0.76  fof(f276,plain,(
% 3.14/0.76    v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(sK0) | (~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_11 | ~spl4_14 | ~spl4_15)),
% 3.14/0.76    inference(subsumption_resolution,[],[f275,f136])).
% 3.14/0.76  fof(f275,plain,(
% 3.14/0.76    v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_11 | ~spl4_14 | ~spl4_15)),
% 3.14/0.76    inference(subsumption_resolution,[],[f274,f206])).
% 3.14/0.76  fof(f206,plain,(
% 3.14/0.76    v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl4_3 | ~spl4_4)),
% 3.14/0.76    inference(unit_resulting_resolution,[],[f141,f146,f83])).
% 3.14/0.76  fof(f83,plain,(
% 3.14/0.76    ( ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.14/0.76    inference(cnf_transformation,[],[f32])).
% 3.14/0.76  fof(f32,plain,(
% 3.14/0.76    ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.14/0.76    inference(flattening,[],[f31])).
% 3.14/0.76  fof(f31,plain,(
% 3.14/0.76    ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.14/0.76    inference(ennf_transformation,[],[f23])).
% 3.14/0.76  fof(f23,plain,(
% 3.14/0.76    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))),
% 3.14/0.76    inference(pure_predicate_removal,[],[f18])).
% 3.14/0.76  fof(f18,axiom,(
% 3.14/0.76    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 3.14/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_pre_topc)).
% 3.14/0.76  fof(f274,plain,(
% 3.14/0.76    v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl4_5 | ~spl4_11 | ~spl4_14 | ~spl4_15)),
% 3.14/0.76    inference(subsumption_resolution,[],[f273,f151])).
% 3.14/0.76  fof(f273,plain,(
% 3.14/0.76    v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl4_11 | ~spl4_14 | ~spl4_15)),
% 3.14/0.76    inference(subsumption_resolution,[],[f272,f229])).
% 3.14/0.76  fof(f272,plain,(
% 3.14/0.76    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl4_11 | ~spl4_14)),
% 3.14/0.76    inference(subsumption_resolution,[],[f271,f223])).
% 3.14/0.76  fof(f271,plain,(
% 3.14/0.76    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~spl4_11),
% 3.14/0.76    inference(resolution,[],[f121,f203])).
% 3.14/0.76  fof(f651,plain,(
% 3.14/0.76    ~spl4_41 | ~spl4_42 | spl4_43 | ~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_11 | ~spl4_14 | ~spl4_15 | ~spl4_23),
% 3.14/0.76    inference(avatar_split_clause,[],[f346,f335,f227,f221,f201,f149,f144,f139,f134,f129,f648,f644,f640])).
% 3.14/0.76  fof(f644,plain,(
% 3.14/0.76    spl4_42 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))),
% 3.14/0.76    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).
% 3.14/0.76  fof(f335,plain,(
% 3.14/0.76    spl4_23 <=> m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 3.14/0.76    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 3.14/0.76  fof(f346,plain,(
% 3.14/0.76    v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | (~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_11 | ~spl4_14 | ~spl4_15 | ~spl4_23)),
% 3.14/0.76    inference(subsumption_resolution,[],[f285,f344])).
% 3.14/0.76  fof(f344,plain,(
% 3.14/0.76    l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~spl4_23),
% 3.14/0.76    inference(unit_resulting_resolution,[],[f337,f91])).
% 3.14/0.76  fof(f337,plain,(
% 3.14/0.76    m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~spl4_23),
% 3.14/0.76    inference(avatar_component_clause,[],[f335])).
% 3.14/0.76  fof(f285,plain,(
% 3.14/0.76    v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_11 | ~spl4_14 | ~spl4_15)),
% 3.14/0.76    inference(subsumption_resolution,[],[f284,f205])).
% 3.14/0.76  fof(f205,plain,(
% 3.14/0.76    v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl4_1 | ~spl4_2)),
% 3.14/0.76    inference(unit_resulting_resolution,[],[f131,f136,f83])).
% 3.14/0.76  fof(f284,plain,(
% 3.14/0.76    v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_11 | ~spl4_14 | ~spl4_15)),
% 3.14/0.76    inference(subsumption_resolution,[],[f283,f141])).
% 3.14/0.76  fof(f283,plain,(
% 3.14/0.76    v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v2_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl4_4 | ~spl4_5 | ~spl4_11 | ~spl4_14 | ~spl4_15)),
% 3.14/0.76    inference(subsumption_resolution,[],[f282,f146])).
% 3.14/0.76  fof(f282,plain,(
% 3.14/0.76    v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl4_5 | ~spl4_11 | ~spl4_14 | ~spl4_15)),
% 3.14/0.76    inference(subsumption_resolution,[],[f281,f151])).
% 3.14/0.76  fof(f281,plain,(
% 3.14/0.76    v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl4_11 | ~spl4_14 | ~spl4_15)),
% 3.14/0.76    inference(subsumption_resolution,[],[f280,f229])).
% 3.14/0.76  fof(f280,plain,(
% 3.14/0.76    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl4_11 | ~spl4_14)),
% 3.14/0.76    inference(subsumption_resolution,[],[f279,f223])).
% 3.14/0.76  fof(f279,plain,(
% 3.14/0.76    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~spl4_11),
% 3.14/0.76    inference(resolution,[],[f123,f203])).
% 3.14/0.76  fof(f563,plain,(
% 3.14/0.76    spl4_38 | spl4_39 | ~spl4_11 | ~spl4_15),
% 3.14/0.76    inference(avatar_split_clause,[],[f264,f227,f201,f560,f556])).
% 3.14/0.76  fof(f556,plain,(
% 3.14/0.76    spl4_38 <=> k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 3.14/0.76    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).
% 3.14/0.76  fof(f264,plain,(
% 3.14/0.76    u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK2) | k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl4_11 | ~spl4_15)),
% 3.14/0.76    inference(forward_demodulation,[],[f263,f237])).
% 3.14/0.76  fof(f237,plain,(
% 3.14/0.76    k1_relat_1(sK2) = k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2) | ~spl4_15),
% 3.14/0.76    inference(unit_resulting_resolution,[],[f229,f99])).
% 3.14/0.76  fof(f263,plain,(
% 3.14/0.76    u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2) | k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl4_11 | ~spl4_15)),
% 3.14/0.76    inference(subsumption_resolution,[],[f259,f229])).
% 3.14/0.76  fof(f259,plain,(
% 3.14/0.76    u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2) | k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~spl4_11),
% 3.14/0.76    inference(resolution,[],[f101,f203])).
% 3.14/0.76  fof(f101,plain,(
% 3.14/0.76    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) = X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.14/0.76    inference(cnf_transformation,[],[f63])).
% 3.14/0.76  fof(f440,plain,(
% 3.14/0.76    spl4_32 | ~spl4_15),
% 3.14/0.76    inference(avatar_split_clause,[],[f250,f227,f437])).
% 3.14/0.76  fof(f250,plain,(
% 3.14/0.76    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~spl4_15),
% 3.14/0.76    inference(unit_resulting_resolution,[],[f113,f229,f107])).
% 3.14/0.76  fof(f107,plain,(
% 3.14/0.76    ( ! [X2,X0,X3,X1] : (~r1_tarski(k1_relat_1(X3),X1) | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) )),
% 3.14/0.76    inference(cnf_transformation,[],[f50])).
% 3.14/0.76  fof(f50,plain,(
% 3.14/0.76    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 3.14/0.76    inference(flattening,[],[f49])).
% 3.14/0.76  fof(f49,plain,(
% 3.14/0.76    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 3.14/0.76    inference(ennf_transformation,[],[f11])).
% 3.14/0.76  fof(f11,axiom,(
% 3.14/0.76    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => (r1_tarski(k1_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))),
% 3.14/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).
% 3.14/0.76  fof(f113,plain,(
% 3.14/0.76    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.14/0.76    inference(equality_resolution,[],[f95])).
% 3.14/0.76  fof(f95,plain,(
% 3.14/0.76    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.14/0.76    inference(cnf_transformation,[],[f62])).
% 3.14/0.76  fof(f62,plain,(
% 3.14/0.76    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.14/0.76    inference(flattening,[],[f61])).
% 3.14/0.76  fof(f61,plain,(
% 3.14/0.76    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.14/0.76    inference(nnf_transformation,[],[f2])).
% 3.14/0.76  fof(f2,axiom,(
% 3.14/0.76    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.14/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 3.14/0.76  fof(f391,plain,(
% 3.14/0.76    spl4_29 | spl4_30 | ~spl4_8 | ~spl4_9),
% 3.14/0.76    inference(avatar_split_clause,[],[f262,f170,f164,f388,f384])).
% 3.14/0.76  fof(f262,plain,(
% 3.14/0.76    u1_struct_0(sK0) = k1_relat_1(sK2) | k1_xboole_0 = u1_struct_0(sK1) | (~spl4_8 | ~spl4_9)),
% 3.14/0.76    inference(forward_demodulation,[],[f261,f236])).
% 3.14/0.76  fof(f236,plain,(
% 3.14/0.76    k1_relat_1(sK2) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | ~spl4_9),
% 3.14/0.76    inference(unit_resulting_resolution,[],[f172,f99])).
% 3.14/0.76  fof(f261,plain,(
% 3.14/0.76    u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | k1_xboole_0 = u1_struct_0(sK1) | (~spl4_8 | ~spl4_9)),
% 3.14/0.76    inference(subsumption_resolution,[],[f258,f172])).
% 3.14/0.76  fof(f258,plain,(
% 3.14/0.76    u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | k1_xboole_0 = u1_struct_0(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~spl4_8),
% 3.14/0.76    inference(resolution,[],[f101,f166])).
% 3.14/0.76  fof(f370,plain,(
% 3.14/0.76    spl4_27 | ~spl4_23),
% 3.14/0.76    inference(avatar_split_clause,[],[f344,f335,f367])).
% 3.14/0.76  fof(f363,plain,(
% 3.14/0.76    spl4_26 | ~spl4_9),
% 3.14/0.76    inference(avatar_split_clause,[],[f249,f170,f360])).
% 3.14/0.76  fof(f249,plain,(
% 3.14/0.76    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))) | ~spl4_9),
% 3.14/0.76    inference(unit_resulting_resolution,[],[f113,f172,f107])).
% 3.14/0.76  fof(f343,plain,(
% 3.14/0.76    spl4_24 | ~spl4_4),
% 3.14/0.76    inference(avatar_split_clause,[],[f183,f144,f340])).
% 3.14/0.76  fof(f183,plain,(
% 3.14/0.76    m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) | ~spl4_4),
% 3.14/0.76    inference(unit_resulting_resolution,[],[f146,f82])).
% 3.14/0.76  fof(f82,plain,(
% 3.14/0.76    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 3.14/0.76    inference(cnf_transformation,[],[f30])).
% 3.14/0.76  fof(f30,plain,(
% 3.14/0.76    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.14/0.76    inference(ennf_transformation,[],[f17])).
% 3.14/0.76  fof(f17,axiom,(
% 3.14/0.76    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.14/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).
% 3.14/0.76  fof(f338,plain,(
% 3.14/0.76    spl4_23 | ~spl4_2),
% 3.14/0.76    inference(avatar_split_clause,[],[f182,f134,f335])).
% 3.14/0.76  fof(f182,plain,(
% 3.14/0.76    m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~spl4_2),
% 3.14/0.76    inference(unit_resulting_resolution,[],[f136,f82])).
% 3.14/0.76  fof(f324,plain,(
% 3.14/0.76    spl4_21 | ~spl4_3 | ~spl4_4),
% 3.14/0.76    inference(avatar_split_clause,[],[f206,f144,f139,f321])).
% 3.14/0.76  fof(f319,plain,(
% 3.14/0.76    spl4_20 | ~spl4_1 | ~spl4_2),
% 3.14/0.76    inference(avatar_split_clause,[],[f205,f134,f129,f316])).
% 3.14/0.76  fof(f302,plain,(
% 3.14/0.76    spl4_19 | ~spl4_7),
% 3.14/0.76    inference(avatar_split_clause,[],[f208,f159,f299])).
% 3.14/0.76  fof(f208,plain,(
% 3.14/0.76    v1_xboole_0(k6_partfun1(k1_xboole_0)) | ~spl4_7),
% 3.14/0.76    inference(unit_resulting_resolution,[],[f161,f80,f90])).
% 3.14/0.76  fof(f292,plain,(
% 3.14/0.76    spl4_18 | ~spl4_9),
% 3.14/0.76    inference(avatar_split_clause,[],[f195,f170,f289])).
% 3.14/0.76  fof(f195,plain,(
% 3.14/0.76    v4_relat_1(sK2,u1_struct_0(sK0)) | ~spl4_9),
% 3.14/0.76    inference(unit_resulting_resolution,[],[f172,f100])).
% 3.14/0.76  fof(f247,plain,(
% 3.14/0.76    spl4_16 | ~spl4_7),
% 3.14/0.76    inference(avatar_split_clause,[],[f168,f159,f244])).
% 3.14/0.76  fof(f168,plain,(
% 3.14/0.76    v1_funct_1(k1_xboole_0) | ~spl4_7),
% 3.14/0.76    inference(unit_resulting_resolution,[],[f161,f81])).
% 3.14/0.76  fof(f81,plain,(
% 3.14/0.76    ( ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0)) )),
% 3.14/0.76    inference(cnf_transformation,[],[f29])).
% 3.14/0.76  fof(f29,plain,(
% 3.14/0.76    ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0))),
% 3.14/0.76    inference(ennf_transformation,[],[f6])).
% 3.14/0.76  fof(f6,axiom,(
% 3.14/0.76    ! [X0] : (v1_xboole_0(X0) => v1_funct_1(X0))),
% 3.14/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_1)).
% 3.14/0.76  fof(f230,plain,(
% 3.14/0.76    spl4_15),
% 3.14/0.76    inference(avatar_split_clause,[],[f124,f227])).
% 3.14/0.76  fof(f124,plain,(
% 3.14/0.76    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))),
% 3.14/0.76    inference(forward_demodulation,[],[f73,f74])).
% 3.14/0.76  fof(f74,plain,(
% 3.14/0.76    sK2 = sK3),
% 3.14/0.76    inference(cnf_transformation,[],[f57])).
% 3.14/0.76  fof(f57,plain,(
% 3.14/0.76    ((((~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,sK1)) & (v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,sK1)) & sK2 = sK3 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) & v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 3.14/0.76    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f52,f56,f55,f54,f53])).
% 3.14/0.76  fof(f53,plain,(
% 3.14/0.76    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,sK0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,sK0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 3.14/0.76    introduced(choice_axiom,[])).
% 3.14/0.76  fof(f54,plain,(
% 3.14/0.76    ? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,sK0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,sK0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) => (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(X2,sK0,sK1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(X2,sK0,sK1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1))),
% 3.14/0.76    introduced(choice_axiom,[])).
% 3.14/0.76  fof(f55,plain,(
% 3.14/0.76    ? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(X2,sK0,sK1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(X2,sK0,sK1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) => (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,sK1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,sK1)) & sK2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2))),
% 3.14/0.76    introduced(choice_axiom,[])).
% 3.14/0.76  fof(f56,plain,(
% 3.14/0.76    ? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,sK1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,sK1)) & sK2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) & v1_funct_1(X3)) => ((~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,sK1)) & (v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,sK1)) & sK2 = sK3 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) & v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) & v1_funct_1(sK3))),
% 3.14/0.76    introduced(choice_axiom,[])).
% 3.14/0.76  fof(f52,plain,(
% 3.14/0.76    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.14/0.76    inference(flattening,[],[f51])).
% 3.14/0.76  fof(f51,plain,(
% 3.14/0.76    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1))) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.14/0.76    inference(nnf_transformation,[],[f28])).
% 3.14/0.76  fof(f28,plain,(
% 3.14/0.76    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.14/0.76    inference(flattening,[],[f27])).
% 3.14/0.76  fof(f27,plain,(
% 3.14/0.76    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & X2 = X3) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 3.14/0.76    inference(ennf_transformation,[],[f22])).
% 3.14/0.76  fof(f22,negated_conjecture,(
% 3.14/0.76    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 3.14/0.76    inference(negated_conjecture,[],[f21])).
% 3.14/0.76  fof(f21,conjecture,(
% 3.14/0.76    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 3.14/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_pre_topc)).
% 3.14/0.76  fof(f73,plain,(
% 3.14/0.76    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))),
% 3.14/0.76    inference(cnf_transformation,[],[f57])).
% 3.14/0.76  fof(f225,plain,(
% 3.14/0.76    ~spl4_12 | ~spl4_13),
% 3.14/0.76    inference(avatar_split_clause,[],[f76,f215,f211])).
% 3.14/0.76  fof(f76,plain,(
% 3.14/0.76    ~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,sK1)),
% 3.14/0.76    inference(cnf_transformation,[],[f57])).
% 3.22/0.77  fof(f218,plain,(
% 3.22/0.77    spl4_12 | spl4_13),
% 3.22/0.77    inference(avatar_split_clause,[],[f75,f215,f211])).
% 3.22/0.77  fof(f75,plain,(
% 3.22/0.77    v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,sK1)),
% 3.22/0.77    inference(cnf_transformation,[],[f57])).
% 3.22/0.77  fof(f204,plain,(
% 3.22/0.77    spl4_11),
% 3.22/0.77    inference(avatar_split_clause,[],[f125,f201])).
% 3.22/0.77  fof(f125,plain,(
% 3.22/0.77    v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 3.22/0.77    inference(forward_demodulation,[],[f72,f74])).
% 3.22/0.77  fof(f72,plain,(
% 3.22/0.77    v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 3.22/0.77    inference(cnf_transformation,[],[f57])).
% 3.22/0.77  fof(f191,plain,(
% 3.22/0.77    spl4_10 | ~spl4_9),
% 3.22/0.77    inference(avatar_split_clause,[],[f177,f170,f188])).
% 3.22/0.77  fof(f177,plain,(
% 3.22/0.77    v1_relat_1(sK2) | ~spl4_9),
% 3.22/0.77    inference(unit_resulting_resolution,[],[f172,f98])).
% 3.22/0.77  fof(f173,plain,(
% 3.22/0.77    spl4_9),
% 3.22/0.77    inference(avatar_split_clause,[],[f70,f170])).
% 3.22/0.77  fof(f70,plain,(
% 3.22/0.77    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 3.22/0.77    inference(cnf_transformation,[],[f57])).
% 3.22/0.77  fof(f167,plain,(
% 3.22/0.77    spl4_8),
% 3.22/0.77    inference(avatar_split_clause,[],[f69,f164])).
% 3.22/0.77  fof(f69,plain,(
% 3.22/0.77    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 3.22/0.77    inference(cnf_transformation,[],[f57])).
% 3.22/0.77  fof(f162,plain,(
% 3.22/0.77    spl4_7),
% 3.22/0.77    inference(avatar_split_clause,[],[f77,f159])).
% 3.22/0.77  fof(f77,plain,(
% 3.22/0.77    v1_xboole_0(k1_xboole_0)),
% 3.22/0.77    inference(cnf_transformation,[],[f1])).
% 3.22/0.77  fof(f1,axiom,(
% 3.22/0.77    v1_xboole_0(k1_xboole_0)),
% 3.22/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 3.22/0.77  fof(f157,plain,(
% 3.22/0.77    spl4_6),
% 3.22/0.77    inference(avatar_split_clause,[],[f74,f154])).
% 3.22/0.77  fof(f152,plain,(
% 3.22/0.77    spl4_5),
% 3.22/0.77    inference(avatar_split_clause,[],[f126,f149])).
% 3.22/0.77  fof(f126,plain,(
% 3.22/0.77    v1_funct_1(sK2)),
% 3.22/0.77    inference(forward_demodulation,[],[f71,f74])).
% 3.22/0.77  fof(f71,plain,(
% 3.22/0.77    v1_funct_1(sK3)),
% 3.22/0.77    inference(cnf_transformation,[],[f57])).
% 3.22/0.77  fof(f147,plain,(
% 3.22/0.77    spl4_4),
% 3.22/0.77    inference(avatar_split_clause,[],[f67,f144])).
% 3.22/0.77  fof(f67,plain,(
% 3.22/0.77    l1_pre_topc(sK1)),
% 3.22/0.77    inference(cnf_transformation,[],[f57])).
% 3.22/0.77  fof(f142,plain,(
% 3.22/0.77    spl4_3),
% 3.22/0.77    inference(avatar_split_clause,[],[f66,f139])).
% 3.22/0.77  fof(f66,plain,(
% 3.22/0.77    v2_pre_topc(sK1)),
% 3.22/0.77    inference(cnf_transformation,[],[f57])).
% 3.22/0.77  fof(f137,plain,(
% 3.22/0.77    spl4_2),
% 3.22/0.77    inference(avatar_split_clause,[],[f65,f134])).
% 3.22/0.77  fof(f65,plain,(
% 3.22/0.77    l1_pre_topc(sK0)),
% 3.22/0.77    inference(cnf_transformation,[],[f57])).
% 3.22/0.77  fof(f132,plain,(
% 3.22/0.77    spl4_1),
% 3.22/0.77    inference(avatar_split_clause,[],[f64,f129])).
% 3.22/0.77  fof(f64,plain,(
% 3.22/0.77    v2_pre_topc(sK0)),
% 3.22/0.77    inference(cnf_transformation,[],[f57])).
% 3.22/0.77  % SZS output end Proof for theBenchmark
% 3.22/0.77  % (6128)------------------------------
% 3.22/0.77  % (6128)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.22/0.77  % (6128)Termination reason: Refutation
% 3.22/0.77  
% 3.22/0.77  % (6128)Memory used [KB]: 12665
% 3.22/0.77  % (6128)Time elapsed: 0.296 s
% 3.22/0.77  % (6128)------------------------------
% 3.22/0.77  % (6128)------------------------------
% 3.22/0.77  % (6100)Success in time 0.41 s
%------------------------------------------------------------------------------
