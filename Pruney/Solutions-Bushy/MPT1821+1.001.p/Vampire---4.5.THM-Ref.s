%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1821+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:39 EST 2020

% Result     : Theorem 1.51s
% Output     : Refutation 1.51s
% Verified   : 
% Statistics : Number of formulae       :  251 ( 791 expanded)
%              Number of leaves         :   56 ( 390 expanded)
%              Depth                    :    9
%              Number of atoms          : 1676 (9018 expanded)
%              Number of equality atoms :   10 ( 204 expanded)
%              Maximal formula depth    :   30 (   7 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1243,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f110,f116,f120,f124,f128,f132,f136,f140,f144,f148,f152,f156,f160,f164,f168,f175,f179,f242,f244,f246,f248,f333,f335,f337,f341,f456,f481,f858,f868,f881,f886,f912,f914,f916,f918,f954,f1043,f1045,f1049,f1070,f1081,f1098,f1109,f1198,f1213,f1220,f1230,f1235,f1240,f1242])).

fof(f1242,plain,
    ( spl7_1
    | spl7_20
    | ~ spl7_2
    | ~ spl7_21
    | spl7_22
    | ~ spl7_23
    | spl7_24
    | ~ spl7_25
    | ~ spl7_26
    | ~ spl7_133 ),
    inference(avatar_split_clause,[],[f1241,f852,f238,f235,f232,f229,f226,f223,f108,f220,f105])).

fof(f105,plain,
    ( spl7_1
  <=> r3_tsep_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f220,plain,
    ( spl7_20
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f108,plain,
    ( spl7_2
  <=> r1_tsep_1(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f223,plain,
    ( spl7_21
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).

fof(f226,plain,
    ( spl7_22
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).

fof(f229,plain,
    ( spl7_23
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).

fof(f232,plain,
    ( spl7_24
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).

fof(f235,plain,
    ( spl7_25
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).

fof(f238,plain,
    ( spl7_26
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).

fof(f852,plain,
    ( spl7_133
  <=> v2_struct_0(sK5(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_133])])).

fof(f1241,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ r1_tsep_1(sK1,sK2)
    | v2_struct_0(sK0)
    | r3_tsep_1(sK0,sK1,sK2)
    | ~ spl7_133 ),
    inference(resolution,[],[f853,f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(sK5(X0,X1,X2))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ r1_tsep_1(X1,X2)
      | v2_struct_0(X0)
      | r3_tsep_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_tsep_1(X0,X1,X2)
              <=> ( ! [X3] :
                      ( ! [X4] :
                          ( ( m1_subset_1(k2_tmap_1(X0,X3,X4,k1_tsep_1(X0,X1,X2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                            & v5_pre_topc(k2_tmap_1(X0,X3,X4,k1_tsep_1(X0,X1,X2)),k1_tsep_1(X0,X1,X2),X3)
                            & v1_funct_2(k2_tmap_1(X0,X3,X4,k1_tsep_1(X0,X1,X2)),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                            & v1_funct_1(k2_tmap_1(X0,X3,X4,k1_tsep_1(X0,X1,X2))) )
                          | ~ m1_subset_1(k2_tmap_1(X0,X3,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                          | ~ v5_pre_topc(k2_tmap_1(X0,X3,X4,X2),X2,X3)
                          | ~ v1_funct_2(k2_tmap_1(X0,X3,X4,X2),u1_struct_0(X2),u1_struct_0(X3))
                          | ~ v1_funct_1(k2_tmap_1(X0,X3,X4,X2))
                          | ~ m1_subset_1(k2_tmap_1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                          | ~ v5_pre_topc(k2_tmap_1(X0,X3,X4,X1),X1,X3)
                          | ~ v1_funct_2(k2_tmap_1(X0,X3,X4,X1),u1_struct_0(X1),u1_struct_0(X3))
                          | ~ v1_funct_1(k2_tmap_1(X0,X3,X4,X1))
                          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
                          | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3))
                          | ~ v1_funct_1(X4) )
                      | ~ l1_pre_topc(X3)
                      | ~ v2_pre_topc(X3)
                      | v2_struct_0(X3) )
                  & r1_tsep_1(X1,X2) ) )
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
              ( ( r3_tsep_1(X0,X1,X2)
              <=> ( ! [X3] :
                      ( ! [X4] :
                          ( ( m1_subset_1(k2_tmap_1(X0,X3,X4,k1_tsep_1(X0,X1,X2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                            & v5_pre_topc(k2_tmap_1(X0,X3,X4,k1_tsep_1(X0,X1,X2)),k1_tsep_1(X0,X1,X2),X3)
                            & v1_funct_2(k2_tmap_1(X0,X3,X4,k1_tsep_1(X0,X1,X2)),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                            & v1_funct_1(k2_tmap_1(X0,X3,X4,k1_tsep_1(X0,X1,X2))) )
                          | ~ m1_subset_1(k2_tmap_1(X0,X3,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                          | ~ v5_pre_topc(k2_tmap_1(X0,X3,X4,X2),X2,X3)
                          | ~ v1_funct_2(k2_tmap_1(X0,X3,X4,X2),u1_struct_0(X2),u1_struct_0(X3))
                          | ~ v1_funct_1(k2_tmap_1(X0,X3,X4,X2))
                          | ~ m1_subset_1(k2_tmap_1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                          | ~ v5_pre_topc(k2_tmap_1(X0,X3,X4,X1),X1,X3)
                          | ~ v1_funct_2(k2_tmap_1(X0,X3,X4,X1),u1_struct_0(X1),u1_struct_0(X3))
                          | ~ v1_funct_1(k2_tmap_1(X0,X3,X4,X1))
                          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
                          | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3))
                          | ~ v1_funct_1(X4) )
                      | ~ l1_pre_topc(X3)
                      | ~ v2_pre_topc(X3)
                      | v2_struct_0(X3) )
                  & r1_tsep_1(X1,X2) ) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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
             => ( r3_tsep_1(X0,X1,X2)
              <=> ( ! [X3] :
                      ( ( l1_pre_topc(X3)
                        & v2_pre_topc(X3)
                        & ~ v2_struct_0(X3) )
                     => ! [X4] :
                          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
                            & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3))
                            & v1_funct_1(X4) )
                         => ( ( m1_subset_1(k2_tmap_1(X0,X3,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                              & v5_pre_topc(k2_tmap_1(X0,X3,X4,X2),X2,X3)
                              & v1_funct_2(k2_tmap_1(X0,X3,X4,X2),u1_struct_0(X2),u1_struct_0(X3))
                              & v1_funct_1(k2_tmap_1(X0,X3,X4,X2))
                              & m1_subset_1(k2_tmap_1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                              & v5_pre_topc(k2_tmap_1(X0,X3,X4,X1),X1,X3)
                              & v1_funct_2(k2_tmap_1(X0,X3,X4,X1),u1_struct_0(X1),u1_struct_0(X3))
                              & v1_funct_1(k2_tmap_1(X0,X3,X4,X1)) )
                           => ( m1_subset_1(k2_tmap_1(X0,X3,X4,k1_tsep_1(X0,X1,X2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                              & v5_pre_topc(k2_tmap_1(X0,X3,X4,k1_tsep_1(X0,X1,X2)),k1_tsep_1(X0,X1,X2),X3)
                              & v1_funct_2(k2_tmap_1(X0,X3,X4,k1_tsep_1(X0,X1,X2)),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                              & v1_funct_1(k2_tmap_1(X0,X3,X4,k1_tsep_1(X0,X1,X2))) ) ) ) )
                  & r1_tsep_1(X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t136_tmap_1)).

fof(f853,plain,
    ( v2_struct_0(sK5(sK0,sK1,sK2))
    | ~ spl7_133 ),
    inference(avatar_component_clause,[],[f852])).

fof(f1240,plain,
    ( spl7_1
    | spl7_20
    | ~ spl7_2
    | ~ spl7_21
    | spl7_22
    | ~ spl7_23
    | spl7_24
    | ~ spl7_25
    | ~ spl7_26
    | spl7_143 ),
    inference(avatar_split_clause,[],[f1237,f949,f238,f235,f232,f229,f226,f223,f108,f220,f105])).

fof(f949,plain,
    ( spl7_143
  <=> v1_funct_2(k2_tmap_1(sK0,sK5(sK0,sK1,sK2),sK6(sK0,sK1,sK2),sK1),u1_struct_0(sK1),u1_struct_0(sK5(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_143])])).

fof(f1237,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ r1_tsep_1(sK1,sK2)
    | v2_struct_0(sK0)
    | r3_tsep_1(sK0,sK1,sK2)
    | spl7_143 ),
    inference(resolution,[],[f950,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_tmap_1(X0,sK5(X0,X1,X2),sK6(X0,X1,X2),X1),u1_struct_0(X1),u1_struct_0(sK5(X0,X1,X2)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ r1_tsep_1(X1,X2)
      | v2_struct_0(X0)
      | r3_tsep_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f950,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,sK5(sK0,sK1,sK2),sK6(sK0,sK1,sK2),sK1),u1_struct_0(sK1),u1_struct_0(sK5(sK0,sK1,sK2)))
    | spl7_143 ),
    inference(avatar_component_clause,[],[f949])).

fof(f1235,plain,
    ( spl7_1
    | spl7_20
    | ~ spl7_2
    | ~ spl7_21
    | spl7_22
    | ~ spl7_23
    | spl7_24
    | ~ spl7_25
    | ~ spl7_26
    | spl7_140 ),
    inference(avatar_split_clause,[],[f1232,f939,f238,f235,f232,f229,f226,f223,f108,f220,f105])).

fof(f939,plain,
    ( spl7_140
  <=> v1_funct_2(k2_tmap_1(sK0,sK5(sK0,sK1,sK2),sK6(sK0,sK1,sK2),sK2),u1_struct_0(sK2),u1_struct_0(sK5(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_140])])).

fof(f1232,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ r1_tsep_1(sK1,sK2)
    | v2_struct_0(sK0)
    | r3_tsep_1(sK0,sK1,sK2)
    | spl7_140 ),
    inference(resolution,[],[f940,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_tmap_1(X0,sK5(X0,X1,X2),sK6(X0,X1,X2),X2),u1_struct_0(X2),u1_struct_0(sK5(X0,X1,X2)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ r1_tsep_1(X1,X2)
      | v2_struct_0(X0)
      | r3_tsep_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f940,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,sK5(sK0,sK1,sK2),sK6(sK0,sK1,sK2),sK2),u1_struct_0(sK2),u1_struct_0(sK5(sK0,sK1,sK2)))
    | spl7_140 ),
    inference(avatar_component_clause,[],[f939])).

fof(f1230,plain,
    ( spl7_1
    | spl7_20
    | ~ spl7_2
    | ~ spl7_21
    | spl7_22
    | ~ spl7_23
    | spl7_24
    | ~ spl7_25
    | ~ spl7_26
    | spl7_142 ),
    inference(avatar_split_clause,[],[f1228,f946,f238,f235,f232,f229,f226,f223,f108,f220,f105])).

fof(f946,plain,
    ( spl7_142
  <=> v5_pre_topc(k2_tmap_1(sK0,sK5(sK0,sK1,sK2),sK6(sK0,sK1,sK2),sK1),sK1,sK5(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_142])])).

fof(f1228,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ r1_tsep_1(sK1,sK2)
    | v2_struct_0(sK0)
    | r3_tsep_1(sK0,sK1,sK2)
    | spl7_142 ),
    inference(resolution,[],[f947,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(k2_tmap_1(X0,sK5(X0,X1,X2),sK6(X0,X1,X2),X1),X1,sK5(X0,X1,X2))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ r1_tsep_1(X1,X2)
      | v2_struct_0(X0)
      | r3_tsep_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f947,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK0,sK5(sK0,sK1,sK2),sK6(sK0,sK1,sK2),sK1),sK1,sK5(sK0,sK1,sK2))
    | spl7_142 ),
    inference(avatar_component_clause,[],[f946])).

fof(f1220,plain,
    ( spl7_1
    | spl7_20
    | ~ spl7_2
    | ~ spl7_21
    | spl7_22
    | ~ spl7_23
    | spl7_24
    | ~ spl7_25
    | ~ spl7_26
    | spl7_139 ),
    inference(avatar_split_clause,[],[f1218,f936,f238,f235,f232,f229,f226,f223,f108,f220,f105])).

fof(f936,plain,
    ( spl7_139
  <=> v5_pre_topc(k2_tmap_1(sK0,sK5(sK0,sK1,sK2),sK6(sK0,sK1,sK2),sK2),sK2,sK5(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_139])])).

fof(f1218,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ r1_tsep_1(sK1,sK2)
    | v2_struct_0(sK0)
    | r3_tsep_1(sK0,sK1,sK2)
    | spl7_139 ),
    inference(resolution,[],[f937,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(k2_tmap_1(X0,sK5(X0,X1,X2),sK6(X0,X1,X2),X2),X2,sK5(X0,X1,X2))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ r1_tsep_1(X1,X2)
      | v2_struct_0(X0)
      | r3_tsep_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f937,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK0,sK5(sK0,sK1,sK2),sK6(sK0,sK1,sK2),sK2),sK2,sK5(sK0,sK1,sK2))
    | spl7_139 ),
    inference(avatar_component_clause,[],[f936])).

fof(f1213,plain,
    ( spl7_1
    | spl7_20
    | ~ spl7_2
    | ~ spl7_21
    | spl7_22
    | ~ spl7_23
    | spl7_24
    | ~ spl7_25
    | ~ spl7_26
    | spl7_127 ),
    inference(avatar_split_clause,[],[f1212,f834,f238,f235,f232,f229,f226,f223,f108,f220,f105])).

fof(f834,plain,
    ( spl7_127
  <=> m1_subset_1(sK6(sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK5(sK0,sK1,sK2))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_127])])).

fof(f1212,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ r1_tsep_1(sK1,sK2)
    | v2_struct_0(sK0)
    | r3_tsep_1(sK0,sK1,sK2)
    | spl7_127 ),
    inference(resolution,[],[f835,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK5(X0,X1,X2)))))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ r1_tsep_1(X1,X2)
      | v2_struct_0(X0)
      | r3_tsep_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f835,plain,
    ( ~ m1_subset_1(sK6(sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK5(sK0,sK1,sK2)))))
    | spl7_127 ),
    inference(avatar_component_clause,[],[f834])).

fof(f1198,plain,
    ( spl7_1
    | spl7_20
    | ~ spl7_2
    | ~ spl7_21
    | spl7_22
    | ~ spl7_23
    | spl7_24
    | ~ spl7_25
    | ~ spl7_26
    | spl7_144 ),
    inference(avatar_split_clause,[],[f1195,f952,f238,f235,f232,f229,f226,f223,f108,f220,f105])).

fof(f952,plain,
    ( spl7_144
  <=> v1_funct_1(k2_tmap_1(sK0,sK5(sK0,sK1,sK2),sK6(sK0,sK1,sK2),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_144])])).

fof(f1195,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ r1_tsep_1(sK1,sK2)
    | v2_struct_0(sK0)
    | r3_tsep_1(sK0,sK1,sK2)
    | spl7_144 ),
    inference(resolution,[],[f953,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(k2_tmap_1(X0,sK5(X0,X1,X2),sK6(X0,X1,X2),X1))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ r1_tsep_1(X1,X2)
      | v2_struct_0(X0)
      | r3_tsep_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f953,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK0,sK5(sK0,sK1,sK2),sK6(sK0,sK1,sK2),sK1))
    | spl7_144 ),
    inference(avatar_component_clause,[],[f952])).

fof(f1109,plain,
    ( ~ spl7_4
    | ~ spl7_3
    | ~ spl7_15
    | ~ spl7_16
    | ~ spl7_14
    | ~ spl7_13
    | ~ spl7_12
    | ~ spl7_11
    | ~ spl7_10
    | ~ spl7_9
    | ~ spl7_8
    | ~ spl7_7
    | spl7_5
    | spl7_17
    | ~ spl7_6
    | ~ spl7_18 ),
    inference(avatar_split_clause,[],[f1104,f177,f126,f171,f122,f130,f134,f138,f142,f146,f150,f154,f158,f166,f162,f113,f118])).

fof(f118,plain,
    ( spl7_4
  <=> v2_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f113,plain,
    ( spl7_3
  <=> l1_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f162,plain,
    ( spl7_15
  <=> v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f166,plain,
    ( spl7_16
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f158,plain,
    ( spl7_14
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f154,plain,
    ( spl7_13
  <=> v1_funct_1(k2_tmap_1(sK0,sK3,sK4,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f150,plain,
    ( spl7_12
  <=> v1_funct_2(k2_tmap_1(sK0,sK3,sK4,sK1),u1_struct_0(sK1),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f146,plain,
    ( spl7_11
  <=> v5_pre_topc(k2_tmap_1(sK0,sK3,sK4,sK1),sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f142,plain,
    ( spl7_10
  <=> m1_subset_1(k2_tmap_1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f138,plain,
    ( spl7_9
  <=> v1_funct_1(k2_tmap_1(sK0,sK3,sK4,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f134,plain,
    ( spl7_8
  <=> v1_funct_2(k2_tmap_1(sK0,sK3,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f130,plain,
    ( spl7_7
  <=> v5_pre_topc(k2_tmap_1(sK0,sK3,sK4,sK2),sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f122,plain,
    ( spl7_5
  <=> v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f171,plain,
    ( spl7_17
  <=> v5_pre_topc(sK4,sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f126,plain,
    ( spl7_6
  <=> m1_subset_1(k2_tmap_1(sK0,sK3,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f177,plain,
    ( spl7_18
  <=> ! [X3,X4] :
        ( v2_struct_0(X3)
        | v5_pre_topc(X4,sK0,X3)
        | ~ m1_subset_1(k2_tmap_1(sK0,X3,X4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X3))))
        | ~ v5_pre_topc(k2_tmap_1(sK0,X3,X4,sK2),sK2,X3)
        | ~ v1_funct_2(k2_tmap_1(sK0,X3,X4,sK2),u1_struct_0(sK2),u1_struct_0(X3))
        | ~ v1_funct_1(k2_tmap_1(sK0,X3,X4,sK2))
        | ~ m1_subset_1(k2_tmap_1(sK0,X3,X4,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X3))))
        | ~ v5_pre_topc(k2_tmap_1(sK0,X3,X4,sK1),sK1,X3)
        | ~ v1_funct_2(k2_tmap_1(sK0,X3,X4,sK1),u1_struct_0(sK1),u1_struct_0(X3))
        | ~ v1_funct_1(k2_tmap_1(sK0,X3,X4,sK1))
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X3))))
        | ~ v1_funct_1(X4)
        | ~ v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X3))
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f1104,plain,
    ( v5_pre_topc(sK4,sK0,sK3)
    | v2_struct_0(sK3)
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK3,sK4,sK2),sK2,sK3)
    | ~ v1_funct_2(k2_tmap_1(sK0,sK3,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK3,sK4,sK2))
    | ~ m1_subset_1(k2_tmap_1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK3))))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK3,sK4,sK1),sK1,sK3)
    | ~ v1_funct_2(k2_tmap_1(sK0,sK3,sK4,sK1),u1_struct_0(sK1),u1_struct_0(sK3))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK3,sK4,sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK3))))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK3))
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | ~ spl7_6
    | ~ spl7_18 ),
    inference(resolution,[],[f178,f127])).

fof(f127,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK3,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f126])).

fof(f178,plain,
    ( ! [X4,X3] :
        ( ~ m1_subset_1(k2_tmap_1(sK0,X3,X4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X3))))
        | v5_pre_topc(X4,sK0,X3)
        | v2_struct_0(X3)
        | ~ v5_pre_topc(k2_tmap_1(sK0,X3,X4,sK2),sK2,X3)
        | ~ v1_funct_2(k2_tmap_1(sK0,X3,X4,sK2),u1_struct_0(sK2),u1_struct_0(X3))
        | ~ v1_funct_1(k2_tmap_1(sK0,X3,X4,sK2))
        | ~ m1_subset_1(k2_tmap_1(sK0,X3,X4,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X3))))
        | ~ v5_pre_topc(k2_tmap_1(sK0,X3,X4,sK1),sK1,X3)
        | ~ v1_funct_2(k2_tmap_1(sK0,X3,X4,sK1),u1_struct_0(sK1),u1_struct_0(X3))
        | ~ v1_funct_1(k2_tmap_1(sK0,X3,X4,sK1))
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X3))))
        | ~ v1_funct_1(X4)
        | ~ v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X3))
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(X3) )
    | ~ spl7_18 ),
    inference(avatar_component_clause,[],[f177])).

fof(f1098,plain,
    ( ~ spl7_19
    | spl7_18 ),
    inference(avatar_split_clause,[],[f1097,f177,f217])).

fof(f217,plain,
    ( spl7_19
  <=> r4_tsep_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f1097,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ r4_tsep_1(sK0,sK1,sK2)
      | ~ v1_funct_1(k2_tmap_1(sK0,X0,X1,sK1))
      | ~ v1_funct_2(k2_tmap_1(sK0,X0,X1,sK1),u1_struct_0(sK1),u1_struct_0(X0))
      | ~ v5_pre_topc(k2_tmap_1(sK0,X0,X1,sK1),sK1,X0)
      | ~ m1_subset_1(k2_tmap_1(sK0,X0,X1,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
      | ~ v1_funct_1(k2_tmap_1(sK0,X0,X1,sK2))
      | ~ v1_funct_2(k2_tmap_1(sK0,X0,X1,sK2),u1_struct_0(sK2),u1_struct_0(X0))
      | ~ v5_pre_topc(k2_tmap_1(sK0,X0,X1,sK2),sK2,X0)
      | ~ m1_subset_1(k2_tmap_1(sK0,X0,X1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
      | v5_pre_topc(X1,sK0,X0) ) ),
    inference(global_subsumption,[],[f52,f55,f57,f58,f59,f53,f56,f674])).

fof(f674,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | v2_struct_0(sK1)
      | ~ m1_pre_topc(sK1,sK0)
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(sK2,sK0)
      | v2_struct_0(sK0)
      | ~ r4_tsep_1(sK0,sK1,sK2)
      | ~ v1_funct_1(k2_tmap_1(sK0,X0,X1,sK1))
      | ~ v1_funct_2(k2_tmap_1(sK0,X0,X1,sK1),u1_struct_0(sK1),u1_struct_0(X0))
      | ~ v5_pre_topc(k2_tmap_1(sK0,X0,X1,sK1),sK1,X0)
      | ~ m1_subset_1(k2_tmap_1(sK0,X0,X1,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
      | ~ v1_funct_1(k2_tmap_1(sK0,X0,X1,sK2))
      | ~ v1_funct_2(k2_tmap_1(sK0,X0,X1,sK2),u1_struct_0(sK2),u1_struct_0(X0))
      | ~ v5_pre_topc(k2_tmap_1(sK0,X0,X1,sK2),sK2,X0)
      | ~ m1_subset_1(k2_tmap_1(sK0,X0,X1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
      | v5_pre_topc(X1,sK0,X0) ) ),
    inference(trivial_inequality_removal,[],[f663])).

fof(f663,plain,(
    ! [X0,X1] :
      ( sK0 != sK0
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | v2_struct_0(sK1)
      | ~ m1_pre_topc(sK1,sK0)
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(sK2,sK0)
      | v2_struct_0(sK0)
      | ~ r4_tsep_1(sK0,sK1,sK2)
      | ~ v1_funct_1(k2_tmap_1(sK0,X0,X1,sK1))
      | ~ v1_funct_2(k2_tmap_1(sK0,X0,X1,sK1),u1_struct_0(sK1),u1_struct_0(X0))
      | ~ v5_pre_topc(k2_tmap_1(sK0,X0,X1,sK1),sK1,X0)
      | ~ m1_subset_1(k2_tmap_1(sK0,X0,X1,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
      | ~ v1_funct_1(k2_tmap_1(sK0,X0,X1,sK2))
      | ~ v1_funct_2(k2_tmap_1(sK0,X0,X1,sK2),u1_struct_0(sK2),u1_struct_0(X0))
      | ~ v5_pre_topc(k2_tmap_1(sK0,X0,X1,sK2),sK2,X0)
      | ~ m1_subset_1(k2_tmap_1(sK0,X0,X1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
      | v5_pre_topc(X1,sK0,X0) ) ),
    inference(superposition,[],[f61,f54])).

fof(f54,plain,(
    sK0 = k1_tsep_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r3_tsep_1(X0,X1,X2)
              <~> ( ! [X3] :
                      ( ! [X4] :
                          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
                            & v5_pre_topc(X4,X0,X3)
                            & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3))
                            & v1_funct_1(X4) )
                          | ~ m1_subset_1(k2_tmap_1(X0,X3,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                          | ~ v5_pre_topc(k2_tmap_1(X0,X3,X4,X2),X2,X3)
                          | ~ v1_funct_2(k2_tmap_1(X0,X3,X4,X2),u1_struct_0(X2),u1_struct_0(X3))
                          | ~ v1_funct_1(k2_tmap_1(X0,X3,X4,X2))
                          | ~ m1_subset_1(k2_tmap_1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                          | ~ v5_pre_topc(k2_tmap_1(X0,X3,X4,X1),X1,X3)
                          | ~ v1_funct_2(k2_tmap_1(X0,X3,X4,X1),u1_struct_0(X1),u1_struct_0(X3))
                          | ~ v1_funct_1(k2_tmap_1(X0,X3,X4,X1))
                          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
                          | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3))
                          | ~ v1_funct_1(X4) )
                      | ~ l1_pre_topc(X3)
                      | ~ v2_pre_topc(X3)
                      | v2_struct_0(X3) )
                  & r1_tsep_1(X1,X2) ) )
              & k1_tsep_1(X0,X1,X2) = X0
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
              ( ( r3_tsep_1(X0,X1,X2)
              <~> ( ! [X3] :
                      ( ! [X4] :
                          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
                            & v5_pre_topc(X4,X0,X3)
                            & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3))
                            & v1_funct_1(X4) )
                          | ~ m1_subset_1(k2_tmap_1(X0,X3,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                          | ~ v5_pre_topc(k2_tmap_1(X0,X3,X4,X2),X2,X3)
                          | ~ v1_funct_2(k2_tmap_1(X0,X3,X4,X2),u1_struct_0(X2),u1_struct_0(X3))
                          | ~ v1_funct_1(k2_tmap_1(X0,X3,X4,X2))
                          | ~ m1_subset_1(k2_tmap_1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                          | ~ v5_pre_topc(k2_tmap_1(X0,X3,X4,X1),X1,X3)
                          | ~ v1_funct_2(k2_tmap_1(X0,X3,X4,X1),u1_struct_0(X1),u1_struct_0(X3))
                          | ~ v1_funct_1(k2_tmap_1(X0,X3,X4,X1))
                          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
                          | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3))
                          | ~ v1_funct_1(X4) )
                      | ~ l1_pre_topc(X3)
                      | ~ v2_pre_topc(X3)
                      | v2_struct_0(X3) )
                  & r1_tsep_1(X1,X2) ) )
              & k1_tsep_1(X0,X1,X2) = X0
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
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
               => ( k1_tsep_1(X0,X1,X2) = X0
                 => ( r3_tsep_1(X0,X1,X2)
                  <=> ( ! [X3] :
                          ( ( l1_pre_topc(X3)
                            & v2_pre_topc(X3)
                            & ~ v2_struct_0(X3) )
                         => ! [X4] :
                              ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
                                & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3))
                                & v1_funct_1(X4) )
                             => ( ( m1_subset_1(k2_tmap_1(X0,X3,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                                  & v5_pre_topc(k2_tmap_1(X0,X3,X4,X2),X2,X3)
                                  & v1_funct_2(k2_tmap_1(X0,X3,X4,X2),u1_struct_0(X2),u1_struct_0(X3))
                                  & v1_funct_1(k2_tmap_1(X0,X3,X4,X2))
                                  & m1_subset_1(k2_tmap_1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                                  & v5_pre_topc(k2_tmap_1(X0,X3,X4,X1),X1,X3)
                                  & v1_funct_2(k2_tmap_1(X0,X3,X4,X1),u1_struct_0(X1),u1_struct_0(X3))
                                  & v1_funct_1(k2_tmap_1(X0,X3,X4,X1)) )
                               => ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
                                  & v5_pre_topc(X4,X0,X3)
                                  & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3))
                                  & v1_funct_1(X4) ) ) ) )
                      & r1_tsep_1(X1,X2) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
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
             => ( k1_tsep_1(X0,X1,X2) = X0
               => ( r3_tsep_1(X0,X1,X2)
                <=> ( ! [X3] :
                        ( ( l1_pre_topc(X3)
                          & v2_pre_topc(X3)
                          & ~ v2_struct_0(X3) )
                       => ! [X4] :
                            ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
                              & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3))
                              & v1_funct_1(X4) )
                           => ( ( m1_subset_1(k2_tmap_1(X0,X3,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                                & v5_pre_topc(k2_tmap_1(X0,X3,X4,X2),X2,X3)
                                & v1_funct_2(k2_tmap_1(X0,X3,X4,X2),u1_struct_0(X2),u1_struct_0(X3))
                                & v1_funct_1(k2_tmap_1(X0,X3,X4,X2))
                                & m1_subset_1(k2_tmap_1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                                & v5_pre_topc(k2_tmap_1(X0,X3,X4,X1),X1,X3)
                                & v1_funct_2(k2_tmap_1(X0,X3,X4,X1),u1_struct_0(X1),u1_struct_0(X3))
                                & v1_funct_1(k2_tmap_1(X0,X3,X4,X1)) )
                             => ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
                                & v5_pre_topc(X4,X0,X3)
                                & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3))
                                & v1_funct_1(X4) ) ) ) )
                    & r1_tsep_1(X1,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_tmap_1)).

fof(f61,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k1_tsep_1(X0,X3,X4) != X0
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X4,X0)
      | v2_struct_0(X0)
      | ~ r4_tsep_1(X0,X3,X4)
      | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X3))
      | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
      | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
      | ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
      | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
      | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
      | ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
      | v5_pre_topc(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                          & v5_pre_topc(X2,X0,X1)
                          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                          & v1_funct_1(X2) )
                      <=> ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                          & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) )
                      | ~ r4_tsep_1(X0,X3,X4)
                      | k1_tsep_1(X0,X3,X4) != X0
                      | ~ m1_pre_topc(X4,X0)
                      | v2_struct_0(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                          & v5_pre_topc(X2,X0,X1)
                          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                          & v1_funct_1(X2) )
                      <=> ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                          & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) )
                      | ~ r4_tsep_1(X0,X3,X4)
                      | k1_tsep_1(X0,X3,X4) != X0
                      | ~ m1_pre_topc(X4,X0)
                      | v2_struct_0(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_pre_topc(X4,X0)
                        & ~ v2_struct_0(X4) )
                     => ( ( r4_tsep_1(X0,X3,X4)
                          & k1_tsep_1(X0,X3,X4) = X0 )
                       => ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                            & v5_pre_topc(X2,X0,X1)
                            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                            & v1_funct_1(X2) )
                        <=> ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                            & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                            & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                            & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                            & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                            & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                            & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                            & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_tmap_1)).

fof(f56,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f53,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f59,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f58,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f57,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f55,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f52,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f1081,plain,
    ( spl7_2
    | spl7_20
    | ~ spl7_21
    | spl7_22
    | ~ spl7_23
    | spl7_24
    | ~ spl7_25
    | ~ spl7_26
    | ~ spl7_1 ),
    inference(avatar_split_clause,[],[f1080,f105,f238,f235,f232,f229,f226,f223,f220,f108])).

fof(f1080,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | r1_tsep_1(sK1,sK2)
    | ~ spl7_1 ),
    inference(resolution,[],[f106,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_tsep_1(X0,X1,X2)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X0)
      | r1_tsep_1(X1,X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tsep_1(X1,X2)
              | ~ r3_tsep_1(X0,X1,X2)
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
              ( r1_tsep_1(X1,X2)
              | ~ r3_tsep_1(X0,X1,X2)
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
             => ( r3_tsep_1(X0,X1,X2)
               => r1_tsep_1(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_tsep_1)).

fof(f106,plain,
    ( r3_tsep_1(sK0,sK1,sK2)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f105])).

fof(f1070,plain,
    ( spl7_20
    | ~ spl7_1
    | ~ spl7_21
    | spl7_22
    | ~ spl7_23
    | spl7_24
    | ~ spl7_25
    | ~ spl7_26
    | spl7_19 ),
    inference(avatar_split_clause,[],[f249,f217,f238,f235,f232,f229,f226,f223,f105,f220])).

fof(f249,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ r3_tsep_1(sK0,sK1,sK2)
    | v2_struct_0(sK0)
    | spl7_19 ),
    inference(resolution,[],[f218,f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( r4_tsep_1(X0,X1,X2)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ r3_tsep_1(X0,X1,X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r4_tsep_1(X0,X1,X2)
                  & r1_tsep_1(X1,X2) )
              <=> r3_tsep_1(X0,X1,X2) )
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
              ( ( ( r4_tsep_1(X0,X1,X2)
                  & r1_tsep_1(X1,X2) )
              <=> r3_tsep_1(X0,X1,X2) )
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
             => ( ( r4_tsep_1(X0,X1,X2)
                  & r1_tsep_1(X1,X2) )
              <=> r3_tsep_1(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_tsep_1)).

fof(f218,plain,
    ( ~ r4_tsep_1(sK0,sK1,sK2)
    | spl7_19 ),
    inference(avatar_component_clause,[],[f217])).

fof(f1049,plain,
    ( spl7_1
    | spl7_20
    | ~ spl7_2
    | ~ spl7_21
    | spl7_22
    | ~ spl7_23
    | spl7_24
    | ~ spl7_25
    | ~ spl7_26
    | spl7_141 ),
    inference(avatar_split_clause,[],[f1046,f942,f238,f235,f232,f229,f226,f223,f108,f220,f105])).

fof(f942,plain,
    ( spl7_141
  <=> v1_funct_1(k2_tmap_1(sK0,sK5(sK0,sK1,sK2),sK6(sK0,sK1,sK2),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_141])])).

fof(f1046,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ r1_tsep_1(sK1,sK2)
    | v2_struct_0(sK0)
    | r3_tsep_1(sK0,sK1,sK2)
    | spl7_141 ),
    inference(resolution,[],[f943,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(k2_tmap_1(X0,sK5(X0,X1,X2),sK6(X0,X1,X2),X2))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ r1_tsep_1(X1,X2)
      | v2_struct_0(X0)
      | r3_tsep_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f943,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK0,sK5(sK0,sK1,sK2),sK6(sK0,sK1,sK2),sK2))
    | spl7_141 ),
    inference(avatar_component_clause,[],[f942])).

fof(f1045,plain,
    ( spl7_1
    | spl7_20
    | ~ spl7_2
    | ~ spl7_21
    | spl7_22
    | ~ spl7_23
    | spl7_24
    | ~ spl7_25
    | ~ spl7_26
    | spl7_129 ),
    inference(avatar_split_clause,[],[f1044,f840,f238,f235,f232,f229,f226,f223,f108,f220,f105])).

fof(f840,plain,
    ( spl7_129
  <=> v1_funct_2(sK6(sK0,sK1,sK2),u1_struct_0(sK0),u1_struct_0(sK5(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_129])])).

fof(f1044,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ r1_tsep_1(sK1,sK2)
    | v2_struct_0(sK0)
    | r3_tsep_1(sK0,sK1,sK2)
    | spl7_129 ),
    inference(resolution,[],[f841,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(sK6(X0,X1,X2),u1_struct_0(X0),u1_struct_0(sK5(X0,X1,X2)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ r1_tsep_1(X1,X2)
      | v2_struct_0(X0)
      | r3_tsep_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f841,plain,
    ( ~ v1_funct_2(sK6(sK0,sK1,sK2),u1_struct_0(sK0),u1_struct_0(sK5(sK0,sK1,sK2)))
    | spl7_129 ),
    inference(avatar_component_clause,[],[f840])).

fof(f1043,plain,
    ( spl7_1
    | spl7_20
    | ~ spl7_2
    | ~ spl7_21
    | spl7_22
    | ~ spl7_23
    | spl7_24
    | ~ spl7_25
    | ~ spl7_26
    | spl7_134 ),
    inference(avatar_split_clause,[],[f1042,f856,f238,f235,f232,f229,f226,f223,f108,f220,f105])).

fof(f856,plain,
    ( spl7_134
  <=> l1_struct_0(sK5(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_134])])).

fof(f1042,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ r1_tsep_1(sK1,sK2)
    | v2_struct_0(sK0)
    | r3_tsep_1(sK0,sK1,sK2)
    | spl7_134 ),
    inference(resolution,[],[f1041,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( l1_pre_topc(sK5(X0,X1,X2))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ r1_tsep_1(X1,X2)
      | v2_struct_0(X0)
      | r3_tsep_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f1041,plain,
    ( ~ l1_pre_topc(sK5(sK0,sK1,sK2))
    | spl7_134 ),
    inference(resolution,[],[f857,f60])).

fof(f60,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
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

fof(f857,plain,
    ( ~ l1_struct_0(sK5(sK0,sK1,sK2))
    | spl7_134 ),
    inference(avatar_component_clause,[],[f856])).

fof(f954,plain,
    ( spl7_20
    | ~ spl7_21
    | spl7_22
    | ~ spl7_25
    | ~ spl7_26
    | spl7_133
    | ~ spl7_139
    | ~ spl7_140
    | ~ spl7_141
    | spl7_128
    | ~ spl7_142
    | ~ spl7_143
    | ~ spl7_144
    | ~ spl7_127
    | ~ spl7_130
    | ~ spl7_129
    | ~ spl7_131
    | ~ spl7_132
    | spl7_24
    | ~ spl7_23
    | ~ spl7_2
    | spl7_1
    | ~ spl7_33 ),
    inference(avatar_split_clause,[],[f934,f331,f105,f108,f229,f232,f849,f846,f840,f843,f834,f952,f949,f946,f837,f942,f939,f936,f852,f238,f235,f226,f223,f220])).

fof(f837,plain,
    ( spl7_128
  <=> v5_pre_topc(sK6(sK0,sK1,sK2),sK0,sK5(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_128])])).

fof(f843,plain,
    ( spl7_130
  <=> v1_funct_1(sK6(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_130])])).

fof(f846,plain,
    ( spl7_131
  <=> l1_pre_topc(sK5(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_131])])).

fof(f849,plain,
    ( spl7_132
  <=> v2_pre_topc(sK5(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_132])])).

fof(f331,plain,
    ( spl7_33
  <=> ! [X3] :
        ( v5_pre_topc(sK6(sK0,X3,sK2),sK0,sK5(sK0,X3,sK2))
        | r3_tsep_1(sK0,X3,sK2)
        | ~ r1_tsep_1(X3,sK2)
        | ~ m1_pre_topc(X3,sK0)
        | v2_struct_0(X3)
        | ~ v2_pre_topc(sK5(sK0,X3,sK2))
        | ~ l1_pre_topc(sK5(sK0,X3,sK2))
        | ~ v1_funct_2(sK6(sK0,X3,sK2),u1_struct_0(sK0),u1_struct_0(sK5(sK0,X3,sK2)))
        | ~ v1_funct_1(sK6(sK0,X3,sK2))
        | ~ m1_subset_1(sK6(sK0,X3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK5(sK0,X3,sK2)))))
        | ~ v1_funct_1(k2_tmap_1(sK0,sK5(sK0,X3,sK2),sK6(sK0,X3,sK2),sK1))
        | ~ v1_funct_2(k2_tmap_1(sK0,sK5(sK0,X3,sK2),sK6(sK0,X3,sK2),sK1),u1_struct_0(sK1),u1_struct_0(sK5(sK0,X3,sK2)))
        | ~ v5_pre_topc(k2_tmap_1(sK0,sK5(sK0,X3,sK2),sK6(sK0,X3,sK2),sK1),sK1,sK5(sK0,X3,sK2))
        | ~ m1_subset_1(k2_tmap_1(sK0,sK5(sK0,X3,sK2),sK6(sK0,X3,sK2),sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK5(sK0,X3,sK2)))))
        | ~ v1_funct_1(k2_tmap_1(sK0,sK5(sK0,X3,sK2),sK6(sK0,X3,sK2),sK2))
        | ~ v1_funct_2(k2_tmap_1(sK0,sK5(sK0,X3,sK2),sK6(sK0,X3,sK2),sK2),u1_struct_0(sK2),u1_struct_0(sK5(sK0,X3,sK2)))
        | ~ v5_pre_topc(k2_tmap_1(sK0,sK5(sK0,X3,sK2),sK6(sK0,X3,sK2),sK2),sK2,sK5(sK0,X3,sK2))
        | v2_struct_0(sK5(sK0,X3,sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_33])])).

fof(f934,plain,
    ( r3_tsep_1(sK0,sK1,sK2)
    | ~ r1_tsep_1(sK1,sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK5(sK0,sK1,sK2))
    | ~ l1_pre_topc(sK5(sK0,sK1,sK2))
    | ~ v1_funct_2(sK6(sK0,sK1,sK2),u1_struct_0(sK0),u1_struct_0(sK5(sK0,sK1,sK2)))
    | ~ v1_funct_1(sK6(sK0,sK1,sK2))
    | ~ m1_subset_1(sK6(sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK5(sK0,sK1,sK2)))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK5(sK0,sK1,sK2),sK6(sK0,sK1,sK2),sK1))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK5(sK0,sK1,sK2),sK6(sK0,sK1,sK2),sK1),u1_struct_0(sK1),u1_struct_0(sK5(sK0,sK1,sK2)))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK5(sK0,sK1,sK2),sK6(sK0,sK1,sK2),sK1),sK1,sK5(sK0,sK1,sK2))
    | v5_pre_topc(sK6(sK0,sK1,sK2),sK0,sK5(sK0,sK1,sK2))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK5(sK0,sK1,sK2),sK6(sK0,sK1,sK2),sK2))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK5(sK0,sK1,sK2),sK6(sK0,sK1,sK2),sK2),u1_struct_0(sK2),u1_struct_0(sK5(sK0,sK1,sK2)))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK5(sK0,sK1,sK2),sK6(sK0,sK1,sK2),sK2),sK2,sK5(sK0,sK1,sK2))
    | v2_struct_0(sK5(sK0,sK1,sK2))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | ~ spl7_33 ),
    inference(duplicate_literal_removal,[],[f931])).

fof(f931,plain,
    ( r3_tsep_1(sK0,sK1,sK2)
    | ~ r1_tsep_1(sK1,sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK5(sK0,sK1,sK2))
    | ~ l1_pre_topc(sK5(sK0,sK1,sK2))
    | ~ v1_funct_2(sK6(sK0,sK1,sK2),u1_struct_0(sK0),u1_struct_0(sK5(sK0,sK1,sK2)))
    | ~ v1_funct_1(sK6(sK0,sK1,sK2))
    | ~ m1_subset_1(sK6(sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK5(sK0,sK1,sK2)))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK5(sK0,sK1,sK2),sK6(sK0,sK1,sK2),sK1))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK5(sK0,sK1,sK2),sK6(sK0,sK1,sK2),sK1),u1_struct_0(sK1),u1_struct_0(sK5(sK0,sK1,sK2)))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK5(sK0,sK1,sK2),sK6(sK0,sK1,sK2),sK1),sK1,sK5(sK0,sK1,sK2))
    | v5_pre_topc(sK6(sK0,sK1,sK2),sK0,sK5(sK0,sK1,sK2))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK5(sK0,sK1,sK2),sK6(sK0,sK1,sK2),sK2))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK5(sK0,sK1,sK2),sK6(sK0,sK1,sK2),sK2),u1_struct_0(sK2),u1_struct_0(sK5(sK0,sK1,sK2)))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK5(sK0,sK1,sK2),sK6(sK0,sK1,sK2),sK2),sK2,sK5(sK0,sK1,sK2))
    | v2_struct_0(sK5(sK0,sK1,sK2))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ r1_tsep_1(sK1,sK2)
    | v2_struct_0(sK0)
    | r3_tsep_1(sK0,sK1,sK2)
    | ~ spl7_33 ),
    inference(resolution,[],[f332,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_tmap_1(X0,sK5(X0,X1,X2),sK6(X0,X1,X2),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK5(X0,X1,X2)))))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ r1_tsep_1(X1,X2)
      | v2_struct_0(X0)
      | r3_tsep_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f332,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(k2_tmap_1(sK0,sK5(sK0,X3,sK2),sK6(sK0,X3,sK2),sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK5(sK0,X3,sK2)))))
        | r3_tsep_1(sK0,X3,sK2)
        | ~ r1_tsep_1(X3,sK2)
        | ~ m1_pre_topc(X3,sK0)
        | v2_struct_0(X3)
        | ~ v2_pre_topc(sK5(sK0,X3,sK2))
        | ~ l1_pre_topc(sK5(sK0,X3,sK2))
        | ~ v1_funct_2(sK6(sK0,X3,sK2),u1_struct_0(sK0),u1_struct_0(sK5(sK0,X3,sK2)))
        | ~ v1_funct_1(sK6(sK0,X3,sK2))
        | ~ m1_subset_1(sK6(sK0,X3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK5(sK0,X3,sK2)))))
        | ~ v1_funct_1(k2_tmap_1(sK0,sK5(sK0,X3,sK2),sK6(sK0,X3,sK2),sK1))
        | ~ v1_funct_2(k2_tmap_1(sK0,sK5(sK0,X3,sK2),sK6(sK0,X3,sK2),sK1),u1_struct_0(sK1),u1_struct_0(sK5(sK0,X3,sK2)))
        | ~ v5_pre_topc(k2_tmap_1(sK0,sK5(sK0,X3,sK2),sK6(sK0,X3,sK2),sK1),sK1,sK5(sK0,X3,sK2))
        | v5_pre_topc(sK6(sK0,X3,sK2),sK0,sK5(sK0,X3,sK2))
        | ~ v1_funct_1(k2_tmap_1(sK0,sK5(sK0,X3,sK2),sK6(sK0,X3,sK2),sK2))
        | ~ v1_funct_2(k2_tmap_1(sK0,sK5(sK0,X3,sK2),sK6(sK0,X3,sK2),sK2),u1_struct_0(sK2),u1_struct_0(sK5(sK0,X3,sK2)))
        | ~ v5_pre_topc(k2_tmap_1(sK0,sK5(sK0,X3,sK2),sK6(sK0,X3,sK2),sK2),sK2,sK5(sK0,X3,sK2))
        | v2_struct_0(sK5(sK0,X3,sK2)) )
    | ~ spl7_33 ),
    inference(avatar_component_clause,[],[f331])).

fof(f918,plain,
    ( spl7_1
    | spl7_20
    | ~ spl7_2
    | ~ spl7_21
    | spl7_22
    | ~ spl7_23
    | spl7_24
    | ~ spl7_25
    | ~ spl7_26
    | spl7_132 ),
    inference(avatar_split_clause,[],[f917,f849,f238,f235,f232,f229,f226,f223,f108,f220,f105])).

fof(f917,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ r1_tsep_1(sK1,sK2)
    | v2_struct_0(sK0)
    | r3_tsep_1(sK0,sK1,sK2)
    | spl7_132 ),
    inference(resolution,[],[f850,f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( v2_pre_topc(sK5(X0,X1,X2))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ r1_tsep_1(X1,X2)
      | v2_struct_0(X0)
      | r3_tsep_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f850,plain,
    ( ~ v2_pre_topc(sK5(sK0,sK1,sK2))
    | spl7_132 ),
    inference(avatar_component_clause,[],[f849])).

fof(f916,plain,
    ( spl7_1
    | spl7_20
    | ~ spl7_2
    | ~ spl7_21
    | spl7_22
    | ~ spl7_23
    | spl7_24
    | ~ spl7_25
    | ~ spl7_26
    | spl7_131 ),
    inference(avatar_split_clause,[],[f915,f846,f238,f235,f232,f229,f226,f223,f108,f220,f105])).

fof(f915,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ r1_tsep_1(sK1,sK2)
    | v2_struct_0(sK0)
    | r3_tsep_1(sK0,sK1,sK2)
    | spl7_131 ),
    inference(resolution,[],[f847,f89])).

fof(f847,plain,
    ( ~ l1_pre_topc(sK5(sK0,sK1,sK2))
    | spl7_131 ),
    inference(avatar_component_clause,[],[f846])).

fof(f914,plain,(
    ~ spl7_24 ),
    inference(avatar_contradiction_clause,[],[f913])).

fof(f913,plain,
    ( $false
    | ~ spl7_24 ),
    inference(resolution,[],[f233,f55])).

fof(f233,plain,
    ( v2_struct_0(sK1)
    | ~ spl7_24 ),
    inference(avatar_component_clause,[],[f232])).

fof(f912,plain,
    ( spl7_1
    | spl7_20
    | ~ spl7_2
    | ~ spl7_21
    | spl7_22
    | ~ spl7_23
    | spl7_24
    | ~ spl7_25
    | ~ spl7_26
    | spl7_130 ),
    inference(avatar_split_clause,[],[f911,f843,f238,f235,f232,f229,f226,f223,f108,f220,f105])).

fof(f911,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ r1_tsep_1(sK1,sK2)
    | v2_struct_0(sK0)
    | r3_tsep_1(sK0,sK1,sK2)
    | spl7_130 ),
    inference(resolution,[],[f844,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(sK6(X0,X1,X2))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ r1_tsep_1(X1,X2)
      | v2_struct_0(X0)
      | r3_tsep_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f844,plain,
    ( ~ v1_funct_1(sK6(sK0,sK1,sK2))
    | spl7_130 ),
    inference(avatar_component_clause,[],[f843])).

fof(f886,plain,
    ( ~ spl7_29
    | ~ spl7_127
    | ~ spl7_129
    | ~ spl7_130
    | ~ spl7_134
    | spl7_57 ),
    inference(avatar_split_clause,[],[f885,f479,f856,f843,f840,f834,f317])).

fof(f317,plain,
    ( spl7_29
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_29])])).

fof(f479,plain,
    ( spl7_57
  <=> m1_subset_1(k2_tmap_1(sK0,sK5(sK0,sK1,sK2),sK6(sK0,sK1,sK2),sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK5(sK0,sK1,sK2))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_57])])).

fof(f885,plain,
    ( ~ l1_struct_0(sK5(sK0,sK1,sK2))
    | ~ v1_funct_1(sK6(sK0,sK1,sK2))
    | ~ v1_funct_2(sK6(sK0,sK1,sK2),u1_struct_0(sK0),u1_struct_0(sK5(sK0,sK1,sK2)))
    | ~ m1_subset_1(sK6(sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK5(sK0,sK1,sK2)))))
    | ~ l1_struct_0(sK0)
    | spl7_57 ),
    inference(duplicate_literal_removal,[],[f884])).

fof(f884,plain,
    ( ~ l1_struct_0(sK5(sK0,sK1,sK2))
    | ~ v1_funct_1(sK6(sK0,sK1,sK2))
    | ~ v1_funct_2(sK6(sK0,sK1,sK2),u1_struct_0(sK0),u1_struct_0(sK5(sK0,sK1,sK2)))
    | ~ m1_subset_1(sK6(sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK5(sK0,sK1,sK2)))))
    | ~ l1_struct_0(sK0)
    | ~ l1_struct_0(sK0)
    | spl7_57 ),
    inference(resolution,[],[f480,f103])).

fof(f103,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ l1_struct_0(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_struct_0(X3)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( l1_struct_0(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(X2)
        & l1_struct_0(X1)
        & l1_struct_0(X0) )
     => ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tmap_1)).

fof(f480,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK0,sK5(sK0,sK1,sK2),sK6(sK0,sK1,sK2),sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK5(sK0,sK1,sK2)))))
    | spl7_57 ),
    inference(avatar_component_clause,[],[f479])).

fof(f881,plain,
    ( ~ spl7_29
    | ~ spl7_127
    | ~ spl7_129
    | ~ spl7_130
    | ~ spl7_134
    | spl7_55 ),
    inference(avatar_split_clause,[],[f878,f473,f856,f843,f840,f834,f317])).

fof(f473,plain,
    ( spl7_55
  <=> v1_funct_2(k2_tmap_1(sK0,sK5(sK0,sK1,sK2),sK6(sK0,sK1,sK2),sK0),u1_struct_0(sK0),u1_struct_0(sK5(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_55])])).

fof(f878,plain,
    ( ~ l1_struct_0(sK5(sK0,sK1,sK2))
    | ~ v1_funct_1(sK6(sK0,sK1,sK2))
    | ~ v1_funct_2(sK6(sK0,sK1,sK2),u1_struct_0(sK0),u1_struct_0(sK5(sK0,sK1,sK2)))
    | ~ m1_subset_1(sK6(sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK5(sK0,sK1,sK2)))))
    | ~ l1_struct_0(sK0)
    | spl7_55 ),
    inference(duplicate_literal_removal,[],[f877])).

fof(f877,plain,
    ( ~ l1_struct_0(sK5(sK0,sK1,sK2))
    | ~ v1_funct_1(sK6(sK0,sK1,sK2))
    | ~ v1_funct_2(sK6(sK0,sK1,sK2),u1_struct_0(sK0),u1_struct_0(sK5(sK0,sK1,sK2)))
    | ~ m1_subset_1(sK6(sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK5(sK0,sK1,sK2)))))
    | ~ l1_struct_0(sK0)
    | ~ l1_struct_0(sK0)
    | spl7_55 ),
    inference(resolution,[],[f474,f102])).

fof(f102,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
      | ~ l1_struct_0(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_struct_0(X3)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f474,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,sK5(sK0,sK1,sK2),sK6(sK0,sK1,sK2),sK0),u1_struct_0(sK0),u1_struct_0(sK5(sK0,sK1,sK2)))
    | spl7_55 ),
    inference(avatar_component_clause,[],[f473])).

fof(f868,plain,
    ( ~ spl7_51
    | spl7_20
    | ~ spl7_127
    | ~ spl7_128
    | ~ spl7_129
    | ~ spl7_130
    | ~ spl7_131
    | ~ spl7_132
    | spl7_133
    | ~ spl7_25
    | ~ spl7_26
    | spl7_54 ),
    inference(avatar_split_clause,[],[f867,f470,f238,f235,f852,f849,f846,f843,f840,f837,f834,f220,f423])).

fof(f423,plain,
    ( spl7_51
  <=> m1_pre_topc(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_51])])).

fof(f470,plain,
    ( spl7_54
  <=> v5_pre_topc(k2_tmap_1(sK0,sK5(sK0,sK1,sK2),sK6(sK0,sK1,sK2),sK0),sK0,sK5(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_54])])).

fof(f867,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK5(sK0,sK1,sK2))
    | ~ v2_pre_topc(sK5(sK0,sK1,sK2))
    | ~ l1_pre_topc(sK5(sK0,sK1,sK2))
    | ~ v1_funct_1(sK6(sK0,sK1,sK2))
    | ~ v1_funct_2(sK6(sK0,sK1,sK2),u1_struct_0(sK0),u1_struct_0(sK5(sK0,sK1,sK2)))
    | ~ v5_pre_topc(sK6(sK0,sK1,sK2),sK0,sK5(sK0,sK1,sK2))
    | ~ m1_subset_1(sK6(sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK5(sK0,sK1,sK2)))))
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | spl7_54 ),
    inference(duplicate_literal_removal,[],[f866])).

fof(f866,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK5(sK0,sK1,sK2))
    | ~ v2_pre_topc(sK5(sK0,sK1,sK2))
    | ~ l1_pre_topc(sK5(sK0,sK1,sK2))
    | ~ v1_funct_1(sK6(sK0,sK1,sK2))
    | ~ v1_funct_2(sK6(sK0,sK1,sK2),u1_struct_0(sK0),u1_struct_0(sK5(sK0,sK1,sK2)))
    | ~ v5_pre_topc(sK6(sK0,sK1,sK2),sK0,sK5(sK0,sK1,sK2))
    | ~ m1_subset_1(sK6(sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK5(sK0,sK1,sK2)))))
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | v2_struct_0(sK0)
    | spl7_54 ),
    inference(resolution,[],[f471,f100])).

fof(f100,plain,(
    ! [X2,X0,X3,X1] :
      ( v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( ( v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_pre_topc(X3,X0)
        & ~ v2_struct_0(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v5_pre_topc(X2,X0,X1)
        & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(X2)
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_tmap_1)).

fof(f471,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK0,sK5(sK0,sK1,sK2),sK6(sK0,sK1,sK2),sK0),sK0,sK5(sK0,sK1,sK2))
    | spl7_54 ),
    inference(avatar_component_clause,[],[f470])).

fof(f858,plain,
    ( ~ spl7_29
    | ~ spl7_127
    | ~ spl7_129
    | ~ spl7_130
    | ~ spl7_134
    | spl7_56 ),
    inference(avatar_split_clause,[],[f831,f476,f856,f843,f840,f834,f317])).

fof(f476,plain,
    ( spl7_56
  <=> v1_funct_1(k2_tmap_1(sK0,sK5(sK0,sK1,sK2),sK6(sK0,sK1,sK2),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_56])])).

fof(f831,plain,
    ( ~ l1_struct_0(sK5(sK0,sK1,sK2))
    | ~ v1_funct_1(sK6(sK0,sK1,sK2))
    | ~ v1_funct_2(sK6(sK0,sK1,sK2),u1_struct_0(sK0),u1_struct_0(sK5(sK0,sK1,sK2)))
    | ~ m1_subset_1(sK6(sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK5(sK0,sK1,sK2)))))
    | ~ l1_struct_0(sK0)
    | spl7_56 ),
    inference(duplicate_literal_removal,[],[f830])).

fof(f830,plain,
    ( ~ l1_struct_0(sK5(sK0,sK1,sK2))
    | ~ v1_funct_1(sK6(sK0,sK1,sK2))
    | ~ v1_funct_2(sK6(sK0,sK1,sK2),u1_struct_0(sK0),u1_struct_0(sK5(sK0,sK1,sK2)))
    | ~ m1_subset_1(sK6(sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK5(sK0,sK1,sK2)))))
    | ~ l1_struct_0(sK0)
    | ~ l1_struct_0(sK0)
    | spl7_56 ),
    inference(resolution,[],[f477,f101])).

fof(f101,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_tmap_1(X0,X1,X2,X3))
      | ~ l1_struct_0(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_struct_0(X3)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f477,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK0,sK5(sK0,sK1,sK2),sK6(sK0,sK1,sK2),sK0))
    | spl7_56 ),
    inference(avatar_component_clause,[],[f476])).

fof(f481,plain,
    ( spl7_1
    | ~ spl7_54
    | ~ spl7_55
    | ~ spl7_56
    | ~ spl7_57 ),
    inference(avatar_split_clause,[],[f468,f479,f476,f473,f470,f105])).

fof(f468,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK0,sK5(sK0,sK1,sK2),sK6(sK0,sK1,sK2),sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK5(sK0,sK1,sK2)))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK5(sK0,sK1,sK2),sK6(sK0,sK1,sK2),sK0))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK5(sK0,sK1,sK2),sK6(sK0,sK1,sK2),sK0),u1_struct_0(sK0),u1_struct_0(sK5(sK0,sK1,sK2)))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK5(sK0,sK1,sK2),sK6(sK0,sK1,sK2),sK0),sK0,sK5(sK0,sK1,sK2))
    | r3_tsep_1(sK0,sK1,sK2) ),
    inference(global_subsumption,[],[f51,f52,f55,f57,f58,f59,f53,f56,f458])).

fof(f458,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK0,sK5(sK0,sK1,sK2),sK6(sK0,sK1,sK2),sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK5(sK0,sK1,sK2)))))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ r1_tsep_1(sK1,sK2)
    | ~ v1_funct_1(k2_tmap_1(sK0,sK5(sK0,sK1,sK2),sK6(sK0,sK1,sK2),sK0))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK5(sK0,sK1,sK2),sK6(sK0,sK1,sK2),sK0),u1_struct_0(sK0),u1_struct_0(sK5(sK0,sK1,sK2)))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK5(sK0,sK1,sK2),sK6(sK0,sK1,sK2),sK0),sK0,sK5(sK0,sK1,sK2))
    | v2_struct_0(sK0)
    | r3_tsep_1(sK0,sK1,sK2) ),
    inference(superposition,[],[f71,f54])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k2_tmap_1(X0,sK5(X0,X1,X2),sK6(X0,X1,X2),k1_tsep_1(X0,X1,X2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(sK5(X0,X1,X2)))))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ r1_tsep_1(X1,X2)
      | ~ v1_funct_1(k2_tmap_1(X0,sK5(X0,X1,X2),sK6(X0,X1,X2),k1_tsep_1(X0,X1,X2)))
      | ~ v1_funct_2(k2_tmap_1(X0,sK5(X0,X1,X2),sK6(X0,X1,X2),k1_tsep_1(X0,X1,X2)),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(sK5(X0,X1,X2)))
      | ~ v5_pre_topc(k2_tmap_1(X0,sK5(X0,X1,X2),sK6(X0,X1,X2),k1_tsep_1(X0,X1,X2)),k1_tsep_1(X0,X1,X2),sK5(X0,X1,X2))
      | v2_struct_0(X0)
      | r3_tsep_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f51,plain,
    ( r1_tsep_1(sK1,sK2)
    | r3_tsep_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f456,plain,(
    spl7_51 ),
    inference(avatar_contradiction_clause,[],[f455])).

fof(f455,plain,
    ( $false
    | spl7_51 ),
    inference(resolution,[],[f424,f182])).

fof(f182,plain,(
    m1_pre_topc(sK0,sK0) ),
    inference(global_subsumption,[],[f52,f55,f57,f59,f53,f56,f181])).

fof(f181,plain,
    ( m1_pre_topc(sK0,sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f96,f54])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f2])).

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

fof(f424,plain,
    ( ~ m1_pre_topc(sK0,sK0)
    | spl7_51 ),
    inference(avatar_component_clause,[],[f423])).

fof(f341,plain,(
    spl7_29 ),
    inference(avatar_contradiction_clause,[],[f340])).

fof(f340,plain,
    ( $false
    | spl7_29 ),
    inference(resolution,[],[f338,f59])).

fof(f338,plain,
    ( ~ l1_pre_topc(sK0)
    | spl7_29 ),
    inference(resolution,[],[f318,f60])).

fof(f318,plain,
    ( ~ l1_struct_0(sK0)
    | spl7_29 ),
    inference(avatar_component_clause,[],[f317])).

fof(f337,plain,(
    ~ spl7_22 ),
    inference(avatar_contradiction_clause,[],[f336])).

fof(f336,plain,
    ( $false
    | ~ spl7_22 ),
    inference(resolution,[],[f227,f52])).

fof(f227,plain,
    ( v2_struct_0(sK2)
    | ~ spl7_22 ),
    inference(avatar_component_clause,[],[f226])).

fof(f335,plain,(
    ~ spl7_20 ),
    inference(avatar_contradiction_clause,[],[f334])).

fof(f334,plain,
    ( $false
    | ~ spl7_20 ),
    inference(resolution,[],[f221,f57])).

fof(f221,plain,
    ( v2_struct_0(sK0)
    | ~ spl7_20 ),
    inference(avatar_component_clause,[],[f220])).

fof(f333,plain,
    ( spl7_20
    | ~ spl7_21
    | spl7_22
    | ~ spl7_25
    | ~ spl7_26
    | spl7_33
    | ~ spl7_18 ),
    inference(avatar_split_clause,[],[f314,f177,f331,f238,f235,f226,f223,f220])).

fof(f314,plain,
    ( ! [X3] :
        ( v5_pre_topc(sK6(sK0,X3,sK2),sK0,sK5(sK0,X3,sK2))
        | v2_struct_0(sK5(sK0,X3,sK2))
        | ~ v5_pre_topc(k2_tmap_1(sK0,sK5(sK0,X3,sK2),sK6(sK0,X3,sK2),sK2),sK2,sK5(sK0,X3,sK2))
        | ~ v1_funct_2(k2_tmap_1(sK0,sK5(sK0,X3,sK2),sK6(sK0,X3,sK2),sK2),u1_struct_0(sK2),u1_struct_0(sK5(sK0,X3,sK2)))
        | ~ v1_funct_1(k2_tmap_1(sK0,sK5(sK0,X3,sK2),sK6(sK0,X3,sK2),sK2))
        | ~ m1_subset_1(k2_tmap_1(sK0,sK5(sK0,X3,sK2),sK6(sK0,X3,sK2),sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK5(sK0,X3,sK2)))))
        | ~ v5_pre_topc(k2_tmap_1(sK0,sK5(sK0,X3,sK2),sK6(sK0,X3,sK2),sK1),sK1,sK5(sK0,X3,sK2))
        | ~ v1_funct_2(k2_tmap_1(sK0,sK5(sK0,X3,sK2),sK6(sK0,X3,sK2),sK1),u1_struct_0(sK1),u1_struct_0(sK5(sK0,X3,sK2)))
        | ~ v1_funct_1(k2_tmap_1(sK0,sK5(sK0,X3,sK2),sK6(sK0,X3,sK2),sK1))
        | ~ m1_subset_1(sK6(sK0,X3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK5(sK0,X3,sK2)))))
        | ~ v1_funct_1(sK6(sK0,X3,sK2))
        | ~ v1_funct_2(sK6(sK0,X3,sK2),u1_struct_0(sK0),u1_struct_0(sK5(sK0,X3,sK2)))
        | ~ l1_pre_topc(sK5(sK0,X3,sK2))
        | ~ v2_pre_topc(sK5(sK0,X3,sK2))
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,sK0)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(sK2,sK0)
        | ~ r1_tsep_1(X3,sK2)
        | v2_struct_0(sK0)
        | r3_tsep_1(sK0,X3,sK2) )
    | ~ spl7_18 ),
    inference(resolution,[],[f178,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_tmap_1(X0,sK5(X0,X1,X2),sK6(X0,X1,X2),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK5(X0,X1,X2)))))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ r1_tsep_1(X1,X2)
      | v2_struct_0(X0)
      | r3_tsep_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f248,plain,(
    spl7_23 ),
    inference(avatar_contradiction_clause,[],[f247])).

fof(f247,plain,
    ( $false
    | spl7_23 ),
    inference(resolution,[],[f230,f56])).

fof(f230,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | spl7_23 ),
    inference(avatar_component_clause,[],[f229])).

fof(f246,plain,(
    spl7_21 ),
    inference(avatar_contradiction_clause,[],[f245])).

fof(f245,plain,
    ( $false
    | spl7_21 ),
    inference(resolution,[],[f224,f53])).

fof(f224,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | spl7_21 ),
    inference(avatar_component_clause,[],[f223])).

fof(f244,plain,(
    spl7_26 ),
    inference(avatar_contradiction_clause,[],[f243])).

fof(f243,plain,
    ( $false
    | spl7_26 ),
    inference(resolution,[],[f239,f58])).

fof(f239,plain,
    ( ~ v2_pre_topc(sK0)
    | spl7_26 ),
    inference(avatar_component_clause,[],[f238])).

fof(f242,plain,(
    spl7_25 ),
    inference(avatar_contradiction_clause,[],[f241])).

fof(f241,plain,
    ( $false
    | spl7_25 ),
    inference(resolution,[],[f236,f59])).

fof(f236,plain,
    ( ~ l1_pre_topc(sK0)
    | spl7_25 ),
    inference(avatar_component_clause,[],[f235])).

fof(f179,plain,
    ( spl7_1
    | spl7_18 ),
    inference(avatar_split_clause,[],[f35,f177,f105])).

fof(f35,plain,(
    ! [X4,X3] :
      ( v2_struct_0(X3)
      | ~ v2_pre_topc(X3)
      | ~ l1_pre_topc(X3)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X3))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X3))))
      | ~ v1_funct_1(k2_tmap_1(sK0,X3,X4,sK1))
      | ~ v1_funct_2(k2_tmap_1(sK0,X3,X4,sK1),u1_struct_0(sK1),u1_struct_0(X3))
      | ~ v5_pre_topc(k2_tmap_1(sK0,X3,X4,sK1),sK1,X3)
      | ~ m1_subset_1(k2_tmap_1(sK0,X3,X4,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X3))))
      | ~ v1_funct_1(k2_tmap_1(sK0,X3,X4,sK2))
      | ~ v1_funct_2(k2_tmap_1(sK0,X3,X4,sK2),u1_struct_0(sK2),u1_struct_0(X3))
      | ~ v5_pre_topc(k2_tmap_1(sK0,X3,X4,sK2),sK2,X3)
      | ~ m1_subset_1(k2_tmap_1(sK0,X3,X4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X3))))
      | v5_pre_topc(X4,sK0,X3)
      | r3_tsep_1(sK0,sK1,sK2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f175,plain,
    ( ~ spl7_1
    | ~ spl7_14
    | ~ spl7_17
    | ~ spl7_15
    | ~ spl7_16
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f36,f108,f166,f162,f171,f158,f105])).

fof(f36,plain,
    ( ~ r1_tsep_1(sK1,sK2)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK3))
    | ~ v5_pre_topc(sK4,sK0,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK3))))
    | ~ r3_tsep_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f168,plain,
    ( ~ spl7_1
    | spl7_16
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f37,f108,f166,f105])).

fof(f37,plain,
    ( ~ r1_tsep_1(sK1,sK2)
    | v1_funct_1(sK4)
    | ~ r3_tsep_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f164,plain,
    ( ~ spl7_1
    | spl7_15
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f38,f108,f162,f105])).

fof(f38,plain,
    ( ~ r1_tsep_1(sK1,sK2)
    | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK3))
    | ~ r3_tsep_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f160,plain,
    ( ~ spl7_1
    | spl7_14
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f39,f108,f158,f105])).

fof(f39,plain,
    ( ~ r1_tsep_1(sK1,sK2)
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK3))))
    | ~ r3_tsep_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f156,plain,
    ( ~ spl7_1
    | spl7_13
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f40,f108,f154,f105])).

fof(f40,plain,
    ( ~ r1_tsep_1(sK1,sK2)
    | v1_funct_1(k2_tmap_1(sK0,sK3,sK4,sK1))
    | ~ r3_tsep_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f152,plain,
    ( ~ spl7_1
    | spl7_12
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f41,f108,f150,f105])).

fof(f41,plain,
    ( ~ r1_tsep_1(sK1,sK2)
    | v1_funct_2(k2_tmap_1(sK0,sK3,sK4,sK1),u1_struct_0(sK1),u1_struct_0(sK3))
    | ~ r3_tsep_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f148,plain,
    ( ~ spl7_1
    | spl7_11
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f42,f108,f146,f105])).

fof(f42,plain,
    ( ~ r1_tsep_1(sK1,sK2)
    | v5_pre_topc(k2_tmap_1(sK0,sK3,sK4,sK1),sK1,sK3)
    | ~ r3_tsep_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f144,plain,
    ( ~ spl7_1
    | spl7_10
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f43,f108,f142,f105])).

fof(f43,plain,
    ( ~ r1_tsep_1(sK1,sK2)
    | m1_subset_1(k2_tmap_1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK3))))
    | ~ r3_tsep_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f140,plain,
    ( ~ spl7_1
    | spl7_9
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f44,f108,f138,f105])).

fof(f44,plain,
    ( ~ r1_tsep_1(sK1,sK2)
    | v1_funct_1(k2_tmap_1(sK0,sK3,sK4,sK2))
    | ~ r3_tsep_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f136,plain,
    ( ~ spl7_1
    | spl7_8
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f45,f108,f134,f105])).

fof(f45,plain,
    ( ~ r1_tsep_1(sK1,sK2)
    | v1_funct_2(k2_tmap_1(sK0,sK3,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ r3_tsep_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f132,plain,
    ( ~ spl7_1
    | spl7_7
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f46,f108,f130,f105])).

fof(f46,plain,
    ( ~ r1_tsep_1(sK1,sK2)
    | v5_pre_topc(k2_tmap_1(sK0,sK3,sK4,sK2),sK2,sK3)
    | ~ r3_tsep_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f128,plain,
    ( ~ spl7_1
    | spl7_6
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f47,f108,f126,f105])).

fof(f47,plain,
    ( ~ r1_tsep_1(sK1,sK2)
    | m1_subset_1(k2_tmap_1(sK0,sK3,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ r3_tsep_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f124,plain,
    ( ~ spl7_1
    | ~ spl7_5
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f48,f108,f122,f105])).

fof(f48,plain,
    ( ~ r1_tsep_1(sK1,sK2)
    | ~ v2_struct_0(sK3)
    | ~ r3_tsep_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f120,plain,
    ( ~ spl7_1
    | spl7_4
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f49,f108,f118,f105])).

fof(f49,plain,
    ( ~ r1_tsep_1(sK1,sK2)
    | v2_pre_topc(sK3)
    | ~ r3_tsep_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f116,plain,
    ( ~ spl7_1
    | spl7_3
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f50,f108,f113,f105])).

fof(f50,plain,
    ( ~ r1_tsep_1(sK1,sK2)
    | l1_pre_topc(sK3)
    | ~ r3_tsep_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f110,plain,
    ( spl7_1
    | spl7_2 ),
    inference(avatar_split_clause,[],[f51,f108,f105])).

%------------------------------------------------------------------------------
