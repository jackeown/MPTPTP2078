%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tmap_1__t137_tmap_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:08 EDT 2019

% Result     : Theorem 1.30s
% Output     : Refutation 1.30s
% Verified   : 
% Statistics : Number of formulae       :  316 (1399 expanded)
%              Number of leaves         :   93 ( 705 expanded)
%              Depth                    :   17
%              Number of atoms          : 2675 (39576 expanded)
%              Number of equality atoms :   35 ( 729 expanded)
%              Maximal formula depth    :   30 (   8 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5418,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f268,f272,f276,f280,f284,f288,f292,f296,f300,f304,f308,f312,f316,f320,f324,f331,f335,f385,f389,f397,f401,f405,f409,f413,f441,f443,f451,f459,f461,f463,f465,f710,f1026,f2185,f2476,f2557,f2600,f2648,f2677,f3965,f3968,f4665,f4668,f4743,f4843,f4846,f4849,f4852,f4856,f4881,f5348,f5414,f5417])).

fof(f5417,plain,
    ( ~ spl12_39
    | ~ spl12_41
    | spl12_106
    | ~ spl12_51
    | ~ spl12_53
    | ~ spl12_55
    | ~ spl12_109
    | ~ spl12_113
    | ~ spl12_57
    | spl12_36
    | ~ spl12_611
    | spl12_71 ),
    inference(avatar_split_clause,[],[f5416,f431,f2437,f362,f2602,f626,f619,f616,f613,f610,f607,f368,f365])).

fof(f365,plain,
    ( spl12_39
  <=> ~ v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_39])])).

fof(f368,plain,
    ( spl12_41
  <=> ~ l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_41])])).

fof(f607,plain,
    ( spl12_106
  <=> v2_struct_0(sK6(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_106])])).

fof(f610,plain,
    ( spl12_51
  <=> ~ v2_pre_topc(sK6(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_51])])).

fof(f613,plain,
    ( spl12_53
  <=> ~ l1_pre_topc(sK6(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_53])])).

fof(f616,plain,
    ( spl12_55
  <=> ~ v1_funct_1(sK7(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_55])])).

fof(f619,plain,
    ( spl12_109
  <=> ~ v1_funct_2(sK7(sK0,sK1,sK2),u1_struct_0(sK0),u1_struct_0(sK6(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_109])])).

fof(f626,plain,
    ( spl12_113
  <=> ~ v5_pre_topc(sK7(sK0,sK1,sK2),sK0,sK6(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_113])])).

fof(f2602,plain,
    ( spl12_57
  <=> ~ m1_subset_1(sK7(sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK6(sK0,sK1,sK2))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_57])])).

fof(f362,plain,
    ( spl12_36
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_36])])).

fof(f2437,plain,
    ( spl12_611
  <=> ~ m1_pre_topc(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_611])])).

fof(f431,plain,
    ( spl12_71
  <=> ~ v5_pre_topc(k2_tmap_1(sK0,sK6(sK0,sK1,sK2),sK7(sK0,sK1,sK2),sK0),sK0,sK6(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_71])])).

fof(f5416,plain,
    ( ~ m1_pre_topc(sK0,sK0)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(sK7(sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK6(sK0,sK1,sK2)))))
    | ~ v5_pre_topc(sK7(sK0,sK1,sK2),sK0,sK6(sK0,sK1,sK2))
    | ~ v1_funct_2(sK7(sK0,sK1,sK2),u1_struct_0(sK0),u1_struct_0(sK6(sK0,sK1,sK2)))
    | ~ v1_funct_1(sK7(sK0,sK1,sK2))
    | ~ l1_pre_topc(sK6(sK0,sK1,sK2))
    | ~ v2_pre_topc(sK6(sK0,sK1,sK2))
    | v2_struct_0(sK6(sK0,sK1,sK2))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl12_71 ),
    inference(duplicate_literal_removal,[],[f5415])).

fof(f5415,plain,
    ( ~ m1_pre_topc(sK0,sK0)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(sK7(sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK6(sK0,sK1,sK2)))))
    | ~ v5_pre_topc(sK7(sK0,sK1,sK2),sK0,sK6(sK0,sK1,sK2))
    | ~ v1_funct_2(sK7(sK0,sK1,sK2),u1_struct_0(sK0),u1_struct_0(sK6(sK0,sK1,sK2)))
    | ~ v1_funct_1(sK7(sK0,sK1,sK2))
    | ~ l1_pre_topc(sK6(sK0,sK1,sK2))
    | ~ v2_pre_topc(sK6(sK0,sK1,sK2))
    | v2_struct_0(sK6(sK0,sK1,sK2))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_71 ),
    inference(resolution,[],[f432,f232])).

fof(f232,plain,(
    ! [X2,X0,X3,X1] :
      ( v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
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
    inference(cnf_transformation,[],[f95])).

fof(f95,plain,(
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
    inference(flattening,[],[f94])).

fof(f94,plain,(
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
    inference(ennf_transformation,[],[f45])).

fof(f45,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/tmap_1__t137_tmap_1.p',fc2_tmap_1)).

fof(f432,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK0,sK6(sK0,sK1,sK2),sK7(sK0,sK1,sK2),sK0),sK0,sK6(sK0,sK1,sK2))
    | ~ spl12_71 ),
    inference(avatar_component_clause,[],[f431])).

fof(f5414,plain,
    ( ~ spl12_121
    | ~ spl12_55
    | ~ spl12_109
    | ~ spl12_57
    | ~ spl12_119
    | spl12_73 ),
    inference(avatar_split_clause,[],[f5403,f434,f637,f2602,f619,f616,f640])).

fof(f640,plain,
    ( spl12_121
  <=> ~ l1_struct_0(sK6(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_121])])).

fof(f637,plain,
    ( spl12_119
  <=> ~ l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_119])])).

fof(f434,plain,
    ( spl12_73
  <=> ~ v1_funct_2(k2_tmap_1(sK0,sK6(sK0,sK1,sK2),sK7(sK0,sK1,sK2),sK0),u1_struct_0(sK0),u1_struct_0(sK6(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_73])])).

fof(f5403,plain,
    ( ~ l1_struct_0(sK0)
    | ~ m1_subset_1(sK7(sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK6(sK0,sK1,sK2)))))
    | ~ v1_funct_2(sK7(sK0,sK1,sK2),u1_struct_0(sK0),u1_struct_0(sK6(sK0,sK1,sK2)))
    | ~ v1_funct_1(sK7(sK0,sK1,sK2))
    | ~ l1_struct_0(sK6(sK0,sK1,sK2))
    | ~ spl12_73 ),
    inference(duplicate_literal_removal,[],[f5402])).

fof(f5402,plain,
    ( ~ l1_struct_0(sK0)
    | ~ m1_subset_1(sK7(sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK6(sK0,sK1,sK2)))))
    | ~ v1_funct_2(sK7(sK0,sK1,sK2),u1_struct_0(sK0),u1_struct_0(sK6(sK0,sK1,sK2)))
    | ~ v1_funct_1(sK7(sK0,sK1,sK2))
    | ~ l1_struct_0(sK6(sK0,sK1,sK2))
    | ~ l1_struct_0(sK0)
    | ~ spl12_73 ),
    inference(resolution,[],[f435,f234])).

fof(f234,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f97])).

fof(f97,plain,(
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
    inference(flattening,[],[f96])).

fof(f96,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/tmap_1__t137_tmap_1.p',dt_k2_tmap_1)).

fof(f435,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,sK6(sK0,sK1,sK2),sK7(sK0,sK1,sK2),sK0),u1_struct_0(sK0),u1_struct_0(sK6(sK0,sK1,sK2)))
    | ~ spl12_73 ),
    inference(avatar_component_clause,[],[f434])).

fof(f5348,plain,
    ( spl12_36
    | ~ spl12_39
    | ~ spl12_41
    | spl12_42
    | ~ spl12_45
    | spl12_46
    | ~ spl12_49
    | ~ spl12_3
    | spl12_0
    | ~ spl12_119
    | ~ spl12_71
    | ~ spl12_73
    | ~ spl12_75
    | ~ spl12_124 ),
    inference(avatar_split_clause,[],[f5347,f647,f437,f434,f431,f637,f326,f254,f380,f377,f374,f371,f368,f365,f362])).

fof(f371,plain,
    ( spl12_42
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_42])])).

fof(f374,plain,
    ( spl12_45
  <=> ~ m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_45])])).

fof(f377,plain,
    ( spl12_46
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_46])])).

fof(f380,plain,
    ( spl12_49
  <=> ~ m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_49])])).

fof(f254,plain,
    ( spl12_3
  <=> ~ r1_tsep_1(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_3])])).

fof(f326,plain,
    ( spl12_0
  <=> r3_tsep_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_0])])).

fof(f437,plain,
    ( spl12_75
  <=> ~ v1_funct_1(k2_tmap_1(sK0,sK6(sK0,sK1,sK2),sK7(sK0,sK1,sK2),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_75])])).

fof(f647,plain,
    ( spl12_124
  <=> ! [X4] :
        ( ~ l1_struct_0(X4)
        | m1_subset_1(k2_tmap_1(sK0,sK6(sK0,sK1,sK2),sK7(sK0,sK1,sK2),X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK6(sK0,sK1,sK2))))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_124])])).

fof(f5347,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK0,sK6(sK0,sK1,sK2),sK7(sK0,sK1,sK2),sK0))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK6(sK0,sK1,sK2),sK7(sK0,sK1,sK2),sK0),u1_struct_0(sK0),u1_struct_0(sK6(sK0,sK1,sK2)))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK6(sK0,sK1,sK2),sK7(sK0,sK1,sK2),sK0),sK0,sK6(sK0,sK1,sK2))
    | ~ l1_struct_0(sK0)
    | r3_tsep_1(sK0,sK1,sK2)
    | ~ r1_tsep_1(sK1,sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_124 ),
    inference(forward_demodulation,[],[f5346,f138])).

fof(f138,plain,(
    k1_tsep_1(sK0,sK1,sK2) = sK0 ),
    inference(cnf_transformation,[],[f110])).

fof(f110,plain,
    ( ( ( ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK3))))
          | ~ v5_pre_topc(sK4,sK0,sK3)
          | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK3))
          | ~ v1_funct_1(sK4) )
        & m1_subset_1(k2_tmap_1(sK0,sK3,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
        & v5_pre_topc(k2_tmap_1(sK0,sK3,sK4,sK2),sK2,sK3)
        & v1_funct_2(k2_tmap_1(sK0,sK3,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK3))
        & v1_funct_1(k2_tmap_1(sK0,sK3,sK4,sK2))
        & m1_subset_1(k2_tmap_1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK3))))
        & v5_pre_topc(k2_tmap_1(sK0,sK3,sK4,sK1),sK1,sK3)
        & v1_funct_2(k2_tmap_1(sK0,sK3,sK4,sK1),u1_struct_0(sK1),u1_struct_0(sK3))
        & v1_funct_1(k2_tmap_1(sK0,sK3,sK4,sK1))
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK3))))
        & v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK3))
        & v1_funct_1(sK4)
        & l1_pre_topc(sK3)
        & v2_pre_topc(sK3)
        & ~ v2_struct_0(sK3) )
      | ~ r1_tsep_1(sK1,sK2)
      | ~ r3_tsep_1(sK0,sK1,sK2) )
    & ( ( ! [X5] :
            ( ! [X6] :
                ( ( m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X5))))
                  & v5_pre_topc(X6,sK0,X5)
                  & v1_funct_2(X6,u1_struct_0(sK0),u1_struct_0(X5))
                  & v1_funct_1(X6) )
                | ~ m1_subset_1(k2_tmap_1(sK0,X5,X6,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X5))))
                | ~ v5_pre_topc(k2_tmap_1(sK0,X5,X6,sK2),sK2,X5)
                | ~ v1_funct_2(k2_tmap_1(sK0,X5,X6,sK2),u1_struct_0(sK2),u1_struct_0(X5))
                | ~ v1_funct_1(k2_tmap_1(sK0,X5,X6,sK2))
                | ~ m1_subset_1(k2_tmap_1(sK0,X5,X6,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X5))))
                | ~ v5_pre_topc(k2_tmap_1(sK0,X5,X6,sK1),sK1,X5)
                | ~ v1_funct_2(k2_tmap_1(sK0,X5,X6,sK1),u1_struct_0(sK1),u1_struct_0(X5))
                | ~ v1_funct_1(k2_tmap_1(sK0,X5,X6,sK1))
                | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X5))))
                | ~ v1_funct_2(X6,u1_struct_0(sK0),u1_struct_0(X5))
                | ~ v1_funct_1(X6) )
            | ~ l1_pre_topc(X5)
            | ~ v2_pre_topc(X5)
            | v2_struct_0(X5) )
        & r1_tsep_1(sK1,sK2) )
      | r3_tsep_1(sK0,sK1,sK2) )
    & k1_tsep_1(sK0,sK1,sK2) = sK0
    & m1_pre_topc(sK2,sK0)
    & ~ v2_struct_0(sK2)
    & m1_pre_topc(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f104,f109,f108,f107,f106,f105])).

fof(f105,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ? [X3] :
                      ( ? [X4] :
                          ( ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
                            | ~ v5_pre_topc(X4,X0,X3)
                            | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3))
                            | ~ v1_funct_1(X4) )
                          & m1_subset_1(k2_tmap_1(X0,X3,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                          & v5_pre_topc(k2_tmap_1(X0,X3,X4,X2),X2,X3)
                          & v1_funct_2(k2_tmap_1(X0,X3,X4,X2),u1_struct_0(X2),u1_struct_0(X3))
                          & v1_funct_1(k2_tmap_1(X0,X3,X4,X2))
                          & m1_subset_1(k2_tmap_1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                          & v5_pre_topc(k2_tmap_1(X0,X3,X4,X1),X1,X3)
                          & v1_funct_2(k2_tmap_1(X0,X3,X4,X1),u1_struct_0(X1),u1_struct_0(X3))
                          & v1_funct_1(k2_tmap_1(X0,X3,X4,X1))
                          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
                          & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3))
                          & v1_funct_1(X4) )
                      & l1_pre_topc(X3)
                      & v2_pre_topc(X3)
                      & ~ v2_struct_0(X3) )
                  | ~ r1_tsep_1(X1,X2)
                  | ~ r3_tsep_1(X0,X1,X2) )
                & ( ( ! [X5] :
                        ( ! [X6] :
                            ( ( m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X5))))
                              & v5_pre_topc(X6,X0,X5)
                              & v1_funct_2(X6,u1_struct_0(X0),u1_struct_0(X5))
                              & v1_funct_1(X6) )
                            | ~ m1_subset_1(k2_tmap_1(X0,X5,X6,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X5))))
                            | ~ v5_pre_topc(k2_tmap_1(X0,X5,X6,X2),X2,X5)
                            | ~ v1_funct_2(k2_tmap_1(X0,X5,X6,X2),u1_struct_0(X2),u1_struct_0(X5))
                            | ~ v1_funct_1(k2_tmap_1(X0,X5,X6,X2))
                            | ~ m1_subset_1(k2_tmap_1(X0,X5,X6,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X5))))
                            | ~ v5_pre_topc(k2_tmap_1(X0,X5,X6,X1),X1,X5)
                            | ~ v1_funct_2(k2_tmap_1(X0,X5,X6,X1),u1_struct_0(X1),u1_struct_0(X5))
                            | ~ v1_funct_1(k2_tmap_1(X0,X5,X6,X1))
                            | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X5))))
                            | ~ v1_funct_2(X6,u1_struct_0(X0),u1_struct_0(X5))
                            | ~ v1_funct_1(X6) )
                        | ~ l1_pre_topc(X5)
                        | ~ v2_pre_topc(X5)
                        | v2_struct_0(X5) )
                    & r1_tsep_1(X1,X2) )
                  | r3_tsep_1(X0,X1,X2) )
                & k1_tsep_1(X0,X1,X2) = X0
                & m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ? [X4] :
                        ( ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X3))))
                          | ~ v5_pre_topc(X4,sK0,X3)
                          | ~ v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X3))
                          | ~ v1_funct_1(X4) )
                        & m1_subset_1(k2_tmap_1(sK0,X3,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                        & v5_pre_topc(k2_tmap_1(sK0,X3,X4,X2),X2,X3)
                        & v1_funct_2(k2_tmap_1(sK0,X3,X4,X2),u1_struct_0(X2),u1_struct_0(X3))
                        & v1_funct_1(k2_tmap_1(sK0,X3,X4,X2))
                        & m1_subset_1(k2_tmap_1(sK0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                        & v5_pre_topc(k2_tmap_1(sK0,X3,X4,X1),X1,X3)
                        & v1_funct_2(k2_tmap_1(sK0,X3,X4,X1),u1_struct_0(X1),u1_struct_0(X3))
                        & v1_funct_1(k2_tmap_1(sK0,X3,X4,X1))
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X3))))
                        & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X3))
                        & v1_funct_1(X4) )
                    & l1_pre_topc(X3)
                    & v2_pre_topc(X3)
                    & ~ v2_struct_0(X3) )
                | ~ r1_tsep_1(X1,X2)
                | ~ r3_tsep_1(sK0,X1,X2) )
              & ( ( ! [X5] :
                      ( ! [X6] :
                          ( ( m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X5))))
                            & v5_pre_topc(X6,sK0,X5)
                            & v1_funct_2(X6,u1_struct_0(sK0),u1_struct_0(X5))
                            & v1_funct_1(X6) )
                          | ~ m1_subset_1(k2_tmap_1(sK0,X5,X6,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X5))))
                          | ~ v5_pre_topc(k2_tmap_1(sK0,X5,X6,X2),X2,X5)
                          | ~ v1_funct_2(k2_tmap_1(sK0,X5,X6,X2),u1_struct_0(X2),u1_struct_0(X5))
                          | ~ v1_funct_1(k2_tmap_1(sK0,X5,X6,X2))
                          | ~ m1_subset_1(k2_tmap_1(sK0,X5,X6,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X5))))
                          | ~ v5_pre_topc(k2_tmap_1(sK0,X5,X6,X1),X1,X5)
                          | ~ v1_funct_2(k2_tmap_1(sK0,X5,X6,X1),u1_struct_0(X1),u1_struct_0(X5))
                          | ~ v1_funct_1(k2_tmap_1(sK0,X5,X6,X1))
                          | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X5))))
                          | ~ v1_funct_2(X6,u1_struct_0(sK0),u1_struct_0(X5))
                          | ~ v1_funct_1(X6) )
                      | ~ l1_pre_topc(X5)
                      | ~ v2_pre_topc(X5)
                      | v2_struct_0(X5) )
                  & r1_tsep_1(X1,X2) )
                | r3_tsep_1(sK0,X1,X2) )
              & k1_tsep_1(sK0,X1,X2) = sK0
              & m1_pre_topc(X2,sK0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,sK0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f106,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ? [X4] :
                        ( ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
                          | ~ v5_pre_topc(X4,X0,X3)
                          | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3))
                          | ~ v1_funct_1(X4) )
                        & m1_subset_1(k2_tmap_1(X0,X3,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                        & v5_pre_topc(k2_tmap_1(X0,X3,X4,X2),X2,X3)
                        & v1_funct_2(k2_tmap_1(X0,X3,X4,X2),u1_struct_0(X2),u1_struct_0(X3))
                        & v1_funct_1(k2_tmap_1(X0,X3,X4,X2))
                        & m1_subset_1(k2_tmap_1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                        & v5_pre_topc(k2_tmap_1(X0,X3,X4,X1),X1,X3)
                        & v1_funct_2(k2_tmap_1(X0,X3,X4,X1),u1_struct_0(X1),u1_struct_0(X3))
                        & v1_funct_1(k2_tmap_1(X0,X3,X4,X1))
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
                        & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3))
                        & v1_funct_1(X4) )
                    & l1_pre_topc(X3)
                    & v2_pre_topc(X3)
                    & ~ v2_struct_0(X3) )
                | ~ r1_tsep_1(X1,X2)
                | ~ r3_tsep_1(X0,X1,X2) )
              & ( ( ! [X5] :
                      ( ! [X6] :
                          ( ( m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X5))))
                            & v5_pre_topc(X6,X0,X5)
                            & v1_funct_2(X6,u1_struct_0(X0),u1_struct_0(X5))
                            & v1_funct_1(X6) )
                          | ~ m1_subset_1(k2_tmap_1(X0,X5,X6,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X5))))
                          | ~ v5_pre_topc(k2_tmap_1(X0,X5,X6,X2),X2,X5)
                          | ~ v1_funct_2(k2_tmap_1(X0,X5,X6,X2),u1_struct_0(X2),u1_struct_0(X5))
                          | ~ v1_funct_1(k2_tmap_1(X0,X5,X6,X2))
                          | ~ m1_subset_1(k2_tmap_1(X0,X5,X6,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X5))))
                          | ~ v5_pre_topc(k2_tmap_1(X0,X5,X6,X1),X1,X5)
                          | ~ v1_funct_2(k2_tmap_1(X0,X5,X6,X1),u1_struct_0(X1),u1_struct_0(X5))
                          | ~ v1_funct_1(k2_tmap_1(X0,X5,X6,X1))
                          | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X5))))
                          | ~ v1_funct_2(X6,u1_struct_0(X0),u1_struct_0(X5))
                          | ~ v1_funct_1(X6) )
                      | ~ l1_pre_topc(X5)
                      | ~ v2_pre_topc(X5)
                      | v2_struct_0(X5) )
                  & r1_tsep_1(X1,X2) )
                | r3_tsep_1(X0,X1,X2) )
              & k1_tsep_1(X0,X1,X2) = X0
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ( ? [X3] :
                  ( ? [X4] :
                      ( ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
                        | ~ v5_pre_topc(X4,X0,X3)
                        | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3))
                        | ~ v1_funct_1(X4) )
                      & m1_subset_1(k2_tmap_1(X0,X3,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                      & v5_pre_topc(k2_tmap_1(X0,X3,X4,X2),X2,X3)
                      & v1_funct_2(k2_tmap_1(X0,X3,X4,X2),u1_struct_0(X2),u1_struct_0(X3))
                      & v1_funct_1(k2_tmap_1(X0,X3,X4,X2))
                      & m1_subset_1(k2_tmap_1(X0,X3,X4,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X3))))
                      & v5_pre_topc(k2_tmap_1(X0,X3,X4,sK1),sK1,X3)
                      & v1_funct_2(k2_tmap_1(X0,X3,X4,sK1),u1_struct_0(sK1),u1_struct_0(X3))
                      & v1_funct_1(k2_tmap_1(X0,X3,X4,sK1))
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
                      & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3))
                      & v1_funct_1(X4) )
                  & l1_pre_topc(X3)
                  & v2_pre_topc(X3)
                  & ~ v2_struct_0(X3) )
              | ~ r1_tsep_1(sK1,X2)
              | ~ r3_tsep_1(X0,sK1,X2) )
            & ( ( ! [X5] :
                    ( ! [X6] :
                        ( ( m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X5))))
                          & v5_pre_topc(X6,X0,X5)
                          & v1_funct_2(X6,u1_struct_0(X0),u1_struct_0(X5))
                          & v1_funct_1(X6) )
                        | ~ m1_subset_1(k2_tmap_1(X0,X5,X6,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X5))))
                        | ~ v5_pre_topc(k2_tmap_1(X0,X5,X6,X2),X2,X5)
                        | ~ v1_funct_2(k2_tmap_1(X0,X5,X6,X2),u1_struct_0(X2),u1_struct_0(X5))
                        | ~ v1_funct_1(k2_tmap_1(X0,X5,X6,X2))
                        | ~ m1_subset_1(k2_tmap_1(X0,X5,X6,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X5))))
                        | ~ v5_pre_topc(k2_tmap_1(X0,X5,X6,sK1),sK1,X5)
                        | ~ v1_funct_2(k2_tmap_1(X0,X5,X6,sK1),u1_struct_0(sK1),u1_struct_0(X5))
                        | ~ v1_funct_1(k2_tmap_1(X0,X5,X6,sK1))
                        | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X5))))
                        | ~ v1_funct_2(X6,u1_struct_0(X0),u1_struct_0(X5))
                        | ~ v1_funct_1(X6) )
                    | ~ l1_pre_topc(X5)
                    | ~ v2_pre_topc(X5)
                    | v2_struct_0(X5) )
                & r1_tsep_1(sK1,X2) )
              | r3_tsep_1(X0,sK1,X2) )
            & k1_tsep_1(X0,sK1,X2) = X0
            & m1_pre_topc(X2,X0)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(sK1,X0)
        & ~ v2_struct_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f107,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ? [X3] :
                ( ? [X4] :
                    ( ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
                      | ~ v5_pre_topc(X4,X0,X3)
                      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3))
                      | ~ v1_funct_1(X4) )
                    & m1_subset_1(k2_tmap_1(X0,X3,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                    & v5_pre_topc(k2_tmap_1(X0,X3,X4,X2),X2,X3)
                    & v1_funct_2(k2_tmap_1(X0,X3,X4,X2),u1_struct_0(X2),u1_struct_0(X3))
                    & v1_funct_1(k2_tmap_1(X0,X3,X4,X2))
                    & m1_subset_1(k2_tmap_1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                    & v5_pre_topc(k2_tmap_1(X0,X3,X4,X1),X1,X3)
                    & v1_funct_2(k2_tmap_1(X0,X3,X4,X1),u1_struct_0(X1),u1_struct_0(X3))
                    & v1_funct_1(k2_tmap_1(X0,X3,X4,X1))
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
                    & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3))
                    & v1_funct_1(X4) )
                & l1_pre_topc(X3)
                & v2_pre_topc(X3)
                & ~ v2_struct_0(X3) )
            | ~ r1_tsep_1(X1,X2)
            | ~ r3_tsep_1(X0,X1,X2) )
          & ( ( ! [X5] :
                  ( ! [X6] :
                      ( ( m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X5))))
                        & v5_pre_topc(X6,X0,X5)
                        & v1_funct_2(X6,u1_struct_0(X0),u1_struct_0(X5))
                        & v1_funct_1(X6) )
                      | ~ m1_subset_1(k2_tmap_1(X0,X5,X6,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X5))))
                      | ~ v5_pre_topc(k2_tmap_1(X0,X5,X6,X2),X2,X5)
                      | ~ v1_funct_2(k2_tmap_1(X0,X5,X6,X2),u1_struct_0(X2),u1_struct_0(X5))
                      | ~ v1_funct_1(k2_tmap_1(X0,X5,X6,X2))
                      | ~ m1_subset_1(k2_tmap_1(X0,X5,X6,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X5))))
                      | ~ v5_pre_topc(k2_tmap_1(X0,X5,X6,X1),X1,X5)
                      | ~ v1_funct_2(k2_tmap_1(X0,X5,X6,X1),u1_struct_0(X1),u1_struct_0(X5))
                      | ~ v1_funct_1(k2_tmap_1(X0,X5,X6,X1))
                      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X5))))
                      | ~ v1_funct_2(X6,u1_struct_0(X0),u1_struct_0(X5))
                      | ~ v1_funct_1(X6) )
                  | ~ l1_pre_topc(X5)
                  | ~ v2_pre_topc(X5)
                  | v2_struct_0(X5) )
              & r1_tsep_1(X1,X2) )
            | r3_tsep_1(X0,X1,X2) )
          & k1_tsep_1(X0,X1,X2) = X0
          & m1_pre_topc(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( ( ? [X3] :
              ( ? [X4] :
                  ( ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
                    | ~ v5_pre_topc(X4,X0,X3)
                    | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3))
                    | ~ v1_funct_1(X4) )
                  & m1_subset_1(k2_tmap_1(X0,X3,X4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X3))))
                  & v5_pre_topc(k2_tmap_1(X0,X3,X4,sK2),sK2,X3)
                  & v1_funct_2(k2_tmap_1(X0,X3,X4,sK2),u1_struct_0(sK2),u1_struct_0(X3))
                  & v1_funct_1(k2_tmap_1(X0,X3,X4,sK2))
                  & m1_subset_1(k2_tmap_1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                  & v5_pre_topc(k2_tmap_1(X0,X3,X4,X1),X1,X3)
                  & v1_funct_2(k2_tmap_1(X0,X3,X4,X1),u1_struct_0(X1),u1_struct_0(X3))
                  & v1_funct_1(k2_tmap_1(X0,X3,X4,X1))
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
                  & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3))
                  & v1_funct_1(X4) )
              & l1_pre_topc(X3)
              & v2_pre_topc(X3)
              & ~ v2_struct_0(X3) )
          | ~ r1_tsep_1(X1,sK2)
          | ~ r3_tsep_1(X0,X1,sK2) )
        & ( ( ! [X5] :
                ( ! [X6] :
                    ( ( m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X5))))
                      & v5_pre_topc(X6,X0,X5)
                      & v1_funct_2(X6,u1_struct_0(X0),u1_struct_0(X5))
                      & v1_funct_1(X6) )
                    | ~ m1_subset_1(k2_tmap_1(X0,X5,X6,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X5))))
                    | ~ v5_pre_topc(k2_tmap_1(X0,X5,X6,sK2),sK2,X5)
                    | ~ v1_funct_2(k2_tmap_1(X0,X5,X6,sK2),u1_struct_0(sK2),u1_struct_0(X5))
                    | ~ v1_funct_1(k2_tmap_1(X0,X5,X6,sK2))
                    | ~ m1_subset_1(k2_tmap_1(X0,X5,X6,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X5))))
                    | ~ v5_pre_topc(k2_tmap_1(X0,X5,X6,X1),X1,X5)
                    | ~ v1_funct_2(k2_tmap_1(X0,X5,X6,X1),u1_struct_0(X1),u1_struct_0(X5))
                    | ~ v1_funct_1(k2_tmap_1(X0,X5,X6,X1))
                    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X5))))
                    | ~ v1_funct_2(X6,u1_struct_0(X0),u1_struct_0(X5))
                    | ~ v1_funct_1(X6) )
                | ~ l1_pre_topc(X5)
                | ~ v2_pre_topc(X5)
                | v2_struct_0(X5) )
            & r1_tsep_1(X1,sK2) )
          | r3_tsep_1(X0,X1,sK2) )
        & k1_tsep_1(X0,X1,sK2) = X0
        & m1_pre_topc(sK2,X0)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
                | ~ v5_pre_topc(X4,X0,X3)
                | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3))
                | ~ v1_funct_1(X4) )
              & m1_subset_1(k2_tmap_1(X0,X3,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
              & v5_pre_topc(k2_tmap_1(X0,X3,X4,X2),X2,X3)
              & v1_funct_2(k2_tmap_1(X0,X3,X4,X2),u1_struct_0(X2),u1_struct_0(X3))
              & v1_funct_1(k2_tmap_1(X0,X3,X4,X2))
              & m1_subset_1(k2_tmap_1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
              & v5_pre_topc(k2_tmap_1(X0,X3,X4,X1),X1,X3)
              & v1_funct_2(k2_tmap_1(X0,X3,X4,X1),u1_struct_0(X1),u1_struct_0(X3))
              & v1_funct_1(k2_tmap_1(X0,X3,X4,X1))
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
              & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3))
              & v1_funct_1(X4) )
          & l1_pre_topc(X3)
          & v2_pre_topc(X3)
          & ~ v2_struct_0(X3) )
     => ( ? [X4] :
            ( ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
              | ~ v5_pre_topc(X4,X0,sK3)
              | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(sK3))
              | ~ v1_funct_1(X4) )
            & m1_subset_1(k2_tmap_1(X0,sK3,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK3))))
            & v5_pre_topc(k2_tmap_1(X0,sK3,X4,X2),X2,sK3)
            & v1_funct_2(k2_tmap_1(X0,sK3,X4,X2),u1_struct_0(X2),u1_struct_0(sK3))
            & v1_funct_1(k2_tmap_1(X0,sK3,X4,X2))
            & m1_subset_1(k2_tmap_1(X0,sK3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3))))
            & v5_pre_topc(k2_tmap_1(X0,sK3,X4,X1),X1,sK3)
            & v1_funct_2(k2_tmap_1(X0,sK3,X4,X1),u1_struct_0(X1),u1_struct_0(sK3))
            & v1_funct_1(k2_tmap_1(X0,sK3,X4,X1))
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
            & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(sK3))
            & v1_funct_1(X4) )
        & l1_pre_topc(sK3)
        & v2_pre_topc(sK3)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f109,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
            | ~ v5_pre_topc(X4,X0,X3)
            | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3))
            | ~ v1_funct_1(X4) )
          & m1_subset_1(k2_tmap_1(X0,X3,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
          & v5_pre_topc(k2_tmap_1(X0,X3,X4,X2),X2,X3)
          & v1_funct_2(k2_tmap_1(X0,X3,X4,X2),u1_struct_0(X2),u1_struct_0(X3))
          & v1_funct_1(k2_tmap_1(X0,X3,X4,X2))
          & m1_subset_1(k2_tmap_1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
          & v5_pre_topc(k2_tmap_1(X0,X3,X4,X1),X1,X3)
          & v1_funct_2(k2_tmap_1(X0,X3,X4,X1),u1_struct_0(X1),u1_struct_0(X3))
          & v1_funct_1(k2_tmap_1(X0,X3,X4,X1))
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
          & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3))
          & v1_funct_1(X4) )
     => ( ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
          | ~ v5_pre_topc(sK4,X0,X3)
          | ~ v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X3))
          | ~ v1_funct_1(sK4) )
        & m1_subset_1(k2_tmap_1(X0,X3,sK4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
        & v5_pre_topc(k2_tmap_1(X0,X3,sK4,X2),X2,X3)
        & v1_funct_2(k2_tmap_1(X0,X3,sK4,X2),u1_struct_0(X2),u1_struct_0(X3))
        & v1_funct_1(k2_tmap_1(X0,X3,sK4,X2))
        & m1_subset_1(k2_tmap_1(X0,X3,sK4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
        & v5_pre_topc(k2_tmap_1(X0,X3,sK4,X1),X1,X3)
        & v1_funct_2(k2_tmap_1(X0,X3,sK4,X1),u1_struct_0(X1),u1_struct_0(X3))
        & v1_funct_1(k2_tmap_1(X0,X3,sK4,X1))
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
        & v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X3))
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f104,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ? [X4] :
                        ( ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
                          | ~ v5_pre_topc(X4,X0,X3)
                          | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3))
                          | ~ v1_funct_1(X4) )
                        & m1_subset_1(k2_tmap_1(X0,X3,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                        & v5_pre_topc(k2_tmap_1(X0,X3,X4,X2),X2,X3)
                        & v1_funct_2(k2_tmap_1(X0,X3,X4,X2),u1_struct_0(X2),u1_struct_0(X3))
                        & v1_funct_1(k2_tmap_1(X0,X3,X4,X2))
                        & m1_subset_1(k2_tmap_1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                        & v5_pre_topc(k2_tmap_1(X0,X3,X4,X1),X1,X3)
                        & v1_funct_2(k2_tmap_1(X0,X3,X4,X1),u1_struct_0(X1),u1_struct_0(X3))
                        & v1_funct_1(k2_tmap_1(X0,X3,X4,X1))
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
                        & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3))
                        & v1_funct_1(X4) )
                    & l1_pre_topc(X3)
                    & v2_pre_topc(X3)
                    & ~ v2_struct_0(X3) )
                | ~ r1_tsep_1(X1,X2)
                | ~ r3_tsep_1(X0,X1,X2) )
              & ( ( ! [X5] :
                      ( ! [X6] :
                          ( ( m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X5))))
                            & v5_pre_topc(X6,X0,X5)
                            & v1_funct_2(X6,u1_struct_0(X0),u1_struct_0(X5))
                            & v1_funct_1(X6) )
                          | ~ m1_subset_1(k2_tmap_1(X0,X5,X6,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X5))))
                          | ~ v5_pre_topc(k2_tmap_1(X0,X5,X6,X2),X2,X5)
                          | ~ v1_funct_2(k2_tmap_1(X0,X5,X6,X2),u1_struct_0(X2),u1_struct_0(X5))
                          | ~ v1_funct_1(k2_tmap_1(X0,X5,X6,X2))
                          | ~ m1_subset_1(k2_tmap_1(X0,X5,X6,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X5))))
                          | ~ v5_pre_topc(k2_tmap_1(X0,X5,X6,X1),X1,X5)
                          | ~ v1_funct_2(k2_tmap_1(X0,X5,X6,X1),u1_struct_0(X1),u1_struct_0(X5))
                          | ~ v1_funct_1(k2_tmap_1(X0,X5,X6,X1))
                          | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X5))))
                          | ~ v1_funct_2(X6,u1_struct_0(X0),u1_struct_0(X5))
                          | ~ v1_funct_1(X6) )
                      | ~ l1_pre_topc(X5)
                      | ~ v2_pre_topc(X5)
                      | v2_struct_0(X5) )
                  & r1_tsep_1(X1,X2) )
                | r3_tsep_1(X0,X1,X2) )
              & k1_tsep_1(X0,X1,X2) = X0
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(rectify,[],[f103])).

fof(f103,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ? [X4] :
                        ( ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
                          | ~ v5_pre_topc(X4,X0,X3)
                          | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3))
                          | ~ v1_funct_1(X4) )
                        & m1_subset_1(k2_tmap_1(X0,X3,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                        & v5_pre_topc(k2_tmap_1(X0,X3,X4,X2),X2,X3)
                        & v1_funct_2(k2_tmap_1(X0,X3,X4,X2),u1_struct_0(X2),u1_struct_0(X3))
                        & v1_funct_1(k2_tmap_1(X0,X3,X4,X2))
                        & m1_subset_1(k2_tmap_1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                        & v5_pre_topc(k2_tmap_1(X0,X3,X4,X1),X1,X3)
                        & v1_funct_2(k2_tmap_1(X0,X3,X4,X1),u1_struct_0(X1),u1_struct_0(X3))
                        & v1_funct_1(k2_tmap_1(X0,X3,X4,X1))
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
                        & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3))
                        & v1_funct_1(X4) )
                    & l1_pre_topc(X3)
                    & v2_pre_topc(X3)
                    & ~ v2_struct_0(X3) )
                | ~ r1_tsep_1(X1,X2)
                | ~ r3_tsep_1(X0,X1,X2) )
              & ( ( ! [X3] :
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
                  & r1_tsep_1(X1,X2) )
                | r3_tsep_1(X0,X1,X2) )
              & k1_tsep_1(X0,X1,X2) = X0
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f102])).

fof(f102,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ? [X4] :
                        ( ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
                          | ~ v5_pre_topc(X4,X0,X3)
                          | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3))
                          | ~ v1_funct_1(X4) )
                        & m1_subset_1(k2_tmap_1(X0,X3,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                        & v5_pre_topc(k2_tmap_1(X0,X3,X4,X2),X2,X3)
                        & v1_funct_2(k2_tmap_1(X0,X3,X4,X2),u1_struct_0(X2),u1_struct_0(X3))
                        & v1_funct_1(k2_tmap_1(X0,X3,X4,X2))
                        & m1_subset_1(k2_tmap_1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                        & v5_pre_topc(k2_tmap_1(X0,X3,X4,X1),X1,X3)
                        & v1_funct_2(k2_tmap_1(X0,X3,X4,X1),u1_struct_0(X1),u1_struct_0(X3))
                        & v1_funct_1(k2_tmap_1(X0,X3,X4,X1))
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
                        & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3))
                        & v1_funct_1(X4) )
                    & l1_pre_topc(X3)
                    & v2_pre_topc(X3)
                    & ~ v2_struct_0(X3) )
                | ~ r1_tsep_1(X1,X2)
                | ~ r3_tsep_1(X0,X1,X2) )
              & ( ( ! [X3] :
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
                  & r1_tsep_1(X1,X2) )
                | r3_tsep_1(X0,X1,X2) )
              & k1_tsep_1(X0,X1,X2) = X0
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f50])).

fof(f50,plain,(
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
    inference(flattening,[],[f49])).

fof(f49,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
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
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/tmap_1__t137_tmap_1.p',t137_tmap_1)).

fof(f5346,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,sK6(sK0,sK1,sK2),sK7(sK0,sK1,sK2),sK0),u1_struct_0(sK0),u1_struct_0(sK6(sK0,sK1,sK2)))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK6(sK0,sK1,sK2),sK7(sK0,sK1,sK2),sK0),sK0,sK6(sK0,sK1,sK2))
    | ~ l1_struct_0(sK0)
    | r3_tsep_1(sK0,sK1,sK2)
    | ~ v1_funct_1(k2_tmap_1(sK0,sK6(sK0,sK1,sK2),sK7(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2)))
    | ~ r1_tsep_1(sK1,sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_124 ),
    inference(forward_demodulation,[],[f5345,f138])).

fof(f5345,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK0,sK6(sK0,sK1,sK2),sK7(sK0,sK1,sK2),sK0),sK0,sK6(sK0,sK1,sK2))
    | ~ l1_struct_0(sK0)
    | r3_tsep_1(sK0,sK1,sK2)
    | ~ v1_funct_2(k2_tmap_1(sK0,sK6(sK0,sK1,sK2),sK7(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK6(sK0,sK1,sK2)))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK6(sK0,sK1,sK2),sK7(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2)))
    | ~ r1_tsep_1(sK1,sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_124 ),
    inference(forward_demodulation,[],[f5344,f138])).

fof(f5344,plain,
    ( ~ l1_struct_0(sK0)
    | r3_tsep_1(sK0,sK1,sK2)
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK6(sK0,sK1,sK2),sK7(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2)),k1_tsep_1(sK0,sK1,sK2),sK6(sK0,sK1,sK2))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK6(sK0,sK1,sK2),sK7(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK6(sK0,sK1,sK2)))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK6(sK0,sK1,sK2),sK7(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2)))
    | ~ r1_tsep_1(sK1,sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_124 ),
    inference(forward_demodulation,[],[f5312,f138])).

fof(f5312,plain,
    ( ~ l1_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | r3_tsep_1(sK0,sK1,sK2)
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK6(sK0,sK1,sK2),sK7(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2)),k1_tsep_1(sK0,sK1,sK2),sK6(sK0,sK1,sK2))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK6(sK0,sK1,sK2),sK7(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK6(sK0,sK1,sK2)))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK6(sK0,sK1,sK2),sK7(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2)))
    | ~ r1_tsep_1(sK1,sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_124 ),
    inference(resolution,[],[f648,f200])).

fof(f200,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k2_tmap_1(X0,sK6(X0,X1,X2),sK7(X0,X1,X2),k1_tsep_1(X0,X1,X2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(sK6(X0,X1,X2)))))
      | r3_tsep_1(X0,X1,X2)
      | ~ v5_pre_topc(k2_tmap_1(X0,sK6(X0,X1,X2),sK7(X0,X1,X2),k1_tsep_1(X0,X1,X2)),k1_tsep_1(X0,X1,X2),sK6(X0,X1,X2))
      | ~ v1_funct_2(k2_tmap_1(X0,sK6(X0,X1,X2),sK7(X0,X1,X2),k1_tsep_1(X0,X1,X2)),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(sK6(X0,X1,X2)))
      | ~ v1_funct_1(k2_tmap_1(X0,sK6(X0,X1,X2),sK7(X0,X1,X2),k1_tsep_1(X0,X1,X2)))
      | ~ r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f120])).

fof(f120,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r3_tsep_1(X0,X1,X2)
                  | ( ( ~ m1_subset_1(k2_tmap_1(X0,sK6(X0,X1,X2),sK7(X0,X1,X2),k1_tsep_1(X0,X1,X2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(sK6(X0,X1,X2)))))
                      | ~ v5_pre_topc(k2_tmap_1(X0,sK6(X0,X1,X2),sK7(X0,X1,X2),k1_tsep_1(X0,X1,X2)),k1_tsep_1(X0,X1,X2),sK6(X0,X1,X2))
                      | ~ v1_funct_2(k2_tmap_1(X0,sK6(X0,X1,X2),sK7(X0,X1,X2),k1_tsep_1(X0,X1,X2)),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(sK6(X0,X1,X2)))
                      | ~ v1_funct_1(k2_tmap_1(X0,sK6(X0,X1,X2),sK7(X0,X1,X2),k1_tsep_1(X0,X1,X2))) )
                    & m1_subset_1(k2_tmap_1(X0,sK6(X0,X1,X2),sK7(X0,X1,X2),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK6(X0,X1,X2)))))
                    & v5_pre_topc(k2_tmap_1(X0,sK6(X0,X1,X2),sK7(X0,X1,X2),X2),X2,sK6(X0,X1,X2))
                    & v1_funct_2(k2_tmap_1(X0,sK6(X0,X1,X2),sK7(X0,X1,X2),X2),u1_struct_0(X2),u1_struct_0(sK6(X0,X1,X2)))
                    & v1_funct_1(k2_tmap_1(X0,sK6(X0,X1,X2),sK7(X0,X1,X2),X2))
                    & m1_subset_1(k2_tmap_1(X0,sK6(X0,X1,X2),sK7(X0,X1,X2),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK6(X0,X1,X2)))))
                    & v5_pre_topc(k2_tmap_1(X0,sK6(X0,X1,X2),sK7(X0,X1,X2),X1),X1,sK6(X0,X1,X2))
                    & v1_funct_2(k2_tmap_1(X0,sK6(X0,X1,X2),sK7(X0,X1,X2),X1),u1_struct_0(X1),u1_struct_0(sK6(X0,X1,X2)))
                    & v1_funct_1(k2_tmap_1(X0,sK6(X0,X1,X2),sK7(X0,X1,X2),X1))
                    & m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK6(X0,X1,X2)))))
                    & v1_funct_2(sK7(X0,X1,X2),u1_struct_0(X0),u1_struct_0(sK6(X0,X1,X2)))
                    & v1_funct_1(sK7(X0,X1,X2))
                    & l1_pre_topc(sK6(X0,X1,X2))
                    & v2_pre_topc(sK6(X0,X1,X2))
                    & ~ v2_struct_0(sK6(X0,X1,X2)) )
                  | ~ r1_tsep_1(X1,X2) )
                & ( ( ! [X5] :
                        ( ! [X6] :
                            ( ( m1_subset_1(k2_tmap_1(X0,X5,X6,k1_tsep_1(X0,X1,X2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X5))))
                              & v5_pre_topc(k2_tmap_1(X0,X5,X6,k1_tsep_1(X0,X1,X2)),k1_tsep_1(X0,X1,X2),X5)
                              & v1_funct_2(k2_tmap_1(X0,X5,X6,k1_tsep_1(X0,X1,X2)),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X5))
                              & v1_funct_1(k2_tmap_1(X0,X5,X6,k1_tsep_1(X0,X1,X2))) )
                            | ~ m1_subset_1(k2_tmap_1(X0,X5,X6,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X5))))
                            | ~ v5_pre_topc(k2_tmap_1(X0,X5,X6,X2),X2,X5)
                            | ~ v1_funct_2(k2_tmap_1(X0,X5,X6,X2),u1_struct_0(X2),u1_struct_0(X5))
                            | ~ v1_funct_1(k2_tmap_1(X0,X5,X6,X2))
                            | ~ m1_subset_1(k2_tmap_1(X0,X5,X6,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X5))))
                            | ~ v5_pre_topc(k2_tmap_1(X0,X5,X6,X1),X1,X5)
                            | ~ v1_funct_2(k2_tmap_1(X0,X5,X6,X1),u1_struct_0(X1),u1_struct_0(X5))
                            | ~ v1_funct_1(k2_tmap_1(X0,X5,X6,X1))
                            | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X5))))
                            | ~ v1_funct_2(X6,u1_struct_0(X0),u1_struct_0(X5))
                            | ~ v1_funct_1(X6) )
                        | ~ l1_pre_topc(X5)
                        | ~ v2_pre_topc(X5)
                        | v2_struct_0(X5) )
                    & r1_tsep_1(X1,X2) )
                  | ~ r3_tsep_1(X0,X1,X2) ) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f117,f119,f118])).

fof(f118,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ? [X4] :
              ( ( ~ m1_subset_1(k2_tmap_1(X0,X3,X4,k1_tsep_1(X0,X1,X2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                | ~ v5_pre_topc(k2_tmap_1(X0,X3,X4,k1_tsep_1(X0,X1,X2)),k1_tsep_1(X0,X1,X2),X3)
                | ~ v1_funct_2(k2_tmap_1(X0,X3,X4,k1_tsep_1(X0,X1,X2)),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                | ~ v1_funct_1(k2_tmap_1(X0,X3,X4,k1_tsep_1(X0,X1,X2))) )
              & m1_subset_1(k2_tmap_1(X0,X3,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
              & v5_pre_topc(k2_tmap_1(X0,X3,X4,X2),X2,X3)
              & v1_funct_2(k2_tmap_1(X0,X3,X4,X2),u1_struct_0(X2),u1_struct_0(X3))
              & v1_funct_1(k2_tmap_1(X0,X3,X4,X2))
              & m1_subset_1(k2_tmap_1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
              & v5_pre_topc(k2_tmap_1(X0,X3,X4,X1),X1,X3)
              & v1_funct_2(k2_tmap_1(X0,X3,X4,X1),u1_struct_0(X1),u1_struct_0(X3))
              & v1_funct_1(k2_tmap_1(X0,X3,X4,X1))
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
              & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3))
              & v1_funct_1(X4) )
          & l1_pre_topc(X3)
          & v2_pre_topc(X3)
          & ~ v2_struct_0(X3) )
     => ( ? [X4] :
            ( ( ~ m1_subset_1(k2_tmap_1(X0,sK6(X0,X1,X2),X4,k1_tsep_1(X0,X1,X2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(sK6(X0,X1,X2)))))
              | ~ v5_pre_topc(k2_tmap_1(X0,sK6(X0,X1,X2),X4,k1_tsep_1(X0,X1,X2)),k1_tsep_1(X0,X1,X2),sK6(X0,X1,X2))
              | ~ v1_funct_2(k2_tmap_1(X0,sK6(X0,X1,X2),X4,k1_tsep_1(X0,X1,X2)),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(sK6(X0,X1,X2)))
              | ~ v1_funct_1(k2_tmap_1(X0,sK6(X0,X1,X2),X4,k1_tsep_1(X0,X1,X2))) )
            & m1_subset_1(k2_tmap_1(X0,sK6(X0,X1,X2),X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK6(X0,X1,X2)))))
            & v5_pre_topc(k2_tmap_1(X0,sK6(X0,X1,X2),X4,X2),X2,sK6(X0,X1,X2))
            & v1_funct_2(k2_tmap_1(X0,sK6(X0,X1,X2),X4,X2),u1_struct_0(X2),u1_struct_0(sK6(X0,X1,X2)))
            & v1_funct_1(k2_tmap_1(X0,sK6(X0,X1,X2),X4,X2))
            & m1_subset_1(k2_tmap_1(X0,sK6(X0,X1,X2),X4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK6(X0,X1,X2)))))
            & v5_pre_topc(k2_tmap_1(X0,sK6(X0,X1,X2),X4,X1),X1,sK6(X0,X1,X2))
            & v1_funct_2(k2_tmap_1(X0,sK6(X0,X1,X2),X4,X1),u1_struct_0(X1),u1_struct_0(sK6(X0,X1,X2)))
            & v1_funct_1(k2_tmap_1(X0,sK6(X0,X1,X2),X4,X1))
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK6(X0,X1,X2)))))
            & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(sK6(X0,X1,X2)))
            & v1_funct_1(X4) )
        & l1_pre_topc(sK6(X0,X1,X2))
        & v2_pre_topc(sK6(X0,X1,X2))
        & ~ v2_struct_0(sK6(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f119,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ~ m1_subset_1(k2_tmap_1(X0,X3,X4,k1_tsep_1(X0,X1,X2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
            | ~ v5_pre_topc(k2_tmap_1(X0,X3,X4,k1_tsep_1(X0,X1,X2)),k1_tsep_1(X0,X1,X2),X3)
            | ~ v1_funct_2(k2_tmap_1(X0,X3,X4,k1_tsep_1(X0,X1,X2)),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
            | ~ v1_funct_1(k2_tmap_1(X0,X3,X4,k1_tsep_1(X0,X1,X2))) )
          & m1_subset_1(k2_tmap_1(X0,X3,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
          & v5_pre_topc(k2_tmap_1(X0,X3,X4,X2),X2,X3)
          & v1_funct_2(k2_tmap_1(X0,X3,X4,X2),u1_struct_0(X2),u1_struct_0(X3))
          & v1_funct_1(k2_tmap_1(X0,X3,X4,X2))
          & m1_subset_1(k2_tmap_1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
          & v5_pre_topc(k2_tmap_1(X0,X3,X4,X1),X1,X3)
          & v1_funct_2(k2_tmap_1(X0,X3,X4,X1),u1_struct_0(X1),u1_struct_0(X3))
          & v1_funct_1(k2_tmap_1(X0,X3,X4,X1))
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
          & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3))
          & v1_funct_1(X4) )
     => ( ( ~ m1_subset_1(k2_tmap_1(X0,X3,sK7(X0,X1,X2),k1_tsep_1(X0,X1,X2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
          | ~ v5_pre_topc(k2_tmap_1(X0,X3,sK7(X0,X1,X2),k1_tsep_1(X0,X1,X2)),k1_tsep_1(X0,X1,X2),X3)
          | ~ v1_funct_2(k2_tmap_1(X0,X3,sK7(X0,X1,X2),k1_tsep_1(X0,X1,X2)),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
          | ~ v1_funct_1(k2_tmap_1(X0,X3,sK7(X0,X1,X2),k1_tsep_1(X0,X1,X2))) )
        & m1_subset_1(k2_tmap_1(X0,X3,sK7(X0,X1,X2),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
        & v5_pre_topc(k2_tmap_1(X0,X3,sK7(X0,X1,X2),X2),X2,X3)
        & v1_funct_2(k2_tmap_1(X0,X3,sK7(X0,X1,X2),X2),u1_struct_0(X2),u1_struct_0(X3))
        & v1_funct_1(k2_tmap_1(X0,X3,sK7(X0,X1,X2),X2))
        & m1_subset_1(k2_tmap_1(X0,X3,sK7(X0,X1,X2),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
        & v5_pre_topc(k2_tmap_1(X0,X3,sK7(X0,X1,X2),X1),X1,X3)
        & v1_funct_2(k2_tmap_1(X0,X3,sK7(X0,X1,X2),X1),u1_struct_0(X1),u1_struct_0(X3))
        & v1_funct_1(k2_tmap_1(X0,X3,sK7(X0,X1,X2),X1))
        & m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
        & v1_funct_2(sK7(X0,X1,X2),u1_struct_0(X0),u1_struct_0(X3))
        & v1_funct_1(sK7(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f117,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r3_tsep_1(X0,X1,X2)
                  | ? [X3] :
                      ( ? [X4] :
                          ( ( ~ m1_subset_1(k2_tmap_1(X0,X3,X4,k1_tsep_1(X0,X1,X2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                            | ~ v5_pre_topc(k2_tmap_1(X0,X3,X4,k1_tsep_1(X0,X1,X2)),k1_tsep_1(X0,X1,X2),X3)
                            | ~ v1_funct_2(k2_tmap_1(X0,X3,X4,k1_tsep_1(X0,X1,X2)),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                            | ~ v1_funct_1(k2_tmap_1(X0,X3,X4,k1_tsep_1(X0,X1,X2))) )
                          & m1_subset_1(k2_tmap_1(X0,X3,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                          & v5_pre_topc(k2_tmap_1(X0,X3,X4,X2),X2,X3)
                          & v1_funct_2(k2_tmap_1(X0,X3,X4,X2),u1_struct_0(X2),u1_struct_0(X3))
                          & v1_funct_1(k2_tmap_1(X0,X3,X4,X2))
                          & m1_subset_1(k2_tmap_1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                          & v5_pre_topc(k2_tmap_1(X0,X3,X4,X1),X1,X3)
                          & v1_funct_2(k2_tmap_1(X0,X3,X4,X1),u1_struct_0(X1),u1_struct_0(X3))
                          & v1_funct_1(k2_tmap_1(X0,X3,X4,X1))
                          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
                          & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3))
                          & v1_funct_1(X4) )
                      & l1_pre_topc(X3)
                      & v2_pre_topc(X3)
                      & ~ v2_struct_0(X3) )
                  | ~ r1_tsep_1(X1,X2) )
                & ( ( ! [X5] :
                        ( ! [X6] :
                            ( ( m1_subset_1(k2_tmap_1(X0,X5,X6,k1_tsep_1(X0,X1,X2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X5))))
                              & v5_pre_topc(k2_tmap_1(X0,X5,X6,k1_tsep_1(X0,X1,X2)),k1_tsep_1(X0,X1,X2),X5)
                              & v1_funct_2(k2_tmap_1(X0,X5,X6,k1_tsep_1(X0,X1,X2)),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X5))
                              & v1_funct_1(k2_tmap_1(X0,X5,X6,k1_tsep_1(X0,X1,X2))) )
                            | ~ m1_subset_1(k2_tmap_1(X0,X5,X6,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X5))))
                            | ~ v5_pre_topc(k2_tmap_1(X0,X5,X6,X2),X2,X5)
                            | ~ v1_funct_2(k2_tmap_1(X0,X5,X6,X2),u1_struct_0(X2),u1_struct_0(X5))
                            | ~ v1_funct_1(k2_tmap_1(X0,X5,X6,X2))
                            | ~ m1_subset_1(k2_tmap_1(X0,X5,X6,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X5))))
                            | ~ v5_pre_topc(k2_tmap_1(X0,X5,X6,X1),X1,X5)
                            | ~ v1_funct_2(k2_tmap_1(X0,X5,X6,X1),u1_struct_0(X1),u1_struct_0(X5))
                            | ~ v1_funct_1(k2_tmap_1(X0,X5,X6,X1))
                            | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X5))))
                            | ~ v1_funct_2(X6,u1_struct_0(X0),u1_struct_0(X5))
                            | ~ v1_funct_1(X6) )
                        | ~ l1_pre_topc(X5)
                        | ~ v2_pre_topc(X5)
                        | v2_struct_0(X5) )
                    & r1_tsep_1(X1,X2) )
                  | ~ r3_tsep_1(X0,X1,X2) ) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f116])).

fof(f116,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r3_tsep_1(X0,X1,X2)
                  | ? [X3] :
                      ( ? [X4] :
                          ( ( ~ m1_subset_1(k2_tmap_1(X0,X3,X4,k1_tsep_1(X0,X1,X2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                            | ~ v5_pre_topc(k2_tmap_1(X0,X3,X4,k1_tsep_1(X0,X1,X2)),k1_tsep_1(X0,X1,X2),X3)
                            | ~ v1_funct_2(k2_tmap_1(X0,X3,X4,k1_tsep_1(X0,X1,X2)),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                            | ~ v1_funct_1(k2_tmap_1(X0,X3,X4,k1_tsep_1(X0,X1,X2))) )
                          & m1_subset_1(k2_tmap_1(X0,X3,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                          & v5_pre_topc(k2_tmap_1(X0,X3,X4,X2),X2,X3)
                          & v1_funct_2(k2_tmap_1(X0,X3,X4,X2),u1_struct_0(X2),u1_struct_0(X3))
                          & v1_funct_1(k2_tmap_1(X0,X3,X4,X2))
                          & m1_subset_1(k2_tmap_1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                          & v5_pre_topc(k2_tmap_1(X0,X3,X4,X1),X1,X3)
                          & v1_funct_2(k2_tmap_1(X0,X3,X4,X1),u1_struct_0(X1),u1_struct_0(X3))
                          & v1_funct_1(k2_tmap_1(X0,X3,X4,X1))
                          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
                          & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3))
                          & v1_funct_1(X4) )
                      & l1_pre_topc(X3)
                      & v2_pre_topc(X3)
                      & ~ v2_struct_0(X3) )
                  | ~ r1_tsep_1(X1,X2) )
                & ( ( ! [X3] :
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
                    & r1_tsep_1(X1,X2) )
                  | ~ r3_tsep_1(X0,X1,X2) ) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f115])).

fof(f115,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r3_tsep_1(X0,X1,X2)
                  | ? [X3] :
                      ( ? [X4] :
                          ( ( ~ m1_subset_1(k2_tmap_1(X0,X3,X4,k1_tsep_1(X0,X1,X2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                            | ~ v5_pre_topc(k2_tmap_1(X0,X3,X4,k1_tsep_1(X0,X1,X2)),k1_tsep_1(X0,X1,X2),X3)
                            | ~ v1_funct_2(k2_tmap_1(X0,X3,X4,k1_tsep_1(X0,X1,X2)),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                            | ~ v1_funct_1(k2_tmap_1(X0,X3,X4,k1_tsep_1(X0,X1,X2))) )
                          & m1_subset_1(k2_tmap_1(X0,X3,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                          & v5_pre_topc(k2_tmap_1(X0,X3,X4,X2),X2,X3)
                          & v1_funct_2(k2_tmap_1(X0,X3,X4,X2),u1_struct_0(X2),u1_struct_0(X3))
                          & v1_funct_1(k2_tmap_1(X0,X3,X4,X2))
                          & m1_subset_1(k2_tmap_1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                          & v5_pre_topc(k2_tmap_1(X0,X3,X4,X1),X1,X3)
                          & v1_funct_2(k2_tmap_1(X0,X3,X4,X1),u1_struct_0(X1),u1_struct_0(X3))
                          & v1_funct_1(k2_tmap_1(X0,X3,X4,X1))
                          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
                          & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3))
                          & v1_funct_1(X4) )
                      & l1_pre_topc(X3)
                      & v2_pre_topc(X3)
                      & ~ v2_struct_0(X3) )
                  | ~ r1_tsep_1(X1,X2) )
                & ( ( ! [X3] :
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
                    & r1_tsep_1(X1,X2) )
                  | ~ r3_tsep_1(X0,X1,X2) ) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f65])).

fof(f65,plain,(
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
    inference(flattening,[],[f64])).

fof(f64,plain,(
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
    inference(ennf_transformation,[],[f33])).

fof(f33,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/tmap_1__t137_tmap_1.p',t136_tmap_1)).

fof(f648,plain,
    ( ! [X4] :
        ( m1_subset_1(k2_tmap_1(sK0,sK6(sK0,sK1,sK2),sK7(sK0,sK1,sK2),X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK6(sK0,sK1,sK2)))))
        | ~ l1_struct_0(X4) )
    | ~ spl12_124 ),
    inference(avatar_component_clause,[],[f647])).

fof(f4881,plain,
    ( spl12_36
    | spl12_74
    | ~ spl12_114 ),
    inference(avatar_split_clause,[],[f4859,f629,f4879,f362])).

fof(f4879,plain,
    ( spl12_74
  <=> v1_funct_1(k2_tmap_1(sK0,sK6(sK0,sK1,sK2),sK7(sK0,sK1,sK2),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_74])])).

fof(f629,plain,
    ( spl12_114
  <=> ! [X1] :
        ( ~ m1_pre_topc(X1,sK0)
        | v1_funct_1(k2_tmap_1(sK0,sK6(sK0,sK1,sK2),sK7(sK0,sK1,sK2),X1))
        | v2_struct_0(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_114])])).

fof(f4859,plain,
    ( v1_funct_1(k2_tmap_1(sK0,sK6(sK0,sK1,sK2),sK7(sK0,sK1,sK2),sK0))
    | v2_struct_0(sK0)
    | ~ spl12_114 ),
    inference(resolution,[],[f630,f422])).

fof(f422,plain,(
    m1_pre_topc(sK0,sK0) ),
    inference(global_subsumption,[],[f131,f133,f134,f136,f135,f137,f419])).

fof(f419,plain,
    ( m1_pre_topc(sK0,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f225,f138])).

fof(f225,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f86])).

fof(f86,plain,(
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
    inference(flattening,[],[f85])).

fof(f85,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/tmap_1__t137_tmap_1.p',dt_k1_tsep_1)).

fof(f137,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f110])).

fof(f135,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f110])).

fof(f136,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f110])).

fof(f134,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f110])).

fof(f133,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f110])).

fof(f131,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f110])).

fof(f630,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(X1,sK0)
        | v1_funct_1(k2_tmap_1(sK0,sK6(sK0,sK1,sK2),sK7(sK0,sK1,sK2),X1))
        | v2_struct_0(X1) )
    | ~ spl12_114 ),
    inference(avatar_component_clause,[],[f629])).

fof(f4856,plain,
    ( spl12_36
    | ~ spl12_39
    | ~ spl12_41
    | spl12_42
    | ~ spl12_45
    | spl12_46
    | ~ spl12_49
    | ~ spl12_3
    | spl12_0
    | spl12_477 ),
    inference(avatar_split_clause,[],[f4854,f1768,f326,f254,f380,f377,f374,f371,f368,f365,f362])).

fof(f1768,plain,
    ( spl12_477
  <=> ~ v5_pre_topc(k2_tmap_1(sK0,sK6(sK0,sK1,sK2),sK7(sK0,sK1,sK2),sK2),sK2,sK6(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_477])])).

fof(f4854,plain,
    ( r3_tsep_1(sK0,sK1,sK2)
    | ~ r1_tsep_1(sK1,sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_477 ),
    inference(resolution,[],[f1769,f198])).

fof(f198,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(k2_tmap_1(X0,sK6(X0,X1,X2),sK7(X0,X1,X2),X2),X2,sK6(X0,X1,X2))
      | r3_tsep_1(X0,X1,X2)
      | ~ r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f120])).

fof(f1769,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK0,sK6(sK0,sK1,sK2),sK7(sK0,sK1,sK2),sK2),sK2,sK6(sK0,sK1,sK2))
    | ~ spl12_477 ),
    inference(avatar_component_clause,[],[f1768])).

fof(f4852,plain,
    ( spl12_36
    | ~ spl12_39
    | ~ spl12_41
    | spl12_42
    | ~ spl12_45
    | spl12_46
    | ~ spl12_49
    | ~ spl12_3
    | spl12_0
    | spl12_473 ),
    inference(avatar_split_clause,[],[f4850,f1761,f326,f254,f380,f377,f374,f371,f368,f365,f362])).

fof(f1761,plain,
    ( spl12_473
  <=> ~ v1_funct_2(k2_tmap_1(sK0,sK6(sK0,sK1,sK2),sK7(sK0,sK1,sK2),sK2),u1_struct_0(sK2),u1_struct_0(sK6(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_473])])).

fof(f4850,plain,
    ( r3_tsep_1(sK0,sK1,sK2)
    | ~ r1_tsep_1(sK1,sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_473 ),
    inference(resolution,[],[f1762,f197])).

fof(f197,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_tmap_1(X0,sK6(X0,X1,X2),sK7(X0,X1,X2),X2),u1_struct_0(X2),u1_struct_0(sK6(X0,X1,X2)))
      | r3_tsep_1(X0,X1,X2)
      | ~ r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f120])).

fof(f1762,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,sK6(sK0,sK1,sK2),sK7(sK0,sK1,sK2),sK2),u1_struct_0(sK2),u1_struct_0(sK6(sK0,sK1,sK2)))
    | ~ spl12_473 ),
    inference(avatar_component_clause,[],[f1761])).

fof(f4849,plain,
    ( spl12_36
    | ~ spl12_39
    | ~ spl12_41
    | spl12_42
    | ~ spl12_45
    | spl12_46
    | ~ spl12_49
    | ~ spl12_3
    | spl12_0
    | spl12_439 ),
    inference(avatar_split_clause,[],[f4847,f1671,f326,f254,f380,f377,f374,f371,f368,f365,f362])).

fof(f1671,plain,
    ( spl12_439
  <=> ~ v5_pre_topc(k2_tmap_1(sK0,sK6(sK0,sK1,sK2),sK7(sK0,sK1,sK2),sK1),sK1,sK6(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_439])])).

fof(f4847,plain,
    ( r3_tsep_1(sK0,sK1,sK2)
    | ~ r1_tsep_1(sK1,sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_439 ),
    inference(resolution,[],[f1672,f194])).

fof(f194,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(k2_tmap_1(X0,sK6(X0,X1,X2),sK7(X0,X1,X2),X1),X1,sK6(X0,X1,X2))
      | r3_tsep_1(X0,X1,X2)
      | ~ r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f120])).

fof(f1672,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK0,sK6(sK0,sK1,sK2),sK7(sK0,sK1,sK2),sK1),sK1,sK6(sK0,sK1,sK2))
    | ~ spl12_439 ),
    inference(avatar_component_clause,[],[f1671])).

fof(f4846,plain,
    ( spl12_36
    | ~ spl12_39
    | ~ spl12_41
    | spl12_42
    | ~ spl12_45
    | spl12_46
    | ~ spl12_49
    | ~ spl12_3
    | spl12_0
    | ~ spl12_106 ),
    inference(avatar_split_clause,[],[f4845,f607,f326,f254,f380,f377,f374,f371,f368,f365,f362])).

fof(f4845,plain,
    ( r3_tsep_1(sK0,sK1,sK2)
    | ~ r1_tsep_1(sK1,sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_106 ),
    inference(resolution,[],[f608,f186])).

fof(f186,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(sK6(X0,X1,X2))
      | r3_tsep_1(X0,X1,X2)
      | ~ r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f120])).

fof(f608,plain,
    ( v2_struct_0(sK6(sK0,sK1,sK2))
    | ~ spl12_106 ),
    inference(avatar_component_clause,[],[f607])).

fof(f4843,plain,
    ( spl12_36
    | ~ spl12_39
    | ~ spl12_41
    | spl12_42
    | ~ spl12_45
    | spl12_46
    | ~ spl12_49
    | ~ spl12_3
    | spl12_0
    | spl12_435 ),
    inference(avatar_split_clause,[],[f4841,f1664,f326,f254,f380,f377,f374,f371,f368,f365,f362])).

fof(f1664,plain,
    ( spl12_435
  <=> ~ v1_funct_2(k2_tmap_1(sK0,sK6(sK0,sK1,sK2),sK7(sK0,sK1,sK2),sK1),u1_struct_0(sK1),u1_struct_0(sK6(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_435])])).

fof(f4841,plain,
    ( r3_tsep_1(sK0,sK1,sK2)
    | ~ r1_tsep_1(sK1,sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_435 ),
    inference(resolution,[],[f1665,f193])).

fof(f193,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_tmap_1(X0,sK6(X0,X1,X2),sK7(X0,X1,X2),X1),u1_struct_0(X1),u1_struct_0(sK6(X0,X1,X2)))
      | r3_tsep_1(X0,X1,X2)
      | ~ r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f120])).

fof(f1665,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,sK6(sK0,sK1,sK2),sK7(sK0,sK1,sK2),sK1),u1_struct_0(sK1),u1_struct_0(sK6(sK0,sK1,sK2)))
    | ~ spl12_435 ),
    inference(avatar_component_clause,[],[f1664])).

fof(f4743,plain,
    ( spl12_112
    | ~ spl12_477
    | ~ spl12_473
    | ~ spl12_63
    | ~ spl12_61
    | ~ spl12_439
    | ~ spl12_435
    | ~ spl12_59
    | ~ spl12_57
    | ~ spl12_109
    | ~ spl12_55
    | ~ spl12_53
    | ~ spl12_51
    | spl12_106
    | ~ spl12_34
    | ~ spl12_64 ),
    inference(avatar_split_clause,[],[f4720,f411,f329,f607,f610,f613,f616,f619,f2602,f1661,f1664,f1671,f2656,f1758,f1761,f1768,f2608])).

fof(f2608,plain,
    ( spl12_112
  <=> v5_pre_topc(sK7(sK0,sK1,sK2),sK0,sK6(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_112])])).

fof(f1758,plain,
    ( spl12_63
  <=> ~ v1_funct_1(k2_tmap_1(sK0,sK6(sK0,sK1,sK2),sK7(sK0,sK1,sK2),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_63])])).

fof(f2656,plain,
    ( spl12_61
  <=> ~ m1_subset_1(k2_tmap_1(sK0,sK6(sK0,sK1,sK2),sK7(sK0,sK1,sK2),sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK6(sK0,sK1,sK2))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_61])])).

fof(f1661,plain,
    ( spl12_59
  <=> ~ v1_funct_1(k2_tmap_1(sK0,sK6(sK0,sK1,sK2),sK7(sK0,sK1,sK2),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_59])])).

fof(f329,plain,
    ( spl12_34
  <=> ! [X5,X6] :
        ( v5_pre_topc(X6,sK0,X5)
        | v2_struct_0(X5)
        | ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X5)
        | ~ v1_funct_1(X6)
        | ~ v1_funct_2(X6,u1_struct_0(sK0),u1_struct_0(X5))
        | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X5))))
        | ~ v1_funct_1(k2_tmap_1(sK0,X5,X6,sK1))
        | ~ v1_funct_2(k2_tmap_1(sK0,X5,X6,sK1),u1_struct_0(sK1),u1_struct_0(X5))
        | ~ v5_pre_topc(k2_tmap_1(sK0,X5,X6,sK1),sK1,X5)
        | ~ m1_subset_1(k2_tmap_1(sK0,X5,X6,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X5))))
        | ~ v1_funct_1(k2_tmap_1(sK0,X5,X6,sK2))
        | ~ v1_funct_2(k2_tmap_1(sK0,X5,X6,sK2),u1_struct_0(sK2),u1_struct_0(X5))
        | ~ v5_pre_topc(k2_tmap_1(sK0,X5,X6,sK2),sK2,X5)
        | ~ m1_subset_1(k2_tmap_1(sK0,X5,X6,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X5)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_34])])).

fof(f411,plain,
    ( spl12_64
  <=> m1_subset_1(k2_tmap_1(sK0,sK6(sK0,sK1,sK2),sK7(sK0,sK1,sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK6(sK0,sK1,sK2))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_64])])).

fof(f4720,plain,
    ( v2_struct_0(sK6(sK0,sK1,sK2))
    | ~ v2_pre_topc(sK6(sK0,sK1,sK2))
    | ~ l1_pre_topc(sK6(sK0,sK1,sK2))
    | ~ v1_funct_1(sK7(sK0,sK1,sK2))
    | ~ v1_funct_2(sK7(sK0,sK1,sK2),u1_struct_0(sK0),u1_struct_0(sK6(sK0,sK1,sK2)))
    | ~ m1_subset_1(sK7(sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK6(sK0,sK1,sK2)))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK6(sK0,sK1,sK2),sK7(sK0,sK1,sK2),sK1))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK6(sK0,sK1,sK2),sK7(sK0,sK1,sK2),sK1),u1_struct_0(sK1),u1_struct_0(sK6(sK0,sK1,sK2)))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK6(sK0,sK1,sK2),sK7(sK0,sK1,sK2),sK1),sK1,sK6(sK0,sK1,sK2))
    | ~ m1_subset_1(k2_tmap_1(sK0,sK6(sK0,sK1,sK2),sK7(sK0,sK1,sK2),sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK6(sK0,sK1,sK2)))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK6(sK0,sK1,sK2),sK7(sK0,sK1,sK2),sK2))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK6(sK0,sK1,sK2),sK7(sK0,sK1,sK2),sK2),u1_struct_0(sK2),u1_struct_0(sK6(sK0,sK1,sK2)))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK6(sK0,sK1,sK2),sK7(sK0,sK1,sK2),sK2),sK2,sK6(sK0,sK1,sK2))
    | v5_pre_topc(sK7(sK0,sK1,sK2),sK0,sK6(sK0,sK1,sK2))
    | ~ spl12_34
    | ~ spl12_64 ),
    inference(resolution,[],[f412,f330])).

fof(f330,plain,
    ( ! [X6,X5] :
        ( ~ m1_subset_1(k2_tmap_1(sK0,X5,X6,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X5))))
        | v2_struct_0(X5)
        | ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X5)
        | ~ v1_funct_1(X6)
        | ~ v1_funct_2(X6,u1_struct_0(sK0),u1_struct_0(X5))
        | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X5))))
        | ~ v1_funct_1(k2_tmap_1(sK0,X5,X6,sK1))
        | ~ v1_funct_2(k2_tmap_1(sK0,X5,X6,sK1),u1_struct_0(sK1),u1_struct_0(X5))
        | ~ v5_pre_topc(k2_tmap_1(sK0,X5,X6,sK1),sK1,X5)
        | ~ m1_subset_1(k2_tmap_1(sK0,X5,X6,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X5))))
        | ~ v1_funct_1(k2_tmap_1(sK0,X5,X6,sK2))
        | ~ v1_funct_2(k2_tmap_1(sK0,X5,X6,sK2),u1_struct_0(sK2),u1_struct_0(X5))
        | ~ v5_pre_topc(k2_tmap_1(sK0,X5,X6,sK2),sK2,X5)
        | v5_pre_topc(X6,sK0,X5) )
    | ~ spl12_34 ),
    inference(avatar_component_clause,[],[f329])).

fof(f412,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK6(sK0,sK1,sK2),sK7(sK0,sK1,sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK6(sK0,sK1,sK2)))))
    | ~ spl12_64 ),
    inference(avatar_component_clause,[],[f411])).

fof(f4668,plain,
    ( ~ spl12_119
    | ~ spl12_121
    | ~ spl12_55
    | ~ spl12_109
    | spl12_124
    | ~ spl12_56 ),
    inference(avatar_split_clause,[],[f4651,f395,f647,f619,f616,f640,f637])).

fof(f395,plain,
    ( spl12_56
  <=> m1_subset_1(sK7(sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK6(sK0,sK1,sK2))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_56])])).

fof(f4651,plain,
    ( ! [X4] :
        ( ~ l1_struct_0(X4)
        | m1_subset_1(k2_tmap_1(sK0,sK6(sK0,sK1,sK2),sK7(sK0,sK1,sK2),X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK6(sK0,sK1,sK2)))))
        | ~ v1_funct_2(sK7(sK0,sK1,sK2),u1_struct_0(sK0),u1_struct_0(sK6(sK0,sK1,sK2)))
        | ~ v1_funct_1(sK7(sK0,sK1,sK2))
        | ~ l1_struct_0(sK6(sK0,sK1,sK2))
        | ~ l1_struct_0(sK0) )
    | ~ spl12_56 ),
    inference(resolution,[],[f396,f235])).

fof(f235,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_struct_0(X3)
      | m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f97])).

fof(f396,plain,
    ( m1_subset_1(sK7(sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK6(sK0,sK1,sK2)))))
    | ~ spl12_56 ),
    inference(avatar_component_clause,[],[f395])).

fof(f4665,plain,
    ( spl12_36
    | ~ spl12_39
    | ~ spl12_41
    | spl12_106
    | ~ spl12_51
    | ~ spl12_53
    | ~ spl12_55
    | ~ spl12_109
    | ~ spl12_113
    | spl12_114
    | ~ spl12_56 ),
    inference(avatar_split_clause,[],[f4648,f395,f629,f626,f619,f616,f613,f610,f607,f368,f365,f362])).

fof(f4648,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | v1_funct_1(k2_tmap_1(sK0,sK6(sK0,sK1,sK2),sK7(sK0,sK1,sK2),X1))
        | ~ v5_pre_topc(sK7(sK0,sK1,sK2),sK0,sK6(sK0,sK1,sK2))
        | ~ v1_funct_2(sK7(sK0,sK1,sK2),u1_struct_0(sK0),u1_struct_0(sK6(sK0,sK1,sK2)))
        | ~ v1_funct_1(sK7(sK0,sK1,sK2))
        | ~ l1_pre_topc(sK6(sK0,sK1,sK2))
        | ~ v2_pre_topc(sK6(sK0,sK1,sK2))
        | v2_struct_0(sK6(sK0,sK1,sK2))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl12_56 ),
    inference(resolution,[],[f396,f230])).

fof(f230,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | v1_funct_1(k2_tmap_1(X0,X1,X2,X3))
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f95])).

fof(f3968,plain,
    ( ~ spl12_52
    | spl12_121 ),
    inference(avatar_contradiction_clause,[],[f3967])).

fof(f3967,plain,
    ( $false
    | ~ spl12_52
    | ~ spl12_121 ),
    inference(subsumption_resolution,[],[f388,f3966])).

fof(f3966,plain,
    ( ~ l1_pre_topc(sK6(sK0,sK1,sK2))
    | ~ spl12_121 ),
    inference(resolution,[],[f641,f162])).

fof(f162,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t137_tmap_1.p',dt_l1_pre_topc)).

fof(f641,plain,
    ( ~ l1_struct_0(sK6(sK0,sK1,sK2))
    | ~ spl12_121 ),
    inference(avatar_component_clause,[],[f640])).

fof(f388,plain,
    ( l1_pre_topc(sK6(sK0,sK1,sK2))
    | ~ spl12_52 ),
    inference(avatar_component_clause,[],[f387])).

fof(f387,plain,
    ( spl12_52
  <=> l1_pre_topc(sK6(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_52])])).

fof(f3965,plain,
    ( spl12_36
    | ~ spl12_39
    | ~ spl12_41
    | spl12_42
    | ~ spl12_45
    | spl12_46
    | ~ spl12_49
    | ~ spl12_3
    | spl12_0
    | spl12_109 ),
    inference(avatar_split_clause,[],[f3964,f619,f326,f254,f380,f377,f374,f371,f368,f365,f362])).

fof(f3964,plain,
    ( r3_tsep_1(sK0,sK1,sK2)
    | ~ r1_tsep_1(sK1,sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_109 ),
    inference(resolution,[],[f620,f190])).

fof(f190,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(sK7(X0,X1,X2),u1_struct_0(X0),u1_struct_0(sK6(X0,X1,X2)))
      | r3_tsep_1(X0,X1,X2)
      | ~ r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f120])).

fof(f620,plain,
    ( ~ v1_funct_2(sK7(sK0,sK1,sK2),u1_struct_0(sK0),u1_struct_0(sK6(sK0,sK1,sK2)))
    | ~ spl12_109 ),
    inference(avatar_component_clause,[],[f619])).

fof(f2677,plain,
    ( ~ spl12_41
    | ~ spl12_45
    | ~ spl12_49
    | ~ spl12_637
    | spl12_639 ),
    inference(avatar_split_clause,[],[f2675,f2555,f2546,f380,f374,f368])).

fof(f2546,plain,
    ( spl12_637
  <=> ~ r4_tsep_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_637])])).

fof(f2555,plain,
    ( spl12_639
  <=> ~ r4_tsep_1(sK0,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_639])])).

fof(f2675,plain,
    ( ~ r4_tsep_1(sK0,sK1,sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl12_639 ),
    inference(resolution,[],[f2556,f226])).

fof(f226,plain,(
    ! [X2,X0,X1] :
      ( r4_tsep_1(X0,X2,X1)
      | ~ r4_tsep_1(X0,X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f88])).

fof(f88,plain,(
    ! [X0,X1,X2] :
      ( r4_tsep_1(X0,X2,X1)
      | ~ r4_tsep_1(X0,X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f87])).

fof(f87,plain,(
    ! [X0,X1,X2] :
      ( r4_tsep_1(X0,X2,X1)
      | ~ r4_tsep_1(X0,X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & m1_pre_topc(X1,X0)
        & l1_pre_topc(X0) )
     => ( r4_tsep_1(X0,X1,X2)
       => r4_tsep_1(X0,X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t137_tmap_1.p',symmetry_r4_tsep_1)).

fof(f2556,plain,
    ( ~ r4_tsep_1(sK0,sK2,sK1)
    | ~ spl12_639 ),
    inference(avatar_component_clause,[],[f2555])).

fof(f2648,plain,
    ( spl12_36
    | ~ spl12_39
    | ~ spl12_41
    | spl12_42
    | ~ spl12_45
    | spl12_46
    | ~ spl12_49
    | ~ spl12_3
    | spl12_54
    | spl12_1 ),
    inference(avatar_split_clause,[],[f2641,f251,f391,f254,f380,f377,f374,f371,f368,f365,f362])).

fof(f391,plain,
    ( spl12_54
  <=> v1_funct_1(sK7(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_54])])).

fof(f251,plain,
    ( spl12_1
  <=> ~ r3_tsep_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).

fof(f2641,plain,
    ( v1_funct_1(sK7(sK0,sK1,sK2))
    | ~ r1_tsep_1(sK1,sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_1 ),
    inference(resolution,[],[f252,f189])).

fof(f189,plain,(
    ! [X2,X0,X1] :
      ( r3_tsep_1(X0,X1,X2)
      | v1_funct_1(sK7(X0,X1,X2))
      | ~ r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f120])).

fof(f252,plain,
    ( ~ r3_tsep_1(sK0,sK1,sK2)
    | ~ spl12_1 ),
    inference(avatar_component_clause,[],[f251])).

fof(f2600,plain,
    ( spl12_36
    | ~ spl12_39
    | ~ spl12_41
    | spl12_42
    | ~ spl12_45
    | spl12_46
    | ~ spl12_49
    | ~ spl12_1
    | spl12_637 ),
    inference(avatar_split_clause,[],[f2598,f2546,f251,f380,f377,f374,f371,f368,f365,f362])).

fof(f2598,plain,
    ( ~ r3_tsep_1(sK0,sK1,sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_637 ),
    inference(resolution,[],[f2547,f203])).

fof(f203,plain,(
    ! [X2,X0,X1] :
      ( r4_tsep_1(X0,X1,X2)
      | ~ r3_tsep_1(X0,X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f122])).

fof(f122,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( r4_tsep_1(X0,X1,X2)
                    & r1_tsep_1(X1,X2) )
                  | ~ r3_tsep_1(X0,X1,X2) )
                & ( r3_tsep_1(X0,X1,X2)
                  | ~ r4_tsep_1(X0,X1,X2)
                  | ~ r1_tsep_1(X1,X2) ) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f121])).

fof(f121,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( r4_tsep_1(X0,X1,X2)
                    & r1_tsep_1(X1,X2) )
                  | ~ r3_tsep_1(X0,X1,X2) )
                & ( r3_tsep_1(X0,X1,X2)
                  | ~ r4_tsep_1(X0,X1,X2)
                  | ~ r1_tsep_1(X1,X2) ) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f67])).

fof(f67,plain,(
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
    inference(flattening,[],[f66])).

fof(f66,plain,(
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
    inference(ennf_transformation,[],[f42])).

fof(f42,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/tmap_1__t137_tmap_1.p',t85_tsep_1)).

fof(f2547,plain,
    ( ~ r4_tsep_1(sK0,sK1,sK2)
    | ~ spl12_637 ),
    inference(avatar_component_clause,[],[f2546])).

fof(f2557,plain,
    ( ~ spl12_15
    | ~ spl12_17
    | ~ spl12_19
    | ~ spl12_639
    | ~ spl12_49
    | spl12_46
    | ~ spl12_12
    | ~ spl12_220 ),
    inference(avatar_split_clause,[],[f2553,f939,f270,f377,f380,f2555,f800,f797,f794])).

fof(f794,plain,
    ( spl12_15
  <=> ~ v5_pre_topc(k2_tmap_1(sK0,sK3,sK4,sK2),sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_15])])).

fof(f797,plain,
    ( spl12_17
  <=> ~ v1_funct_2(k2_tmap_1(sK0,sK3,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_17])])).

fof(f800,plain,
    ( spl12_19
  <=> ~ v1_funct_1(k2_tmap_1(sK0,sK3,sK4,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_19])])).

fof(f270,plain,
    ( spl12_12
  <=> m1_subset_1(k2_tmap_1(sK0,sK3,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_12])])).

fof(f939,plain,
    ( spl12_220
  <=> ! [X3] :
        ( ~ m1_subset_1(k2_tmap_1(sK0,sK3,sK4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3))))
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,sK0)
        | k1_tsep_1(sK0,X3,sK1) != sK0
        | ~ r4_tsep_1(sK0,X3,sK1)
        | ~ v1_funct_1(k2_tmap_1(sK0,sK3,sK4,X3))
        | ~ v1_funct_2(k2_tmap_1(sK0,sK3,sK4,X3),u1_struct_0(X3),u1_struct_0(sK3))
        | ~ v5_pre_topc(k2_tmap_1(sK0,sK3,sK4,X3),X3,sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_220])])).

fof(f2553,plain,
    ( v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ r4_tsep_1(sK0,sK2,sK1)
    | ~ v1_funct_1(k2_tmap_1(sK0,sK3,sK4,sK2))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK3,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK3,sK4,sK2),sK2,sK3)
    | ~ spl12_12
    | ~ spl12_220 ),
    inference(trivial_inequality_removal,[],[f2552])).

fof(f2552,plain,
    ( sK0 != sK0
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ r4_tsep_1(sK0,sK2,sK1)
    | ~ v1_funct_1(k2_tmap_1(sK0,sK3,sK4,sK2))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK3,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK3,sK4,sK2),sK2,sK3)
    | ~ spl12_12
    | ~ spl12_220 ),
    inference(forward_demodulation,[],[f2550,f572])).

fof(f572,plain,(
    k1_tsep_1(sK0,sK2,sK1) = sK0 ),
    inference(global_subsumption,[],[f136,f571])).

fof(f571,plain,
    ( k1_tsep_1(sK0,sK2,sK1) = sK0
    | v2_struct_0(sK2) ),
    inference(forward_demodulation,[],[f567,f138])).

fof(f567,plain,
    ( k1_tsep_1(sK0,sK1,sK2) = k1_tsep_1(sK0,sK2,sK1)
    | v2_struct_0(sK2) ),
    inference(resolution,[],[f341,f137])).

fof(f341,plain,(
    ! [X1] :
      ( ~ m1_pre_topc(X1,sK0)
      | k1_tsep_1(sK0,X1,sK1) = k1_tsep_1(sK0,sK1,X1)
      | v2_struct_0(X1) ) ),
    inference(global_subsumption,[],[f131,f133,f134,f337])).

fof(f337,plain,(
    ! [X1] :
      ( k1_tsep_1(sK0,X1,sK1) = k1_tsep_1(sK0,sK1,X1)
      | v2_struct_0(sK1)
      | ~ m1_pre_topc(X1,sK0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f135,f222])).

fof(f222,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X2,X0)
      | k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f84])).

fof(f84,plain,(
    ! [X0,X1,X2] :
      ( k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f83])).

fof(f83,plain,(
    ! [X0,X1,X2] :
      ( k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t137_tmap_1.p',commutativity_k1_tsep_1)).

fof(f2550,plain,
    ( v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | k1_tsep_1(sK0,sK2,sK1) != sK0
    | ~ r4_tsep_1(sK0,sK2,sK1)
    | ~ v1_funct_1(k2_tmap_1(sK0,sK3,sK4,sK2))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK3,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK3,sK4,sK2),sK2,sK3)
    | ~ spl12_12
    | ~ spl12_220 ),
    inference(resolution,[],[f940,f271])).

fof(f271,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK3,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ spl12_12 ),
    inference(avatar_component_clause,[],[f270])).

fof(f940,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(k2_tmap_1(sK0,sK3,sK4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3))))
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,sK0)
        | k1_tsep_1(sK0,X3,sK1) != sK0
        | ~ r4_tsep_1(sK0,X3,sK1)
        | ~ v1_funct_1(k2_tmap_1(sK0,sK3,sK4,X3))
        | ~ v1_funct_2(k2_tmap_1(sK0,sK3,sK4,X3),u1_struct_0(X3),u1_struct_0(sK3))
        | ~ v5_pre_topc(k2_tmap_1(sK0,sK3,sK4,X3),X3,sK3) )
    | ~ spl12_220 ),
    inference(avatar_component_clause,[],[f939])).

fof(f2476,plain,(
    spl12_611 ),
    inference(avatar_contradiction_clause,[],[f2475])).

fof(f2475,plain,
    ( $false
    | ~ spl12_611 ),
    inference(subsumption_resolution,[],[f422,f2438])).

fof(f2438,plain,
    ( ~ m1_pre_topc(sK0,sK0)
    | ~ spl12_611 ),
    inference(avatar_component_clause,[],[f2437])).

fof(f2185,plain,
    ( spl12_36
    | ~ spl12_39
    | ~ spl12_41
    | spl12_32
    | ~ spl12_31
    | ~ spl12_29
    | ~ spl12_5
    | ~ spl12_7
    | ~ spl12_11
    | spl12_42
    | ~ spl12_45
    | spl12_220
    | ~ spl12_27
    | ~ spl12_25
    | ~ spl12_23
    | spl12_8
    | ~ spl12_20 ),
    inference(avatar_split_clause,[],[f2164,f286,f791,f806,f809,f812,f939,f374,f371,f266,f260,f257,f735,f732,f729,f368,f365,f362])).

fof(f729,plain,
    ( spl12_32
  <=> v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_32])])).

fof(f732,plain,
    ( spl12_31
  <=> ~ v2_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_31])])).

fof(f735,plain,
    ( spl12_29
  <=> ~ l1_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_29])])).

fof(f257,plain,
    ( spl12_5
  <=> ~ v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_5])])).

fof(f260,plain,
    ( spl12_7
  <=> ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_7])])).

fof(f266,plain,
    ( spl12_11
  <=> ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_11])])).

fof(f812,plain,
    ( spl12_27
  <=> ~ v1_funct_1(k2_tmap_1(sK0,sK3,sK4,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_27])])).

fof(f809,plain,
    ( spl12_25
  <=> ~ v1_funct_2(k2_tmap_1(sK0,sK3,sK4,sK1),u1_struct_0(sK1),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_25])])).

fof(f806,plain,
    ( spl12_23
  <=> ~ v5_pre_topc(k2_tmap_1(sK0,sK3,sK4,sK1),sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_23])])).

fof(f791,plain,
    ( spl12_8
  <=> v5_pre_topc(sK4,sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_8])])).

fof(f286,plain,
    ( spl12_20
  <=> m1_subset_1(k2_tmap_1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_20])])).

fof(f2164,plain,
    ( ! [X3] :
        ( v5_pre_topc(sK4,sK0,sK3)
        | ~ v5_pre_topc(k2_tmap_1(sK0,sK3,sK4,sK1),sK1,sK3)
        | ~ v1_funct_2(k2_tmap_1(sK0,sK3,sK4,sK1),u1_struct_0(sK1),u1_struct_0(sK3))
        | ~ v1_funct_1(k2_tmap_1(sK0,sK3,sK4,sK1))
        | ~ m1_subset_1(k2_tmap_1(sK0,sK3,sK4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3))))
        | ~ v5_pre_topc(k2_tmap_1(sK0,sK3,sK4,X3),X3,sK3)
        | ~ v1_funct_2(k2_tmap_1(sK0,sK3,sK4,X3),u1_struct_0(X3),u1_struct_0(sK3))
        | ~ v1_funct_1(k2_tmap_1(sK0,sK3,sK4,X3))
        | ~ r4_tsep_1(sK0,X3,sK1)
        | k1_tsep_1(sK0,X3,sK1) != sK0
        | ~ m1_pre_topc(sK1,sK0)
        | v2_struct_0(sK1)
        | ~ m1_pre_topc(X3,sK0)
        | v2_struct_0(X3)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK3))))
        | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK3))
        | ~ v1_funct_1(sK4)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl12_20 ),
    inference(resolution,[],[f287,f178])).

fof(f178,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
      | v5_pre_topc(X2,X0,X1)
      | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
      | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
      | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
      | ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
      | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X3))
      | ~ r4_tsep_1(X0,X3,X4)
      | k1_tsep_1(X0,X3,X4) != X0
      | ~ m1_pre_topc(X4,X0)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f114])).

fof(f114,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                            & v5_pre_topc(X2,X0,X1)
                            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                            & v1_funct_1(X2) )
                          | ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                          | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                          | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                          | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                          | ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                          | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                          | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
                        & ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                            & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                            & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                            & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                            & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                            & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                            & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                            & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
                          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                          | ~ v5_pre_topc(X2,X0,X1)
                          | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                          | ~ v1_funct_1(X2) ) )
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
    inference(flattening,[],[f113])).

fof(f113,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                            & v5_pre_topc(X2,X0,X1)
                            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                            & v1_funct_1(X2) )
                          | ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                          | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                          | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                          | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                          | ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                          | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                          | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
                        & ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                            & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                            & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                            & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                            & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                            & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                            & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                            & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
                          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                          | ~ v5_pre_topc(X2,X0,X1)
                          | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                          | ~ v1_funct_1(X2) ) )
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
    inference(nnf_transformation,[],[f61])).

fof(f61,plain,(
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
    inference(flattening,[],[f60])).

fof(f60,plain,(
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
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/tmap_1__t137_tmap_1.p',t132_tmap_1)).

fof(f287,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK3))))
    | ~ spl12_20 ),
    inference(avatar_component_clause,[],[f286])).

fof(f1026,plain,(
    spl12_119 ),
    inference(avatar_contradiction_clause,[],[f1025])).

fof(f1025,plain,
    ( $false
    | ~ spl12_119 ),
    inference(subsumption_resolution,[],[f133,f767])).

fof(f767,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl12_119 ),
    inference(resolution,[],[f638,f162])).

fof(f638,plain,
    ( ~ l1_struct_0(sK0)
    | ~ spl12_119 ),
    inference(avatar_component_clause,[],[f637])).

fof(f710,plain,
    ( spl12_36
    | ~ spl12_39
    | ~ spl12_41
    | spl12_42
    | ~ spl12_45
    | spl12_46
    | ~ spl12_49
    | spl12_2
    | ~ spl12_0 ),
    inference(avatar_split_clause,[],[f707,f326,f333,f380,f377,f374,f371,f368,f365,f362])).

fof(f333,plain,
    ( spl12_2
  <=> r1_tsep_1(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).

fof(f707,plain,
    ( r1_tsep_1(sK1,sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_0 ),
    inference(resolution,[],[f327,f180])).

fof(f180,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_tsep_1(X0,X1,X2)
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
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
    inference(flattening,[],[f62])).

fof(f62,plain,(
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
    inference(ennf_transformation,[],[f39])).

fof(f39,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/tmap_1__t137_tmap_1.p',t68_tsep_1)).

fof(f327,plain,
    ( r3_tsep_1(sK0,sK1,sK2)
    | ~ spl12_0 ),
    inference(avatar_component_clause,[],[f326])).

fof(f465,plain,(
    ~ spl12_46 ),
    inference(avatar_contradiction_clause,[],[f464])).

fof(f464,plain,
    ( $false
    | ~ spl12_46 ),
    inference(subsumption_resolution,[],[f136,f378])).

fof(f378,plain,
    ( v2_struct_0(sK2)
    | ~ spl12_46 ),
    inference(avatar_component_clause,[],[f377])).

fof(f463,plain,(
    ~ spl12_42 ),
    inference(avatar_contradiction_clause,[],[f462])).

fof(f462,plain,
    ( $false
    | ~ spl12_42 ),
    inference(subsumption_resolution,[],[f134,f372])).

fof(f372,plain,
    ( v2_struct_0(sK1)
    | ~ spl12_42 ),
    inference(avatar_component_clause,[],[f371])).

fof(f461,plain,(
    ~ spl12_36 ),
    inference(avatar_contradiction_clause,[],[f460])).

fof(f460,plain,
    ( $false
    | ~ spl12_36 ),
    inference(subsumption_resolution,[],[f131,f363])).

fof(f363,plain,
    ( v2_struct_0(sK0)
    | ~ spl12_36 ),
    inference(avatar_component_clause,[],[f362])).

fof(f459,plain,(
    spl12_39 ),
    inference(avatar_contradiction_clause,[],[f458])).

fof(f458,plain,
    ( $false
    | ~ spl12_39 ),
    inference(subsumption_resolution,[],[f132,f366])).

fof(f366,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ spl12_39 ),
    inference(avatar_component_clause,[],[f365])).

fof(f132,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f110])).

fof(f451,plain,(
    spl12_49 ),
    inference(avatar_contradiction_clause,[],[f450])).

fof(f450,plain,
    ( $false
    | ~ spl12_49 ),
    inference(subsumption_resolution,[],[f137,f381])).

fof(f381,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | ~ spl12_49 ),
    inference(avatar_component_clause,[],[f380])).

fof(f443,plain,(
    spl12_45 ),
    inference(avatar_contradiction_clause,[],[f442])).

fof(f442,plain,
    ( $false
    | ~ spl12_45 ),
    inference(subsumption_resolution,[],[f135,f375])).

fof(f375,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | ~ spl12_45 ),
    inference(avatar_component_clause,[],[f374])).

fof(f441,plain,(
    spl12_41 ),
    inference(avatar_contradiction_clause,[],[f440])).

fof(f440,plain,
    ( $false
    | ~ spl12_41 ),
    inference(subsumption_resolution,[],[f133,f369])).

fof(f369,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl12_41 ),
    inference(avatar_component_clause,[],[f368])).

fof(f413,plain,
    ( spl12_36
    | ~ spl12_39
    | ~ spl12_41
    | spl12_42
    | ~ spl12_45
    | spl12_46
    | ~ spl12_49
    | ~ spl12_3
    | spl12_64
    | spl12_1 ),
    inference(avatar_split_clause,[],[f359,f251,f411,f254,f380,f377,f374,f371,f368,f365,f362])).

fof(f359,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK6(sK0,sK1,sK2),sK7(sK0,sK1,sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK6(sK0,sK1,sK2)))))
    | ~ r1_tsep_1(sK1,sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_1 ),
    inference(resolution,[],[f252,f199])).

fof(f199,plain,(
    ! [X2,X0,X1] :
      ( r3_tsep_1(X0,X1,X2)
      | m1_subset_1(k2_tmap_1(X0,sK6(X0,X1,X2),sK7(X0,X1,X2),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK6(X0,X1,X2)))))
      | ~ r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f120])).

fof(f409,plain,
    ( spl12_36
    | ~ spl12_39
    | ~ spl12_41
    | spl12_42
    | ~ spl12_45
    | spl12_46
    | ~ spl12_49
    | ~ spl12_3
    | spl12_62
    | spl12_1 ),
    inference(avatar_split_clause,[],[f358,f251,f407,f254,f380,f377,f374,f371,f368,f365,f362])).

fof(f407,plain,
    ( spl12_62
  <=> v1_funct_1(k2_tmap_1(sK0,sK6(sK0,sK1,sK2),sK7(sK0,sK1,sK2),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_62])])).

fof(f358,plain,
    ( v1_funct_1(k2_tmap_1(sK0,sK6(sK0,sK1,sK2),sK7(sK0,sK1,sK2),sK2))
    | ~ r1_tsep_1(sK1,sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_1 ),
    inference(resolution,[],[f252,f196])).

fof(f196,plain,(
    ! [X2,X0,X1] :
      ( r3_tsep_1(X0,X1,X2)
      | v1_funct_1(k2_tmap_1(X0,sK6(X0,X1,X2),sK7(X0,X1,X2),X2))
      | ~ r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f120])).

fof(f405,plain,
    ( spl12_36
    | ~ spl12_39
    | ~ spl12_41
    | spl12_42
    | ~ spl12_45
    | spl12_46
    | ~ spl12_49
    | ~ spl12_3
    | spl12_60
    | spl12_1 ),
    inference(avatar_split_clause,[],[f357,f251,f403,f254,f380,f377,f374,f371,f368,f365,f362])).

fof(f403,plain,
    ( spl12_60
  <=> m1_subset_1(k2_tmap_1(sK0,sK6(sK0,sK1,sK2),sK7(sK0,sK1,sK2),sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK6(sK0,sK1,sK2))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_60])])).

fof(f357,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK6(sK0,sK1,sK2),sK7(sK0,sK1,sK2),sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK6(sK0,sK1,sK2)))))
    | ~ r1_tsep_1(sK1,sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_1 ),
    inference(resolution,[],[f252,f195])).

fof(f195,plain,(
    ! [X2,X0,X1] :
      ( r3_tsep_1(X0,X1,X2)
      | m1_subset_1(k2_tmap_1(X0,sK6(X0,X1,X2),sK7(X0,X1,X2),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK6(X0,X1,X2)))))
      | ~ r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f120])).

fof(f401,plain,
    ( spl12_36
    | ~ spl12_39
    | ~ spl12_41
    | spl12_42
    | ~ spl12_45
    | spl12_46
    | ~ spl12_49
    | ~ spl12_3
    | spl12_58
    | spl12_1 ),
    inference(avatar_split_clause,[],[f356,f251,f399,f254,f380,f377,f374,f371,f368,f365,f362])).

fof(f399,plain,
    ( spl12_58
  <=> v1_funct_1(k2_tmap_1(sK0,sK6(sK0,sK1,sK2),sK7(sK0,sK1,sK2),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_58])])).

fof(f356,plain,
    ( v1_funct_1(k2_tmap_1(sK0,sK6(sK0,sK1,sK2),sK7(sK0,sK1,sK2),sK1))
    | ~ r1_tsep_1(sK1,sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_1 ),
    inference(resolution,[],[f252,f192])).

fof(f192,plain,(
    ! [X2,X0,X1] :
      ( r3_tsep_1(X0,X1,X2)
      | v1_funct_1(k2_tmap_1(X0,sK6(X0,X1,X2),sK7(X0,X1,X2),X1))
      | ~ r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f120])).

fof(f397,plain,
    ( spl12_36
    | ~ spl12_39
    | ~ spl12_41
    | spl12_42
    | ~ spl12_45
    | spl12_46
    | ~ spl12_49
    | ~ spl12_3
    | spl12_56
    | spl12_1 ),
    inference(avatar_split_clause,[],[f355,f251,f395,f254,f380,f377,f374,f371,f368,f365,f362])).

fof(f355,plain,
    ( m1_subset_1(sK7(sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK6(sK0,sK1,sK2)))))
    | ~ r1_tsep_1(sK1,sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_1 ),
    inference(resolution,[],[f252,f191])).

fof(f191,plain,(
    ! [X2,X0,X1] :
      ( r3_tsep_1(X0,X1,X2)
      | m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK6(X0,X1,X2)))))
      | ~ r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f120])).

fof(f389,plain,
    ( spl12_36
    | ~ spl12_39
    | ~ spl12_41
    | spl12_42
    | ~ spl12_45
    | spl12_46
    | ~ spl12_49
    | ~ spl12_3
    | spl12_52
    | spl12_1 ),
    inference(avatar_split_clause,[],[f353,f251,f387,f254,f380,f377,f374,f371,f368,f365,f362])).

fof(f353,plain,
    ( l1_pre_topc(sK6(sK0,sK1,sK2))
    | ~ r1_tsep_1(sK1,sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_1 ),
    inference(resolution,[],[f252,f188])).

fof(f188,plain,(
    ! [X2,X0,X1] :
      ( r3_tsep_1(X0,X1,X2)
      | l1_pre_topc(sK6(X0,X1,X2))
      | ~ r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f120])).

fof(f385,plain,
    ( spl12_36
    | ~ spl12_39
    | ~ spl12_41
    | spl12_42
    | ~ spl12_45
    | spl12_46
    | ~ spl12_49
    | ~ spl12_3
    | spl12_50
    | spl12_1 ),
    inference(avatar_split_clause,[],[f352,f251,f383,f254,f380,f377,f374,f371,f368,f365,f362])).

fof(f383,plain,
    ( spl12_50
  <=> v2_pre_topc(sK6(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_50])])).

fof(f352,plain,
    ( v2_pre_topc(sK6(sK0,sK1,sK2))
    | ~ r1_tsep_1(sK1,sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_1 ),
    inference(resolution,[],[f252,f187])).

fof(f187,plain,(
    ! [X2,X0,X1] :
      ( r3_tsep_1(X0,X1,X2)
      | v2_pre_topc(sK6(X0,X1,X2))
      | ~ r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f120])).

fof(f335,plain,
    ( spl12_0
    | spl12_2 ),
    inference(avatar_split_clause,[],[f139,f333,f326])).

fof(f139,plain,
    ( r1_tsep_1(sK1,sK2)
    | r3_tsep_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f110])).

fof(f331,plain,
    ( spl12_0
    | spl12_34 ),
    inference(avatar_split_clause,[],[f142,f329,f326])).

fof(f142,plain,(
    ! [X6,X5] :
      ( v5_pre_topc(X6,sK0,X5)
      | ~ m1_subset_1(k2_tmap_1(sK0,X5,X6,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X5))))
      | ~ v5_pre_topc(k2_tmap_1(sK0,X5,X6,sK2),sK2,X5)
      | ~ v1_funct_2(k2_tmap_1(sK0,X5,X6,sK2),u1_struct_0(sK2),u1_struct_0(X5))
      | ~ v1_funct_1(k2_tmap_1(sK0,X5,X6,sK2))
      | ~ m1_subset_1(k2_tmap_1(sK0,X5,X6,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X5))))
      | ~ v5_pre_topc(k2_tmap_1(sK0,X5,X6,sK1),sK1,X5)
      | ~ v1_funct_2(k2_tmap_1(sK0,X5,X6,sK1),u1_struct_0(sK1),u1_struct_0(X5))
      | ~ v1_funct_1(k2_tmap_1(sK0,X5,X6,sK1))
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X5))))
      | ~ v1_funct_2(X6,u1_struct_0(sK0),u1_struct_0(X5))
      | ~ v1_funct_1(X6)
      | ~ l1_pre_topc(X5)
      | ~ v2_pre_topc(X5)
      | v2_struct_0(X5)
      | r3_tsep_1(sK0,sK1,sK2) ) ),
    inference(cnf_transformation,[],[f110])).

fof(f324,plain,
    ( ~ spl12_1
    | ~ spl12_3
    | ~ spl12_33 ),
    inference(avatar_split_clause,[],[f144,f322,f254,f251])).

fof(f322,plain,
    ( spl12_33
  <=> ~ v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_33])])).

fof(f144,plain,
    ( ~ v2_struct_0(sK3)
    | ~ r1_tsep_1(sK1,sK2)
    | ~ r3_tsep_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f110])).

fof(f320,plain,
    ( ~ spl12_1
    | ~ spl12_3
    | spl12_30 ),
    inference(avatar_split_clause,[],[f145,f318,f254,f251])).

fof(f318,plain,
    ( spl12_30
  <=> v2_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_30])])).

fof(f145,plain,
    ( v2_pre_topc(sK3)
    | ~ r1_tsep_1(sK1,sK2)
    | ~ r3_tsep_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f110])).

fof(f316,plain,
    ( ~ spl12_1
    | ~ spl12_3
    | spl12_28 ),
    inference(avatar_split_clause,[],[f146,f314,f254,f251])).

fof(f314,plain,
    ( spl12_28
  <=> l1_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_28])])).

fof(f146,plain,
    ( l1_pre_topc(sK3)
    | ~ r1_tsep_1(sK1,sK2)
    | ~ r3_tsep_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f110])).

fof(f312,plain,
    ( ~ spl12_1
    | ~ spl12_3
    | spl12_4 ),
    inference(avatar_split_clause,[],[f147,f310,f254,f251])).

fof(f310,plain,
    ( spl12_4
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_4])])).

fof(f147,plain,
    ( v1_funct_1(sK4)
    | ~ r1_tsep_1(sK1,sK2)
    | ~ r3_tsep_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f110])).

fof(f308,plain,
    ( ~ spl12_1
    | ~ spl12_3
    | spl12_6 ),
    inference(avatar_split_clause,[],[f148,f306,f254,f251])).

fof(f306,plain,
    ( spl12_6
  <=> v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_6])])).

fof(f148,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK3))
    | ~ r1_tsep_1(sK1,sK2)
    | ~ r3_tsep_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f110])).

fof(f304,plain,
    ( ~ spl12_1
    | ~ spl12_3
    | spl12_10 ),
    inference(avatar_split_clause,[],[f149,f302,f254,f251])).

fof(f302,plain,
    ( spl12_10
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_10])])).

fof(f149,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK3))))
    | ~ r1_tsep_1(sK1,sK2)
    | ~ r3_tsep_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f110])).

fof(f300,plain,
    ( ~ spl12_1
    | ~ spl12_3
    | spl12_26 ),
    inference(avatar_split_clause,[],[f150,f298,f254,f251])).

fof(f298,plain,
    ( spl12_26
  <=> v1_funct_1(k2_tmap_1(sK0,sK3,sK4,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_26])])).

fof(f150,plain,
    ( v1_funct_1(k2_tmap_1(sK0,sK3,sK4,sK1))
    | ~ r1_tsep_1(sK1,sK2)
    | ~ r3_tsep_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f110])).

fof(f296,plain,
    ( ~ spl12_1
    | ~ spl12_3
    | spl12_24 ),
    inference(avatar_split_clause,[],[f151,f294,f254,f251])).

fof(f294,plain,
    ( spl12_24
  <=> v1_funct_2(k2_tmap_1(sK0,sK3,sK4,sK1),u1_struct_0(sK1),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_24])])).

fof(f151,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK3,sK4,sK1),u1_struct_0(sK1),u1_struct_0(sK3))
    | ~ r1_tsep_1(sK1,sK2)
    | ~ r3_tsep_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f110])).

fof(f292,plain,
    ( ~ spl12_1
    | ~ spl12_3
    | spl12_22 ),
    inference(avatar_split_clause,[],[f152,f290,f254,f251])).

fof(f290,plain,
    ( spl12_22
  <=> v5_pre_topc(k2_tmap_1(sK0,sK3,sK4,sK1),sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_22])])).

fof(f152,plain,
    ( v5_pre_topc(k2_tmap_1(sK0,sK3,sK4,sK1),sK1,sK3)
    | ~ r1_tsep_1(sK1,sK2)
    | ~ r3_tsep_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f110])).

fof(f288,plain,
    ( ~ spl12_1
    | ~ spl12_3
    | spl12_20 ),
    inference(avatar_split_clause,[],[f153,f286,f254,f251])).

fof(f153,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK3))))
    | ~ r1_tsep_1(sK1,sK2)
    | ~ r3_tsep_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f110])).

fof(f284,plain,
    ( ~ spl12_1
    | ~ spl12_3
    | spl12_18 ),
    inference(avatar_split_clause,[],[f154,f282,f254,f251])).

fof(f282,plain,
    ( spl12_18
  <=> v1_funct_1(k2_tmap_1(sK0,sK3,sK4,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_18])])).

fof(f154,plain,
    ( v1_funct_1(k2_tmap_1(sK0,sK3,sK4,sK2))
    | ~ r1_tsep_1(sK1,sK2)
    | ~ r3_tsep_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f110])).

fof(f280,plain,
    ( ~ spl12_1
    | ~ spl12_3
    | spl12_16 ),
    inference(avatar_split_clause,[],[f155,f278,f254,f251])).

fof(f278,plain,
    ( spl12_16
  <=> v1_funct_2(k2_tmap_1(sK0,sK3,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_16])])).

fof(f155,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK3,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ r1_tsep_1(sK1,sK2)
    | ~ r3_tsep_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f110])).

fof(f276,plain,
    ( ~ spl12_1
    | ~ spl12_3
    | spl12_14 ),
    inference(avatar_split_clause,[],[f156,f274,f254,f251])).

fof(f274,plain,
    ( spl12_14
  <=> v5_pre_topc(k2_tmap_1(sK0,sK3,sK4,sK2),sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_14])])).

fof(f156,plain,
    ( v5_pre_topc(k2_tmap_1(sK0,sK3,sK4,sK2),sK2,sK3)
    | ~ r1_tsep_1(sK1,sK2)
    | ~ r3_tsep_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f110])).

fof(f272,plain,
    ( ~ spl12_1
    | ~ spl12_3
    | spl12_12 ),
    inference(avatar_split_clause,[],[f157,f270,f254,f251])).

fof(f157,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK3,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ r1_tsep_1(sK1,sK2)
    | ~ r3_tsep_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f110])).

fof(f268,plain,
    ( ~ spl12_1
    | ~ spl12_3
    | ~ spl12_5
    | ~ spl12_7
    | ~ spl12_9
    | ~ spl12_11 ),
    inference(avatar_split_clause,[],[f158,f266,f263,f260,f257,f254,f251])).

fof(f263,plain,
    ( spl12_9
  <=> ~ v5_pre_topc(sK4,sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_9])])).

fof(f158,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK3))))
    | ~ v5_pre_topc(sK4,sK0,sK3)
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | ~ r1_tsep_1(sK1,sK2)
    | ~ r3_tsep_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f110])).
%------------------------------------------------------------------------------
