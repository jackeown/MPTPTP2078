%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tmap_1__t150_tmap_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:10 EDT 2019

% Result     : Theorem 69.91s
% Output     : Refutation 69.91s
% Verified   : 
% Statistics : Number of formulae       :  561 (1601 expanded)
%              Number of leaves         :   82 ( 613 expanded)
%              Depth                    :   43
%              Number of atoms          : 6136 (25111 expanded)
%              Number of equality atoms :   15 (  55 expanded)
%              Maximal formula depth    :   39 (  11 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8330,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f268,f275,f282,f289,f296,f303,f310,f317,f324,f331,f338,f345,f353,f362,f369,f376,f383,f390,f397,f404,f411,f477,f485,f494,f503,f879,f899,f1052,f1161,f1174,f3925,f3943,f3964,f3996,f4026,f4053,f4091,f4173,f4186,f4233,f4267,f4335,f4421,f6834,f6858,f6889,f8188,f8329])).

fof(f8329,plain,
    ( ~ spl13_42
    | spl13_45
    | ~ spl13_46
    | spl13_49
    | ~ spl13_50
    | ~ spl13_52
    | spl13_55
    | ~ spl13_82
    | spl13_85
    | ~ spl13_456 ),
    inference(avatar_contradiction_clause,[],[f8328])).

fof(f8328,plain,
    ( $false
    | ~ spl13_42
    | ~ spl13_45
    | ~ spl13_46
    | ~ spl13_49
    | ~ spl13_50
    | ~ spl13_52
    | ~ spl13_55
    | ~ spl13_82
    | ~ spl13_85
    | ~ spl13_456 ),
    inference(subsumption_resolution,[],[f8327,f410])).

fof(f410,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl13_55 ),
    inference(avatar_component_clause,[],[f409])).

fof(f409,plain,
    ( spl13_55
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_55])])).

fof(f8327,plain,
    ( v2_struct_0(sK0)
    | ~ spl13_42
    | ~ spl13_45
    | ~ spl13_46
    | ~ spl13_49
    | ~ spl13_50
    | ~ spl13_52
    | ~ spl13_82
    | ~ spl13_85
    | ~ spl13_456 ),
    inference(subsumption_resolution,[],[f8326,f403])).

fof(f403,plain,
    ( v2_pre_topc(sK0)
    | ~ spl13_52 ),
    inference(avatar_component_clause,[],[f402])).

fof(f402,plain,
    ( spl13_52
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_52])])).

fof(f8326,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_42
    | ~ spl13_45
    | ~ spl13_46
    | ~ spl13_49
    | ~ spl13_50
    | ~ spl13_82
    | ~ spl13_85
    | ~ spl13_456 ),
    inference(subsumption_resolution,[],[f8325,f396])).

fof(f396,plain,
    ( l1_pre_topc(sK0)
    | ~ spl13_50 ),
    inference(avatar_component_clause,[],[f395])).

fof(f395,plain,
    ( spl13_50
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_50])])).

fof(f8325,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_42
    | ~ spl13_45
    | ~ spl13_46
    | ~ spl13_49
    | ~ spl13_82
    | ~ spl13_85
    | ~ spl13_456 ),
    inference(subsumption_resolution,[],[f8324,f375])).

fof(f375,plain,
    ( ~ v2_struct_0(sK2)
    | ~ spl13_45 ),
    inference(avatar_component_clause,[],[f374])).

fof(f374,plain,
    ( spl13_45
  <=> ~ v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_45])])).

fof(f8324,plain,
    ( v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_42
    | ~ spl13_46
    | ~ spl13_49
    | ~ spl13_82
    | ~ spl13_85
    | ~ spl13_456 ),
    inference(subsumption_resolution,[],[f8323,f368])).

fof(f368,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ spl13_42 ),
    inference(avatar_component_clause,[],[f367])).

fof(f367,plain,
    ( spl13_42
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_42])])).

fof(f8323,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_46
    | ~ spl13_49
    | ~ spl13_82
    | ~ spl13_85
    | ~ spl13_456 ),
    inference(subsumption_resolution,[],[f8322,f389])).

fof(f389,plain,
    ( ~ v2_struct_0(sK1)
    | ~ spl13_49 ),
    inference(avatar_component_clause,[],[f388])).

fof(f388,plain,
    ( spl13_49
  <=> ~ v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_49])])).

fof(f8322,plain,
    ( v2_struct_0(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_46
    | ~ spl13_82
    | ~ spl13_85
    | ~ spl13_456 ),
    inference(subsumption_resolution,[],[f8321,f382])).

fof(f382,plain,
    ( m1_pre_topc(sK1,sK0)
    | ~ spl13_46 ),
    inference(avatar_component_clause,[],[f381])).

fof(f381,plain,
    ( spl13_46
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_46])])).

fof(f8321,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_82
    | ~ spl13_85
    | ~ spl13_456 ),
    inference(subsumption_resolution,[],[f8320,f541])).

fof(f541,plain,
    ( r1_tsep_1(sK2,sK1)
    | ~ spl13_82 ),
    inference(avatar_component_clause,[],[f540])).

fof(f540,plain,
    ( spl13_82
  <=> r1_tsep_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_82])])).

fof(f8320,plain,
    ( ~ r1_tsep_1(sK2,sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_85
    | ~ spl13_456 ),
    inference(subsumption_resolution,[],[f8318,f566])).

fof(f566,plain,
    ( ~ r3_tsep_1(sK0,sK2,sK1)
    | ~ spl13_85 ),
    inference(avatar_component_clause,[],[f565])).

fof(f565,plain,
    ( spl13_85
  <=> ~ r3_tsep_1(sK0,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_85])])).

fof(f8318,plain,
    ( r3_tsep_1(sK0,sK2,sK1)
    | ~ r1_tsep_1(sK2,sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_456 ),
    inference(resolution,[],[f8056,f1128])).

fof(f1128,plain,(
    ! [X4,X5,X3] :
      ( ~ v5_pre_topc(sK7(X3,X4,X5),k1_tsep_1(X3,X5,X4),sK6(X3,X4,X5))
      | r3_tsep_1(X3,X4,X5)
      | ~ r1_tsep_1(X4,X5)
      | ~ m1_pre_topc(X5,X3)
      | v2_struct_0(X5)
      | ~ m1_pre_topc(X4,X3)
      | v2_struct_0(X4)
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | v2_struct_0(X3) ) ),
    inference(duplicate_literal_removal,[],[f1127])).

fof(f1127,plain,(
    ! [X4,X5,X3] :
      ( ~ v5_pre_topc(sK7(X3,X4,X5),k1_tsep_1(X3,X5,X4),sK6(X3,X4,X5))
      | r3_tsep_1(X3,X4,X5)
      | ~ r1_tsep_1(X4,X5)
      | ~ m1_pre_topc(X5,X3)
      | v2_struct_0(X5)
      | ~ m1_pre_topc(X4,X3)
      | v2_struct_0(X4)
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X5,X3)
      | v2_struct_0(X5)
      | ~ m1_pre_topc(X4,X3)
      | v2_struct_0(X4)
      | ~ l1_pre_topc(X3)
      | v2_struct_0(X3) ) ),
    inference(superposition,[],[f1114,f163])).

fof(f163,plain,(
    ! [X2,X0,X1] :
      ( k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
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
    file('/export/starexec/sandbox/benchmark/tmap_1__t150_tmap_1.p',commutativity_k1_tsep_1)).

fof(f1114,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_pre_topc(sK7(X0,X1,X2),k1_tsep_1(X0,X1,X2),sK6(X0,X1,X2))
      | r3_tsep_1(X0,X1,X2)
      | ~ r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f1113,f172])).

fof(f172,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(sK7(X0,X1,X2))
      | r3_tsep_1(X0,X1,X2)
      | ~ r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f119])).

fof(f119,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r3_tsep_1(X0,X1,X2)
                  | ( ( ~ m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(sK6(X0,X1,X2)))))
                      | ~ v5_pre_topc(sK7(X0,X1,X2),k1_tsep_1(X0,X1,X2),sK6(X0,X1,X2))
                      | ~ v1_funct_2(sK7(X0,X1,X2),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(sK6(X0,X1,X2)))
                      | ~ v1_funct_1(sK7(X0,X1,X2)) )
                    & m1_subset_1(k3_tmap_1(X0,sK6(X0,X1,X2),k1_tsep_1(X0,X1,X2),X2,sK7(X0,X1,X2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK6(X0,X1,X2)))))
                    & v5_pre_topc(k3_tmap_1(X0,sK6(X0,X1,X2),k1_tsep_1(X0,X1,X2),X2,sK7(X0,X1,X2)),X2,sK6(X0,X1,X2))
                    & v1_funct_2(k3_tmap_1(X0,sK6(X0,X1,X2),k1_tsep_1(X0,X1,X2),X2,sK7(X0,X1,X2)),u1_struct_0(X2),u1_struct_0(sK6(X0,X1,X2)))
                    & v1_funct_1(k3_tmap_1(X0,sK6(X0,X1,X2),k1_tsep_1(X0,X1,X2),X2,sK7(X0,X1,X2)))
                    & m1_subset_1(k3_tmap_1(X0,sK6(X0,X1,X2),k1_tsep_1(X0,X1,X2),X1,sK7(X0,X1,X2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK6(X0,X1,X2)))))
                    & v5_pre_topc(k3_tmap_1(X0,sK6(X0,X1,X2),k1_tsep_1(X0,X1,X2),X1,sK7(X0,X1,X2)),X1,sK6(X0,X1,X2))
                    & v1_funct_2(k3_tmap_1(X0,sK6(X0,X1,X2),k1_tsep_1(X0,X1,X2),X1,sK7(X0,X1,X2)),u1_struct_0(X1),u1_struct_0(sK6(X0,X1,X2)))
                    & v1_funct_1(k3_tmap_1(X0,sK6(X0,X1,X2),k1_tsep_1(X0,X1,X2),X1,sK7(X0,X1,X2)))
                    & m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(sK6(X0,X1,X2)))))
                    & v1_funct_2(sK7(X0,X1,X2),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(sK6(X0,X1,X2)))
                    & v1_funct_1(sK7(X0,X1,X2))
                    & l1_pre_topc(sK6(X0,X1,X2))
                    & v2_pre_topc(sK6(X0,X1,X2))
                    & ~ v2_struct_0(sK6(X0,X1,X2)) )
                  | ~ r1_tsep_1(X1,X2) )
                & ( ( ! [X5] :
                        ( ! [X6] :
                            ( ( m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X5))))
                              & v5_pre_topc(X6,k1_tsep_1(X0,X1,X2),X5)
                              & v1_funct_2(X6,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X5))
                              & v1_funct_1(X6) )
                            | ~ m1_subset_1(k3_tmap_1(X0,X5,k1_tsep_1(X0,X1,X2),X2,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X5))))
                            | ~ v5_pre_topc(k3_tmap_1(X0,X5,k1_tsep_1(X0,X1,X2),X2,X6),X2,X5)
                            | ~ v1_funct_2(k3_tmap_1(X0,X5,k1_tsep_1(X0,X1,X2),X2,X6),u1_struct_0(X2),u1_struct_0(X5))
                            | ~ v1_funct_1(k3_tmap_1(X0,X5,k1_tsep_1(X0,X1,X2),X2,X6))
                            | ~ m1_subset_1(k3_tmap_1(X0,X5,k1_tsep_1(X0,X1,X2),X1,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X5))))
                            | ~ v5_pre_topc(k3_tmap_1(X0,X5,k1_tsep_1(X0,X1,X2),X1,X6),X1,X5)
                            | ~ v1_funct_2(k3_tmap_1(X0,X5,k1_tsep_1(X0,X1,X2),X1,X6),u1_struct_0(X1),u1_struct_0(X5))
                            | ~ v1_funct_1(k3_tmap_1(X0,X5,k1_tsep_1(X0,X1,X2),X1,X6))
                            | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X5))))
                            | ~ v1_funct_2(X6,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X5))
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f116,f118,f117])).

fof(f117,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ? [X4] :
              ( ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                | ~ v5_pre_topc(X4,k1_tsep_1(X0,X1,X2),X3)
                | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                | ~ v1_funct_1(X4) )
              & m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
              & v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),X2,X3)
              & v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),u1_struct_0(X2),u1_struct_0(X3))
              & v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4))
              & m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
              & v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),X1,X3)
              & v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),u1_struct_0(X1),u1_struct_0(X3))
              & v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4))
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
              & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
              & v1_funct_1(X4) )
          & l1_pre_topc(X3)
          & v2_pre_topc(X3)
          & ~ v2_struct_0(X3) )
     => ( ? [X4] :
            ( ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(sK6(X0,X1,X2)))))
              | ~ v5_pre_topc(X4,k1_tsep_1(X0,X1,X2),sK6(X0,X1,X2))
              | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(sK6(X0,X1,X2)))
              | ~ v1_funct_1(X4) )
            & m1_subset_1(k3_tmap_1(X0,sK6(X0,X1,X2),k1_tsep_1(X0,X1,X2),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK6(X0,X1,X2)))))
            & v5_pre_topc(k3_tmap_1(X0,sK6(X0,X1,X2),k1_tsep_1(X0,X1,X2),X2,X4),X2,sK6(X0,X1,X2))
            & v1_funct_2(k3_tmap_1(X0,sK6(X0,X1,X2),k1_tsep_1(X0,X1,X2),X2,X4),u1_struct_0(X2),u1_struct_0(sK6(X0,X1,X2)))
            & v1_funct_1(k3_tmap_1(X0,sK6(X0,X1,X2),k1_tsep_1(X0,X1,X2),X2,X4))
            & m1_subset_1(k3_tmap_1(X0,sK6(X0,X1,X2),k1_tsep_1(X0,X1,X2),X1,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK6(X0,X1,X2)))))
            & v5_pre_topc(k3_tmap_1(X0,sK6(X0,X1,X2),k1_tsep_1(X0,X1,X2),X1,X4),X1,sK6(X0,X1,X2))
            & v1_funct_2(k3_tmap_1(X0,sK6(X0,X1,X2),k1_tsep_1(X0,X1,X2),X1,X4),u1_struct_0(X1),u1_struct_0(sK6(X0,X1,X2)))
            & v1_funct_1(k3_tmap_1(X0,sK6(X0,X1,X2),k1_tsep_1(X0,X1,X2),X1,X4))
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(sK6(X0,X1,X2)))))
            & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(sK6(X0,X1,X2)))
            & v1_funct_1(X4) )
        & l1_pre_topc(sK6(X0,X1,X2))
        & v2_pre_topc(sK6(X0,X1,X2))
        & ~ v2_struct_0(sK6(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f118,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
            | ~ v5_pre_topc(X4,k1_tsep_1(X0,X1,X2),X3)
            | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
            | ~ v1_funct_1(X4) )
          & m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
          & v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),X2,X3)
          & v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),u1_struct_0(X2),u1_struct_0(X3))
          & v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4))
          & m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
          & v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),X1,X3)
          & v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),u1_struct_0(X1),u1_struct_0(X3))
          & v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4))
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
          & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
          & v1_funct_1(X4) )
     => ( ( ~ m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
          | ~ v5_pre_topc(sK7(X0,X1,X2),k1_tsep_1(X0,X1,X2),X3)
          | ~ v1_funct_2(sK7(X0,X1,X2),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
          | ~ v1_funct_1(sK7(X0,X1,X2)) )
        & m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,sK7(X0,X1,X2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
        & v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,sK7(X0,X1,X2)),X2,X3)
        & v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,sK7(X0,X1,X2)),u1_struct_0(X2),u1_struct_0(X3))
        & v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,sK7(X0,X1,X2)))
        & m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,sK7(X0,X1,X2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
        & v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,sK7(X0,X1,X2)),X1,X3)
        & v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,sK7(X0,X1,X2)),u1_struct_0(X1),u1_struct_0(X3))
        & v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,sK7(X0,X1,X2)))
        & m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
        & v1_funct_2(sK7(X0,X1,X2),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
        & v1_funct_1(sK7(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f116,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r3_tsep_1(X0,X1,X2)
                  | ? [X3] :
                      ( ? [X4] :
                          ( ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                            | ~ v5_pre_topc(X4,k1_tsep_1(X0,X1,X2),X3)
                            | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                            | ~ v1_funct_1(X4) )
                          & m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                          & v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),X2,X3)
                          & v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),u1_struct_0(X2),u1_struct_0(X3))
                          & v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4))
                          & m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                          & v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),X1,X3)
                          & v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),u1_struct_0(X1),u1_struct_0(X3))
                          & v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4))
                          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                          & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                          & v1_funct_1(X4) )
                      & l1_pre_topc(X3)
                      & v2_pre_topc(X3)
                      & ~ v2_struct_0(X3) )
                  | ~ r1_tsep_1(X1,X2) )
                & ( ( ! [X5] :
                        ( ! [X6] :
                            ( ( m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X5))))
                              & v5_pre_topc(X6,k1_tsep_1(X0,X1,X2),X5)
                              & v1_funct_2(X6,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X5))
                              & v1_funct_1(X6) )
                            | ~ m1_subset_1(k3_tmap_1(X0,X5,k1_tsep_1(X0,X1,X2),X2,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X5))))
                            | ~ v5_pre_topc(k3_tmap_1(X0,X5,k1_tsep_1(X0,X1,X2),X2,X6),X2,X5)
                            | ~ v1_funct_2(k3_tmap_1(X0,X5,k1_tsep_1(X0,X1,X2),X2,X6),u1_struct_0(X2),u1_struct_0(X5))
                            | ~ v1_funct_1(k3_tmap_1(X0,X5,k1_tsep_1(X0,X1,X2),X2,X6))
                            | ~ m1_subset_1(k3_tmap_1(X0,X5,k1_tsep_1(X0,X1,X2),X1,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X5))))
                            | ~ v5_pre_topc(k3_tmap_1(X0,X5,k1_tsep_1(X0,X1,X2),X1,X6),X1,X5)
                            | ~ v1_funct_2(k3_tmap_1(X0,X5,k1_tsep_1(X0,X1,X2),X1,X6),u1_struct_0(X1),u1_struct_0(X5))
                            | ~ v1_funct_1(k3_tmap_1(X0,X5,k1_tsep_1(X0,X1,X2),X1,X6))
                            | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X5))))
                            | ~ v1_funct_2(X6,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X5))
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
    inference(rectify,[],[f115])).

fof(f115,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r3_tsep_1(X0,X1,X2)
                  | ? [X3] :
                      ( ? [X4] :
                          ( ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                            | ~ v5_pre_topc(X4,k1_tsep_1(X0,X1,X2),X3)
                            | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                            | ~ v1_funct_1(X4) )
                          & m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                          & v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),X2,X3)
                          & v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),u1_struct_0(X2),u1_struct_0(X3))
                          & v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4))
                          & m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                          & v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),X1,X3)
                          & v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),u1_struct_0(X1),u1_struct_0(X3))
                          & v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4))
                          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                          & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                          & v1_funct_1(X4) )
                      & l1_pre_topc(X3)
                      & v2_pre_topc(X3)
                      & ~ v2_struct_0(X3) )
                  | ~ r1_tsep_1(X1,X2) )
                & ( ( ! [X3] :
                        ( ! [X4] :
                            ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                              & v5_pre_topc(X4,k1_tsep_1(X0,X1,X2),X3)
                              & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                              & v1_funct_1(X4) )
                            | ~ m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                            | ~ v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),X2,X3)
                            | ~ v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),u1_struct_0(X2),u1_struct_0(X3))
                            | ~ v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4))
                            | ~ m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                            | ~ v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),X1,X3)
                            | ~ v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),u1_struct_0(X1),u1_struct_0(X3))
                            | ~ v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4))
                            | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                            | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
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
    inference(flattening,[],[f114])).

fof(f114,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r3_tsep_1(X0,X1,X2)
                  | ? [X3] :
                      ( ? [X4] :
                          ( ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                            | ~ v5_pre_topc(X4,k1_tsep_1(X0,X1,X2),X3)
                            | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                            | ~ v1_funct_1(X4) )
                          & m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                          & v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),X2,X3)
                          & v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),u1_struct_0(X2),u1_struct_0(X3))
                          & v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4))
                          & m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                          & v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),X1,X3)
                          & v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),u1_struct_0(X1),u1_struct_0(X3))
                          & v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4))
                          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                          & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                          & v1_funct_1(X4) )
                      & l1_pre_topc(X3)
                      & v2_pre_topc(X3)
                      & ~ v2_struct_0(X3) )
                  | ~ r1_tsep_1(X1,X2) )
                & ( ( ! [X3] :
                        ( ! [X4] :
                            ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                              & v5_pre_topc(X4,k1_tsep_1(X0,X1,X2),X3)
                              & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                              & v1_funct_1(X4) )
                            | ~ m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                            | ~ v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),X2,X3)
                            | ~ v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),u1_struct_0(X2),u1_struct_0(X3))
                            | ~ v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4))
                            | ~ m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                            | ~ v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),X1,X3)
                            | ~ v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),u1_struct_0(X1),u1_struct_0(X3))
                            | ~ v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4))
                            | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                            | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
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
    inference(nnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_tsep_1(X0,X1,X2)
              <=> ( ! [X3] :
                      ( ! [X4] :
                          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                            & v5_pre_topc(X4,k1_tsep_1(X0,X1,X2),X3)
                            & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                            & v1_funct_1(X4) )
                          | ~ m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                          | ~ v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),X2,X3)
                          | ~ v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),u1_struct_0(X2),u1_struct_0(X3))
                          | ~ v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4))
                          | ~ m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                          | ~ v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),X1,X3)
                          | ~ v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),u1_struct_0(X1),u1_struct_0(X3))
                          | ~ v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4))
                          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                          | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
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
    inference(flattening,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_tsep_1(X0,X1,X2)
              <=> ( ! [X3] :
                      ( ! [X4] :
                          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                            & v5_pre_topc(X4,k1_tsep_1(X0,X1,X2),X3)
                            & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                            & v1_funct_1(X4) )
                          | ~ m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                          | ~ v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),X2,X3)
                          | ~ v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),u1_struct_0(X2),u1_struct_0(X3))
                          | ~ v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4))
                          | ~ m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                          | ~ v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),X1,X3)
                          | ~ v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),u1_struct_0(X1),u1_struct_0(X3))
                          | ~ v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4))
                          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                          | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
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
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
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
                          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                            & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                            & v1_funct_1(X4) )
                         => ( ( m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                              & v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),X2,X3)
                              & v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),u1_struct_0(X2),u1_struct_0(X3))
                              & v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4))
                              & m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                              & v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),X1,X3)
                              & v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),u1_struct_0(X1),u1_struct_0(X3))
                              & v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4)) )
                           => ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                              & v5_pre_topc(X4,k1_tsep_1(X0,X1,X2),X3)
                              & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                              & v1_funct_1(X4) ) ) ) )
                  & r1_tsep_1(X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t150_tmap_1.p',t135_tmap_1)).

fof(f1113,plain,(
    ! [X2,X0,X1] :
      ( r3_tsep_1(X0,X1,X2)
      | ~ v5_pre_topc(sK7(X0,X1,X2),k1_tsep_1(X0,X1,X2),sK6(X0,X1,X2))
      | ~ v1_funct_1(sK7(X0,X1,X2))
      | ~ r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f1112,f173])).

fof(f173,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(sK7(X0,X1,X2),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(sK6(X0,X1,X2)))
      | r3_tsep_1(X0,X1,X2)
      | ~ r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f119])).

fof(f1112,plain,(
    ! [X2,X0,X1] :
      ( r3_tsep_1(X0,X1,X2)
      | ~ v5_pre_topc(sK7(X0,X1,X2),k1_tsep_1(X0,X1,X2),sK6(X0,X1,X2))
      | ~ v1_funct_2(sK7(X0,X1,X2),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(sK6(X0,X1,X2)))
      | ~ v1_funct_1(sK7(X0,X1,X2))
      | ~ r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f183,f174])).

fof(f174,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(sK6(X0,X1,X2)))))
      | r3_tsep_1(X0,X1,X2)
      | ~ r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f119])).

fof(f183,plain,(
    ! [X2,X0,X1] :
      ( r3_tsep_1(X0,X1,X2)
      | ~ m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(sK6(X0,X1,X2)))))
      | ~ v5_pre_topc(sK7(X0,X1,X2),k1_tsep_1(X0,X1,X2),sK6(X0,X1,X2))
      | ~ v1_funct_2(sK7(X0,X1,X2),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(sK6(X0,X1,X2)))
      | ~ v1_funct_1(sK7(X0,X1,X2))
      | ~ r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f119])).

fof(f8056,plain,
    ( v5_pre_topc(sK7(sK0,sK2,sK1),k1_tsep_1(sK0,sK1,sK2),sK6(sK0,sK2,sK1))
    | ~ spl13_456 ),
    inference(avatar_component_clause,[],[f8055])).

fof(f8055,plain,
    ( spl13_456
  <=> v5_pre_topc(sK7(sK0,sK2,sK1),k1_tsep_1(sK0,sK1,sK2),sK6(sK0,sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_456])])).

fof(f8188,plain,
    ( spl13_456
    | ~ spl13_36
    | ~ spl13_42
    | spl13_45
    | ~ spl13_46
    | spl13_49
    | ~ spl13_50
    | ~ spl13_52
    | spl13_55
    | ~ spl13_82
    | spl13_85
    | ~ spl13_260
    | ~ spl13_262
    | ~ spl13_264
    | ~ spl13_266
    | ~ spl13_268
    | ~ spl13_270
    | ~ spl13_272
    | ~ spl13_274
    | ~ spl13_276
    | spl13_279
    | ~ spl13_280
    | ~ spl13_282
    | ~ spl13_284 ),
    inference(avatar_split_clause,[],[f8187,f3865,f3859,f3853,f3847,f3841,f3835,f3829,f3823,f3817,f3811,f3805,f3799,f3793,f565,f540,f409,f402,f395,f388,f381,f374,f367,f351,f8055])).

fof(f351,plain,
    ( spl13_36
  <=> ! [X7,X8,X6] :
        ( v5_pre_topc(k10_tmap_1(sK0,X6,sK1,sK2,X7,X8),k1_tsep_1(sK0,sK1,sK2),X6)
        | v2_struct_0(X6)
        | ~ v2_pre_topc(X6)
        | ~ l1_pre_topc(X6)
        | ~ v1_funct_1(X7)
        | ~ v1_funct_2(X7,u1_struct_0(sK1),u1_struct_0(X6))
        | ~ v5_pre_topc(X7,sK1,X6)
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X6))))
        | ~ v1_funct_1(X8)
        | ~ v1_funct_2(X8,u1_struct_0(sK2),u1_struct_0(X6))
        | ~ v5_pre_topc(X8,sK2,X6)
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X6)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_36])])).

fof(f3793,plain,
    ( spl13_260
  <=> v5_pre_topc(k3_tmap_1(sK0,sK6(sK0,sK2,sK1),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK2,sK1)),sK2,sK6(sK0,sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_260])])).

fof(f3799,plain,
    ( spl13_262
  <=> v1_funct_2(k3_tmap_1(sK0,sK6(sK0,sK2,sK1),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK2,sK1)),u1_struct_0(sK2),u1_struct_0(sK6(sK0,sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_262])])).

fof(f3805,plain,
    ( spl13_264
  <=> v1_funct_1(k3_tmap_1(sK0,sK6(sK0,sK2,sK1),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_264])])).

fof(f3811,plain,
    ( spl13_266
  <=> m1_subset_1(k3_tmap_1(sK0,sK6(sK0,sK2,sK1),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK2,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK6(sK0,sK2,sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_266])])).

fof(f3817,plain,
    ( spl13_268
  <=> v5_pre_topc(k3_tmap_1(sK0,sK6(sK0,sK2,sK1),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK2,sK1)),sK1,sK6(sK0,sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_268])])).

fof(f3823,plain,
    ( spl13_270
  <=> v1_funct_2(k3_tmap_1(sK0,sK6(sK0,sK2,sK1),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK2,sK1)),u1_struct_0(sK1),u1_struct_0(sK6(sK0,sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_270])])).

fof(f3829,plain,
    ( spl13_272
  <=> v1_funct_1(k3_tmap_1(sK0,sK6(sK0,sK2,sK1),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_272])])).

fof(f3835,plain,
    ( spl13_274
  <=> l1_pre_topc(sK6(sK0,sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_274])])).

fof(f3841,plain,
    ( spl13_276
  <=> v2_pre_topc(sK6(sK0,sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_276])])).

fof(f3847,plain,
    ( spl13_279
  <=> ~ v2_struct_0(sK6(sK0,sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_279])])).

fof(f3853,plain,
    ( spl13_280
  <=> v1_funct_1(sK7(sK0,sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_280])])).

fof(f3859,plain,
    ( spl13_282
  <=> v1_funct_2(sK7(sK0,sK2,sK1),u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK6(sK0,sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_282])])).

fof(f3865,plain,
    ( spl13_284
  <=> m1_subset_1(sK7(sK0,sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK6(sK0,sK2,sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_284])])).

fof(f8187,plain,
    ( v5_pre_topc(sK7(sK0,sK2,sK1),k1_tsep_1(sK0,sK1,sK2),sK6(sK0,sK2,sK1))
    | ~ spl13_36
    | ~ spl13_42
    | ~ spl13_45
    | ~ spl13_46
    | ~ spl13_49
    | ~ spl13_50
    | ~ spl13_52
    | ~ spl13_55
    | ~ spl13_82
    | ~ spl13_85
    | ~ spl13_260
    | ~ spl13_262
    | ~ spl13_264
    | ~ spl13_266
    | ~ spl13_268
    | ~ spl13_270
    | ~ spl13_272
    | ~ spl13_274
    | ~ spl13_276
    | ~ spl13_279
    | ~ spl13_280
    | ~ spl13_282
    | ~ spl13_284 ),
    inference(subsumption_resolution,[],[f8186,f410])).

fof(f8186,plain,
    ( v5_pre_topc(sK7(sK0,sK2,sK1),k1_tsep_1(sK0,sK1,sK2),sK6(sK0,sK2,sK1))
    | v2_struct_0(sK0)
    | ~ spl13_36
    | ~ spl13_42
    | ~ spl13_45
    | ~ spl13_46
    | ~ spl13_49
    | ~ spl13_50
    | ~ spl13_52
    | ~ spl13_55
    | ~ spl13_82
    | ~ spl13_85
    | ~ spl13_260
    | ~ spl13_262
    | ~ spl13_264
    | ~ spl13_266
    | ~ spl13_268
    | ~ spl13_270
    | ~ spl13_272
    | ~ spl13_274
    | ~ spl13_276
    | ~ spl13_279
    | ~ spl13_280
    | ~ spl13_282
    | ~ spl13_284 ),
    inference(subsumption_resolution,[],[f8185,f403])).

fof(f8185,plain,
    ( v5_pre_topc(sK7(sK0,sK2,sK1),k1_tsep_1(sK0,sK1,sK2),sK6(sK0,sK2,sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_36
    | ~ spl13_42
    | ~ spl13_45
    | ~ spl13_46
    | ~ spl13_49
    | ~ spl13_50
    | ~ spl13_52
    | ~ spl13_55
    | ~ spl13_82
    | ~ spl13_85
    | ~ spl13_260
    | ~ spl13_262
    | ~ spl13_264
    | ~ spl13_266
    | ~ spl13_268
    | ~ spl13_270
    | ~ spl13_272
    | ~ spl13_274
    | ~ spl13_276
    | ~ spl13_279
    | ~ spl13_280
    | ~ spl13_282
    | ~ spl13_284 ),
    inference(subsumption_resolution,[],[f8184,f396])).

fof(f8184,plain,
    ( v5_pre_topc(sK7(sK0,sK2,sK1),k1_tsep_1(sK0,sK1,sK2),sK6(sK0,sK2,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_36
    | ~ spl13_42
    | ~ spl13_45
    | ~ spl13_46
    | ~ spl13_49
    | ~ spl13_50
    | ~ spl13_52
    | ~ spl13_55
    | ~ spl13_82
    | ~ spl13_85
    | ~ spl13_260
    | ~ spl13_262
    | ~ spl13_264
    | ~ spl13_266
    | ~ spl13_268
    | ~ spl13_270
    | ~ spl13_272
    | ~ spl13_274
    | ~ spl13_276
    | ~ spl13_279
    | ~ spl13_280
    | ~ spl13_282
    | ~ spl13_284 ),
    inference(subsumption_resolution,[],[f8183,f375])).

fof(f8183,plain,
    ( v5_pre_topc(sK7(sK0,sK2,sK1),k1_tsep_1(sK0,sK1,sK2),sK6(sK0,sK2,sK1))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_36
    | ~ spl13_42
    | ~ spl13_45
    | ~ spl13_46
    | ~ spl13_49
    | ~ spl13_50
    | ~ spl13_52
    | ~ spl13_55
    | ~ spl13_82
    | ~ spl13_85
    | ~ spl13_260
    | ~ spl13_262
    | ~ spl13_264
    | ~ spl13_266
    | ~ spl13_268
    | ~ spl13_270
    | ~ spl13_272
    | ~ spl13_274
    | ~ spl13_276
    | ~ spl13_279
    | ~ spl13_280
    | ~ spl13_282
    | ~ spl13_284 ),
    inference(subsumption_resolution,[],[f8182,f368])).

fof(f8182,plain,
    ( v5_pre_topc(sK7(sK0,sK2,sK1),k1_tsep_1(sK0,sK1,sK2),sK6(sK0,sK2,sK1))
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_36
    | ~ spl13_42
    | ~ spl13_45
    | ~ spl13_46
    | ~ spl13_49
    | ~ spl13_50
    | ~ spl13_52
    | ~ spl13_55
    | ~ spl13_82
    | ~ spl13_85
    | ~ spl13_260
    | ~ spl13_262
    | ~ spl13_264
    | ~ spl13_266
    | ~ spl13_268
    | ~ spl13_270
    | ~ spl13_272
    | ~ spl13_274
    | ~ spl13_276
    | ~ spl13_279
    | ~ spl13_280
    | ~ spl13_282
    | ~ spl13_284 ),
    inference(subsumption_resolution,[],[f8181,f389])).

fof(f8181,plain,
    ( v5_pre_topc(sK7(sK0,sK2,sK1),k1_tsep_1(sK0,sK1,sK2),sK6(sK0,sK2,sK1))
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_36
    | ~ spl13_42
    | ~ spl13_45
    | ~ spl13_46
    | ~ spl13_49
    | ~ spl13_50
    | ~ spl13_52
    | ~ spl13_55
    | ~ spl13_82
    | ~ spl13_85
    | ~ spl13_260
    | ~ spl13_262
    | ~ spl13_264
    | ~ spl13_266
    | ~ spl13_268
    | ~ spl13_270
    | ~ spl13_272
    | ~ spl13_274
    | ~ spl13_276
    | ~ spl13_279
    | ~ spl13_280
    | ~ spl13_282
    | ~ spl13_284 ),
    inference(subsumption_resolution,[],[f8180,f382])).

fof(f8180,plain,
    ( v5_pre_topc(sK7(sK0,sK2,sK1),k1_tsep_1(sK0,sK1,sK2),sK6(sK0,sK2,sK1))
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_36
    | ~ spl13_42
    | ~ spl13_45
    | ~ spl13_46
    | ~ spl13_49
    | ~ spl13_50
    | ~ spl13_52
    | ~ spl13_55
    | ~ spl13_82
    | ~ spl13_85
    | ~ spl13_260
    | ~ spl13_262
    | ~ spl13_264
    | ~ spl13_266
    | ~ spl13_268
    | ~ spl13_270
    | ~ spl13_272
    | ~ spl13_274
    | ~ spl13_276
    | ~ spl13_279
    | ~ spl13_280
    | ~ spl13_282
    | ~ spl13_284 ),
    inference(subsumption_resolution,[],[f8179,f541])).

fof(f8179,plain,
    ( v5_pre_topc(sK7(sK0,sK2,sK1),k1_tsep_1(sK0,sK1,sK2),sK6(sK0,sK2,sK1))
    | ~ r1_tsep_1(sK2,sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_36
    | ~ spl13_42
    | ~ spl13_45
    | ~ spl13_46
    | ~ spl13_49
    | ~ spl13_50
    | ~ spl13_52
    | ~ spl13_55
    | ~ spl13_85
    | ~ spl13_260
    | ~ spl13_262
    | ~ spl13_264
    | ~ spl13_266
    | ~ spl13_268
    | ~ spl13_270
    | ~ spl13_272
    | ~ spl13_274
    | ~ spl13_276
    | ~ spl13_279
    | ~ spl13_280
    | ~ spl13_282
    | ~ spl13_284 ),
    inference(subsumption_resolution,[],[f8178,f566])).

fof(f8178,plain,
    ( v5_pre_topc(sK7(sK0,sK2,sK1),k1_tsep_1(sK0,sK1,sK2),sK6(sK0,sK2,sK1))
    | r3_tsep_1(sK0,sK2,sK1)
    | ~ r1_tsep_1(sK2,sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_36
    | ~ spl13_42
    | ~ spl13_45
    | ~ spl13_46
    | ~ spl13_49
    | ~ spl13_50
    | ~ spl13_52
    | ~ spl13_55
    | ~ spl13_260
    | ~ spl13_262
    | ~ spl13_264
    | ~ spl13_266
    | ~ spl13_268
    | ~ spl13_270
    | ~ spl13_272
    | ~ spl13_274
    | ~ spl13_276
    | ~ spl13_279
    | ~ spl13_280
    | ~ spl13_282
    | ~ spl13_284 ),
    inference(subsumption_resolution,[],[f8177,f3854])).

fof(f3854,plain,
    ( v1_funct_1(sK7(sK0,sK2,sK1))
    | ~ spl13_280 ),
    inference(avatar_component_clause,[],[f3853])).

fof(f8177,plain,
    ( v5_pre_topc(sK7(sK0,sK2,sK1),k1_tsep_1(sK0,sK1,sK2),sK6(sK0,sK2,sK1))
    | ~ v1_funct_1(sK7(sK0,sK2,sK1))
    | r3_tsep_1(sK0,sK2,sK1)
    | ~ r1_tsep_1(sK2,sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_36
    | ~ spl13_42
    | ~ spl13_45
    | ~ spl13_46
    | ~ spl13_49
    | ~ spl13_50
    | ~ spl13_52
    | ~ spl13_55
    | ~ spl13_260
    | ~ spl13_262
    | ~ spl13_264
    | ~ spl13_266
    | ~ spl13_268
    | ~ spl13_270
    | ~ spl13_272
    | ~ spl13_274
    | ~ spl13_276
    | ~ spl13_279
    | ~ spl13_282
    | ~ spl13_284 ),
    inference(subsumption_resolution,[],[f8176,f3860])).

fof(f3860,plain,
    ( v1_funct_2(sK7(sK0,sK2,sK1),u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK6(sK0,sK2,sK1)))
    | ~ spl13_282 ),
    inference(avatar_component_clause,[],[f3859])).

fof(f8176,plain,
    ( v5_pre_topc(sK7(sK0,sK2,sK1),k1_tsep_1(sK0,sK1,sK2),sK6(sK0,sK2,sK1))
    | ~ v1_funct_2(sK7(sK0,sK2,sK1),u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK6(sK0,sK2,sK1)))
    | ~ v1_funct_1(sK7(sK0,sK2,sK1))
    | r3_tsep_1(sK0,sK2,sK1)
    | ~ r1_tsep_1(sK2,sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_36
    | ~ spl13_42
    | ~ spl13_45
    | ~ spl13_46
    | ~ spl13_49
    | ~ spl13_50
    | ~ spl13_52
    | ~ spl13_55
    | ~ spl13_260
    | ~ spl13_262
    | ~ spl13_264
    | ~ spl13_266
    | ~ spl13_268
    | ~ spl13_270
    | ~ spl13_272
    | ~ spl13_274
    | ~ spl13_276
    | ~ spl13_279
    | ~ spl13_284 ),
    inference(subsumption_resolution,[],[f8175,f3866])).

fof(f3866,plain,
    ( m1_subset_1(sK7(sK0,sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK6(sK0,sK2,sK1)))))
    | ~ spl13_284 ),
    inference(avatar_component_clause,[],[f3865])).

fof(f8175,plain,
    ( v5_pre_topc(sK7(sK0,sK2,sK1),k1_tsep_1(sK0,sK1,sK2),sK6(sK0,sK2,sK1))
    | ~ m1_subset_1(sK7(sK0,sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK6(sK0,sK2,sK1)))))
    | ~ v1_funct_2(sK7(sK0,sK2,sK1),u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK6(sK0,sK2,sK1)))
    | ~ v1_funct_1(sK7(sK0,sK2,sK1))
    | r3_tsep_1(sK0,sK2,sK1)
    | ~ r1_tsep_1(sK2,sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_36
    | ~ spl13_42
    | ~ spl13_45
    | ~ spl13_46
    | ~ spl13_49
    | ~ spl13_50
    | ~ spl13_52
    | ~ spl13_55
    | ~ spl13_260
    | ~ spl13_262
    | ~ spl13_264
    | ~ spl13_266
    | ~ spl13_268
    | ~ spl13_270
    | ~ spl13_272
    | ~ spl13_274
    | ~ spl13_276
    | ~ spl13_279 ),
    inference(subsumption_resolution,[],[f8174,f3794])).

fof(f3794,plain,
    ( v5_pre_topc(k3_tmap_1(sK0,sK6(sK0,sK2,sK1),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK2,sK1)),sK2,sK6(sK0,sK2,sK1))
    | ~ spl13_260 ),
    inference(avatar_component_clause,[],[f3793])).

fof(f8174,plain,
    ( ~ v5_pre_topc(k3_tmap_1(sK0,sK6(sK0,sK2,sK1),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK2,sK1)),sK2,sK6(sK0,sK2,sK1))
    | v5_pre_topc(sK7(sK0,sK2,sK1),k1_tsep_1(sK0,sK1,sK2),sK6(sK0,sK2,sK1))
    | ~ m1_subset_1(sK7(sK0,sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK6(sK0,sK2,sK1)))))
    | ~ v1_funct_2(sK7(sK0,sK2,sK1),u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK6(sK0,sK2,sK1)))
    | ~ v1_funct_1(sK7(sK0,sK2,sK1))
    | r3_tsep_1(sK0,sK2,sK1)
    | ~ r1_tsep_1(sK2,sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_36
    | ~ spl13_42
    | ~ spl13_45
    | ~ spl13_46
    | ~ spl13_49
    | ~ spl13_50
    | ~ spl13_52
    | ~ spl13_55
    | ~ spl13_262
    | ~ spl13_264
    | ~ spl13_266
    | ~ spl13_268
    | ~ spl13_270
    | ~ spl13_272
    | ~ spl13_274
    | ~ spl13_276
    | ~ spl13_279 ),
    inference(subsumption_resolution,[],[f8173,f3800])).

fof(f3800,plain,
    ( v1_funct_2(k3_tmap_1(sK0,sK6(sK0,sK2,sK1),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK2,sK1)),u1_struct_0(sK2),u1_struct_0(sK6(sK0,sK2,sK1)))
    | ~ spl13_262 ),
    inference(avatar_component_clause,[],[f3799])).

fof(f8173,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK0,sK6(sK0,sK2,sK1),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK2,sK1)),u1_struct_0(sK2),u1_struct_0(sK6(sK0,sK2,sK1)))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK6(sK0,sK2,sK1),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK2,sK1)),sK2,sK6(sK0,sK2,sK1))
    | v5_pre_topc(sK7(sK0,sK2,sK1),k1_tsep_1(sK0,sK1,sK2),sK6(sK0,sK2,sK1))
    | ~ m1_subset_1(sK7(sK0,sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK6(sK0,sK2,sK1)))))
    | ~ v1_funct_2(sK7(sK0,sK2,sK1),u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK6(sK0,sK2,sK1)))
    | ~ v1_funct_1(sK7(sK0,sK2,sK1))
    | r3_tsep_1(sK0,sK2,sK1)
    | ~ r1_tsep_1(sK2,sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_36
    | ~ spl13_42
    | ~ spl13_45
    | ~ spl13_46
    | ~ spl13_49
    | ~ spl13_50
    | ~ spl13_52
    | ~ spl13_55
    | ~ spl13_264
    | ~ spl13_266
    | ~ spl13_268
    | ~ spl13_270
    | ~ spl13_272
    | ~ spl13_274
    | ~ spl13_276
    | ~ spl13_279 ),
    inference(subsumption_resolution,[],[f8172,f3806])).

fof(f3806,plain,
    ( v1_funct_1(k3_tmap_1(sK0,sK6(sK0,sK2,sK1),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK2,sK1)))
    | ~ spl13_264 ),
    inference(avatar_component_clause,[],[f3805])).

fof(f8172,plain,
    ( ~ v1_funct_1(k3_tmap_1(sK0,sK6(sK0,sK2,sK1),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK2,sK1)))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK6(sK0,sK2,sK1),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK2,sK1)),u1_struct_0(sK2),u1_struct_0(sK6(sK0,sK2,sK1)))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK6(sK0,sK2,sK1),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK2,sK1)),sK2,sK6(sK0,sK2,sK1))
    | v5_pre_topc(sK7(sK0,sK2,sK1),k1_tsep_1(sK0,sK1,sK2),sK6(sK0,sK2,sK1))
    | ~ m1_subset_1(sK7(sK0,sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK6(sK0,sK2,sK1)))))
    | ~ v1_funct_2(sK7(sK0,sK2,sK1),u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK6(sK0,sK2,sK1)))
    | ~ v1_funct_1(sK7(sK0,sK2,sK1))
    | r3_tsep_1(sK0,sK2,sK1)
    | ~ r1_tsep_1(sK2,sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_36
    | ~ spl13_42
    | ~ spl13_45
    | ~ spl13_46
    | ~ spl13_49
    | ~ spl13_50
    | ~ spl13_52
    | ~ spl13_55
    | ~ spl13_266
    | ~ spl13_268
    | ~ spl13_270
    | ~ spl13_272
    | ~ spl13_274
    | ~ spl13_276
    | ~ spl13_279 ),
    inference(subsumption_resolution,[],[f8171,f3812])).

fof(f3812,plain,
    ( m1_subset_1(k3_tmap_1(sK0,sK6(sK0,sK2,sK1),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK2,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK6(sK0,sK2,sK1)))))
    | ~ spl13_266 ),
    inference(avatar_component_clause,[],[f3811])).

fof(f8171,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK0,sK6(sK0,sK2,sK1),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK2,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK6(sK0,sK2,sK1)))))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK6(sK0,sK2,sK1),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK2,sK1)))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK6(sK0,sK2,sK1),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK2,sK1)),u1_struct_0(sK2),u1_struct_0(sK6(sK0,sK2,sK1)))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK6(sK0,sK2,sK1),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK2,sK1)),sK2,sK6(sK0,sK2,sK1))
    | v5_pre_topc(sK7(sK0,sK2,sK1),k1_tsep_1(sK0,sK1,sK2),sK6(sK0,sK2,sK1))
    | ~ m1_subset_1(sK7(sK0,sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK6(sK0,sK2,sK1)))))
    | ~ v1_funct_2(sK7(sK0,sK2,sK1),u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK6(sK0,sK2,sK1)))
    | ~ v1_funct_1(sK7(sK0,sK2,sK1))
    | r3_tsep_1(sK0,sK2,sK1)
    | ~ r1_tsep_1(sK2,sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_36
    | ~ spl13_42
    | ~ spl13_45
    | ~ spl13_46
    | ~ spl13_49
    | ~ spl13_50
    | ~ spl13_52
    | ~ spl13_55
    | ~ spl13_268
    | ~ spl13_270
    | ~ spl13_272
    | ~ spl13_274
    | ~ spl13_276
    | ~ spl13_279 ),
    inference(subsumption_resolution,[],[f8170,f3818])).

fof(f3818,plain,
    ( v5_pre_topc(k3_tmap_1(sK0,sK6(sK0,sK2,sK1),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK2,sK1)),sK1,sK6(sK0,sK2,sK1))
    | ~ spl13_268 ),
    inference(avatar_component_clause,[],[f3817])).

fof(f8170,plain,
    ( ~ v5_pre_topc(k3_tmap_1(sK0,sK6(sK0,sK2,sK1),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK2,sK1)),sK1,sK6(sK0,sK2,sK1))
    | ~ m1_subset_1(k3_tmap_1(sK0,sK6(sK0,sK2,sK1),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK2,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK6(sK0,sK2,sK1)))))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK6(sK0,sK2,sK1),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK2,sK1)))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK6(sK0,sK2,sK1),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK2,sK1)),u1_struct_0(sK2),u1_struct_0(sK6(sK0,sK2,sK1)))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK6(sK0,sK2,sK1),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK2,sK1)),sK2,sK6(sK0,sK2,sK1))
    | v5_pre_topc(sK7(sK0,sK2,sK1),k1_tsep_1(sK0,sK1,sK2),sK6(sK0,sK2,sK1))
    | ~ m1_subset_1(sK7(sK0,sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK6(sK0,sK2,sK1)))))
    | ~ v1_funct_2(sK7(sK0,sK2,sK1),u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK6(sK0,sK2,sK1)))
    | ~ v1_funct_1(sK7(sK0,sK2,sK1))
    | r3_tsep_1(sK0,sK2,sK1)
    | ~ r1_tsep_1(sK2,sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_36
    | ~ spl13_42
    | ~ spl13_45
    | ~ spl13_46
    | ~ spl13_49
    | ~ spl13_50
    | ~ spl13_52
    | ~ spl13_55
    | ~ spl13_270
    | ~ spl13_272
    | ~ spl13_274
    | ~ spl13_276
    | ~ spl13_279 ),
    inference(subsumption_resolution,[],[f8169,f3824])).

fof(f3824,plain,
    ( v1_funct_2(k3_tmap_1(sK0,sK6(sK0,sK2,sK1),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK2,sK1)),u1_struct_0(sK1),u1_struct_0(sK6(sK0,sK2,sK1)))
    | ~ spl13_270 ),
    inference(avatar_component_clause,[],[f3823])).

fof(f8169,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK0,sK6(sK0,sK2,sK1),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK2,sK1)),u1_struct_0(sK1),u1_struct_0(sK6(sK0,sK2,sK1)))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK6(sK0,sK2,sK1),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK2,sK1)),sK1,sK6(sK0,sK2,sK1))
    | ~ m1_subset_1(k3_tmap_1(sK0,sK6(sK0,sK2,sK1),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK2,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK6(sK0,sK2,sK1)))))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK6(sK0,sK2,sK1),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK2,sK1)))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK6(sK0,sK2,sK1),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK2,sK1)),u1_struct_0(sK2),u1_struct_0(sK6(sK0,sK2,sK1)))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK6(sK0,sK2,sK1),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK2,sK1)),sK2,sK6(sK0,sK2,sK1))
    | v5_pre_topc(sK7(sK0,sK2,sK1),k1_tsep_1(sK0,sK1,sK2),sK6(sK0,sK2,sK1))
    | ~ m1_subset_1(sK7(sK0,sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK6(sK0,sK2,sK1)))))
    | ~ v1_funct_2(sK7(sK0,sK2,sK1),u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK6(sK0,sK2,sK1)))
    | ~ v1_funct_1(sK7(sK0,sK2,sK1))
    | r3_tsep_1(sK0,sK2,sK1)
    | ~ r1_tsep_1(sK2,sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_36
    | ~ spl13_42
    | ~ spl13_45
    | ~ spl13_46
    | ~ spl13_49
    | ~ spl13_50
    | ~ spl13_52
    | ~ spl13_55
    | ~ spl13_272
    | ~ spl13_274
    | ~ spl13_276
    | ~ spl13_279 ),
    inference(subsumption_resolution,[],[f8168,f3830])).

fof(f3830,plain,
    ( v1_funct_1(k3_tmap_1(sK0,sK6(sK0,sK2,sK1),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK2,sK1)))
    | ~ spl13_272 ),
    inference(avatar_component_clause,[],[f3829])).

fof(f8168,plain,
    ( ~ v1_funct_1(k3_tmap_1(sK0,sK6(sK0,sK2,sK1),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK2,sK1)))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK6(sK0,sK2,sK1),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK2,sK1)),u1_struct_0(sK1),u1_struct_0(sK6(sK0,sK2,sK1)))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK6(sK0,sK2,sK1),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK2,sK1)),sK1,sK6(sK0,sK2,sK1))
    | ~ m1_subset_1(k3_tmap_1(sK0,sK6(sK0,sK2,sK1),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK2,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK6(sK0,sK2,sK1)))))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK6(sK0,sK2,sK1),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK2,sK1)))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK6(sK0,sK2,sK1),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK2,sK1)),u1_struct_0(sK2),u1_struct_0(sK6(sK0,sK2,sK1)))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK6(sK0,sK2,sK1),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK2,sK1)),sK2,sK6(sK0,sK2,sK1))
    | v5_pre_topc(sK7(sK0,sK2,sK1),k1_tsep_1(sK0,sK1,sK2),sK6(sK0,sK2,sK1))
    | ~ m1_subset_1(sK7(sK0,sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK6(sK0,sK2,sK1)))))
    | ~ v1_funct_2(sK7(sK0,sK2,sK1),u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK6(sK0,sK2,sK1)))
    | ~ v1_funct_1(sK7(sK0,sK2,sK1))
    | r3_tsep_1(sK0,sK2,sK1)
    | ~ r1_tsep_1(sK2,sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_36
    | ~ spl13_42
    | ~ spl13_45
    | ~ spl13_46
    | ~ spl13_49
    | ~ spl13_50
    | ~ spl13_52
    | ~ spl13_55
    | ~ spl13_274
    | ~ spl13_276
    | ~ spl13_279 ),
    inference(subsumption_resolution,[],[f8167,f3836])).

fof(f3836,plain,
    ( l1_pre_topc(sK6(sK0,sK2,sK1))
    | ~ spl13_274 ),
    inference(avatar_component_clause,[],[f3835])).

fof(f8167,plain,
    ( ~ l1_pre_topc(sK6(sK0,sK2,sK1))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK6(sK0,sK2,sK1),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK2,sK1)))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK6(sK0,sK2,sK1),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK2,sK1)),u1_struct_0(sK1),u1_struct_0(sK6(sK0,sK2,sK1)))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK6(sK0,sK2,sK1),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK2,sK1)),sK1,sK6(sK0,sK2,sK1))
    | ~ m1_subset_1(k3_tmap_1(sK0,sK6(sK0,sK2,sK1),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK2,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK6(sK0,sK2,sK1)))))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK6(sK0,sK2,sK1),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK2,sK1)))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK6(sK0,sK2,sK1),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK2,sK1)),u1_struct_0(sK2),u1_struct_0(sK6(sK0,sK2,sK1)))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK6(sK0,sK2,sK1),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK2,sK1)),sK2,sK6(sK0,sK2,sK1))
    | v5_pre_topc(sK7(sK0,sK2,sK1),k1_tsep_1(sK0,sK1,sK2),sK6(sK0,sK2,sK1))
    | ~ m1_subset_1(sK7(sK0,sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK6(sK0,sK2,sK1)))))
    | ~ v1_funct_2(sK7(sK0,sK2,sK1),u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK6(sK0,sK2,sK1)))
    | ~ v1_funct_1(sK7(sK0,sK2,sK1))
    | r3_tsep_1(sK0,sK2,sK1)
    | ~ r1_tsep_1(sK2,sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_36
    | ~ spl13_42
    | ~ spl13_45
    | ~ spl13_46
    | ~ spl13_49
    | ~ spl13_50
    | ~ spl13_52
    | ~ spl13_55
    | ~ spl13_276
    | ~ spl13_279 ),
    inference(subsumption_resolution,[],[f8166,f3842])).

fof(f3842,plain,
    ( v2_pre_topc(sK6(sK0,sK2,sK1))
    | ~ spl13_276 ),
    inference(avatar_component_clause,[],[f3841])).

fof(f8166,plain,
    ( ~ v2_pre_topc(sK6(sK0,sK2,sK1))
    | ~ l1_pre_topc(sK6(sK0,sK2,sK1))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK6(sK0,sK2,sK1),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK2,sK1)))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK6(sK0,sK2,sK1),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK2,sK1)),u1_struct_0(sK1),u1_struct_0(sK6(sK0,sK2,sK1)))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK6(sK0,sK2,sK1),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK2,sK1)),sK1,sK6(sK0,sK2,sK1))
    | ~ m1_subset_1(k3_tmap_1(sK0,sK6(sK0,sK2,sK1),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK2,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK6(sK0,sK2,sK1)))))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK6(sK0,sK2,sK1),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK2,sK1)))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK6(sK0,sK2,sK1),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK2,sK1)),u1_struct_0(sK2),u1_struct_0(sK6(sK0,sK2,sK1)))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK6(sK0,sK2,sK1),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK2,sK1)),sK2,sK6(sK0,sK2,sK1))
    | v5_pre_topc(sK7(sK0,sK2,sK1),k1_tsep_1(sK0,sK1,sK2),sK6(sK0,sK2,sK1))
    | ~ m1_subset_1(sK7(sK0,sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK6(sK0,sK2,sK1)))))
    | ~ v1_funct_2(sK7(sK0,sK2,sK1),u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK6(sK0,sK2,sK1)))
    | ~ v1_funct_1(sK7(sK0,sK2,sK1))
    | r3_tsep_1(sK0,sK2,sK1)
    | ~ r1_tsep_1(sK2,sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_36
    | ~ spl13_42
    | ~ spl13_45
    | ~ spl13_46
    | ~ spl13_49
    | ~ spl13_50
    | ~ spl13_52
    | ~ spl13_55
    | ~ spl13_279 ),
    inference(subsumption_resolution,[],[f8034,f3848])).

fof(f3848,plain,
    ( ~ v2_struct_0(sK6(sK0,sK2,sK1))
    | ~ spl13_279 ),
    inference(avatar_component_clause,[],[f3847])).

fof(f8034,plain,
    ( v2_struct_0(sK6(sK0,sK2,sK1))
    | ~ v2_pre_topc(sK6(sK0,sK2,sK1))
    | ~ l1_pre_topc(sK6(sK0,sK2,sK1))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK6(sK0,sK2,sK1),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK2,sK1)))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK6(sK0,sK2,sK1),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK2,sK1)),u1_struct_0(sK1),u1_struct_0(sK6(sK0,sK2,sK1)))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK6(sK0,sK2,sK1),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK2,sK1)),sK1,sK6(sK0,sK2,sK1))
    | ~ m1_subset_1(k3_tmap_1(sK0,sK6(sK0,sK2,sK1),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK2,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK6(sK0,sK2,sK1)))))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK6(sK0,sK2,sK1),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK2,sK1)))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK6(sK0,sK2,sK1),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK2,sK1)),u1_struct_0(sK2),u1_struct_0(sK6(sK0,sK2,sK1)))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK6(sK0,sK2,sK1),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK2,sK1)),sK2,sK6(sK0,sK2,sK1))
    | v5_pre_topc(sK7(sK0,sK2,sK1),k1_tsep_1(sK0,sK1,sK2),sK6(sK0,sK2,sK1))
    | ~ m1_subset_1(sK7(sK0,sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK6(sK0,sK2,sK1)))))
    | ~ v1_funct_2(sK7(sK0,sK2,sK1),u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK6(sK0,sK2,sK1)))
    | ~ v1_funct_1(sK7(sK0,sK2,sK1))
    | r3_tsep_1(sK0,sK2,sK1)
    | ~ r1_tsep_1(sK2,sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_36
    | ~ spl13_42
    | ~ spl13_45
    | ~ spl13_46
    | ~ spl13_49
    | ~ spl13_50
    | ~ spl13_52
    | ~ spl13_55 ),
    inference(resolution,[],[f5130,f751])).

fof(f751,plain,(
    ! [X4,X5,X3] :
      ( m1_subset_1(k3_tmap_1(X3,sK6(X3,X4,X5),k1_tsep_1(X3,X5,X4),X4,sK7(X3,X4,X5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK6(X3,X4,X5)))))
      | r3_tsep_1(X3,X4,X5)
      | ~ r1_tsep_1(X4,X5)
      | ~ m1_pre_topc(X5,X3)
      | v2_struct_0(X5)
      | ~ m1_pre_topc(X4,X3)
      | v2_struct_0(X4)
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | v2_struct_0(X3) ) ),
    inference(duplicate_literal_removal,[],[f750])).

fof(f750,plain,(
    ! [X4,X5,X3] :
      ( m1_subset_1(k3_tmap_1(X3,sK6(X3,X4,X5),k1_tsep_1(X3,X5,X4),X4,sK7(X3,X4,X5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK6(X3,X4,X5)))))
      | r3_tsep_1(X3,X4,X5)
      | ~ r1_tsep_1(X4,X5)
      | ~ m1_pre_topc(X5,X3)
      | v2_struct_0(X5)
      | ~ m1_pre_topc(X4,X3)
      | v2_struct_0(X4)
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X5,X3)
      | v2_struct_0(X5)
      | ~ m1_pre_topc(X4,X3)
      | v2_struct_0(X4)
      | ~ l1_pre_topc(X3)
      | v2_struct_0(X3) ) ),
    inference(superposition,[],[f178,f163])).

fof(f178,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k3_tmap_1(X0,sK6(X0,X1,X2),k1_tsep_1(X0,X1,X2),X1,sK7(X0,X1,X2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK6(X0,X1,X2)))))
      | r3_tsep_1(X0,X1,X2)
      | ~ r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f119])).

fof(f5130,plain,
    ( ! [X8,X9] :
        ( ~ m1_subset_1(k3_tmap_1(sK0,X8,k1_tsep_1(sK0,sK1,sK2),sK2,X9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X8))))
        | v2_struct_0(X8)
        | ~ v2_pre_topc(X8)
        | ~ l1_pre_topc(X8)
        | ~ v1_funct_1(k3_tmap_1(sK0,X8,k1_tsep_1(sK0,sK1,sK2),sK1,X9))
        | ~ v1_funct_2(k3_tmap_1(sK0,X8,k1_tsep_1(sK0,sK1,sK2),sK1,X9),u1_struct_0(sK1),u1_struct_0(X8))
        | ~ v5_pre_topc(k3_tmap_1(sK0,X8,k1_tsep_1(sK0,sK1,sK2),sK1,X9),sK1,X8)
        | ~ m1_subset_1(k3_tmap_1(sK0,X8,k1_tsep_1(sK0,sK1,sK2),sK1,X9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X8))))
        | ~ v1_funct_1(k3_tmap_1(sK0,X8,k1_tsep_1(sK0,sK1,sK2),sK2,X9))
        | ~ v1_funct_2(k3_tmap_1(sK0,X8,k1_tsep_1(sK0,sK1,sK2),sK2,X9),u1_struct_0(sK2),u1_struct_0(X8))
        | ~ v5_pre_topc(k3_tmap_1(sK0,X8,k1_tsep_1(sK0,sK1,sK2),sK2,X9),sK2,X8)
        | v5_pre_topc(X9,k1_tsep_1(sK0,sK1,sK2),X8)
        | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(X8))))
        | ~ v1_funct_2(X9,u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(X8))
        | ~ v1_funct_1(X9) )
    | ~ spl13_36
    | ~ spl13_42
    | ~ spl13_45
    | ~ spl13_46
    | ~ spl13_49
    | ~ spl13_50
    | ~ spl13_52
    | ~ spl13_55 ),
    inference(subsumption_resolution,[],[f5129,f410])).

fof(f5129,plain,
    ( ! [X8,X9] :
        ( v5_pre_topc(X9,k1_tsep_1(sK0,sK1,sK2),X8)
        | v2_struct_0(X8)
        | ~ v2_pre_topc(X8)
        | ~ l1_pre_topc(X8)
        | ~ v1_funct_1(k3_tmap_1(sK0,X8,k1_tsep_1(sK0,sK1,sK2),sK1,X9))
        | ~ v1_funct_2(k3_tmap_1(sK0,X8,k1_tsep_1(sK0,sK1,sK2),sK1,X9),u1_struct_0(sK1),u1_struct_0(X8))
        | ~ v5_pre_topc(k3_tmap_1(sK0,X8,k1_tsep_1(sK0,sK1,sK2),sK1,X9),sK1,X8)
        | ~ m1_subset_1(k3_tmap_1(sK0,X8,k1_tsep_1(sK0,sK1,sK2),sK1,X9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X8))))
        | ~ v1_funct_1(k3_tmap_1(sK0,X8,k1_tsep_1(sK0,sK1,sK2),sK2,X9))
        | ~ v1_funct_2(k3_tmap_1(sK0,X8,k1_tsep_1(sK0,sK1,sK2),sK2,X9),u1_struct_0(sK2),u1_struct_0(X8))
        | ~ v5_pre_topc(k3_tmap_1(sK0,X8,k1_tsep_1(sK0,sK1,sK2),sK2,X9),sK2,X8)
        | ~ m1_subset_1(k3_tmap_1(sK0,X8,k1_tsep_1(sK0,sK1,sK2),sK2,X9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X8))))
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(X8))))
        | ~ v1_funct_2(X9,u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(X8))
        | ~ v1_funct_1(X9) )
    | ~ spl13_36
    | ~ spl13_42
    | ~ spl13_45
    | ~ spl13_46
    | ~ spl13_49
    | ~ spl13_50
    | ~ spl13_52 ),
    inference(subsumption_resolution,[],[f5128,f403])).

fof(f5128,plain,
    ( ! [X8,X9] :
        ( v5_pre_topc(X9,k1_tsep_1(sK0,sK1,sK2),X8)
        | v2_struct_0(X8)
        | ~ v2_pre_topc(X8)
        | ~ l1_pre_topc(X8)
        | ~ v1_funct_1(k3_tmap_1(sK0,X8,k1_tsep_1(sK0,sK1,sK2),sK1,X9))
        | ~ v1_funct_2(k3_tmap_1(sK0,X8,k1_tsep_1(sK0,sK1,sK2),sK1,X9),u1_struct_0(sK1),u1_struct_0(X8))
        | ~ v5_pre_topc(k3_tmap_1(sK0,X8,k1_tsep_1(sK0,sK1,sK2),sK1,X9),sK1,X8)
        | ~ m1_subset_1(k3_tmap_1(sK0,X8,k1_tsep_1(sK0,sK1,sK2),sK1,X9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X8))))
        | ~ v1_funct_1(k3_tmap_1(sK0,X8,k1_tsep_1(sK0,sK1,sK2),sK2,X9))
        | ~ v1_funct_2(k3_tmap_1(sK0,X8,k1_tsep_1(sK0,sK1,sK2),sK2,X9),u1_struct_0(sK2),u1_struct_0(X8))
        | ~ v5_pre_topc(k3_tmap_1(sK0,X8,k1_tsep_1(sK0,sK1,sK2),sK2,X9),sK2,X8)
        | ~ m1_subset_1(k3_tmap_1(sK0,X8,k1_tsep_1(sK0,sK1,sK2),sK2,X9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X8))))
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(X8))))
        | ~ v1_funct_2(X9,u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(X8))
        | ~ v1_funct_1(X9) )
    | ~ spl13_36
    | ~ spl13_42
    | ~ spl13_45
    | ~ spl13_46
    | ~ spl13_49
    | ~ spl13_50 ),
    inference(subsumption_resolution,[],[f5127,f396])).

fof(f5127,plain,
    ( ! [X8,X9] :
        ( v5_pre_topc(X9,k1_tsep_1(sK0,sK1,sK2),X8)
        | v2_struct_0(X8)
        | ~ v2_pre_topc(X8)
        | ~ l1_pre_topc(X8)
        | ~ v1_funct_1(k3_tmap_1(sK0,X8,k1_tsep_1(sK0,sK1,sK2),sK1,X9))
        | ~ v1_funct_2(k3_tmap_1(sK0,X8,k1_tsep_1(sK0,sK1,sK2),sK1,X9),u1_struct_0(sK1),u1_struct_0(X8))
        | ~ v5_pre_topc(k3_tmap_1(sK0,X8,k1_tsep_1(sK0,sK1,sK2),sK1,X9),sK1,X8)
        | ~ m1_subset_1(k3_tmap_1(sK0,X8,k1_tsep_1(sK0,sK1,sK2),sK1,X9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X8))))
        | ~ v1_funct_1(k3_tmap_1(sK0,X8,k1_tsep_1(sK0,sK1,sK2),sK2,X9))
        | ~ v1_funct_2(k3_tmap_1(sK0,X8,k1_tsep_1(sK0,sK1,sK2),sK2,X9),u1_struct_0(sK2),u1_struct_0(X8))
        | ~ v5_pre_topc(k3_tmap_1(sK0,X8,k1_tsep_1(sK0,sK1,sK2),sK2,X9),sK2,X8)
        | ~ m1_subset_1(k3_tmap_1(sK0,X8,k1_tsep_1(sK0,sK1,sK2),sK2,X9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X8))))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(X8))))
        | ~ v1_funct_2(X9,u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(X8))
        | ~ v1_funct_1(X9) )
    | ~ spl13_36
    | ~ spl13_42
    | ~ spl13_45
    | ~ spl13_46
    | ~ spl13_49 ),
    inference(subsumption_resolution,[],[f5126,f389])).

fof(f5126,plain,
    ( ! [X8,X9] :
        ( v5_pre_topc(X9,k1_tsep_1(sK0,sK1,sK2),X8)
        | v2_struct_0(X8)
        | ~ v2_pre_topc(X8)
        | ~ l1_pre_topc(X8)
        | ~ v1_funct_1(k3_tmap_1(sK0,X8,k1_tsep_1(sK0,sK1,sK2),sK1,X9))
        | ~ v1_funct_2(k3_tmap_1(sK0,X8,k1_tsep_1(sK0,sK1,sK2),sK1,X9),u1_struct_0(sK1),u1_struct_0(X8))
        | ~ v5_pre_topc(k3_tmap_1(sK0,X8,k1_tsep_1(sK0,sK1,sK2),sK1,X9),sK1,X8)
        | ~ m1_subset_1(k3_tmap_1(sK0,X8,k1_tsep_1(sK0,sK1,sK2),sK1,X9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X8))))
        | ~ v1_funct_1(k3_tmap_1(sK0,X8,k1_tsep_1(sK0,sK1,sK2),sK2,X9))
        | ~ v1_funct_2(k3_tmap_1(sK0,X8,k1_tsep_1(sK0,sK1,sK2),sK2,X9),u1_struct_0(sK2),u1_struct_0(X8))
        | ~ v5_pre_topc(k3_tmap_1(sK0,X8,k1_tsep_1(sK0,sK1,sK2),sK2,X9),sK2,X8)
        | ~ m1_subset_1(k3_tmap_1(sK0,X8,k1_tsep_1(sK0,sK1,sK2),sK2,X9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X8))))
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(X8))))
        | ~ v1_funct_2(X9,u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(X8))
        | ~ v1_funct_1(X9) )
    | ~ spl13_36
    | ~ spl13_42
    | ~ spl13_45
    | ~ spl13_46 ),
    inference(subsumption_resolution,[],[f5125,f382])).

fof(f5125,plain,
    ( ! [X8,X9] :
        ( v5_pre_topc(X9,k1_tsep_1(sK0,sK1,sK2),X8)
        | v2_struct_0(X8)
        | ~ v2_pre_topc(X8)
        | ~ l1_pre_topc(X8)
        | ~ v1_funct_1(k3_tmap_1(sK0,X8,k1_tsep_1(sK0,sK1,sK2),sK1,X9))
        | ~ v1_funct_2(k3_tmap_1(sK0,X8,k1_tsep_1(sK0,sK1,sK2),sK1,X9),u1_struct_0(sK1),u1_struct_0(X8))
        | ~ v5_pre_topc(k3_tmap_1(sK0,X8,k1_tsep_1(sK0,sK1,sK2),sK1,X9),sK1,X8)
        | ~ m1_subset_1(k3_tmap_1(sK0,X8,k1_tsep_1(sK0,sK1,sK2),sK1,X9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X8))))
        | ~ v1_funct_1(k3_tmap_1(sK0,X8,k1_tsep_1(sK0,sK1,sK2),sK2,X9))
        | ~ v1_funct_2(k3_tmap_1(sK0,X8,k1_tsep_1(sK0,sK1,sK2),sK2,X9),u1_struct_0(sK2),u1_struct_0(X8))
        | ~ v5_pre_topc(k3_tmap_1(sK0,X8,k1_tsep_1(sK0,sK1,sK2),sK2,X9),sK2,X8)
        | ~ m1_subset_1(k3_tmap_1(sK0,X8,k1_tsep_1(sK0,sK1,sK2),sK2,X9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X8))))
        | ~ m1_pre_topc(sK1,sK0)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(X8))))
        | ~ v1_funct_2(X9,u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(X8))
        | ~ v1_funct_1(X9) )
    | ~ spl13_36
    | ~ spl13_42
    | ~ spl13_45 ),
    inference(subsumption_resolution,[],[f5124,f375])).

fof(f5124,plain,
    ( ! [X8,X9] :
        ( v5_pre_topc(X9,k1_tsep_1(sK0,sK1,sK2),X8)
        | v2_struct_0(X8)
        | ~ v2_pre_topc(X8)
        | ~ l1_pre_topc(X8)
        | ~ v1_funct_1(k3_tmap_1(sK0,X8,k1_tsep_1(sK0,sK1,sK2),sK1,X9))
        | ~ v1_funct_2(k3_tmap_1(sK0,X8,k1_tsep_1(sK0,sK1,sK2),sK1,X9),u1_struct_0(sK1),u1_struct_0(X8))
        | ~ v5_pre_topc(k3_tmap_1(sK0,X8,k1_tsep_1(sK0,sK1,sK2),sK1,X9),sK1,X8)
        | ~ m1_subset_1(k3_tmap_1(sK0,X8,k1_tsep_1(sK0,sK1,sK2),sK1,X9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X8))))
        | ~ v1_funct_1(k3_tmap_1(sK0,X8,k1_tsep_1(sK0,sK1,sK2),sK2,X9))
        | ~ v1_funct_2(k3_tmap_1(sK0,X8,k1_tsep_1(sK0,sK1,sK2),sK2,X9),u1_struct_0(sK2),u1_struct_0(X8))
        | ~ v5_pre_topc(k3_tmap_1(sK0,X8,k1_tsep_1(sK0,sK1,sK2),sK2,X9),sK2,X8)
        | ~ m1_subset_1(k3_tmap_1(sK0,X8,k1_tsep_1(sK0,sK1,sK2),sK2,X9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X8))))
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(sK1,sK0)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(X8))))
        | ~ v1_funct_2(X9,u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(X8))
        | ~ v1_funct_1(X9) )
    | ~ spl13_36
    | ~ spl13_42 ),
    inference(subsumption_resolution,[],[f5118,f368])).

fof(f5118,plain,
    ( ! [X8,X9] :
        ( v5_pre_topc(X9,k1_tsep_1(sK0,sK1,sK2),X8)
        | v2_struct_0(X8)
        | ~ v2_pre_topc(X8)
        | ~ l1_pre_topc(X8)
        | ~ v1_funct_1(k3_tmap_1(sK0,X8,k1_tsep_1(sK0,sK1,sK2),sK1,X9))
        | ~ v1_funct_2(k3_tmap_1(sK0,X8,k1_tsep_1(sK0,sK1,sK2),sK1,X9),u1_struct_0(sK1),u1_struct_0(X8))
        | ~ v5_pre_topc(k3_tmap_1(sK0,X8,k1_tsep_1(sK0,sK1,sK2),sK1,X9),sK1,X8)
        | ~ m1_subset_1(k3_tmap_1(sK0,X8,k1_tsep_1(sK0,sK1,sK2),sK1,X9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X8))))
        | ~ v1_funct_1(k3_tmap_1(sK0,X8,k1_tsep_1(sK0,sK1,sK2),sK2,X9))
        | ~ v1_funct_2(k3_tmap_1(sK0,X8,k1_tsep_1(sK0,sK1,sK2),sK2,X9),u1_struct_0(sK2),u1_struct_0(X8))
        | ~ v5_pre_topc(k3_tmap_1(sK0,X8,k1_tsep_1(sK0,sK1,sK2),sK2,X9),sK2,X8)
        | ~ m1_subset_1(k3_tmap_1(sK0,X8,k1_tsep_1(sK0,sK1,sK2),sK2,X9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X8))))
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(sK1,sK0)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(X8))))
        | ~ v1_funct_2(X9,u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(X8))
        | ~ v1_funct_1(X9) )
    | ~ spl13_36 ),
    inference(duplicate_literal_removal,[],[f5016])).

fof(f5016,plain,
    ( ! [X8,X9] :
        ( v5_pre_topc(X9,k1_tsep_1(sK0,sK1,sK2),X8)
        | v2_struct_0(X8)
        | ~ v2_pre_topc(X8)
        | ~ l1_pre_topc(X8)
        | ~ v1_funct_1(k3_tmap_1(sK0,X8,k1_tsep_1(sK0,sK1,sK2),sK1,X9))
        | ~ v1_funct_2(k3_tmap_1(sK0,X8,k1_tsep_1(sK0,sK1,sK2),sK1,X9),u1_struct_0(sK1),u1_struct_0(X8))
        | ~ v5_pre_topc(k3_tmap_1(sK0,X8,k1_tsep_1(sK0,sK1,sK2),sK1,X9),sK1,X8)
        | ~ m1_subset_1(k3_tmap_1(sK0,X8,k1_tsep_1(sK0,sK1,sK2),sK1,X9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X8))))
        | ~ v1_funct_1(k3_tmap_1(sK0,X8,k1_tsep_1(sK0,sK1,sK2),sK2,X9))
        | ~ v1_funct_2(k3_tmap_1(sK0,X8,k1_tsep_1(sK0,sK1,sK2),sK2,X9),u1_struct_0(sK2),u1_struct_0(X8))
        | ~ v5_pre_topc(k3_tmap_1(sK0,X8,k1_tsep_1(sK0,sK1,sK2),sK2,X9),sK2,X8)
        | ~ m1_subset_1(k3_tmap_1(sK0,X8,k1_tsep_1(sK0,sK1,sK2),sK2,X9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X8))))
        | ~ v1_funct_1(k3_tmap_1(sK0,X8,k1_tsep_1(sK0,sK1,sK2),sK2,X9))
        | ~ m1_subset_1(k3_tmap_1(sK0,X8,k1_tsep_1(sK0,sK1,sK2),sK1,X9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X8))))
        | ~ v1_funct_2(k3_tmap_1(sK0,X8,k1_tsep_1(sK0,sK1,sK2),sK1,X9),u1_struct_0(sK1),u1_struct_0(X8))
        | ~ v1_funct_1(k3_tmap_1(sK0,X8,k1_tsep_1(sK0,sK1,sK2),sK1,X9))
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(sK1,sK0)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X8)
        | ~ v2_pre_topc(X8)
        | v2_struct_0(X8)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(k3_tmap_1(sK0,X8,k1_tsep_1(sK0,sK1,sK2),sK2,X9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X8))))
        | ~ v1_funct_2(k3_tmap_1(sK0,X8,k1_tsep_1(sK0,sK1,sK2),sK2,X9),u1_struct_0(sK2),u1_struct_0(X8))
        | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(X8))))
        | ~ v1_funct_2(X9,u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(X8))
        | ~ v1_funct_1(X9) )
    | ~ spl13_36 ),
    inference(superposition,[],[f352,f2635])).

fof(f2635,plain,(
    ! [X6,X4,X7,X5,X3] :
      ( k10_tmap_1(X3,X4,X5,X6,k3_tmap_1(X3,X4,k1_tsep_1(X3,X5,X6),X5,X7),k3_tmap_1(X3,X4,k1_tsep_1(X3,X5,X6),X6,X7)) = X7
      | ~ v1_funct_1(k3_tmap_1(X3,X4,k1_tsep_1(X3,X5,X6),X6,X7))
      | ~ m1_subset_1(k3_tmap_1(X3,X4,k1_tsep_1(X3,X5,X6),X5,X7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X4))))
      | ~ v1_funct_2(k3_tmap_1(X3,X4,k1_tsep_1(X3,X5,X6),X5,X7),u1_struct_0(X5),u1_struct_0(X4))
      | ~ v1_funct_1(k3_tmap_1(X3,X4,k1_tsep_1(X3,X5,X6),X5,X7))
      | ~ m1_pre_topc(X6,X3)
      | v2_struct_0(X6)
      | ~ m1_pre_topc(X5,X3)
      | v2_struct_0(X5)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4)
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | v2_struct_0(X3)
      | ~ m1_subset_1(k3_tmap_1(X3,X4,k1_tsep_1(X3,X5,X6),X6,X7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(X4))))
      | ~ v1_funct_2(k3_tmap_1(X3,X4,k1_tsep_1(X3,X5,X6),X6,X7),u1_struct_0(X6),u1_struct_0(X4))
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X5,X6)),u1_struct_0(X4))))
      | ~ v1_funct_2(X7,u1_struct_0(k1_tsep_1(X3,X5,X6)),u1_struct_0(X4))
      | ~ v1_funct_1(X7) ) ),
    inference(duplicate_literal_removal,[],[f2624])).

fof(f2624,plain,(
    ! [X6,X4,X7,X5,X3] :
      ( ~ v1_funct_2(k3_tmap_1(X3,X4,k1_tsep_1(X3,X5,X6),X6,X7),u1_struct_0(X6),u1_struct_0(X4))
      | ~ v1_funct_1(k3_tmap_1(X3,X4,k1_tsep_1(X3,X5,X6),X6,X7))
      | ~ m1_subset_1(k3_tmap_1(X3,X4,k1_tsep_1(X3,X5,X6),X5,X7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X4))))
      | ~ v1_funct_2(k3_tmap_1(X3,X4,k1_tsep_1(X3,X5,X6),X5,X7),u1_struct_0(X5),u1_struct_0(X4))
      | ~ v1_funct_1(k3_tmap_1(X3,X4,k1_tsep_1(X3,X5,X6),X5,X7))
      | ~ m1_pre_topc(X6,X3)
      | v2_struct_0(X6)
      | ~ m1_pre_topc(X5,X3)
      | v2_struct_0(X5)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4)
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | v2_struct_0(X3)
      | ~ m1_subset_1(k3_tmap_1(X3,X4,k1_tsep_1(X3,X5,X6),X6,X7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(X4))))
      | k10_tmap_1(X3,X4,X5,X6,k3_tmap_1(X3,X4,k1_tsep_1(X3,X5,X6),X5,X7),k3_tmap_1(X3,X4,k1_tsep_1(X3,X5,X6),X6,X7)) = X7
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X5,X6)),u1_struct_0(X4))))
      | ~ v1_funct_2(X7,u1_struct_0(k1_tsep_1(X3,X5,X6)),u1_struct_0(X4))
      | ~ v1_funct_1(X7)
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X5,X6)),u1_struct_0(X4))))
      | ~ v1_funct_2(X7,u1_struct_0(k1_tsep_1(X3,X5,X6)),u1_struct_0(X4))
      | ~ v1_funct_1(X7)
      | ~ m1_pre_topc(X6,X3)
      | v2_struct_0(X6)
      | ~ m1_pre_topc(X5,X3)
      | v2_struct_0(X5)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4)
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | v2_struct_0(X3) ) ),
    inference(resolution,[],[f1109,f184])).

fof(f184,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_funct_2(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r2_funct_2(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)))
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
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
                      ( r2_funct_2(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)))
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
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
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => r2_funct_2(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t150_tmap_1.p',t138_tmap_1)).

fof(f1109,plain,(
    ! [X30,X28,X26,X24,X29,X27,X25] :
      ( ~ r2_funct_2(u1_struct_0(k1_tsep_1(X29,X28,X25)),u1_struct_0(X26),X30,k10_tmap_1(X29,X26,X28,X25,X27,X24))
      | ~ v1_funct_2(X24,u1_struct_0(X25),u1_struct_0(X26))
      | ~ v1_funct_1(X24)
      | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X28),u1_struct_0(X26))))
      | ~ v1_funct_2(X27,u1_struct_0(X28),u1_struct_0(X26))
      | ~ v1_funct_1(X27)
      | ~ m1_pre_topc(X25,X29)
      | v2_struct_0(X25)
      | ~ m1_pre_topc(X28,X29)
      | v2_struct_0(X28)
      | ~ l1_pre_topc(X26)
      | ~ v2_pre_topc(X26)
      | v2_struct_0(X26)
      | ~ l1_pre_topc(X29)
      | ~ v2_pre_topc(X29)
      | v2_struct_0(X29)
      | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X25),u1_struct_0(X26))))
      | k10_tmap_1(X29,X26,X28,X25,X27,X24) = X30
      | ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X29,X28,X25)),u1_struct_0(X26))))
      | ~ v1_funct_2(X30,u1_struct_0(k1_tsep_1(X29,X28,X25)),u1_struct_0(X26))
      | ~ v1_funct_1(X30) ) ),
    inference(subsumption_resolution,[],[f1108,f158])).

fof(f158,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
        & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
        & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
        & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
        & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
        & v1_funct_1(X4)
        & m1_pre_topc(X3,X0)
        & ~ v2_struct_0(X3)
        & m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
        & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
        & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t150_tmap_1.p',dt_k10_tmap_1)).

fof(f1108,plain,(
    ! [X30,X28,X26,X24,X29,X27,X25] :
      ( ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X25),u1_struct_0(X26))))
      | ~ v1_funct_2(X24,u1_struct_0(X25),u1_struct_0(X26))
      | ~ v1_funct_1(X24)
      | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X28),u1_struct_0(X26))))
      | ~ v1_funct_2(X27,u1_struct_0(X28),u1_struct_0(X26))
      | ~ v1_funct_1(X27)
      | ~ m1_pre_topc(X25,X29)
      | v2_struct_0(X25)
      | ~ m1_pre_topc(X28,X29)
      | v2_struct_0(X28)
      | ~ l1_pre_topc(X26)
      | ~ v2_pre_topc(X26)
      | v2_struct_0(X26)
      | ~ l1_pre_topc(X29)
      | ~ v2_pre_topc(X29)
      | v2_struct_0(X29)
      | ~ r2_funct_2(u1_struct_0(k1_tsep_1(X29,X28,X25)),u1_struct_0(X26),X30,k10_tmap_1(X29,X26,X28,X25,X27,X24))
      | k10_tmap_1(X29,X26,X28,X25,X27,X24) = X30
      | ~ v1_funct_2(k10_tmap_1(X29,X26,X28,X25,X27,X24),u1_struct_0(k1_tsep_1(X29,X28,X25)),u1_struct_0(X26))
      | ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X29,X28,X25)),u1_struct_0(X26))))
      | ~ v1_funct_2(X30,u1_struct_0(k1_tsep_1(X29,X28,X25)),u1_struct_0(X26))
      | ~ v1_funct_1(X30) ) ),
    inference(subsumption_resolution,[],[f1090,f157])).

fof(f157,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f1090,plain,(
    ! [X30,X28,X26,X24,X29,X27,X25] :
      ( ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X25),u1_struct_0(X26))))
      | ~ v1_funct_2(X24,u1_struct_0(X25),u1_struct_0(X26))
      | ~ v1_funct_1(X24)
      | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X28),u1_struct_0(X26))))
      | ~ v1_funct_2(X27,u1_struct_0(X28),u1_struct_0(X26))
      | ~ v1_funct_1(X27)
      | ~ m1_pre_topc(X25,X29)
      | v2_struct_0(X25)
      | ~ m1_pre_topc(X28,X29)
      | v2_struct_0(X28)
      | ~ l1_pre_topc(X26)
      | ~ v2_pre_topc(X26)
      | v2_struct_0(X26)
      | ~ l1_pre_topc(X29)
      | ~ v2_pre_topc(X29)
      | v2_struct_0(X29)
      | ~ r2_funct_2(u1_struct_0(k1_tsep_1(X29,X28,X25)),u1_struct_0(X26),X30,k10_tmap_1(X29,X26,X28,X25,X27,X24))
      | k10_tmap_1(X29,X26,X28,X25,X27,X24) = X30
      | ~ v1_funct_2(k10_tmap_1(X29,X26,X28,X25,X27,X24),u1_struct_0(k1_tsep_1(X29,X28,X25)),u1_struct_0(X26))
      | ~ v1_funct_1(k10_tmap_1(X29,X26,X28,X25,X27,X24))
      | ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X29,X28,X25)),u1_struct_0(X26))))
      | ~ v1_funct_2(X30,u1_struct_0(k1_tsep_1(X29,X28,X25)),u1_struct_0(X26))
      | ~ v1_funct_1(X30) ) ),
    inference(resolution,[],[f159,f189])).

fof(f189,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_funct_2(X0,X1,X2,X3)
      | X2 = X3
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f120])).

fof(f120,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_funct_2(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_funct_2(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(nnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f64])).

fof(f64,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t150_tmap_1.p',redefinition_r2_funct_2)).

fof(f159,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f352,plain,
    ( ! [X6,X8,X7] :
        ( v5_pre_topc(k10_tmap_1(sK0,X6,sK1,sK2,X7,X8),k1_tsep_1(sK0,sK1,sK2),X6)
        | v2_struct_0(X6)
        | ~ v2_pre_topc(X6)
        | ~ l1_pre_topc(X6)
        | ~ v1_funct_1(X7)
        | ~ v1_funct_2(X7,u1_struct_0(sK1),u1_struct_0(X6))
        | ~ v5_pre_topc(X7,sK1,X6)
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X6))))
        | ~ v1_funct_1(X8)
        | ~ v1_funct_2(X8,u1_struct_0(sK2),u1_struct_0(X6))
        | ~ v5_pre_topc(X8,sK2,X6)
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X6)))) )
    | ~ spl13_36 ),
    inference(avatar_component_clause,[],[f351])).

fof(f6889,plain,
    ( spl13_11
    | ~ spl13_12
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_24
    | ~ spl13_26
    | ~ spl13_28
    | ~ spl13_30
    | spl13_33
    | ~ spl13_42
    | spl13_45
    | ~ spl13_46
    | spl13_49
    | ~ spl13_50
    | ~ spl13_52
    | spl13_55 ),
    inference(avatar_contradiction_clause,[],[f6888])).

fof(f6888,plain,
    ( $false
    | ~ spl13_11
    | ~ spl13_12
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_24
    | ~ spl13_26
    | ~ spl13_28
    | ~ spl13_30
    | ~ spl13_33
    | ~ spl13_42
    | ~ spl13_45
    | ~ spl13_46
    | ~ spl13_49
    | ~ spl13_50
    | ~ spl13_52
    | ~ spl13_55 ),
    inference(subsumption_resolution,[],[f6887,f410])).

fof(f6887,plain,
    ( v2_struct_0(sK0)
    | ~ spl13_11
    | ~ spl13_12
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_24
    | ~ spl13_26
    | ~ spl13_28
    | ~ spl13_30
    | ~ spl13_33
    | ~ spl13_42
    | ~ spl13_45
    | ~ spl13_46
    | ~ spl13_49
    | ~ spl13_50
    | ~ spl13_52 ),
    inference(subsumption_resolution,[],[f6886,f403])).

fof(f6886,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_11
    | ~ spl13_12
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_24
    | ~ spl13_26
    | ~ spl13_28
    | ~ spl13_30
    | ~ spl13_33
    | ~ spl13_42
    | ~ spl13_45
    | ~ spl13_46
    | ~ spl13_49
    | ~ spl13_50 ),
    inference(subsumption_resolution,[],[f6885,f396])).

fof(f6885,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_11
    | ~ spl13_12
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_24
    | ~ spl13_26
    | ~ spl13_28
    | ~ spl13_30
    | ~ spl13_33
    | ~ spl13_42
    | ~ spl13_45
    | ~ spl13_46
    | ~ spl13_49 ),
    inference(subsumption_resolution,[],[f6884,f344])).

fof(f344,plain,
    ( ~ v2_struct_0(sK3)
    | ~ spl13_33 ),
    inference(avatar_component_clause,[],[f343])).

fof(f343,plain,
    ( spl13_33
  <=> ~ v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_33])])).

fof(f6884,plain,
    ( v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_11
    | ~ spl13_12
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_24
    | ~ spl13_26
    | ~ spl13_28
    | ~ spl13_30
    | ~ spl13_42
    | ~ spl13_45
    | ~ spl13_46
    | ~ spl13_49 ),
    inference(subsumption_resolution,[],[f6883,f337])).

fof(f337,plain,
    ( v2_pre_topc(sK3)
    | ~ spl13_30 ),
    inference(avatar_component_clause,[],[f336])).

fof(f336,plain,
    ( spl13_30
  <=> v2_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_30])])).

fof(f6883,plain,
    ( ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_11
    | ~ spl13_12
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_24
    | ~ spl13_26
    | ~ spl13_28
    | ~ spl13_42
    | ~ spl13_45
    | ~ spl13_46
    | ~ spl13_49 ),
    inference(subsumption_resolution,[],[f6882,f330])).

fof(f330,plain,
    ( l1_pre_topc(sK3)
    | ~ spl13_28 ),
    inference(avatar_component_clause,[],[f329])).

fof(f329,plain,
    ( spl13_28
  <=> l1_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_28])])).

fof(f6882,plain,
    ( ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_11
    | ~ spl13_12
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_24
    | ~ spl13_26
    | ~ spl13_42
    | ~ spl13_45
    | ~ spl13_46
    | ~ spl13_49 ),
    inference(subsumption_resolution,[],[f6881,f389])).

fof(f6881,plain,
    ( v2_struct_0(sK1)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_11
    | ~ spl13_12
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_24
    | ~ spl13_26
    | ~ spl13_42
    | ~ spl13_45
    | ~ spl13_46 ),
    inference(subsumption_resolution,[],[f6880,f382])).

fof(f6880,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_11
    | ~ spl13_12
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_24
    | ~ spl13_26
    | ~ spl13_42
    | ~ spl13_45 ),
    inference(subsumption_resolution,[],[f6879,f375])).

fof(f6879,plain,
    ( v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_11
    | ~ spl13_12
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_24
    | ~ spl13_26
    | ~ spl13_42 ),
    inference(subsumption_resolution,[],[f6878,f368])).

fof(f6878,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_11
    | ~ spl13_12
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_24
    | ~ spl13_26 ),
    inference(subsumption_resolution,[],[f6877,f323])).

fof(f323,plain,
    ( v1_funct_1(sK4)
    | ~ spl13_26 ),
    inference(avatar_component_clause,[],[f322])).

fof(f322,plain,
    ( spl13_26
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_26])])).

fof(f6877,plain,
    ( ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_11
    | ~ spl13_12
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_24 ),
    inference(subsumption_resolution,[],[f6876,f316])).

fof(f316,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK3))
    | ~ spl13_24 ),
    inference(avatar_component_clause,[],[f315])).

fof(f315,plain,
    ( spl13_24
  <=> v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_24])])).

fof(f6876,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_11
    | ~ spl13_12
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20 ),
    inference(subsumption_resolution,[],[f6875,f302])).

fof(f302,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK3))))
    | ~ spl13_20 ),
    inference(avatar_component_clause,[],[f301])).

fof(f301,plain,
    ( spl13_20
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_20])])).

fof(f6875,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_11
    | ~ spl13_12
    | ~ spl13_16
    | ~ spl13_18 ),
    inference(subsumption_resolution,[],[f6874,f295])).

fof(f295,plain,
    ( v1_funct_1(sK5)
    | ~ spl13_18 ),
    inference(avatar_component_clause,[],[f294])).

fof(f294,plain,
    ( spl13_18
  <=> v1_funct_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_18])])).

fof(f6874,plain,
    ( ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_11
    | ~ spl13_12
    | ~ spl13_16 ),
    inference(subsumption_resolution,[],[f6873,f288])).

fof(f288,plain,
    ( v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ spl13_16 ),
    inference(avatar_component_clause,[],[f287])).

fof(f287,plain,
    ( spl13_16
  <=> v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_16])])).

fof(f6873,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_11
    | ~ spl13_12 ),
    inference(subsumption_resolution,[],[f6871,f274])).

fof(f274,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ spl13_12 ),
    inference(avatar_component_clause,[],[f273])).

fof(f273,plain,
    ( spl13_12
  <=> m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_12])])).

fof(f6871,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_11 ),
    inference(resolution,[],[f267,f159])).

fof(f267,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK0,sK3,sK1,sK2,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK3))))
    | ~ spl13_11 ),
    inference(avatar_component_clause,[],[f266])).

fof(f266,plain,
    ( spl13_11
  <=> ~ m1_subset_1(k10_tmap_1(sK0,sK3,sK1,sK2,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_11])])).

fof(f6858,plain,
    ( spl13_7
    | ~ spl13_12
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_24
    | ~ spl13_26
    | ~ spl13_28
    | ~ spl13_30
    | spl13_33
    | ~ spl13_42
    | spl13_45
    | ~ spl13_46
    | spl13_49
    | ~ spl13_50
    | ~ spl13_52
    | spl13_55 ),
    inference(avatar_contradiction_clause,[],[f6857])).

fof(f6857,plain,
    ( $false
    | ~ spl13_7
    | ~ spl13_12
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_24
    | ~ spl13_26
    | ~ spl13_28
    | ~ spl13_30
    | ~ spl13_33
    | ~ spl13_42
    | ~ spl13_45
    | ~ spl13_46
    | ~ spl13_49
    | ~ spl13_50
    | ~ spl13_52
    | ~ spl13_55 ),
    inference(subsumption_resolution,[],[f6856,f410])).

fof(f6856,plain,
    ( v2_struct_0(sK0)
    | ~ spl13_7
    | ~ spl13_12
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_24
    | ~ spl13_26
    | ~ spl13_28
    | ~ spl13_30
    | ~ spl13_33
    | ~ spl13_42
    | ~ spl13_45
    | ~ spl13_46
    | ~ spl13_49
    | ~ spl13_50
    | ~ spl13_52 ),
    inference(subsumption_resolution,[],[f6855,f403])).

fof(f6855,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_7
    | ~ spl13_12
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_24
    | ~ spl13_26
    | ~ spl13_28
    | ~ spl13_30
    | ~ spl13_33
    | ~ spl13_42
    | ~ spl13_45
    | ~ spl13_46
    | ~ spl13_49
    | ~ spl13_50 ),
    inference(subsumption_resolution,[],[f6854,f396])).

fof(f6854,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_7
    | ~ spl13_12
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_24
    | ~ spl13_26
    | ~ spl13_28
    | ~ spl13_30
    | ~ spl13_33
    | ~ spl13_42
    | ~ spl13_45
    | ~ spl13_46
    | ~ spl13_49 ),
    inference(subsumption_resolution,[],[f6853,f344])).

fof(f6853,plain,
    ( v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_7
    | ~ spl13_12
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_24
    | ~ spl13_26
    | ~ spl13_28
    | ~ spl13_30
    | ~ spl13_42
    | ~ spl13_45
    | ~ spl13_46
    | ~ spl13_49 ),
    inference(subsumption_resolution,[],[f6852,f337])).

fof(f6852,plain,
    ( ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_7
    | ~ spl13_12
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_24
    | ~ spl13_26
    | ~ spl13_28
    | ~ spl13_42
    | ~ spl13_45
    | ~ spl13_46
    | ~ spl13_49 ),
    inference(subsumption_resolution,[],[f6851,f330])).

fof(f6851,plain,
    ( ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_7
    | ~ spl13_12
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_24
    | ~ spl13_26
    | ~ spl13_42
    | ~ spl13_45
    | ~ spl13_46
    | ~ spl13_49 ),
    inference(subsumption_resolution,[],[f6850,f389])).

fof(f6850,plain,
    ( v2_struct_0(sK1)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_7
    | ~ spl13_12
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_24
    | ~ spl13_26
    | ~ spl13_42
    | ~ spl13_45
    | ~ spl13_46 ),
    inference(subsumption_resolution,[],[f6849,f382])).

fof(f6849,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_7
    | ~ spl13_12
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_24
    | ~ spl13_26
    | ~ spl13_42
    | ~ spl13_45 ),
    inference(subsumption_resolution,[],[f6848,f375])).

fof(f6848,plain,
    ( v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_7
    | ~ spl13_12
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_24
    | ~ spl13_26
    | ~ spl13_42 ),
    inference(subsumption_resolution,[],[f6847,f368])).

fof(f6847,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_7
    | ~ spl13_12
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_24
    | ~ spl13_26 ),
    inference(subsumption_resolution,[],[f6846,f323])).

fof(f6846,plain,
    ( ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_7
    | ~ spl13_12
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_24 ),
    inference(subsumption_resolution,[],[f6845,f316])).

fof(f6845,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_7
    | ~ spl13_12
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20 ),
    inference(subsumption_resolution,[],[f6844,f302])).

fof(f6844,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_7
    | ~ spl13_12
    | ~ spl13_16
    | ~ spl13_18 ),
    inference(subsumption_resolution,[],[f6843,f295])).

fof(f6843,plain,
    ( ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_7
    | ~ spl13_12
    | ~ spl13_16 ),
    inference(subsumption_resolution,[],[f6842,f288])).

fof(f6842,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_7
    | ~ spl13_12 ),
    inference(subsumption_resolution,[],[f6840,f274])).

fof(f6840,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_7 ),
    inference(resolution,[],[f255,f158])).

fof(f255,plain,
    ( ~ v1_funct_2(k10_tmap_1(sK0,sK3,sK1,sK2,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK3))
    | ~ spl13_7 ),
    inference(avatar_component_clause,[],[f254])).

fof(f254,plain,
    ( spl13_7
  <=> ~ v1_funct_2(k10_tmap_1(sK0,sK3,sK1,sK2,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_7])])).

fof(f6834,plain,
    ( spl13_92
    | ~ spl13_0
    | ~ spl13_42
    | spl13_45
    | ~ spl13_46
    | spl13_49
    | ~ spl13_50
    | ~ spl13_52
    | spl13_55 ),
    inference(avatar_split_clause,[],[f6833,f409,f402,f395,f388,f381,f374,f367,f233,f885])).

fof(f885,plain,
    ( spl13_92
  <=> r4_tsep_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_92])])).

fof(f233,plain,
    ( spl13_0
  <=> r3_tsep_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_0])])).

fof(f6833,plain,
    ( r4_tsep_1(sK0,sK1,sK2)
    | ~ spl13_0
    | ~ spl13_42
    | ~ spl13_45
    | ~ spl13_46
    | ~ spl13_49
    | ~ spl13_50
    | ~ spl13_52
    | ~ spl13_55 ),
    inference(subsumption_resolution,[],[f6832,f410])).

fof(f6832,plain,
    ( r4_tsep_1(sK0,sK1,sK2)
    | v2_struct_0(sK0)
    | ~ spl13_0
    | ~ spl13_42
    | ~ spl13_45
    | ~ spl13_46
    | ~ spl13_49
    | ~ spl13_50
    | ~ spl13_52 ),
    inference(subsumption_resolution,[],[f6831,f403])).

fof(f6831,plain,
    ( r4_tsep_1(sK0,sK1,sK2)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_0
    | ~ spl13_42
    | ~ spl13_45
    | ~ spl13_46
    | ~ spl13_49
    | ~ spl13_50 ),
    inference(subsumption_resolution,[],[f6830,f396])).

fof(f6830,plain,
    ( r4_tsep_1(sK0,sK1,sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_0
    | ~ spl13_42
    | ~ spl13_45
    | ~ spl13_46
    | ~ spl13_49 ),
    inference(subsumption_resolution,[],[f6829,f389])).

fof(f6829,plain,
    ( r4_tsep_1(sK0,sK1,sK2)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_0
    | ~ spl13_42
    | ~ spl13_45
    | ~ spl13_46 ),
    inference(subsumption_resolution,[],[f6828,f382])).

fof(f6828,plain,
    ( r4_tsep_1(sK0,sK1,sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_0
    | ~ spl13_42
    | ~ spl13_45 ),
    inference(subsumption_resolution,[],[f6827,f375])).

fof(f6827,plain,
    ( r4_tsep_1(sK0,sK1,sK2)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_0
    | ~ spl13_42 ),
    inference(subsumption_resolution,[],[f6824,f368])).

fof(f6824,plain,
    ( r4_tsep_1(sK0,sK1,sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_0 ),
    inference(resolution,[],[f234,f210])).

fof(f210,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_tsep_1(X0,X1,X2)
      | r4_tsep_1(X0,X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f126])).

fof(f126,plain,(
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
    inference(flattening,[],[f125])).

fof(f125,plain,(
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
    inference(nnf_transformation,[],[f86])).

fof(f86,plain,(
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
    inference(flattening,[],[f85])).

fof(f85,plain,(
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
    inference(ennf_transformation,[],[f43])).

fof(f43,axiom,(
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
    file('/export/starexec/sandbox/benchmark/tmap_1__t150_tmap_1.p',t85_tsep_1)).

fof(f234,plain,
    ( r3_tsep_1(sK0,sK1,sK2)
    | ~ spl13_0 ),
    inference(avatar_component_clause,[],[f233])).

fof(f4421,plain,
    ( ~ spl13_42
    | spl13_45
    | ~ spl13_46
    | spl13_49
    | ~ spl13_50
    | ~ spl13_52
    | spl13_55
    | ~ spl13_82
    | spl13_85
    | ~ spl13_278 ),
    inference(avatar_contradiction_clause,[],[f4420])).

fof(f4420,plain,
    ( $false
    | ~ spl13_42
    | ~ spl13_45
    | ~ spl13_46
    | ~ spl13_49
    | ~ spl13_50
    | ~ spl13_52
    | ~ spl13_55
    | ~ spl13_82
    | ~ spl13_85
    | ~ spl13_278 ),
    inference(subsumption_resolution,[],[f4419,f410])).

fof(f4419,plain,
    ( v2_struct_0(sK0)
    | ~ spl13_42
    | ~ spl13_45
    | ~ spl13_46
    | ~ spl13_49
    | ~ spl13_50
    | ~ spl13_52
    | ~ spl13_82
    | ~ spl13_85
    | ~ spl13_278 ),
    inference(subsumption_resolution,[],[f4418,f403])).

fof(f4418,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_42
    | ~ spl13_45
    | ~ spl13_46
    | ~ spl13_49
    | ~ spl13_50
    | ~ spl13_82
    | ~ spl13_85
    | ~ spl13_278 ),
    inference(subsumption_resolution,[],[f4417,f396])).

fof(f4417,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_42
    | ~ spl13_45
    | ~ spl13_46
    | ~ spl13_49
    | ~ spl13_82
    | ~ spl13_85
    | ~ spl13_278 ),
    inference(subsumption_resolution,[],[f4416,f375])).

fof(f4416,plain,
    ( v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_42
    | ~ spl13_46
    | ~ spl13_49
    | ~ spl13_82
    | ~ spl13_85
    | ~ spl13_278 ),
    inference(subsumption_resolution,[],[f4415,f368])).

fof(f4415,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_46
    | ~ spl13_49
    | ~ spl13_82
    | ~ spl13_85
    | ~ spl13_278 ),
    inference(subsumption_resolution,[],[f4414,f389])).

fof(f4414,plain,
    ( v2_struct_0(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_46
    | ~ spl13_82
    | ~ spl13_85
    | ~ spl13_278 ),
    inference(subsumption_resolution,[],[f4413,f382])).

fof(f4413,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_82
    | ~ spl13_85
    | ~ spl13_278 ),
    inference(subsumption_resolution,[],[f4412,f541])).

fof(f4412,plain,
    ( ~ r1_tsep_1(sK2,sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_85
    | ~ spl13_278 ),
    inference(subsumption_resolution,[],[f4410,f566])).

fof(f4410,plain,
    ( r3_tsep_1(sK0,sK2,sK1)
    | ~ r1_tsep_1(sK2,sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_278 ),
    inference(resolution,[],[f3851,f169])).

fof(f169,plain,(
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
    inference(cnf_transformation,[],[f119])).

fof(f3851,plain,
    ( v2_struct_0(sK6(sK0,sK2,sK1))
    | ~ spl13_278 ),
    inference(avatar_component_clause,[],[f3850])).

fof(f3850,plain,
    ( spl13_278
  <=> v2_struct_0(sK6(sK0,sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_278])])).

fof(f4335,plain,
    ( ~ spl13_42
    | spl13_45
    | ~ spl13_46
    | spl13_49
    | ~ spl13_50
    | ~ spl13_52
    | spl13_55
    | ~ spl13_82
    | spl13_85
    | spl13_285 ),
    inference(avatar_contradiction_clause,[],[f4334])).

fof(f4334,plain,
    ( $false
    | ~ spl13_42
    | ~ spl13_45
    | ~ spl13_46
    | ~ spl13_49
    | ~ spl13_50
    | ~ spl13_52
    | ~ spl13_55
    | ~ spl13_82
    | ~ spl13_85
    | ~ spl13_285 ),
    inference(subsumption_resolution,[],[f4333,f410])).

fof(f4333,plain,
    ( v2_struct_0(sK0)
    | ~ spl13_42
    | ~ spl13_45
    | ~ spl13_46
    | ~ spl13_49
    | ~ spl13_50
    | ~ spl13_52
    | ~ spl13_82
    | ~ spl13_85
    | ~ spl13_285 ),
    inference(subsumption_resolution,[],[f4332,f403])).

fof(f4332,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_42
    | ~ spl13_45
    | ~ spl13_46
    | ~ spl13_49
    | ~ spl13_50
    | ~ spl13_82
    | ~ spl13_85
    | ~ spl13_285 ),
    inference(subsumption_resolution,[],[f4331,f396])).

fof(f4331,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_42
    | ~ spl13_45
    | ~ spl13_46
    | ~ spl13_49
    | ~ spl13_82
    | ~ spl13_85
    | ~ spl13_285 ),
    inference(subsumption_resolution,[],[f4330,f375])).

fof(f4330,plain,
    ( v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_42
    | ~ spl13_46
    | ~ spl13_49
    | ~ spl13_82
    | ~ spl13_85
    | ~ spl13_285 ),
    inference(subsumption_resolution,[],[f4329,f368])).

fof(f4329,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_46
    | ~ spl13_49
    | ~ spl13_82
    | ~ spl13_85
    | ~ spl13_285 ),
    inference(subsumption_resolution,[],[f4328,f389])).

fof(f4328,plain,
    ( v2_struct_0(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_46
    | ~ spl13_82
    | ~ spl13_85
    | ~ spl13_285 ),
    inference(subsumption_resolution,[],[f4327,f382])).

fof(f4327,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_82
    | ~ spl13_85
    | ~ spl13_285 ),
    inference(subsumption_resolution,[],[f4326,f541])).

fof(f4326,plain,
    ( ~ r1_tsep_1(sK2,sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_85
    | ~ spl13_285 ),
    inference(subsumption_resolution,[],[f4324,f566])).

fof(f4324,plain,
    ( r3_tsep_1(sK0,sK2,sK1)
    | ~ r1_tsep_1(sK2,sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_285 ),
    inference(resolution,[],[f3869,f672])).

fof(f672,plain,(
    ! [X4,X5,X3] :
      ( m1_subset_1(sK7(X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X5,X4)),u1_struct_0(sK6(X3,X4,X5)))))
      | r3_tsep_1(X3,X4,X5)
      | ~ r1_tsep_1(X4,X5)
      | ~ m1_pre_topc(X5,X3)
      | v2_struct_0(X5)
      | ~ m1_pre_topc(X4,X3)
      | v2_struct_0(X4)
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | v2_struct_0(X3) ) ),
    inference(duplicate_literal_removal,[],[f671])).

fof(f671,plain,(
    ! [X4,X5,X3] :
      ( m1_subset_1(sK7(X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X5,X4)),u1_struct_0(sK6(X3,X4,X5)))))
      | r3_tsep_1(X3,X4,X5)
      | ~ r1_tsep_1(X4,X5)
      | ~ m1_pre_topc(X5,X3)
      | v2_struct_0(X5)
      | ~ m1_pre_topc(X4,X3)
      | v2_struct_0(X4)
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X5,X3)
      | v2_struct_0(X5)
      | ~ m1_pre_topc(X4,X3)
      | v2_struct_0(X4)
      | ~ l1_pre_topc(X3)
      | v2_struct_0(X3) ) ),
    inference(superposition,[],[f174,f163])).

fof(f3869,plain,
    ( ~ m1_subset_1(sK7(sK0,sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK6(sK0,sK2,sK1)))))
    | ~ spl13_285 ),
    inference(avatar_component_clause,[],[f3868])).

fof(f3868,plain,
    ( spl13_285
  <=> ~ m1_subset_1(sK7(sK0,sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK6(sK0,sK2,sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_285])])).

fof(f4267,plain,
    ( ~ spl13_42
    | spl13_45
    | ~ spl13_46
    | spl13_49
    | ~ spl13_50
    | ~ spl13_52
    | spl13_55
    | ~ spl13_82
    | spl13_85
    | spl13_283 ),
    inference(avatar_contradiction_clause,[],[f4266])).

fof(f4266,plain,
    ( $false
    | ~ spl13_42
    | ~ spl13_45
    | ~ spl13_46
    | ~ spl13_49
    | ~ spl13_50
    | ~ spl13_52
    | ~ spl13_55
    | ~ spl13_82
    | ~ spl13_85
    | ~ spl13_283 ),
    inference(subsumption_resolution,[],[f4265,f410])).

fof(f4265,plain,
    ( v2_struct_0(sK0)
    | ~ spl13_42
    | ~ spl13_45
    | ~ spl13_46
    | ~ spl13_49
    | ~ spl13_50
    | ~ spl13_52
    | ~ spl13_82
    | ~ spl13_85
    | ~ spl13_283 ),
    inference(subsumption_resolution,[],[f4264,f403])).

fof(f4264,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_42
    | ~ spl13_45
    | ~ spl13_46
    | ~ spl13_49
    | ~ spl13_50
    | ~ spl13_82
    | ~ spl13_85
    | ~ spl13_283 ),
    inference(subsumption_resolution,[],[f4263,f396])).

fof(f4263,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_42
    | ~ spl13_45
    | ~ spl13_46
    | ~ spl13_49
    | ~ spl13_82
    | ~ spl13_85
    | ~ spl13_283 ),
    inference(subsumption_resolution,[],[f4262,f375])).

fof(f4262,plain,
    ( v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_42
    | ~ spl13_46
    | ~ spl13_49
    | ~ spl13_82
    | ~ spl13_85
    | ~ spl13_283 ),
    inference(subsumption_resolution,[],[f4261,f368])).

fof(f4261,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_46
    | ~ spl13_49
    | ~ spl13_82
    | ~ spl13_85
    | ~ spl13_283 ),
    inference(subsumption_resolution,[],[f4260,f389])).

fof(f4260,plain,
    ( v2_struct_0(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_46
    | ~ spl13_82
    | ~ spl13_85
    | ~ spl13_283 ),
    inference(subsumption_resolution,[],[f4259,f382])).

fof(f4259,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_82
    | ~ spl13_85
    | ~ spl13_283 ),
    inference(subsumption_resolution,[],[f4258,f541])).

fof(f4258,plain,
    ( ~ r1_tsep_1(sK2,sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_85
    | ~ spl13_283 ),
    inference(subsumption_resolution,[],[f4256,f566])).

fof(f4256,plain,
    ( r3_tsep_1(sK0,sK2,sK1)
    | ~ r1_tsep_1(sK2,sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_283 ),
    inference(resolution,[],[f3863,f647])).

fof(f647,plain,(
    ! [X4,X5,X3] :
      ( v1_funct_2(sK7(X3,X4,X5),u1_struct_0(k1_tsep_1(X3,X5,X4)),u1_struct_0(sK6(X3,X4,X5)))
      | r3_tsep_1(X3,X4,X5)
      | ~ r1_tsep_1(X4,X5)
      | ~ m1_pre_topc(X5,X3)
      | v2_struct_0(X5)
      | ~ m1_pre_topc(X4,X3)
      | v2_struct_0(X4)
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | v2_struct_0(X3) ) ),
    inference(duplicate_literal_removal,[],[f646])).

fof(f646,plain,(
    ! [X4,X5,X3] :
      ( v1_funct_2(sK7(X3,X4,X5),u1_struct_0(k1_tsep_1(X3,X5,X4)),u1_struct_0(sK6(X3,X4,X5)))
      | r3_tsep_1(X3,X4,X5)
      | ~ r1_tsep_1(X4,X5)
      | ~ m1_pre_topc(X5,X3)
      | v2_struct_0(X5)
      | ~ m1_pre_topc(X4,X3)
      | v2_struct_0(X4)
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X5,X3)
      | v2_struct_0(X5)
      | ~ m1_pre_topc(X4,X3)
      | v2_struct_0(X4)
      | ~ l1_pre_topc(X3)
      | v2_struct_0(X3) ) ),
    inference(superposition,[],[f173,f163])).

fof(f3863,plain,
    ( ~ v1_funct_2(sK7(sK0,sK2,sK1),u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK6(sK0,sK2,sK1)))
    | ~ spl13_283 ),
    inference(avatar_component_clause,[],[f3862])).

fof(f3862,plain,
    ( spl13_283
  <=> ~ v1_funct_2(sK7(sK0,sK2,sK1),u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK6(sK0,sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_283])])).

fof(f4233,plain,
    ( ~ spl13_42
    | spl13_45
    | ~ spl13_46
    | spl13_49
    | ~ spl13_50
    | ~ spl13_52
    | spl13_55
    | ~ spl13_82
    | spl13_85
    | spl13_281 ),
    inference(avatar_contradiction_clause,[],[f4232])).

fof(f4232,plain,
    ( $false
    | ~ spl13_42
    | ~ spl13_45
    | ~ spl13_46
    | ~ spl13_49
    | ~ spl13_50
    | ~ spl13_52
    | ~ spl13_55
    | ~ spl13_82
    | ~ spl13_85
    | ~ spl13_281 ),
    inference(subsumption_resolution,[],[f4231,f410])).

fof(f4231,plain,
    ( v2_struct_0(sK0)
    | ~ spl13_42
    | ~ spl13_45
    | ~ spl13_46
    | ~ spl13_49
    | ~ spl13_50
    | ~ spl13_52
    | ~ spl13_82
    | ~ spl13_85
    | ~ spl13_281 ),
    inference(subsumption_resolution,[],[f4230,f403])).

fof(f4230,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_42
    | ~ spl13_45
    | ~ spl13_46
    | ~ spl13_49
    | ~ spl13_50
    | ~ spl13_82
    | ~ spl13_85
    | ~ spl13_281 ),
    inference(subsumption_resolution,[],[f4229,f396])).

fof(f4229,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_42
    | ~ spl13_45
    | ~ spl13_46
    | ~ spl13_49
    | ~ spl13_82
    | ~ spl13_85
    | ~ spl13_281 ),
    inference(subsumption_resolution,[],[f4228,f375])).

fof(f4228,plain,
    ( v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_42
    | ~ spl13_46
    | ~ spl13_49
    | ~ spl13_82
    | ~ spl13_85
    | ~ spl13_281 ),
    inference(subsumption_resolution,[],[f4227,f368])).

fof(f4227,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_46
    | ~ spl13_49
    | ~ spl13_82
    | ~ spl13_85
    | ~ spl13_281 ),
    inference(subsumption_resolution,[],[f4226,f389])).

fof(f4226,plain,
    ( v2_struct_0(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_46
    | ~ spl13_82
    | ~ spl13_85
    | ~ spl13_281 ),
    inference(subsumption_resolution,[],[f4225,f382])).

fof(f4225,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_82
    | ~ spl13_85
    | ~ spl13_281 ),
    inference(subsumption_resolution,[],[f4224,f541])).

fof(f4224,plain,
    ( ~ r1_tsep_1(sK2,sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_85
    | ~ spl13_281 ),
    inference(subsumption_resolution,[],[f4222,f566])).

fof(f4222,plain,
    ( r3_tsep_1(sK0,sK2,sK1)
    | ~ r1_tsep_1(sK2,sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_281 ),
    inference(resolution,[],[f3857,f172])).

fof(f3857,plain,
    ( ~ v1_funct_1(sK7(sK0,sK2,sK1))
    | ~ spl13_281 ),
    inference(avatar_component_clause,[],[f3856])).

fof(f3856,plain,
    ( spl13_281
  <=> ~ v1_funct_1(sK7(sK0,sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_281])])).

fof(f4186,plain,
    ( ~ spl13_42
    | spl13_45
    | ~ spl13_46
    | spl13_49
    | ~ spl13_50
    | ~ spl13_52
    | spl13_55
    | ~ spl13_82
    | spl13_85
    | spl13_277 ),
    inference(avatar_contradiction_clause,[],[f4185])).

fof(f4185,plain,
    ( $false
    | ~ spl13_42
    | ~ spl13_45
    | ~ spl13_46
    | ~ spl13_49
    | ~ spl13_50
    | ~ spl13_52
    | ~ spl13_55
    | ~ spl13_82
    | ~ spl13_85
    | ~ spl13_277 ),
    inference(subsumption_resolution,[],[f4184,f410])).

fof(f4184,plain,
    ( v2_struct_0(sK0)
    | ~ spl13_42
    | ~ spl13_45
    | ~ spl13_46
    | ~ spl13_49
    | ~ spl13_50
    | ~ spl13_52
    | ~ spl13_82
    | ~ spl13_85
    | ~ spl13_277 ),
    inference(subsumption_resolution,[],[f4183,f403])).

fof(f4183,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_42
    | ~ spl13_45
    | ~ spl13_46
    | ~ spl13_49
    | ~ spl13_50
    | ~ spl13_82
    | ~ spl13_85
    | ~ spl13_277 ),
    inference(subsumption_resolution,[],[f4182,f396])).

fof(f4182,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_42
    | ~ spl13_45
    | ~ spl13_46
    | ~ spl13_49
    | ~ spl13_82
    | ~ spl13_85
    | ~ spl13_277 ),
    inference(subsumption_resolution,[],[f4181,f375])).

fof(f4181,plain,
    ( v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_42
    | ~ spl13_46
    | ~ spl13_49
    | ~ spl13_82
    | ~ spl13_85
    | ~ spl13_277 ),
    inference(subsumption_resolution,[],[f4180,f368])).

fof(f4180,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_46
    | ~ spl13_49
    | ~ spl13_82
    | ~ spl13_85
    | ~ spl13_277 ),
    inference(subsumption_resolution,[],[f4179,f389])).

fof(f4179,plain,
    ( v2_struct_0(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_46
    | ~ spl13_82
    | ~ spl13_85
    | ~ spl13_277 ),
    inference(subsumption_resolution,[],[f4178,f382])).

fof(f4178,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_82
    | ~ spl13_85
    | ~ spl13_277 ),
    inference(subsumption_resolution,[],[f4177,f541])).

fof(f4177,plain,
    ( ~ r1_tsep_1(sK2,sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_85
    | ~ spl13_277 ),
    inference(subsumption_resolution,[],[f4175,f566])).

fof(f4175,plain,
    ( r3_tsep_1(sK0,sK2,sK1)
    | ~ r1_tsep_1(sK2,sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_277 ),
    inference(resolution,[],[f3845,f170])).

fof(f170,plain,(
    ! [X2,X0,X1] :
      ( v2_pre_topc(sK6(X0,X1,X2))
      | r3_tsep_1(X0,X1,X2)
      | ~ r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f119])).

fof(f3845,plain,
    ( ~ v2_pre_topc(sK6(sK0,sK2,sK1))
    | ~ spl13_277 ),
    inference(avatar_component_clause,[],[f3844])).

fof(f3844,plain,
    ( spl13_277
  <=> ~ v2_pre_topc(sK6(sK0,sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_277])])).

fof(f4173,plain,
    ( ~ spl13_42
    | spl13_45
    | ~ spl13_46
    | spl13_49
    | ~ spl13_50
    | ~ spl13_52
    | spl13_55
    | ~ spl13_82
    | spl13_85
    | spl13_275 ),
    inference(avatar_contradiction_clause,[],[f4172])).

fof(f4172,plain,
    ( $false
    | ~ spl13_42
    | ~ spl13_45
    | ~ spl13_46
    | ~ spl13_49
    | ~ spl13_50
    | ~ spl13_52
    | ~ spl13_55
    | ~ spl13_82
    | ~ spl13_85
    | ~ spl13_275 ),
    inference(subsumption_resolution,[],[f4171,f410])).

fof(f4171,plain,
    ( v2_struct_0(sK0)
    | ~ spl13_42
    | ~ spl13_45
    | ~ spl13_46
    | ~ spl13_49
    | ~ spl13_50
    | ~ spl13_52
    | ~ spl13_82
    | ~ spl13_85
    | ~ spl13_275 ),
    inference(subsumption_resolution,[],[f4170,f403])).

fof(f4170,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_42
    | ~ spl13_45
    | ~ spl13_46
    | ~ spl13_49
    | ~ spl13_50
    | ~ spl13_82
    | ~ spl13_85
    | ~ spl13_275 ),
    inference(subsumption_resolution,[],[f4169,f396])).

fof(f4169,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_42
    | ~ spl13_45
    | ~ spl13_46
    | ~ spl13_49
    | ~ spl13_82
    | ~ spl13_85
    | ~ spl13_275 ),
    inference(subsumption_resolution,[],[f4168,f375])).

fof(f4168,plain,
    ( v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_42
    | ~ spl13_46
    | ~ spl13_49
    | ~ spl13_82
    | ~ spl13_85
    | ~ spl13_275 ),
    inference(subsumption_resolution,[],[f4167,f368])).

fof(f4167,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_46
    | ~ spl13_49
    | ~ spl13_82
    | ~ spl13_85
    | ~ spl13_275 ),
    inference(subsumption_resolution,[],[f4166,f389])).

fof(f4166,plain,
    ( v2_struct_0(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_46
    | ~ spl13_82
    | ~ spl13_85
    | ~ spl13_275 ),
    inference(subsumption_resolution,[],[f4165,f382])).

fof(f4165,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_82
    | ~ spl13_85
    | ~ spl13_275 ),
    inference(subsumption_resolution,[],[f4164,f541])).

fof(f4164,plain,
    ( ~ r1_tsep_1(sK2,sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_85
    | ~ spl13_275 ),
    inference(subsumption_resolution,[],[f4162,f566])).

fof(f4162,plain,
    ( r3_tsep_1(sK0,sK2,sK1)
    | ~ r1_tsep_1(sK2,sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_275 ),
    inference(resolution,[],[f3839,f171])).

fof(f171,plain,(
    ! [X2,X0,X1] :
      ( l1_pre_topc(sK6(X0,X1,X2))
      | r3_tsep_1(X0,X1,X2)
      | ~ r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f119])).

fof(f3839,plain,
    ( ~ l1_pre_topc(sK6(sK0,sK2,sK1))
    | ~ spl13_275 ),
    inference(avatar_component_clause,[],[f3838])).

fof(f3838,plain,
    ( spl13_275
  <=> ~ l1_pre_topc(sK6(sK0,sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_275])])).

fof(f4091,plain,
    ( ~ spl13_42
    | spl13_45
    | ~ spl13_46
    | spl13_49
    | ~ spl13_50
    | ~ spl13_52
    | spl13_55
    | ~ spl13_82
    | spl13_85
    | spl13_273 ),
    inference(avatar_contradiction_clause,[],[f4090])).

fof(f4090,plain,
    ( $false
    | ~ spl13_42
    | ~ spl13_45
    | ~ spl13_46
    | ~ spl13_49
    | ~ spl13_50
    | ~ spl13_52
    | ~ spl13_55
    | ~ spl13_82
    | ~ spl13_85
    | ~ spl13_273 ),
    inference(subsumption_resolution,[],[f4089,f410])).

fof(f4089,plain,
    ( v2_struct_0(sK0)
    | ~ spl13_42
    | ~ spl13_45
    | ~ spl13_46
    | ~ spl13_49
    | ~ spl13_50
    | ~ spl13_52
    | ~ spl13_82
    | ~ spl13_85
    | ~ spl13_273 ),
    inference(subsumption_resolution,[],[f4088,f403])).

fof(f4088,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_42
    | ~ spl13_45
    | ~ spl13_46
    | ~ spl13_49
    | ~ spl13_50
    | ~ spl13_82
    | ~ spl13_85
    | ~ spl13_273 ),
    inference(subsumption_resolution,[],[f4087,f396])).

fof(f4087,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_42
    | ~ spl13_45
    | ~ spl13_46
    | ~ spl13_49
    | ~ spl13_82
    | ~ spl13_85
    | ~ spl13_273 ),
    inference(subsumption_resolution,[],[f4086,f375])).

fof(f4086,plain,
    ( v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_42
    | ~ spl13_46
    | ~ spl13_49
    | ~ spl13_82
    | ~ spl13_85
    | ~ spl13_273 ),
    inference(subsumption_resolution,[],[f4085,f368])).

fof(f4085,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_46
    | ~ spl13_49
    | ~ spl13_82
    | ~ spl13_85
    | ~ spl13_273 ),
    inference(subsumption_resolution,[],[f4084,f389])).

fof(f4084,plain,
    ( v2_struct_0(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_46
    | ~ spl13_82
    | ~ spl13_85
    | ~ spl13_273 ),
    inference(subsumption_resolution,[],[f4083,f382])).

fof(f4083,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_82
    | ~ spl13_85
    | ~ spl13_273 ),
    inference(subsumption_resolution,[],[f4082,f541])).

fof(f4082,plain,
    ( ~ r1_tsep_1(sK2,sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_85
    | ~ spl13_273 ),
    inference(subsumption_resolution,[],[f4076,f566])).

fof(f4076,plain,
    ( r3_tsep_1(sK0,sK2,sK1)
    | ~ r1_tsep_1(sK2,sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_273 ),
    inference(resolution,[],[f3833,f659])).

fof(f659,plain,(
    ! [X4,X5,X3] :
      ( v1_funct_1(k3_tmap_1(X3,sK6(X3,X4,X5),k1_tsep_1(X3,X5,X4),X5,sK7(X3,X4,X5)))
      | r3_tsep_1(X3,X4,X5)
      | ~ r1_tsep_1(X4,X5)
      | ~ m1_pre_topc(X5,X3)
      | v2_struct_0(X5)
      | ~ m1_pre_topc(X4,X3)
      | v2_struct_0(X4)
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | v2_struct_0(X3) ) ),
    inference(duplicate_literal_removal,[],[f658])).

fof(f658,plain,(
    ! [X4,X5,X3] :
      ( v1_funct_1(k3_tmap_1(X3,sK6(X3,X4,X5),k1_tsep_1(X3,X5,X4),X5,sK7(X3,X4,X5)))
      | r3_tsep_1(X3,X4,X5)
      | ~ r1_tsep_1(X4,X5)
      | ~ m1_pre_topc(X5,X3)
      | v2_struct_0(X5)
      | ~ m1_pre_topc(X4,X3)
      | v2_struct_0(X4)
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X5,X3)
      | v2_struct_0(X5)
      | ~ m1_pre_topc(X4,X3)
      | v2_struct_0(X4)
      | ~ l1_pre_topc(X3)
      | v2_struct_0(X3) ) ),
    inference(superposition,[],[f179,f163])).

fof(f179,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(k3_tmap_1(X0,sK6(X0,X1,X2),k1_tsep_1(X0,X1,X2),X2,sK7(X0,X1,X2)))
      | r3_tsep_1(X0,X1,X2)
      | ~ r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f119])).

fof(f3833,plain,
    ( ~ v1_funct_1(k3_tmap_1(sK0,sK6(sK0,sK2,sK1),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK2,sK1)))
    | ~ spl13_273 ),
    inference(avatar_component_clause,[],[f3832])).

fof(f3832,plain,
    ( spl13_273
  <=> ~ v1_funct_1(k3_tmap_1(sK0,sK6(sK0,sK2,sK1),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_273])])).

fof(f4053,plain,
    ( ~ spl13_42
    | spl13_45
    | ~ spl13_46
    | spl13_49
    | ~ spl13_50
    | ~ spl13_52
    | spl13_55
    | ~ spl13_82
    | spl13_85
    | spl13_271 ),
    inference(avatar_contradiction_clause,[],[f4052])).

fof(f4052,plain,
    ( $false
    | ~ spl13_42
    | ~ spl13_45
    | ~ spl13_46
    | ~ spl13_49
    | ~ spl13_50
    | ~ spl13_52
    | ~ spl13_55
    | ~ spl13_82
    | ~ spl13_85
    | ~ spl13_271 ),
    inference(subsumption_resolution,[],[f4051,f410])).

fof(f4051,plain,
    ( v2_struct_0(sK0)
    | ~ spl13_42
    | ~ spl13_45
    | ~ spl13_46
    | ~ spl13_49
    | ~ spl13_50
    | ~ spl13_52
    | ~ spl13_82
    | ~ spl13_85
    | ~ spl13_271 ),
    inference(subsumption_resolution,[],[f4050,f403])).

fof(f4050,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_42
    | ~ spl13_45
    | ~ spl13_46
    | ~ spl13_49
    | ~ spl13_50
    | ~ spl13_82
    | ~ spl13_85
    | ~ spl13_271 ),
    inference(subsumption_resolution,[],[f4049,f396])).

fof(f4049,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_42
    | ~ spl13_45
    | ~ spl13_46
    | ~ spl13_49
    | ~ spl13_82
    | ~ spl13_85
    | ~ spl13_271 ),
    inference(subsumption_resolution,[],[f4048,f375])).

fof(f4048,plain,
    ( v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_42
    | ~ spl13_46
    | ~ spl13_49
    | ~ spl13_82
    | ~ spl13_85
    | ~ spl13_271 ),
    inference(subsumption_resolution,[],[f4047,f368])).

fof(f4047,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_46
    | ~ spl13_49
    | ~ spl13_82
    | ~ spl13_85
    | ~ spl13_271 ),
    inference(subsumption_resolution,[],[f4046,f389])).

fof(f4046,plain,
    ( v2_struct_0(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_46
    | ~ spl13_82
    | ~ spl13_85
    | ~ spl13_271 ),
    inference(subsumption_resolution,[],[f4045,f382])).

fof(f4045,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_82
    | ~ spl13_85
    | ~ spl13_271 ),
    inference(subsumption_resolution,[],[f4044,f541])).

fof(f4044,plain,
    ( ~ r1_tsep_1(sK2,sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_85
    | ~ spl13_271 ),
    inference(subsumption_resolution,[],[f4041,f566])).

fof(f4041,plain,
    ( r3_tsep_1(sK0,sK2,sK1)
    | ~ r1_tsep_1(sK2,sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_271 ),
    inference(resolution,[],[f3827,f717])).

fof(f717,plain,(
    ! [X4,X5,X3] :
      ( v1_funct_2(k3_tmap_1(X3,sK6(X3,X4,X5),k1_tsep_1(X3,X5,X4),X5,sK7(X3,X4,X5)),u1_struct_0(X5),u1_struct_0(sK6(X3,X4,X5)))
      | r3_tsep_1(X3,X4,X5)
      | ~ r1_tsep_1(X4,X5)
      | ~ m1_pre_topc(X5,X3)
      | v2_struct_0(X5)
      | ~ m1_pre_topc(X4,X3)
      | v2_struct_0(X4)
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | v2_struct_0(X3) ) ),
    inference(duplicate_literal_removal,[],[f716])).

fof(f716,plain,(
    ! [X4,X5,X3] :
      ( v1_funct_2(k3_tmap_1(X3,sK6(X3,X4,X5),k1_tsep_1(X3,X5,X4),X5,sK7(X3,X4,X5)),u1_struct_0(X5),u1_struct_0(sK6(X3,X4,X5)))
      | r3_tsep_1(X3,X4,X5)
      | ~ r1_tsep_1(X4,X5)
      | ~ m1_pre_topc(X5,X3)
      | v2_struct_0(X5)
      | ~ m1_pre_topc(X4,X3)
      | v2_struct_0(X4)
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X5,X3)
      | v2_struct_0(X5)
      | ~ m1_pre_topc(X4,X3)
      | v2_struct_0(X4)
      | ~ l1_pre_topc(X3)
      | v2_struct_0(X3) ) ),
    inference(superposition,[],[f180,f163])).

fof(f180,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k3_tmap_1(X0,sK6(X0,X1,X2),k1_tsep_1(X0,X1,X2),X2,sK7(X0,X1,X2)),u1_struct_0(X2),u1_struct_0(sK6(X0,X1,X2)))
      | r3_tsep_1(X0,X1,X2)
      | ~ r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f119])).

fof(f3827,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK0,sK6(sK0,sK2,sK1),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK2,sK1)),u1_struct_0(sK1),u1_struct_0(sK6(sK0,sK2,sK1)))
    | ~ spl13_271 ),
    inference(avatar_component_clause,[],[f3826])).

fof(f3826,plain,
    ( spl13_271
  <=> ~ v1_funct_2(k3_tmap_1(sK0,sK6(sK0,sK2,sK1),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK2,sK1)),u1_struct_0(sK1),u1_struct_0(sK6(sK0,sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_271])])).

fof(f4026,plain,
    ( ~ spl13_42
    | spl13_45
    | ~ spl13_46
    | spl13_49
    | ~ spl13_50
    | ~ spl13_52
    | spl13_55
    | ~ spl13_82
    | spl13_85
    | spl13_269 ),
    inference(avatar_contradiction_clause,[],[f4025])).

fof(f4025,plain,
    ( $false
    | ~ spl13_42
    | ~ spl13_45
    | ~ spl13_46
    | ~ spl13_49
    | ~ spl13_50
    | ~ spl13_52
    | ~ spl13_55
    | ~ spl13_82
    | ~ spl13_85
    | ~ spl13_269 ),
    inference(subsumption_resolution,[],[f4024,f410])).

fof(f4024,plain,
    ( v2_struct_0(sK0)
    | ~ spl13_42
    | ~ spl13_45
    | ~ spl13_46
    | ~ spl13_49
    | ~ spl13_50
    | ~ spl13_52
    | ~ spl13_82
    | ~ spl13_85
    | ~ spl13_269 ),
    inference(subsumption_resolution,[],[f4023,f403])).

fof(f4023,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_42
    | ~ spl13_45
    | ~ spl13_46
    | ~ spl13_49
    | ~ spl13_50
    | ~ spl13_82
    | ~ spl13_85
    | ~ spl13_269 ),
    inference(subsumption_resolution,[],[f4022,f396])).

fof(f4022,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_42
    | ~ spl13_45
    | ~ spl13_46
    | ~ spl13_49
    | ~ spl13_82
    | ~ spl13_85
    | ~ spl13_269 ),
    inference(subsumption_resolution,[],[f4021,f375])).

fof(f4021,plain,
    ( v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_42
    | ~ spl13_46
    | ~ spl13_49
    | ~ spl13_82
    | ~ spl13_85
    | ~ spl13_269 ),
    inference(subsumption_resolution,[],[f4020,f368])).

fof(f4020,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_46
    | ~ spl13_49
    | ~ spl13_82
    | ~ spl13_85
    | ~ spl13_269 ),
    inference(subsumption_resolution,[],[f4019,f389])).

fof(f4019,plain,
    ( v2_struct_0(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_46
    | ~ spl13_82
    | ~ spl13_85
    | ~ spl13_269 ),
    inference(subsumption_resolution,[],[f4018,f382])).

fof(f4018,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_82
    | ~ spl13_85
    | ~ spl13_269 ),
    inference(subsumption_resolution,[],[f4017,f541])).

fof(f4017,plain,
    ( ~ r1_tsep_1(sK2,sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_85
    | ~ spl13_269 ),
    inference(subsumption_resolution,[],[f4015,f566])).

fof(f4015,plain,
    ( r3_tsep_1(sK0,sK2,sK1)
    | ~ r1_tsep_1(sK2,sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_269 ),
    inference(resolution,[],[f3821,f705])).

fof(f705,plain,(
    ! [X4,X5,X3] :
      ( v5_pre_topc(k3_tmap_1(X3,sK6(X3,X4,X5),k1_tsep_1(X3,X5,X4),X5,sK7(X3,X4,X5)),X5,sK6(X3,X4,X5))
      | r3_tsep_1(X3,X4,X5)
      | ~ r1_tsep_1(X4,X5)
      | ~ m1_pre_topc(X5,X3)
      | v2_struct_0(X5)
      | ~ m1_pre_topc(X4,X3)
      | v2_struct_0(X4)
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | v2_struct_0(X3) ) ),
    inference(duplicate_literal_removal,[],[f704])).

fof(f704,plain,(
    ! [X4,X5,X3] :
      ( v5_pre_topc(k3_tmap_1(X3,sK6(X3,X4,X5),k1_tsep_1(X3,X5,X4),X5,sK7(X3,X4,X5)),X5,sK6(X3,X4,X5))
      | r3_tsep_1(X3,X4,X5)
      | ~ r1_tsep_1(X4,X5)
      | ~ m1_pre_topc(X5,X3)
      | v2_struct_0(X5)
      | ~ m1_pre_topc(X4,X3)
      | v2_struct_0(X4)
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X5,X3)
      | v2_struct_0(X5)
      | ~ m1_pre_topc(X4,X3)
      | v2_struct_0(X4)
      | ~ l1_pre_topc(X3)
      | v2_struct_0(X3) ) ),
    inference(superposition,[],[f181,f163])).

fof(f181,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(k3_tmap_1(X0,sK6(X0,X1,X2),k1_tsep_1(X0,X1,X2),X2,sK7(X0,X1,X2)),X2,sK6(X0,X1,X2))
      | r3_tsep_1(X0,X1,X2)
      | ~ r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f119])).

fof(f3821,plain,
    ( ~ v5_pre_topc(k3_tmap_1(sK0,sK6(sK0,sK2,sK1),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK2,sK1)),sK1,sK6(sK0,sK2,sK1))
    | ~ spl13_269 ),
    inference(avatar_component_clause,[],[f3820])).

fof(f3820,plain,
    ( spl13_269
  <=> ~ v5_pre_topc(k3_tmap_1(sK0,sK6(sK0,sK2,sK1),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK2,sK1)),sK1,sK6(sK0,sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_269])])).

fof(f3996,plain,
    ( ~ spl13_42
    | spl13_45
    | ~ spl13_46
    | spl13_49
    | ~ spl13_50
    | ~ spl13_52
    | spl13_55
    | ~ spl13_82
    | spl13_85
    | spl13_267 ),
    inference(avatar_contradiction_clause,[],[f3995])).

fof(f3995,plain,
    ( $false
    | ~ spl13_42
    | ~ spl13_45
    | ~ spl13_46
    | ~ spl13_49
    | ~ spl13_50
    | ~ spl13_52
    | ~ spl13_55
    | ~ spl13_82
    | ~ spl13_85
    | ~ spl13_267 ),
    inference(subsumption_resolution,[],[f3994,f410])).

fof(f3994,plain,
    ( v2_struct_0(sK0)
    | ~ spl13_42
    | ~ spl13_45
    | ~ spl13_46
    | ~ spl13_49
    | ~ spl13_50
    | ~ spl13_52
    | ~ spl13_82
    | ~ spl13_85
    | ~ spl13_267 ),
    inference(subsumption_resolution,[],[f3993,f403])).

fof(f3993,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_42
    | ~ spl13_45
    | ~ spl13_46
    | ~ spl13_49
    | ~ spl13_50
    | ~ spl13_82
    | ~ spl13_85
    | ~ spl13_267 ),
    inference(subsumption_resolution,[],[f3992,f396])).

fof(f3992,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_42
    | ~ spl13_45
    | ~ spl13_46
    | ~ spl13_49
    | ~ spl13_82
    | ~ spl13_85
    | ~ spl13_267 ),
    inference(subsumption_resolution,[],[f3991,f375])).

fof(f3991,plain,
    ( v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_42
    | ~ spl13_46
    | ~ spl13_49
    | ~ spl13_82
    | ~ spl13_85
    | ~ spl13_267 ),
    inference(subsumption_resolution,[],[f3990,f368])).

fof(f3990,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_46
    | ~ spl13_49
    | ~ spl13_82
    | ~ spl13_85
    | ~ spl13_267 ),
    inference(subsumption_resolution,[],[f3989,f389])).

fof(f3989,plain,
    ( v2_struct_0(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_46
    | ~ spl13_82
    | ~ spl13_85
    | ~ spl13_267 ),
    inference(subsumption_resolution,[],[f3988,f382])).

fof(f3988,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_82
    | ~ spl13_85
    | ~ spl13_267 ),
    inference(subsumption_resolution,[],[f3987,f541])).

fof(f3987,plain,
    ( ~ r1_tsep_1(sK2,sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_85
    | ~ spl13_267 ),
    inference(subsumption_resolution,[],[f3984,f566])).

fof(f3984,plain,
    ( r3_tsep_1(sK0,sK2,sK1)
    | ~ r1_tsep_1(sK2,sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_267 ),
    inference(resolution,[],[f3815,f777])).

fof(f777,plain,(
    ! [X4,X5,X3] :
      ( m1_subset_1(k3_tmap_1(X3,sK6(X3,X4,X5),k1_tsep_1(X3,X5,X4),X5,sK7(X3,X4,X5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK6(X3,X4,X5)))))
      | r3_tsep_1(X3,X4,X5)
      | ~ r1_tsep_1(X4,X5)
      | ~ m1_pre_topc(X5,X3)
      | v2_struct_0(X5)
      | ~ m1_pre_topc(X4,X3)
      | v2_struct_0(X4)
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | v2_struct_0(X3) ) ),
    inference(duplicate_literal_removal,[],[f776])).

fof(f776,plain,(
    ! [X4,X5,X3] :
      ( m1_subset_1(k3_tmap_1(X3,sK6(X3,X4,X5),k1_tsep_1(X3,X5,X4),X5,sK7(X3,X4,X5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK6(X3,X4,X5)))))
      | r3_tsep_1(X3,X4,X5)
      | ~ r1_tsep_1(X4,X5)
      | ~ m1_pre_topc(X5,X3)
      | v2_struct_0(X5)
      | ~ m1_pre_topc(X4,X3)
      | v2_struct_0(X4)
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X5,X3)
      | v2_struct_0(X5)
      | ~ m1_pre_topc(X4,X3)
      | v2_struct_0(X4)
      | ~ l1_pre_topc(X3)
      | v2_struct_0(X3) ) ),
    inference(superposition,[],[f182,f163])).

fof(f182,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k3_tmap_1(X0,sK6(X0,X1,X2),k1_tsep_1(X0,X1,X2),X2,sK7(X0,X1,X2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK6(X0,X1,X2)))))
      | r3_tsep_1(X0,X1,X2)
      | ~ r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f119])).

fof(f3815,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK0,sK6(sK0,sK2,sK1),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK2,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK6(sK0,sK2,sK1)))))
    | ~ spl13_267 ),
    inference(avatar_component_clause,[],[f3814])).

fof(f3814,plain,
    ( spl13_267
  <=> ~ m1_subset_1(k3_tmap_1(sK0,sK6(sK0,sK2,sK1),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK2,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK6(sK0,sK2,sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_267])])).

fof(f3964,plain,
    ( ~ spl13_42
    | spl13_45
    | ~ spl13_46
    | spl13_49
    | ~ spl13_50
    | ~ spl13_52
    | spl13_55
    | ~ spl13_82
    | spl13_85
    | spl13_265 ),
    inference(avatar_contradiction_clause,[],[f3963])).

fof(f3963,plain,
    ( $false
    | ~ spl13_42
    | ~ spl13_45
    | ~ spl13_46
    | ~ spl13_49
    | ~ spl13_50
    | ~ spl13_52
    | ~ spl13_55
    | ~ spl13_82
    | ~ spl13_85
    | ~ spl13_265 ),
    inference(subsumption_resolution,[],[f3962,f410])).

fof(f3962,plain,
    ( v2_struct_0(sK0)
    | ~ spl13_42
    | ~ spl13_45
    | ~ spl13_46
    | ~ spl13_49
    | ~ spl13_50
    | ~ spl13_52
    | ~ spl13_82
    | ~ spl13_85
    | ~ spl13_265 ),
    inference(subsumption_resolution,[],[f3961,f403])).

fof(f3961,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_42
    | ~ spl13_45
    | ~ spl13_46
    | ~ spl13_49
    | ~ spl13_50
    | ~ spl13_82
    | ~ spl13_85
    | ~ spl13_265 ),
    inference(subsumption_resolution,[],[f3960,f396])).

fof(f3960,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_42
    | ~ spl13_45
    | ~ spl13_46
    | ~ spl13_49
    | ~ spl13_82
    | ~ spl13_85
    | ~ spl13_265 ),
    inference(subsumption_resolution,[],[f3959,f375])).

fof(f3959,plain,
    ( v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_42
    | ~ spl13_46
    | ~ spl13_49
    | ~ spl13_82
    | ~ spl13_85
    | ~ spl13_265 ),
    inference(subsumption_resolution,[],[f3958,f368])).

fof(f3958,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_46
    | ~ spl13_49
    | ~ spl13_82
    | ~ spl13_85
    | ~ spl13_265 ),
    inference(subsumption_resolution,[],[f3957,f389])).

fof(f3957,plain,
    ( v2_struct_0(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_46
    | ~ spl13_82
    | ~ spl13_85
    | ~ spl13_265 ),
    inference(subsumption_resolution,[],[f3956,f382])).

fof(f3956,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_82
    | ~ spl13_85
    | ~ spl13_265 ),
    inference(subsumption_resolution,[],[f3955,f541])).

fof(f3955,plain,
    ( ~ r1_tsep_1(sK2,sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_85
    | ~ spl13_265 ),
    inference(subsumption_resolution,[],[f3949,f566])).

fof(f3949,plain,
    ( r3_tsep_1(sK0,sK2,sK1)
    | ~ r1_tsep_1(sK2,sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_265 ),
    inference(resolution,[],[f3809,f651])).

fof(f651,plain,(
    ! [X4,X5,X3] :
      ( v1_funct_1(k3_tmap_1(X3,sK6(X3,X4,X5),k1_tsep_1(X3,X5,X4),X4,sK7(X3,X4,X5)))
      | r3_tsep_1(X3,X4,X5)
      | ~ r1_tsep_1(X4,X5)
      | ~ m1_pre_topc(X5,X3)
      | v2_struct_0(X5)
      | ~ m1_pre_topc(X4,X3)
      | v2_struct_0(X4)
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | v2_struct_0(X3) ) ),
    inference(duplicate_literal_removal,[],[f650])).

fof(f650,plain,(
    ! [X4,X5,X3] :
      ( v1_funct_1(k3_tmap_1(X3,sK6(X3,X4,X5),k1_tsep_1(X3,X5,X4),X4,sK7(X3,X4,X5)))
      | r3_tsep_1(X3,X4,X5)
      | ~ r1_tsep_1(X4,X5)
      | ~ m1_pre_topc(X5,X3)
      | v2_struct_0(X5)
      | ~ m1_pre_topc(X4,X3)
      | v2_struct_0(X4)
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X5,X3)
      | v2_struct_0(X5)
      | ~ m1_pre_topc(X4,X3)
      | v2_struct_0(X4)
      | ~ l1_pre_topc(X3)
      | v2_struct_0(X3) ) ),
    inference(superposition,[],[f175,f163])).

fof(f175,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(k3_tmap_1(X0,sK6(X0,X1,X2),k1_tsep_1(X0,X1,X2),X1,sK7(X0,X1,X2)))
      | r3_tsep_1(X0,X1,X2)
      | ~ r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f119])).

fof(f3809,plain,
    ( ~ v1_funct_1(k3_tmap_1(sK0,sK6(sK0,sK2,sK1),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK2,sK1)))
    | ~ spl13_265 ),
    inference(avatar_component_clause,[],[f3808])).

fof(f3808,plain,
    ( spl13_265
  <=> ~ v1_funct_1(k3_tmap_1(sK0,sK6(sK0,sK2,sK1),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_265])])).

fof(f3943,plain,
    ( ~ spl13_42
    | spl13_45
    | ~ spl13_46
    | spl13_49
    | ~ spl13_50
    | ~ spl13_52
    | spl13_55
    | ~ spl13_82
    | spl13_85
    | spl13_263 ),
    inference(avatar_contradiction_clause,[],[f3942])).

fof(f3942,plain,
    ( $false
    | ~ spl13_42
    | ~ spl13_45
    | ~ spl13_46
    | ~ spl13_49
    | ~ spl13_50
    | ~ spl13_52
    | ~ spl13_55
    | ~ spl13_82
    | ~ spl13_85
    | ~ spl13_263 ),
    inference(subsumption_resolution,[],[f3941,f410])).

fof(f3941,plain,
    ( v2_struct_0(sK0)
    | ~ spl13_42
    | ~ spl13_45
    | ~ spl13_46
    | ~ spl13_49
    | ~ spl13_50
    | ~ spl13_52
    | ~ spl13_82
    | ~ spl13_85
    | ~ spl13_263 ),
    inference(subsumption_resolution,[],[f3940,f403])).

fof(f3940,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_42
    | ~ spl13_45
    | ~ spl13_46
    | ~ spl13_49
    | ~ spl13_50
    | ~ spl13_82
    | ~ spl13_85
    | ~ spl13_263 ),
    inference(subsumption_resolution,[],[f3939,f396])).

fof(f3939,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_42
    | ~ spl13_45
    | ~ spl13_46
    | ~ spl13_49
    | ~ spl13_82
    | ~ spl13_85
    | ~ spl13_263 ),
    inference(subsumption_resolution,[],[f3938,f375])).

fof(f3938,plain,
    ( v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_42
    | ~ spl13_46
    | ~ spl13_49
    | ~ spl13_82
    | ~ spl13_85
    | ~ spl13_263 ),
    inference(subsumption_resolution,[],[f3937,f368])).

fof(f3937,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_46
    | ~ spl13_49
    | ~ spl13_82
    | ~ spl13_85
    | ~ spl13_263 ),
    inference(subsumption_resolution,[],[f3936,f389])).

fof(f3936,plain,
    ( v2_struct_0(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_46
    | ~ spl13_82
    | ~ spl13_85
    | ~ spl13_263 ),
    inference(subsumption_resolution,[],[f3935,f382])).

fof(f3935,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_82
    | ~ spl13_85
    | ~ spl13_263 ),
    inference(subsumption_resolution,[],[f3934,f541])).

fof(f3934,plain,
    ( ~ r1_tsep_1(sK2,sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_85
    | ~ spl13_263 ),
    inference(subsumption_resolution,[],[f3931,f566])).

fof(f3931,plain,
    ( r3_tsep_1(sK0,sK2,sK1)
    | ~ r1_tsep_1(sK2,sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_263 ),
    inference(resolution,[],[f3803,f711])).

fof(f711,plain,(
    ! [X4,X5,X3] :
      ( v1_funct_2(k3_tmap_1(X3,sK6(X3,X4,X5),k1_tsep_1(X3,X5,X4),X4,sK7(X3,X4,X5)),u1_struct_0(X4),u1_struct_0(sK6(X3,X4,X5)))
      | r3_tsep_1(X3,X4,X5)
      | ~ r1_tsep_1(X4,X5)
      | ~ m1_pre_topc(X5,X3)
      | v2_struct_0(X5)
      | ~ m1_pre_topc(X4,X3)
      | v2_struct_0(X4)
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | v2_struct_0(X3) ) ),
    inference(duplicate_literal_removal,[],[f710])).

fof(f710,plain,(
    ! [X4,X5,X3] :
      ( v1_funct_2(k3_tmap_1(X3,sK6(X3,X4,X5),k1_tsep_1(X3,X5,X4),X4,sK7(X3,X4,X5)),u1_struct_0(X4),u1_struct_0(sK6(X3,X4,X5)))
      | r3_tsep_1(X3,X4,X5)
      | ~ r1_tsep_1(X4,X5)
      | ~ m1_pre_topc(X5,X3)
      | v2_struct_0(X5)
      | ~ m1_pre_topc(X4,X3)
      | v2_struct_0(X4)
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X5,X3)
      | v2_struct_0(X5)
      | ~ m1_pre_topc(X4,X3)
      | v2_struct_0(X4)
      | ~ l1_pre_topc(X3)
      | v2_struct_0(X3) ) ),
    inference(superposition,[],[f176,f163])).

fof(f176,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k3_tmap_1(X0,sK6(X0,X1,X2),k1_tsep_1(X0,X1,X2),X1,sK7(X0,X1,X2)),u1_struct_0(X1),u1_struct_0(sK6(X0,X1,X2)))
      | r3_tsep_1(X0,X1,X2)
      | ~ r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f119])).

fof(f3803,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK0,sK6(sK0,sK2,sK1),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK2,sK1)),u1_struct_0(sK2),u1_struct_0(sK6(sK0,sK2,sK1)))
    | ~ spl13_263 ),
    inference(avatar_component_clause,[],[f3802])).

fof(f3802,plain,
    ( spl13_263
  <=> ~ v1_funct_2(k3_tmap_1(sK0,sK6(sK0,sK2,sK1),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK2,sK1)),u1_struct_0(sK2),u1_struct_0(sK6(sK0,sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_263])])).

fof(f3925,plain,
    ( ~ spl13_42
    | spl13_45
    | ~ spl13_46
    | spl13_49
    | ~ spl13_50
    | ~ spl13_52
    | spl13_55
    | ~ spl13_82
    | spl13_85
    | spl13_261 ),
    inference(avatar_contradiction_clause,[],[f3924])).

fof(f3924,plain,
    ( $false
    | ~ spl13_42
    | ~ spl13_45
    | ~ spl13_46
    | ~ spl13_49
    | ~ spl13_50
    | ~ spl13_52
    | ~ spl13_55
    | ~ spl13_82
    | ~ spl13_85
    | ~ spl13_261 ),
    inference(subsumption_resolution,[],[f3923,f410])).

fof(f3923,plain,
    ( v2_struct_0(sK0)
    | ~ spl13_42
    | ~ spl13_45
    | ~ spl13_46
    | ~ spl13_49
    | ~ spl13_50
    | ~ spl13_52
    | ~ spl13_82
    | ~ spl13_85
    | ~ spl13_261 ),
    inference(subsumption_resolution,[],[f3922,f403])).

fof(f3922,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_42
    | ~ spl13_45
    | ~ spl13_46
    | ~ spl13_49
    | ~ spl13_50
    | ~ spl13_82
    | ~ spl13_85
    | ~ spl13_261 ),
    inference(subsumption_resolution,[],[f3921,f396])).

fof(f3921,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_42
    | ~ spl13_45
    | ~ spl13_46
    | ~ spl13_49
    | ~ spl13_82
    | ~ spl13_85
    | ~ spl13_261 ),
    inference(subsumption_resolution,[],[f3920,f375])).

fof(f3920,plain,
    ( v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_42
    | ~ spl13_46
    | ~ spl13_49
    | ~ spl13_82
    | ~ spl13_85
    | ~ spl13_261 ),
    inference(subsumption_resolution,[],[f3919,f368])).

fof(f3919,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_46
    | ~ spl13_49
    | ~ spl13_82
    | ~ spl13_85
    | ~ spl13_261 ),
    inference(subsumption_resolution,[],[f3918,f389])).

fof(f3918,plain,
    ( v2_struct_0(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_46
    | ~ spl13_82
    | ~ spl13_85
    | ~ spl13_261 ),
    inference(subsumption_resolution,[],[f3917,f382])).

fof(f3917,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_82
    | ~ spl13_85
    | ~ spl13_261 ),
    inference(subsumption_resolution,[],[f3916,f541])).

fof(f3916,plain,
    ( ~ r1_tsep_1(sK2,sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_85
    | ~ spl13_261 ),
    inference(subsumption_resolution,[],[f3914,f566])).

fof(f3914,plain,
    ( r3_tsep_1(sK0,sK2,sK1)
    | ~ r1_tsep_1(sK2,sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_261 ),
    inference(resolution,[],[f3797,f699])).

fof(f699,plain,(
    ! [X4,X5,X3] :
      ( v5_pre_topc(k3_tmap_1(X3,sK6(X3,X4,X5),k1_tsep_1(X3,X5,X4),X4,sK7(X3,X4,X5)),X4,sK6(X3,X4,X5))
      | r3_tsep_1(X3,X4,X5)
      | ~ r1_tsep_1(X4,X5)
      | ~ m1_pre_topc(X5,X3)
      | v2_struct_0(X5)
      | ~ m1_pre_topc(X4,X3)
      | v2_struct_0(X4)
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | v2_struct_0(X3) ) ),
    inference(duplicate_literal_removal,[],[f698])).

fof(f698,plain,(
    ! [X4,X5,X3] :
      ( v5_pre_topc(k3_tmap_1(X3,sK6(X3,X4,X5),k1_tsep_1(X3,X5,X4),X4,sK7(X3,X4,X5)),X4,sK6(X3,X4,X5))
      | r3_tsep_1(X3,X4,X5)
      | ~ r1_tsep_1(X4,X5)
      | ~ m1_pre_topc(X5,X3)
      | v2_struct_0(X5)
      | ~ m1_pre_topc(X4,X3)
      | v2_struct_0(X4)
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X5,X3)
      | v2_struct_0(X5)
      | ~ m1_pre_topc(X4,X3)
      | v2_struct_0(X4)
      | ~ l1_pre_topc(X3)
      | v2_struct_0(X3) ) ),
    inference(superposition,[],[f177,f163])).

fof(f177,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(k3_tmap_1(X0,sK6(X0,X1,X2),k1_tsep_1(X0,X1,X2),X1,sK7(X0,X1,X2)),X1,sK6(X0,X1,X2))
      | r3_tsep_1(X0,X1,X2)
      | ~ r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f119])).

fof(f3797,plain,
    ( ~ v5_pre_topc(k3_tmap_1(sK0,sK6(sK0,sK2,sK1),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK2,sK1)),sK2,sK6(sK0,sK2,sK1))
    | ~ spl13_261 ),
    inference(avatar_component_clause,[],[f3796])).

fof(f3796,plain,
    ( spl13_261
  <=> ~ v5_pre_topc(k3_tmap_1(sK0,sK6(sK0,sK2,sK1),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK2,sK1)),sK2,sK6(sK0,sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_261])])).

fof(f1174,plain,
    ( spl13_0
    | ~ spl13_42
    | ~ spl13_46
    | ~ spl13_50
    | ~ spl13_84 ),
    inference(avatar_split_clause,[],[f1173,f568,f395,f381,f367,f233])).

fof(f568,plain,
    ( spl13_84
  <=> r3_tsep_1(sK0,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_84])])).

fof(f1173,plain,
    ( r3_tsep_1(sK0,sK1,sK2)
    | ~ spl13_42
    | ~ spl13_46
    | ~ spl13_50
    | ~ spl13_84 ),
    inference(subsumption_resolution,[],[f1172,f396])).

fof(f1172,plain,
    ( r3_tsep_1(sK0,sK1,sK2)
    | ~ l1_pre_topc(sK0)
    | ~ spl13_42
    | ~ spl13_46
    | ~ spl13_84 ),
    inference(subsumption_resolution,[],[f1171,f368])).

fof(f1171,plain,
    ( r3_tsep_1(sK0,sK1,sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl13_46
    | ~ spl13_84 ),
    inference(subsumption_resolution,[],[f903,f382])).

fof(f903,plain,
    ( r3_tsep_1(sK0,sK1,sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl13_84 ),
    inference(resolution,[],[f569,f212])).

fof(f212,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_tsep_1(X0,X1,X2)
      | r3_tsep_1(X0,X2,X1)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f90])).

fof(f90,plain,(
    ! [X0,X1,X2] :
      ( r3_tsep_1(X0,X2,X1)
      | ~ r3_tsep_1(X0,X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f89])).

fof(f89,plain,(
    ! [X0,X1,X2] :
      ( r3_tsep_1(X0,X2,X1)
      | ~ r3_tsep_1(X0,X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & m1_pre_topc(X1,X0)
        & l1_pre_topc(X0) )
     => ( r3_tsep_1(X0,X1,X2)
       => r3_tsep_1(X0,X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t150_tmap_1.p',symmetry_r3_tsep_1)).

fof(f569,plain,
    ( r3_tsep_1(sK0,sK2,sK1)
    | ~ spl13_84 ),
    inference(avatar_component_clause,[],[f568])).

fof(f1161,plain,
    ( ~ spl13_2
    | spl13_9
    | ~ spl13_12
    | ~ spl13_14
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_26
    | ~ spl13_28
    | ~ spl13_30
    | spl13_33
    | ~ spl13_42
    | spl13_45
    | ~ spl13_46
    | spl13_49
    | ~ spl13_50
    | ~ spl13_52
    | spl13_55
    | ~ spl13_92 ),
    inference(avatar_contradiction_clause,[],[f1160])).

fof(f1160,plain,
    ( $false
    | ~ spl13_2
    | ~ spl13_9
    | ~ spl13_12
    | ~ spl13_14
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_26
    | ~ spl13_28
    | ~ spl13_30
    | ~ spl13_33
    | ~ spl13_42
    | ~ spl13_45
    | ~ spl13_46
    | ~ spl13_49
    | ~ spl13_50
    | ~ spl13_52
    | ~ spl13_55
    | ~ spl13_92 ),
    inference(subsumption_resolution,[],[f1159,f410])).

fof(f1159,plain,
    ( v2_struct_0(sK0)
    | ~ spl13_2
    | ~ spl13_9
    | ~ spl13_12
    | ~ spl13_14
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_26
    | ~ spl13_28
    | ~ spl13_30
    | ~ spl13_33
    | ~ spl13_42
    | ~ spl13_45
    | ~ spl13_46
    | ~ spl13_49
    | ~ spl13_50
    | ~ spl13_52
    | ~ spl13_92 ),
    inference(subsumption_resolution,[],[f1158,f403])).

fof(f1158,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_2
    | ~ spl13_9
    | ~ spl13_12
    | ~ spl13_14
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_26
    | ~ spl13_28
    | ~ spl13_30
    | ~ spl13_33
    | ~ spl13_42
    | ~ spl13_45
    | ~ spl13_46
    | ~ spl13_49
    | ~ spl13_50
    | ~ spl13_92 ),
    inference(subsumption_resolution,[],[f1157,f396])).

fof(f1157,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_2
    | ~ spl13_9
    | ~ spl13_12
    | ~ spl13_14
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_26
    | ~ spl13_28
    | ~ spl13_30
    | ~ spl13_33
    | ~ spl13_42
    | ~ spl13_45
    | ~ spl13_46
    | ~ spl13_49
    | ~ spl13_92 ),
    inference(subsumption_resolution,[],[f1156,f344])).

fof(f1156,plain,
    ( v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_2
    | ~ spl13_9
    | ~ spl13_12
    | ~ spl13_14
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_26
    | ~ spl13_28
    | ~ spl13_30
    | ~ spl13_42
    | ~ spl13_45
    | ~ spl13_46
    | ~ spl13_49
    | ~ spl13_92 ),
    inference(subsumption_resolution,[],[f1155,f337])).

fof(f1155,plain,
    ( ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_2
    | ~ spl13_9
    | ~ spl13_12
    | ~ spl13_14
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_26
    | ~ spl13_28
    | ~ spl13_42
    | ~ spl13_45
    | ~ spl13_46
    | ~ spl13_49
    | ~ spl13_92 ),
    inference(subsumption_resolution,[],[f1154,f330])).

fof(f1154,plain,
    ( ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_2
    | ~ spl13_9
    | ~ spl13_12
    | ~ spl13_14
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_26
    | ~ spl13_42
    | ~ spl13_45
    | ~ spl13_46
    | ~ spl13_49
    | ~ spl13_92 ),
    inference(subsumption_resolution,[],[f1153,f389])).

fof(f1153,plain,
    ( v2_struct_0(sK1)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_2
    | ~ spl13_9
    | ~ spl13_12
    | ~ spl13_14
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_26
    | ~ spl13_42
    | ~ spl13_45
    | ~ spl13_46
    | ~ spl13_92 ),
    inference(subsumption_resolution,[],[f1152,f382])).

fof(f1152,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_2
    | ~ spl13_9
    | ~ spl13_12
    | ~ spl13_14
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_26
    | ~ spl13_42
    | ~ spl13_45
    | ~ spl13_92 ),
    inference(subsumption_resolution,[],[f1151,f375])).

fof(f1151,plain,
    ( v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_2
    | ~ spl13_9
    | ~ spl13_12
    | ~ spl13_14
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_26
    | ~ spl13_42
    | ~ spl13_92 ),
    inference(subsumption_resolution,[],[f1150,f368])).

fof(f1150,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_2
    | ~ spl13_9
    | ~ spl13_12
    | ~ spl13_14
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_26
    | ~ spl13_92 ),
    inference(subsumption_resolution,[],[f1149,f240])).

fof(f240,plain,
    ( r1_tsep_1(sK1,sK2)
    | ~ spl13_2 ),
    inference(avatar_component_clause,[],[f239])).

fof(f239,plain,
    ( spl13_2
  <=> r1_tsep_1(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_2])])).

fof(f1149,plain,
    ( ~ r1_tsep_1(sK1,sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_9
    | ~ spl13_12
    | ~ spl13_14
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_26
    | ~ spl13_92 ),
    inference(subsumption_resolution,[],[f1148,f323])).

fof(f1148,plain,
    ( ~ v1_funct_1(sK4)
    | ~ r1_tsep_1(sK1,sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_9
    | ~ spl13_12
    | ~ spl13_14
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_92 ),
    inference(subsumption_resolution,[],[f1147,f316])).

fof(f1147,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | ~ r1_tsep_1(sK1,sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_9
    | ~ spl13_12
    | ~ spl13_14
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_92 ),
    inference(subsumption_resolution,[],[f1146,f309])).

fof(f309,plain,
    ( v5_pre_topc(sK4,sK1,sK3)
    | ~ spl13_22 ),
    inference(avatar_component_clause,[],[f308])).

fof(f308,plain,
    ( spl13_22
  <=> v5_pre_topc(sK4,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_22])])).

fof(f1146,plain,
    ( ~ v5_pre_topc(sK4,sK1,sK3)
    | ~ v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | ~ r1_tsep_1(sK1,sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_9
    | ~ spl13_12
    | ~ spl13_14
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_92 ),
    inference(subsumption_resolution,[],[f1145,f302])).

fof(f1145,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK3))))
    | ~ v5_pre_topc(sK4,sK1,sK3)
    | ~ v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | ~ r1_tsep_1(sK1,sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_9
    | ~ spl13_12
    | ~ spl13_14
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_92 ),
    inference(subsumption_resolution,[],[f1144,f295])).

fof(f1144,plain,
    ( ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK3))))
    | ~ v5_pre_topc(sK4,sK1,sK3)
    | ~ v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | ~ r1_tsep_1(sK1,sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_9
    | ~ spl13_12
    | ~ spl13_14
    | ~ spl13_16
    | ~ spl13_92 ),
    inference(subsumption_resolution,[],[f1143,f288])).

fof(f1143,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK3))))
    | ~ v5_pre_topc(sK4,sK1,sK3)
    | ~ v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | ~ r1_tsep_1(sK1,sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_9
    | ~ spl13_12
    | ~ spl13_14
    | ~ spl13_92 ),
    inference(subsumption_resolution,[],[f1142,f281])).

fof(f281,plain,
    ( v5_pre_topc(sK5,sK2,sK3)
    | ~ spl13_14 ),
    inference(avatar_component_clause,[],[f280])).

fof(f280,plain,
    ( spl13_14
  <=> v5_pre_topc(sK5,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_14])])).

fof(f1142,plain,
    ( ~ v5_pre_topc(sK5,sK2,sK3)
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK3))))
    | ~ v5_pre_topc(sK4,sK1,sK3)
    | ~ v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | ~ r1_tsep_1(sK1,sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_9
    | ~ spl13_12
    | ~ spl13_92 ),
    inference(subsumption_resolution,[],[f1141,f274])).

fof(f1141,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v5_pre_topc(sK5,sK2,sK3)
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK3))))
    | ~ v5_pre_topc(sK4,sK1,sK3)
    | ~ v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | ~ r1_tsep_1(sK1,sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_9
    | ~ spl13_92 ),
    inference(subsumption_resolution,[],[f1135,f886])).

fof(f886,plain,
    ( r4_tsep_1(sK0,sK1,sK2)
    | ~ spl13_92 ),
    inference(avatar_component_clause,[],[f885])).

fof(f1135,plain,
    ( ~ r4_tsep_1(sK0,sK1,sK2)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v5_pre_topc(sK5,sK2,sK3)
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK3))))
    | ~ v5_pre_topc(sK4,sK1,sK3)
    | ~ v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | ~ r1_tsep_1(sK1,sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_9 ),
    inference(resolution,[],[f187,f261])).

fof(f261,plain,
    ( ~ v5_pre_topc(k10_tmap_1(sK0,sK3,sK1,sK2,sK4,sK5),k1_tsep_1(sK0,sK1,sK2),sK3)
    | ~ spl13_9 ),
    inference(avatar_component_clause,[],[f260])).

fof(f260,plain,
    ( spl13_9
  <=> ~ v5_pre_topc(k10_tmap_1(sK0,sK3,sK1,sK2,sK4,sK5),k1_tsep_1(sK0,sK1,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_9])])).

fof(f187,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1)
      | ~ r4_tsep_1(X0,X2,X3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v5_pre_topc(X5,X3,X1)
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v5_pre_topc(X4,X2,X1)
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ r1_tsep_1(X2,X3)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                            & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1)
                            & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                            & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
                          | ~ r4_tsep_1(X0,X2,X3)
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          | ~ v5_pre_topc(X5,X3,X1)
                          | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v5_pre_topc(X4,X2,X1)
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ r1_tsep_1(X2,X3)
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f62])).

fof(f62,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                            & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1)
                            & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                            & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
                          | ~ r4_tsep_1(X0,X2,X3)
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          | ~ v5_pre_topc(X5,X3,X1)
                          | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v5_pre_topc(X4,X2,X1)
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ r1_tsep_1(X2,X3)
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ( r1_tsep_1(X2,X3)
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v5_pre_topc(X4,X2,X1)
                          & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => ! [X5] :
                            ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                              & v5_pre_topc(X5,X3,X1)
                              & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                              & v1_funct_1(X5) )
                           => ( r4_tsep_1(X0,X2,X3)
                             => ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                                & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1)
                                & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                                & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t150_tmap_1.p',t145_tmap_1)).

fof(f1052,plain,
    ( spl13_5
    | ~ spl13_12
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_24
    | ~ spl13_26
    | ~ spl13_28
    | ~ spl13_30
    | spl13_33
    | ~ spl13_42
    | spl13_45
    | ~ spl13_46
    | spl13_49
    | ~ spl13_50
    | ~ spl13_52
    | spl13_55 ),
    inference(avatar_contradiction_clause,[],[f1051])).

fof(f1051,plain,
    ( $false
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_24
    | ~ spl13_26
    | ~ spl13_28
    | ~ spl13_30
    | ~ spl13_33
    | ~ spl13_42
    | ~ spl13_45
    | ~ spl13_46
    | ~ spl13_49
    | ~ spl13_50
    | ~ spl13_52
    | ~ spl13_55 ),
    inference(unit_resulting_resolution,[],[f410,f403,f396,f344,f337,f330,f389,f323,f375,f295,f382,f368,f316,f288,f302,f274,f249,f157])).

fof(f249,plain,
    ( ~ v1_funct_1(k10_tmap_1(sK0,sK3,sK1,sK2,sK4,sK5))
    | ~ spl13_5 ),
    inference(avatar_component_clause,[],[f248])).

fof(f248,plain,
    ( spl13_5
  <=> ~ v1_funct_1(k10_tmap_1(sK0,sK3,sK1,sK2,sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_5])])).

fof(f899,plain,
    ( spl13_82
    | ~ spl13_2
    | ~ spl13_74
    | ~ spl13_76 ),
    inference(avatar_split_clause,[],[f898,f501,f492,f239,f540])).

fof(f492,plain,
    ( spl13_74
  <=> l1_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_74])])).

fof(f501,plain,
    ( spl13_76
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_76])])).

fof(f898,plain,
    ( r1_tsep_1(sK2,sK1)
    | ~ spl13_2
    | ~ spl13_74
    | ~ spl13_76 ),
    inference(subsumption_resolution,[],[f897,f502])).

fof(f502,plain,
    ( l1_struct_0(sK1)
    | ~ spl13_76 ),
    inference(avatar_component_clause,[],[f501])).

fof(f897,plain,
    ( r1_tsep_1(sK2,sK1)
    | ~ l1_struct_0(sK1)
    | ~ spl13_2
    | ~ spl13_74 ),
    inference(subsumption_resolution,[],[f896,f493])).

fof(f493,plain,
    ( l1_struct_0(sK2)
    | ~ spl13_74 ),
    inference(avatar_component_clause,[],[f492])).

fof(f896,plain,
    ( r1_tsep_1(sK2,sK1)
    | ~ l1_struct_0(sK2)
    | ~ l1_struct_0(sK1)
    | ~ spl13_2 ),
    inference(resolution,[],[f240,f207])).

fof(f207,plain,(
    ! [X0,X1] :
      ( ~ r1_tsep_1(X0,X1)
      | r1_tsep_1(X1,X0)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1] :
      ( ( l1_struct_0(X1)
        & l1_struct_0(X0) )
     => ( r1_tsep_1(X0,X1)
       => r1_tsep_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t150_tmap_1.p',symmetry_r1_tsep_1)).

fof(f879,plain,
    ( spl13_2
    | ~ spl13_0
    | ~ spl13_42
    | spl13_45
    | ~ spl13_46
    | spl13_49
    | ~ spl13_50
    | ~ spl13_52
    | spl13_55 ),
    inference(avatar_split_clause,[],[f878,f409,f402,f395,f388,f381,f374,f367,f233,f239])).

fof(f878,plain,
    ( r1_tsep_1(sK1,sK2)
    | ~ spl13_0
    | ~ spl13_42
    | ~ spl13_45
    | ~ spl13_46
    | ~ spl13_49
    | ~ spl13_50
    | ~ spl13_52
    | ~ spl13_55 ),
    inference(subsumption_resolution,[],[f877,f410])).

fof(f877,plain,
    ( r1_tsep_1(sK1,sK2)
    | v2_struct_0(sK0)
    | ~ spl13_0
    | ~ spl13_42
    | ~ spl13_45
    | ~ spl13_46
    | ~ spl13_49
    | ~ spl13_50
    | ~ spl13_52 ),
    inference(subsumption_resolution,[],[f876,f403])).

fof(f876,plain,
    ( r1_tsep_1(sK1,sK2)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_0
    | ~ spl13_42
    | ~ spl13_45
    | ~ spl13_46
    | ~ spl13_49
    | ~ spl13_50 ),
    inference(subsumption_resolution,[],[f875,f396])).

fof(f875,plain,
    ( r1_tsep_1(sK1,sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_0
    | ~ spl13_42
    | ~ spl13_45
    | ~ spl13_46
    | ~ spl13_49 ),
    inference(subsumption_resolution,[],[f874,f389])).

fof(f874,plain,
    ( r1_tsep_1(sK1,sK2)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_0
    | ~ spl13_42
    | ~ spl13_45
    | ~ spl13_46 ),
    inference(subsumption_resolution,[],[f873,f382])).

fof(f873,plain,
    ( r1_tsep_1(sK1,sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_0
    | ~ spl13_42
    | ~ spl13_45 ),
    inference(subsumption_resolution,[],[f872,f375])).

fof(f872,plain,
    ( r1_tsep_1(sK1,sK2)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_0
    | ~ spl13_42 ),
    inference(subsumption_resolution,[],[f850,f368])).

fof(f850,plain,
    ( r1_tsep_1(sK1,sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_0 ),
    inference(resolution,[],[f234,f164])).

fof(f164,plain,(
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
    inference(cnf_transformation,[],[f119])).

fof(f503,plain,
    ( spl13_76
    | ~ spl13_72 ),
    inference(avatar_split_clause,[],[f496,f483,f501])).

fof(f483,plain,
    ( spl13_72
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_72])])).

fof(f496,plain,
    ( l1_struct_0(sK1)
    | ~ spl13_72 ),
    inference(resolution,[],[f484,f229])).

fof(f229,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f103])).

fof(f103,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t150_tmap_1.p',dt_l1_pre_topc)).

fof(f484,plain,
    ( l1_pre_topc(sK1)
    | ~ spl13_72 ),
    inference(avatar_component_clause,[],[f483])).

fof(f494,plain,
    ( spl13_74
    | ~ spl13_70 ),
    inference(avatar_split_clause,[],[f487,f475,f492])).

fof(f475,plain,
    ( spl13_70
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_70])])).

fof(f487,plain,
    ( l1_struct_0(sK2)
    | ~ spl13_70 ),
    inference(resolution,[],[f476,f229])).

fof(f476,plain,
    ( l1_pre_topc(sK2)
    | ~ spl13_70 ),
    inference(avatar_component_clause,[],[f475])).

fof(f485,plain,
    ( spl13_72
    | ~ spl13_46
    | ~ spl13_50 ),
    inference(avatar_split_clause,[],[f478,f395,f381,f483])).

fof(f478,plain,
    ( l1_pre_topc(sK1)
    | ~ spl13_46
    | ~ spl13_50 ),
    inference(subsumption_resolution,[],[f467,f396])).

fof(f467,plain,
    ( l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl13_46 ),
    inference(resolution,[],[f216,f382])).

fof(f216,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f96])).

fof(f96,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t150_tmap_1.p',dt_m1_pre_topc)).

fof(f477,plain,
    ( spl13_70
    | ~ spl13_42
    | ~ spl13_50 ),
    inference(avatar_split_clause,[],[f470,f395,f367,f475])).

fof(f470,plain,
    ( l1_pre_topc(sK2)
    | ~ spl13_42
    | ~ spl13_50 ),
    inference(subsumption_resolution,[],[f466,f396])).

fof(f466,plain,
    ( l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ spl13_42 ),
    inference(resolution,[],[f216,f368])).

fof(f411,plain,(
    ~ spl13_55 ),
    inference(avatar_split_clause,[],[f133,f409])).

fof(f133,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f113])).

fof(f113,plain,
    ( ( ( ( ~ m1_subset_1(k10_tmap_1(sK0,sK3,sK1,sK2,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK3))))
          | ~ v5_pre_topc(k10_tmap_1(sK0,sK3,sK1,sK2,sK4,sK5),k1_tsep_1(sK0,sK1,sK2),sK3)
          | ~ v1_funct_2(k10_tmap_1(sK0,sK3,sK1,sK2,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK3))
          | ~ v1_funct_1(k10_tmap_1(sK0,sK3,sK1,sK2,sK4,sK5)) )
        & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
        & v5_pre_topc(sK5,sK2,sK3)
        & v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3))
        & v1_funct_1(sK5)
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK3))))
        & v5_pre_topc(sK4,sK1,sK3)
        & v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK3))
        & v1_funct_1(sK4)
        & l1_pre_topc(sK3)
        & v2_pre_topc(sK3)
        & ~ v2_struct_0(sK3) )
      | ~ r1_tsep_1(sK1,sK2)
      | ~ r3_tsep_1(sK0,sK1,sK2) )
    & ( ( ! [X6] :
            ( ! [X7] :
                ( ! [X8] :
                    ( ( m1_subset_1(k10_tmap_1(sK0,X6,sK1,sK2,X7,X8),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(X6))))
                      & v5_pre_topc(k10_tmap_1(sK0,X6,sK1,sK2,X7,X8),k1_tsep_1(sK0,sK1,sK2),X6)
                      & v1_funct_2(k10_tmap_1(sK0,X6,sK1,sK2,X7,X8),u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(X6))
                      & v1_funct_1(k10_tmap_1(sK0,X6,sK1,sK2,X7,X8)) )
                    | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X6))))
                    | ~ v5_pre_topc(X8,sK2,X6)
                    | ~ v1_funct_2(X8,u1_struct_0(sK2),u1_struct_0(X6))
                    | ~ v1_funct_1(X8) )
                | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X6))))
                | ~ v5_pre_topc(X7,sK1,X6)
                | ~ v1_funct_2(X7,u1_struct_0(sK1),u1_struct_0(X6))
                | ~ v1_funct_1(X7) )
            | ~ l1_pre_topc(X6)
            | ~ v2_pre_topc(X6)
            | v2_struct_0(X6) )
        & r1_tsep_1(sK1,sK2) )
      | r3_tsep_1(sK0,sK1,sK2) )
    & m1_pre_topc(sK2,sK0)
    & ~ v2_struct_0(sK2)
    & m1_pre_topc(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f106,f112,f111,f110,f109,f108,f107])).

fof(f107,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ? [X3] :
                      ( ? [X4] :
                          ( ? [X5] :
                              ( ( ~ m1_subset_1(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                                | ~ v5_pre_topc(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_tsep_1(X0,X1,X2),X3)
                                | ~ v1_funct_2(k10_tmap_1(X0,X3,X1,X2,X4,X5),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                                | ~ v1_funct_1(k10_tmap_1(X0,X3,X1,X2,X4,X5)) )
                              & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                              & v5_pre_topc(X5,X2,X3)
                              & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3))
                              & v1_funct_1(X5) )
                          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                          & v5_pre_topc(X4,X1,X3)
                          & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X3))
                          & v1_funct_1(X4) )
                      & l1_pre_topc(X3)
                      & v2_pre_topc(X3)
                      & ~ v2_struct_0(X3) )
                  | ~ r1_tsep_1(X1,X2)
                  | ~ r3_tsep_1(X0,X1,X2) )
                & ( ( ! [X6] :
                        ( ! [X7] :
                            ( ! [X8] :
                                ( ( m1_subset_1(k10_tmap_1(X0,X6,X1,X2,X7,X8),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X6))))
                                  & v5_pre_topc(k10_tmap_1(X0,X6,X1,X2,X7,X8),k1_tsep_1(X0,X1,X2),X6)
                                  & v1_funct_2(k10_tmap_1(X0,X6,X1,X2,X7,X8),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X6))
                                  & v1_funct_1(k10_tmap_1(X0,X6,X1,X2,X7,X8)) )
                                | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X6))))
                                | ~ v5_pre_topc(X8,X2,X6)
                                | ~ v1_funct_2(X8,u1_struct_0(X2),u1_struct_0(X6))
                                | ~ v1_funct_1(X8) )
                            | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X6))))
                            | ~ v5_pre_topc(X7,X1,X6)
                            | ~ v1_funct_2(X7,u1_struct_0(X1),u1_struct_0(X6))
                            | ~ v1_funct_1(X7) )
                        | ~ l1_pre_topc(X6)
                        | ~ v2_pre_topc(X6)
                        | v2_struct_0(X6) )
                    & r1_tsep_1(X1,X2) )
                  | r3_tsep_1(X0,X1,X2) )
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
                        ( ? [X5] :
                            ( ( ~ m1_subset_1(k10_tmap_1(sK0,X3,X1,X2,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,X1,X2)),u1_struct_0(X3))))
                              | ~ v5_pre_topc(k10_tmap_1(sK0,X3,X1,X2,X4,X5),k1_tsep_1(sK0,X1,X2),X3)
                              | ~ v1_funct_2(k10_tmap_1(sK0,X3,X1,X2,X4,X5),u1_struct_0(k1_tsep_1(sK0,X1,X2)),u1_struct_0(X3))
                              | ~ v1_funct_1(k10_tmap_1(sK0,X3,X1,X2,X4,X5)) )
                            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                            & v5_pre_topc(X5,X2,X3)
                            & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3))
                            & v1_funct_1(X5) )
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                        & v5_pre_topc(X4,X1,X3)
                        & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X3))
                        & v1_funct_1(X4) )
                    & l1_pre_topc(X3)
                    & v2_pre_topc(X3)
                    & ~ v2_struct_0(X3) )
                | ~ r1_tsep_1(X1,X2)
                | ~ r3_tsep_1(sK0,X1,X2) )
              & ( ( ! [X6] :
                      ( ! [X7] :
                          ( ! [X8] :
                              ( ( m1_subset_1(k10_tmap_1(sK0,X6,X1,X2,X7,X8),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,X1,X2)),u1_struct_0(X6))))
                                & v5_pre_topc(k10_tmap_1(sK0,X6,X1,X2,X7,X8),k1_tsep_1(sK0,X1,X2),X6)
                                & v1_funct_2(k10_tmap_1(sK0,X6,X1,X2,X7,X8),u1_struct_0(k1_tsep_1(sK0,X1,X2)),u1_struct_0(X6))
                                & v1_funct_1(k10_tmap_1(sK0,X6,X1,X2,X7,X8)) )
                              | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X6))))
                              | ~ v5_pre_topc(X8,X2,X6)
                              | ~ v1_funct_2(X8,u1_struct_0(X2),u1_struct_0(X6))
                              | ~ v1_funct_1(X8) )
                          | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X6))))
                          | ~ v5_pre_topc(X7,X1,X6)
                          | ~ v1_funct_2(X7,u1_struct_0(X1),u1_struct_0(X6))
                          | ~ v1_funct_1(X7) )
                      | ~ l1_pre_topc(X6)
                      | ~ v2_pre_topc(X6)
                      | v2_struct_0(X6) )
                  & r1_tsep_1(X1,X2) )
                | r3_tsep_1(sK0,X1,X2) )
              & m1_pre_topc(X2,sK0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,sK0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f108,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ( ~ m1_subset_1(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                              | ~ v5_pre_topc(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_tsep_1(X0,X1,X2),X3)
                              | ~ v1_funct_2(k10_tmap_1(X0,X3,X1,X2,X4,X5),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                              | ~ v1_funct_1(k10_tmap_1(X0,X3,X1,X2,X4,X5)) )
                            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                            & v5_pre_topc(X5,X2,X3)
                            & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3))
                            & v1_funct_1(X5) )
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                        & v5_pre_topc(X4,X1,X3)
                        & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X3))
                        & v1_funct_1(X4) )
                    & l1_pre_topc(X3)
                    & v2_pre_topc(X3)
                    & ~ v2_struct_0(X3) )
                | ~ r1_tsep_1(X1,X2)
                | ~ r3_tsep_1(X0,X1,X2) )
              & ( ( ! [X6] :
                      ( ! [X7] :
                          ( ! [X8] :
                              ( ( m1_subset_1(k10_tmap_1(X0,X6,X1,X2,X7,X8),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X6))))
                                & v5_pre_topc(k10_tmap_1(X0,X6,X1,X2,X7,X8),k1_tsep_1(X0,X1,X2),X6)
                                & v1_funct_2(k10_tmap_1(X0,X6,X1,X2,X7,X8),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X6))
                                & v1_funct_1(k10_tmap_1(X0,X6,X1,X2,X7,X8)) )
                              | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X6))))
                              | ~ v5_pre_topc(X8,X2,X6)
                              | ~ v1_funct_2(X8,u1_struct_0(X2),u1_struct_0(X6))
                              | ~ v1_funct_1(X8) )
                          | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X6))))
                          | ~ v5_pre_topc(X7,X1,X6)
                          | ~ v1_funct_2(X7,u1_struct_0(X1),u1_struct_0(X6))
                          | ~ v1_funct_1(X7) )
                      | ~ l1_pre_topc(X6)
                      | ~ v2_pre_topc(X6)
                      | v2_struct_0(X6) )
                  & r1_tsep_1(X1,X2) )
                | r3_tsep_1(X0,X1,X2) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ~ m1_subset_1(k10_tmap_1(X0,X3,sK1,X2,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,sK1,X2)),u1_struct_0(X3))))
                            | ~ v5_pre_topc(k10_tmap_1(X0,X3,sK1,X2,X4,X5),k1_tsep_1(X0,sK1,X2),X3)
                            | ~ v1_funct_2(k10_tmap_1(X0,X3,sK1,X2,X4,X5),u1_struct_0(k1_tsep_1(X0,sK1,X2)),u1_struct_0(X3))
                            | ~ v1_funct_1(k10_tmap_1(X0,X3,sK1,X2,X4,X5)) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                          & v5_pre_topc(X5,X2,X3)
                          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X3))))
                      & v5_pre_topc(X4,sK1,X3)
                      & v1_funct_2(X4,u1_struct_0(sK1),u1_struct_0(X3))
                      & v1_funct_1(X4) )
                  & l1_pre_topc(X3)
                  & v2_pre_topc(X3)
                  & ~ v2_struct_0(X3) )
              | ~ r1_tsep_1(sK1,X2)
              | ~ r3_tsep_1(X0,sK1,X2) )
            & ( ( ! [X6] :
                    ( ! [X7] :
                        ( ! [X8] :
                            ( ( m1_subset_1(k10_tmap_1(X0,X6,sK1,X2,X7,X8),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,sK1,X2)),u1_struct_0(X6))))
                              & v5_pre_topc(k10_tmap_1(X0,X6,sK1,X2,X7,X8),k1_tsep_1(X0,sK1,X2),X6)
                              & v1_funct_2(k10_tmap_1(X0,X6,sK1,X2,X7,X8),u1_struct_0(k1_tsep_1(X0,sK1,X2)),u1_struct_0(X6))
                              & v1_funct_1(k10_tmap_1(X0,X6,sK1,X2,X7,X8)) )
                            | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X6))))
                            | ~ v5_pre_topc(X8,X2,X6)
                            | ~ v1_funct_2(X8,u1_struct_0(X2),u1_struct_0(X6))
                            | ~ v1_funct_1(X8) )
                        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X6))))
                        | ~ v5_pre_topc(X7,sK1,X6)
                        | ~ v1_funct_2(X7,u1_struct_0(sK1),u1_struct_0(X6))
                        | ~ v1_funct_1(X7) )
                    | ~ l1_pre_topc(X6)
                    | ~ v2_pre_topc(X6)
                    | v2_struct_0(X6) )
                & r1_tsep_1(sK1,X2) )
              | r3_tsep_1(X0,sK1,X2) )
            & m1_pre_topc(X2,X0)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(sK1,X0)
        & ~ v2_struct_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f109,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ( ~ m1_subset_1(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                          | ~ v5_pre_topc(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_tsep_1(X0,X1,X2),X3)
                          | ~ v1_funct_2(k10_tmap_1(X0,X3,X1,X2,X4,X5),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                          | ~ v1_funct_1(k10_tmap_1(X0,X3,X1,X2,X4,X5)) )
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                        & v5_pre_topc(X5,X2,X3)
                        & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3))
                        & v1_funct_1(X5) )
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                    & v5_pre_topc(X4,X1,X3)
                    & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X3))
                    & v1_funct_1(X4) )
                & l1_pre_topc(X3)
                & v2_pre_topc(X3)
                & ~ v2_struct_0(X3) )
            | ~ r1_tsep_1(X1,X2)
            | ~ r3_tsep_1(X0,X1,X2) )
          & ( ( ! [X6] :
                  ( ! [X7] :
                      ( ! [X8] :
                          ( ( m1_subset_1(k10_tmap_1(X0,X6,X1,X2,X7,X8),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X6))))
                            & v5_pre_topc(k10_tmap_1(X0,X6,X1,X2,X7,X8),k1_tsep_1(X0,X1,X2),X6)
                            & v1_funct_2(k10_tmap_1(X0,X6,X1,X2,X7,X8),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X6))
                            & v1_funct_1(k10_tmap_1(X0,X6,X1,X2,X7,X8)) )
                          | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X6))))
                          | ~ v5_pre_topc(X8,X2,X6)
                          | ~ v1_funct_2(X8,u1_struct_0(X2),u1_struct_0(X6))
                          | ~ v1_funct_1(X8) )
                      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X6))))
                      | ~ v5_pre_topc(X7,X1,X6)
                      | ~ v1_funct_2(X7,u1_struct_0(X1),u1_struct_0(X6))
                      | ~ v1_funct_1(X7) )
                  | ~ l1_pre_topc(X6)
                  | ~ v2_pre_topc(X6)
                  | v2_struct_0(X6) )
              & r1_tsep_1(X1,X2) )
            | r3_tsep_1(X0,X1,X2) )
          & m1_pre_topc(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ( ~ m1_subset_1(k10_tmap_1(X0,X3,X1,sK2,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,sK2)),u1_struct_0(X3))))
                        | ~ v5_pre_topc(k10_tmap_1(X0,X3,X1,sK2,X4,X5),k1_tsep_1(X0,X1,sK2),X3)
                        | ~ v1_funct_2(k10_tmap_1(X0,X3,X1,sK2,X4,X5),u1_struct_0(k1_tsep_1(X0,X1,sK2)),u1_struct_0(X3))
                        | ~ v1_funct_1(k10_tmap_1(X0,X3,X1,sK2,X4,X5)) )
                      & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X3))))
                      & v5_pre_topc(X5,sK2,X3)
                      & v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(X3))
                      & v1_funct_1(X5) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                  & v5_pre_topc(X4,X1,X3)
                  & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X3))
                  & v1_funct_1(X4) )
              & l1_pre_topc(X3)
              & v2_pre_topc(X3)
              & ~ v2_struct_0(X3) )
          | ~ r1_tsep_1(X1,sK2)
          | ~ r3_tsep_1(X0,X1,sK2) )
        & ( ( ! [X6] :
                ( ! [X7] :
                    ( ! [X8] :
                        ( ( m1_subset_1(k10_tmap_1(X0,X6,X1,sK2,X7,X8),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,sK2)),u1_struct_0(X6))))
                          & v5_pre_topc(k10_tmap_1(X0,X6,X1,sK2,X7,X8),k1_tsep_1(X0,X1,sK2),X6)
                          & v1_funct_2(k10_tmap_1(X0,X6,X1,sK2,X7,X8),u1_struct_0(k1_tsep_1(X0,X1,sK2)),u1_struct_0(X6))
                          & v1_funct_1(k10_tmap_1(X0,X6,X1,sK2,X7,X8)) )
                        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X6))))
                        | ~ v5_pre_topc(X8,sK2,X6)
                        | ~ v1_funct_2(X8,u1_struct_0(sK2),u1_struct_0(X6))
                        | ~ v1_funct_1(X8) )
                    | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X6))))
                    | ~ v5_pre_topc(X7,X1,X6)
                    | ~ v1_funct_2(X7,u1_struct_0(X1),u1_struct_0(X6))
                    | ~ v1_funct_1(X7) )
                | ~ l1_pre_topc(X6)
                | ~ v2_pre_topc(X6)
                | v2_struct_0(X6) )
            & r1_tsep_1(X1,sK2) )
          | r3_tsep_1(X0,X1,sK2) )
        & m1_pre_topc(sK2,X0)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ( ~ m1_subset_1(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                    | ~ v5_pre_topc(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_tsep_1(X0,X1,X2),X3)
                    | ~ v1_funct_2(k10_tmap_1(X0,X3,X1,X2,X4,X5),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                    | ~ v1_funct_1(k10_tmap_1(X0,X3,X1,X2,X4,X5)) )
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                  & v5_pre_topc(X5,X2,X3)
                  & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3))
                  & v1_funct_1(X5) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
              & v5_pre_topc(X4,X1,X3)
              & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X3))
              & v1_funct_1(X4) )
          & l1_pre_topc(X3)
          & v2_pre_topc(X3)
          & ~ v2_struct_0(X3) )
     => ( ? [X4] :
            ( ? [X5] :
                ( ( ~ m1_subset_1(k10_tmap_1(X0,sK3,X1,X2,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(sK3))))
                  | ~ v5_pre_topc(k10_tmap_1(X0,sK3,X1,X2,X4,X5),k1_tsep_1(X0,X1,X2),sK3)
                  | ~ v1_funct_2(k10_tmap_1(X0,sK3,X1,X2,X4,X5),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(sK3))
                  | ~ v1_funct_1(k10_tmap_1(X0,sK3,X1,X2,X4,X5)) )
                & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK3))))
                & v5_pre_topc(X5,X2,sK3)
                & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(sK3))
                & v1_funct_1(X5) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3))))
            & v5_pre_topc(X4,X1,sK3)
            & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(sK3))
            & v1_funct_1(X4) )
        & l1_pre_topc(sK3)
        & v2_pre_topc(sK3)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f111,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ? [X5] :
              ( ( ~ m1_subset_1(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                | ~ v5_pre_topc(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_tsep_1(X0,X1,X2),X3)
                | ~ v1_funct_2(k10_tmap_1(X0,X3,X1,X2,X4,X5),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                | ~ v1_funct_1(k10_tmap_1(X0,X3,X1,X2,X4,X5)) )
              & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
              & v5_pre_topc(X5,X2,X3)
              & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3))
              & v1_funct_1(X5) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
          & v5_pre_topc(X4,X1,X3)
          & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X3))
          & v1_funct_1(X4) )
     => ( ? [X5] :
            ( ( ~ m1_subset_1(k10_tmap_1(X0,X3,X1,X2,sK4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
              | ~ v5_pre_topc(k10_tmap_1(X0,X3,X1,X2,sK4,X5),k1_tsep_1(X0,X1,X2),X3)
              | ~ v1_funct_2(k10_tmap_1(X0,X3,X1,X2,sK4,X5),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
              | ~ v1_funct_1(k10_tmap_1(X0,X3,X1,X2,sK4,X5)) )
            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
            & v5_pre_topc(X5,X2,X3)
            & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3))
            & v1_funct_1(X5) )
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
        & v5_pre_topc(sK4,X1,X3)
        & v1_funct_2(sK4,u1_struct_0(X1),u1_struct_0(X3))
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f112,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( ( ~ m1_subset_1(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
            | ~ v5_pre_topc(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_tsep_1(X0,X1,X2),X3)
            | ~ v1_funct_2(k10_tmap_1(X0,X3,X1,X2,X4,X5),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
            | ~ v1_funct_1(k10_tmap_1(X0,X3,X1,X2,X4,X5)) )
          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
          & v5_pre_topc(X5,X2,X3)
          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3))
          & v1_funct_1(X5) )
     => ( ( ~ m1_subset_1(k10_tmap_1(X0,X3,X1,X2,X4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
          | ~ v5_pre_topc(k10_tmap_1(X0,X3,X1,X2,X4,sK5),k1_tsep_1(X0,X1,X2),X3)
          | ~ v1_funct_2(k10_tmap_1(X0,X3,X1,X2,X4,sK5),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
          | ~ v1_funct_1(k10_tmap_1(X0,X3,X1,X2,X4,sK5)) )
        & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
        & v5_pre_topc(sK5,X2,X3)
        & v1_funct_2(sK5,u1_struct_0(X2),u1_struct_0(X3))
        & v1_funct_1(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f106,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ( ~ m1_subset_1(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                              | ~ v5_pre_topc(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_tsep_1(X0,X1,X2),X3)
                              | ~ v1_funct_2(k10_tmap_1(X0,X3,X1,X2,X4,X5),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                              | ~ v1_funct_1(k10_tmap_1(X0,X3,X1,X2,X4,X5)) )
                            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                            & v5_pre_topc(X5,X2,X3)
                            & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3))
                            & v1_funct_1(X5) )
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                        & v5_pre_topc(X4,X1,X3)
                        & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X3))
                        & v1_funct_1(X4) )
                    & l1_pre_topc(X3)
                    & v2_pre_topc(X3)
                    & ~ v2_struct_0(X3) )
                | ~ r1_tsep_1(X1,X2)
                | ~ r3_tsep_1(X0,X1,X2) )
              & ( ( ! [X6] :
                      ( ! [X7] :
                          ( ! [X8] :
                              ( ( m1_subset_1(k10_tmap_1(X0,X6,X1,X2,X7,X8),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X6))))
                                & v5_pre_topc(k10_tmap_1(X0,X6,X1,X2,X7,X8),k1_tsep_1(X0,X1,X2),X6)
                                & v1_funct_2(k10_tmap_1(X0,X6,X1,X2,X7,X8),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X6))
                                & v1_funct_1(k10_tmap_1(X0,X6,X1,X2,X7,X8)) )
                              | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X6))))
                              | ~ v5_pre_topc(X8,X2,X6)
                              | ~ v1_funct_2(X8,u1_struct_0(X2),u1_struct_0(X6))
                              | ~ v1_funct_1(X8) )
                          | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X6))))
                          | ~ v5_pre_topc(X7,X1,X6)
                          | ~ v1_funct_2(X7,u1_struct_0(X1),u1_struct_0(X6))
                          | ~ v1_funct_1(X7) )
                      | ~ l1_pre_topc(X6)
                      | ~ v2_pre_topc(X6)
                      | v2_struct_0(X6) )
                  & r1_tsep_1(X1,X2) )
                | r3_tsep_1(X0,X1,X2) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(rectify,[],[f105])).

fof(f105,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ( ~ m1_subset_1(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                              | ~ v5_pre_topc(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_tsep_1(X0,X1,X2),X3)
                              | ~ v1_funct_2(k10_tmap_1(X0,X3,X1,X2,X4,X5),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                              | ~ v1_funct_1(k10_tmap_1(X0,X3,X1,X2,X4,X5)) )
                            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                            & v5_pre_topc(X5,X2,X3)
                            & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3))
                            & v1_funct_1(X5) )
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                        & v5_pre_topc(X4,X1,X3)
                        & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X3))
                        & v1_funct_1(X4) )
                    & l1_pre_topc(X3)
                    & v2_pre_topc(X3)
                    & ~ v2_struct_0(X3) )
                | ~ r1_tsep_1(X1,X2)
                | ~ r3_tsep_1(X0,X1,X2) )
              & ( ( ! [X3] :
                      ( ! [X4] :
                          ( ! [X5] :
                              ( ( m1_subset_1(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                                & v5_pre_topc(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_tsep_1(X0,X1,X2),X3)
                                & v1_funct_2(k10_tmap_1(X0,X3,X1,X2,X4,X5),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                                & v1_funct_1(k10_tmap_1(X0,X3,X1,X2,X4,X5)) )
                              | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                              | ~ v5_pre_topc(X5,X2,X3)
                              | ~ v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3))
                              | ~ v1_funct_1(X5) )
                          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                          | ~ v5_pre_topc(X4,X1,X3)
                          | ~ v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X3))
                          | ~ v1_funct_1(X4) )
                      | ~ l1_pre_topc(X3)
                      | ~ v2_pre_topc(X3)
                      | v2_struct_0(X3) )
                  & r1_tsep_1(X1,X2) )
                | r3_tsep_1(X0,X1,X2) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f104])).

fof(f104,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ( ~ m1_subset_1(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                              | ~ v5_pre_topc(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_tsep_1(X0,X1,X2),X3)
                              | ~ v1_funct_2(k10_tmap_1(X0,X3,X1,X2,X4,X5),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                              | ~ v1_funct_1(k10_tmap_1(X0,X3,X1,X2,X4,X5)) )
                            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                            & v5_pre_topc(X5,X2,X3)
                            & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3))
                            & v1_funct_1(X5) )
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                        & v5_pre_topc(X4,X1,X3)
                        & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X3))
                        & v1_funct_1(X4) )
                    & l1_pre_topc(X3)
                    & v2_pre_topc(X3)
                    & ~ v2_struct_0(X3) )
                | ~ r1_tsep_1(X1,X2)
                | ~ r3_tsep_1(X0,X1,X2) )
              & ( ( ! [X3] :
                      ( ! [X4] :
                          ( ! [X5] :
                              ( ( m1_subset_1(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                                & v5_pre_topc(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_tsep_1(X0,X1,X2),X3)
                                & v1_funct_2(k10_tmap_1(X0,X3,X1,X2,X4,X5),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                                & v1_funct_1(k10_tmap_1(X0,X3,X1,X2,X4,X5)) )
                              | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                              | ~ v5_pre_topc(X5,X2,X3)
                              | ~ v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3))
                              | ~ v1_funct_1(X5) )
                          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                          | ~ v5_pre_topc(X4,X1,X3)
                          | ~ v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X3))
                          | ~ v1_funct_1(X4) )
                      | ~ l1_pre_topc(X3)
                      | ~ v2_pre_topc(X3)
                      | v2_struct_0(X3) )
                  & r1_tsep_1(X1,X2) )
                | r3_tsep_1(X0,X1,X2) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f51])).

fof(f51,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r3_tsep_1(X0,X1,X2)
              <~> ( ! [X3] :
                      ( ! [X4] :
                          ( ! [X5] :
                              ( ( m1_subset_1(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                                & v5_pre_topc(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_tsep_1(X0,X1,X2),X3)
                                & v1_funct_2(k10_tmap_1(X0,X3,X1,X2,X4,X5),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                                & v1_funct_1(k10_tmap_1(X0,X3,X1,X2,X4,X5)) )
                              | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                              | ~ v5_pre_topc(X5,X2,X3)
                              | ~ v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3))
                              | ~ v1_funct_1(X5) )
                          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                          | ~ v5_pre_topc(X4,X1,X3)
                          | ~ v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X3))
                          | ~ v1_funct_1(X4) )
                      | ~ l1_pre_topc(X3)
                      | ~ v2_pre_topc(X3)
                      | v2_struct_0(X3) )
                  & r1_tsep_1(X1,X2) ) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r3_tsep_1(X0,X1,X2)
              <~> ( ! [X3] :
                      ( ! [X4] :
                          ( ! [X5] :
                              ( ( m1_subset_1(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                                & v5_pre_topc(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_tsep_1(X0,X1,X2),X3)
                                & v1_funct_2(k10_tmap_1(X0,X3,X1,X2,X4,X5),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                                & v1_funct_1(k10_tmap_1(X0,X3,X1,X2,X4,X5)) )
                              | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                              | ~ v5_pre_topc(X5,X2,X3)
                              | ~ v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3))
                              | ~ v1_funct_1(X5) )
                          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                          | ~ v5_pre_topc(X4,X1,X3)
                          | ~ v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X3))
                          | ~ v1_funct_1(X4) )
                      | ~ l1_pre_topc(X3)
                      | ~ v2_pre_topc(X3)
                      | v2_struct_0(X3) )
                  & r1_tsep_1(X1,X2) ) )
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
               => ( r3_tsep_1(X0,X1,X2)
                <=> ( ! [X3] :
                        ( ( l1_pre_topc(X3)
                          & v2_pre_topc(X3)
                          & ~ v2_struct_0(X3) )
                       => ! [X4] :
                            ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                              & v5_pre_topc(X4,X1,X3)
                              & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X3))
                              & v1_funct_1(X4) )
                           => ! [X5] :
                                ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                                  & v5_pre_topc(X5,X2,X3)
                                  & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3))
                                  & v1_funct_1(X5) )
                               => ( m1_subset_1(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                                  & v5_pre_topc(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_tsep_1(X0,X1,X2),X3)
                                  & v1_funct_2(k10_tmap_1(X0,X3,X1,X2,X4,X5),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                                  & v1_funct_1(k10_tmap_1(X0,X3,X1,X2,X4,X5)) ) ) ) )
                    & r1_tsep_1(X1,X2) ) ) ) ) ) ),
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
             => ( r3_tsep_1(X0,X1,X2)
              <=> ( ! [X3] :
                      ( ( l1_pre_topc(X3)
                        & v2_pre_topc(X3)
                        & ~ v2_struct_0(X3) )
                     => ! [X4] :
                          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                            & v5_pre_topc(X4,X1,X3)
                            & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X3))
                            & v1_funct_1(X4) )
                         => ! [X5] :
                              ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                                & v5_pre_topc(X5,X2,X3)
                                & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3))
                                & v1_funct_1(X5) )
                             => ( m1_subset_1(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                                & v5_pre_topc(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_tsep_1(X0,X1,X2),X3)
                                & v1_funct_2(k10_tmap_1(X0,X3,X1,X2,X4,X5),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                                & v1_funct_1(k10_tmap_1(X0,X3,X1,X2,X4,X5)) ) ) ) )
                  & r1_tsep_1(X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t150_tmap_1.p',t150_tmap_1)).

fof(f404,plain,(
    spl13_52 ),
    inference(avatar_split_clause,[],[f134,f402])).

fof(f134,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f113])).

fof(f397,plain,(
    spl13_50 ),
    inference(avatar_split_clause,[],[f135,f395])).

fof(f135,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f113])).

fof(f390,plain,(
    ~ spl13_49 ),
    inference(avatar_split_clause,[],[f136,f388])).

fof(f136,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f113])).

fof(f383,plain,(
    spl13_46 ),
    inference(avatar_split_clause,[],[f137,f381])).

fof(f137,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f113])).

fof(f376,plain,(
    ~ spl13_45 ),
    inference(avatar_split_clause,[],[f138,f374])).

fof(f138,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f113])).

fof(f369,plain,(
    spl13_42 ),
    inference(avatar_split_clause,[],[f139,f367])).

fof(f139,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f113])).

fof(f362,plain,
    ( spl13_0
    | spl13_2 ),
    inference(avatar_split_clause,[],[f140,f239,f233])).

fof(f140,plain,
    ( r1_tsep_1(sK1,sK2)
    | r3_tsep_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f113])).

fof(f353,plain,
    ( spl13_0
    | spl13_36 ),
    inference(avatar_split_clause,[],[f143,f351,f233])).

fof(f143,plain,(
    ! [X6,X8,X7] :
      ( v5_pre_topc(k10_tmap_1(sK0,X6,sK1,sK2,X7,X8),k1_tsep_1(sK0,sK1,sK2),X6)
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X6))))
      | ~ v5_pre_topc(X8,sK2,X6)
      | ~ v1_funct_2(X8,u1_struct_0(sK2),u1_struct_0(X6))
      | ~ v1_funct_1(X8)
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X6))))
      | ~ v5_pre_topc(X7,sK1,X6)
      | ~ v1_funct_2(X7,u1_struct_0(sK1),u1_struct_0(X6))
      | ~ v1_funct_1(X7)
      | ~ l1_pre_topc(X6)
      | ~ v2_pre_topc(X6)
      | v2_struct_0(X6)
      | r3_tsep_1(sK0,sK1,sK2) ) ),
    inference(cnf_transformation,[],[f113])).

fof(f345,plain,
    ( ~ spl13_1
    | ~ spl13_3
    | ~ spl13_33 ),
    inference(avatar_split_clause,[],[f145,f343,f242,f236])).

fof(f236,plain,
    ( spl13_1
  <=> ~ r3_tsep_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1])])).

fof(f242,plain,
    ( spl13_3
  <=> ~ r1_tsep_1(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_3])])).

fof(f145,plain,
    ( ~ v2_struct_0(sK3)
    | ~ r1_tsep_1(sK1,sK2)
    | ~ r3_tsep_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f113])).

fof(f338,plain,
    ( ~ spl13_1
    | ~ spl13_3
    | spl13_30 ),
    inference(avatar_split_clause,[],[f146,f336,f242,f236])).

fof(f146,plain,
    ( v2_pre_topc(sK3)
    | ~ r1_tsep_1(sK1,sK2)
    | ~ r3_tsep_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f113])).

fof(f331,plain,
    ( ~ spl13_1
    | ~ spl13_3
    | spl13_28 ),
    inference(avatar_split_clause,[],[f147,f329,f242,f236])).

fof(f147,plain,
    ( l1_pre_topc(sK3)
    | ~ r1_tsep_1(sK1,sK2)
    | ~ r3_tsep_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f113])).

fof(f324,plain,
    ( ~ spl13_1
    | ~ spl13_3
    | spl13_26 ),
    inference(avatar_split_clause,[],[f148,f322,f242,f236])).

fof(f148,plain,
    ( v1_funct_1(sK4)
    | ~ r1_tsep_1(sK1,sK2)
    | ~ r3_tsep_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f113])).

fof(f317,plain,
    ( ~ spl13_1
    | ~ spl13_3
    | spl13_24 ),
    inference(avatar_split_clause,[],[f149,f315,f242,f236])).

fof(f149,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK3))
    | ~ r1_tsep_1(sK1,sK2)
    | ~ r3_tsep_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f113])).

fof(f310,plain,
    ( ~ spl13_1
    | ~ spl13_3
    | spl13_22 ),
    inference(avatar_split_clause,[],[f150,f308,f242,f236])).

fof(f150,plain,
    ( v5_pre_topc(sK4,sK1,sK3)
    | ~ r1_tsep_1(sK1,sK2)
    | ~ r3_tsep_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f113])).

fof(f303,plain,
    ( ~ spl13_1
    | ~ spl13_3
    | spl13_20 ),
    inference(avatar_split_clause,[],[f151,f301,f242,f236])).

fof(f151,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK3))))
    | ~ r1_tsep_1(sK1,sK2)
    | ~ r3_tsep_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f113])).

fof(f296,plain,
    ( ~ spl13_1
    | ~ spl13_3
    | spl13_18 ),
    inference(avatar_split_clause,[],[f152,f294,f242,f236])).

fof(f152,plain,
    ( v1_funct_1(sK5)
    | ~ r1_tsep_1(sK1,sK2)
    | ~ r3_tsep_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f113])).

fof(f289,plain,
    ( ~ spl13_1
    | ~ spl13_3
    | spl13_16 ),
    inference(avatar_split_clause,[],[f153,f287,f242,f236])).

fof(f153,plain,
    ( v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ r1_tsep_1(sK1,sK2)
    | ~ r3_tsep_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f113])).

fof(f282,plain,
    ( ~ spl13_1
    | ~ spl13_3
    | spl13_14 ),
    inference(avatar_split_clause,[],[f154,f280,f242,f236])).

fof(f154,plain,
    ( v5_pre_topc(sK5,sK2,sK3)
    | ~ r1_tsep_1(sK1,sK2)
    | ~ r3_tsep_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f113])).

fof(f275,plain,
    ( ~ spl13_1
    | ~ spl13_3
    | spl13_12 ),
    inference(avatar_split_clause,[],[f155,f273,f242,f236])).

fof(f155,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ r1_tsep_1(sK1,sK2)
    | ~ r3_tsep_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f113])).

fof(f268,plain,
    ( ~ spl13_1
    | ~ spl13_3
    | ~ spl13_5
    | ~ spl13_7
    | ~ spl13_9
    | ~ spl13_11 ),
    inference(avatar_split_clause,[],[f156,f266,f260,f254,f248,f242,f236])).

fof(f156,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK0,sK3,sK1,sK2,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK3))))
    | ~ v5_pre_topc(k10_tmap_1(sK0,sK3,sK1,sK2,sK4,sK5),k1_tsep_1(sK0,sK1,sK2),sK3)
    | ~ v1_funct_2(k10_tmap_1(sK0,sK3,sK1,sK2,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK3))
    | ~ v1_funct_1(k10_tmap_1(sK0,sK3,sK1,sK2,sK4,sK5))
    | ~ r1_tsep_1(sK1,sK2)
    | ~ r3_tsep_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f113])).
%------------------------------------------------------------------------------
