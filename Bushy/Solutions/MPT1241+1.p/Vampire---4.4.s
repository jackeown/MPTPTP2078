%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tops_1__t55_tops_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:30 EDT 2019

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  242 ( 598 expanded)
%              Number of leaves         :   71 ( 277 expanded)
%              Depth                    :    9
%              Number of atoms          :  698 (2127 expanded)
%              Number of equality atoms :   92 ( 344 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f735,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f115,f122,f129,f136,f143,f150,f157,f169,f185,f194,f201,f213,f234,f236,f243,f269,f289,f298,f305,f342,f352,f389,f414,f437,f447,f467,f474,f481,f488,f517,f524,f538,f552,f561,f568,f598,f605,f653,f660,f667,f677,f684,f691,f720])).

fof(f720,plain,
    ( ~ spl6_4
    | ~ spl6_12
    | spl6_23
    | ~ spl6_36
    | ~ spl6_64
    | ~ spl6_78 ),
    inference(avatar_contradiction_clause,[],[f719])).

fof(f719,plain,
    ( $false
    | ~ spl6_4
    | ~ spl6_12
    | ~ spl6_23
    | ~ spl6_36
    | ~ spl6_64
    | ~ spl6_78 ),
    inference(subsumption_resolution,[],[f718,f200])).

fof(f200,plain,
    ( k1_tops_1(sK1,sK3) != sK3
    | ~ spl6_23 ),
    inference(avatar_component_clause,[],[f199])).

fof(f199,plain,
    ( spl6_23
  <=> k1_tops_1(sK1,sK3) != sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f718,plain,
    ( k1_tops_1(sK1,sK3) = sK3
    | ~ spl6_4
    | ~ spl6_12
    | ~ spl6_36
    | ~ spl6_64
    | ~ spl6_78 ),
    inference(forward_demodulation,[],[f717,f659])).

fof(f659,plain,
    ( k3_subset_1(u1_struct_0(sK1),k3_subset_1(u1_struct_0(sK1),sK3)) = sK3
    | ~ spl6_78 ),
    inference(avatar_component_clause,[],[f658])).

fof(f658,plain,
    ( spl6_78
  <=> k3_subset_1(u1_struct_0(sK1),k3_subset_1(u1_struct_0(sK1),sK3)) = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_78])])).

fof(f717,plain,
    ( k1_tops_1(sK1,sK3) = k3_subset_1(u1_struct_0(sK1),k3_subset_1(u1_struct_0(sK1),sK3))
    | ~ spl6_4
    | ~ spl6_12
    | ~ spl6_36
    | ~ spl6_64 ),
    inference(forward_demodulation,[],[f710,f539])).

fof(f539,plain,
    ( k3_subset_1(u1_struct_0(sK1),sK3) = k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK3))
    | ~ spl6_4
    | ~ spl6_36
    | ~ spl6_64 ),
    inference(unit_resulting_resolution,[],[f128,f304,f537,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ~ v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t55_tops_1.p',t52_pre_topc)).

fof(f537,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(sK1),sK3),sK1)
    | ~ spl6_64 ),
    inference(avatar_component_clause,[],[f536])).

fof(f536,plain,
    ( spl6_64
  <=> v4_pre_topc(k3_subset_1(u1_struct_0(sK1),sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_64])])).

fof(f304,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK1),sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl6_36 ),
    inference(avatar_component_clause,[],[f303])).

fof(f303,plain,
    ( spl6_36
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK1),sK3),k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).

fof(f128,plain,
    ( l1_pre_topc(sK1)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl6_4
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f710,plain,
    ( k1_tops_1(sK1,sK3) = k3_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK3)))
    | ~ spl6_4
    | ~ spl6_12 ),
    inference(unit_resulting_resolution,[],[f128,f156,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t55_tops_1.p',d1_tops_1)).

fof(f156,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f155])).

fof(f155,plain,
    ( spl6_12
  <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f691,plain,
    ( spl6_86
    | ~ spl6_4
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f620,f155,f127,f689])).

fof(f689,plain,
    ( spl6_86
  <=> k1_tops_1(sK1,sK3) = k1_tops_1(sK1,k1_tops_1(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_86])])).

fof(f620,plain,
    ( k1_tops_1(sK1,sK3) = k1_tops_1(sK1,k1_tops_1(sK1,sK3))
    | ~ spl6_4
    | ~ spl6_12 ),
    inference(unit_resulting_resolution,[],[f128,f156,f103])).

fof(f103,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t55_tops_1.p',projectivity_k1_tops_1)).

fof(f684,plain,
    ( spl6_84
    | ~ spl6_2
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f619,f148,f120,f682])).

fof(f682,plain,
    ( spl6_84
  <=> k1_tops_1(sK0,sK2) = k1_tops_1(sK0,k1_tops_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_84])])).

fof(f120,plain,
    ( spl6_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f148,plain,
    ( spl6_10
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f619,plain,
    ( k1_tops_1(sK0,sK2) = k1_tops_1(sK0,k1_tops_1(sK0,sK2))
    | ~ spl6_2
    | ~ spl6_10 ),
    inference(unit_resulting_resolution,[],[f121,f149,f103])).

fof(f149,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f148])).

fof(f121,plain,
    ( l1_pre_topc(sK0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f120])).

fof(f677,plain,
    ( spl6_82
    | ~ spl6_4
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f579,f155,f127,f675])).

fof(f675,plain,
    ( spl6_82
  <=> k2_pre_topc(sK1,sK3) = k2_pre_topc(sK1,k2_pre_topc(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_82])])).

fof(f579,plain,
    ( k2_pre_topc(sK1,sK3) = k2_pre_topc(sK1,k2_pre_topc(sK1,sK3))
    | ~ spl6_4
    | ~ spl6_12 ),
    inference(unit_resulting_resolution,[],[f128,f156,f102])).

fof(f102,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t55_tops_1.p',projectivity_k2_pre_topc)).

fof(f667,plain,
    ( spl6_80
    | ~ spl6_2
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f578,f148,f120,f665])).

fof(f665,plain,
    ( spl6_80
  <=> k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k2_pre_topc(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_80])])).

fof(f578,plain,
    ( k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k2_pre_topc(sK0,sK2))
    | ~ spl6_2
    | ~ spl6_10 ),
    inference(unit_resulting_resolution,[],[f121,f149,f102])).

fof(f660,plain,
    ( spl6_78
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f322,f155,f658])).

fof(f322,plain,
    ( k3_subset_1(u1_struct_0(sK1),k3_subset_1(u1_struct_0(sK1),sK3)) = sK3
    | ~ spl6_12 ),
    inference(unit_resulting_resolution,[],[f156,f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t55_tops_1.p',involutiveness_k3_subset_1)).

fof(f653,plain,
    ( spl6_76
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f321,f148,f651])).

fof(f651,plain,
    ( spl6_76
  <=> k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2)) = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_76])])).

fof(f321,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2)) = sK2
    | ~ spl6_10 ),
    inference(unit_resulting_resolution,[],[f149,f98])).

fof(f605,plain,
    ( spl6_74
    | ~ spl6_2
    | ~ spl6_46
    | ~ spl6_52 ),
    inference(avatar_split_clause,[],[f525,f465,f412,f120,f603])).

fof(f603,plain,
    ( spl6_74
  <=> v4_pre_topc(k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_74])])).

fof(f412,plain,
    ( spl6_46
  <=> v3_pre_topc(k1_tops_1(sK0,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_46])])).

fof(f465,plain,
    ( spl6_52
  <=> m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_52])])).

fof(f525,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK2)),sK0)
    | ~ spl6_2
    | ~ spl6_46
    | ~ spl6_52 ),
    inference(unit_resulting_resolution,[],[f121,f413,f466,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t55_tops_1.p',t30_tops_1)).

fof(f466,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_52 ),
    inference(avatar_component_clause,[],[f465])).

fof(f413,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK2),sK0)
    | ~ spl6_46 ),
    inference(avatar_component_clause,[],[f412])).

fof(f598,plain,
    ( spl6_72
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_34 ),
    inference(avatar_split_clause,[],[f379,f296,f120,f113,f596])).

fof(f596,plain,
    ( spl6_72
  <=> v3_pre_topc(k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_72])])).

fof(f113,plain,
    ( spl6_0
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_0])])).

fof(f296,plain,
    ( spl6_34
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).

fof(f379,plain,
    ( v3_pre_topc(k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK2)),sK0)
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_34 ),
    inference(unit_resulting_resolution,[],[f114,f121,f297,f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t55_tops_1.p',fc9_tops_1)).

fof(f297,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_34 ),
    inference(avatar_component_clause,[],[f296])).

fof(f114,plain,
    ( v2_pre_topc(sK0)
    | ~ spl6_0 ),
    inference(avatar_component_clause,[],[f113])).

fof(f568,plain,
    ( spl6_70
    | ~ spl6_0
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f382,f120,f113,f566])).

fof(f566,plain,
    ( spl6_70
  <=> v3_pre_topc(k1_tops_1(sK0,sK4(k1_zfmisc_1(u1_struct_0(sK0)))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_70])])).

fof(f382,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK4(k1_zfmisc_1(u1_struct_0(sK0)))),sK0)
    | ~ spl6_0
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f114,f121,f93,f99])).

fof(f93,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f18,f71])).

fof(f71,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f18,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t55_tops_1.p',existence_m1_subset_1)).

fof(f561,plain,
    ( ~ spl6_69
    | spl6_49 ),
    inference(avatar_split_clause,[],[f439,f435,f559])).

fof(f559,plain,
    ( spl6_69
  <=> ~ r2_hidden(k1_zfmisc_1(o_0_0_xboole_0),sK4(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_69])])).

fof(f435,plain,
    ( spl6_49
  <=> ~ m1_subset_1(k1_zfmisc_1(o_0_0_xboole_0),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_49])])).

fof(f439,plain,
    ( ~ r2_hidden(k1_zfmisc_1(o_0_0_xboole_0),sK4(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))
    | ~ spl6_49 ),
    inference(unit_resulting_resolution,[],[f93,f436,f106])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f62])).

fof(f62,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t55_tops_1.p',t4_subset)).

fof(f436,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(o_0_0_xboole_0),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl6_49 ),
    inference(avatar_component_clause,[],[f435])).

fof(f552,plain,
    ( ~ spl6_67
    | ~ spl6_2
    | ~ spl6_10
    | spl6_19 ),
    inference(avatar_split_clause,[],[f543,f183,f148,f120,f550])).

fof(f550,plain,
    ( spl6_67
  <=> ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_67])])).

fof(f183,plain,
    ( spl6_19
  <=> ~ v3_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f543,plain,
    ( ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK2),sK0)
    | ~ spl6_2
    | ~ spl6_10
    | ~ spl6_19 ),
    inference(unit_resulting_resolution,[],[f121,f184,f149,f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X1,X0)
      | ~ v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f184,plain,
    ( ~ v3_pre_topc(sK2,sK0)
    | ~ spl6_19 ),
    inference(avatar_component_clause,[],[f183])).

fof(f538,plain,
    ( spl6_64
    | ~ spl6_4
    | ~ spl6_12
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f526,f177,f155,f127,f536])).

fof(f177,plain,
    ( spl6_16
  <=> v3_pre_topc(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f526,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(sK1),sK3),sK1)
    | ~ spl6_4
    | ~ spl6_12
    | ~ spl6_16 ),
    inference(unit_resulting_resolution,[],[f128,f178,f156,f91])).

fof(f178,plain,
    ( v3_pre_topc(sK3,sK1)
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f177])).

fof(f524,plain,
    ( spl6_62
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_56 ),
    inference(avatar_split_clause,[],[f502,f479,f120,f113,f522])).

fof(f522,plain,
    ( spl6_62
  <=> v3_pre_topc(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_62])])).

fof(f479,plain,
    ( spl6_56
  <=> m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_56])])).

fof(f502,plain,
    ( v3_pre_topc(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK0)
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_56 ),
    inference(unit_resulting_resolution,[],[f114,f121,f480,f99])).

fof(f480,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_56 ),
    inference(avatar_component_clause,[],[f479])).

fof(f517,plain,
    ( spl6_60
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_52 ),
    inference(avatar_split_clause,[],[f491,f465,f120,f113,f515])).

fof(f515,plain,
    ( spl6_60
  <=> v3_pre_topc(k1_tops_1(sK0,k1_tops_1(sK0,sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_60])])).

fof(f491,plain,
    ( v3_pre_topc(k1_tops_1(sK0,k1_tops_1(sK0,sK2)),sK0)
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_52 ),
    inference(unit_resulting_resolution,[],[f114,f121,f466,f99])).

fof(f488,plain,
    ( spl6_58
    | ~ spl6_4
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f456,f155,f127,f486])).

fof(f486,plain,
    ( spl6_58
  <=> m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_58])])).

fof(f456,plain,
    ( m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl6_4
    | ~ spl6_12 ),
    inference(unit_resulting_resolution,[],[f128,f156,f101])).

fof(f101,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t55_tops_1.p',dt_k2_pre_topc)).

fof(f481,plain,
    ( spl6_56
    | ~ spl6_2
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f455,f148,f120,f479])).

fof(f455,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_2
    | ~ spl6_10 ),
    inference(unit_resulting_resolution,[],[f121,f149,f101])).

fof(f474,plain,
    ( spl6_54
    | ~ spl6_4
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f421,f155,f127,f472])).

fof(f472,plain,
    ( spl6_54
  <=> m1_subset_1(k1_tops_1(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_54])])).

fof(f421,plain,
    ( m1_subset_1(k1_tops_1(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl6_4
    | ~ spl6_12 ),
    inference(unit_resulting_resolution,[],[f128,f156,f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
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
    file('/export/starexec/sandbox/benchmark/tops_1__t55_tops_1.p',dt_k1_tops_1)).

fof(f467,plain,
    ( spl6_52
    | ~ spl6_2
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f420,f148,f120,f465])).

fof(f420,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_2
    | ~ spl6_10 ),
    inference(unit_resulting_resolution,[],[f121,f149,f100])).

fof(f447,plain,
    ( ~ spl6_51
    | spl6_49 ),
    inference(avatar_split_clause,[],[f440,f435,f445])).

fof(f445,plain,
    ( spl6_51
  <=> ~ r2_hidden(k1_zfmisc_1(o_0_0_xboole_0),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_51])])).

fof(f440,plain,
    ( ~ r2_hidden(k1_zfmisc_1(o_0_0_xboole_0),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl6_49 ),
    inference(unit_resulting_resolution,[],[f436,f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t55_tops_1.p',t1_subset)).

fof(f437,plain,
    ( ~ spl6_49
    | ~ spl6_6
    | ~ spl6_40 ),
    inference(avatar_split_clause,[],[f398,f340,f134,f435])).

fof(f134,plain,
    ( spl6_6
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f340,plain,
    ( spl6_40
  <=> r2_hidden(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).

fof(f398,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(o_0_0_xboole_0),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl6_6
    | ~ spl6_40 ),
    inference(unit_resulting_resolution,[],[f135,f341,f107])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t55_tops_1.p',t5_subset)).

fof(f341,plain,
    ( r2_hidden(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl6_40 ),
    inference(avatar_component_clause,[],[f340])).

fof(f135,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f134])).

fof(f414,plain,
    ( spl6_46
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f381,f148,f120,f113,f412])).

fof(f381,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK2),sK0)
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_10 ),
    inference(unit_resulting_resolution,[],[f114,f121,f149,f99])).

fof(f389,plain,
    ( ~ spl6_45
    | ~ spl6_6
    | spl6_39 ),
    inference(avatar_split_clause,[],[f373,f331,f134,f387])).

fof(f387,plain,
    ( spl6_45
  <=> ~ v1_xboole_0(k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_45])])).

fof(f331,plain,
    ( spl6_39
  <=> k1_zfmisc_1(o_0_0_xboole_0) != o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_39])])).

fof(f373,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl6_6
    | ~ spl6_39 ),
    inference(unit_resulting_resolution,[],[f135,f332,f104])).

fof(f104,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t55_tops_1.p',t8_boole)).

fof(f332,plain,
    ( k1_zfmisc_1(o_0_0_xboole_0) != o_0_0_xboole_0
    | ~ spl6_39 ),
    inference(avatar_component_clause,[],[f331])).

fof(f352,plain,
    ( spl6_42
    | ~ spl6_28
    | ~ spl6_38 ),
    inference(avatar_split_clause,[],[f344,f334,f241,f350])).

fof(f350,plain,
    ( spl6_42
  <=> m1_subset_1(o_0_0_xboole_0,o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).

fof(f241,plain,
    ( spl6_28
  <=> m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f334,plain,
    ( spl6_38
  <=> k1_zfmisc_1(o_0_0_xboole_0) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).

fof(f344,plain,
    ( m1_subset_1(o_0_0_xboole_0,o_0_0_xboole_0)
    | ~ spl6_28
    | ~ spl6_38 ),
    inference(backward_demodulation,[],[f335,f242])).

fof(f242,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl6_28 ),
    inference(avatar_component_clause,[],[f241])).

fof(f335,plain,
    ( k1_zfmisc_1(o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl6_38 ),
    inference(avatar_component_clause,[],[f334])).

fof(f342,plain,
    ( spl6_38
    | spl6_40
    | ~ spl6_6
    | ~ spl6_28 ),
    inference(avatar_split_clause,[],[f246,f241,f134,f340,f334])).

fof(f246,plain,
    ( r2_hidden(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | k1_zfmisc_1(o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl6_6
    | ~ spl6_28 ),
    inference(resolution,[],[f204,f242])).

fof(f204,plain,
    ( ! [X4,X3] :
        ( ~ m1_subset_1(X3,X4)
        | r2_hidden(X3,X4)
        | o_0_0_xboole_0 = X4 )
    | ~ spl6_6 ),
    inference(resolution,[],[f96,f160])).

fof(f160,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | o_0_0_xboole_0 = X0 )
    | ~ spl6_6 ),
    inference(backward_demodulation,[],[f158,f87])).

fof(f87,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t55_tops_1.p',t6_boole)).

fof(f158,plain,
    ( o_0_0_xboole_0 = k1_xboole_0
    | ~ spl6_6 ),
    inference(unit_resulting_resolution,[],[f135,f87])).

fof(f96,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,X1) ) ),
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
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t55_tops_1.p',t2_subset)).

fof(f305,plain,
    ( spl6_36
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f260,f155,f303])).

fof(f260,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK1),sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl6_12 ),
    inference(unit_resulting_resolution,[],[f156,f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t55_tops_1.p',dt_k3_subset_1)).

fof(f298,plain,
    ( spl6_34
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f259,f148,f296])).

fof(f259,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_10 ),
    inference(unit_resulting_resolution,[],[f149,f97])).

fof(f289,plain,
    ( spl6_32
    | ~ spl6_6
    | ~ spl6_30 ),
    inference(avatar_split_clause,[],[f275,f267,f134,f287])).

fof(f287,plain,
    ( spl6_32
  <=> k3_subset_1(o_0_0_xboole_0,o_0_0_xboole_0) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).

fof(f267,plain,
    ( spl6_30
  <=> m1_subset_1(k3_subset_1(o_0_0_xboole_0,o_0_0_xboole_0),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).

fof(f275,plain,
    ( k3_subset_1(o_0_0_xboole_0,o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl6_6
    | ~ spl6_30 ),
    inference(unit_resulting_resolution,[],[f271,f249])).

fof(f249,plain,
    ( ! [X0] :
        ( r2_hidden(sK4(X0),X0)
        | o_0_0_xboole_0 = X0 )
    | ~ spl6_6 ),
    inference(resolution,[],[f204,f93])).

fof(f271,plain,
    ( ! [X0] : ~ r2_hidden(X0,k3_subset_1(o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl6_6
    | ~ spl6_30 ),
    inference(unit_resulting_resolution,[],[f135,f268,f107])).

fof(f268,plain,
    ( m1_subset_1(k3_subset_1(o_0_0_xboole_0,o_0_0_xboole_0),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl6_30 ),
    inference(avatar_component_clause,[],[f267])).

fof(f269,plain,
    ( spl6_30
    | ~ spl6_28 ),
    inference(avatar_split_clause,[],[f258,f241,f267])).

fof(f258,plain,
    ( m1_subset_1(k3_subset_1(o_0_0_xboole_0,o_0_0_xboole_0),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl6_28 ),
    inference(unit_resulting_resolution,[],[f242,f97])).

fof(f243,plain,
    ( spl6_28
    | ~ spl6_26 ),
    inference(avatar_split_clause,[],[f235,f232,f241])).

fof(f232,plain,
    ( spl6_26
  <=> o_0_0_xboole_0 = sK4(k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f235,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl6_26 ),
    inference(superposition,[],[f93,f233])).

fof(f233,plain,
    ( o_0_0_xboole_0 = sK4(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl6_26 ),
    inference(avatar_component_clause,[],[f232])).

fof(f236,plain,
    ( ~ spl6_23
    | spl6_20 ),
    inference(avatar_split_clause,[],[f81,f192,f199])).

fof(f192,plain,
    ( spl6_20
  <=> k1_tops_1(sK0,sK2) = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f81,plain,
    ( k1_tops_1(sK0,sK2) = sK2
    | k1_tops_1(sK1,sK3) != sK3 ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,
    ( ( ( ~ v3_pre_topc(sK2,sK0)
        & k1_tops_1(sK0,sK2) = sK2 )
      | ( k1_tops_1(sK1,sK3) != sK3
        & v3_pre_topc(sK3,sK1) ) )
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f38,f68,f67,f66,f65])).

fof(f65,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ( ~ v3_pre_topc(X2,X0)
                        & k1_tops_1(X0,X2) = X2 )
                      | ( k1_tops_1(X1,X3) != X3
                        & v3_pre_topc(X3,X1) ) )
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & l1_pre_topc(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ~ v3_pre_topc(X2,sK0)
                      & k1_tops_1(sK0,X2) = X2 )
                    | ( k1_tops_1(X1,X3) != X3
                      & v3_pre_topc(X3,X1) ) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ~ v3_pre_topc(X2,X0)
                      & k1_tops_1(X0,X2) = X2 )
                    | ( k1_tops_1(X1,X3) != X3
                      & v3_pre_topc(X3,X1) ) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & l1_pre_topc(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ( ( ~ v3_pre_topc(X2,X0)
                    & k1_tops_1(X0,X2) = X2 )
                  | ( k1_tops_1(sK1,X3) != X3
                    & v3_pre_topc(X3,sK1) ) )
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ( ( ~ v3_pre_topc(X2,X0)
                  & k1_tops_1(X0,X2) = X2 )
                | ( k1_tops_1(X1,X3) != X3
                  & v3_pre_topc(X3,X1) ) )
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X3] :
            ( ( ( ~ v3_pre_topc(sK2,X0)
                & k1_tops_1(X0,sK2) = sK2 )
              | ( k1_tops_1(X1,X3) != X3
                & v3_pre_topc(X3,X1) ) )
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ( ( ~ v3_pre_topc(X2,X0)
              & k1_tops_1(X0,X2) = X2 )
            | ( k1_tops_1(X1,X3) != X3
              & v3_pre_topc(X3,X1) ) )
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ( ( ~ v3_pre_topc(X2,X0)
            & k1_tops_1(X0,X2) = X2 )
          | ( k1_tops_1(X1,sK3) != sK3
            & v3_pre_topc(sK3,X1) ) )
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ~ v3_pre_topc(X2,X0)
                      & k1_tops_1(X0,X2) = X2 )
                    | ( k1_tops_1(X1,X3) != X3
                      & v3_pre_topc(X3,X1) ) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ~ v3_pre_topc(X2,X0)
                      & k1_tops_1(X0,X2) = X2 )
                    | ( k1_tops_1(X1,X3) != X3
                      & v3_pre_topc(X3,X1) ) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( l1_pre_topc(X1)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( ( k1_tops_1(X0,X2) = X2
                       => v3_pre_topc(X2,X0) )
                      & ( v3_pre_topc(X3,X1)
                       => k1_tops_1(X1,X3) = X3 ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( k1_tops_1(X0,X2) = X2
                     => v3_pre_topc(X2,X0) )
                    & ( v3_pre_topc(X3,X1)
                     => k1_tops_1(X1,X3) = X3 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t55_tops_1.p',t55_tops_1)).

fof(f234,plain,
    ( spl6_26
    | ~ spl6_6
    | ~ spl6_24 ),
    inference(avatar_split_clause,[],[f219,f211,f134,f232])).

fof(f211,plain,
    ( spl6_24
  <=> v1_xboole_0(sK4(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f219,plain,
    ( o_0_0_xboole_0 = sK4(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl6_6
    | ~ spl6_24 ),
    inference(unit_resulting_resolution,[],[f212,f160])).

fof(f212,plain,
    ( v1_xboole_0(sK4(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl6_24 ),
    inference(avatar_component_clause,[],[f211])).

fof(f213,plain,
    ( spl6_24
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f206,f134,f211])).

fof(f206,plain,
    ( v1_xboole_0(sK4(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl6_6 ),
    inference(unit_resulting_resolution,[],[f93,f205,f96])).

fof(f205,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK4(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl6_6 ),
    inference(unit_resulting_resolution,[],[f135,f93,f107])).

fof(f201,plain,
    ( ~ spl6_23
    | ~ spl6_19 ),
    inference(avatar_split_clause,[],[f83,f183,f199])).

fof(f83,plain,
    ( ~ v3_pre_topc(sK2,sK0)
    | k1_tops_1(sK1,sK3) != sK3 ),
    inference(cnf_transformation,[],[f69])).

fof(f194,plain,
    ( spl6_16
    | spl6_20 ),
    inference(avatar_split_clause,[],[f80,f192,f177])).

fof(f80,plain,
    ( k1_tops_1(sK0,sK2) = sK2
    | v3_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f69])).

fof(f185,plain,
    ( spl6_16
    | ~ spl6_19 ),
    inference(avatar_split_clause,[],[f82,f183,f177])).

fof(f82,plain,
    ( ~ v3_pre_topc(sK2,sK0)
    | v3_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f69])).

fof(f169,plain,
    ( spl6_14
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f158,f134,f167])).

fof(f167,plain,
    ( spl6_14
  <=> o_0_0_xboole_0 = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f157,plain,(
    spl6_12 ),
    inference(avatar_split_clause,[],[f79,f155])).

fof(f79,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f69])).

fof(f150,plain,(
    spl6_10 ),
    inference(avatar_split_clause,[],[f78,f148])).

fof(f78,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f69])).

fof(f143,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f108,f141])).

fof(f141,plain,
    ( spl6_8
  <=> l1_pre_topc(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f108,plain,(
    l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f74])).

fof(f74,plain,(
    l1_pre_topc(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f16,f73])).

fof(f73,plain,
    ( ? [X0] : l1_pre_topc(X0)
   => l1_pre_topc(sK5) ),
    introduced(choice_axiom,[])).

fof(f16,axiom,(
    ? [X0] : l1_pre_topc(X0) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t55_tops_1.p',existence_l1_pre_topc)).

fof(f136,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f84,f134])).

fof(f84,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t55_tops_1.p',dt_o_0_0_xboole_0)).

fof(f129,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f77,f127])).

fof(f77,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f69])).

fof(f122,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f76,f120])).

fof(f76,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f69])).

fof(f115,plain,(
    spl6_0 ),
    inference(avatar_split_clause,[],[f75,f113])).

fof(f75,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f69])).
%------------------------------------------------------------------------------
