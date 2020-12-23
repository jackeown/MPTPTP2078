%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tmap_1__t115_tmap_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:04 EDT 2019

% Result     : Theorem 0.74s
% Output     : Refutation 0.74s
% Verified   : 
% Statistics : Number of formulae       :  342 ( 823 expanded)
%              Number of leaves         :   76 ( 328 expanded)
%              Depth                    :   16
%              Number of atoms          : 1439 (3128 expanded)
%              Number of equality atoms :  130 ( 276 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1012,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f133,f140,f147,f154,f161,f168,f175,f182,f189,f201,f217,f237,f264,f341,f345,f378,f382,f386,f396,f417,f423,f430,f437,f467,f606,f649,f653,f663,f667,f671,f678,f685,f692,f707,f712,f721,f724,f731,f761,f780,f786,f809,f819,f853,f875,f901,f934,f950,f1011])).

fof(f1011,plain,
    ( ~ spl8_10
    | ~ spl8_12
    | spl8_15
    | ~ spl8_22
    | ~ spl8_46
    | ~ spl8_102 ),
    inference(avatar_contradiction_clause,[],[f1010])).

fof(f1010,plain,
    ( $false
    | ~ spl8_10
    | ~ spl8_12
    | ~ spl8_15
    | ~ spl8_22
    | ~ spl8_46
    | ~ spl8_102 ),
    inference(subsumption_resolution,[],[f1009,f181])).

fof(f181,plain,
    ( ~ v1_tsep_1(sK2,k8_tmap_1(sK0,sK1))
    | ~ spl8_15 ),
    inference(avatar_component_clause,[],[f180])).

fof(f180,plain,
    ( spl8_15
  <=> ~ v1_tsep_1(sK2,k8_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).

fof(f1009,plain,
    ( v1_tsep_1(sK2,k8_tmap_1(sK0,sK1))
    | ~ spl8_10
    | ~ spl8_12
    | ~ spl8_22
    | ~ spl8_46
    | ~ spl8_102 ),
    inference(subsumption_resolution,[],[f1008,f213])).

fof(f213,plain,
    ( l1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ spl8_22 ),
    inference(avatar_component_clause,[],[f212])).

fof(f212,plain,
    ( spl8_22
  <=> l1_pre_topc(k8_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).

fof(f1008,plain,
    ( ~ l1_pre_topc(k8_tmap_1(sK0,sK1))
    | v1_tsep_1(sK2,k8_tmap_1(sK0,sK1))
    | ~ spl8_10
    | ~ spl8_12
    | ~ spl8_46
    | ~ spl8_102 ),
    inference(subsumption_resolution,[],[f1007,f410])).

fof(f410,plain,
    ( v2_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ spl8_46 ),
    inference(avatar_component_clause,[],[f409])).

fof(f409,plain,
    ( spl8_46
  <=> v2_pre_topc(k8_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_46])])).

fof(f1007,plain,
    ( ~ v2_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(k8_tmap_1(sK0,sK1))
    | v1_tsep_1(sK2,k8_tmap_1(sK0,sK1))
    | ~ spl8_10
    | ~ spl8_12
    | ~ spl8_102 ),
    inference(subsumption_resolution,[],[f1004,f167])).

fof(f167,plain,
    ( m1_pre_topc(sK2,k8_tmap_1(sK0,sK1))
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f166])).

fof(f166,plain,
    ( spl8_10
  <=> m1_pre_topc(sK2,k8_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f1004,plain,
    ( ~ m1_pre_topc(sK2,k8_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(k8_tmap_1(sK0,sK1))
    | v1_tsep_1(sK2,k8_tmap_1(sK0,sK1))
    | ~ spl8_12
    | ~ spl8_102 ),
    inference(resolution,[],[f900,f471])).

fof(f471,plain,
    ( ! [X0] :
        ( ~ v3_pre_topc(u1_struct_0(sK1),X0)
        | ~ m1_pre_topc(sK2,X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v1_tsep_1(sK2,X0) )
    | ~ spl8_12 ),
    inference(superposition,[],[f257,f174])).

fof(f174,plain,
    ( u1_struct_0(sK1) = u1_struct_0(sK2)
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f173])).

fof(f173,plain,
    ( spl8_12
  <=> u1_struct_0(sK1) = u1_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f257,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v1_tsep_1(X1,X0) ) ),
    inference(duplicate_literal_removal,[],[f254])).

fof(f254,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0)
      | ~ v3_pre_topc(u1_struct_0(X1),X0)
      | v1_tsep_1(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f121,f112])).

fof(f112,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f74,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f43])).

fof(f43,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t115_tmap_1.p',t1_tsep_1)).

fof(f121,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0)
      | ~ v3_pre_topc(u1_struct_0(X1),X0)
      | v1_tsep_1(X1,X0) ) ),
    inference(equality_resolution,[],[f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X1) != X2
      | ~ v3_pre_topc(X2,X0)
      | v1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) )
              <=> v3_pre_topc(X2,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) )
              <=> v3_pre_topc(X2,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f40])).

fof(f40,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( ( m1_pre_topc(X1,X0)
                    & v1_tsep_1(X1,X0) )
                <=> v3_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t115_tmap_1.p',t16_tsep_1)).

fof(f900,plain,
    ( v3_pre_topc(u1_struct_0(sK1),k8_tmap_1(sK0,sK1))
    | ~ spl8_102 ),
    inference(avatar_component_clause,[],[f899])).

fof(f899,plain,
    ( spl8_102
  <=> v3_pre_topc(u1_struct_0(sK1),k8_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_102])])).

fof(f950,plain,
    ( ~ spl8_63
    | spl8_104
    | spl8_1
    | ~ spl8_18
    | ~ spl8_30 ),
    inference(avatar_split_clause,[],[f629,f343,f199,f131,f948,f658])).

fof(f658,plain,
    ( spl8_63
  <=> ~ v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_63])])).

fof(f948,plain,
    ( spl8_104
  <=> ! [X5,X4,X6] :
        ( ~ m1_pre_topc(X4,sK1)
        | ~ m1_pre_topc(X6,sK2)
        | k4_subset_1(u1_struct_0(sK1),u1_struct_0(X6),sK5(sK1,X4,X5)) = k4_subset_1(u1_struct_0(sK1),sK5(sK1,X4,X5),u1_struct_0(X6))
        | k8_tmap_1(sK1,X4) = X5
        | ~ v1_pre_topc(X5)
        | ~ l1_pre_topc(X5)
        | ~ v2_pre_topc(X5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_104])])).

fof(f131,plain,
    ( spl8_1
  <=> ~ v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f199,plain,
    ( spl8_18
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f343,plain,
    ( spl8_30
  <=> ! [X0] :
        ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_pre_topc(X0,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_30])])).

fof(f629,plain,
    ( ! [X6,X4,X5] :
        ( ~ m1_pre_topc(X4,sK1)
        | ~ v1_pre_topc(X5)
        | ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X5)
        | k8_tmap_1(sK1,X4) = X5
        | ~ v2_pre_topc(sK1)
        | k4_subset_1(u1_struct_0(sK1),u1_struct_0(X6),sK5(sK1,X4,X5)) = k4_subset_1(u1_struct_0(sK1),sK5(sK1,X4,X5),u1_struct_0(X6))
        | ~ m1_pre_topc(X6,sK2) )
    | ~ spl8_1
    | ~ spl8_18
    | ~ spl8_30 ),
    inference(subsumption_resolution,[],[f628,f132])).

fof(f132,plain,
    ( ~ v2_struct_0(sK1)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f131])).

fof(f628,plain,
    ( ! [X6,X4,X5] :
        ( ~ m1_pre_topc(X4,sK1)
        | ~ v1_pre_topc(X5)
        | ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X5)
        | v2_struct_0(sK1)
        | k8_tmap_1(sK1,X4) = X5
        | ~ v2_pre_topc(sK1)
        | k4_subset_1(u1_struct_0(sK1),u1_struct_0(X6),sK5(sK1,X4,X5)) = k4_subset_1(u1_struct_0(sK1),sK5(sK1,X4,X5),u1_struct_0(X6))
        | ~ m1_pre_topc(X6,sK2) )
    | ~ spl8_18
    | ~ spl8_30 ),
    inference(subsumption_resolution,[],[f621,f200])).

fof(f200,plain,
    ( l1_pre_topc(sK1)
    | ~ spl8_18 ),
    inference(avatar_component_clause,[],[f199])).

fof(f621,plain,
    ( ! [X6,X4,X5] :
        ( ~ l1_pre_topc(sK1)
        | ~ m1_pre_topc(X4,sK1)
        | ~ v1_pre_topc(X5)
        | ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X5)
        | v2_struct_0(sK1)
        | k8_tmap_1(sK1,X4) = X5
        | ~ v2_pre_topc(sK1)
        | k4_subset_1(u1_struct_0(sK1),u1_struct_0(X6),sK5(sK1,X4,X5)) = k4_subset_1(u1_struct_0(sK1),sK5(sK1,X4,X5),u1_struct_0(X6))
        | ~ m1_pre_topc(X6,sK2) )
    | ~ spl8_30 ),
    inference(resolution,[],[f289,f344])).

fof(f344,plain,
    ( ! [X0] :
        ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_pre_topc(X0,sK2) )
    | ~ spl8_30 ),
    inference(avatar_component_clause,[],[f343])).

fof(f289,plain,(
    ! [X12,X10,X11,X9] :
      ( ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X9)))
      | ~ l1_pre_topc(X9)
      | ~ m1_pre_topc(X10,X9)
      | ~ v1_pre_topc(X11)
      | ~ v2_pre_topc(X11)
      | ~ l1_pre_topc(X11)
      | v2_struct_0(X9)
      | k8_tmap_1(X9,X10) = X11
      | ~ v2_pre_topc(X9)
      | k4_subset_1(u1_struct_0(X9),X12,sK5(X9,X10,X11)) = k4_subset_1(u1_struct_0(X9),sK5(X9,X10,X11),X12) ) ),
    inference(resolution,[],[f109,f97])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t115_tmap_1.p',commutativity_k4_subset_1)).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X2)
      | v2_struct_0(X0)
      | k8_tmap_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k8_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( k6_tmap_1(X0,X3) = X2
                    | u1_struct_0(X1) != X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f72])).

fof(f72,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k8_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( k6_tmap_1(X0,X3) = X2
                    | u1_struct_0(X1) != X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m1_pre_topc(X1,X0) )
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
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( ( l1_pre_topc(X2)
                & v2_pre_topc(X2)
                & v1_pre_topc(X2) )
             => ( k8_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => ( u1_struct_0(X1) = X3
                     => k6_tmap_1(X0,X3) = X2 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t115_tmap_1.p',d11_tmap_1)).

fof(f934,plain,
    ( ~ spl8_6
    | ~ spl8_8
    | spl8_101 ),
    inference(avatar_contradiction_clause,[],[f933])).

fof(f933,plain,
    ( $false
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_101 ),
    inference(subsumption_resolution,[],[f932,f153])).

fof(f153,plain,
    ( l1_pre_topc(sK0)
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f152])).

fof(f152,plain,
    ( spl8_6
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f932,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl8_8
    | ~ spl8_101 ),
    inference(subsumption_resolution,[],[f931,f160])).

fof(f160,plain,
    ( m1_pre_topc(sK1,sK0)
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f159])).

fof(f159,plain,
    ( spl8_8
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f931,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl8_101 ),
    inference(resolution,[],[f894,f112])).

fof(f894,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_101 ),
    inference(avatar_component_clause,[],[f893])).

fof(f893,plain,
    ( spl8_101
  <=> ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_101])])).

fof(f901,plain,
    ( ~ spl8_101
    | spl8_102
    | spl8_3
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_10
    | ~ spl8_12
    | ~ spl8_56 ),
    inference(avatar_split_clause,[],[f888,f604,f173,f166,f152,f145,f138,f899,f893])).

fof(f138,plain,
    ( spl8_3
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f145,plain,
    ( spl8_4
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f604,plain,
    ( spl8_56
  <=> k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_56])])).

fof(f888,plain,
    ( v3_pre_topc(u1_struct_0(sK1),k8_tmap_1(sK0,sK1))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_10
    | ~ spl8_12
    | ~ spl8_56 ),
    inference(subsumption_resolution,[],[f887,f167])).

fof(f887,plain,
    ( ~ m1_pre_topc(sK2,k8_tmap_1(sK0,sK1))
    | v3_pre_topc(u1_struct_0(sK1),k8_tmap_1(sK0,sK1))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_12
    | ~ spl8_56 ),
    inference(forward_demodulation,[],[f886,f605])).

fof(f605,plain,
    ( k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | ~ spl8_56 ),
    inference(avatar_component_clause,[],[f604])).

fof(f886,plain,
    ( v3_pre_topc(u1_struct_0(sK1),k8_tmap_1(sK0,sK1))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_pre_topc(sK2,k6_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_12
    | ~ spl8_56 ),
    inference(subsumption_resolution,[],[f885,f139])).

fof(f139,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f138])).

fof(f885,plain,
    ( v3_pre_topc(u1_struct_0(sK1),k8_tmap_1(sK0,sK1))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(sK2,k6_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_12
    | ~ spl8_56 ),
    inference(subsumption_resolution,[],[f884,f153])).

fof(f884,plain,
    ( v3_pre_topc(u1_struct_0(sK1),k8_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(sK2,k6_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ spl8_4
    | ~ spl8_12
    | ~ spl8_56 ),
    inference(subsumption_resolution,[],[f880,f146])).

fof(f146,plain,
    ( v2_pre_topc(sK0)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f145])).

fof(f880,plain,
    ( v3_pre_topc(u1_struct_0(sK1),k8_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(sK2,k6_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ spl8_12
    | ~ spl8_56 ),
    inference(superposition,[],[f327,f605])).

fof(f327,plain,
    ( ! [X6] :
        ( v3_pre_topc(u1_struct_0(sK1),k6_tmap_1(X6,u1_struct_0(sK1)))
        | ~ v2_pre_topc(X6)
        | ~ l1_pre_topc(X6)
        | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(X6)))
        | v2_struct_0(X6)
        | ~ m1_pre_topc(sK2,k6_tmap_1(X6,u1_struct_0(sK1))) )
    | ~ spl8_12 ),
    inference(subsumption_resolution,[],[f315,f106])).

fof(f106,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | l1_pre_topc(k6_tmap_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t115_tmap_1.p',dt_k6_tmap_1)).

fof(f315,plain,
    ( ! [X6] :
        ( ~ m1_pre_topc(sK2,k6_tmap_1(X6,u1_struct_0(sK1)))
        | ~ l1_pre_topc(k6_tmap_1(X6,u1_struct_0(sK1)))
        | ~ v2_pre_topc(X6)
        | ~ l1_pre_topc(X6)
        | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(X6)))
        | v2_struct_0(X6)
        | v3_pre_topc(u1_struct_0(sK1),k6_tmap_1(X6,u1_struct_0(sK1))) )
    | ~ spl8_12 ),
    inference(resolution,[],[f220,f123])).

fof(f123,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X2))))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_struct_0(X0)
      | v3_pre_topc(X2,k6_tmap_1(X0,X2)) ) ),
    inference(equality_resolution,[],[f107])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1))))
      | X1 != X2
      | v3_pre_topc(X2,k6_tmap_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v3_pre_topc(X2,k6_tmap_1(X0,X1))
              | X1 != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f70])).

fof(f70,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v3_pre_topc(X2,k6_tmap_1(X0,X1))
              | X1 != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
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
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1))))
             => ( X1 = X2
               => v3_pre_topc(X2,k6_tmap_1(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t115_tmap_1.p',t105_tmap_1)).

fof(f220,plain,
    ( ! [X0] :
        ( m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_pre_topc(sK2,X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl8_12 ),
    inference(superposition,[],[f112,f174])).

fof(f875,plain,
    ( spl8_98
    | ~ spl8_18
    | ~ spl8_88 ),
    inference(avatar_split_clause,[],[f823,f778,f199,f873])).

fof(f873,plain,
    ( spl8_98
  <=> u1_struct_0(sK6(sK1)) = k4_subset_1(u1_struct_0(sK1),u1_struct_0(sK6(sK1)),u1_struct_0(sK6(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_98])])).

fof(f778,plain,
    ( spl8_88
  <=> ! [X9] :
        ( ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK1)))
        | k4_subset_1(u1_struct_0(sK1),X9,X9) = X9 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_88])])).

fof(f823,plain,
    ( u1_struct_0(sK6(sK1)) = k4_subset_1(u1_struct_0(sK1),u1_struct_0(sK6(sK1)),u1_struct_0(sK6(sK1)))
    | ~ spl8_18
    | ~ spl8_88 ),
    inference(subsumption_resolution,[],[f822,f200])).

fof(f822,plain,
    ( u1_struct_0(sK6(sK1)) = k4_subset_1(u1_struct_0(sK1),u1_struct_0(sK6(sK1)),u1_struct_0(sK6(sK1)))
    | ~ l1_pre_topc(sK1)
    | ~ spl8_18
    | ~ spl8_88 ),
    inference(resolution,[],[f791,f118])).

fof(f118,plain,(
    ! [X0] :
      ( m1_pre_topc(sK6(X0),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f80])).

fof(f80,plain,(
    ! [X0] :
      ( ? [X1] : m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ? [X1] : m1_pre_topc(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t115_tmap_1.p',existence_m1_pre_topc)).

fof(f791,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(X1,sK1)
        | u1_struct_0(X1) = k4_subset_1(u1_struct_0(sK1),u1_struct_0(X1),u1_struct_0(X1)) )
    | ~ spl8_18
    | ~ spl8_88 ),
    inference(subsumption_resolution,[],[f788,f200])).

fof(f788,plain,
    ( ! [X1] :
        ( u1_struct_0(X1) = k4_subset_1(u1_struct_0(sK1),u1_struct_0(X1),u1_struct_0(X1))
        | ~ m1_pre_topc(X1,sK1)
        | ~ l1_pre_topc(sK1) )
    | ~ spl8_88 ),
    inference(resolution,[],[f779,f112])).

fof(f779,plain,
    ( ! [X9] :
        ( ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK1)))
        | k4_subset_1(u1_struct_0(sK1),X9,X9) = X9 )
    | ~ spl8_88 ),
    inference(avatar_component_clause,[],[f778])).

fof(f853,plain,
    ( spl8_96
    | ~ spl8_20
    | ~ spl8_30
    | ~ spl8_88 ),
    inference(avatar_split_clause,[],[f812,f778,f343,f209,f851])).

fof(f851,plain,
    ( spl8_96
  <=> u1_struct_0(sK6(sK2)) = k4_subset_1(u1_struct_0(sK1),u1_struct_0(sK6(sK2)),u1_struct_0(sK6(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_96])])).

fof(f209,plain,
    ( spl8_20
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).

fof(f812,plain,
    ( u1_struct_0(sK6(sK2)) = k4_subset_1(u1_struct_0(sK1),u1_struct_0(sK6(sK2)),u1_struct_0(sK6(sK2)))
    | ~ spl8_20
    | ~ spl8_30
    | ~ spl8_88 ),
    inference(subsumption_resolution,[],[f811,f210])).

fof(f210,plain,
    ( l1_pre_topc(sK2)
    | ~ spl8_20 ),
    inference(avatar_component_clause,[],[f209])).

fof(f811,plain,
    ( u1_struct_0(sK6(sK2)) = k4_subset_1(u1_struct_0(sK1),u1_struct_0(sK6(sK2)),u1_struct_0(sK6(sK2)))
    | ~ l1_pre_topc(sK2)
    | ~ spl8_30
    | ~ spl8_88 ),
    inference(resolution,[],[f787,f118])).

fof(f787,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK2)
        | u1_struct_0(X0) = k4_subset_1(u1_struct_0(sK1),u1_struct_0(X0),u1_struct_0(X0)) )
    | ~ spl8_30
    | ~ spl8_88 ),
    inference(resolution,[],[f779,f344])).

fof(f819,plain,
    ( spl8_94
    | ~ spl8_18
    | ~ spl8_24 ),
    inference(avatar_split_clause,[],[f550,f262,f199,f817])).

fof(f817,plain,
    ( spl8_94
  <=> k4_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),u1_pre_topc(sK1),u1_pre_topc(sK2)) = k4_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),u1_pre_topc(sK2),u1_pre_topc(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_94])])).

fof(f262,plain,
    ( spl8_24
  <=> m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).

fof(f550,plain,
    ( k4_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),u1_pre_topc(sK1),u1_pre_topc(sK2)) = k4_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),u1_pre_topc(sK2),u1_pre_topc(sK1))
    | ~ spl8_18
    | ~ spl8_24 ),
    inference(subsumption_resolution,[],[f547,f200])).

fof(f547,plain,
    ( k4_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),u1_pre_topc(sK1),u1_pre_topc(sK2)) = k4_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),u1_pre_topc(sK2),u1_pre_topc(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ spl8_24 ),
    inference(resolution,[],[f252,f263])).

fof(f263,plain,
    ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ spl8_24 ),
    inference(avatar_component_clause,[],[f262])).

fof(f252,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
      | k4_subset_1(k1_zfmisc_1(u1_struct_0(X1)),X0,u1_pre_topc(X1)) = k4_subset_1(k1_zfmisc_1(u1_struct_0(X1)),u1_pre_topc(X1),X0)
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f97,f114])).

fof(f114,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f77])).

fof(f77,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t115_tmap_1.p',dt_u1_pre_topc)).

fof(f809,plain,
    ( spl8_90
    | spl8_92
    | ~ spl8_18
    | ~ spl8_30 ),
    inference(avatar_split_clause,[],[f516,f343,f199,f807,f804])).

fof(f804,plain,
    ( spl8_90
  <=> ! [X4] : ~ m1_pre_topc(X4,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_90])])).

fof(f807,plain,
    ( spl8_92
  <=> ! [X3] :
        ( u1_struct_0(X3) = k4_subset_1(u1_struct_0(sK1),u1_struct_0(X3),u1_struct_0(X3))
        | ~ m1_pre_topc(X3,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_92])])).

fof(f516,plain,
    ( ! [X4,X3] :
        ( u1_struct_0(X3) = k4_subset_1(u1_struct_0(sK1),u1_struct_0(X3),u1_struct_0(X3))
        | ~ m1_pre_topc(X4,sK1)
        | ~ m1_pre_topc(X3,sK2) )
    | ~ spl8_18
    | ~ spl8_30 ),
    inference(subsumption_resolution,[],[f509,f200])).

fof(f509,plain,
    ( ! [X4,X3] :
        ( u1_struct_0(X3) = k4_subset_1(u1_struct_0(sK1),u1_struct_0(X3),u1_struct_0(X3))
        | ~ m1_pre_topc(X4,sK1)
        | ~ l1_pre_topc(sK1)
        | ~ m1_pre_topc(X3,sK2) )
    | ~ spl8_30 ),
    inference(resolution,[],[f239,f344])).

fof(f239,plain,(
    ! [X4,X2,X3] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
      | k4_subset_1(u1_struct_0(X3),X2,X2) = X2
      | ~ m1_pre_topc(X4,X3)
      | ~ l1_pre_topc(X3) ) ),
    inference(resolution,[],[f98,f112])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X1) = X1 ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f62])).

fof(f62,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f35])).

fof(f35,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t115_tmap_1.p',idempotence_k4_subset_1)).

fof(f786,plain,
    ( spl8_3
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_8
    | spl8_87 ),
    inference(avatar_contradiction_clause,[],[f785])).

fof(f785,plain,
    ( $false
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_87 ),
    inference(subsumption_resolution,[],[f784,f139])).

fof(f784,plain,
    ( v2_struct_0(sK0)
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_87 ),
    inference(subsumption_resolution,[],[f783,f160])).

fof(f783,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0)
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_87 ),
    inference(subsumption_resolution,[],[f782,f153])).

fof(f782,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0)
    | ~ spl8_4
    | ~ spl8_87 ),
    inference(subsumption_resolution,[],[f781,f146])).

fof(f781,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0)
    | ~ spl8_87 ),
    inference(resolution,[],[f757,f115])).

fof(f115,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(k8_tmap_1(X0,X1))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t115_tmap_1.p',dt_k8_tmap_1)).

fof(f757,plain,
    ( ~ v1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ spl8_87 ),
    inference(avatar_component_clause,[],[f756])).

fof(f756,plain,
    ( spl8_87
  <=> ~ v1_pre_topc(k8_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_87])])).

fof(f780,plain,
    ( spl8_88
    | spl8_60
    | ~ spl8_30 ),
    inference(avatar_split_clause,[],[f353,f343,f647,f778])).

fof(f647,plain,
    ( spl8_60
  <=> ! [X12] : ~ m1_pre_topc(X12,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_60])])).

fof(f353,plain,
    ( ! [X8,X9] :
        ( ~ m1_pre_topc(X8,sK2)
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK1)))
        | k4_subset_1(u1_struct_0(sK1),X9,X9) = X9 )
    | ~ spl8_30 ),
    inference(resolution,[],[f344,f98])).

fof(f761,plain,
    ( ~ spl8_85
    | spl8_86
    | spl8_3
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_12
    | ~ spl8_56 ),
    inference(avatar_split_clause,[],[f748,f604,f173,f152,f145,f138,f759,f753])).

fof(f753,plain,
    ( spl8_85
  <=> ~ m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_85])])).

fof(f759,plain,
    ( spl8_86
  <=> v1_pre_topc(k8_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_86])])).

fof(f748,plain,
    ( v1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ m1_pre_topc(sK2,sK0)
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_12
    | ~ spl8_56 ),
    inference(subsumption_resolution,[],[f747,f139])).

fof(f747,plain,
    ( v1_pre_topc(k8_tmap_1(sK0,sK1))
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_12
    | ~ spl8_56 ),
    inference(subsumption_resolution,[],[f746,f146])).

fof(f746,plain,
    ( v1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ spl8_6
    | ~ spl8_12
    | ~ spl8_56 ),
    inference(subsumption_resolution,[],[f738,f153])).

fof(f738,plain,
    ( v1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ spl8_12
    | ~ spl8_56 ),
    inference(superposition,[],[f321,f605])).

fof(f321,plain,
    ( ! [X5] :
        ( v1_pre_topc(k6_tmap_1(X5,u1_struct_0(sK1)))
        | ~ l1_pre_topc(X5)
        | ~ v2_pre_topc(X5)
        | v2_struct_0(X5)
        | ~ m1_pre_topc(sK2,X5) )
    | ~ spl8_12 ),
    inference(duplicate_literal_removal,[],[f314])).

fof(f314,plain,
    ( ! [X5] :
        ( ~ m1_pre_topc(sK2,X5)
        | ~ l1_pre_topc(X5)
        | ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X5)
        | v2_struct_0(X5)
        | v1_pre_topc(k6_tmap_1(X5,u1_struct_0(sK1))) )
    | ~ spl8_12 ),
    inference(resolution,[],[f220,f104])).

fof(f104,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | v1_pre_topc(k6_tmap_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f731,plain,
    ( spl8_82
    | spl8_3
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f545,f159,f152,f145,f138,f729])).

fof(f729,plain,
    ( spl8_82
  <=> k8_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(k8_tmap_1(sK0,sK1)),u1_pre_topc(k8_tmap_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_82])])).

fof(f545,plain,
    ( k8_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(k8_tmap_1(sK0,sK1)),u1_pre_topc(k8_tmap_1(sK0,sK1)))
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f544,f139])).

fof(f544,plain,
    ( v2_struct_0(sK0)
    | k8_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(k8_tmap_1(sK0,sK1)),u1_pre_topc(k8_tmap_1(sK0,sK1)))
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f543,f146])).

fof(f543,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | k8_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(k8_tmap_1(sK0,sK1)),u1_pre_topc(k8_tmap_1(sK0,sK1)))
    | ~ spl8_6
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f537,f153])).

fof(f537,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | k8_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(k8_tmap_1(sK0,sK1)),u1_pre_topc(k8_tmap_1(sK0,sK1)))
    | ~ spl8_8 ),
    inference(resolution,[],[f231,f160])).

fof(f231,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | k8_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(k8_tmap_1(X0,X1)),u1_pre_topc(k8_tmap_1(X0,X1))) ) ),
    inference(subsumption_resolution,[],[f230,f117])).

fof(f117,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(k8_tmap_1(X0,X1))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f230,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(k8_tmap_1(X0,X1))
      | k8_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(k8_tmap_1(X0,X1)),u1_pre_topc(k8_tmap_1(X0,X1))) ) ),
    inference(resolution,[],[f115,f113])).

fof(f113,plain,(
    ! [X0] :
      ( ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f76])).

fof(f76,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f75])).

fof(f75,plain,(
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
    file('/export/starexec/sandbox/benchmark/tmap_1__t115_tmap_1.p',abstractness_v1_pre_topc)).

fof(f724,plain,
    ( spl8_74
    | spl8_77
    | spl8_79 ),
    inference(avatar_split_clause,[],[f710,f705,f699,f690])).

fof(f690,plain,
    ( spl8_74
  <=> g1_pre_topc(u1_struct_0(sK3(sK1)),u1_pre_topc(sK3(sK1))) = sK3(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_74])])).

fof(f699,plain,
    ( spl8_77
  <=> ~ r2_hidden(sK4(g1_pre_topc(u1_struct_0(sK3(sK1)),u1_pre_topc(sK3(sK1))),sK3(sK1)),g1_pre_topc(u1_struct_0(sK3(sK1)),u1_pre_topc(sK3(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_77])])).

fof(f705,plain,
    ( spl8_79
  <=> ~ r2_hidden(sK4(g1_pre_topc(u1_struct_0(sK3(sK1)),u1_pre_topc(sK3(sK1))),sK3(sK1)),sK3(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_79])])).

fof(f710,plain,
    ( g1_pre_topc(u1_struct_0(sK3(sK1)),u1_pre_topc(sK3(sK1))) = sK3(sK1)
    | ~ spl8_77
    | ~ spl8_79 ),
    inference(subsumption_resolution,[],[f709,f706])).

fof(f706,plain,
    ( ~ r2_hidden(sK4(g1_pre_topc(u1_struct_0(sK3(sK1)),u1_pre_topc(sK3(sK1))),sK3(sK1)),sK3(sK1))
    | ~ spl8_79 ),
    inference(avatar_component_clause,[],[f705])).

fof(f709,plain,
    ( r2_hidden(sK4(g1_pre_topc(u1_struct_0(sK3(sK1)),u1_pre_topc(sK3(sK1))),sK3(sK1)),sK3(sK1))
    | g1_pre_topc(u1_struct_0(sK3(sK1)),u1_pre_topc(sK3(sK1))) = sK3(sK1)
    | ~ spl8_77 ),
    inference(resolution,[],[f700,f102])).

fof(f102,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X1)
      | r2_hidden(sK4(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f46])).

fof(f46,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t115_tmap_1.p',t2_tarski)).

fof(f700,plain,
    ( ~ r2_hidden(sK4(g1_pre_topc(u1_struct_0(sK3(sK1)),u1_pre_topc(sK3(sK1))),sK3(sK1)),g1_pre_topc(u1_struct_0(sK3(sK1)),u1_pre_topc(sK3(sK1))))
    | ~ spl8_77 ),
    inference(avatar_component_clause,[],[f699])).

fof(f721,plain,
    ( ~ spl8_81
    | spl8_77
    | spl8_79 ),
    inference(avatar_split_clause,[],[f713,f705,f699,f719])).

fof(f719,plain,
    ( spl8_81
  <=> ~ r2_hidden(sK4(sK3(sK1),sK3(sK1)),sK3(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_81])])).

fof(f713,plain,
    ( ~ r2_hidden(sK4(sK3(sK1),sK3(sK1)),sK3(sK1))
    | ~ spl8_77
    | ~ spl8_79 ),
    inference(backward_demodulation,[],[f710,f700])).

fof(f712,plain,
    ( spl8_75
    | spl8_77
    | spl8_79 ),
    inference(avatar_contradiction_clause,[],[f711])).

fof(f711,plain,
    ( $false
    | ~ spl8_75
    | ~ spl8_77
    | ~ spl8_79 ),
    inference(subsumption_resolution,[],[f710,f688])).

fof(f688,plain,
    ( g1_pre_topc(u1_struct_0(sK3(sK1)),u1_pre_topc(sK3(sK1))) != sK3(sK1)
    | ~ spl8_75 ),
    inference(avatar_component_clause,[],[f687])).

fof(f687,plain,
    ( spl8_75
  <=> g1_pre_topc(u1_struct_0(sK3(sK1)),u1_pre_topc(sK3(sK1))) != sK3(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_75])])).

fof(f707,plain,
    ( ~ spl8_77
    | ~ spl8_79
    | spl8_75 ),
    inference(avatar_split_clause,[],[f693,f687,f705,f699])).

fof(f693,plain,
    ( ~ r2_hidden(sK4(g1_pre_topc(u1_struct_0(sK3(sK1)),u1_pre_topc(sK3(sK1))),sK3(sK1)),sK3(sK1))
    | ~ r2_hidden(sK4(g1_pre_topc(u1_struct_0(sK3(sK1)),u1_pre_topc(sK3(sK1))),sK3(sK1)),g1_pre_topc(u1_struct_0(sK3(sK1)),u1_pre_topc(sK3(sK1))))
    | ~ spl8_75 ),
    inference(extensionality_resolution,[],[f103,f688])).

fof(f103,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | ~ r2_hidden(sK4(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f67])).

fof(f692,plain,
    ( spl8_74
    | ~ spl8_63
    | spl8_1
    | ~ spl8_18 ),
    inference(avatar_split_clause,[],[f488,f199,f131,f658,f690])).

fof(f488,plain,
    ( ~ v2_pre_topc(sK1)
    | g1_pre_topc(u1_struct_0(sK3(sK1)),u1_pre_topc(sK3(sK1))) = sK3(sK1)
    | ~ spl8_1
    | ~ spl8_18 ),
    inference(subsumption_resolution,[],[f479,f132])).

fof(f479,plain,
    ( ~ v2_pre_topc(sK1)
    | g1_pre_topc(u1_struct_0(sK3(sK1)),u1_pre_topc(sK3(sK1))) = sK3(sK1)
    | v2_struct_0(sK1)
    | ~ spl8_18 ),
    inference(resolution,[],[f223,f200])).

fof(f223,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | g1_pre_topc(u1_struct_0(sK3(X0)),u1_pre_topc(sK3(X0))) = sK3(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f222,f204])).

fof(f204,plain,(
    ! [X0] :
      ( l1_pre_topc(sK3(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f203])).

fof(f203,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | l1_pre_topc(sK3(X0)) ) ),
    inference(resolution,[],[f92,f119])).

fof(f119,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f81])).

fof(f81,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t115_tmap_1.p',dt_m1_pre_topc)).

fof(f92,plain,(
    ! [X0] :
      ( m1_pre_topc(sK3(X0),X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_tsep_1(X1,X0)
          & v2_pre_topc(X1)
          & v1_pre_topc(X1)
          & ~ v2_struct_0(X1)
          & m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_tsep_1(X1,X0)
          & v2_pre_topc(X1)
          & v1_pre_topc(X1)
          & ~ v2_struct_0(X1)
          & m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f53])).

fof(f53,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( v1_tsep_1(X1,X0)
          & v2_pre_topc(X1)
          & v1_pre_topc(X1)
          & ~ v2_struct_0(X1)
          & m1_pre_topc(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t115_tmap_1.p',rc2_tsep_1)).

fof(f222,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK3(X0))
      | g1_pre_topc(u1_struct_0(sK3(X0)),u1_pre_topc(sK3(X0))) = sK3(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f113,f94])).

fof(f94,plain,(
    ! [X0] :
      ( v1_pre_topc(sK3(X0))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f685,plain,
    ( spl8_72
    | ~ spl8_18
    | ~ spl8_24 ),
    inference(avatar_split_clause,[],[f495,f262,f199,f683])).

fof(f683,plain,
    ( spl8_72
  <=> u1_pre_topc(sK2) = k4_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),u1_pre_topc(sK2),u1_pre_topc(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_72])])).

fof(f495,plain,
    ( u1_pre_topc(sK2) = k4_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),u1_pre_topc(sK2),u1_pre_topc(sK2))
    | ~ spl8_18
    | ~ spl8_24 ),
    inference(subsumption_resolution,[],[f492,f200])).

fof(f492,plain,
    ( u1_pre_topc(sK2) = k4_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),u1_pre_topc(sK2),u1_pre_topc(sK2))
    | ~ l1_pre_topc(sK1)
    | ~ spl8_24 ),
    inference(resolution,[],[f238,f263])).

fof(f238,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
      | k4_subset_1(k1_zfmisc_1(u1_struct_0(X1)),X0,X0) = X0
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f98,f114])).

fof(f678,plain,
    ( spl8_70
    | spl8_3
    | ~ spl8_4
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f487,f152,f145,f138,f676])).

fof(f676,plain,
    ( spl8_70
  <=> g1_pre_topc(u1_struct_0(sK3(sK0)),u1_pre_topc(sK3(sK0))) = sK3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_70])])).

fof(f487,plain,
    ( g1_pre_topc(u1_struct_0(sK3(sK0)),u1_pre_topc(sK3(sK0))) = sK3(sK0)
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f486,f139])).

fof(f486,plain,
    ( g1_pre_topc(u1_struct_0(sK3(sK0)),u1_pre_topc(sK3(sK0))) = sK3(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_4
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f478,f146])).

fof(f478,plain,
    ( ~ v2_pre_topc(sK0)
    | g1_pre_topc(u1_struct_0(sK3(sK0)),u1_pre_topc(sK3(sK0))) = sK3(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_6 ),
    inference(resolution,[],[f223,f153])).

fof(f671,plain,
    ( ~ spl8_63
    | spl8_68
    | spl8_1
    | ~ spl8_18
    | ~ spl8_30 ),
    inference(avatar_split_clause,[],[f362,f343,f199,f131,f669,f658])).

fof(f669,plain,
    ( spl8_68
  <=> ! [X5] :
        ( ~ m1_pre_topc(X5,sK2)
        | v1_pre_topc(k6_tmap_1(sK1,u1_struct_0(X5))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_68])])).

fof(f362,plain,
    ( ! [X5] :
        ( ~ m1_pre_topc(X5,sK2)
        | ~ v2_pre_topc(sK1)
        | v1_pre_topc(k6_tmap_1(sK1,u1_struct_0(X5))) )
    | ~ spl8_1
    | ~ spl8_18
    | ~ spl8_30 ),
    inference(subsumption_resolution,[],[f361,f132])).

fof(f361,plain,
    ( ! [X5] :
        ( ~ m1_pre_topc(X5,sK2)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | v1_pre_topc(k6_tmap_1(sK1,u1_struct_0(X5))) )
    | ~ spl8_18
    | ~ spl8_30 ),
    inference(subsumption_resolution,[],[f351,f200])).

fof(f351,plain,
    ( ! [X5] :
        ( ~ m1_pre_topc(X5,sK2)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(sK1)
        | v1_pre_topc(k6_tmap_1(sK1,u1_struct_0(X5))) )
    | ~ spl8_30 ),
    inference(resolution,[],[f344,f104])).

fof(f667,plain,
    ( ~ spl8_63
    | spl8_66
    | spl8_1
    | ~ spl8_18
    | ~ spl8_30 ),
    inference(avatar_split_clause,[],[f360,f343,f199,f131,f665,f658])).

fof(f665,plain,
    ( spl8_66
  <=> ! [X4] :
        ( ~ m1_pre_topc(X4,sK2)
        | v2_pre_topc(k6_tmap_1(sK1,u1_struct_0(X4))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_66])])).

fof(f360,plain,
    ( ! [X4] :
        ( ~ m1_pre_topc(X4,sK2)
        | ~ v2_pre_topc(sK1)
        | v2_pre_topc(k6_tmap_1(sK1,u1_struct_0(X4))) )
    | ~ spl8_1
    | ~ spl8_18
    | ~ spl8_30 ),
    inference(subsumption_resolution,[],[f359,f132])).

fof(f359,plain,
    ( ! [X4] :
        ( ~ m1_pre_topc(X4,sK2)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | v2_pre_topc(k6_tmap_1(sK1,u1_struct_0(X4))) )
    | ~ spl8_18
    | ~ spl8_30 ),
    inference(subsumption_resolution,[],[f350,f200])).

fof(f350,plain,
    ( ! [X4] :
        ( ~ m1_pre_topc(X4,sK2)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(sK1)
        | v2_pre_topc(k6_tmap_1(sK1,u1_struct_0(X4))) )
    | ~ spl8_30 ),
    inference(resolution,[],[f344,f105])).

fof(f105,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | v2_pre_topc(k6_tmap_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f663,plain,
    ( ~ spl8_63
    | spl8_64
    | spl8_1
    | ~ spl8_18
    | ~ spl8_30 ),
    inference(avatar_split_clause,[],[f358,f343,f199,f131,f661,f658])).

fof(f661,plain,
    ( spl8_64
  <=> ! [X3] :
        ( ~ m1_pre_topc(X3,sK2)
        | l1_pre_topc(k6_tmap_1(sK1,u1_struct_0(X3))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_64])])).

fof(f358,plain,
    ( ! [X3] :
        ( ~ m1_pre_topc(X3,sK2)
        | ~ v2_pre_topc(sK1)
        | l1_pre_topc(k6_tmap_1(sK1,u1_struct_0(X3))) )
    | ~ spl8_1
    | ~ spl8_18
    | ~ spl8_30 ),
    inference(subsumption_resolution,[],[f357,f132])).

fof(f357,plain,
    ( ! [X3] :
        ( ~ m1_pre_topc(X3,sK2)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | l1_pre_topc(k6_tmap_1(sK1,u1_struct_0(X3))) )
    | ~ spl8_18
    | ~ spl8_30 ),
    inference(subsumption_resolution,[],[f349,f200])).

fof(f349,plain,
    ( ! [X3] :
        ( ~ m1_pre_topc(X3,sK2)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(sK1)
        | l1_pre_topc(k6_tmap_1(sK1,u1_struct_0(X3))) )
    | ~ spl8_30 ),
    inference(resolution,[],[f344,f106])).

fof(f653,plain,
    ( ~ spl8_20
    | ~ spl8_60 ),
    inference(avatar_contradiction_clause,[],[f652])).

fof(f652,plain,
    ( $false
    | ~ spl8_20
    | ~ spl8_60 ),
    inference(subsumption_resolution,[],[f651,f210])).

fof(f651,plain,
    ( ~ l1_pre_topc(sK2)
    | ~ spl8_60 ),
    inference(resolution,[],[f648,f118])).

fof(f648,plain,
    ( ! [X12] : ~ m1_pre_topc(X12,sK2)
    | ~ spl8_60 ),
    inference(avatar_component_clause,[],[f647])).

fof(f649,plain,
    ( spl8_58
    | spl8_60
    | ~ spl8_30 ),
    inference(avatar_split_clause,[],[f355,f343,f647,f644])).

fof(f644,plain,
    ( spl8_58
  <=> ! [X13] : k9_subset_1(u1_struct_0(sK1),X13,X13) = X13 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_58])])).

fof(f355,plain,
    ( ! [X12,X13] :
        ( ~ m1_pre_topc(X12,sK2)
        | k9_subset_1(u1_struct_0(sK1),X13,X13) = X13 )
    | ~ spl8_30 ),
    inference(resolution,[],[f344,f100])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X1) = X1 ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t115_tmap_1.p',idempotence_k9_subset_1)).

fof(f606,plain,
    ( spl8_56
    | spl8_3
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f527,f159,f152,f145,f138,f604])).

fof(f527,plain,
    ( k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f526,f139])).

fof(f526,plain,
    ( v2_struct_0(sK0)
    | k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f525,f146])).

fof(f525,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | ~ spl8_6
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f519,f153])).

fof(f519,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | ~ spl8_8 ),
    inference(resolution,[],[f306,f160])).

fof(f306,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f305,f117])).

fof(f305,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(k8_tmap_1(X0,X1))
      | v2_struct_0(X0)
      | k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f304,f116])).

fof(f116,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(k8_tmap_1(X0,X1))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f304,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v2_pre_topc(k8_tmap_1(X0,X1))
      | ~ l1_pre_topc(k8_tmap_1(X0,X1))
      | v2_struct_0(X0)
      | k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f303,f115])).

fof(f303,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_pre_topc(k8_tmap_1(X0,X1))
      | ~ v2_pre_topc(k8_tmap_1(X0,X1))
      | ~ l1_pre_topc(k8_tmap_1(X0,X1))
      | v2_struct_0(X0)
      | k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1)) ) ),
    inference(duplicate_literal_removal,[],[f300])).

fof(f300,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_pre_topc(k8_tmap_1(X0,X1))
      | ~ v2_pre_topc(k8_tmap_1(X0,X1))
      | ~ l1_pre_topc(k8_tmap_1(X0,X1))
      | v2_struct_0(X0)
      | k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f125,f112])).

fof(f125,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_pre_topc(k8_tmap_1(X0,X1))
      | ~ v2_pre_topc(k8_tmap_1(X0,X1))
      | ~ l1_pre_topc(k8_tmap_1(X0,X1))
      | v2_struct_0(X0)
      | k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1)) ) ),
    inference(equality_resolution,[],[f124])).

fof(f124,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X2)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | k6_tmap_1(X0,u1_struct_0(X1)) = X2
      | k8_tmap_1(X0,X1) != X2 ) ),
    inference(equality_resolution,[],[f108])).

fof(f108,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X1) != X3
      | k6_tmap_1(X0,X3) = X2
      | k8_tmap_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f73])).

fof(f467,plain,
    ( ~ spl8_55
    | ~ spl8_18
    | spl8_29 ),
    inference(avatar_split_clause,[],[f401,f336,f199,f465])).

fof(f465,plain,
    ( spl8_55
  <=> ~ m1_pre_topc(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_55])])).

fof(f336,plain,
    ( spl8_29
  <=> ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_29])])).

fof(f401,plain,
    ( ~ m1_pre_topc(sK1,sK1)
    | ~ spl8_18
    | ~ spl8_29 ),
    inference(subsumption_resolution,[],[f399,f200])).

fof(f399,plain,
    ( ~ m1_pre_topc(sK1,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ spl8_29 ),
    inference(resolution,[],[f337,f112])).

fof(f337,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl8_29 ),
    inference(avatar_component_clause,[],[f336])).

fof(f437,plain,
    ( ~ spl8_53
    | ~ spl8_12
    | ~ spl8_18
    | spl8_29 ),
    inference(avatar_split_clause,[],[f400,f336,f199,f173,f435])).

fof(f435,plain,
    ( spl8_53
  <=> ~ m1_pre_topc(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_53])])).

fof(f400,plain,
    ( ~ m1_pre_topc(sK2,sK1)
    | ~ spl8_12
    | ~ spl8_18
    | ~ spl8_29 ),
    inference(subsumption_resolution,[],[f397,f200])).

fof(f397,plain,
    ( ~ m1_pre_topc(sK2,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ spl8_12
    | ~ spl8_29 ),
    inference(resolution,[],[f337,f220])).

fof(f430,plain,
    ( ~ spl8_51
    | spl8_29
    | ~ spl8_30 ),
    inference(avatar_split_clause,[],[f398,f343,f336,f428])).

fof(f428,plain,
    ( spl8_51
  <=> ~ m1_pre_topc(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_51])])).

fof(f398,plain,
    ( ~ m1_pre_topc(sK1,sK2)
    | ~ spl8_29
    | ~ spl8_30 ),
    inference(resolution,[],[f337,f344])).

fof(f423,plain,
    ( spl8_3
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_8
    | spl8_47 ),
    inference(avatar_contradiction_clause,[],[f422])).

fof(f422,plain,
    ( $false
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_47 ),
    inference(subsumption_resolution,[],[f421,f139])).

fof(f421,plain,
    ( v2_struct_0(sK0)
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_47 ),
    inference(subsumption_resolution,[],[f420,f160])).

fof(f420,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0)
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_47 ),
    inference(subsumption_resolution,[],[f419,f153])).

fof(f419,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0)
    | ~ spl8_4
    | ~ spl8_47 ),
    inference(subsumption_resolution,[],[f418,f146])).

fof(f418,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0)
    | ~ spl8_47 ),
    inference(resolution,[],[f413,f116])).

fof(f413,plain,
    ( ~ v2_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ spl8_47 ),
    inference(avatar_component_clause,[],[f412])).

fof(f412,plain,
    ( spl8_47
  <=> ~ v2_pre_topc(k8_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_47])])).

fof(f417,plain,
    ( spl8_44
    | ~ spl8_47
    | spl8_48
    | ~ spl8_10
    | ~ spl8_12
    | ~ spl8_22 ),
    inference(avatar_split_clause,[],[f281,f212,f173,f166,f415,f412,f406])).

fof(f406,plain,
    ( spl8_44
  <=> v2_struct_0(k8_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_44])])).

fof(f415,plain,
    ( spl8_48
  <=> ! [X1] :
        ( u1_struct_0(sK1) = sK5(k8_tmap_1(sK0,sK1),sK2,X1)
        | k8_tmap_1(k8_tmap_1(sK0,sK1),sK2) = X1
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | ~ v1_pre_topc(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_48])])).

fof(f281,plain,
    ( ! [X1] :
        ( u1_struct_0(sK1) = sK5(k8_tmap_1(sK0,sK1),sK2,X1)
        | ~ v2_pre_topc(k8_tmap_1(sK0,sK1))
        | v2_struct_0(k8_tmap_1(sK0,sK1))
        | ~ v1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | k8_tmap_1(k8_tmap_1(sK0,sK1),sK2) = X1 )
    | ~ spl8_10
    | ~ spl8_12
    | ~ spl8_22 ),
    inference(forward_demodulation,[],[f280,f174])).

fof(f280,plain,
    ( ! [X1] :
        ( ~ v2_pre_topc(k8_tmap_1(sK0,sK1))
        | v2_struct_0(k8_tmap_1(sK0,sK1))
        | ~ v1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | u1_struct_0(sK2) = sK5(k8_tmap_1(sK0,sK1),sK2,X1)
        | k8_tmap_1(k8_tmap_1(sK0,sK1),sK2) = X1 )
    | ~ spl8_10
    | ~ spl8_22 ),
    inference(subsumption_resolution,[],[f272,f213])).

fof(f272,plain,
    ( ! [X1] :
        ( ~ v2_pre_topc(k8_tmap_1(sK0,sK1))
        | ~ l1_pre_topc(k8_tmap_1(sK0,sK1))
        | v2_struct_0(k8_tmap_1(sK0,sK1))
        | ~ v1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | u1_struct_0(sK2) = sK5(k8_tmap_1(sK0,sK1),sK2,X1)
        | k8_tmap_1(k8_tmap_1(sK0,sK1),sK2) = X1 )
    | ~ spl8_10 ),
    inference(resolution,[],[f110,f167])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ v1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X2)
      | u1_struct_0(X1) = sK5(X0,X1,X2)
      | k8_tmap_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f73])).

fof(f396,plain,
    ( spl8_32
    | ~ spl8_35
    | spl8_42
    | ~ spl8_12
    | ~ spl8_20 ),
    inference(avatar_split_clause,[],[f297,f209,f173,f394,f373,f367])).

fof(f367,plain,
    ( spl8_32
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_32])])).

fof(f373,plain,
    ( spl8_35
  <=> ~ v2_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_35])])).

fof(f394,plain,
    ( spl8_42
  <=> ! [X1,X0] :
        ( m1_subset_1(sK5(sK2,X0,X1),k1_zfmisc_1(u1_struct_0(sK1)))
        | k8_tmap_1(sK2,X0) = X1
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | ~ v1_pre_topc(X1)
        | ~ m1_pre_topc(X0,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_42])])).

fof(f297,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(sK5(sK2,X0,X1),k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ v2_pre_topc(sK2)
        | ~ m1_pre_topc(X0,sK2)
        | ~ v1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(sK2)
        | k8_tmap_1(sK2,X0) = X1 )
    | ~ spl8_12
    | ~ spl8_20 ),
    inference(subsumption_resolution,[],[f293,f210])).

fof(f293,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(sK5(sK2,X0,X1),k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ v2_pre_topc(sK2)
        | ~ l1_pre_topc(sK2)
        | ~ m1_pre_topc(X0,sK2)
        | ~ v1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(sK2)
        | k8_tmap_1(sK2,X0) = X1 )
    | ~ spl8_12 ),
    inference(superposition,[],[f109,f174])).

fof(f386,plain,
    ( spl8_32
    | ~ spl8_35
    | spl8_40
    | ~ spl8_12
    | ~ spl8_20 ),
    inference(avatar_split_clause,[],[f251,f209,f173,f384,f373,f367])).

fof(f384,plain,
    ( spl8_40
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | l1_pre_topc(k6_tmap_1(sK2,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_40])])).

fof(f251,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2)
        | l1_pre_topc(k6_tmap_1(sK2,X0)) )
    | ~ spl8_12
    | ~ spl8_20 ),
    inference(subsumption_resolution,[],[f249,f210])).

fof(f249,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ v2_pre_topc(sK2)
        | ~ l1_pre_topc(sK2)
        | v2_struct_0(sK2)
        | l1_pre_topc(k6_tmap_1(sK2,X0)) )
    | ~ spl8_12 ),
    inference(superposition,[],[f106,f174])).

fof(f382,plain,
    ( spl8_32
    | ~ spl8_35
    | spl8_38
    | ~ spl8_12
    | ~ spl8_20 ),
    inference(avatar_split_clause,[],[f247,f209,f173,f380,f373,f367])).

fof(f380,plain,
    ( spl8_38
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | v2_pre_topc(k6_tmap_1(sK2,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_38])])).

fof(f247,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2)
        | v2_pre_topc(k6_tmap_1(sK2,X0)) )
    | ~ spl8_12
    | ~ spl8_20 ),
    inference(subsumption_resolution,[],[f245,f210])).

fof(f245,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ v2_pre_topc(sK2)
        | ~ l1_pre_topc(sK2)
        | v2_struct_0(sK2)
        | v2_pre_topc(k6_tmap_1(sK2,X0)) )
    | ~ spl8_12 ),
    inference(superposition,[],[f105,f174])).

fof(f378,plain,
    ( spl8_32
    | ~ spl8_35
    | spl8_36
    | ~ spl8_12
    | ~ spl8_20 ),
    inference(avatar_split_clause,[],[f243,f209,f173,f376,f373,f367])).

fof(f376,plain,
    ( spl8_36
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | v1_pre_topc(k6_tmap_1(sK2,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_36])])).

fof(f243,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2)
        | v1_pre_topc(k6_tmap_1(sK2,X0)) )
    | ~ spl8_12
    | ~ spl8_20 ),
    inference(subsumption_resolution,[],[f241,f210])).

fof(f241,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ v2_pre_topc(sK2)
        | ~ l1_pre_topc(sK2)
        | v2_struct_0(sK2)
        | v1_pre_topc(k6_tmap_1(sK2,X0)) )
    | ~ spl8_12 ),
    inference(superposition,[],[f104,f174])).

fof(f345,plain,
    ( ~ spl8_21
    | spl8_30
    | ~ spl8_12 ),
    inference(avatar_split_clause,[],[f221,f173,f343,f206])).

fof(f206,plain,
    ( spl8_21
  <=> ~ l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).

fof(f221,plain,
    ( ! [X0] :
        ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_pre_topc(X0,sK2)
        | ~ l1_pre_topc(sK2) )
    | ~ spl8_12 ),
    inference(superposition,[],[f112,f174])).

fof(f341,plain,
    ( ~ spl8_27
    | spl8_28
    | ~ spl8_12
    | ~ spl8_20 ),
    inference(avatar_split_clause,[],[f328,f209,f173,f339,f333])).

fof(f333,plain,
    ( spl8_27
  <=> ~ m1_pre_topc(sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).

fof(f339,plain,
    ( spl8_28
  <=> m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).

fof(f328,plain,
    ( m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_pre_topc(sK2,sK2)
    | ~ spl8_12
    | ~ spl8_20 ),
    inference(subsumption_resolution,[],[f320,f210])).

fof(f320,plain,
    ( m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_pre_topc(sK2,sK2)
    | ~ l1_pre_topc(sK2)
    | ~ spl8_12 ),
    inference(superposition,[],[f220,f174])).

fof(f264,plain,
    ( ~ spl8_21
    | spl8_24
    | ~ spl8_12 ),
    inference(avatar_split_clause,[],[f202,f173,f262,f206])).

fof(f202,plain,
    ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK2)
    | ~ spl8_12 ),
    inference(superposition,[],[f114,f174])).

fof(f237,plain,
    ( spl8_3
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_8
    | spl8_23 ),
    inference(avatar_contradiction_clause,[],[f236])).

fof(f236,plain,
    ( $false
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_23 ),
    inference(subsumption_resolution,[],[f235,f139])).

fof(f235,plain,
    ( v2_struct_0(sK0)
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_23 ),
    inference(subsumption_resolution,[],[f234,f160])).

fof(f234,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0)
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_23 ),
    inference(subsumption_resolution,[],[f233,f153])).

fof(f233,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0)
    | ~ spl8_4
    | ~ spl8_23 ),
    inference(subsumption_resolution,[],[f232,f146])).

fof(f232,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0)
    | ~ spl8_23 ),
    inference(resolution,[],[f117,f216])).

fof(f216,plain,
    ( ~ l1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ spl8_23 ),
    inference(avatar_component_clause,[],[f215])).

fof(f215,plain,
    ( spl8_23
  <=> ~ l1_pre_topc(k8_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).

fof(f217,plain,
    ( spl8_20
    | ~ spl8_23
    | ~ spl8_10 ),
    inference(avatar_split_clause,[],[f191,f166,f215,f209])).

fof(f191,plain,
    ( ~ l1_pre_topc(k8_tmap_1(sK0,sK1))
    | l1_pre_topc(sK2)
    | ~ spl8_10 ),
    inference(resolution,[],[f119,f167])).

fof(f201,plain,
    ( spl8_18
    | ~ spl8_6
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f194,f159,f152,f199])).

fof(f194,plain,
    ( l1_pre_topc(sK1)
    | ~ spl8_6
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f190,f153])).

fof(f190,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK1)
    | ~ spl8_8 ),
    inference(resolution,[],[f119,f160])).

fof(f189,plain,(
    spl8_16 ),
    inference(avatar_split_clause,[],[f120,f187])).

fof(f187,plain,
    ( spl8_16
  <=> l1_pre_topc(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f120,plain,(
    l1_pre_topc(sK7) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,axiom,(
    ? [X0] : l1_pre_topc(X0) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t115_tmap_1.p',existence_l1_pre_topc)).

fof(f182,plain,(
    ~ spl8_15 ),
    inference(avatar_split_clause,[],[f126,f180])).

fof(f126,plain,(
    ~ v1_tsep_1(sK2,k8_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f82,f83])).

fof(f83,plain,(
    m1_pre_topc(sK2,k8_tmap_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_pre_topc(X2,k8_tmap_1(X0,X1))
                | ~ v1_tsep_1(X2,k8_tmap_1(X0,X1)) )
              & u1_struct_0(X1) = u1_struct_0(X2)
              & m1_pre_topc(X2,k8_tmap_1(X0,X1)) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_pre_topc(X2,k8_tmap_1(X0,X1))
                | ~ v1_tsep_1(X2,k8_tmap_1(X0,X1)) )
              & u1_struct_0(X1) = u1_struct_0(X2)
              & m1_pre_topc(X2,k8_tmap_1(X0,X1)) )
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
                ( m1_pre_topc(X2,k8_tmap_1(X0,X1))
               => ( u1_struct_0(X1) = u1_struct_0(X2)
                 => ( m1_pre_topc(X2,k8_tmap_1(X0,X1))
                    & v1_tsep_1(X2,k8_tmap_1(X0,X1)) ) ) ) ) ) ),
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
              ( m1_pre_topc(X2,k8_tmap_1(X0,X1))
             => ( u1_struct_0(X1) = u1_struct_0(X2)
               => ( m1_pre_topc(X2,k8_tmap_1(X0,X1))
                  & v1_tsep_1(X2,k8_tmap_1(X0,X1)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t115_tmap_1.p',t115_tmap_1)).

fof(f82,plain,
    ( ~ v1_tsep_1(sK2,k8_tmap_1(sK0,sK1))
    | ~ m1_pre_topc(sK2,k8_tmap_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f55])).

fof(f175,plain,(
    spl8_12 ),
    inference(avatar_split_clause,[],[f84,f173])).

fof(f84,plain,(
    u1_struct_0(sK1) = u1_struct_0(sK2) ),
    inference(cnf_transformation,[],[f55])).

fof(f168,plain,(
    spl8_10 ),
    inference(avatar_split_clause,[],[f83,f166])).

fof(f161,plain,(
    spl8_8 ),
    inference(avatar_split_clause,[],[f86,f159])).

fof(f86,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f55])).

fof(f154,plain,(
    spl8_6 ),
    inference(avatar_split_clause,[],[f89,f152])).

fof(f89,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f55])).

fof(f147,plain,(
    spl8_4 ),
    inference(avatar_split_clause,[],[f88,f145])).

fof(f88,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f55])).

fof(f140,plain,(
    ~ spl8_3 ),
    inference(avatar_split_clause,[],[f87,f138])).

fof(f87,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f55])).

fof(f133,plain,(
    ~ spl8_1 ),
    inference(avatar_split_clause,[],[f85,f131])).

fof(f85,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f55])).
%------------------------------------------------------------------------------
