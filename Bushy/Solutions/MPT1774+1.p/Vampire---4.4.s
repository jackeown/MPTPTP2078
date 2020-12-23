%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tmap_1__t85_tmap_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:20 EDT 2019

% Result     : Theorem 0.76s
% Output     : Refutation 0.76s
% Verified   : 
% Statistics : Number of formulae       :  301 ( 702 expanded)
%              Number of leaves         :   68 ( 261 expanded)
%              Depth                    :   29
%              Number of atoms          : 1853 (4919 expanded)
%              Number of equality atoms :   21 ( 128 expanded)
%              Maximal formula depth    :   32 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f685,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f123,f130,f137,f144,f151,f158,f165,f172,f179,f186,f193,f200,f207,f214,f221,f228,f235,f242,f249,f256,f263,f270,f277,f290,f291,f301,f323,f348,f384,f403,f410,f437,f444,f452,f453,f454,f465,f472,f485,f498,f541,f577,f596,f600,f607,f617,f667,f684])).

fof(f684,plain,
    ( ~ spl11_0
    | spl11_3
    | spl11_5
    | spl11_7
    | ~ spl11_8
    | ~ spl11_10
    | spl11_13
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_18
    | ~ spl11_20
    | ~ spl11_24
    | ~ spl11_26
    | ~ spl11_28
    | ~ spl11_30
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40
    | spl11_47
    | ~ spl11_48
    | ~ spl11_94 ),
    inference(avatar_contradiction_clause,[],[f683])).

fof(f683,plain,
    ( $false
    | ~ spl11_0
    | ~ spl11_3
    | ~ spl11_5
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_13
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_18
    | ~ spl11_20
    | ~ spl11_24
    | ~ spl11_26
    | ~ spl11_28
    | ~ spl11_30
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40
    | ~ spl11_47
    | ~ spl11_48
    | ~ spl11_94 ),
    inference(subsumption_resolution,[],[f682,f680])).

fof(f680,plain,
    ( v3_pre_topc(sK5,sK3)
    | ~ spl11_10
    | ~ spl11_18
    | ~ spl11_26
    | ~ spl11_36
    | ~ spl11_94 ),
    inference(subsumption_resolution,[],[f671,f213])).

fof(f213,plain,
    ( m1_pre_topc(sK3,sK1)
    | ~ spl11_26 ),
    inference(avatar_component_clause,[],[f212])).

fof(f212,plain,
    ( spl11_26
  <=> m1_pre_topc(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_26])])).

fof(f671,plain,
    ( v3_pre_topc(sK5,sK3)
    | ~ m1_pre_topc(sK3,sK1)
    | ~ spl11_10
    | ~ spl11_18
    | ~ spl11_36
    | ~ spl11_94 ),
    inference(resolution,[],[f666,f561])).

fof(f561,plain,
    ( ! [X3] :
        ( ~ r1_tarski(sK5,u1_struct_0(X3))
        | v3_pre_topc(sK5,X3)
        | ~ m1_pre_topc(X3,sK1) )
    | ~ spl11_10
    | ~ spl11_18
    | ~ spl11_36 ),
    inference(subsumption_resolution,[],[f560,f157])).

fof(f157,plain,
    ( l1_pre_topc(sK1)
    | ~ spl11_10 ),
    inference(avatar_component_clause,[],[f156])).

fof(f156,plain,
    ( spl11_10
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_10])])).

fof(f560,plain,
    ( ! [X3] :
        ( ~ m1_pre_topc(X3,sK1)
        | ~ l1_pre_topc(sK1)
        | v3_pre_topc(sK5,X3)
        | ~ r1_tarski(sK5,u1_struct_0(X3)) )
    | ~ spl11_18
    | ~ spl11_36 ),
    inference(subsumption_resolution,[],[f558,f185])).

fof(f185,plain,
    ( v3_pre_topc(sK5,sK1)
    | ~ spl11_18 ),
    inference(avatar_component_clause,[],[f184])).

fof(f184,plain,
    ( spl11_18
  <=> v3_pre_topc(sK5,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_18])])).

fof(f558,plain,
    ( ! [X3] :
        ( ~ m1_pre_topc(X3,sK1)
        | ~ v3_pre_topc(sK5,sK1)
        | ~ l1_pre_topc(sK1)
        | v3_pre_topc(sK5,X3)
        | ~ r1_tarski(sK5,u1_struct_0(X3)) )
    | ~ spl11_36 ),
    inference(resolution,[],[f361,f248])).

fof(f248,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl11_36 ),
    inference(avatar_component_clause,[],[f247])).

fof(f247,plain,
    ( spl11_36
  <=> m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_36])])).

fof(f361,plain,(
    ! [X2,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_pre_topc(X3,X2)
      | ~ v3_pre_topc(X1,X2)
      | ~ l1_pre_topc(X2)
      | v3_pre_topc(X1,X3)
      | ~ r1_tarski(X1,u1_struct_0(X3)) ) ),
    inference(resolution,[],[f113,f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t85_tmap_1.p',t3_subset)).

fof(f113,plain,(
    ! [X2,X0,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X2,X0)
      | ~ v3_pre_topc(X3,X0)
      | ~ l1_pre_topc(X0)
      | v3_pre_topc(X3,X2) ) ),
    inference(equality_resolution,[],[f91])).

fof(f91,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X2,X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | X1 != X3
      | v3_pre_topc(X3,X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v3_pre_topc(X3,X2)
                  | X1 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v3_pre_topc(X3,X2)
                  | X1 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( v3_pre_topc(X1,X0)
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
                   => ( X1 = X3
                     => v3_pre_topc(X3,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t85_tmap_1.p',t33_tops_2)).

fof(f666,plain,
    ( r1_tarski(sK5,u1_struct_0(sK3))
    | ~ spl11_94 ),
    inference(avatar_component_clause,[],[f665])).

fof(f665,plain,
    ( spl11_94
  <=> r1_tarski(sK5,u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_94])])).

fof(f682,plain,
    ( ~ v3_pre_topc(sK5,sK3)
    | ~ spl11_0
    | ~ spl11_3
    | ~ spl11_5
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_13
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_20
    | ~ spl11_24
    | ~ spl11_26
    | ~ spl11_28
    | ~ spl11_30
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_38
    | ~ spl11_40
    | ~ spl11_47
    | ~ spl11_48
    | ~ spl11_94 ),
    inference(subsumption_resolution,[],[f681,f227])).

fof(f227,plain,
    ( r1_tarski(sK5,u1_struct_0(sK2))
    | ~ spl11_30 ),
    inference(avatar_component_clause,[],[f226])).

fof(f226,plain,
    ( spl11_30
  <=> r1_tarski(sK5,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_30])])).

fof(f681,plain,
    ( ~ r1_tarski(sK5,u1_struct_0(sK2))
    | ~ v3_pre_topc(sK5,sK3)
    | ~ spl11_0
    | ~ spl11_3
    | ~ spl11_5
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_13
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_20
    | ~ spl11_24
    | ~ spl11_26
    | ~ spl11_28
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_38
    | ~ spl11_40
    | ~ spl11_47
    | ~ spl11_48
    | ~ spl11_94 ),
    inference(subsumption_resolution,[],[f672,f192])).

fof(f192,plain,
    ( r2_hidden(sK6,sK5)
    | ~ spl11_20 ),
    inference(avatar_component_clause,[],[f191])).

fof(f191,plain,
    ( spl11_20
  <=> r2_hidden(sK6,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_20])])).

fof(f672,plain,
    ( ~ r2_hidden(sK6,sK5)
    | ~ r1_tarski(sK5,u1_struct_0(sK2))
    | ~ v3_pre_topc(sK5,sK3)
    | ~ spl11_0
    | ~ spl11_3
    | ~ spl11_5
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_13
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_24
    | ~ spl11_26
    | ~ spl11_28
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_38
    | ~ spl11_40
    | ~ spl11_47
    | ~ spl11_48
    | ~ spl11_94 ),
    inference(resolution,[],[f666,f507])).

fof(f507,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK3))
        | ~ r2_hidden(sK6,X0)
        | ~ r1_tarski(X0,u1_struct_0(sK2))
        | ~ v3_pre_topc(X0,sK3) )
    | ~ spl11_0
    | ~ spl11_3
    | ~ spl11_5
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_13
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_24
    | ~ spl11_26
    | ~ spl11_28
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_38
    | ~ spl11_40
    | ~ spl11_47
    | ~ spl11_48 ),
    inference(resolution,[],[f430,f95])).

fof(f430,plain,
    ( ! [X7] :
        ( ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ v3_pre_topc(X7,sK3)
        | ~ r2_hidden(sK6,X7)
        | ~ r1_tarski(X7,u1_struct_0(sK2)) )
    | ~ spl11_0
    | ~ spl11_3
    | ~ spl11_5
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_13
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_24
    | ~ spl11_26
    | ~ spl11_28
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_38
    | ~ spl11_40
    | ~ spl11_47
    | ~ spl11_48 ),
    inference(subsumption_resolution,[],[f429,f283])).

fof(f283,plain,
    ( ~ r1_tmap_1(sK3,sK0,sK4,sK6)
    | ~ spl11_47 ),
    inference(avatar_component_clause,[],[f282])).

fof(f282,plain,
    ( spl11_47
  <=> ~ r1_tmap_1(sK3,sK0,sK4,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_47])])).

fof(f429,plain,
    ( ! [X7] :
        ( ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ v3_pre_topc(X7,sK3)
        | ~ r2_hidden(sK6,X7)
        | ~ r1_tarski(X7,u1_struct_0(sK2))
        | r1_tmap_1(sK3,sK0,sK4,sK6) )
    | ~ spl11_0
    | ~ spl11_3
    | ~ spl11_5
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_13
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_24
    | ~ spl11_26
    | ~ spl11_28
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_38
    | ~ spl11_40
    | ~ spl11_48 ),
    inference(subsumption_resolution,[],[f428,f143])).

fof(f143,plain,
    ( ~ v2_struct_0(sK1)
    | ~ spl11_7 ),
    inference(avatar_component_clause,[],[f142])).

fof(f142,plain,
    ( spl11_7
  <=> ~ v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_7])])).

fof(f428,plain,
    ( ! [X7] :
        ( ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ v3_pre_topc(X7,sK3)
        | ~ r2_hidden(sK6,X7)
        | ~ r1_tarski(X7,u1_struct_0(sK2))
        | v2_struct_0(sK1)
        | r1_tmap_1(sK3,sK0,sK4,sK6) )
    | ~ spl11_0
    | ~ spl11_3
    | ~ spl11_5
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_13
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_24
    | ~ spl11_26
    | ~ spl11_28
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_38
    | ~ spl11_40
    | ~ spl11_48 ),
    inference(subsumption_resolution,[],[f427,f241])).

fof(f241,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ spl11_34 ),
    inference(avatar_component_clause,[],[f240])).

fof(f240,plain,
    ( spl11_34
  <=> m1_subset_1(sK6,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_34])])).

fof(f427,plain,
    ( ! [X7] :
        ( ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_subset_1(sK6,u1_struct_0(sK2))
        | ~ v3_pre_topc(X7,sK3)
        | ~ r2_hidden(sK6,X7)
        | ~ r1_tarski(X7,u1_struct_0(sK2))
        | v2_struct_0(sK1)
        | r1_tmap_1(sK3,sK0,sK4,sK6) )
    | ~ spl11_0
    | ~ spl11_3
    | ~ spl11_5
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_13
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_24
    | ~ spl11_26
    | ~ spl11_28
    | ~ spl11_32
    | ~ spl11_38
    | ~ spl11_40
    | ~ spl11_48 ),
    inference(subsumption_resolution,[],[f426,f234])).

fof(f234,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ spl11_32 ),
    inference(avatar_component_clause,[],[f233])).

fof(f233,plain,
    ( spl11_32
  <=> m1_subset_1(sK6,u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_32])])).

fof(f426,plain,
    ( ! [X7] :
        ( ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_subset_1(sK6,u1_struct_0(sK3))
        | ~ m1_subset_1(sK6,u1_struct_0(sK2))
        | ~ v3_pre_topc(X7,sK3)
        | ~ r2_hidden(sK6,X7)
        | ~ r1_tarski(X7,u1_struct_0(sK2))
        | v2_struct_0(sK1)
        | r1_tmap_1(sK3,sK0,sK4,sK6) )
    | ~ spl11_0
    | ~ spl11_3
    | ~ spl11_5
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_13
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_24
    | ~ spl11_26
    | ~ spl11_28
    | ~ spl11_38
    | ~ spl11_40
    | ~ spl11_48 ),
    inference(subsumption_resolution,[],[f425,f206])).

fof(f206,plain,
    ( m1_pre_topc(sK2,sK3)
    | ~ spl11_24 ),
    inference(avatar_component_clause,[],[f205])).

fof(f205,plain,
    ( spl11_24
  <=> m1_pre_topc(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_24])])).

fof(f425,plain,
    ( ! [X7] :
        ( ~ m1_pre_topc(sK2,sK3)
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_subset_1(sK6,u1_struct_0(sK3))
        | ~ m1_subset_1(sK6,u1_struct_0(sK2))
        | ~ v3_pre_topc(X7,sK3)
        | ~ r2_hidden(sK6,X7)
        | ~ r1_tarski(X7,u1_struct_0(sK2))
        | v2_struct_0(sK1)
        | r1_tmap_1(sK3,sK0,sK4,sK6) )
    | ~ spl11_0
    | ~ spl11_3
    | ~ spl11_5
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_13
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_26
    | ~ spl11_28
    | ~ spl11_38
    | ~ spl11_40
    | ~ spl11_48 ),
    inference(subsumption_resolution,[],[f424,f262])).

fof(f262,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
    | ~ spl11_40 ),
    inference(avatar_component_clause,[],[f261])).

fof(f261,plain,
    ( spl11_40
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_40])])).

fof(f424,plain,
    ( ! [X7] :
        ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
        | ~ m1_pre_topc(sK2,sK3)
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_subset_1(sK6,u1_struct_0(sK3))
        | ~ m1_subset_1(sK6,u1_struct_0(sK2))
        | ~ v3_pre_topc(X7,sK3)
        | ~ r2_hidden(sK6,X7)
        | ~ r1_tarski(X7,u1_struct_0(sK2))
        | v2_struct_0(sK1)
        | r1_tmap_1(sK3,sK0,sK4,sK6) )
    | ~ spl11_0
    | ~ spl11_3
    | ~ spl11_5
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_13
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_26
    | ~ spl11_28
    | ~ spl11_38
    | ~ spl11_48 ),
    inference(subsumption_resolution,[],[f423,f255])).

fof(f255,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
    | ~ spl11_38 ),
    inference(avatar_component_clause,[],[f254])).

fof(f254,plain,
    ( spl11_38
  <=> v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_38])])).

fof(f423,plain,
    ( ! [X7] :
        ( ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
        | ~ m1_pre_topc(sK2,sK3)
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_subset_1(sK6,u1_struct_0(sK3))
        | ~ m1_subset_1(sK6,u1_struct_0(sK2))
        | ~ v3_pre_topc(X7,sK3)
        | ~ r2_hidden(sK6,X7)
        | ~ r1_tarski(X7,u1_struct_0(sK2))
        | v2_struct_0(sK1)
        | r1_tmap_1(sK3,sK0,sK4,sK6) )
    | ~ spl11_0
    | ~ spl11_3
    | ~ spl11_5
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_13
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_26
    | ~ spl11_28
    | ~ spl11_48 ),
    inference(subsumption_resolution,[],[f422,f122])).

fof(f122,plain,
    ( v1_funct_1(sK4)
    | ~ spl11_0 ),
    inference(avatar_component_clause,[],[f121])).

fof(f121,plain,
    ( spl11_0
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_0])])).

fof(f422,plain,
    ( ! [X7] :
        ( ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
        | ~ m1_pre_topc(sK2,sK3)
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_subset_1(sK6,u1_struct_0(sK3))
        | ~ m1_subset_1(sK6,u1_struct_0(sK2))
        | ~ v3_pre_topc(X7,sK3)
        | ~ r2_hidden(sK6,X7)
        | ~ r1_tarski(X7,u1_struct_0(sK2))
        | v2_struct_0(sK1)
        | r1_tmap_1(sK3,sK0,sK4,sK6) )
    | ~ spl11_3
    | ~ spl11_5
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_13
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_26
    | ~ spl11_28
    | ~ spl11_48 ),
    inference(subsumption_resolution,[],[f421,f213])).

fof(f421,plain,
    ( ! [X7] :
        ( ~ m1_pre_topc(sK3,sK1)
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
        | ~ m1_pre_topc(sK2,sK3)
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_subset_1(sK6,u1_struct_0(sK3))
        | ~ m1_subset_1(sK6,u1_struct_0(sK2))
        | ~ v3_pre_topc(X7,sK3)
        | ~ r2_hidden(sK6,X7)
        | ~ r1_tarski(X7,u1_struct_0(sK2))
        | v2_struct_0(sK1)
        | r1_tmap_1(sK3,sK0,sK4,sK6) )
    | ~ spl11_3
    | ~ spl11_5
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_13
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_28
    | ~ spl11_48 ),
    inference(subsumption_resolution,[],[f420,f129])).

fof(f129,plain,
    ( ~ v2_struct_0(sK3)
    | ~ spl11_3 ),
    inference(avatar_component_clause,[],[f128])).

fof(f128,plain,
    ( spl11_3
  <=> ~ v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).

fof(f420,plain,
    ( ! [X7] :
        ( v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK1)
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
        | ~ m1_pre_topc(sK2,sK3)
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_subset_1(sK6,u1_struct_0(sK3))
        | ~ m1_subset_1(sK6,u1_struct_0(sK2))
        | ~ v3_pre_topc(X7,sK3)
        | ~ r2_hidden(sK6,X7)
        | ~ r1_tarski(X7,u1_struct_0(sK2))
        | v2_struct_0(sK1)
        | r1_tmap_1(sK3,sK0,sK4,sK6) )
    | ~ spl11_5
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_13
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_28
    | ~ spl11_48 ),
    inference(subsumption_resolution,[],[f419,f220])).

fof(f220,plain,
    ( m1_pre_topc(sK2,sK1)
    | ~ spl11_28 ),
    inference(avatar_component_clause,[],[f219])).

fof(f219,plain,
    ( spl11_28
  <=> m1_pre_topc(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_28])])).

fof(f419,plain,
    ( ! [X7] :
        ( ~ m1_pre_topc(sK2,sK1)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK1)
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
        | ~ m1_pre_topc(sK2,sK3)
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_subset_1(sK6,u1_struct_0(sK3))
        | ~ m1_subset_1(sK6,u1_struct_0(sK2))
        | ~ v3_pre_topc(X7,sK3)
        | ~ r2_hidden(sK6,X7)
        | ~ r1_tarski(X7,u1_struct_0(sK2))
        | v2_struct_0(sK1)
        | r1_tmap_1(sK3,sK0,sK4,sK6) )
    | ~ spl11_5
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_13
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_48 ),
    inference(subsumption_resolution,[],[f418,f136])).

fof(f136,plain,
    ( ~ v2_struct_0(sK2)
    | ~ spl11_5 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl11_5
  <=> ~ v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).

fof(f418,plain,
    ( ! [X7] :
        ( v2_struct_0(sK2)
        | ~ m1_pre_topc(sK2,sK1)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK1)
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
        | ~ m1_pre_topc(sK2,sK3)
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_subset_1(sK6,u1_struct_0(sK3))
        | ~ m1_subset_1(sK6,u1_struct_0(sK2))
        | ~ v3_pre_topc(X7,sK3)
        | ~ r2_hidden(sK6,X7)
        | ~ r1_tarski(X7,u1_struct_0(sK2))
        | v2_struct_0(sK1)
        | r1_tmap_1(sK3,sK0,sK4,sK6) )
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_13
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_48 ),
    inference(subsumption_resolution,[],[f417,f178])).

fof(f178,plain,
    ( l1_pre_topc(sK0)
    | ~ spl11_16 ),
    inference(avatar_component_clause,[],[f177])).

fof(f177,plain,
    ( spl11_16
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_16])])).

fof(f417,plain,
    ( ! [X7] :
        ( ~ l1_pre_topc(sK0)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(sK2,sK1)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK1)
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
        | ~ m1_pre_topc(sK2,sK3)
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_subset_1(sK6,u1_struct_0(sK3))
        | ~ m1_subset_1(sK6,u1_struct_0(sK2))
        | ~ v3_pre_topc(X7,sK3)
        | ~ r2_hidden(sK6,X7)
        | ~ r1_tarski(X7,u1_struct_0(sK2))
        | v2_struct_0(sK1)
        | r1_tmap_1(sK3,sK0,sK4,sK6) )
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_13
    | ~ spl11_14
    | ~ spl11_48 ),
    inference(subsumption_resolution,[],[f416,f171])).

fof(f171,plain,
    ( v2_pre_topc(sK0)
    | ~ spl11_14 ),
    inference(avatar_component_clause,[],[f170])).

fof(f170,plain,
    ( spl11_14
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_14])])).

fof(f416,plain,
    ( ! [X7] :
        ( ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(sK2,sK1)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK1)
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
        | ~ m1_pre_topc(sK2,sK3)
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_subset_1(sK6,u1_struct_0(sK3))
        | ~ m1_subset_1(sK6,u1_struct_0(sK2))
        | ~ v3_pre_topc(X7,sK3)
        | ~ r2_hidden(sK6,X7)
        | ~ r1_tarski(X7,u1_struct_0(sK2))
        | v2_struct_0(sK1)
        | r1_tmap_1(sK3,sK0,sK4,sK6) )
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_13
    | ~ spl11_48 ),
    inference(subsumption_resolution,[],[f415,f164])).

fof(f164,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl11_13 ),
    inference(avatar_component_clause,[],[f163])).

fof(f163,plain,
    ( spl11_13
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_13])])).

fof(f415,plain,
    ( ! [X7] :
        ( v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(sK2,sK1)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK1)
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
        | ~ m1_pre_topc(sK2,sK3)
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_subset_1(sK6,u1_struct_0(sK3))
        | ~ m1_subset_1(sK6,u1_struct_0(sK2))
        | ~ v3_pre_topc(X7,sK3)
        | ~ r2_hidden(sK6,X7)
        | ~ r1_tarski(X7,u1_struct_0(sK2))
        | v2_struct_0(sK1)
        | r1_tmap_1(sK3,sK0,sK4,sK6) )
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_48 ),
    inference(subsumption_resolution,[],[f414,f157])).

fof(f414,plain,
    ( ! [X7] :
        ( ~ l1_pre_topc(sK1)
        | v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(sK2,sK1)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK1)
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
        | ~ m1_pre_topc(sK2,sK3)
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_subset_1(sK6,u1_struct_0(sK3))
        | ~ m1_subset_1(sK6,u1_struct_0(sK2))
        | ~ v3_pre_topc(X7,sK3)
        | ~ r2_hidden(sK6,X7)
        | ~ r1_tarski(X7,u1_struct_0(sK2))
        | v2_struct_0(sK1)
        | r1_tmap_1(sK3,sK0,sK4,sK6) )
    | ~ spl11_8
    | ~ spl11_48 ),
    inference(subsumption_resolution,[],[f412,f150])).

fof(f150,plain,
    ( v2_pre_topc(sK1)
    | ~ spl11_8 ),
    inference(avatar_component_clause,[],[f149])).

fof(f149,plain,
    ( spl11_8
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_8])])).

fof(f412,plain,
    ( ! [X7] :
        ( ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(sK2,sK1)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK1)
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
        | ~ m1_pre_topc(sK2,sK3)
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_subset_1(sK6,u1_struct_0(sK3))
        | ~ m1_subset_1(sK6,u1_struct_0(sK2))
        | ~ v3_pre_topc(X7,sK3)
        | ~ r2_hidden(sK6,X7)
        | ~ r1_tarski(X7,u1_struct_0(sK2))
        | v2_struct_0(sK1)
        | r1_tmap_1(sK3,sK0,sK4,sK6) )
    | ~ spl11_48 ),
    inference(resolution,[],[f112,f286])).

fof(f286,plain,
    ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6)
    | ~ spl11_48 ),
    inference(avatar_component_clause,[],[f285])).

fof(f285,plain,
    ( spl11_48
  <=> r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_48])])).

fof(f112,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ m1_subset_1(X7,u1_struct_0(X3))
      | ~ m1_subset_1(X7,u1_struct_0(X2))
      | ~ v3_pre_topc(X5,X3)
      | ~ r2_hidden(X7,X5)
      | ~ r1_tarski(X5,u1_struct_0(X2))
      | v2_struct_0(X0)
      | r1_tmap_1(X3,X1,X4,X7) ) ),
    inference(equality_resolution,[],[f88])).

fof(f88,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X7,u1_struct_0(X2))
      | ~ v3_pre_topc(X5,X3)
      | ~ r2_hidden(X6,X5)
      | ~ r1_tarski(X5,u1_struct_0(X2))
      | X6 != X7
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
      | r1_tmap_1(X3,X1,X4,X6) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ! [X7] :
                                  ( ( r1_tmap_1(X3,X1,X4,X6)
                                  <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) )
                                  | X6 != X7
                                  | ~ r1_tarski(X5,u1_struct_0(X2))
                                  | ~ r2_hidden(X6,X5)
                                  | ~ v3_pre_topc(X5,X3)
                                  | ~ m1_subset_1(X7,u1_struct_0(X2)) )
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
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
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ! [X7] :
                                  ( ( r1_tmap_1(X3,X1,X4,X6)
                                  <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) )
                                  | X6 != X7
                                  | ~ r1_tarski(X5,u1_struct_0(X2))
                                  | ~ r2_hidden(X6,X5)
                                  | ~ v3_pre_topc(X5,X3)
                                  | ~ m1_subset_1(X7,u1_struct_0(X2)) )
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
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
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
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
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( m1_pre_topc(X2,X3)
                       => ! [X5] :
                            ( m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X3))
                               => ! [X7] :
                                    ( m1_subset_1(X7,u1_struct_0(X2))
                                   => ( ( X6 = X7
                                        & r1_tarski(X5,u1_struct_0(X2))
                                        & r2_hidden(X6,X5)
                                        & v3_pre_topc(X5,X3) )
                                     => ( r1_tmap_1(X3,X1,X4,X6)
                                      <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) ) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t85_tmap_1.p',t84_tmap_1)).

fof(f667,plain,
    ( spl11_94
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_24
    | ~ spl11_26
    | ~ spl11_28
    | ~ spl11_30 ),
    inference(avatar_split_clause,[],[f656,f226,f219,f212,f205,f156,f149,f665])).

fof(f656,plain,
    ( r1_tarski(sK5,u1_struct_0(sK3))
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_24
    | ~ spl11_26
    | ~ spl11_28
    | ~ spl11_30 ),
    inference(subsumption_resolution,[],[f655,f206])).

fof(f655,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | r1_tarski(sK5,u1_struct_0(sK3))
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_26
    | ~ spl11_28
    | ~ spl11_30 ),
    inference(subsumption_resolution,[],[f645,f220])).

fof(f645,plain,
    ( ~ m1_pre_topc(sK2,sK1)
    | ~ m1_pre_topc(sK2,sK3)
    | r1_tarski(sK5,u1_struct_0(sK3))
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_26
    | ~ spl11_30 ),
    inference(resolution,[],[f504,f227])).

fof(f504,plain,
    ( ! [X2,X3] :
        ( ~ r1_tarski(X3,u1_struct_0(X2))
        | ~ m1_pre_topc(X2,sK1)
        | ~ m1_pre_topc(X2,sK3)
        | r1_tarski(X3,u1_struct_0(sK3)) )
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_26 ),
    inference(resolution,[],[f359,f94])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t85_tmap_1.p',t1_xboole_1)).

fof(f359,plain,
    ( ! [X2] :
        ( r1_tarski(u1_struct_0(X2),u1_struct_0(sK3))
        | ~ m1_pre_topc(X2,sK3)
        | ~ m1_pre_topc(X2,sK1) )
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_26 ),
    inference(subsumption_resolution,[],[f358,f150])).

fof(f358,plain,
    ( ! [X2] :
        ( ~ m1_pre_topc(X2,sK1)
        | ~ v2_pre_topc(sK1)
        | ~ m1_pre_topc(X2,sK3)
        | r1_tarski(u1_struct_0(X2),u1_struct_0(sK3)) )
    | ~ spl11_10
    | ~ spl11_26 ),
    inference(subsumption_resolution,[],[f351,f157])).

fof(f351,plain,
    ( ! [X2] :
        ( ~ l1_pre_topc(sK1)
        | ~ m1_pre_topc(X2,sK1)
        | ~ v2_pre_topc(sK1)
        | ~ m1_pre_topc(X2,sK3)
        | r1_tarski(u1_struct_0(X2),u1_struct_0(sK3)) )
    | ~ spl11_26 ),
    inference(resolution,[],[f97,f213])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X1,X2)
      | r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t85_tmap_1.p',t4_tsep_1)).

fof(f617,plain,
    ( spl11_90
    | ~ spl11_93
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_26 ),
    inference(avatar_split_clause,[],[f528,f212,f156,f149,f615,f609])).

fof(f609,plain,
    ( spl11_90
  <=> ! [X9,X8] :
        ( ~ r2_hidden(X8,u1_struct_0(X9))
        | ~ m1_pre_topc(X9,sK1)
        | ~ m1_pre_topc(X9,sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_90])])).

fof(f615,plain,
    ( spl11_93
  <=> ~ v1_xboole_0(u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_93])])).

fof(f528,plain,
    ( ! [X8,X9] :
        ( ~ v1_xboole_0(u1_struct_0(sK3))
        | ~ r2_hidden(X8,u1_struct_0(X9))
        | ~ m1_pre_topc(X9,sK3)
        | ~ m1_pre_topc(X9,sK1) )
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_26 ),
    inference(resolution,[],[f326,f359])).

fof(f326,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_tarski(X3,X4)
      | ~ v1_xboole_0(X4)
      | ~ r2_hidden(X2,X3) ) ),
    inference(resolution,[],[f99,f95])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t85_tmap_1.p',t5_subset)).

fof(f607,plain,
    ( spl11_88
    | ~ spl11_10
    | ~ spl11_18
    | ~ spl11_28
    | ~ spl11_30
    | ~ spl11_36 ),
    inference(avatar_split_clause,[],[f592,f247,f226,f219,f184,f156,f605])).

fof(f605,plain,
    ( spl11_88
  <=> v3_pre_topc(sK5,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_88])])).

fof(f592,plain,
    ( v3_pre_topc(sK5,sK2)
    | ~ spl11_10
    | ~ spl11_18
    | ~ spl11_28
    | ~ spl11_30
    | ~ spl11_36 ),
    inference(subsumption_resolution,[],[f588,f220])).

fof(f588,plain,
    ( v3_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(sK2,sK1)
    | ~ spl11_10
    | ~ spl11_18
    | ~ spl11_30
    | ~ spl11_36 ),
    inference(resolution,[],[f561,f227])).

fof(f600,plain,
    ( spl11_86
    | ~ spl11_81
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_24
    | ~ spl11_26
    | ~ spl11_54 ),
    inference(avatar_split_clause,[],[f527,f346,f212,f205,f156,f149,f539,f598])).

fof(f598,plain,
    ( spl11_86
  <=> ! [X7,X6] :
        ( ~ r2_hidden(X6,u1_struct_0(X7))
        | ~ m1_pre_topc(X7,sK3)
        | ~ m1_pre_topc(X7,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_86])])).

fof(f539,plain,
    ( spl11_81
  <=> ~ v1_xboole_0(u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_81])])).

fof(f346,plain,
    ( spl11_54
  <=> l1_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_54])])).

fof(f527,plain,
    ( ! [X6,X7] :
        ( ~ v1_xboole_0(u1_struct_0(sK2))
        | ~ r2_hidden(X6,u1_struct_0(X7))
        | ~ m1_pre_topc(X7,sK2)
        | ~ m1_pre_topc(X7,sK3) )
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_24
    | ~ spl11_26
    | ~ spl11_54 ),
    inference(resolution,[],[f326,f355])).

fof(f355,plain,
    ( ! [X0] :
        ( r1_tarski(u1_struct_0(X0),u1_struct_0(sK2))
        | ~ m1_pre_topc(X0,sK2)
        | ~ m1_pre_topc(X0,sK3) )
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_24
    | ~ spl11_26
    | ~ spl11_54 ),
    inference(subsumption_resolution,[],[f354,f337])).

fof(f337,plain,
    ( v2_pre_topc(sK3)
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_26 ),
    inference(subsumption_resolution,[],[f336,f150])).

fof(f336,plain,
    ( ~ v2_pre_topc(sK1)
    | v2_pre_topc(sK3)
    | ~ spl11_10
    | ~ spl11_26 ),
    inference(subsumption_resolution,[],[f330,f157])).

fof(f330,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_pre_topc(sK3)
    | ~ spl11_26 ),
    inference(resolution,[],[f106,f213])).

fof(f106,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t85_tmap_1.p',cc1_pre_topc)).

fof(f354,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK3)
        | ~ v2_pre_topc(sK3)
        | ~ m1_pre_topc(X0,sK2)
        | r1_tarski(u1_struct_0(X0),u1_struct_0(sK2)) )
    | ~ spl11_24
    | ~ spl11_54 ),
    inference(subsumption_resolution,[],[f349,f347])).

fof(f347,plain,
    ( l1_pre_topc(sK3)
    | ~ spl11_54 ),
    inference(avatar_component_clause,[],[f346])).

fof(f349,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK3)
        | ~ m1_pre_topc(X0,sK3)
        | ~ v2_pre_topc(sK3)
        | ~ m1_pre_topc(X0,sK2)
        | r1_tarski(u1_struct_0(X0),u1_struct_0(sK2)) )
    | ~ spl11_24 ),
    inference(resolution,[],[f97,f206])).

fof(f596,plain,
    ( spl11_84
    | ~ spl11_81
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_28 ),
    inference(avatar_split_clause,[],[f526,f219,f156,f149,f539,f594])).

fof(f594,plain,
    ( spl11_84
  <=> ! [X5,X4] :
        ( ~ r2_hidden(X4,u1_struct_0(X5))
        | ~ m1_pre_topc(X5,sK1)
        | ~ m1_pre_topc(X5,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_84])])).

fof(f526,plain,
    ( ! [X4,X5] :
        ( ~ v1_xboole_0(u1_struct_0(sK2))
        | ~ r2_hidden(X4,u1_struct_0(X5))
        | ~ m1_pre_topc(X5,sK2)
        | ~ m1_pre_topc(X5,sK1) )
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_28 ),
    inference(resolution,[],[f326,f357])).

fof(f357,plain,
    ( ! [X1] :
        ( r1_tarski(u1_struct_0(X1),u1_struct_0(sK2))
        | ~ m1_pre_topc(X1,sK2)
        | ~ m1_pre_topc(X1,sK1) )
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_28 ),
    inference(subsumption_resolution,[],[f356,f150])).

fof(f356,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(X1,sK1)
        | ~ v2_pre_topc(sK1)
        | ~ m1_pre_topc(X1,sK2)
        | r1_tarski(u1_struct_0(X1),u1_struct_0(sK2)) )
    | ~ spl11_10
    | ~ spl11_28 ),
    inference(subsumption_resolution,[],[f350,f157])).

fof(f350,plain,
    ( ! [X1] :
        ( ~ l1_pre_topc(sK1)
        | ~ m1_pre_topc(X1,sK1)
        | ~ v2_pre_topc(sK1)
        | ~ m1_pre_topc(X1,sK2)
        | r1_tarski(u1_struct_0(X1),u1_struct_0(sK2)) )
    | ~ spl11_28 ),
    inference(resolution,[],[f97,f220])).

fof(f577,plain,
    ( spl11_82
    | ~ spl11_81
    | ~ spl11_30 ),
    inference(avatar_split_clause,[],[f524,f226,f539,f575])).

fof(f575,plain,
    ( spl11_82
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,X1)
        | ~ r1_tarski(X1,sK5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_82])])).

fof(f524,plain,
    ( ! [X0,X1] :
        ( ~ v1_xboole_0(u1_struct_0(sK2))
        | ~ r2_hidden(X0,X1)
        | ~ r1_tarski(X1,sK5) )
    | ~ spl11_30 ),
    inference(resolution,[],[f326,f316])).

fof(f316,plain,
    ( ! [X0] :
        ( r1_tarski(X0,u1_struct_0(sK2))
        | ~ r1_tarski(X0,sK5) )
    | ~ spl11_30 ),
    inference(resolution,[],[f94,f227])).

fof(f541,plain,
    ( spl11_68
    | ~ spl11_81
    | ~ spl11_30 ),
    inference(avatar_split_clause,[],[f529,f226,f539,f463])).

fof(f463,plain,
    ( spl11_68
  <=> ! [X0] : ~ r2_hidden(X0,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_68])])).

fof(f529,plain,
    ( ! [X10] :
        ( ~ v1_xboole_0(u1_struct_0(sK2))
        | ~ r2_hidden(X10,sK5) )
    | ~ spl11_30 ),
    inference(resolution,[],[f326,f227])).

fof(f498,plain,
    ( ~ spl11_77
    | spl11_78
    | ~ spl11_40 ),
    inference(avatar_split_clause,[],[f325,f261,f496,f493])).

fof(f493,plain,
    ( spl11_77
  <=> ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_77])])).

fof(f496,plain,
    ( spl11_78
  <=> ! [X1] : ~ r2_hidden(X1,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_78])])).

fof(f325,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK4)
        | ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))) )
    | ~ spl11_40 ),
    inference(resolution,[],[f99,f262])).

fof(f485,plain,
    ( ~ spl11_73
    | spl11_74
    | spl11_63 ),
    inference(avatar_split_clause,[],[f445,f442,f483,f477])).

fof(f477,plain,
    ( spl11_73
  <=> ~ m1_subset_1(sK5,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_73])])).

fof(f483,plain,
    ( spl11_74
  <=> v1_xboole_0(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_74])])).

fof(f442,plain,
    ( spl11_63
  <=> ~ r2_hidden(sK5,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_63])])).

fof(f445,plain,
    ( v1_xboole_0(sK6)
    | ~ m1_subset_1(sK5,sK6)
    | ~ spl11_63 ),
    inference(resolution,[],[f443,f102])).

fof(f102,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t85_tmap_1.p',t2_subset)).

fof(f443,plain,
    ( ~ r2_hidden(sK5,sK6)
    | ~ spl11_63 ),
    inference(avatar_component_clause,[],[f442])).

fof(f472,plain,
    ( spl11_70
    | ~ spl11_40 ),
    inference(avatar_split_clause,[],[f303,f261,f470])).

fof(f470,plain,
    ( spl11_70
  <=> r1_tarski(sK4,k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_70])])).

fof(f303,plain,
    ( r1_tarski(sK4,k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))
    | ~ spl11_40 ),
    inference(resolution,[],[f96,f262])).

fof(f96,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f465,plain,
    ( ~ spl11_67
    | spl11_68
    | ~ spl11_36 ),
    inference(avatar_split_clause,[],[f324,f247,f463,f460])).

fof(f460,plain,
    ( spl11_67
  <=> ~ v1_xboole_0(u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_67])])).

fof(f324,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK5)
        | ~ v1_xboole_0(u1_struct_0(sK1)) )
    | ~ spl11_36 ),
    inference(resolution,[],[f99,f248])).

fof(f454,plain,
    ( spl11_56
    | ~ spl11_59
    | ~ spl11_10
    | ~ spl11_24
    | ~ spl11_26 ),
    inference(avatar_split_clause,[],[f333,f212,f205,f156,f405,f382])).

fof(f382,plain,
    ( spl11_56
  <=> v2_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_56])])).

fof(f405,plain,
    ( spl11_59
  <=> ~ v2_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_59])])).

fof(f333,plain,
    ( ~ v2_pre_topc(sK3)
    | v2_pre_topc(sK2)
    | ~ spl11_10
    | ~ spl11_24
    | ~ spl11_26 ),
    inference(subsumption_resolution,[],[f328,f312])).

fof(f312,plain,
    ( l1_pre_topc(sK3)
    | ~ spl11_10
    | ~ spl11_26 ),
    inference(subsumption_resolution,[],[f308,f157])).

fof(f308,plain,
    ( ~ l1_pre_topc(sK1)
    | l1_pre_topc(sK3)
    | ~ spl11_26 ),
    inference(resolution,[],[f108,f213])).

fof(f108,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t85_tmap_1.p',dt_m1_pre_topc)).

fof(f328,plain,
    ( ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_pre_topc(sK2)
    | ~ spl11_24 ),
    inference(resolution,[],[f106,f206])).

fof(f453,plain,
    ( spl11_52
    | ~ spl11_55
    | ~ spl11_24 ),
    inference(avatar_split_clause,[],[f306,f205,f343,f321])).

fof(f321,plain,
    ( spl11_52
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_52])])).

fof(f343,plain,
    ( spl11_55
  <=> ~ l1_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_55])])).

fof(f306,plain,
    ( ~ l1_pre_topc(sK3)
    | l1_pre_topc(sK2)
    | ~ spl11_24 ),
    inference(resolution,[],[f108,f206])).

fof(f452,plain,
    ( spl11_64
    | ~ spl11_36 ),
    inference(avatar_split_clause,[],[f302,f247,f450])).

fof(f450,plain,
    ( spl11_64
  <=> r1_tarski(sK5,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_64])])).

fof(f302,plain,
    ( r1_tarski(sK5,u1_struct_0(sK1))
    | ~ spl11_36 ),
    inference(resolution,[],[f96,f248])).

fof(f444,plain,
    ( ~ spl11_63
    | ~ spl11_20 ),
    inference(avatar_split_clause,[],[f294,f191,f442])).

fof(f294,plain,
    ( ~ r2_hidden(sK5,sK6)
    | ~ spl11_20 ),
    inference(resolution,[],[f104,f192])).

fof(f104,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t85_tmap_1.p',antisymmetry_r2_hidden)).

fof(f437,plain,
    ( spl11_60
    | ~ spl11_20 ),
    inference(avatar_split_clause,[],[f293,f191,f435])).

fof(f435,plain,
    ( spl11_60
  <=> m1_subset_1(sK6,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_60])])).

fof(f293,plain,
    ( m1_subset_1(sK6,sK5)
    | ~ spl11_20 ),
    inference(resolution,[],[f103,f192])).

fof(f103,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t85_tmap_1.p',t1_subset)).

fof(f410,plain,
    ( spl11_58
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_26 ),
    inference(avatar_split_clause,[],[f337,f212,f156,f149,f408])).

fof(f408,plain,
    ( spl11_58
  <=> v2_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_58])])).

fof(f403,plain,
    ( ~ spl11_0
    | spl11_3
    | spl11_5
    | spl11_7
    | ~ spl11_8
    | ~ spl11_10
    | spl11_13
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_24
    | ~ spl11_26
    | ~ spl11_28
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_38
    | ~ spl11_40
    | ~ spl11_46
    | spl11_49 ),
    inference(avatar_contradiction_clause,[],[f402])).

fof(f402,plain,
    ( $false
    | ~ spl11_0
    | ~ spl11_3
    | ~ spl11_5
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_13
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_24
    | ~ spl11_26
    | ~ spl11_28
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_38
    | ~ spl11_40
    | ~ spl11_46
    | ~ spl11_49 ),
    inference(subsumption_resolution,[],[f401,f143])).

fof(f401,plain,
    ( v2_struct_0(sK1)
    | ~ spl11_0
    | ~ spl11_3
    | ~ spl11_5
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_13
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_24
    | ~ spl11_26
    | ~ spl11_28
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_38
    | ~ spl11_40
    | ~ spl11_46
    | ~ spl11_49 ),
    inference(subsumption_resolution,[],[f400,f280])).

fof(f280,plain,
    ( r1_tmap_1(sK3,sK0,sK4,sK6)
    | ~ spl11_46 ),
    inference(avatar_component_clause,[],[f279])).

fof(f279,plain,
    ( spl11_46
  <=> r1_tmap_1(sK3,sK0,sK4,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_46])])).

fof(f400,plain,
    ( ~ r1_tmap_1(sK3,sK0,sK4,sK6)
    | v2_struct_0(sK1)
    | ~ spl11_0
    | ~ spl11_3
    | ~ spl11_5
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_13
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_24
    | ~ spl11_26
    | ~ spl11_28
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_38
    | ~ spl11_40
    | ~ spl11_49 ),
    inference(subsumption_resolution,[],[f399,f206])).

fof(f399,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | ~ r1_tmap_1(sK3,sK0,sK4,sK6)
    | v2_struct_0(sK1)
    | ~ spl11_0
    | ~ spl11_3
    | ~ spl11_5
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_13
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_26
    | ~ spl11_28
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_38
    | ~ spl11_40
    | ~ spl11_49 ),
    inference(subsumption_resolution,[],[f398,f241])).

fof(f398,plain,
    ( ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ r1_tmap_1(sK3,sK0,sK4,sK6)
    | v2_struct_0(sK1)
    | ~ spl11_0
    | ~ spl11_3
    | ~ spl11_5
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_13
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_26
    | ~ spl11_28
    | ~ spl11_32
    | ~ spl11_38
    | ~ spl11_40
    | ~ spl11_49 ),
    inference(subsumption_resolution,[],[f397,f234])).

fof(f397,plain,
    ( ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ r1_tmap_1(sK3,sK0,sK4,sK6)
    | v2_struct_0(sK1)
    | ~ spl11_0
    | ~ spl11_3
    | ~ spl11_5
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_13
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_26
    | ~ spl11_28
    | ~ spl11_38
    | ~ spl11_40
    | ~ spl11_49 ),
    inference(subsumption_resolution,[],[f396,f262])).

fof(f396,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ r1_tmap_1(sK3,sK0,sK4,sK6)
    | v2_struct_0(sK1)
    | ~ spl11_0
    | ~ spl11_3
    | ~ spl11_5
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_13
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_26
    | ~ spl11_28
    | ~ spl11_38
    | ~ spl11_49 ),
    inference(subsumption_resolution,[],[f395,f255])).

fof(f395,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ r1_tmap_1(sK3,sK0,sK4,sK6)
    | v2_struct_0(sK1)
    | ~ spl11_0
    | ~ spl11_3
    | ~ spl11_5
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_13
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_26
    | ~ spl11_28
    | ~ spl11_49 ),
    inference(subsumption_resolution,[],[f394,f122])).

fof(f394,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ r1_tmap_1(sK3,sK0,sK4,sK6)
    | v2_struct_0(sK1)
    | ~ spl11_3
    | ~ spl11_5
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_13
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_26
    | ~ spl11_28
    | ~ spl11_49 ),
    inference(subsumption_resolution,[],[f393,f220])).

fof(f393,plain,
    ( ~ m1_pre_topc(sK2,sK1)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ r1_tmap_1(sK3,sK0,sK4,sK6)
    | v2_struct_0(sK1)
    | ~ spl11_3
    | ~ spl11_5
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_13
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_26
    | ~ spl11_49 ),
    inference(subsumption_resolution,[],[f392,f136])).

fof(f392,plain,
    ( v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK1)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ r1_tmap_1(sK3,sK0,sK4,sK6)
    | v2_struct_0(sK1)
    | ~ spl11_3
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_13
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_26
    | ~ spl11_49 ),
    inference(subsumption_resolution,[],[f391,f213])).

fof(f391,plain,
    ( ~ m1_pre_topc(sK3,sK1)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK1)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ r1_tmap_1(sK3,sK0,sK4,sK6)
    | v2_struct_0(sK1)
    | ~ spl11_3
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_13
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_49 ),
    inference(subsumption_resolution,[],[f390,f129])).

fof(f390,plain,
    ( v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK1)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK1)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ r1_tmap_1(sK3,sK0,sK4,sK6)
    | v2_struct_0(sK1)
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_13
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_49 ),
    inference(subsumption_resolution,[],[f389,f178])).

fof(f389,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK1)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK1)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ r1_tmap_1(sK3,sK0,sK4,sK6)
    | v2_struct_0(sK1)
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_13
    | ~ spl11_14
    | ~ spl11_49 ),
    inference(subsumption_resolution,[],[f388,f171])).

fof(f388,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK1)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK1)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ r1_tmap_1(sK3,sK0,sK4,sK6)
    | v2_struct_0(sK1)
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_13
    | ~ spl11_49 ),
    inference(subsumption_resolution,[],[f387,f164])).

fof(f387,plain,
    ( v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK1)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK1)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ r1_tmap_1(sK3,sK0,sK4,sK6)
    | v2_struct_0(sK1)
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_49 ),
    inference(subsumption_resolution,[],[f386,f157])).

fof(f386,plain,
    ( ~ l1_pre_topc(sK1)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK1)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK1)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ r1_tmap_1(sK3,sK0,sK4,sK6)
    | v2_struct_0(sK1)
    | ~ spl11_8
    | ~ spl11_49 ),
    inference(subsumption_resolution,[],[f385,f150])).

fof(f385,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK1)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK1)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ r1_tmap_1(sK3,sK0,sK4,sK6)
    | v2_struct_0(sK1)
    | ~ spl11_49 ),
    inference(resolution,[],[f110,f289])).

fof(f289,plain,
    ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6)
    | ~ spl11_49 ),
    inference(avatar_component_clause,[],[f288])).

fof(f288,plain,
    ( spl11_49
  <=> ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_49])])).

fof(f110,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ m1_subset_1(X6,u1_struct_0(X2))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_pre_topc(X3,X2)
      | ~ r1_tmap_1(X2,X1,X4,X6)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f87])).

fof(f87,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ m1_subset_1(X5,u1_struct_0(X2))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | X5 != X6
      | ~ m1_pre_topc(X3,X2)
      | ~ r1_tmap_1(X2,X1,X4,X5)
      | r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)
                              | ~ r1_tmap_1(X2,X1,X4,X5)
                              | ~ m1_pre_topc(X3,X2)
                              | X5 != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X2)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
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
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)
                              | ~ r1_tmap_1(X2,X1,X4,X5)
                              | ~ m1_pre_topc(X3,X2)
                              | X5 != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X2)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
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
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
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
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X2))
                         => ! [X6] :
                              ( m1_subset_1(X6,u1_struct_0(X3))
                             => ( ( r1_tmap_1(X2,X1,X4,X5)
                                  & m1_pre_topc(X3,X2)
                                  & X5 = X6 )
                               => r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t85_tmap_1.p',t81_tmap_1)).

fof(f384,plain,
    ( spl11_56
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_28 ),
    inference(avatar_split_clause,[],[f335,f219,f156,f149,f382])).

fof(f335,plain,
    ( v2_pre_topc(sK2)
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_28 ),
    inference(subsumption_resolution,[],[f334,f150])).

fof(f334,plain,
    ( ~ v2_pre_topc(sK1)
    | v2_pre_topc(sK2)
    | ~ spl11_10
    | ~ spl11_28 ),
    inference(subsumption_resolution,[],[f329,f157])).

fof(f329,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_pre_topc(sK2)
    | ~ spl11_28 ),
    inference(resolution,[],[f106,f220])).

fof(f348,plain,
    ( spl11_54
    | ~ spl11_10
    | ~ spl11_26 ),
    inference(avatar_split_clause,[],[f312,f212,f156,f346])).

fof(f323,plain,
    ( spl11_52
    | ~ spl11_10
    | ~ spl11_28 ),
    inference(avatar_split_clause,[],[f311,f219,f156,f321])).

fof(f311,plain,
    ( l1_pre_topc(sK2)
    | ~ spl11_10
    | ~ spl11_28 ),
    inference(subsumption_resolution,[],[f307,f157])).

fof(f307,plain,
    ( ~ l1_pre_topc(sK1)
    | l1_pre_topc(sK2)
    | ~ spl11_28 ),
    inference(resolution,[],[f108,f220])).

fof(f301,plain,
    ( ~ spl11_51
    | ~ spl11_20 ),
    inference(avatar_split_clause,[],[f292,f191,f299])).

fof(f299,plain,
    ( spl11_51
  <=> ~ v1_xboole_0(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_51])])).

fof(f292,plain,
    ( ~ v1_xboole_0(sK5)
    | ~ spl11_20 ),
    inference(resolution,[],[f101,f192])).

fof(f101,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t85_tmap_1.p',t7_boole)).

fof(f291,plain,
    ( spl11_46
    | spl11_48 ),
    inference(avatar_split_clause,[],[f116,f285,f279])).

fof(f116,plain,
    ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6)
    | r1_tmap_1(sK3,sK0,sK4,sK6) ),
    inference(forward_demodulation,[],[f61,f67])).

fof(f67,plain,(
    sK6 = sK7 ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ? [X7] :
                                  ( ( r1_tmap_1(X3,X0,X4,X6)
                                  <~> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) )
                                  & X6 = X7
                                  & r1_tarski(X5,u1_struct_0(X2))
                                  & r2_hidden(X6,X5)
                                  & v3_pre_topc(X5,X1)
                                  & m1_subset_1(X7,u1_struct_0(X2)) )
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
                      & m1_pre_topc(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ? [X7] :
                                  ( ( r1_tmap_1(X3,X0,X4,X6)
                                  <~> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) )
                                  & X6 = X7
                                  & r1_tarski(X5,u1_struct_0(X2))
                                  & r2_hidden(X6,X5)
                                  & v3_pre_topc(X5,X1)
                                  & m1_subset_1(X7,u1_struct_0(X2)) )
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
                      & m1_pre_topc(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
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
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X1)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X1)
                      & ~ v2_struct_0(X3) )
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                          & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                          & v1_funct_1(X4) )
                       => ( m1_pre_topc(X2,X3)
                         => ! [X5] :
                              ( m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))
                             => ! [X6] :
                                  ( m1_subset_1(X6,u1_struct_0(X3))
                                 => ! [X7] :
                                      ( m1_subset_1(X7,u1_struct_0(X2))
                                     => ( ( X6 = X7
                                          & r1_tarski(X5,u1_struct_0(X2))
                                          & r2_hidden(X6,X5)
                                          & v3_pre_topc(X5,X1) )
                                       => ( r1_tmap_1(X3,X0,X4,X6)
                                        <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) ) ) ) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X1)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X1)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                        & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                        & v1_funct_1(X4) )
                     => ( m1_pre_topc(X2,X3)
                       => ! [X5] :
                            ( m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X3))
                               => ! [X7] :
                                    ( m1_subset_1(X7,u1_struct_0(X2))
                                   => ( ( X6 = X7
                                        & r1_tarski(X5,u1_struct_0(X2))
                                        & r2_hidden(X6,X5)
                                        & v3_pre_topc(X5,X1) )
                                     => ( r1_tmap_1(X3,X0,X4,X6)
                                      <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) ) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t85_tmap_1.p',t85_tmap_1)).

fof(f61,plain,
    ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7)
    | r1_tmap_1(sK3,sK0,sK4,sK6) ),
    inference(cnf_transformation,[],[f34])).

fof(f290,plain,
    ( ~ spl11_47
    | ~ spl11_49 ),
    inference(avatar_split_clause,[],[f115,f288,f282])).

fof(f115,plain,
    ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6)
    | ~ r1_tmap_1(sK3,sK0,sK4,sK6) ),
    inference(forward_demodulation,[],[f62,f67])).

fof(f62,plain,
    ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7)
    | ~ r1_tmap_1(sK3,sK0,sK4,sK6) ),
    inference(cnf_transformation,[],[f34])).

fof(f277,plain,(
    spl11_44 ),
    inference(avatar_split_clause,[],[f93,f275])).

fof(f275,plain,
    ( spl11_44
  <=> k1_xboole_0 = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_44])])).

fof(f93,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t85_tmap_1.p',d2_xboole_0)).

fof(f270,plain,(
    spl11_42 ),
    inference(avatar_split_clause,[],[f109,f268])).

fof(f268,plain,
    ( spl11_42
  <=> l1_pre_topc(sK10) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_42])])).

fof(f109,plain,(
    l1_pre_topc(sK10) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ? [X0] : l1_pre_topc(X0) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t85_tmap_1.p',existence_l1_pre_topc)).

fof(f263,plain,(
    spl11_40 ),
    inference(avatar_split_clause,[],[f72,f261])).

fof(f72,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f34])).

fof(f256,plain,(
    spl11_38 ),
    inference(avatar_split_clause,[],[f71,f254])).

fof(f71,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f34])).

fof(f249,plain,(
    spl11_36 ),
    inference(avatar_split_clause,[],[f69,f247])).

fof(f69,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f34])).

fof(f242,plain,(
    spl11_34 ),
    inference(avatar_split_clause,[],[f114,f240])).

fof(f114,plain,(
    m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f63,f67])).

fof(f63,plain,(
    m1_subset_1(sK7,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f34])).

fof(f235,plain,(
    spl11_32 ),
    inference(avatar_split_clause,[],[f68,f233])).

fof(f68,plain,(
    m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f34])).

fof(f228,plain,(
    spl11_30 ),
    inference(avatar_split_clause,[],[f66,f226])).

fof(f66,plain,(
    r1_tarski(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f34])).

fof(f221,plain,(
    spl11_28 ),
    inference(avatar_split_clause,[],[f77,f219])).

fof(f77,plain,(
    m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f214,plain,(
    spl11_26 ),
    inference(avatar_split_clause,[],[f75,f212])).

fof(f75,plain,(
    m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f207,plain,(
    spl11_24 ),
    inference(avatar_split_clause,[],[f73,f205])).

fof(f73,plain,(
    m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f200,plain,(
    spl11_22 ),
    inference(avatar_split_clause,[],[f67,f198])).

fof(f198,plain,
    ( spl11_22
  <=> sK6 = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_22])])).

fof(f193,plain,(
    spl11_20 ),
    inference(avatar_split_clause,[],[f65,f191])).

fof(f65,plain,(
    r2_hidden(sK6,sK5) ),
    inference(cnf_transformation,[],[f34])).

fof(f186,plain,(
    spl11_18 ),
    inference(avatar_split_clause,[],[f64,f184])).

fof(f64,plain,(
    v3_pre_topc(sK5,sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f179,plain,(
    spl11_16 ),
    inference(avatar_split_clause,[],[f83,f177])).

fof(f83,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f172,plain,(
    spl11_14 ),
    inference(avatar_split_clause,[],[f82,f170])).

fof(f82,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f165,plain,(
    ~ spl11_13 ),
    inference(avatar_split_clause,[],[f81,f163])).

fof(f81,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f158,plain,(
    spl11_10 ),
    inference(avatar_split_clause,[],[f80,f156])).

fof(f80,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f151,plain,(
    spl11_8 ),
    inference(avatar_split_clause,[],[f79,f149])).

fof(f79,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f144,plain,(
    ~ spl11_7 ),
    inference(avatar_split_clause,[],[f78,f142])).

fof(f78,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f137,plain,(
    ~ spl11_5 ),
    inference(avatar_split_clause,[],[f76,f135])).

fof(f76,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f130,plain,(
    ~ spl11_3 ),
    inference(avatar_split_clause,[],[f74,f128])).

fof(f74,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f123,plain,(
    spl11_0 ),
    inference(avatar_split_clause,[],[f70,f121])).

fof(f70,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f34])).
%------------------------------------------------------------------------------
