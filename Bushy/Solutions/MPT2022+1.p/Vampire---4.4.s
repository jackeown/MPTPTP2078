%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : waybel_9__t21_waybel_9.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:09 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 270 expanded)
%              Number of leaves         :   27 ( 108 expanded)
%              Depth                    :   18
%              Number of atoms          :  578 (1096 expanded)
%              Number of equality atoms :   22 (  56 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f433,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f121,f128,f135,f142,f149,f156,f163,f202,f218,f279,f286,f293,f313,f343,f401,f432])).

fof(f432,plain,
    ( spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_7
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_16
    | ~ spl8_28 ),
    inference(avatar_contradiction_clause,[],[f431])).

fof(f431,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_16
    | ~ spl8_28 ),
    inference(subsumption_resolution,[],[f429,f292])).

fof(f292,plain,
    ( r2_hidden(sK1,sK2)
    | ~ spl8_28 ),
    inference(avatar_component_clause,[],[f291])).

fof(f291,plain,
    ( spl8_28
  <=> r2_hidden(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).

fof(f429,plain,
    ( ~ r2_hidden(sK1,sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_16 ),
    inference(resolution,[],[f422,f141])).

fof(f141,plain,
    ( ~ m1_connsp_2(sK2,sK0,sK1)
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f140])).

fof(f140,plain,
    ( spl8_7
  <=> ~ m1_connsp_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f422,plain,
    ( ! [X0] :
        ( m1_connsp_2(sK2,sK0,X0)
        | ~ r2_hidden(X0,sK2) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_16 ),
    inference(forward_demodulation,[],[f421,f217])).

fof(f217,plain,
    ( sK2 = sK4(sK0,sK1,sK2)
    | ~ spl8_16 ),
    inference(avatar_component_clause,[],[f216])).

fof(f216,plain,
    ( spl8_16
  <=> sK2 = sK4(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f421,plain,
    ( ! [X0] :
        ( m1_connsp_2(sK2,sK0,X0)
        | ~ r2_hidden(X0,sK4(sK0,sK1,sK2)) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f420,f155])).

fof(f155,plain,
    ( m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1)))
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f154])).

fof(f154,plain,
    ( spl8_10
  <=> m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f420,plain,
    ( ! [X0] :
        ( m1_connsp_2(sK2,sK0,X0)
        | ~ r2_hidden(X0,sK4(sK0,sK1,sK2))
        | ~ m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1))) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_8
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f419,f148])).

fof(f148,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f147])).

fof(f147,plain,
    ( spl8_8
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f419,plain,
    ( ! [X0] :
        ( m1_connsp_2(sK2,sK0,X0)
        | ~ r2_hidden(X0,sK4(sK0,sK1,sK2))
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1))) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f418,f127])).

fof(f127,plain,
    ( v2_pre_topc(sK0)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f126])).

fof(f126,plain,
    ( spl8_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f418,plain,
    ( ! [X0] :
        ( m1_connsp_2(sK2,sK0,X0)
        | ~ r2_hidden(X0,sK4(sK0,sK1,sK2))
        | ~ v2_pre_topc(sK0)
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1))) )
    | ~ spl8_1
    | ~ spl8_4
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f417,f120])).

fof(f120,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f119])).

fof(f119,plain,
    ( spl8_1
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f417,plain,
    ( ! [X0] :
        ( m1_connsp_2(sK2,sK0,X0)
        | v2_struct_0(sK0)
        | ~ r2_hidden(X0,sK4(sK0,sK1,sK2))
        | ~ v2_pre_topc(sK0)
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1))) )
    | ~ spl8_4
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f415,f134])).

fof(f134,plain,
    ( l1_pre_topc(sK0)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f133])).

fof(f133,plain,
    ( spl8_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f415,plain,
    ( ! [X0] :
        ( m1_connsp_2(sK2,sK0,X0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0)
        | ~ r2_hidden(X0,sK4(sK0,sK1,sK2))
        | ~ v2_pre_topc(sK0)
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1))) )
    | ~ spl8_16 ),
    inference(superposition,[],[f253,f217])).

fof(f253,plain,(
    ! [X6,X4,X7,X5] :
      ( m1_connsp_2(sK4(X4,X6,X7),X4,X5)
      | ~ l1_pre_topc(X4)
      | v2_struct_0(X4)
      | ~ r2_hidden(X5,sK4(X4,X6,X7))
      | ~ v2_pre_topc(X4)
      | ~ m1_subset_1(X6,u1_struct_0(X4))
      | ~ m1_subset_1(X7,u1_struct_0(k9_yellow_6(X4,X6))) ) ),
    inference(subsumption_resolution,[],[f252,f90])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(sK4(X0,X1,X2),X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( v3_pre_topc(X3,X0)
                  & r2_hidden(X1,X3)
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( v3_pre_topc(X3,X0)
                  & r2_hidden(X1,X3)
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f38])).

fof(f38,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
             => ? [X3] :
                  ( v3_pre_topc(X3,X0)
                  & r2_hidden(X1,X3)
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_9__t21_waybel_9.p',t38_yellow_6)).

fof(f252,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ v2_pre_topc(X4)
      | ~ l1_pre_topc(X4)
      | v2_struct_0(X4)
      | ~ v3_pre_topc(sK4(X4,X6,X7),X4)
      | ~ r2_hidden(X5,sK4(X4,X6,X7))
      | m1_connsp_2(sK4(X4,X6,X7),X4,X5)
      | ~ m1_subset_1(X6,u1_struct_0(X4))
      | ~ m1_subset_1(X7,u1_struct_0(k9_yellow_6(X4,X6))) ) ),
    inference(subsumption_resolution,[],[f248,f225])).

fof(f225,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,sK4(X0,X1,X2))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | m1_subset_1(X3,u1_struct_0(X0)) ) ),
    inference(resolution,[],[f87,f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f61])).

fof(f61,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f40])).

fof(f40,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_9__t21_waybel_9.p',t4_subset)).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f248,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ v2_pre_topc(X4)
      | ~ l1_pre_topc(X4)
      | v2_struct_0(X4)
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ v3_pre_topc(sK4(X4,X6,X7),X4)
      | ~ r2_hidden(X5,sK4(X4,X6,X7))
      | m1_connsp_2(sK4(X4,X6,X7),X4,X5)
      | ~ m1_subset_1(X6,u1_struct_0(X4))
      | ~ m1_subset_1(X7,u1_struct_0(k9_yellow_6(X4,X6))) ) ),
    inference(duplicate_literal_removal,[],[f246])).

fof(f246,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ v2_pre_topc(X4)
      | ~ l1_pre_topc(X4)
      | v2_struct_0(X4)
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ v3_pre_topc(sK4(X4,X6,X7),X4)
      | ~ r2_hidden(X5,sK4(X4,X6,X7))
      | m1_connsp_2(sK4(X4,X6,X7),X4,X5)
      | ~ v2_pre_topc(X4)
      | ~ l1_pre_topc(X4)
      | ~ m1_subset_1(X6,u1_struct_0(X4))
      | ~ m1_subset_1(X7,u1_struct_0(k9_yellow_6(X4,X6)))
      | v2_struct_0(X4) ) ),
    inference(resolution,[],[f85,f87])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v3_pre_topc(X1,X0)
      | ~ r2_hidden(X2,X1)
      | m1_connsp_2(X1,X0,X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X1,X0,X2)
              | ~ r2_hidden(X2,X1)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X1,X0,X2)
              | ~ r2_hidden(X2,X1)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f41])).

fof(f41,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ( r2_hidden(X2,X1)
                  & v3_pre_topc(X1,X0) )
               => m1_connsp_2(X1,X0,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_9__t21_waybel_9.p',t5_connsp_2)).

fof(f401,plain,
    ( ~ spl8_35
    | spl8_36
    | ~ spl8_32 ),
    inference(avatar_split_clause,[],[f372,f341,f399,f396])).

fof(f396,plain,
    ( spl8_35
  <=> ~ v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_35])])).

fof(f399,plain,
    ( spl8_36
  <=> ! [X4] : ~ r2_hidden(X4,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_36])])).

fof(f341,plain,
    ( spl8_32
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_32])])).

fof(f372,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,sK2)
        | ~ v1_xboole_0(u1_struct_0(sK0)) )
    | ~ spl8_32 ),
    inference(resolution,[],[f342,f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f42])).

fof(f42,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_9__t21_waybel_9.p',t5_subset)).

fof(f342,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_32 ),
    inference(avatar_component_clause,[],[f341])).

fof(f343,plain,
    ( spl8_32
    | spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_16 ),
    inference(avatar_split_clause,[],[f234,f216,f154,f147,f133,f126,f119,f341])).

fof(f234,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f233,f120])).

fof(f233,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f232,f155])).

fof(f232,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1)))
    | v2_struct_0(sK0)
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_8
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f231,f148])).

fof(f231,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1)))
    | v2_struct_0(sK0)
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f230,f134])).

fof(f230,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1)))
    | v2_struct_0(sK0)
    | ~ spl8_2
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f227,f127])).

fof(f227,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1)))
    | v2_struct_0(sK0)
    | ~ spl8_16 ),
    inference(superposition,[],[f87,f217])).

fof(f313,plain,
    ( spl8_30
    | ~ spl8_28 ),
    inference(avatar_split_clause,[],[f300,f291,f311])).

fof(f311,plain,
    ( spl8_30
  <=> m1_subset_1(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_30])])).

fof(f300,plain,
    ( m1_subset_1(sK1,sK2)
    | ~ spl8_28 ),
    inference(resolution,[],[f292,f101])).

fof(f101,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f35])).

fof(f35,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_9__t21_waybel_9.p',t1_subset)).

fof(f293,plain,
    ( spl8_28
    | spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_16 ),
    inference(avatar_split_clause,[],[f244,f216,f154,f147,f133,f126,f119,f291])).

fof(f244,plain,
    ( r2_hidden(sK1,sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f243,f120])).

fof(f243,plain,
    ( r2_hidden(sK1,sK2)
    | v2_struct_0(sK0)
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f242,f155])).

fof(f242,plain,
    ( r2_hidden(sK1,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1)))
    | v2_struct_0(sK0)
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_8
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f241,f148])).

fof(f241,plain,
    ( r2_hidden(sK1,sK2)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1)))
    | v2_struct_0(sK0)
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f240,f134])).

fof(f240,plain,
    ( r2_hidden(sK1,sK2)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1)))
    | v2_struct_0(sK0)
    | ~ spl8_2
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f229,f127])).

fof(f229,plain,
    ( r2_hidden(sK1,sK2)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1)))
    | v2_struct_0(sK0)
    | ~ spl8_16 ),
    inference(superposition,[],[f89,f217])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,sK4(X0,X1,X2))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f286,plain,
    ( spl8_26
    | spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_16 ),
    inference(avatar_split_clause,[],[f239,f216,f154,f147,f133,f126,f119,f284])).

fof(f284,plain,
    ( spl8_26
  <=> v3_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).

fof(f239,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f238,f120])).

fof(f238,plain,
    ( v3_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f237,f155])).

fof(f237,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1)))
    | v2_struct_0(sK0)
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_8
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f236,f148])).

fof(f236,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1)))
    | v2_struct_0(sK0)
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f235,f134])).

fof(f235,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1)))
    | v2_struct_0(sK0)
    | ~ spl8_2
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f228,f127])).

fof(f228,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1)))
    | v2_struct_0(sK0)
    | ~ spl8_16 ),
    inference(superposition,[],[f90,f217])).

fof(f279,plain,
    ( spl8_18
    | spl8_20
    | ~ spl8_23
    | ~ spl8_25
    | ~ spl8_10 ),
    inference(avatar_split_clause,[],[f191,f154,f277,f271,f265,f259])).

fof(f259,plain,
    ( spl8_18
  <=> k9_yellow_6(k9_yellow_6(sK0,sK1),sK2) = k7_lattice3(k2_yellow_1(a_2_0_yellow_6(k9_yellow_6(sK0,sK1),sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f265,plain,
    ( spl8_20
  <=> v2_struct_0(k9_yellow_6(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).

fof(f271,plain,
    ( spl8_23
  <=> ~ l1_pre_topc(k9_yellow_6(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).

fof(f277,plain,
    ( spl8_25
  <=> ~ v2_pre_topc(k9_yellow_6(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).

fof(f191,plain,
    ( ~ v2_pre_topc(k9_yellow_6(sK0,sK1))
    | ~ l1_pre_topc(k9_yellow_6(sK0,sK1))
    | v2_struct_0(k9_yellow_6(sK0,sK1))
    | k9_yellow_6(k9_yellow_6(sK0,sK1),sK2) = k7_lattice3(k2_yellow_1(a_2_0_yellow_6(k9_yellow_6(sK0,sK1),sK2)))
    | ~ spl8_10 ),
    inference(resolution,[],[f91,f155])).

fof(f91,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | k9_yellow_6(X0,X1) = k7_lattice3(k2_yellow_1(a_2_0_yellow_6(X0,X1))) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k9_yellow_6(X0,X1) = k7_lattice3(k2_yellow_1(a_2_0_yellow_6(X0,X1)))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k9_yellow_6(X0,X1) = k7_lattice3(k2_yellow_1(a_2_0_yellow_6(X0,X1)))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k9_yellow_6(X0,X1) = k7_lattice3(k2_yellow_1(a_2_0_yellow_6(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_9__t21_waybel_9.p',d17_yellow_6)).

fof(f218,plain,
    ( spl8_16
    | spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_8
    | ~ spl8_10 ),
    inference(avatar_split_clause,[],[f210,f154,f147,f133,f126,f119,f216])).

fof(f210,plain,
    ( sK2 = sK4(sK0,sK1,sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_8
    | ~ spl8_10 ),
    inference(subsumption_resolution,[],[f209,f120])).

fof(f209,plain,
    ( v2_struct_0(sK0)
    | sK2 = sK4(sK0,sK1,sK2)
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_8
    | ~ spl8_10 ),
    inference(subsumption_resolution,[],[f208,f148])).

fof(f208,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | sK2 = sK4(sK0,sK1,sK2)
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_10 ),
    inference(subsumption_resolution,[],[f207,f134])).

fof(f207,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | sK2 = sK4(sK0,sK1,sK2)
    | ~ spl8_2
    | ~ spl8_10 ),
    inference(subsumption_resolution,[],[f205,f127])).

fof(f205,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | sK2 = sK4(sK0,sK1,sK2)
    | ~ spl8_10 ),
    inference(resolution,[],[f88,f155])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0)
      | sK4(X0,X1,X2) = X2 ) ),
    inference(cnf_transformation,[],[f57])).

fof(f202,plain,
    ( spl8_14
    | spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f195,f147,f133,f126,f119,f200])).

fof(f200,plain,
    ( spl8_14
  <=> k9_yellow_6(sK0,sK1) = k7_lattice3(k2_yellow_1(a_2_0_yellow_6(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f195,plain,
    ( k9_yellow_6(sK0,sK1) = k7_lattice3(k2_yellow_1(a_2_0_yellow_6(sK0,sK1)))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f194,f120])).

fof(f194,plain,
    ( v2_struct_0(sK0)
    | k9_yellow_6(sK0,sK1) = k7_lattice3(k2_yellow_1(a_2_0_yellow_6(sK0,sK1)))
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f193,f134])).

fof(f193,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | k9_yellow_6(sK0,sK1) = k7_lattice3(k2_yellow_1(a_2_0_yellow_6(sK0,sK1)))
    | ~ spl8_2
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f190,f127])).

fof(f190,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | k9_yellow_6(sK0,sK1) = k7_lattice3(k2_yellow_1(a_2_0_yellow_6(sK0,sK1)))
    | ~ spl8_8 ),
    inference(resolution,[],[f91,f148])).

fof(f163,plain,(
    spl8_12 ),
    inference(avatar_split_clause,[],[f106,f161])).

fof(f161,plain,
    ( spl8_12
  <=> l1_pre_topc(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f106,plain,(
    l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,axiom,(
    ? [X0] : l1_pre_topc(X0) ),
    file('/export/starexec/sandbox/benchmark/waybel_9__t21_waybel_9.p',existence_l1_pre_topc)).

fof(f156,plain,(
    spl8_10 ),
    inference(avatar_split_clause,[],[f77,f154])).

fof(f77,plain,(
    m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ m1_connsp_2(X2,X0,X1)
              & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ m1_connsp_2(X2,X0,X1)
              & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
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
                ( m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
               => m1_connsp_2(X2,X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
             => m1_connsp_2(X2,X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_9__t21_waybel_9.p',t21_waybel_9)).

fof(f149,plain,(
    spl8_8 ),
    inference(avatar_split_clause,[],[f79,f147])).

fof(f79,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f47])).

fof(f142,plain,(
    ~ spl8_7 ),
    inference(avatar_split_clause,[],[f78,f140])).

fof(f78,plain,(
    ~ m1_connsp_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f135,plain,(
    spl8_4 ),
    inference(avatar_split_clause,[],[f82,f133])).

fof(f82,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f128,plain,(
    spl8_2 ),
    inference(avatar_split_clause,[],[f81,f126])).

fof(f81,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f121,plain,(
    ~ spl8_1 ),
    inference(avatar_split_clause,[],[f80,f119])).

fof(f80,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f47])).
%------------------------------------------------------------------------------
