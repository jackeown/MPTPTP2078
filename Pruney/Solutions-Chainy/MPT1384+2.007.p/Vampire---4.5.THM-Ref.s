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
% DateTime   : Thu Dec  3 13:15:07 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.74s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 260 expanded)
%              Number of leaves         :   29 ( 108 expanded)
%              Depth                    :   16
%              Number of atoms          :  596 (1223 expanded)
%              Number of equality atoms :    6 (   9 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f403,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f61,f66,f71,f76,f85,f102,f116,f121,f130,f137,f142,f146,f158,f160,f191,f200,f218,f225,f335,f396,f402])).

fof(f402,plain,(
    spl5_19 ),
    inference(avatar_contradiction_clause,[],[f397])).

fof(f397,plain,
    ( $false
    | spl5_19 ),
    inference(unit_resulting_resolution,[],[f56,f157])).

fof(f157,plain,
    ( ~ r1_tarski(sK1,sK1)
    | spl5_19 ),
    inference(avatar_component_clause,[],[f155])).

fof(f155,plain,
    ( spl5_19
  <=> r1_tarski(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f56,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f396,plain,
    ( ~ spl5_2
    | ~ spl5_4
    | ~ spl5_3
    | spl5_5
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f361,f123,f78,f68,f73,f63])).

fof(f63,plain,
    ( spl5_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f73,plain,
    ( spl5_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f68,plain,
    ( spl5_3
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f78,plain,
    ( spl5_5
  <=> v3_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f123,plain,
    ( spl5_13
  <=> sK1 = k1_tops_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f361,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ spl5_13 ),
    inference(superposition,[],[f45,f125])).

fof(f125,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f123])).

fof(f45,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

fof(f335,plain,
    ( spl5_14
    | ~ spl5_4
    | ~ spl5_11
    | ~ spl5_15
    | ~ spl5_17
    | ~ spl5_23
    | ~ spl5_25
    | ~ spl5_26 ),
    inference(avatar_split_clause,[],[f334,f223,f216,f198,f144,f135,f114,f73,f127])).

fof(f127,plain,
    ( spl5_14
  <=> r1_tarski(sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f114,plain,
    ( spl5_11
  <=> ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r1_tarski(sK3(X2),sK1)
        | ~ r2_hidden(X2,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f135,plain,
    ( spl5_15
  <=> ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | m1_connsp_2(sK3(X2),sK0,X2)
        | ~ r2_hidden(X2,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f144,plain,
    ( spl5_17
  <=> ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | m1_subset_1(sK3(X2),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X2,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f198,plain,
    ( spl5_23
  <=> ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_connsp_2(sK1,sK0,X2)
        | r2_hidden(X2,k1_tops_1(sK0,sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f216,plain,
    ( spl5_25
  <=> ! [X5,X6] :
        ( ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ m1_connsp_2(sK3(X5),sK0,X6)
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | r2_hidden(X6,k1_tops_1(sK0,sK3(X5)))
        | ~ r2_hidden(X5,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f223,plain,
    ( spl5_26
  <=> ! [X3,X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_tarski(X3,sK1)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | m1_connsp_2(sK1,sK0,X2)
        | ~ r2_hidden(X2,k1_tops_1(sK0,X3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f334,plain,
    ( r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | ~ spl5_4
    | ~ spl5_11
    | ~ spl5_15
    | ~ spl5_17
    | ~ spl5_23
    | ~ spl5_25
    | ~ spl5_26 ),
    inference(duplicate_literal_removal,[],[f332])).

fof(f332,plain,
    ( r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | ~ spl5_4
    | ~ spl5_11
    | ~ spl5_15
    | ~ spl5_17
    | ~ spl5_23
    | ~ spl5_25
    | ~ spl5_26 ),
    inference(resolution,[],[f331,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f331,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4(X0,k1_tops_1(sK0,sK1)),sK1)
        | r1_tarski(X0,k1_tops_1(sK0,sK1)) )
    | ~ spl5_4
    | ~ spl5_11
    | ~ spl5_15
    | ~ spl5_17
    | ~ spl5_23
    | ~ spl5_25
    | ~ spl5_26 ),
    inference(duplicate_literal_removal,[],[f330])).

fof(f330,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4(X0,k1_tops_1(sK0,sK1)),sK1)
        | r1_tarski(X0,k1_tops_1(sK0,sK1))
        | ~ r2_hidden(sK4(X0,k1_tops_1(sK0,sK1)),sK1) )
    | ~ spl5_4
    | ~ spl5_11
    | ~ spl5_15
    | ~ spl5_17
    | ~ spl5_23
    | ~ spl5_25
    | ~ spl5_26 ),
    inference(resolution,[],[f325,f132])).

fof(f132,plain,
    ( ! [X0] :
        ( r1_tarski(sK3(X0),sK1)
        | ~ r2_hidden(X0,sK1) )
    | ~ spl5_4
    | ~ spl5_11 ),
    inference(duplicate_literal_removal,[],[f131])).

fof(f131,plain,
    ( ! [X0] :
        ( r1_tarski(sK3(X0),sK1)
        | ~ r2_hidden(X0,sK1)
        | ~ r2_hidden(X0,sK1) )
    | ~ spl5_4
    | ~ spl5_11 ),
    inference(resolution,[],[f115,f90])).

fof(f90,plain,
    ( ! [X3] :
        ( m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r2_hidden(X3,sK1) )
    | ~ spl5_4 ),
    inference(resolution,[],[f75,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f75,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f73])).

fof(f115,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r1_tarski(sK3(X2),sK1)
        | ~ r2_hidden(X2,sK1) )
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f114])).

fof(f325,plain,
    ( ! [X2] :
        ( ~ r1_tarski(sK3(sK4(X2,k1_tops_1(sK0,sK1))),sK1)
        | ~ r2_hidden(sK4(X2,k1_tops_1(sK0,sK1)),sK1)
        | r1_tarski(X2,k1_tops_1(sK0,sK1)) )
    | ~ spl5_4
    | ~ spl5_15
    | ~ spl5_17
    | ~ spl5_23
    | ~ spl5_25
    | ~ spl5_26 ),
    inference(duplicate_literal_removal,[],[f324])).

fof(f324,plain,
    ( ! [X2] :
        ( ~ r1_tarski(sK3(sK4(X2,k1_tops_1(sK0,sK1))),sK1)
        | ~ r2_hidden(sK4(X2,k1_tops_1(sK0,sK1)),sK1)
        | r1_tarski(X2,k1_tops_1(sK0,sK1))
        | ~ r2_hidden(sK4(X2,k1_tops_1(sK0,sK1)),sK1) )
    | ~ spl5_4
    | ~ spl5_15
    | ~ spl5_17
    | ~ spl5_23
    | ~ spl5_25
    | ~ spl5_26 ),
    inference(resolution,[],[f253,f90])).

fof(f253,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK4(X0,k1_tops_1(sK0,sK1)),u1_struct_0(sK0))
        | ~ r1_tarski(sK3(sK4(X0,k1_tops_1(sK0,sK1))),sK1)
        | ~ r2_hidden(sK4(X0,k1_tops_1(sK0,sK1)),sK1)
        | r1_tarski(X0,k1_tops_1(sK0,sK1)) )
    | ~ spl5_15
    | ~ spl5_17
    | ~ spl5_23
    | ~ spl5_25
    | ~ spl5_26 ),
    inference(duplicate_literal_removal,[],[f252])).

fof(f252,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK3(sK4(X0,k1_tops_1(sK0,sK1))),sK1)
        | ~ m1_subset_1(sK4(X0,k1_tops_1(sK0,sK1)),u1_struct_0(sK0))
        | ~ r2_hidden(sK4(X0,k1_tops_1(sK0,sK1)),sK1)
        | ~ m1_subset_1(sK4(X0,k1_tops_1(sK0,sK1)),u1_struct_0(sK0))
        | r1_tarski(X0,k1_tops_1(sK0,sK1)) )
    | ~ spl5_15
    | ~ spl5_17
    | ~ spl5_23
    | ~ spl5_25
    | ~ spl5_26 ),
    inference(resolution,[],[f250,f201])).

fof(f201,plain,
    ( ! [X0] :
        ( ~ m1_connsp_2(sK1,sK0,sK4(X0,k1_tops_1(sK0,sK1)))
        | ~ m1_subset_1(sK4(X0,k1_tops_1(sK0,sK1)),u1_struct_0(sK0))
        | r1_tarski(X0,k1_tops_1(sK0,sK1)) )
    | ~ spl5_23 ),
    inference(resolution,[],[f199,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f199,plain,
    ( ! [X2] :
        ( r2_hidden(X2,k1_tops_1(sK0,sK1))
        | ~ m1_connsp_2(sK1,sK0,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
    | ~ spl5_23 ),
    inference(avatar_component_clause,[],[f198])).

fof(f250,plain,
    ( ! [X0] :
        ( m1_connsp_2(sK1,sK0,X0)
        | ~ r1_tarski(sK3(X0),sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,sK1) )
    | ~ spl5_15
    | ~ spl5_17
    | ~ spl5_25
    | ~ spl5_26 ),
    inference(duplicate_literal_removal,[],[f247])).

fof(f247,plain,
    ( ! [X0] :
        ( m1_connsp_2(sK1,sK0,X0)
        | ~ r1_tarski(sK3(X0),sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,sK1) )
    | ~ spl5_15
    | ~ spl5_17
    | ~ spl5_25
    | ~ spl5_26 ),
    inference(resolution,[],[f246,f136])).

fof(f136,plain,
    ( ! [X2] :
        ( m1_connsp_2(sK3(X2),sK0,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_hidden(X2,sK1) )
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f135])).

fof(f246,plain,
    ( ! [X2,X3] :
        ( ~ m1_connsp_2(sK3(X3),sK0,X2)
        | m1_connsp_2(sK1,sK0,X2)
        | ~ r1_tarski(sK3(X3),sK1)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r2_hidden(X3,sK1)
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
    | ~ spl5_17
    | ~ spl5_25
    | ~ spl5_26 ),
    inference(duplicate_literal_removal,[],[f244])).

fof(f244,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | m1_connsp_2(sK1,sK0,X2)
        | ~ r1_tarski(sK3(X3),sK1)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r2_hidden(X3,sK1)
        | ~ m1_connsp_2(sK3(X3),sK0,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r2_hidden(X3,sK1) )
    | ~ spl5_17
    | ~ spl5_25
    | ~ spl5_26 ),
    inference(resolution,[],[f233,f217])).

fof(f217,plain,
    ( ! [X6,X5] :
        ( r2_hidden(X6,k1_tops_1(sK0,sK3(X5)))
        | ~ m1_connsp_2(sK3(X5),sK0,X6)
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ r2_hidden(X5,sK1) )
    | ~ spl5_25 ),
    inference(avatar_component_clause,[],[f216])).

fof(f233,plain,
    ( ! [X6,X7] :
        ( ~ r2_hidden(X7,k1_tops_1(sK0,sK3(X6)))
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | m1_connsp_2(sK1,sK0,X7)
        | ~ r1_tarski(sK3(X6),sK1)
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ r2_hidden(X6,sK1) )
    | ~ spl5_17
    | ~ spl5_26 ),
    inference(resolution,[],[f224,f145])).

fof(f145,plain,
    ( ! [X2] :
        ( m1_subset_1(sK3(X2),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_hidden(X2,sK1) )
    | ~ spl5_17 ),
    inference(avatar_component_clause,[],[f144])).

fof(f224,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X3,sK1)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | m1_connsp_2(sK1,sK0,X2)
        | ~ r2_hidden(X2,k1_tops_1(sK0,X3)) )
    | ~ spl5_26 ),
    inference(avatar_component_clause,[],[f223])).

fof(f225,plain,
    ( ~ spl5_3
    | ~ spl5_4
    | spl5_26
    | ~ spl5_22 ),
    inference(avatar_split_clause,[],[f196,f189,f223,f73,f68])).

fof(f189,plain,
    ( spl5_22
  <=> ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | m1_connsp_2(sK1,sK0,X1)
        | ~ r2_hidden(X1,k1_tops_1(sK0,sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f196,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_hidden(X2,k1_tops_1(sK0,X3))
        | m1_connsp_2(sK1,sK0,X2)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X3,sK1)
        | ~ l1_pre_topc(sK0) )
    | ~ spl5_22 ),
    inference(resolution,[],[f193,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X1,X2)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).

fof(f193,plain,
    ( ! [X2,X1] :
        ( ~ r1_tarski(X2,k1_tops_1(sK0,sK1))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X1,X2)
        | m1_connsp_2(sK1,sK0,X1) )
    | ~ spl5_22 ),
    inference(resolution,[],[f190,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f190,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k1_tops_1(sK0,sK1))
        | m1_connsp_2(sK1,sK0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl5_22 ),
    inference(avatar_component_clause,[],[f189])).

fof(f218,plain,
    ( spl5_1
    | ~ spl5_3
    | ~ spl5_2
    | spl5_25
    | ~ spl5_17 ),
    inference(avatar_split_clause,[],[f165,f144,f216,f63,f68,f58])).

fof(f58,plain,
    ( spl5_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f165,plain,
    ( ! [X6,X5] :
        ( ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ r2_hidden(X5,sK1)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | r2_hidden(X6,k1_tops_1(sK0,sK3(X5)))
        | ~ m1_connsp_2(sK3(X5),sK0,X6) )
    | ~ spl5_17 ),
    inference(resolution,[],[f145,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0)
      | r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_connsp_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
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
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_connsp_2)).

fof(f200,plain,
    ( spl5_1
    | spl5_23
    | ~ spl5_3
    | ~ spl5_2
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f88,f73,f63,f68,f198,f58])).

fof(f88,plain,
    ( ! [X2] :
        ( ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | r2_hidden(X2,k1_tops_1(sK0,sK1))
        | ~ m1_connsp_2(sK1,sK0,X2) )
    | ~ spl5_4 ),
    inference(resolution,[],[f75,f42])).

fof(f191,plain,
    ( spl5_1
    | spl5_22
    | ~ spl5_3
    | ~ spl5_2
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f87,f73,f63,f68,f189,f58])).

fof(f87,plain,
    ( ! [X1] :
        ( ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | ~ r2_hidden(X1,k1_tops_1(sK0,sK1))
        | m1_connsp_2(sK1,sK0,X1) )
    | ~ spl5_4 ),
    inference(resolution,[],[f75,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0)
      | ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | m1_connsp_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f160,plain,
    ( spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_12
    | spl5_18 ),
    inference(avatar_contradiction_clause,[],[f159])).

fof(f159,plain,
    ( $false
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_12
    | spl5_18 ),
    inference(unit_resulting_resolution,[],[f65,f70,f60,f84,f79,f120,f75,f153,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v3_pre_topc(X1,X0)
      | ~ r2_hidden(X2,X1)
      | m1_connsp_2(X1,X0,X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_connsp_2)).

fof(f153,plain,
    ( ~ m1_connsp_2(sK1,sK0,sK2)
    | spl5_18 ),
    inference(avatar_component_clause,[],[f151])).

fof(f151,plain,
    ( spl5_18
  <=> m1_connsp_2(sK1,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f120,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f118])).

fof(f118,plain,
    ( spl5_12
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f79,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f78])).

fof(f84,plain,
    ( r2_hidden(sK2,sK1)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl5_6
  <=> r2_hidden(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f60,plain,
    ( ~ v2_struct_0(sK0)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f58])).

fof(f70,plain,
    ( l1_pre_topc(sK0)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f68])).

fof(f65,plain,
    ( v2_pre_topc(sK0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f63])).

fof(f158,plain,
    ( ~ spl5_18
    | ~ spl5_19
    | ~ spl5_4
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f149,f140,f73,f155,f151])).

fof(f140,plain,
    ( spl5_16
  <=> ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X3,sK1)
        | ~ m1_connsp_2(X3,sK0,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f149,plain,
    ( ~ r1_tarski(sK1,sK1)
    | ~ m1_connsp_2(sK1,sK0,sK2)
    | ~ spl5_4
    | ~ spl5_16 ),
    inference(resolution,[],[f141,f75])).

fof(f141,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X3,sK1)
        | ~ m1_connsp_2(X3,sK0,sK2) )
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f140])).

fof(f146,plain,
    ( spl5_5
    | spl5_17 ),
    inference(avatar_split_clause,[],[f29,f144,f78])).

fof(f29,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r2_hidden(X2,sK1)
      | m1_subset_1(sK3(X2),k1_zfmisc_1(u1_struct_0(sK0)))
      | v3_pre_topc(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> ! [X2] :
                ( ? [X3] :
                    ( r1_tarski(X3,X1)
                    & m1_connsp_2(X3,X0,X2)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> ! [X2] :
                ( ? [X3] :
                    ( r1_tarski(X3,X1)
                    & m1_connsp_2(X3,X0,X2)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
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
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
            <=> ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ~ ( ! [X3] :
                          ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                         => ~ ( r1_tarski(X3,X1)
                              & m1_connsp_2(X3,X0,X2) ) )
                      & r2_hidden(X2,X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ~ ( r1_tarski(X3,X1)
                            & m1_connsp_2(X3,X0,X2) ) )
                    & r2_hidden(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_connsp_2)).

fof(f142,plain,
    ( ~ spl5_5
    | spl5_16 ),
    inference(avatar_split_clause,[],[f32,f140,f78])).

fof(f32,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_connsp_2(X3,sK0,sK2)
      | ~ r1_tarski(X3,sK1)
      | ~ v3_pre_topc(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f137,plain,
    ( spl5_5
    | spl5_15 ),
    inference(avatar_split_clause,[],[f30,f135,f78])).

fof(f30,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r2_hidden(X2,sK1)
      | m1_connsp_2(sK3(X2),sK0,X2)
      | v3_pre_topc(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f130,plain,
    ( spl5_13
    | ~ spl5_14
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f103,f99,f127,f123])).

fof(f99,plain,
    ( spl5_8
  <=> r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f103,plain,
    ( ~ r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | sK1 = k1_tops_1(sK0,sK1)
    | ~ spl5_8 ),
    inference(resolution,[],[f101,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f101,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f99])).

fof(f121,plain,
    ( ~ spl5_5
    | spl5_12 ),
    inference(avatar_split_clause,[],[f33,f118,f78])).

fof(f33,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f116,plain,
    ( spl5_5
    | spl5_11 ),
    inference(avatar_split_clause,[],[f31,f114,f78])).

fof(f31,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r2_hidden(X2,sK1)
      | r1_tarski(sK3(X2),sK1)
      | v3_pre_topc(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f102,plain,
    ( spl5_8
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f89,f73,f68,f99])).

fof(f89,plain,
    ( ~ l1_pre_topc(sK0)
    | r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl5_4 ),
    inference(resolution,[],[f75,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | r1_tarski(k1_tops_1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

fof(f85,plain,
    ( ~ spl5_5
    | spl5_6 ),
    inference(avatar_split_clause,[],[f34,f82,f78])).

fof(f34,plain,
    ( r2_hidden(sK2,sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f76,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f35,f73])).

fof(f35,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f14])).

fof(f71,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f38,f68])).

fof(f38,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f66,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f37,f63])).

fof(f37,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f61,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f36,f58])).

fof(f36,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:28:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.51  % (20831)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (20833)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.53  % (20839)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.53  % (20827)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (20840)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.54  % (20836)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.54  % (20829)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (20846)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.54  % (20847)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.54  % (20830)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (20856)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.54  % (20834)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.54  % (20848)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.54  % (20841)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.55  % (20826)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.55  % (20852)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.55  % (20832)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.55  % (20828)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.55  % (20854)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.55  % (20845)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.55  % (20844)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.55  % (20837)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.56  % (20838)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.56  % (20849)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.56  % (20850)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.56  % (20853)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.56  % (20835)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.56  % (20842)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.56  % (20851)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.57  % (20843)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.57  % (20852)Refutation not found, incomplete strategy% (20852)------------------------------
% 0.21/0.57  % (20852)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (20852)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (20852)Memory used [KB]: 10746
% 0.21/0.57  % (20852)Time elapsed: 0.159 s
% 0.21/0.57  % (20852)------------------------------
% 0.21/0.57  % (20852)------------------------------
% 0.21/0.57  % (20848)Refutation found. Thanks to Tanya!
% 0.21/0.57  % SZS status Theorem for theBenchmark
% 0.21/0.57  % SZS output start Proof for theBenchmark
% 0.21/0.57  fof(f403,plain,(
% 0.21/0.57    $false),
% 0.21/0.57    inference(avatar_sat_refutation,[],[f61,f66,f71,f76,f85,f102,f116,f121,f130,f137,f142,f146,f158,f160,f191,f200,f218,f225,f335,f396,f402])).
% 1.74/0.59  fof(f402,plain,(
% 1.74/0.59    spl5_19),
% 1.74/0.59    inference(avatar_contradiction_clause,[],[f397])).
% 1.74/0.59  fof(f397,plain,(
% 1.74/0.59    $false | spl5_19),
% 1.74/0.59    inference(unit_resulting_resolution,[],[f56,f157])).
% 1.74/0.59  fof(f157,plain,(
% 1.74/0.59    ~r1_tarski(sK1,sK1) | spl5_19),
% 1.74/0.59    inference(avatar_component_clause,[],[f155])).
% 1.74/0.59  fof(f155,plain,(
% 1.74/0.59    spl5_19 <=> r1_tarski(sK1,sK1)),
% 1.74/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 1.74/0.59  fof(f56,plain,(
% 1.74/0.59    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.74/0.59    inference(equality_resolution,[],[f46])).
% 1.74/0.59  fof(f46,plain,(
% 1.74/0.59    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 1.74/0.59    inference(cnf_transformation,[],[f2])).
% 1.74/0.59  fof(f2,axiom,(
% 1.74/0.59    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.74/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.74/0.59  fof(f396,plain,(
% 1.74/0.59    ~spl5_2 | ~spl5_4 | ~spl5_3 | spl5_5 | ~spl5_13),
% 1.74/0.59    inference(avatar_split_clause,[],[f361,f123,f78,f68,f73,f63])).
% 1.74/0.59  fof(f63,plain,(
% 1.74/0.59    spl5_2 <=> v2_pre_topc(sK0)),
% 1.74/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.74/0.59  fof(f73,plain,(
% 1.74/0.59    spl5_4 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.74/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 1.74/0.59  fof(f68,plain,(
% 1.74/0.59    spl5_3 <=> l1_pre_topc(sK0)),
% 1.74/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.74/0.60  fof(f78,plain,(
% 1.74/0.60    spl5_5 <=> v3_pre_topc(sK1,sK0)),
% 1.74/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 1.74/0.60  fof(f123,plain,(
% 1.74/0.60    spl5_13 <=> sK1 = k1_tops_1(sK0,sK1)),
% 1.74/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 1.74/0.60  fof(f361,plain,(
% 1.74/0.60    v3_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | ~spl5_13),
% 1.74/0.60    inference(superposition,[],[f45,f125])).
% 1.74/0.60  fof(f125,plain,(
% 1.74/0.60    sK1 = k1_tops_1(sK0,sK1) | ~spl5_13),
% 1.74/0.60    inference(avatar_component_clause,[],[f123])).
% 1.74/0.60  fof(f45,plain,(
% 1.74/0.60    ( ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0)) )),
% 1.74/0.60    inference(cnf_transformation,[],[f25])).
% 1.74/0.60  fof(f25,plain,(
% 1.74/0.60    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.74/0.60    inference(flattening,[],[f24])).
% 1.74/0.60  fof(f24,plain,(
% 1.74/0.60    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.74/0.60    inference(ennf_transformation,[],[f5])).
% 1.74/0.60  fof(f5,axiom,(
% 1.74/0.60    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 1.74/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).
% 1.74/0.60  fof(f335,plain,(
% 1.74/0.60    spl5_14 | ~spl5_4 | ~spl5_11 | ~spl5_15 | ~spl5_17 | ~spl5_23 | ~spl5_25 | ~spl5_26),
% 1.74/0.60    inference(avatar_split_clause,[],[f334,f223,f216,f198,f144,f135,f114,f73,f127])).
% 1.74/0.60  fof(f127,plain,(
% 1.74/0.60    spl5_14 <=> r1_tarski(sK1,k1_tops_1(sK0,sK1))),
% 1.74/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 1.74/0.60  fof(f114,plain,(
% 1.74/0.60    spl5_11 <=> ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | r1_tarski(sK3(X2),sK1) | ~r2_hidden(X2,sK1))),
% 1.74/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 1.74/0.60  fof(f135,plain,(
% 1.74/0.60    spl5_15 <=> ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | m1_connsp_2(sK3(X2),sK0,X2) | ~r2_hidden(X2,sK1))),
% 1.74/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 1.74/0.60  fof(f144,plain,(
% 1.74/0.60    spl5_17 <=> ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | m1_subset_1(sK3(X2),k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X2,sK1))),
% 1.74/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 1.74/0.60  fof(f198,plain,(
% 1.74/0.60    spl5_23 <=> ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_connsp_2(sK1,sK0,X2) | r2_hidden(X2,k1_tops_1(sK0,sK1)))),
% 1.74/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).
% 1.74/0.60  fof(f216,plain,(
% 1.74/0.60    spl5_25 <=> ! [X5,X6] : (~m1_subset_1(X5,u1_struct_0(sK0)) | ~m1_connsp_2(sK3(X5),sK0,X6) | ~m1_subset_1(X6,u1_struct_0(sK0)) | r2_hidden(X6,k1_tops_1(sK0,sK3(X5))) | ~r2_hidden(X5,sK1))),
% 1.74/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).
% 1.74/0.60  fof(f223,plain,(
% 1.74/0.60    spl5_26 <=> ! [X3,X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | ~r1_tarski(X3,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | m1_connsp_2(sK1,sK0,X2) | ~r2_hidden(X2,k1_tops_1(sK0,X3)))),
% 1.74/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).
% 1.74/0.60  fof(f334,plain,(
% 1.74/0.60    r1_tarski(sK1,k1_tops_1(sK0,sK1)) | (~spl5_4 | ~spl5_11 | ~spl5_15 | ~spl5_17 | ~spl5_23 | ~spl5_25 | ~spl5_26)),
% 1.74/0.60    inference(duplicate_literal_removal,[],[f332])).
% 1.74/0.60  fof(f332,plain,(
% 1.74/0.60    r1_tarski(sK1,k1_tops_1(sK0,sK1)) | r1_tarski(sK1,k1_tops_1(sK0,sK1)) | (~spl5_4 | ~spl5_11 | ~spl5_15 | ~spl5_17 | ~spl5_23 | ~spl5_25 | ~spl5_26)),
% 1.74/0.60    inference(resolution,[],[f331,f50])).
% 1.74/0.60  fof(f50,plain,(
% 1.74/0.60    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.74/0.60    inference(cnf_transformation,[],[f26])).
% 1.74/0.60  fof(f26,plain,(
% 1.74/0.60    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.74/0.60    inference(ennf_transformation,[],[f1])).
% 1.74/0.60  fof(f1,axiom,(
% 1.74/0.60    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.74/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.74/0.60  fof(f331,plain,(
% 1.74/0.60    ( ! [X0] : (~r2_hidden(sK4(X0,k1_tops_1(sK0,sK1)),sK1) | r1_tarski(X0,k1_tops_1(sK0,sK1))) ) | (~spl5_4 | ~spl5_11 | ~spl5_15 | ~spl5_17 | ~spl5_23 | ~spl5_25 | ~spl5_26)),
% 1.74/0.60    inference(duplicate_literal_removal,[],[f330])).
% 1.74/0.60  fof(f330,plain,(
% 1.74/0.60    ( ! [X0] : (~r2_hidden(sK4(X0,k1_tops_1(sK0,sK1)),sK1) | r1_tarski(X0,k1_tops_1(sK0,sK1)) | ~r2_hidden(sK4(X0,k1_tops_1(sK0,sK1)),sK1)) ) | (~spl5_4 | ~spl5_11 | ~spl5_15 | ~spl5_17 | ~spl5_23 | ~spl5_25 | ~spl5_26)),
% 1.74/0.60    inference(resolution,[],[f325,f132])).
% 1.74/0.60  fof(f132,plain,(
% 1.74/0.60    ( ! [X0] : (r1_tarski(sK3(X0),sK1) | ~r2_hidden(X0,sK1)) ) | (~spl5_4 | ~spl5_11)),
% 1.74/0.60    inference(duplicate_literal_removal,[],[f131])).
% 1.74/0.60  fof(f131,plain,(
% 1.74/0.60    ( ! [X0] : (r1_tarski(sK3(X0),sK1) | ~r2_hidden(X0,sK1) | ~r2_hidden(X0,sK1)) ) | (~spl5_4 | ~spl5_11)),
% 1.74/0.60    inference(resolution,[],[f115,f90])).
% 1.74/0.60  fof(f90,plain,(
% 1.74/0.60    ( ! [X3] : (m1_subset_1(X3,u1_struct_0(sK0)) | ~r2_hidden(X3,sK1)) ) | ~spl5_4),
% 1.74/0.60    inference(resolution,[],[f75,f54])).
% 1.74/0.60  fof(f54,plain,(
% 1.74/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1) | m1_subset_1(X0,X2)) )),
% 1.74/0.60    inference(cnf_transformation,[],[f28])).
% 1.74/0.60  fof(f28,plain,(
% 1.74/0.60    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.74/0.60    inference(flattening,[],[f27])).
% 1.74/0.60  fof(f27,plain,(
% 1.74/0.60    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 1.74/0.60    inference(ennf_transformation,[],[f4])).
% 1.74/0.60  fof(f4,axiom,(
% 1.74/0.60    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 1.74/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 1.74/0.60  fof(f75,plain,(
% 1.74/0.60    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_4),
% 1.74/0.60    inference(avatar_component_clause,[],[f73])).
% 1.74/0.60  fof(f115,plain,(
% 1.74/0.60    ( ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | r1_tarski(sK3(X2),sK1) | ~r2_hidden(X2,sK1)) ) | ~spl5_11),
% 1.74/0.60    inference(avatar_component_clause,[],[f114])).
% 1.74/0.60  fof(f325,plain,(
% 1.74/0.60    ( ! [X2] : (~r1_tarski(sK3(sK4(X2,k1_tops_1(sK0,sK1))),sK1) | ~r2_hidden(sK4(X2,k1_tops_1(sK0,sK1)),sK1) | r1_tarski(X2,k1_tops_1(sK0,sK1))) ) | (~spl5_4 | ~spl5_15 | ~spl5_17 | ~spl5_23 | ~spl5_25 | ~spl5_26)),
% 1.74/0.60    inference(duplicate_literal_removal,[],[f324])).
% 1.74/0.60  fof(f324,plain,(
% 1.74/0.60    ( ! [X2] : (~r1_tarski(sK3(sK4(X2,k1_tops_1(sK0,sK1))),sK1) | ~r2_hidden(sK4(X2,k1_tops_1(sK0,sK1)),sK1) | r1_tarski(X2,k1_tops_1(sK0,sK1)) | ~r2_hidden(sK4(X2,k1_tops_1(sK0,sK1)),sK1)) ) | (~spl5_4 | ~spl5_15 | ~spl5_17 | ~spl5_23 | ~spl5_25 | ~spl5_26)),
% 1.74/0.60    inference(resolution,[],[f253,f90])).
% 1.74/0.60  fof(f253,plain,(
% 1.74/0.60    ( ! [X0] : (~m1_subset_1(sK4(X0,k1_tops_1(sK0,sK1)),u1_struct_0(sK0)) | ~r1_tarski(sK3(sK4(X0,k1_tops_1(sK0,sK1))),sK1) | ~r2_hidden(sK4(X0,k1_tops_1(sK0,sK1)),sK1) | r1_tarski(X0,k1_tops_1(sK0,sK1))) ) | (~spl5_15 | ~spl5_17 | ~spl5_23 | ~spl5_25 | ~spl5_26)),
% 1.74/0.60    inference(duplicate_literal_removal,[],[f252])).
% 1.74/0.60  fof(f252,plain,(
% 1.74/0.60    ( ! [X0] : (~r1_tarski(sK3(sK4(X0,k1_tops_1(sK0,sK1))),sK1) | ~m1_subset_1(sK4(X0,k1_tops_1(sK0,sK1)),u1_struct_0(sK0)) | ~r2_hidden(sK4(X0,k1_tops_1(sK0,sK1)),sK1) | ~m1_subset_1(sK4(X0,k1_tops_1(sK0,sK1)),u1_struct_0(sK0)) | r1_tarski(X0,k1_tops_1(sK0,sK1))) ) | (~spl5_15 | ~spl5_17 | ~spl5_23 | ~spl5_25 | ~spl5_26)),
% 1.74/0.60    inference(resolution,[],[f250,f201])).
% 1.74/0.60  fof(f201,plain,(
% 1.74/0.60    ( ! [X0] : (~m1_connsp_2(sK1,sK0,sK4(X0,k1_tops_1(sK0,sK1))) | ~m1_subset_1(sK4(X0,k1_tops_1(sK0,sK1)),u1_struct_0(sK0)) | r1_tarski(X0,k1_tops_1(sK0,sK1))) ) | ~spl5_23),
% 1.74/0.60    inference(resolution,[],[f199,f51])).
% 1.74/0.60  fof(f51,plain,(
% 1.74/0.60    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.74/0.60    inference(cnf_transformation,[],[f26])).
% 1.74/0.60  fof(f199,plain,(
% 1.74/0.60    ( ! [X2] : (r2_hidden(X2,k1_tops_1(sK0,sK1)) | ~m1_connsp_2(sK1,sK0,X2) | ~m1_subset_1(X2,u1_struct_0(sK0))) ) | ~spl5_23),
% 1.74/0.60    inference(avatar_component_clause,[],[f198])).
% 1.74/0.60  fof(f250,plain,(
% 1.74/0.60    ( ! [X0] : (m1_connsp_2(sK1,sK0,X0) | ~r1_tarski(sK3(X0),sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,sK1)) ) | (~spl5_15 | ~spl5_17 | ~spl5_25 | ~spl5_26)),
% 1.74/0.60    inference(duplicate_literal_removal,[],[f247])).
% 1.74/0.60  fof(f247,plain,(
% 1.74/0.60    ( ! [X0] : (m1_connsp_2(sK1,sK0,X0) | ~r1_tarski(sK3(X0),sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,sK1)) ) | (~spl5_15 | ~spl5_17 | ~spl5_25 | ~spl5_26)),
% 1.74/0.60    inference(resolution,[],[f246,f136])).
% 1.74/0.60  fof(f136,plain,(
% 1.74/0.60    ( ! [X2] : (m1_connsp_2(sK3(X2),sK0,X2) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_hidden(X2,sK1)) ) | ~spl5_15),
% 1.74/0.60    inference(avatar_component_clause,[],[f135])).
% 1.74/0.60  fof(f246,plain,(
% 1.74/0.60    ( ! [X2,X3] : (~m1_connsp_2(sK3(X3),sK0,X2) | m1_connsp_2(sK1,sK0,X2) | ~r1_tarski(sK3(X3),sK1) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~r2_hidden(X3,sK1) | ~m1_subset_1(X2,u1_struct_0(sK0))) ) | (~spl5_17 | ~spl5_25 | ~spl5_26)),
% 1.74/0.60    inference(duplicate_literal_removal,[],[f244])).
% 1.74/0.60  fof(f244,plain,(
% 1.74/0.60    ( ! [X2,X3] : (~m1_subset_1(X2,u1_struct_0(sK0)) | m1_connsp_2(sK1,sK0,X2) | ~r1_tarski(sK3(X3),sK1) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~r2_hidden(X3,sK1) | ~m1_connsp_2(sK3(X3),sK0,X2) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~r2_hidden(X3,sK1)) ) | (~spl5_17 | ~spl5_25 | ~spl5_26)),
% 1.74/0.60    inference(resolution,[],[f233,f217])).
% 1.74/0.60  fof(f217,plain,(
% 1.74/0.60    ( ! [X6,X5] : (r2_hidden(X6,k1_tops_1(sK0,sK3(X5))) | ~m1_connsp_2(sK3(X5),sK0,X6) | ~m1_subset_1(X6,u1_struct_0(sK0)) | ~m1_subset_1(X5,u1_struct_0(sK0)) | ~r2_hidden(X5,sK1)) ) | ~spl5_25),
% 1.74/0.60    inference(avatar_component_clause,[],[f216])).
% 1.74/0.60  fof(f233,plain,(
% 1.74/0.60    ( ! [X6,X7] : (~r2_hidden(X7,k1_tops_1(sK0,sK3(X6))) | ~m1_subset_1(X7,u1_struct_0(sK0)) | m1_connsp_2(sK1,sK0,X7) | ~r1_tarski(sK3(X6),sK1) | ~m1_subset_1(X6,u1_struct_0(sK0)) | ~r2_hidden(X6,sK1)) ) | (~spl5_17 | ~spl5_26)),
% 1.74/0.60    inference(resolution,[],[f224,f145])).
% 1.74/0.60  fof(f145,plain,(
% 1.74/0.60    ( ! [X2] : (m1_subset_1(sK3(X2),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_hidden(X2,sK1)) ) | ~spl5_17),
% 1.74/0.60    inference(avatar_component_clause,[],[f144])).
% 1.74/0.60  fof(f224,plain,(
% 1.74/0.60    ( ! [X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X3,sK1) | ~m1_subset_1(X2,u1_struct_0(sK0)) | m1_connsp_2(sK1,sK0,X2) | ~r2_hidden(X2,k1_tops_1(sK0,X3))) ) | ~spl5_26),
% 1.74/0.60    inference(avatar_component_clause,[],[f223])).
% 1.74/0.60  fof(f225,plain,(
% 1.74/0.60    ~spl5_3 | ~spl5_4 | spl5_26 | ~spl5_22),
% 1.74/0.60    inference(avatar_split_clause,[],[f196,f189,f223,f73,f68])).
% 1.74/0.60  fof(f189,plain,(
% 1.74/0.60    spl5_22 <=> ! [X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | m1_connsp_2(sK1,sK0,X1) | ~r2_hidden(X1,k1_tops_1(sK0,sK1)))),
% 1.74/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 1.74/0.60  fof(f196,plain,(
% 1.74/0.60    ( ! [X2,X3] : (~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_hidden(X2,k1_tops_1(sK0,X3)) | m1_connsp_2(sK1,sK0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X3,sK1) | ~l1_pre_topc(sK0)) ) | ~spl5_22),
% 1.74/0.60    inference(resolution,[],[f193,f40])).
% 1.74/0.60  fof(f40,plain,(
% 1.74/0.60    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X1,X2) | ~l1_pre_topc(X0)) )),
% 1.74/0.60    inference(cnf_transformation,[],[f17])).
% 1.74/0.60  fof(f17,plain,(
% 1.74/0.60    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.74/0.60    inference(flattening,[],[f16])).
% 1.74/0.60  fof(f16,plain,(
% 1.74/0.60    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.74/0.60    inference(ennf_transformation,[],[f7])).
% 1.74/0.60  fof(f7,axiom,(
% 1.74/0.60    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 1.74/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).
% 1.74/0.60  fof(f193,plain,(
% 1.74/0.60    ( ! [X2,X1] : (~r1_tarski(X2,k1_tops_1(sK0,sK1)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X1,X2) | m1_connsp_2(sK1,sK0,X1)) ) | ~spl5_22),
% 1.74/0.60    inference(resolution,[],[f190,f49])).
% 1.74/0.60  fof(f49,plain,(
% 1.74/0.60    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(X0,X1)) )),
% 1.74/0.60    inference(cnf_transformation,[],[f26])).
% 1.74/0.60  fof(f190,plain,(
% 1.74/0.60    ( ! [X1] : (~r2_hidden(X1,k1_tops_1(sK0,sK1)) | m1_connsp_2(sK1,sK0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | ~spl5_22),
% 1.74/0.60    inference(avatar_component_clause,[],[f189])).
% 1.74/0.60  fof(f218,plain,(
% 1.74/0.60    spl5_1 | ~spl5_3 | ~spl5_2 | spl5_25 | ~spl5_17),
% 1.74/0.60    inference(avatar_split_clause,[],[f165,f144,f216,f63,f68,f58])).
% 1.74/0.60  fof(f58,plain,(
% 1.74/0.60    spl5_1 <=> v2_struct_0(sK0)),
% 1.74/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.74/0.60  fof(f165,plain,(
% 1.74/0.60    ( ! [X6,X5] : (~m1_subset_1(X5,u1_struct_0(sK0)) | ~r2_hidden(X5,sK1) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X6,u1_struct_0(sK0)) | v2_struct_0(sK0) | r2_hidden(X6,k1_tops_1(sK0,sK3(X5))) | ~m1_connsp_2(sK3(X5),sK0,X6)) ) | ~spl5_17),
% 1.74/0.60    inference(resolution,[],[f145,f42])).
% 1.74/0.60  fof(f42,plain,(
% 1.74/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0) | r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1)) )),
% 1.74/0.60    inference(cnf_transformation,[],[f19])).
% 1.74/0.60  fof(f19,plain,(
% 1.74/0.60    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.74/0.60    inference(flattening,[],[f18])).
% 1.74/0.60  fof(f18,plain,(
% 1.74/0.60    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.74/0.60    inference(ennf_transformation,[],[f8])).
% 1.74/0.60  fof(f8,axiom,(
% 1.74/0.60    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))))))),
% 1.74/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_connsp_2)).
% 1.74/0.60  fof(f200,plain,(
% 1.74/0.60    spl5_1 | spl5_23 | ~spl5_3 | ~spl5_2 | ~spl5_4),
% 1.74/0.60    inference(avatar_split_clause,[],[f88,f73,f63,f68,f198,f58])).
% 1.74/0.60  fof(f88,plain,(
% 1.74/0.60    ( ! [X2] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | v2_struct_0(sK0) | r2_hidden(X2,k1_tops_1(sK0,sK1)) | ~m1_connsp_2(sK1,sK0,X2)) ) | ~spl5_4),
% 1.74/0.60    inference(resolution,[],[f75,f42])).
% 1.74/0.60  fof(f191,plain,(
% 1.74/0.60    spl5_1 | spl5_22 | ~spl5_3 | ~spl5_2 | ~spl5_4),
% 1.74/0.60    inference(avatar_split_clause,[],[f87,f73,f63,f68,f189,f58])).
% 1.74/0.60  fof(f87,plain,(
% 1.74/0.60    ( ! [X1] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | v2_struct_0(sK0) | ~r2_hidden(X1,k1_tops_1(sK0,sK1)) | m1_connsp_2(sK1,sK0,X1)) ) | ~spl5_4),
% 1.74/0.60    inference(resolution,[],[f75,f41])).
% 1.74/0.60  fof(f41,plain,(
% 1.74/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0) | ~r2_hidden(X1,k1_tops_1(X0,X2)) | m1_connsp_2(X2,X0,X1)) )),
% 1.74/0.60    inference(cnf_transformation,[],[f19])).
% 1.74/0.60  fof(f160,plain,(
% 1.74/0.60    spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_12 | spl5_18),
% 1.74/0.60    inference(avatar_contradiction_clause,[],[f159])).
% 1.74/0.60  fof(f159,plain,(
% 1.74/0.60    $false | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_12 | spl5_18)),
% 1.74/0.60    inference(unit_resulting_resolution,[],[f65,f70,f60,f84,f79,f120,f75,f153,f43])).
% 1.74/0.60  fof(f43,plain,(
% 1.74/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~v3_pre_topc(X1,X0) | ~r2_hidden(X2,X1) | m1_connsp_2(X1,X0,X2)) )),
% 1.74/0.60    inference(cnf_transformation,[],[f21])).
% 1.74/0.60  fof(f21,plain,(
% 1.74/0.60    ! [X0] : (! [X1] : (! [X2] : (m1_connsp_2(X1,X0,X2) | ~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.74/0.60    inference(flattening,[],[f20])).
% 1.74/0.60  fof(f20,plain,(
% 1.74/0.60    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X1,X0,X2) | (~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.74/0.60    inference(ennf_transformation,[],[f10])).
% 1.74/0.61  fof(f10,axiom,(
% 1.74/0.61    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r2_hidden(X2,X1) & v3_pre_topc(X1,X0)) => m1_connsp_2(X1,X0,X2)))))),
% 1.74/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_connsp_2)).
% 1.74/0.61  fof(f153,plain,(
% 1.74/0.61    ~m1_connsp_2(sK1,sK0,sK2) | spl5_18),
% 1.74/0.61    inference(avatar_component_clause,[],[f151])).
% 1.74/0.61  fof(f151,plain,(
% 1.74/0.61    spl5_18 <=> m1_connsp_2(sK1,sK0,sK2)),
% 1.74/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 1.74/0.61  fof(f120,plain,(
% 1.74/0.61    m1_subset_1(sK2,u1_struct_0(sK0)) | ~spl5_12),
% 1.74/0.61    inference(avatar_component_clause,[],[f118])).
% 1.74/0.61  fof(f118,plain,(
% 1.74/0.61    spl5_12 <=> m1_subset_1(sK2,u1_struct_0(sK0))),
% 1.74/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 1.74/0.61  fof(f79,plain,(
% 1.74/0.61    v3_pre_topc(sK1,sK0) | ~spl5_5),
% 1.74/0.61    inference(avatar_component_clause,[],[f78])).
% 1.74/0.61  fof(f84,plain,(
% 1.74/0.61    r2_hidden(sK2,sK1) | ~spl5_6),
% 1.74/0.61    inference(avatar_component_clause,[],[f82])).
% 1.74/0.61  fof(f82,plain,(
% 1.74/0.61    spl5_6 <=> r2_hidden(sK2,sK1)),
% 1.74/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 1.74/0.61  fof(f60,plain,(
% 1.74/0.61    ~v2_struct_0(sK0) | spl5_1),
% 1.74/0.61    inference(avatar_component_clause,[],[f58])).
% 1.74/0.61  fof(f70,plain,(
% 1.74/0.61    l1_pre_topc(sK0) | ~spl5_3),
% 1.74/0.61    inference(avatar_component_clause,[],[f68])).
% 1.74/0.61  fof(f65,plain,(
% 1.74/0.61    v2_pre_topc(sK0) | ~spl5_2),
% 1.74/0.61    inference(avatar_component_clause,[],[f63])).
% 1.74/0.61  fof(f158,plain,(
% 1.74/0.61    ~spl5_18 | ~spl5_19 | ~spl5_4 | ~spl5_16),
% 1.74/0.61    inference(avatar_split_clause,[],[f149,f140,f73,f155,f151])).
% 1.74/0.61  fof(f140,plain,(
% 1.74/0.61    spl5_16 <=> ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X3,sK1) | ~m1_connsp_2(X3,sK0,sK2))),
% 1.74/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 1.74/0.61  fof(f149,plain,(
% 1.74/0.61    ~r1_tarski(sK1,sK1) | ~m1_connsp_2(sK1,sK0,sK2) | (~spl5_4 | ~spl5_16)),
% 1.74/0.61    inference(resolution,[],[f141,f75])).
% 1.74/0.61  fof(f141,plain,(
% 1.74/0.61    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X3,sK1) | ~m1_connsp_2(X3,sK0,sK2)) ) | ~spl5_16),
% 1.74/0.61    inference(avatar_component_clause,[],[f140])).
% 1.74/0.61  fof(f146,plain,(
% 1.74/0.61    spl5_5 | spl5_17),
% 1.74/0.61    inference(avatar_split_clause,[],[f29,f144,f78])).
% 1.74/0.61  fof(f29,plain,(
% 1.74/0.61    ( ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_hidden(X2,sK1) | m1_subset_1(sK3(X2),k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(sK1,sK0)) )),
% 1.74/0.61    inference(cnf_transformation,[],[f14])).
% 1.74/0.61  fof(f14,plain,(
% 1.74/0.61    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> ! [X2] : (? [X3] : (r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.74/0.61    inference(flattening,[],[f13])).
% 1.74/0.61  fof(f13,plain,(
% 1.74/0.61    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> ! [X2] : ((? [X3] : ((r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.74/0.61    inference(ennf_transformation,[],[f12])).
% 1.74/0.61  fof(f12,negated_conjecture,(
% 1.74/0.61    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2))) & r2_hidden(X2,X1))))))),
% 1.74/0.61    inference(negated_conjecture,[],[f11])).
% 1.74/0.61  fof(f11,conjecture,(
% 1.74/0.61    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2))) & r2_hidden(X2,X1))))))),
% 1.74/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_connsp_2)).
% 1.74/0.61  fof(f142,plain,(
% 1.74/0.61    ~spl5_5 | spl5_16),
% 1.74/0.61    inference(avatar_split_clause,[],[f32,f140,f78])).
% 1.74/0.61  fof(f32,plain,(
% 1.74/0.61    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_connsp_2(X3,sK0,sK2) | ~r1_tarski(X3,sK1) | ~v3_pre_topc(sK1,sK0)) )),
% 1.74/0.61    inference(cnf_transformation,[],[f14])).
% 1.74/0.61  fof(f137,plain,(
% 1.74/0.61    spl5_5 | spl5_15),
% 1.74/0.61    inference(avatar_split_clause,[],[f30,f135,f78])).
% 1.74/0.61  fof(f30,plain,(
% 1.74/0.61    ( ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_hidden(X2,sK1) | m1_connsp_2(sK3(X2),sK0,X2) | v3_pre_topc(sK1,sK0)) )),
% 1.74/0.61    inference(cnf_transformation,[],[f14])).
% 1.74/0.61  fof(f130,plain,(
% 1.74/0.61    spl5_13 | ~spl5_14 | ~spl5_8),
% 1.74/0.61    inference(avatar_split_clause,[],[f103,f99,f127,f123])).
% 1.74/0.61  fof(f99,plain,(
% 1.74/0.61    spl5_8 <=> r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 1.74/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 1.74/0.61  fof(f103,plain,(
% 1.74/0.61    ~r1_tarski(sK1,k1_tops_1(sK0,sK1)) | sK1 = k1_tops_1(sK0,sK1) | ~spl5_8),
% 1.74/0.61    inference(resolution,[],[f101,f48])).
% 1.74/0.61  fof(f48,plain,(
% 1.74/0.61    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 1.74/0.61    inference(cnf_transformation,[],[f2])).
% 1.74/0.61  fof(f101,plain,(
% 1.74/0.61    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~spl5_8),
% 1.74/0.61    inference(avatar_component_clause,[],[f99])).
% 1.74/0.61  fof(f121,plain,(
% 1.74/0.61    ~spl5_5 | spl5_12),
% 1.74/0.61    inference(avatar_split_clause,[],[f33,f118,f78])).
% 1.74/0.61  fof(f33,plain,(
% 1.74/0.61    m1_subset_1(sK2,u1_struct_0(sK0)) | ~v3_pre_topc(sK1,sK0)),
% 1.74/0.61    inference(cnf_transformation,[],[f14])).
% 1.74/0.61  fof(f116,plain,(
% 1.74/0.61    spl5_5 | spl5_11),
% 1.74/0.61    inference(avatar_split_clause,[],[f31,f114,f78])).
% 1.74/0.61  fof(f31,plain,(
% 1.74/0.61    ( ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_hidden(X2,sK1) | r1_tarski(sK3(X2),sK1) | v3_pre_topc(sK1,sK0)) )),
% 1.74/0.61    inference(cnf_transformation,[],[f14])).
% 1.74/0.61  fof(f102,plain,(
% 1.74/0.61    spl5_8 | ~spl5_3 | ~spl5_4),
% 1.74/0.61    inference(avatar_split_clause,[],[f89,f73,f68,f99])).
% 1.74/0.61  fof(f89,plain,(
% 1.74/0.61    ~l1_pre_topc(sK0) | r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~spl5_4),
% 1.74/0.61    inference(resolution,[],[f75,f39])).
% 1.74/0.61  fof(f39,plain,(
% 1.74/0.61    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | r1_tarski(k1_tops_1(X0,X1),X1)) )),
% 1.74/0.61    inference(cnf_transformation,[],[f15])).
% 1.74/0.61  fof(f15,plain,(
% 1.74/0.61    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.74/0.61    inference(ennf_transformation,[],[f6])).
% 1.74/0.61  fof(f6,axiom,(
% 1.74/0.61    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 1.74/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).
% 1.74/0.61  fof(f85,plain,(
% 1.74/0.61    ~spl5_5 | spl5_6),
% 1.74/0.61    inference(avatar_split_clause,[],[f34,f82,f78])).
% 1.74/0.61  fof(f34,plain,(
% 1.74/0.61    r2_hidden(sK2,sK1) | ~v3_pre_topc(sK1,sK0)),
% 1.74/0.61    inference(cnf_transformation,[],[f14])).
% 1.74/0.61  fof(f76,plain,(
% 1.74/0.61    spl5_4),
% 1.74/0.61    inference(avatar_split_clause,[],[f35,f73])).
% 1.74/0.61  fof(f35,plain,(
% 1.74/0.61    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.74/0.61    inference(cnf_transformation,[],[f14])).
% 1.74/0.61  fof(f71,plain,(
% 1.74/0.61    spl5_3),
% 1.74/0.61    inference(avatar_split_clause,[],[f38,f68])).
% 1.74/0.61  fof(f38,plain,(
% 1.74/0.61    l1_pre_topc(sK0)),
% 1.74/0.61    inference(cnf_transformation,[],[f14])).
% 1.74/0.61  fof(f66,plain,(
% 1.74/0.61    spl5_2),
% 1.74/0.61    inference(avatar_split_clause,[],[f37,f63])).
% 1.74/0.61  fof(f37,plain,(
% 1.74/0.61    v2_pre_topc(sK0)),
% 1.74/0.61    inference(cnf_transformation,[],[f14])).
% 1.74/0.61  fof(f61,plain,(
% 1.74/0.61    ~spl5_1),
% 1.74/0.61    inference(avatar_split_clause,[],[f36,f58])).
% 1.74/0.61  fof(f36,plain,(
% 1.74/0.61    ~v2_struct_0(sK0)),
% 1.74/0.61    inference(cnf_transformation,[],[f14])).
% 1.74/0.61  % SZS output end Proof for theBenchmark
% 1.74/0.61  % (20848)------------------------------
% 1.74/0.61  % (20848)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.74/0.61  % (20848)Termination reason: Refutation
% 1.74/0.61  
% 1.74/0.61  % (20848)Memory used [KB]: 11001
% 1.74/0.61  % (20848)Time elapsed: 0.115 s
% 1.74/0.61  % (20848)------------------------------
% 1.74/0.61  % (20848)------------------------------
% 1.74/0.61  % (20819)Success in time 0.242 s
%------------------------------------------------------------------------------
