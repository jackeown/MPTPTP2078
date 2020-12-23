%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:04 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 208 expanded)
%              Number of leaves         :   22 (  96 expanded)
%              Depth                    :   10
%              Number of atoms          :  409 ( 908 expanded)
%              Number of equality atoms :   19 (  35 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f289,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f48,f53,f58,f63,f68,f73,f82,f83,f102,f126,f183,f201,f234,f239,f250,f260,f278,f288])).

fof(f288,plain,
    ( ~ spl4_7
    | ~ spl4_1
    | ~ spl4_5
    | spl4_21 ),
    inference(avatar_split_clause,[],[f286,f180,f65,f45,f75])).

fof(f75,plain,
    ( spl4_7
  <=> v3_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f45,plain,
    ( spl4_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f65,plain,
    ( spl4_5
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f180,plain,
    ( spl4_21
  <=> v2_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f286,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v3_tex_2(sK1,sK0)
    | spl4_21 ),
    inference(resolution,[],[f182,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v3_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( X1 = X2
                  | ~ r1_tarski(X1,X2)
                  | ~ v2_tex_2(X2,X0)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( X1 = X2
                  | ~ r1_tarski(X1,X2)
                  | ~ v2_tex_2(X2,X0)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r1_tarski(X1,X2)
                      & v2_tex_2(X2,X0) )
                   => X1 = X2 ) )
              & v2_tex_2(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tex_2)).

fof(f182,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | spl4_21 ),
    inference(avatar_component_clause,[],[f180])).

fof(f278,plain,
    ( spl4_7
    | ~ spl4_1
    | ~ spl4_21
    | ~ spl4_5
    | ~ spl4_26 ),
    inference(avatar_split_clause,[],[f276,f224,f65,f180,f45,f75])).

fof(f224,plain,
    ( spl4_26
  <=> sK1 = sK2(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f276,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tex_2(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | v3_tex_2(sK1,sK0)
    | ~ spl4_26 ),
    inference(trivial_inequality_removal,[],[f273])).

fof(f273,plain,
    ( sK1 != sK1
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tex_2(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | v3_tex_2(sK1,sK0)
    | ~ spl4_26 ),
    inference(superposition,[],[f34,f226])).

fof(f226,plain,
    ( sK1 = sK2(sK0,sK1)
    | ~ spl4_26 ),
    inference(avatar_component_clause,[],[f224])).

fof(f34,plain,(
    ! [X0,X1] :
      ( sK2(X0,X1) != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ l1_pre_topc(X0)
      | v3_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f260,plain,
    ( spl4_6
    | ~ spl4_25
    | ~ spl4_27 ),
    inference(avatar_split_clause,[],[f258,f228,f220,f70])).

fof(f70,plain,
    ( spl4_6
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f220,plain,
    ( spl4_25
  <=> r1_tarski(sK1,sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f228,plain,
    ( spl4_27
  <=> ! [X6] : ~ r2_hidden(X6,sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f258,plain,
    ( v1_xboole_0(sK1)
    | ~ spl4_25
    | ~ spl4_27 ),
    inference(resolution,[],[f256,f39])).

fof(f39,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f256,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK1)
    | ~ spl4_25
    | ~ spl4_27 ),
    inference(subsumption_resolution,[],[f245,f229])).

fof(f229,plain,
    ( ! [X6] : ~ r2_hidden(X6,sK2(sK0,sK1))
    | ~ spl4_27 ),
    inference(avatar_component_clause,[],[f228])).

fof(f245,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK2(sK0,sK1))
        | ~ r2_hidden(X0,sK1) )
    | ~ spl4_25 ),
    inference(resolution,[],[f221,f85])).

fof(f85,plain,(
    ! [X2,X3,X1] :
      ( ~ r1_tarski(X2,X3)
      | r2_hidden(X1,X3)
      | ~ r2_hidden(X1,X2) ) ),
    inference(resolution,[],[f41,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(f221,plain,
    ( r1_tarski(sK1,sK2(sK0,sK1))
    | ~ spl4_25 ),
    inference(avatar_component_clause,[],[f220])).

fof(f250,plain,
    ( spl4_7
    | ~ spl4_1
    | ~ spl4_21
    | ~ spl4_5
    | spl4_28 ),
    inference(avatar_split_clause,[],[f247,f231,f65,f180,f45,f75])).

fof(f231,plain,
    ( spl4_28
  <=> m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f247,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tex_2(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | v3_tex_2(sK1,sK0)
    | spl4_28 ),
    inference(resolution,[],[f233,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ l1_pre_topc(X0)
      | v3_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f233,plain,
    ( ~ m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_28 ),
    inference(avatar_component_clause,[],[f231])).

fof(f239,plain,
    ( spl4_7
    | ~ spl4_1
    | ~ spl4_21
    | ~ spl4_5
    | spl4_25 ),
    inference(avatar_split_clause,[],[f236,f220,f65,f180,f45,f75])).

fof(f236,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tex_2(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | v3_tex_2(sK1,sK0)
    | spl4_25 ),
    inference(resolution,[],[f222,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,sK2(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ l1_pre_topc(X0)
      | v3_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f222,plain,
    ( ~ r1_tarski(sK1,sK2(sK0,sK1))
    | spl4_25 ),
    inference(avatar_component_clause,[],[f220])).

fof(f234,plain,
    ( ~ spl4_25
    | spl4_26
    | spl4_27
    | ~ spl4_5
    | ~ spl4_28
    | spl4_7
    | ~ spl4_13
    | ~ spl4_21 ),
    inference(avatar_split_clause,[],[f208,f180,f124,f75,f231,f65,f228,f224,f220])).

fof(f124,plain,
    ( spl4_13
  <=> ! [X5,X4] :
        ( ~ m1_subset_1(sK2(sK0,X4),k1_zfmisc_1(u1_struct_0(sK0)))
        | v3_tex_2(X4,sK0)
        | ~ v2_tex_2(X4,sK0)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X5,sK2(sK0,X4))
        | sK1 = sK2(sK0,X4)
        | ~ r1_tarski(sK1,sK2(sK0,X4)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f208,plain,
    ( ! [X6] :
        ( v3_tex_2(sK1,sK0)
        | ~ m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X6,sK2(sK0,sK1))
        | sK1 = sK2(sK0,sK1)
        | ~ r1_tarski(sK1,sK2(sK0,sK1)) )
    | ~ spl4_13
    | ~ spl4_21 ),
    inference(resolution,[],[f125,f181])).

fof(f181,plain,
    ( v2_tex_2(sK1,sK0)
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f180])).

fof(f125,plain,
    ( ! [X4,X5] :
        ( ~ v2_tex_2(X4,sK0)
        | v3_tex_2(X4,sK0)
        | ~ m1_subset_1(sK2(sK0,X4),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X5,sK2(sK0,X4))
        | sK1 = sK2(sK0,X4)
        | ~ r1_tarski(sK1,sK2(sK0,X4)) )
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f124])).

fof(f201,plain,
    ( spl4_4
    | ~ spl4_8
    | ~ spl4_5
    | spl4_6
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | spl4_21 ),
    inference(avatar_split_clause,[],[f198,f180,f55,f50,f45,f70,f65,f79,f60])).

fof(f60,plain,
    ( spl4_4
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f79,plain,
    ( spl4_8
  <=> v1_zfmisc_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f50,plain,
    ( spl4_2
  <=> v2_tdlat_3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f55,plain,
    ( spl4_3
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f198,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ v2_tdlat_3(sK0)
    | ~ l1_pre_topc(sK0)
    | v1_xboole_0(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_zfmisc_1(sK1)
    | v2_struct_0(sK0)
    | spl4_21 ),
    inference(resolution,[],[f182,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | ~ v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_zfmisc_1(X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> v1_zfmisc_1(X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> v1_zfmisc_1(X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ( v2_tex_2(X1,X0)
          <=> v1_zfmisc_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tex_2)).

fof(f183,plain,
    ( ~ spl4_5
    | spl4_6
    | ~ spl4_21
    | spl4_8
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f178,f100,f79,f180,f70,f65])).

fof(f100,plain,
    ( spl4_10
  <=> ! [X0] :
        ( v1_xboole_0(X0)
        | ~ v2_tex_2(X0,sK0)
        | v1_zfmisc_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f178,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | v1_xboole_0(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_8
    | ~ spl4_10 ),
    inference(resolution,[],[f81,f101])).

fof(f101,plain,
    ( ! [X0] :
        ( v1_zfmisc_1(X0)
        | ~ v2_tex_2(X0,sK0)
        | v1_xboole_0(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f100])).

fof(f81,plain,
    ( ~ v1_zfmisc_1(sK1)
    | spl4_8 ),
    inference(avatar_component_clause,[],[f79])).

fof(f126,plain,
    ( ~ spl4_1
    | spl4_13
    | spl4_6
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f112,f100,f70,f124,f45])).

fof(f112,plain,
    ( ! [X4,X5] :
        ( ~ m1_subset_1(sK2(sK0,X4),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(sK1,sK2(sK0,X4))
        | sK1 = sK2(sK0,X4)
        | ~ r2_hidden(X5,sK2(sK0,X4))
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(X4,sK0)
        | ~ l1_pre_topc(sK0)
        | v3_tex_2(X4,sK0) )
    | spl4_6
    | ~ spl4_10 ),
    inference(resolution,[],[f109,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( v2_tex_2(sK2(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ l1_pre_topc(X0)
      | v3_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f109,plain,
    ( ! [X0,X1] :
        ( ~ v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(sK1,X0)
        | sK1 = X0
        | ~ r2_hidden(X1,X0) )
    | spl4_6
    | ~ spl4_10 ),
    inference(resolution,[],[f105,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f105,plain,
    ( ! [X0] :
        ( v1_xboole_0(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(X0,sK0)
        | ~ r1_tarski(sK1,X0)
        | sK1 = X0 )
    | spl4_6
    | ~ spl4_10 ),
    inference(resolution,[],[f104,f72])).

fof(f72,plain,
    ( ~ v1_xboole_0(sK1)
    | spl4_6 ),
    inference(avatar_component_clause,[],[f70])).

fof(f104,plain,
    ( ! [X0,X1] :
        ( v1_xboole_0(X1)
        | v1_xboole_0(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(X0,sK0)
        | ~ r1_tarski(X1,X0)
        | X0 = X1 )
    | ~ spl4_10 ),
    inference(duplicate_literal_removal,[],[f103])).

fof(f103,plain,
    ( ! [X0,X1] :
        ( ~ v2_tex_2(X0,sK0)
        | v1_xboole_0(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X0)
        | v1_xboole_0(X1)
        | ~ r1_tarski(X1,X0)
        | X0 = X1 )
    | ~ spl4_10 ),
    inference(resolution,[],[f101,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ v1_zfmisc_1(X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

fof(f102,plain,
    ( spl4_10
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | spl4_4 ),
    inference(avatar_split_clause,[],[f98,f60,f55,f50,f45,f100])).

fof(f98,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(sK0)
        | ~ v2_tdlat_3(sK0)
        | ~ l1_pre_topc(sK0)
        | v1_xboole_0(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_zfmisc_1(X0)
        | ~ v2_tex_2(X0,sK0) )
    | spl4_4 ),
    inference(resolution,[],[f38,f62])).

fof(f62,plain,
    ( ~ v2_struct_0(sK0)
    | spl4_4 ),
    inference(avatar_component_clause,[],[f60])).

fof(f38,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_zfmisc_1(X1)
      | ~ v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f83,plain,
    ( spl4_7
    | spl4_8 ),
    inference(avatar_split_clause,[],[f21,f79,f75])).

fof(f21,plain,
    ( v1_zfmisc_1(sK1)
    | v3_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tex_2(X1,X0)
          <~> v1_zfmisc_1(X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tex_2(X1,X0)
          <~> v1_zfmisc_1(X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & ~ v1_xboole_0(X1) )
           => ( v3_tex_2(X1,X0)
            <=> v1_zfmisc_1(X1) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ( v3_tex_2(X1,X0)
          <=> v1_zfmisc_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_tex_2)).

fof(f82,plain,
    ( ~ spl4_7
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f22,f79,f75])).

fof(f22,plain,
    ( ~ v1_zfmisc_1(sK1)
    | ~ v3_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f73,plain,(
    ~ spl4_6 ),
    inference(avatar_split_clause,[],[f23,f70])).

fof(f23,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f68,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f24,f65])).

fof(f24,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f11])).

fof(f63,plain,(
    ~ spl4_4 ),
    inference(avatar_split_clause,[],[f25,f60])).

fof(f25,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f58,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f26,f55])).

fof(f26,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f53,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f27,f50])).

fof(f27,plain,(
    v2_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f48,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f28,f45])).

fof(f28,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:24:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.47  % (27249)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.47  % (27249)Refutation not found, incomplete strategy% (27249)------------------------------
% 0.21/0.47  % (27249)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (27249)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (27249)Memory used [KB]: 1663
% 0.21/0.47  % (27249)Time elapsed: 0.064 s
% 0.21/0.47  % (27249)------------------------------
% 0.21/0.47  % (27249)------------------------------
% 0.21/0.47  % (27257)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.48  % (27257)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f289,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f48,f53,f58,f63,f68,f73,f82,f83,f102,f126,f183,f201,f234,f239,f250,f260,f278,f288])).
% 0.21/0.48  fof(f288,plain,(
% 0.21/0.48    ~spl4_7 | ~spl4_1 | ~spl4_5 | spl4_21),
% 0.21/0.48    inference(avatar_split_clause,[],[f286,f180,f65,f45,f75])).
% 0.21/0.48  fof(f75,plain,(
% 0.21/0.48    spl4_7 <=> v3_tex_2(sK1,sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.48  fof(f45,plain,(
% 0.21/0.48    spl4_1 <=> l1_pre_topc(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.48  fof(f65,plain,(
% 0.21/0.48    spl4_5 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.48  fof(f180,plain,(
% 0.21/0.48    spl4_21 <=> v2_tex_2(sK1,sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 0.21/0.48  fof(f286,plain,(
% 0.21/0.48    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v3_tex_2(sK1,sK0) | spl4_21),
% 0.21/0.48    inference(resolution,[],[f182,f36])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v3_tex_2(X1,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(flattening,[],[f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : ((X1 = X2 | (~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v2_tex_2(X2,X0)) => X1 = X2)) & v2_tex_2(X1,X0)))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tex_2)).
% 0.21/0.48  fof(f182,plain,(
% 0.21/0.48    ~v2_tex_2(sK1,sK0) | spl4_21),
% 0.21/0.48    inference(avatar_component_clause,[],[f180])).
% 0.21/0.48  fof(f278,plain,(
% 0.21/0.48    spl4_7 | ~spl4_1 | ~spl4_21 | ~spl4_5 | ~spl4_26),
% 0.21/0.48    inference(avatar_split_clause,[],[f276,f224,f65,f180,f45,f75])).
% 0.21/0.48  fof(f224,plain,(
% 0.21/0.48    spl4_26 <=> sK1 = sK2(sK0,sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 0.21/0.48  fof(f276,plain,(
% 0.21/0.48    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(sK1,sK0) | ~l1_pre_topc(sK0) | v3_tex_2(sK1,sK0) | ~spl4_26),
% 0.21/0.48    inference(trivial_inequality_removal,[],[f273])).
% 0.21/0.48  fof(f273,plain,(
% 0.21/0.48    sK1 != sK1 | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(sK1,sK0) | ~l1_pre_topc(sK0) | v3_tex_2(sK1,sK0) | ~spl4_26),
% 0.21/0.48    inference(superposition,[],[f34,f226])).
% 0.21/0.48  fof(f226,plain,(
% 0.21/0.48    sK1 = sK2(sK0,sK1) | ~spl4_26),
% 0.21/0.48    inference(avatar_component_clause,[],[f224])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    ( ! [X0,X1] : (sK2(X0,X1) != X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~l1_pre_topc(X0) | v3_tex_2(X1,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f17])).
% 0.21/0.48  fof(f260,plain,(
% 0.21/0.48    spl4_6 | ~spl4_25 | ~spl4_27),
% 0.21/0.48    inference(avatar_split_clause,[],[f258,f228,f220,f70])).
% 0.21/0.48  fof(f70,plain,(
% 0.21/0.48    spl4_6 <=> v1_xboole_0(sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.48  fof(f220,plain,(
% 0.21/0.48    spl4_25 <=> r1_tarski(sK1,sK2(sK0,sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 0.21/0.48  fof(f228,plain,(
% 0.21/0.48    spl4_27 <=> ! [X6] : ~r2_hidden(X6,sK2(sK0,sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).
% 0.21/0.48  fof(f258,plain,(
% 0.21/0.48    v1_xboole_0(sK1) | (~spl4_25 | ~spl4_27)),
% 0.21/0.48    inference(resolution,[],[f256,f39])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    ( ! [X0] : (r2_hidden(sK3(X0),X0) | v1_xboole_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.48  fof(f256,plain,(
% 0.21/0.48    ( ! [X0] : (~r2_hidden(X0,sK1)) ) | (~spl4_25 | ~spl4_27)),
% 0.21/0.48    inference(subsumption_resolution,[],[f245,f229])).
% 0.21/0.48  fof(f229,plain,(
% 0.21/0.48    ( ! [X6] : (~r2_hidden(X6,sK2(sK0,sK1))) ) | ~spl4_27),
% 0.21/0.48    inference(avatar_component_clause,[],[f228])).
% 0.21/0.48  fof(f245,plain,(
% 0.21/0.48    ( ! [X0] : (r2_hidden(X0,sK2(sK0,sK1)) | ~r2_hidden(X0,sK1)) ) | ~spl4_25),
% 0.21/0.48    inference(resolution,[],[f221,f85])).
% 0.21/0.48  fof(f85,plain,(
% 0.21/0.48    ( ! [X2,X3,X1] : (~r1_tarski(X2,X3) | r2_hidden(X1,X3) | ~r2_hidden(X1,X2)) )),
% 0.21/0.48    inference(resolution,[],[f41,f42])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 0.21/0.48  fof(f221,plain,(
% 0.21/0.48    r1_tarski(sK1,sK2(sK0,sK1)) | ~spl4_25),
% 0.21/0.48    inference(avatar_component_clause,[],[f220])).
% 0.21/0.48  fof(f250,plain,(
% 0.21/0.48    spl4_7 | ~spl4_1 | ~spl4_21 | ~spl4_5 | spl4_28),
% 0.21/0.48    inference(avatar_split_clause,[],[f247,f231,f65,f180,f45,f75])).
% 0.21/0.48  fof(f231,plain,(
% 0.21/0.48    spl4_28 <=> m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).
% 0.21/0.48  fof(f247,plain,(
% 0.21/0.48    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(sK1,sK0) | ~l1_pre_topc(sK0) | v3_tex_2(sK1,sK0) | spl4_28),
% 0.21/0.48    inference(resolution,[],[f233,f31])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ( ! [X0,X1] : (m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~l1_pre_topc(X0) | v3_tex_2(X1,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f17])).
% 0.21/0.48  fof(f233,plain,(
% 0.21/0.48    ~m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl4_28),
% 0.21/0.48    inference(avatar_component_clause,[],[f231])).
% 0.21/0.48  fof(f239,plain,(
% 0.21/0.48    spl4_7 | ~spl4_1 | ~spl4_21 | ~spl4_5 | spl4_25),
% 0.21/0.48    inference(avatar_split_clause,[],[f236,f220,f65,f180,f45,f75])).
% 0.21/0.48  fof(f236,plain,(
% 0.21/0.48    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(sK1,sK0) | ~l1_pre_topc(sK0) | v3_tex_2(sK1,sK0) | spl4_25),
% 0.21/0.48    inference(resolution,[],[f222,f33])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tarski(X1,sK2(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~l1_pre_topc(X0) | v3_tex_2(X1,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f17])).
% 0.21/0.48  fof(f222,plain,(
% 0.21/0.48    ~r1_tarski(sK1,sK2(sK0,sK1)) | spl4_25),
% 0.21/0.48    inference(avatar_component_clause,[],[f220])).
% 0.21/0.48  fof(f234,plain,(
% 0.21/0.48    ~spl4_25 | spl4_26 | spl4_27 | ~spl4_5 | ~spl4_28 | spl4_7 | ~spl4_13 | ~spl4_21),
% 0.21/0.48    inference(avatar_split_clause,[],[f208,f180,f124,f75,f231,f65,f228,f224,f220])).
% 0.21/0.48  fof(f124,plain,(
% 0.21/0.48    spl4_13 <=> ! [X5,X4] : (~m1_subset_1(sK2(sK0,X4),k1_zfmisc_1(u1_struct_0(sK0))) | v3_tex_2(X4,sK0) | ~v2_tex_2(X4,sK0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X5,sK2(sK0,X4)) | sK1 = sK2(sK0,X4) | ~r1_tarski(sK1,sK2(sK0,X4)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.21/0.48  fof(f208,plain,(
% 0.21/0.48    ( ! [X6] : (v3_tex_2(sK1,sK0) | ~m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X6,sK2(sK0,sK1)) | sK1 = sK2(sK0,sK1) | ~r1_tarski(sK1,sK2(sK0,sK1))) ) | (~spl4_13 | ~spl4_21)),
% 0.21/0.48    inference(resolution,[],[f125,f181])).
% 0.21/0.48  fof(f181,plain,(
% 0.21/0.48    v2_tex_2(sK1,sK0) | ~spl4_21),
% 0.21/0.48    inference(avatar_component_clause,[],[f180])).
% 0.21/0.48  fof(f125,plain,(
% 0.21/0.48    ( ! [X4,X5] : (~v2_tex_2(X4,sK0) | v3_tex_2(X4,sK0) | ~m1_subset_1(sK2(sK0,X4),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X5,sK2(sK0,X4)) | sK1 = sK2(sK0,X4) | ~r1_tarski(sK1,sK2(sK0,X4))) ) | ~spl4_13),
% 0.21/0.48    inference(avatar_component_clause,[],[f124])).
% 0.21/0.48  fof(f201,plain,(
% 0.21/0.48    spl4_4 | ~spl4_8 | ~spl4_5 | spl4_6 | ~spl4_1 | ~spl4_2 | ~spl4_3 | spl4_21),
% 0.21/0.48    inference(avatar_split_clause,[],[f198,f180,f55,f50,f45,f70,f65,f79,f60])).
% 0.21/0.48  fof(f60,plain,(
% 0.21/0.48    spl4_4 <=> v2_struct_0(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.48  fof(f79,plain,(
% 0.21/0.48    spl4_8 <=> v1_zfmisc_1(sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.48  fof(f50,plain,(
% 0.21/0.48    spl4_2 <=> v2_tdlat_3(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.48  fof(f55,plain,(
% 0.21/0.48    spl4_3 <=> v2_pre_topc(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.48  fof(f198,plain,(
% 0.21/0.48    ~v2_pre_topc(sK0) | ~v2_tdlat_3(sK0) | ~l1_pre_topc(sK0) | v1_xboole_0(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_zfmisc_1(sK1) | v2_struct_0(sK0) | spl4_21),
% 0.21/0.48    inference(resolution,[],[f182,f37])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v2_tex_2(X1,X0) | ~v2_pre_topc(X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_zfmisc_1(X1) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,axiom,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tex_2)).
% 0.21/0.48  fof(f183,plain,(
% 0.21/0.48    ~spl4_5 | spl4_6 | ~spl4_21 | spl4_8 | ~spl4_10),
% 0.21/0.48    inference(avatar_split_clause,[],[f178,f100,f79,f180,f70,f65])).
% 0.21/0.48  fof(f100,plain,(
% 0.21/0.48    spl4_10 <=> ! [X0] : (v1_xboole_0(X0) | ~v2_tex_2(X0,sK0) | v1_zfmisc_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.21/0.48  fof(f178,plain,(
% 0.21/0.48    ~v2_tex_2(sK1,sK0) | v1_xboole_0(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (spl4_8 | ~spl4_10)),
% 0.21/0.48    inference(resolution,[],[f81,f101])).
% 0.21/0.48  fof(f101,plain,(
% 0.21/0.48    ( ! [X0] : (v1_zfmisc_1(X0) | ~v2_tex_2(X0,sK0) | v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl4_10),
% 0.21/0.48    inference(avatar_component_clause,[],[f100])).
% 0.21/0.48  fof(f81,plain,(
% 0.21/0.48    ~v1_zfmisc_1(sK1) | spl4_8),
% 0.21/0.48    inference(avatar_component_clause,[],[f79])).
% 0.21/0.48  fof(f126,plain,(
% 0.21/0.48    ~spl4_1 | spl4_13 | spl4_6 | ~spl4_10),
% 0.21/0.48    inference(avatar_split_clause,[],[f112,f100,f70,f124,f45])).
% 0.21/0.48  fof(f112,plain,(
% 0.21/0.48    ( ! [X4,X5] : (~m1_subset_1(sK2(sK0,X4),k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(sK1,sK2(sK0,X4)) | sK1 = sK2(sK0,X4) | ~r2_hidden(X5,sK2(sK0,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X4,sK0) | ~l1_pre_topc(sK0) | v3_tex_2(X4,sK0)) ) | (spl4_6 | ~spl4_10)),
% 0.21/0.48    inference(resolution,[],[f109,f32])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v2_tex_2(sK2(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~l1_pre_topc(X0) | v3_tex_2(X1,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f17])).
% 0.21/0.48  fof(f109,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(sK1,X0) | sK1 = X0 | ~r2_hidden(X1,X0)) ) | (spl4_6 | ~spl4_10)),
% 0.21/0.48    inference(resolution,[],[f105,f40])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~r2_hidden(X1,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f1])).
% 0.21/0.48  fof(f105,plain,(
% 0.21/0.48    ( ! [X0] : (v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X0,sK0) | ~r1_tarski(sK1,X0) | sK1 = X0) ) | (spl4_6 | ~spl4_10)),
% 0.21/0.48    inference(resolution,[],[f104,f72])).
% 0.21/0.48  fof(f72,plain,(
% 0.21/0.48    ~v1_xboole_0(sK1) | spl4_6),
% 0.21/0.48    inference(avatar_component_clause,[],[f70])).
% 0.21/0.48  fof(f104,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v1_xboole_0(X1) | v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X0,sK0) | ~r1_tarski(X1,X0) | X0 = X1) ) | ~spl4_10),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f103])).
% 0.21/0.48  fof(f103,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v2_tex_2(X0,sK0) | v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X0) | v1_xboole_0(X1) | ~r1_tarski(X1,X0) | X0 = X1) ) | ~spl4_10),
% 0.21/0.48    inference(resolution,[],[f101,f29])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v1_zfmisc_1(X1) | v1_xboole_0(X1) | v1_xboole_0(X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 0.21/0.48    inference(cnf_transformation,[],[f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.21/0.48    inference(flattening,[],[f12])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : ((X0 = X1 | ~r1_tarski(X0,X1)) | (~v1_zfmisc_1(X1) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).
% 0.21/0.48  fof(f102,plain,(
% 0.21/0.48    spl4_10 | ~spl4_1 | ~spl4_2 | ~spl4_3 | spl4_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f98,f60,f55,f50,f45,f100])).
% 0.21/0.48  fof(f98,plain,(
% 0.21/0.48    ( ! [X0] : (~v2_pre_topc(sK0) | ~v2_tdlat_3(sK0) | ~l1_pre_topc(sK0) | v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_zfmisc_1(X0) | ~v2_tex_2(X0,sK0)) ) | spl4_4),
% 0.21/0.48    inference(resolution,[],[f38,f62])).
% 0.21/0.48  fof(f62,plain,(
% 0.21/0.48    ~v2_struct_0(sK0) | spl4_4),
% 0.21/0.48    inference(avatar_component_clause,[],[f60])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f19])).
% 0.21/0.48  fof(f83,plain,(
% 0.21/0.48    spl4_7 | spl4_8),
% 0.21/0.48    inference(avatar_split_clause,[],[f21,f79,f75])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    v1_zfmisc_1(sK1) | v3_tex_2(sK1,sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f10])).
% 0.21/0.48  fof(f10,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,negated_conjecture,(
% 0.21/0.48    ~! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v3_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 0.21/0.48    inference(negated_conjecture,[],[f8])).
% 0.21/0.48  fof(f8,conjecture,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v3_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_tex_2)).
% 0.21/0.48  fof(f82,plain,(
% 0.21/0.48    ~spl4_7 | ~spl4_8),
% 0.21/0.48    inference(avatar_split_clause,[],[f22,f79,f75])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ~v1_zfmisc_1(sK1) | ~v3_tex_2(sK1,sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f11])).
% 0.21/0.48  fof(f73,plain,(
% 0.21/0.48    ~spl4_6),
% 0.21/0.48    inference(avatar_split_clause,[],[f23,f70])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ~v1_xboole_0(sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f11])).
% 0.21/0.48  fof(f68,plain,(
% 0.21/0.48    spl4_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f24,f65])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.48    inference(cnf_transformation,[],[f11])).
% 0.21/0.48  fof(f63,plain,(
% 0.21/0.48    ~spl4_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f25,f60])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ~v2_struct_0(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f11])).
% 0.21/0.48  fof(f58,plain,(
% 0.21/0.48    spl4_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f26,f55])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    v2_pre_topc(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f11])).
% 0.21/0.48  fof(f53,plain,(
% 0.21/0.48    spl4_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f27,f50])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    v2_tdlat_3(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f11])).
% 0.21/0.48  fof(f48,plain,(
% 0.21/0.48    spl4_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f28,f45])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    l1_pre_topc(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f11])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (27257)------------------------------
% 0.21/0.48  % (27257)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (27257)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (27257)Memory used [KB]: 6268
% 0.21/0.48  % (27257)Time elapsed: 0.075 s
% 0.21/0.48  % (27257)------------------------------
% 0.21/0.48  % (27257)------------------------------
% 0.21/0.48  % (27241)Success in time 0.127 s
%------------------------------------------------------------------------------
