%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:12:31 EST 2020

% Result     : Theorem 1.63s
% Output     : Refutation 1.63s
% Verified   : 
% Statistics : Number of formulae       :  159 ( 445 expanded)
%              Number of leaves         :   39 ( 179 expanded)
%              Depth                    :   14
%              Number of atoms          :  485 (1192 expanded)
%              Number of equality atoms :   63 ( 283 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1074,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f101,f105,f110,f115,f120,f128,f133,f138,f143,f148,f156,f164,f190,f235,f250,f280,f290,f300,f326,f369,f383,f420,f501,f987,f1070])).

fof(f1070,plain,
    ( spl9_12
    | ~ spl9_68 ),
    inference(avatar_split_clause,[],[f1060,f985,f130])).

fof(f130,plain,
    ( spl9_12
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).

fof(f985,plain,
    ( spl9_68
  <=> ! [X11] : r2_hidden(sK4(X11,X11,sK2),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_68])])).

fof(f1060,plain,
    ( k1_xboole_0 = sK2
    | ~ spl9_68 ),
    inference(resolution,[],[f986,f883])).

fof(f883,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(sK4(X4,X4,X5),k1_xboole_0)
      | k1_xboole_0 = X5 ) ),
    inference(backward_demodulation,[],[f470,f870])).

fof(f870,plain,(
    ! [X7] : k1_xboole_0 = k5_xboole_0(X7,k1_setfam_1(k2_tarski(X7,X7))) ),
    inference(duplicate_literal_removal,[],[f861])).

fof(f861,plain,(
    ! [X7] :
      ( k1_xboole_0 = k5_xboole_0(X7,k1_setfam_1(k2_tarski(X7,X7)))
      | k1_xboole_0 = k5_xboole_0(X7,k1_setfam_1(k2_tarski(X7,X7))) ) ),
    inference(resolution,[],[f470,f411])).

fof(f411,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X0,X1),X1)
      | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X0))) = X1 ) ),
    inference(duplicate_literal_removal,[],[f397])).

fof(f397,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X0,X1),X1)
      | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X0))) = X1
      | r2_hidden(sK4(X0,X0,X1),X1)
      | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X0))) = X1 ) ),
    inference(resolution,[],[f69,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1,X2),X1)
      | r2_hidden(sK4(X0,X1,X2),X2)
      | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = X2 ) ),
    inference(definition_unfolding,[],[f58,f62])).

fof(f62,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f48,f47])).

fof(f47,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f48,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1,X2),X1)
      | r2_hidden(sK4(X0,X1,X2),X2)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X0)
      | r2_hidden(sK4(X0,X1,X2),X2)
      | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = X2 ) ),
    inference(definition_unfolding,[],[f57,f62])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X0)
      | r2_hidden(sK4(X0,X1,X2),X2)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f470,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(sK4(X4,X4,X5),k1_xboole_0)
      | k5_xboole_0(X4,k1_setfam_1(k2_tarski(X4,X4))) = X5 ) ),
    inference(resolution,[],[f411,f178])).

fof(f178,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X1,k1_xboole_0) ) ),
    inference(forward_demodulation,[],[f177,f167])).

fof(f167,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f64,f63])).

fof(f63,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f39,f47])).

fof(f39,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f64,plain,(
    ! [X0] : k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = X0 ),
    inference(definition_unfolding,[],[f40,f62])).

fof(f40,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f177,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k5_xboole_0(X0,k1_xboole_0))
      | ~ r2_hidden(X1,k1_xboole_0) ) ),
    inference(superposition,[],[f72,f63])).

fof(f72,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))))
      | ~ r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) != X2 ) ),
    inference(definition_unfolding,[],[f60,f62])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f986,plain,
    ( ! [X11] : r2_hidden(sK4(X11,X11,sK2),k1_xboole_0)
    | ~ spl9_68 ),
    inference(avatar_component_clause,[],[f985])).

fof(f987,plain,
    ( spl9_12
    | spl9_68
    | ~ spl9_52 ),
    inference(avatar_split_clause,[],[f964,f498,f985,f130])).

fof(f498,plain,
    ( spl9_52
  <=> r1_tarski(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_52])])).

fof(f964,plain,
    ( ! [X11] :
        ( r2_hidden(sK4(X11,X11,sK2),k1_xboole_0)
        | k1_xboole_0 = sK2 )
    | ~ spl9_52 ),
    inference(resolution,[],[f913,f500])).

fof(f500,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | ~ spl9_52 ),
    inference(avatar_component_clause,[],[f498])).

fof(f913,plain,(
    ! [X10,X11,X9] :
      ( ~ r1_tarski(X9,X11)
      | r2_hidden(sK4(X10,X10,X9),X11)
      | k1_xboole_0 = X9 ) ),
    inference(resolution,[],[f885,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
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

fof(f885,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X0,X1),X1)
      | k1_xboole_0 = X1 ) ),
    inference(backward_demodulation,[],[f411,f870])).

fof(f501,plain,
    ( ~ spl9_14
    | spl9_52
    | ~ spl9_9
    | ~ spl9_28
    | ~ spl9_45
    | ~ spl9_47 ),
    inference(avatar_split_clause,[],[f496,f418,f380,f247,f117,f498,f140])).

fof(f140,plain,
    ( spl9_14
  <=> r1_tarski(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).

% (15049)Termination reason: Refutation not found, incomplete strategy

% (15049)Memory used [KB]: 10874
% (15049)Time elapsed: 0.159 s
% (15049)------------------------------
% (15049)------------------------------
fof(f117,plain,
    ( spl9_9
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).

fof(f247,plain,
    ( spl9_28
  <=> k1_xboole_0 = k1_tops_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_28])])).

fof(f380,plain,
    ( spl9_45
  <=> sK2 = k1_tops_1(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_45])])).

fof(f418,plain,
    ( spl9_47
  <=> ! [X5] :
        ( ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,X5))
        | ~ r1_tarski(sK2,X5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_47])])).

fof(f496,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | ~ r1_tarski(sK2,sK1)
    | ~ spl9_9
    | ~ spl9_28
    | ~ spl9_45
    | ~ spl9_47 ),
    inference(forward_demodulation,[],[f488,f248])).

fof(f248,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ spl9_28 ),
    inference(avatar_component_clause,[],[f247])).

fof(f488,plain,
    ( r1_tarski(sK2,k1_tops_1(sK0,sK1))
    | ~ r1_tarski(sK2,sK1)
    | ~ spl9_9
    | ~ spl9_45
    | ~ spl9_47 ),
    inference(resolution,[],[f479,f119])).

fof(f119,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl9_9 ),
    inference(avatar_component_clause,[],[f117])).

fof(f479,plain,
    ( ! [X5] :
        ( ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(sK2,k1_tops_1(sK0,X5))
        | ~ r1_tarski(sK2,X5) )
    | ~ spl9_45
    | ~ spl9_47 ),
    inference(forward_demodulation,[],[f419,f382])).

fof(f382,plain,
    ( sK2 = k1_tops_1(sK0,sK2)
    | ~ spl9_45 ),
    inference(avatar_component_clause,[],[f380])).

fof(f419,plain,
    ( ! [X5] :
        ( ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,X5))
        | ~ r1_tarski(sK2,X5) )
    | ~ spl9_47 ),
    inference(avatar_component_clause,[],[f418])).

fof(f420,plain,
    ( spl9_47
    | ~ spl9_7
    | ~ spl9_15 ),
    inference(avatar_split_clause,[],[f415,f145,f107,f418])).

fof(f107,plain,
    ( spl9_7
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f145,plain,
    ( spl9_15
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).

fof(f415,plain,
    ( ! [X5] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(sK2,X5)
        | r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,X5)) )
    | ~ spl9_15 ),
    inference(resolution,[],[f44,f147])).

fof(f147,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl9_15 ),
    inference(avatar_component_clause,[],[f145])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X1,X2)
      | r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).

fof(f383,plain,
    ( ~ spl9_7
    | ~ spl9_13
    | spl9_45
    | ~ spl9_5
    | ~ spl9_15 ),
    inference(avatar_split_clause,[],[f377,f145,f99,f380,f135,f107])).

fof(f135,plain,
    ( spl9_13
  <=> v3_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).

fof(f99,plain,
    ( spl9_5
  <=> ! [X1,X3] :
        ( ~ l1_pre_topc(X1)
        | k1_tops_1(X1,X3) = X3
        | ~ v3_pre_topc(X3,X1)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f377,plain,
    ( sK2 = k1_tops_1(sK0,sK2)
    | ~ v3_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl9_5
    | ~ spl9_15 ),
    inference(resolution,[],[f100,f147])).

fof(f100,plain,
    ( ! [X3,X1] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
        | k1_tops_1(X1,X3) = X3
        | ~ v3_pre_topc(X3,X1)
        | ~ l1_pre_topc(X1) )
    | ~ spl9_5 ),
    inference(avatar_component_clause,[],[f99])).

fof(f369,plain,
    ( ~ spl9_7
    | ~ spl9_8
    | ~ spl9_6
    | ~ spl9_17 ),
    inference(avatar_split_clause,[],[f367,f161,f103,f112,f107])).

fof(f112,plain,
    ( spl9_8
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f103,plain,
    ( spl9_6
  <=> ! [X0] :
        ( ~ v2_pre_topc(X0)
        | ~ sP5(X0)
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f161,plain,
    ( spl9_17
  <=> sP5(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_17])])).

fof(f367,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl9_6
    | ~ spl9_17 ),
    inference(resolution,[],[f104,f163])).

fof(f163,plain,
    ( sP5(sK0)
    | ~ spl9_17 ),
    inference(avatar_component_clause,[],[f161])).

fof(f104,plain,
    ( ! [X0] :
        ( ~ sP5(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl9_6 ),
    inference(avatar_component_clause,[],[f103])).

fof(f326,plain,
    ( ~ spl9_10
    | spl9_28
    | ~ spl9_7
    | ~ spl9_9 ),
    inference(avatar_split_clause,[],[f260,f117,f107,f247,f122])).

fof(f122,plain,
    ( spl9_10
  <=> v2_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).

fof(f260,plain,
    ( ~ l1_pre_topc(sK0)
    | k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ v2_tops_1(sK1,sK0)
    | ~ spl9_9 ),
    inference(resolution,[],[f43,f119])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k1_xboole_0 = k1_tops_1(X0,X1)
      | ~ v2_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).

fof(f300,plain,
    ( ~ spl9_18
    | ~ spl9_26
    | spl9_28
    | ~ spl9_11
    | ~ spl9_33 ),
    inference(avatar_split_clause,[],[f291,f287,f126,f247,f232,f187])).

fof(f187,plain,
    ( spl9_18
  <=> r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).

fof(f232,plain,
    ( spl9_26
  <=> v3_pre_topc(k1_tops_1(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_26])])).

fof(f126,plain,
    ( spl9_11
  <=> ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X2
        | ~ v3_pre_topc(X2,sK0)
        | ~ r1_tarski(X2,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).

fof(f287,plain,
    ( spl9_33
  <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_33])])).

fof(f291,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl9_11
    | ~ spl9_33 ),
    inference(resolution,[],[f289,f127])).

fof(f127,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X2
        | ~ v3_pre_topc(X2,sK0)
        | ~ r1_tarski(X2,sK1) )
    | ~ spl9_11 ),
    inference(avatar_component_clause,[],[f126])).

fof(f289,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl9_33 ),
    inference(avatar_component_clause,[],[f287])).

fof(f290,plain,
    ( spl9_33
    | ~ spl9_32 ),
    inference(avatar_split_clause,[],[f285,f277,f287])).

fof(f277,plain,
    ( spl9_32
  <=> r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_32])])).

fof(f285,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl9_32 ),
    inference(resolution,[],[f279,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f279,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))
    | ~ spl9_32 ),
    inference(avatar_component_clause,[],[f277])).

fof(f280,plain,
    ( spl9_32
    | ~ spl9_16
    | ~ spl9_18 ),
    inference(avatar_split_clause,[],[f274,f187,f153,f277])).

fof(f153,plain,
    ( spl9_16
  <=> r1_tarski(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).

fof(f274,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))
    | ~ spl9_16
    | ~ spl9_18 ),
    inference(resolution,[],[f191,f155])).

fof(f155,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl9_16 ),
    inference(avatar_component_clause,[],[f153])).

fof(f191,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK1,X0)
        | r1_tarski(k1_tops_1(sK0,sK1),X0) )
    | ~ spl9_18 ),
    inference(resolution,[],[f189,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f189,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl9_18 ),
    inference(avatar_component_clause,[],[f187])).

fof(f250,plain,
    ( spl9_10
    | ~ spl9_28
    | ~ spl9_7
    | ~ spl9_9 ),
    inference(avatar_split_clause,[],[f245,f117,f107,f247,f122])).

fof(f245,plain,
    ( ~ l1_pre_topc(sK0)
    | k1_xboole_0 != k1_tops_1(sK0,sK1)
    | v2_tops_1(sK1,sK0)
    | ~ spl9_9 ),
    inference(resolution,[],[f42,f119])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k1_xboole_0 != k1_tops_1(X0,X1)
      | v2_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f235,plain,
    ( spl9_26
    | ~ spl9_8
    | ~ spl9_7
    | ~ spl9_9 ),
    inference(avatar_split_clause,[],[f230,f117,f107,f112,f232])).

fof(f230,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ spl9_9 ),
    inference(resolution,[],[f49,f119])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

fof(f190,plain,
    ( spl9_18
    | ~ spl9_7
    | ~ spl9_9 ),
    inference(avatar_split_clause,[],[f183,f117,f107,f187])).

fof(f183,plain,
    ( ~ l1_pre_topc(sK0)
    | r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl9_9 ),
    inference(resolution,[],[f41,f119])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | r1_tarski(k1_tops_1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

fof(f164,plain,
    ( spl9_17
    | ~ spl9_9 ),
    inference(avatar_split_clause,[],[f158,f117,f161])).

fof(f158,plain,
    ( sP5(sK0)
    | ~ spl9_9 ),
    inference(resolution,[],[f74,f119])).

fof(f74,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | sP5(X0) ) ),
    inference(cnf_transformation,[],[f74_D])).

fof(f74_D,plain,(
    ! [X0] :
      ( ! [X2] : ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    <=> ~ sP5(X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP5])])).

fof(f156,plain,
    ( spl9_16
    | ~ spl9_9 ),
    inference(avatar_split_clause,[],[f150,f117,f153])).

fof(f150,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl9_9 ),
    inference(resolution,[],[f54,f119])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f148,plain,
    ( ~ spl9_10
    | spl9_15 ),
    inference(avatar_split_clause,[],[f30,f145,f122])).

fof(f30,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tops_1(X1,X0)
          <~> ! [X2] :
                ( k1_xboole_0 = X2
                | ~ v3_pre_topc(X2,X0)
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tops_1(X1,X0)
          <~> ! [X2] :
                ( k1_xboole_0 = X2
                | ~ v3_pre_topc(X2,X0)
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v2_tops_1(X1,X0)
            <=> ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( v3_pre_topc(X2,X0)
                      & r1_tarski(X2,X1) )
                   => k1_xboole_0 = X2 ) ) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v3_pre_topc(X2,X0)
                    & r1_tarski(X2,X1) )
                 => k1_xboole_0 = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_tops_1)).

fof(f143,plain,
    ( ~ spl9_10
    | spl9_14 ),
    inference(avatar_split_clause,[],[f31,f140,f122])).

fof(f31,plain,
    ( r1_tarski(sK2,sK1)
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f138,plain,
    ( ~ spl9_10
    | spl9_13 ),
    inference(avatar_split_clause,[],[f32,f135,f122])).

fof(f32,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f133,plain,
    ( ~ spl9_10
    | ~ spl9_12 ),
    inference(avatar_split_clause,[],[f33,f130,f122])).

fof(f33,plain,
    ( k1_xboole_0 != sK2
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f128,plain,
    ( spl9_10
    | spl9_11 ),
    inference(avatar_split_clause,[],[f34,f126,f122])).

fof(f34,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(X2,sK1)
      | ~ v3_pre_topc(X2,sK0)
      | k1_xboole_0 = X2
      | v2_tops_1(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f120,plain,(
    spl9_9 ),
    inference(avatar_split_clause,[],[f35,f117])).

fof(f35,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f115,plain,(
    spl9_8 ),
    inference(avatar_split_clause,[],[f36,f112])).

fof(f36,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f110,plain,(
    spl9_7 ),
    inference(avatar_split_clause,[],[f37,f107])).

fof(f37,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f105,plain,
    ( spl9_4
    | spl9_6 ),
    inference(avatar_split_clause,[],[f76,f103,f95])).

fof(f95,plain,
    ( spl9_4
  <=> sP6 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f76,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ sP5(X0)
      | sP6 ) ),
    inference(cnf_transformation,[],[f76_D])).

fof(f76_D,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ sP5(X0) )
  <=> ~ sP6 ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP6])])).

fof(f101,plain,
    ( ~ spl9_4
    | spl9_5 ),
    inference(avatar_split_clause,[],[f77,f99,f95])).

fof(f77,plain,(
    ! [X3,X1] :
      ( ~ l1_pre_topc(X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v3_pre_topc(X3,X1)
      | k1_tops_1(X1,X3) = X3
      | ~ sP6 ) ),
    inference(general_splitting,[],[f75,f76_D])).

fof(f75,plain,(
    ! [X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v3_pre_topc(X3,X1)
      | k1_tops_1(X1,X3) = X3
      | ~ sP5(X0) ) ),
    inference(general_splitting,[],[f46,f74_D])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v3_pre_topc(X3,X1)
      | k1_tops_1(X1,X3) = X3 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v3_pre_topc(X2,X0)
                      | k1_tops_1(X0,X2) != X2 )
                    & ( k1_tops_1(X1,X3) = X3
                      | ~ v3_pre_topc(X3,X1) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v3_pre_topc(X2,X0)
                      | k1_tops_1(X0,X2) != X2 )
                    & ( k1_tops_1(X1,X3) = X3
                      | ~ v3_pre_topc(X3,X1) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tops_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:18:22 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.21/0.50  % (15029)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.50  % (15045)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.51  % (15031)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.51  % (15037)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.51  % (15026)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.51  % (15039)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.52  % (15031)Refutation not found, incomplete strategy% (15031)------------------------------
% 0.21/0.52  % (15031)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (15047)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.53  % (15049)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.53  % (15031)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (15031)Memory used [KB]: 10746
% 0.21/0.53  % (15031)Time elapsed: 0.110 s
% 0.21/0.53  % (15031)------------------------------
% 0.21/0.53  % (15031)------------------------------
% 0.21/0.54  % (15023)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.54  % (15050)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (15024)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (15030)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.54  % (15051)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.54  % (15025)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (15032)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.54  % (15028)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.54  % (15052)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.54  % (15043)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.55  % (15041)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.55  % (15046)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.55  % (15042)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.55  % (15040)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.55  % (15044)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.55  % (15035)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.55  % (15027)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.55  % (15033)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.55  % (15048)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.55  % (15034)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.56  % (15036)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.56  % (15049)Refutation not found, incomplete strategy% (15049)------------------------------
% 0.21/0.56  % (15049)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (15038)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.63/0.57  % (15039)Refutation found. Thanks to Tanya!
% 1.63/0.57  % SZS status Theorem for theBenchmark
% 1.63/0.57  % SZS output start Proof for theBenchmark
% 1.63/0.57  fof(f1074,plain,(
% 1.63/0.57    $false),
% 1.63/0.57    inference(avatar_sat_refutation,[],[f101,f105,f110,f115,f120,f128,f133,f138,f143,f148,f156,f164,f190,f235,f250,f280,f290,f300,f326,f369,f383,f420,f501,f987,f1070])).
% 1.63/0.57  fof(f1070,plain,(
% 1.63/0.57    spl9_12 | ~spl9_68),
% 1.63/0.57    inference(avatar_split_clause,[],[f1060,f985,f130])).
% 1.63/0.57  fof(f130,plain,(
% 1.63/0.57    spl9_12 <=> k1_xboole_0 = sK2),
% 1.63/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).
% 1.63/0.57  fof(f985,plain,(
% 1.63/0.57    spl9_68 <=> ! [X11] : r2_hidden(sK4(X11,X11,sK2),k1_xboole_0)),
% 1.63/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_68])])).
% 1.63/0.57  fof(f1060,plain,(
% 1.63/0.57    k1_xboole_0 = sK2 | ~spl9_68),
% 1.63/0.57    inference(resolution,[],[f986,f883])).
% 1.63/0.57  fof(f883,plain,(
% 1.63/0.57    ( ! [X4,X5] : (~r2_hidden(sK4(X4,X4,X5),k1_xboole_0) | k1_xboole_0 = X5) )),
% 1.63/0.57    inference(backward_demodulation,[],[f470,f870])).
% 1.63/0.57  fof(f870,plain,(
% 1.63/0.57    ( ! [X7] : (k1_xboole_0 = k5_xboole_0(X7,k1_setfam_1(k2_tarski(X7,X7)))) )),
% 1.63/0.57    inference(duplicate_literal_removal,[],[f861])).
% 1.63/0.57  fof(f861,plain,(
% 1.63/0.57    ( ! [X7] : (k1_xboole_0 = k5_xboole_0(X7,k1_setfam_1(k2_tarski(X7,X7))) | k1_xboole_0 = k5_xboole_0(X7,k1_setfam_1(k2_tarski(X7,X7)))) )),
% 1.63/0.57    inference(resolution,[],[f470,f411])).
% 1.63/0.57  fof(f411,plain,(
% 1.63/0.57    ( ! [X0,X1] : (r2_hidden(sK4(X0,X0,X1),X1) | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X0))) = X1) )),
% 1.63/0.57    inference(duplicate_literal_removal,[],[f397])).
% 1.63/0.57  fof(f397,plain,(
% 1.63/0.57    ( ! [X0,X1] : (r2_hidden(sK4(X0,X0,X1),X1) | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X0))) = X1 | r2_hidden(sK4(X0,X0,X1),X1) | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X0))) = X1) )),
% 1.63/0.57    inference(resolution,[],[f69,f68])).
% 1.63/0.57  fof(f68,plain,(
% 1.63/0.57    ( ! [X2,X0,X1] : (~r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X2) | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = X2) )),
% 1.63/0.57    inference(definition_unfolding,[],[f58,f62])).
% 1.63/0.57  fof(f62,plain,(
% 1.63/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 1.63/0.57    inference(definition_unfolding,[],[f48,f47])).
% 1.63/0.57  fof(f47,plain,(
% 1.63/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.63/0.57    inference(cnf_transformation,[],[f8])).
% 1.63/0.57  fof(f8,axiom,(
% 1.63/0.57    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.63/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.63/0.57  fof(f48,plain,(
% 1.63/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.63/0.57    inference(cnf_transformation,[],[f3])).
% 1.63/0.57  fof(f3,axiom,(
% 1.63/0.57    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.63/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.63/0.57  fof(f58,plain,(
% 1.63/0.57    ( ! [X2,X0,X1] : (~r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X2) | k4_xboole_0(X0,X1) = X2) )),
% 1.63/0.57    inference(cnf_transformation,[],[f2])).
% 1.63/0.57  fof(f2,axiom,(
% 1.63/0.57    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.63/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.63/0.57  fof(f69,plain,(
% 1.63/0.57    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2) | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = X2) )),
% 1.63/0.57    inference(definition_unfolding,[],[f57,f62])).
% 1.63/0.57  fof(f57,plain,(
% 1.63/0.57    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2) | k4_xboole_0(X0,X1) = X2) )),
% 1.63/0.57    inference(cnf_transformation,[],[f2])).
% 1.63/0.57  fof(f470,plain,(
% 1.63/0.57    ( ! [X4,X5] : (~r2_hidden(sK4(X4,X4,X5),k1_xboole_0) | k5_xboole_0(X4,k1_setfam_1(k2_tarski(X4,X4))) = X5) )),
% 1.63/0.57    inference(resolution,[],[f411,f178])).
% 1.63/0.57  fof(f178,plain,(
% 1.63/0.57    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X1,k1_xboole_0)) )),
% 1.63/0.57    inference(forward_demodulation,[],[f177,f167])).
% 1.63/0.57  fof(f167,plain,(
% 1.63/0.57    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.63/0.57    inference(forward_demodulation,[],[f64,f63])).
% 1.63/0.57  fof(f63,plain,(
% 1.63/0.57    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0))) )),
% 1.63/0.57    inference(definition_unfolding,[],[f39,f47])).
% 1.63/0.57  fof(f39,plain,(
% 1.63/0.57    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.63/0.57    inference(cnf_transformation,[],[f5])).
% 1.63/0.57  fof(f5,axiom,(
% 1.63/0.57    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.63/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 1.63/0.57  fof(f64,plain,(
% 1.63/0.57    ( ! [X0] : (k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = X0) )),
% 1.63/0.57    inference(definition_unfolding,[],[f40,f62])).
% 1.63/0.58  fof(f40,plain,(
% 1.63/0.58    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.63/0.58    inference(cnf_transformation,[],[f7])).
% 1.63/0.58  fof(f7,axiom,(
% 1.63/0.58    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.63/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 1.63/0.58  fof(f177,plain,(
% 1.63/0.58    ( ! [X0,X1] : (~r2_hidden(X1,k5_xboole_0(X0,k1_xboole_0)) | ~r2_hidden(X1,k1_xboole_0)) )),
% 1.63/0.58    inference(superposition,[],[f72,f63])).
% 1.63/0.58  fof(f72,plain,(
% 1.63/0.58    ( ! [X0,X3,X1] : (~r2_hidden(X3,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) | ~r2_hidden(X3,X1)) )),
% 1.63/0.58    inference(equality_resolution,[],[f66])).
% 1.63/0.58  fof(f66,plain,(
% 1.63/0.58    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) != X2) )),
% 1.63/0.58    inference(definition_unfolding,[],[f60,f62])).
% 1.63/0.58  fof(f60,plain,(
% 1.63/0.58    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.63/0.58    inference(cnf_transformation,[],[f2])).
% 1.63/0.58  fof(f986,plain,(
% 1.63/0.58    ( ! [X11] : (r2_hidden(sK4(X11,X11,sK2),k1_xboole_0)) ) | ~spl9_68),
% 1.63/0.58    inference(avatar_component_clause,[],[f985])).
% 1.63/0.58  fof(f987,plain,(
% 1.63/0.58    spl9_12 | spl9_68 | ~spl9_52),
% 1.63/0.58    inference(avatar_split_clause,[],[f964,f498,f985,f130])).
% 1.63/0.58  fof(f498,plain,(
% 1.63/0.58    spl9_52 <=> r1_tarski(sK2,k1_xboole_0)),
% 1.63/0.58    introduced(avatar_definition,[new_symbols(naming,[spl9_52])])).
% 1.63/0.58  fof(f964,plain,(
% 1.63/0.58    ( ! [X11] : (r2_hidden(sK4(X11,X11,sK2),k1_xboole_0) | k1_xboole_0 = sK2) ) | ~spl9_52),
% 1.63/0.58    inference(resolution,[],[f913,f500])).
% 1.63/0.58  fof(f500,plain,(
% 1.63/0.58    r1_tarski(sK2,k1_xboole_0) | ~spl9_52),
% 1.63/0.58    inference(avatar_component_clause,[],[f498])).
% 1.63/0.58  fof(f913,plain,(
% 1.63/0.58    ( ! [X10,X11,X9] : (~r1_tarski(X9,X11) | r2_hidden(sK4(X10,X10,X9),X11) | k1_xboole_0 = X9) )),
% 1.63/0.58    inference(resolution,[],[f885,f50])).
% 1.63/0.58  fof(f50,plain,(
% 1.63/0.58    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 1.63/0.58    inference(cnf_transformation,[],[f27])).
% 1.63/0.58  fof(f27,plain,(
% 1.63/0.58    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.63/0.58    inference(ennf_transformation,[],[f1])).
% 1.63/0.58  fof(f1,axiom,(
% 1.63/0.58    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.63/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.63/0.58  fof(f885,plain,(
% 1.63/0.58    ( ! [X0,X1] : (r2_hidden(sK4(X0,X0,X1),X1) | k1_xboole_0 = X1) )),
% 1.63/0.58    inference(backward_demodulation,[],[f411,f870])).
% 1.63/0.58  fof(f501,plain,(
% 1.63/0.58    ~spl9_14 | spl9_52 | ~spl9_9 | ~spl9_28 | ~spl9_45 | ~spl9_47),
% 1.63/0.58    inference(avatar_split_clause,[],[f496,f418,f380,f247,f117,f498,f140])).
% 1.63/0.58  fof(f140,plain,(
% 1.63/0.58    spl9_14 <=> r1_tarski(sK2,sK1)),
% 1.63/0.58    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).
% 1.63/0.58  % (15049)Termination reason: Refutation not found, incomplete strategy
% 1.63/0.58  
% 1.63/0.58  % (15049)Memory used [KB]: 10874
% 1.63/0.58  % (15049)Time elapsed: 0.159 s
% 1.63/0.58  % (15049)------------------------------
% 1.63/0.58  % (15049)------------------------------
% 1.63/0.58  fof(f117,plain,(
% 1.63/0.58    spl9_9 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.63/0.58    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).
% 1.63/0.58  fof(f247,plain,(
% 1.63/0.58    spl9_28 <=> k1_xboole_0 = k1_tops_1(sK0,sK1)),
% 1.63/0.58    introduced(avatar_definition,[new_symbols(naming,[spl9_28])])).
% 1.63/0.58  fof(f380,plain,(
% 1.63/0.58    spl9_45 <=> sK2 = k1_tops_1(sK0,sK2)),
% 1.63/0.58    introduced(avatar_definition,[new_symbols(naming,[spl9_45])])).
% 1.63/0.58  fof(f418,plain,(
% 1.63/0.58    spl9_47 <=> ! [X5] : (~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,X5)) | ~r1_tarski(sK2,X5))),
% 1.63/0.58    introduced(avatar_definition,[new_symbols(naming,[spl9_47])])).
% 1.63/0.58  fof(f496,plain,(
% 1.63/0.58    r1_tarski(sK2,k1_xboole_0) | ~r1_tarski(sK2,sK1) | (~spl9_9 | ~spl9_28 | ~spl9_45 | ~spl9_47)),
% 1.63/0.58    inference(forward_demodulation,[],[f488,f248])).
% 1.63/0.58  fof(f248,plain,(
% 1.63/0.58    k1_xboole_0 = k1_tops_1(sK0,sK1) | ~spl9_28),
% 1.63/0.58    inference(avatar_component_clause,[],[f247])).
% 1.63/0.58  fof(f488,plain,(
% 1.63/0.58    r1_tarski(sK2,k1_tops_1(sK0,sK1)) | ~r1_tarski(sK2,sK1) | (~spl9_9 | ~spl9_45 | ~spl9_47)),
% 1.63/0.58    inference(resolution,[],[f479,f119])).
% 1.63/0.58  fof(f119,plain,(
% 1.63/0.58    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl9_9),
% 1.63/0.58    inference(avatar_component_clause,[],[f117])).
% 1.63/0.58  fof(f479,plain,(
% 1.63/0.58    ( ! [X5] : (~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(sK2,k1_tops_1(sK0,X5)) | ~r1_tarski(sK2,X5)) ) | (~spl9_45 | ~spl9_47)),
% 1.63/0.58    inference(forward_demodulation,[],[f419,f382])).
% 1.63/0.58  fof(f382,plain,(
% 1.63/0.58    sK2 = k1_tops_1(sK0,sK2) | ~spl9_45),
% 1.63/0.58    inference(avatar_component_clause,[],[f380])).
% 1.63/0.58  fof(f419,plain,(
% 1.63/0.58    ( ! [X5] : (~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,X5)) | ~r1_tarski(sK2,X5)) ) | ~spl9_47),
% 1.63/0.58    inference(avatar_component_clause,[],[f418])).
% 1.63/0.58  fof(f420,plain,(
% 1.63/0.58    spl9_47 | ~spl9_7 | ~spl9_15),
% 1.63/0.58    inference(avatar_split_clause,[],[f415,f145,f107,f418])).
% 1.63/0.58  fof(f107,plain,(
% 1.63/0.58    spl9_7 <=> l1_pre_topc(sK0)),
% 1.63/0.58    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).
% 1.63/0.58  fof(f145,plain,(
% 1.63/0.58    spl9_15 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.63/0.58    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).
% 1.63/0.58  fof(f415,plain,(
% 1.63/0.58    ( ! [X5] : (~l1_pre_topc(sK0) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(sK2,X5) | r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,X5))) ) | ~spl9_15),
% 1.63/0.58    inference(resolution,[],[f44,f147])).
% 1.63/0.58  fof(f147,plain,(
% 1.63/0.58    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl9_15),
% 1.63/0.58    inference(avatar_component_clause,[],[f145])).
% 1.63/0.58  fof(f44,plain,(
% 1.63/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X1,X2) | r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))) )),
% 1.63/0.58    inference(cnf_transformation,[],[f22])).
% 1.63/0.58  fof(f22,plain,(
% 1.63/0.58    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.63/0.58    inference(flattening,[],[f21])).
% 1.63/0.58  fof(f21,plain,(
% 1.63/0.58    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.63/0.58    inference(ennf_transformation,[],[f12])).
% 1.63/0.58  fof(f12,axiom,(
% 1.63/0.58    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 1.63/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).
% 1.63/0.58  fof(f383,plain,(
% 1.63/0.58    ~spl9_7 | ~spl9_13 | spl9_45 | ~spl9_5 | ~spl9_15),
% 1.63/0.58    inference(avatar_split_clause,[],[f377,f145,f99,f380,f135,f107])).
% 1.63/0.58  fof(f135,plain,(
% 1.63/0.58    spl9_13 <=> v3_pre_topc(sK2,sK0)),
% 1.63/0.58    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).
% 1.63/0.58  fof(f99,plain,(
% 1.63/0.58    spl9_5 <=> ! [X1,X3] : (~l1_pre_topc(X1) | k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))),
% 1.63/0.58    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).
% 1.63/0.58  fof(f377,plain,(
% 1.63/0.58    sK2 = k1_tops_1(sK0,sK2) | ~v3_pre_topc(sK2,sK0) | ~l1_pre_topc(sK0) | (~spl9_5 | ~spl9_15)),
% 1.63/0.58    inference(resolution,[],[f100,f147])).
% 1.63/0.58  fof(f100,plain,(
% 1.63/0.58    ( ! [X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1) | ~l1_pre_topc(X1)) ) | ~spl9_5),
% 1.63/0.58    inference(avatar_component_clause,[],[f99])).
% 1.63/0.58  fof(f369,plain,(
% 1.63/0.58    ~spl9_7 | ~spl9_8 | ~spl9_6 | ~spl9_17),
% 1.63/0.58    inference(avatar_split_clause,[],[f367,f161,f103,f112,f107])).
% 1.63/0.58  fof(f112,plain,(
% 1.63/0.58    spl9_8 <=> v2_pre_topc(sK0)),
% 1.63/0.58    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).
% 1.63/0.58  fof(f103,plain,(
% 1.63/0.58    spl9_6 <=> ! [X0] : (~v2_pre_topc(X0) | ~sP5(X0) | ~l1_pre_topc(X0))),
% 1.63/0.58    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).
% 1.63/0.58  fof(f161,plain,(
% 1.63/0.58    spl9_17 <=> sP5(sK0)),
% 1.63/0.58    introduced(avatar_definition,[new_symbols(naming,[spl9_17])])).
% 1.63/0.58  fof(f367,plain,(
% 1.63/0.58    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | (~spl9_6 | ~spl9_17)),
% 1.63/0.58    inference(resolution,[],[f104,f163])).
% 1.63/0.58  fof(f163,plain,(
% 1.63/0.58    sP5(sK0) | ~spl9_17),
% 1.63/0.58    inference(avatar_component_clause,[],[f161])).
% 1.63/0.58  fof(f104,plain,(
% 1.63/0.58    ( ! [X0] : (~sP5(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0)) ) | ~spl9_6),
% 1.63/0.58    inference(avatar_component_clause,[],[f103])).
% 1.63/0.58  fof(f326,plain,(
% 1.63/0.58    ~spl9_10 | spl9_28 | ~spl9_7 | ~spl9_9),
% 1.63/0.58    inference(avatar_split_clause,[],[f260,f117,f107,f247,f122])).
% 1.63/0.58  fof(f122,plain,(
% 1.63/0.58    spl9_10 <=> v2_tops_1(sK1,sK0)),
% 1.63/0.58    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).
% 1.63/0.58  fof(f260,plain,(
% 1.63/0.58    ~l1_pre_topc(sK0) | k1_xboole_0 = k1_tops_1(sK0,sK1) | ~v2_tops_1(sK1,sK0) | ~spl9_9),
% 1.63/0.58    inference(resolution,[],[f43,f119])).
% 1.63/0.58  fof(f43,plain,(
% 1.63/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0)) )),
% 1.63/0.58    inference(cnf_transformation,[],[f20])).
% 1.63/0.58  fof(f20,plain,(
% 1.63/0.58    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.63/0.58    inference(ennf_transformation,[],[f14])).
% 1.63/0.58  fof(f14,axiom,(
% 1.63/0.58    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 1.63/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).
% 1.63/0.58  fof(f300,plain,(
% 1.63/0.58    ~spl9_18 | ~spl9_26 | spl9_28 | ~spl9_11 | ~spl9_33),
% 1.63/0.58    inference(avatar_split_clause,[],[f291,f287,f126,f247,f232,f187])).
% 1.63/0.58  fof(f187,plain,(
% 1.63/0.58    spl9_18 <=> r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 1.63/0.58    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).
% 1.63/0.58  fof(f232,plain,(
% 1.63/0.58    spl9_26 <=> v3_pre_topc(k1_tops_1(sK0,sK1),sK0)),
% 1.63/0.58    introduced(avatar_definition,[new_symbols(naming,[spl9_26])])).
% 1.63/0.58  fof(f126,plain,(
% 1.63/0.58    spl9_11 <=> ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = X2 | ~v3_pre_topc(X2,sK0) | ~r1_tarski(X2,sK1))),
% 1.63/0.58    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).
% 1.63/0.58  fof(f287,plain,(
% 1.63/0.58    spl9_33 <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.63/0.58    introduced(avatar_definition,[new_symbols(naming,[spl9_33])])).
% 1.63/0.58  fof(f291,plain,(
% 1.63/0.58    k1_xboole_0 = k1_tops_1(sK0,sK1) | ~v3_pre_topc(k1_tops_1(sK0,sK1),sK0) | ~r1_tarski(k1_tops_1(sK0,sK1),sK1) | (~spl9_11 | ~spl9_33)),
% 1.63/0.58    inference(resolution,[],[f289,f127])).
% 1.63/0.58  fof(f127,plain,(
% 1.63/0.58    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = X2 | ~v3_pre_topc(X2,sK0) | ~r1_tarski(X2,sK1)) ) | ~spl9_11),
% 1.63/0.58    inference(avatar_component_clause,[],[f126])).
% 1.63/0.58  fof(f289,plain,(
% 1.63/0.58    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl9_33),
% 1.63/0.58    inference(avatar_component_clause,[],[f287])).
% 1.63/0.58  fof(f290,plain,(
% 1.63/0.58    spl9_33 | ~spl9_32),
% 1.63/0.58    inference(avatar_split_clause,[],[f285,f277,f287])).
% 1.63/0.58  fof(f277,plain,(
% 1.63/0.58    spl9_32 <=> r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))),
% 1.63/0.58    introduced(avatar_definition,[new_symbols(naming,[spl9_32])])).
% 1.63/0.58  fof(f285,plain,(
% 1.63/0.58    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl9_32),
% 1.63/0.58    inference(resolution,[],[f279,f53])).
% 1.63/0.58  fof(f53,plain,(
% 1.63/0.58    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.63/0.58    inference(cnf_transformation,[],[f9])).
% 1.63/0.58  fof(f9,axiom,(
% 1.63/0.58    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.63/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.63/0.58  fof(f279,plain,(
% 1.63/0.58    r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) | ~spl9_32),
% 1.63/0.58    inference(avatar_component_clause,[],[f277])).
% 1.63/0.58  fof(f280,plain,(
% 1.63/0.58    spl9_32 | ~spl9_16 | ~spl9_18),
% 1.63/0.58    inference(avatar_split_clause,[],[f274,f187,f153,f277])).
% 1.63/0.58  fof(f153,plain,(
% 1.63/0.58    spl9_16 <=> r1_tarski(sK1,u1_struct_0(sK0))),
% 1.63/0.58    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).
% 1.63/0.58  fof(f274,plain,(
% 1.63/0.58    r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) | (~spl9_16 | ~spl9_18)),
% 1.63/0.58    inference(resolution,[],[f191,f155])).
% 1.63/0.58  fof(f155,plain,(
% 1.63/0.58    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl9_16),
% 1.63/0.58    inference(avatar_component_clause,[],[f153])).
% 1.63/0.58  fof(f191,plain,(
% 1.63/0.58    ( ! [X0] : (~r1_tarski(sK1,X0) | r1_tarski(k1_tops_1(sK0,sK1),X0)) ) | ~spl9_18),
% 1.63/0.58    inference(resolution,[],[f189,f55])).
% 1.63/0.58  fof(f55,plain,(
% 1.63/0.58    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X2) | r1_tarski(X0,X2)) )),
% 1.63/0.58    inference(cnf_transformation,[],[f29])).
% 1.63/0.58  fof(f29,plain,(
% 1.63/0.58    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 1.63/0.58    inference(flattening,[],[f28])).
% 1.63/0.58  fof(f28,plain,(
% 1.63/0.58    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.63/0.58    inference(ennf_transformation,[],[f4])).
% 1.63/0.58  fof(f4,axiom,(
% 1.63/0.58    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 1.63/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 1.63/0.58  fof(f189,plain,(
% 1.63/0.58    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~spl9_18),
% 1.63/0.58    inference(avatar_component_clause,[],[f187])).
% 1.63/0.58  fof(f250,plain,(
% 1.63/0.58    spl9_10 | ~spl9_28 | ~spl9_7 | ~spl9_9),
% 1.63/0.58    inference(avatar_split_clause,[],[f245,f117,f107,f247,f122])).
% 1.63/0.58  fof(f245,plain,(
% 1.63/0.58    ~l1_pre_topc(sK0) | k1_xboole_0 != k1_tops_1(sK0,sK1) | v2_tops_1(sK1,sK0) | ~spl9_9),
% 1.63/0.58    inference(resolution,[],[f42,f119])).
% 1.63/0.58  fof(f42,plain,(
% 1.63/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | k1_xboole_0 != k1_tops_1(X0,X1) | v2_tops_1(X1,X0)) )),
% 1.63/0.58    inference(cnf_transformation,[],[f20])).
% 1.63/0.58  fof(f235,plain,(
% 1.63/0.58    spl9_26 | ~spl9_8 | ~spl9_7 | ~spl9_9),
% 1.63/0.58    inference(avatar_split_clause,[],[f230,f117,f107,f112,f232])).
% 1.63/0.58  fof(f230,plain,(
% 1.63/0.58    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v3_pre_topc(k1_tops_1(sK0,sK1),sK0) | ~spl9_9),
% 1.63/0.58    inference(resolution,[],[f49,f119])).
% 1.63/0.58  fof(f49,plain,(
% 1.63/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v3_pre_topc(k1_tops_1(X0,X1),X0)) )),
% 1.63/0.58    inference(cnf_transformation,[],[f26])).
% 1.63/0.58  fof(f26,plain,(
% 1.63/0.58    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.63/0.58    inference(flattening,[],[f25])).
% 1.63/0.58  fof(f25,plain,(
% 1.63/0.58    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.63/0.58    inference(ennf_transformation,[],[f10])).
% 1.63/0.58  fof(f10,axiom,(
% 1.63/0.58    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 1.63/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).
% 1.63/0.58  fof(f190,plain,(
% 1.63/0.58    spl9_18 | ~spl9_7 | ~spl9_9),
% 1.63/0.58    inference(avatar_split_clause,[],[f183,f117,f107,f187])).
% 1.63/0.58  fof(f183,plain,(
% 1.63/0.58    ~l1_pre_topc(sK0) | r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~spl9_9),
% 1.63/0.58    inference(resolution,[],[f41,f119])).
% 1.63/0.58  fof(f41,plain,(
% 1.63/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | r1_tarski(k1_tops_1(X0,X1),X1)) )),
% 1.63/0.58    inference(cnf_transformation,[],[f19])).
% 1.63/0.58  fof(f19,plain,(
% 1.63/0.58    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.63/0.58    inference(ennf_transformation,[],[f11])).
% 1.63/0.58  fof(f11,axiom,(
% 1.63/0.58    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 1.63/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).
% 1.63/0.58  fof(f164,plain,(
% 1.63/0.58    spl9_17 | ~spl9_9),
% 1.63/0.58    inference(avatar_split_clause,[],[f158,f117,f161])).
% 1.63/0.58  fof(f158,plain,(
% 1.63/0.58    sP5(sK0) | ~spl9_9),
% 1.63/0.58    inference(resolution,[],[f74,f119])).
% 1.63/0.58  fof(f74,plain,(
% 1.63/0.58    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | sP5(X0)) )),
% 1.63/0.58    inference(cnf_transformation,[],[f74_D])).
% 1.63/0.58  fof(f74_D,plain,(
% 1.63/0.58    ( ! [X0] : (( ! [X2] : ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) <=> ~sP5(X0)) )),
% 1.63/0.58    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP5])])).
% 1.63/0.58  fof(f156,plain,(
% 1.63/0.58    spl9_16 | ~spl9_9),
% 1.63/0.58    inference(avatar_split_clause,[],[f150,f117,f153])).
% 1.63/0.58  fof(f150,plain,(
% 1.63/0.58    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl9_9),
% 1.63/0.58    inference(resolution,[],[f54,f119])).
% 1.63/0.58  fof(f54,plain,(
% 1.63/0.58    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.63/0.58    inference(cnf_transformation,[],[f9])).
% 1.63/0.58  fof(f148,plain,(
% 1.63/0.58    ~spl9_10 | spl9_15),
% 1.63/0.58    inference(avatar_split_clause,[],[f30,f145,f122])).
% 1.63/0.58  fof(f30,plain,(
% 1.63/0.58    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tops_1(sK1,sK0)),
% 1.63/0.58    inference(cnf_transformation,[],[f18])).
% 1.63/0.58  fof(f18,plain,(
% 1.63/0.58    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> ! [X2] : (k1_xboole_0 = X2 | ~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.63/0.58    inference(flattening,[],[f17])).
% 1.63/0.58  fof(f17,plain,(
% 1.63/0.58    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> ! [X2] : ((k1_xboole_0 = X2 | (~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 1.63/0.58    inference(ennf_transformation,[],[f16])).
% 1.63/0.58  fof(f16,negated_conjecture,(
% 1.63/0.58    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X2,X0) & r1_tarski(X2,X1)) => k1_xboole_0 = X2)))))),
% 1.63/0.58    inference(negated_conjecture,[],[f15])).
% 1.63/0.58  fof(f15,conjecture,(
% 1.63/0.58    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X2,X0) & r1_tarski(X2,X1)) => k1_xboole_0 = X2)))))),
% 1.63/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_tops_1)).
% 1.63/0.58  fof(f143,plain,(
% 1.63/0.58    ~spl9_10 | spl9_14),
% 1.63/0.58    inference(avatar_split_clause,[],[f31,f140,f122])).
% 1.63/0.58  fof(f31,plain,(
% 1.63/0.58    r1_tarski(sK2,sK1) | ~v2_tops_1(sK1,sK0)),
% 1.63/0.58    inference(cnf_transformation,[],[f18])).
% 1.63/0.58  fof(f138,plain,(
% 1.63/0.58    ~spl9_10 | spl9_13),
% 1.63/0.58    inference(avatar_split_clause,[],[f32,f135,f122])).
% 1.63/0.58  fof(f32,plain,(
% 1.63/0.58    v3_pre_topc(sK2,sK0) | ~v2_tops_1(sK1,sK0)),
% 1.63/0.58    inference(cnf_transformation,[],[f18])).
% 1.63/0.58  fof(f133,plain,(
% 1.63/0.58    ~spl9_10 | ~spl9_12),
% 1.63/0.58    inference(avatar_split_clause,[],[f33,f130,f122])).
% 1.63/0.58  fof(f33,plain,(
% 1.63/0.58    k1_xboole_0 != sK2 | ~v2_tops_1(sK1,sK0)),
% 1.63/0.58    inference(cnf_transformation,[],[f18])).
% 1.63/0.58  fof(f128,plain,(
% 1.63/0.58    spl9_10 | spl9_11),
% 1.63/0.58    inference(avatar_split_clause,[],[f34,f126,f122])).
% 1.63/0.58  fof(f34,plain,(
% 1.63/0.58    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X2,sK1) | ~v3_pre_topc(X2,sK0) | k1_xboole_0 = X2 | v2_tops_1(sK1,sK0)) )),
% 1.63/0.58    inference(cnf_transformation,[],[f18])).
% 1.63/0.58  fof(f120,plain,(
% 1.63/0.58    spl9_9),
% 1.63/0.58    inference(avatar_split_clause,[],[f35,f117])).
% 1.63/0.58  fof(f35,plain,(
% 1.63/0.58    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.63/0.58    inference(cnf_transformation,[],[f18])).
% 1.63/0.58  fof(f115,plain,(
% 1.63/0.58    spl9_8),
% 1.63/0.58    inference(avatar_split_clause,[],[f36,f112])).
% 1.63/0.58  fof(f36,plain,(
% 1.63/0.58    v2_pre_topc(sK0)),
% 1.63/0.58    inference(cnf_transformation,[],[f18])).
% 1.63/0.58  fof(f110,plain,(
% 1.63/0.58    spl9_7),
% 1.63/0.58    inference(avatar_split_clause,[],[f37,f107])).
% 1.63/0.58  fof(f37,plain,(
% 1.63/0.58    l1_pre_topc(sK0)),
% 1.63/0.58    inference(cnf_transformation,[],[f18])).
% 1.63/0.58  fof(f105,plain,(
% 1.63/0.58    spl9_4 | spl9_6),
% 1.63/0.58    inference(avatar_split_clause,[],[f76,f103,f95])).
% 1.63/0.58  fof(f95,plain,(
% 1.63/0.58    spl9_4 <=> sP6),
% 1.63/0.58    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).
% 1.63/0.58  fof(f76,plain,(
% 1.63/0.58    ( ! [X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~sP5(X0) | sP6) )),
% 1.63/0.58    inference(cnf_transformation,[],[f76_D])).
% 1.63/0.58  fof(f76_D,plain,(
% 1.63/0.58    ( ! [X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~sP5(X0)) ) <=> ~sP6),
% 1.63/0.58    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP6])])).
% 1.63/0.58  fof(f101,plain,(
% 1.63/0.58    ~spl9_4 | spl9_5),
% 1.63/0.58    inference(avatar_split_clause,[],[f77,f99,f95])).
% 1.63/0.58  fof(f77,plain,(
% 1.63/0.58    ( ! [X3,X1] : (~l1_pre_topc(X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~v3_pre_topc(X3,X1) | k1_tops_1(X1,X3) = X3 | ~sP6) )),
% 1.63/0.58    inference(general_splitting,[],[f75,f76_D])).
% 1.63/0.58  fof(f75,plain,(
% 1.63/0.58    ( ! [X0,X3,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~l1_pre_topc(X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~v3_pre_topc(X3,X1) | k1_tops_1(X1,X3) = X3 | ~sP5(X0)) )),
% 1.63/0.58    inference(general_splitting,[],[f46,f74_D])).
% 1.63/0.58  fof(f46,plain,(
% 1.63/0.58    ( ! [X2,X0,X3,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~l1_pre_topc(X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~v3_pre_topc(X3,X1) | k1_tops_1(X1,X3) = X3) )),
% 1.63/0.58    inference(cnf_transformation,[],[f24])).
% 1.63/0.58  fof(f24,plain,(
% 1.63/0.58    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.63/0.58    inference(flattening,[],[f23])).
% 1.63/0.58  fof(f23,plain,(
% 1.63/0.58    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.63/0.58    inference(ennf_transformation,[],[f13])).
% 1.63/0.58  fof(f13,axiom,(
% 1.63/0.58    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((k1_tops_1(X0,X2) = X2 => v3_pre_topc(X2,X0)) & (v3_pre_topc(X3,X1) => k1_tops_1(X1,X3) = X3))))))),
% 1.63/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tops_1)).
% 1.63/0.58  % SZS output end Proof for theBenchmark
% 1.63/0.58  % (15039)------------------------------
% 1.63/0.58  % (15039)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.63/0.58  % (15039)Termination reason: Refutation
% 1.63/0.58  
% 1.63/0.58  % (15039)Memory used [KB]: 11385
% 1.63/0.58  % (15039)Time elapsed: 0.172 s
% 1.63/0.58  % (15039)------------------------------
% 1.63/0.58  % (15039)------------------------------
% 1.63/0.58  % (15022)Success in time 0.221 s
%------------------------------------------------------------------------------
