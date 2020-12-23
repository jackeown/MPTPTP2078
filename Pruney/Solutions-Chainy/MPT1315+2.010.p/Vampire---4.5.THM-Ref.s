%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:13:47 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 247 expanded)
%              Number of leaves         :   30 ( 102 expanded)
%              Depth                    :   10
%              Number of atoms          :  362 ( 737 expanded)
%              Number of equality atoms :   46 ( 113 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f364,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f66,f71,f76,f81,f86,f91,f97,f103,f109,f115,f121,f127,f133,f145,f159,f167,f179,f286,f341,f363])).

fof(f363,plain,
    ( ~ spl8_9
    | ~ spl8_3
    | ~ spl8_13
    | spl8_5
    | ~ spl8_13
    | ~ spl8_30
    | ~ spl8_35 ),
    inference(avatar_split_clause,[],[f362,f336,f284,f130,f83,f130,f73,f106])).

fof(f106,plain,
    ( spl8_9
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f73,plain,
    ( spl8_3
  <=> v4_pre_topc(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f83,plain,
    ( spl8_5
  <=> v4_pre_topc(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f130,plain,
    ( spl8_13
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f284,plain,
    ( spl8_30
  <=> ! [X0] :
        ( v4_pre_topc(k9_subset_1(k2_struct_0(sK2),X0,k2_struct_0(sK2)),sK2)
        | ~ v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(k9_subset_1(k2_struct_0(sK2),X0,k2_struct_0(sK2)),k1_zfmisc_1(k2_struct_0(sK2)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_30])])).

fof(f336,plain,
    ( spl8_35
  <=> sK3 = k1_setfam_1(k2_tarski(k2_struct_0(sK2),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_35])])).

fof(f362,plain,
    ( v4_pre_topc(sK3,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK2)))
    | ~ v4_pre_topc(sK3,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl8_13
    | ~ spl8_30
    | ~ spl8_35 ),
    inference(forward_demodulation,[],[f361,f338])).

fof(f338,plain,
    ( sK3 = k1_setfam_1(k2_tarski(k2_struct_0(sK2),sK3))
    | ~ spl8_35 ),
    inference(avatar_component_clause,[],[f336])).

fof(f361,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK2)))
    | ~ v4_pre_topc(sK3,sK0)
    | v4_pre_topc(k1_setfam_1(k2_tarski(k2_struct_0(sK2),sK3)),sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl8_13
    | ~ spl8_30
    | ~ spl8_35 ),
    inference(forward_demodulation,[],[f360,f338])).

fof(f360,plain,
    ( ~ m1_subset_1(k1_setfam_1(k2_tarski(k2_struct_0(sK2),sK3)),k1_zfmisc_1(k2_struct_0(sK2)))
    | ~ v4_pre_topc(sK3,sK0)
    | v4_pre_topc(k1_setfam_1(k2_tarski(k2_struct_0(sK2),sK3)),sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl8_13
    | ~ spl8_30 ),
    inference(superposition,[],[f285,f287])).

fof(f287,plain,
    ( ! [X1] : k9_subset_1(k2_struct_0(sK2),sK3,X1) = k1_setfam_1(k2_tarski(X1,sK3))
    | ~ spl8_13 ),
    inference(forward_demodulation,[],[f183,f186])).

fof(f186,plain,
    ( ! [X1] : k9_subset_1(k2_struct_0(sK2),X1,sK3) = k1_setfam_1(k2_tarski(X1,sK3))
    | ~ spl8_13 ),
    inference(resolution,[],[f59,f132])).

fof(f132,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK2)))
    | ~ spl8_13 ),
    inference(avatar_component_clause,[],[f130])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) ) ),
    inference(definition_unfolding,[],[f54,f49])).

fof(f49,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f183,plain,
    ( ! [X1] : k9_subset_1(k2_struct_0(sK2),X1,sK3) = k9_subset_1(k2_struct_0(sK2),sK3,X1)
    | ~ spl8_13 ),
    inference(resolution,[],[f55,f132])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

fof(f285,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k9_subset_1(k2_struct_0(sK2),X0,k2_struct_0(sK2)),k1_zfmisc_1(k2_struct_0(sK2)))
        | ~ v4_pre_topc(X0,sK0)
        | v4_pre_topc(k9_subset_1(k2_struct_0(sK2),X0,k2_struct_0(sK2)),sK2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) )
    | ~ spl8_30 ),
    inference(avatar_component_clause,[],[f284])).

fof(f341,plain,
    ( spl8_35
    | ~ spl8_9
    | ~ spl8_17
    | ~ spl8_20 ),
    inference(avatar_split_clause,[],[f340,f176,f156,f106,f336])).

fof(f156,plain,
    ( spl8_17
  <=> sK3 = k1_setfam_1(k2_tarski(sK3,k2_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).

fof(f176,plain,
    ( spl8_20
  <=> m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).

fof(f340,plain,
    ( sK3 = k1_setfam_1(k2_tarski(k2_struct_0(sK2),sK3))
    | ~ spl8_9
    | ~ spl8_17
    | ~ spl8_20 ),
    inference(forward_demodulation,[],[f333,f158])).

fof(f158,plain,
    ( sK3 = k1_setfam_1(k2_tarski(sK3,k2_struct_0(sK2)))
    | ~ spl8_17 ),
    inference(avatar_component_clause,[],[f156])).

fof(f333,plain,
    ( k1_setfam_1(k2_tarski(sK3,k2_struct_0(sK2))) = k1_setfam_1(k2_tarski(k2_struct_0(sK2),sK3))
    | ~ spl8_9
    | ~ spl8_20 ),
    inference(superposition,[],[f276,f187])).

fof(f187,plain,
    ( ! [X2] : k9_subset_1(k2_struct_0(sK0),X2,k2_struct_0(sK2)) = k1_setfam_1(k2_tarski(X2,k2_struct_0(sK2)))
    | ~ spl8_20 ),
    inference(resolution,[],[f59,f178])).

fof(f178,plain,
    ( m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl8_20 ),
    inference(avatar_component_clause,[],[f176])).

fof(f276,plain,
    ( ! [X0] : k9_subset_1(k2_struct_0(sK0),sK3,X0) = k1_setfam_1(k2_tarski(X0,sK3))
    | ~ spl8_9 ),
    inference(forward_demodulation,[],[f182,f185])).

fof(f185,plain,
    ( ! [X0] : k9_subset_1(k2_struct_0(sK0),X0,sK3) = k1_setfam_1(k2_tarski(X0,sK3))
    | ~ spl8_9 ),
    inference(resolution,[],[f59,f108])).

fof(f108,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f106])).

fof(f182,plain,
    ( ! [X0] : k9_subset_1(k2_struct_0(sK0),X0,sK3) = k9_subset_1(k2_struct_0(sK0),sK3,X0)
    | ~ spl8_9 ),
    inference(resolution,[],[f55,f108])).

fof(f286,plain,
    ( ~ spl8_1
    | spl8_30
    | ~ spl8_4
    | ~ spl8_8
    | ~ spl8_12 ),
    inference(avatar_split_clause,[],[f282,f124,f100,f78,f284,f63])).

fof(f63,plain,
    ( spl8_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f78,plain,
    ( spl8_4
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f100,plain,
    ( spl8_8
  <=> u1_struct_0(sK0) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f124,plain,
    ( spl8_12
  <=> u1_struct_0(sK2) = k2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f282,plain,
    ( ! [X0] :
        ( v4_pre_topc(k9_subset_1(k2_struct_0(sK2),X0,k2_struct_0(sK2)),sK2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(k9_subset_1(k2_struct_0(sK2),X0,k2_struct_0(sK2)),k1_zfmisc_1(k2_struct_0(sK2)))
        | ~ l1_pre_topc(sK0)
        | ~ v4_pre_topc(X0,sK0) )
    | ~ spl8_4
    | ~ spl8_8
    | ~ spl8_12 ),
    inference(forward_demodulation,[],[f281,f126])).

fof(f126,plain,
    ( u1_struct_0(sK2) = k2_struct_0(sK2)
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f124])).

fof(f281,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(k9_subset_1(k2_struct_0(sK2),X0,k2_struct_0(sK2)),k1_zfmisc_1(k2_struct_0(sK2)))
        | ~ l1_pre_topc(sK0)
        | ~ v4_pre_topc(X0,sK0)
        | v4_pre_topc(k9_subset_1(u1_struct_0(sK2),X0,k2_struct_0(sK2)),sK2) )
    | ~ spl8_4
    | ~ spl8_8
    | ~ spl8_12 ),
    inference(forward_demodulation,[],[f280,f102])).

fof(f102,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f100])).

fof(f280,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k9_subset_1(k2_struct_0(sK2),X0,k2_struct_0(sK2)),k1_zfmisc_1(k2_struct_0(sK2)))
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v4_pre_topc(X0,sK0)
        | v4_pre_topc(k9_subset_1(u1_struct_0(sK2),X0,k2_struct_0(sK2)),sK2) )
    | ~ spl8_4
    | ~ spl8_12 ),
    inference(forward_demodulation,[],[f279,f126])).

fof(f279,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK2),X0,k2_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v4_pre_topc(X0,sK0)
        | v4_pre_topc(k9_subset_1(u1_struct_0(sK2),X0,k2_struct_0(sK2)),sK2) )
    | ~ spl8_4 ),
    inference(resolution,[],[f61,f80])).

fof(f80,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f78])).

fof(f61,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X3,X0)
      | v4_pre_topc(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),X1) ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X3,X0)
      | k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
      | v4_pre_topc(X2,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v4_pre_topc(X2,X1)
              <=> ? [X3] :
                    ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                    & v4_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => ( v4_pre_topc(X2,X1)
              <=> ? [X3] :
                    ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                    & v4_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_pre_topc)).

fof(f179,plain,
    ( spl8_20
    | ~ spl8_18 ),
    inference(avatar_split_clause,[],[f169,f164,f176])).

fof(f164,plain,
    ( spl8_18
  <=> r1_tarski(k2_struct_0(sK2),k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f169,plain,
    ( m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl8_18 ),
    inference(resolution,[],[f166,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f166,plain,
    ( r1_tarski(k2_struct_0(sK2),k2_struct_0(sK0))
    | ~ spl8_18 ),
    inference(avatar_component_clause,[],[f164])).

fof(f167,plain,
    ( ~ spl8_1
    | spl8_18
    | ~ spl8_10
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f162,f78,f112,f164,f63])).

fof(f112,plain,
    ( spl8_10
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f162,plain,
    ( ~ l1_pre_topc(sK2)
    | r1_tarski(k2_struct_0(sK2),k2_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ spl8_4 ),
    inference(resolution,[],[f43,f80])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X1)
      | r1_tarski(k2_struct_0(X1),k2_struct_0(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X1,X0)
          <=> ( ! [X2] :
                  ( ( r2_hidden(X2,u1_pre_topc(X1))
                  <=> ? [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                        & r2_hidden(X3,u1_pre_topc(X0))
                        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
              & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X1,X0)
          <=> ( ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( r2_hidden(X2,u1_pre_topc(X1))
                  <=> ? [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                        & r2_hidden(X3,u1_pre_topc(X0))
                        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) )
              & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_pre_topc)).

fof(f159,plain,
    ( spl8_17
    | ~ spl8_15 ),
    inference(avatar_split_clause,[],[f153,f142,f156])).

fof(f142,plain,
    ( spl8_15
  <=> r1_tarski(sK3,k2_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).

fof(f153,plain,
    ( sK3 = k1_setfam_1(k2_tarski(sK3,k2_struct_0(sK2)))
    | ~ spl8_15 ),
    inference(resolution,[],[f144,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_setfam_1(k2_tarski(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f50,f49])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f144,plain,
    ( r1_tarski(sK3,k2_struct_0(sK2))
    | ~ spl8_15 ),
    inference(avatar_component_clause,[],[f142])).

fof(f145,plain,
    ( spl8_15
    | ~ spl8_13 ),
    inference(avatar_split_clause,[],[f135,f130,f142])).

fof(f135,plain,
    ( r1_tarski(sK3,k2_struct_0(sK2))
    | ~ spl8_13 ),
    inference(resolution,[],[f52,f132])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f133,plain,
    ( spl8_13
    | ~ spl8_6
    | ~ spl8_12 ),
    inference(avatar_split_clause,[],[f128,f124,f88,f130])).

fof(f88,plain,
    ( spl8_6
  <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f128,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK2)))
    | ~ spl8_6
    | ~ spl8_12 ),
    inference(backward_demodulation,[],[f90,f126])).

fof(f90,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f88])).

fof(f127,plain,
    ( spl8_12
    | ~ spl8_11 ),
    inference(avatar_split_clause,[],[f122,f118,f124])).

fof(f118,plain,
    ( spl8_11
  <=> l1_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f122,plain,
    ( u1_struct_0(sK2) = k2_struct_0(sK2)
    | ~ spl8_11 ),
    inference(resolution,[],[f120,f32])).

fof(f32,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f120,plain,
    ( l1_struct_0(sK2)
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f118])).

fof(f121,plain,
    ( spl8_11
    | ~ spl8_10 ),
    inference(avatar_split_clause,[],[f116,f112,f118])).

fof(f116,plain,
    ( l1_struct_0(sK2)
    | ~ spl8_10 ),
    inference(resolution,[],[f114,f33])).

fof(f33,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f114,plain,
    ( l1_pre_topc(sK2)
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f112])).

fof(f115,plain,
    ( spl8_10
    | ~ spl8_1
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f110,f78,f63,f112])).

fof(f110,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK2)
    | ~ spl8_4 ),
    inference(resolution,[],[f44,f80])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f109,plain,
    ( spl8_9
    | ~ spl8_2
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f104,f100,f68,f106])).

fof(f68,plain,
    ( spl8_2
  <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f104,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl8_2
    | ~ spl8_8 ),
    inference(backward_demodulation,[],[f70,f102])).

fof(f70,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f68])).

fof(f103,plain,
    ( spl8_8
    | ~ spl8_7 ),
    inference(avatar_split_clause,[],[f98,f94,f100])).

fof(f94,plain,
    ( spl8_7
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f98,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl8_7 ),
    inference(resolution,[],[f32,f96])).

fof(f96,plain,
    ( l1_struct_0(sK0)
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f94])).

fof(f97,plain,
    ( spl8_7
    | ~ spl8_1 ),
    inference(avatar_split_clause,[],[f92,f63,f94])).

fof(f92,plain,
    ( l1_struct_0(sK0)
    | ~ spl8_1 ),
    inference(resolution,[],[f33,f65])).

fof(f65,plain,
    ( l1_pre_topc(sK0)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f63])).

fof(f91,plain,(
    spl8_6 ),
    inference(avatar_split_clause,[],[f25,f88])).

fof(f25,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v4_pre_topc(X3,X2)
                  & X1 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              & v4_pre_topc(X1,X0)
              & m1_pre_topc(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v4_pre_topc(X3,X2)
                  & X1 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              & v4_pre_topc(X1,X0)
              & m1_pre_topc(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_pre_topc(X2,X0)
               => ( v4_pre_topc(X1,X0)
                 => ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
                     => ( X1 = X3
                       => v4_pre_topc(X3,X2) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( v4_pre_topc(X1,X0)
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
                   => ( X1 = X3
                     => v4_pre_topc(X3,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_tops_2)).

fof(f86,plain,(
    ~ spl8_5 ),
    inference(avatar_split_clause,[],[f27,f83])).

fof(f27,plain,(
    ~ v4_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f81,plain,(
    spl8_4 ),
    inference(avatar_split_clause,[],[f28,f78])).

fof(f28,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f76,plain,(
    spl8_3 ),
    inference(avatar_split_clause,[],[f57,f73])).

fof(f57,plain,(
    v4_pre_topc(sK3,sK0) ),
    inference(definition_unfolding,[],[f29,f26])).

fof(f26,plain,(
    sK1 = sK3 ),
    inference(cnf_transformation,[],[f15])).

fof(f29,plain,(
    v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f71,plain,(
    spl8_2 ),
    inference(avatar_split_clause,[],[f56,f68])).

fof(f56,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(definition_unfolding,[],[f30,f26])).

fof(f30,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f15])).

fof(f66,plain,(
    spl8_1 ),
    inference(avatar_split_clause,[],[f31,f63])).

fof(f31,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:07:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (6487)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.50  % (6479)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.50  % (6474)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.51  % (6474)Refutation not found, incomplete strategy% (6474)------------------------------
% 0.21/0.51  % (6474)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (6466)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (6474)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (6474)Memory used [KB]: 10746
% 0.21/0.51  % (6474)Time elapsed: 0.104 s
% 0.21/0.51  % (6474)------------------------------
% 0.21/0.51  % (6474)------------------------------
% 0.21/0.51  % (6471)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.52  % (6481)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.52  % (6481)Refutation not found, incomplete strategy% (6481)------------------------------
% 0.21/0.52  % (6481)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (6481)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (6481)Memory used [KB]: 10618
% 0.21/0.52  % (6481)Time elapsed: 0.115 s
% 0.21/0.52  % (6481)------------------------------
% 0.21/0.52  % (6481)------------------------------
% 0.21/0.53  % (6469)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (6468)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.53  % (6488)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.53  % (6467)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (6464)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (6465)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (6490)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.53  % (6470)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (6473)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.53  % (6486)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.53  % (6493)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.54  % (6486)Refutation not found, incomplete strategy% (6486)------------------------------
% 0.21/0.54  % (6486)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (6486)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (6486)Memory used [KB]: 10874
% 0.21/0.54  % (6486)Time elapsed: 0.136 s
% 0.21/0.54  % (6486)------------------------------
% 0.21/0.54  % (6486)------------------------------
% 0.21/0.54  % (6477)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.54  % (6485)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.54  % (6484)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.54  % (6480)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.54  % (6482)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.54  % (6491)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.55  % (6475)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (6489)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.55  % (6472)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.55  % (6476)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.55  % (6478)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.55  % (6492)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.55  % (6483)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.57  % (6480)Refutation found. Thanks to Tanya!
% 0.21/0.57  % SZS status Theorem for theBenchmark
% 0.21/0.57  % SZS output start Proof for theBenchmark
% 0.21/0.57  fof(f364,plain,(
% 0.21/0.57    $false),
% 0.21/0.57    inference(avatar_sat_refutation,[],[f66,f71,f76,f81,f86,f91,f97,f103,f109,f115,f121,f127,f133,f145,f159,f167,f179,f286,f341,f363])).
% 0.21/0.57  fof(f363,plain,(
% 0.21/0.57    ~spl8_9 | ~spl8_3 | ~spl8_13 | spl8_5 | ~spl8_13 | ~spl8_30 | ~spl8_35),
% 0.21/0.57    inference(avatar_split_clause,[],[f362,f336,f284,f130,f83,f130,f73,f106])).
% 0.21/0.57  fof(f106,plain,(
% 0.21/0.57    spl8_9 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 0.21/0.57  fof(f73,plain,(
% 0.21/0.57    spl8_3 <=> v4_pre_topc(sK3,sK0)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.21/0.57  fof(f83,plain,(
% 0.21/0.57    spl8_5 <=> v4_pre_topc(sK3,sK2)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.21/0.57  fof(f130,plain,(
% 0.21/0.57    spl8_13 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK2)))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).
% 0.21/0.57  fof(f284,plain,(
% 0.21/0.57    spl8_30 <=> ! [X0] : (v4_pre_topc(k9_subset_1(k2_struct_0(sK2),X0,k2_struct_0(sK2)),sK2) | ~v4_pre_topc(X0,sK0) | ~m1_subset_1(k9_subset_1(k2_struct_0(sK2),X0,k2_struct_0(sK2)),k1_zfmisc_1(k2_struct_0(sK2))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_30])])).
% 0.21/0.57  fof(f336,plain,(
% 0.21/0.57    spl8_35 <=> sK3 = k1_setfam_1(k2_tarski(k2_struct_0(sK2),sK3))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_35])])).
% 0.21/0.57  fof(f362,plain,(
% 0.21/0.57    v4_pre_topc(sK3,sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK2))) | ~v4_pre_topc(sK3,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK0))) | (~spl8_13 | ~spl8_30 | ~spl8_35)),
% 0.21/0.57    inference(forward_demodulation,[],[f361,f338])).
% 0.21/0.57  fof(f338,plain,(
% 0.21/0.57    sK3 = k1_setfam_1(k2_tarski(k2_struct_0(sK2),sK3)) | ~spl8_35),
% 0.21/0.57    inference(avatar_component_clause,[],[f336])).
% 0.21/0.57  fof(f361,plain,(
% 0.21/0.57    ~m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK2))) | ~v4_pre_topc(sK3,sK0) | v4_pre_topc(k1_setfam_1(k2_tarski(k2_struct_0(sK2),sK3)),sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK0))) | (~spl8_13 | ~spl8_30 | ~spl8_35)),
% 0.21/0.57    inference(forward_demodulation,[],[f360,f338])).
% 0.21/0.57  fof(f360,plain,(
% 0.21/0.57    ~m1_subset_1(k1_setfam_1(k2_tarski(k2_struct_0(sK2),sK3)),k1_zfmisc_1(k2_struct_0(sK2))) | ~v4_pre_topc(sK3,sK0) | v4_pre_topc(k1_setfam_1(k2_tarski(k2_struct_0(sK2),sK3)),sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK0))) | (~spl8_13 | ~spl8_30)),
% 0.21/0.57    inference(superposition,[],[f285,f287])).
% 0.21/0.57  fof(f287,plain,(
% 0.21/0.57    ( ! [X1] : (k9_subset_1(k2_struct_0(sK2),sK3,X1) = k1_setfam_1(k2_tarski(X1,sK3))) ) | ~spl8_13),
% 0.21/0.57    inference(forward_demodulation,[],[f183,f186])).
% 0.21/0.57  fof(f186,plain,(
% 0.21/0.57    ( ! [X1] : (k9_subset_1(k2_struct_0(sK2),X1,sK3) = k1_setfam_1(k2_tarski(X1,sK3))) ) | ~spl8_13),
% 0.21/0.57    inference(resolution,[],[f59,f132])).
% 0.21/0.57  fof(f132,plain,(
% 0.21/0.57    m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK2))) | ~spl8_13),
% 0.21/0.57    inference(avatar_component_clause,[],[f130])).
% 0.21/0.57  fof(f59,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))) )),
% 0.21/0.57    inference(definition_unfolding,[],[f54,f49])).
% 0.21/0.57  fof(f49,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f5])).
% 0.21/0.57  fof(f5,axiom,(
% 0.21/0.57    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.21/0.57  fof(f54,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f23])).
% 0.21/0.57  fof(f23,plain,(
% 0.21/0.57    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.21/0.57    inference(ennf_transformation,[],[f4])).
% 0.21/0.57  fof(f4,axiom,(
% 0.21/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 0.21/0.57  fof(f183,plain,(
% 0.21/0.57    ( ! [X1] : (k9_subset_1(k2_struct_0(sK2),X1,sK3) = k9_subset_1(k2_struct_0(sK2),sK3,X1)) ) | ~spl8_13),
% 0.21/0.57    inference(resolution,[],[f55,f132])).
% 0.21/0.57  fof(f55,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f24])).
% 0.21/0.57  fof(f24,plain,(
% 0.21/0.57    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.21/0.57    inference(ennf_transformation,[],[f2])).
% 0.21/0.57  fof(f2,axiom,(
% 0.21/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k9_subset_1)).
% 0.21/0.57  fof(f285,plain,(
% 0.21/0.57    ( ! [X0] : (~m1_subset_1(k9_subset_1(k2_struct_0(sK2),X0,k2_struct_0(sK2)),k1_zfmisc_1(k2_struct_0(sK2))) | ~v4_pre_topc(X0,sK0) | v4_pre_topc(k9_subset_1(k2_struct_0(sK2),X0,k2_struct_0(sK2)),sK2) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))) ) | ~spl8_30),
% 0.21/0.57    inference(avatar_component_clause,[],[f284])).
% 0.21/0.57  fof(f341,plain,(
% 0.21/0.57    spl8_35 | ~spl8_9 | ~spl8_17 | ~spl8_20),
% 0.21/0.57    inference(avatar_split_clause,[],[f340,f176,f156,f106,f336])).
% 0.21/0.57  fof(f156,plain,(
% 0.21/0.57    spl8_17 <=> sK3 = k1_setfam_1(k2_tarski(sK3,k2_struct_0(sK2)))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).
% 0.21/0.57  fof(f176,plain,(
% 0.21/0.57    spl8_20 <=> m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).
% 0.21/0.57  fof(f340,plain,(
% 0.21/0.57    sK3 = k1_setfam_1(k2_tarski(k2_struct_0(sK2),sK3)) | (~spl8_9 | ~spl8_17 | ~spl8_20)),
% 0.21/0.57    inference(forward_demodulation,[],[f333,f158])).
% 0.21/0.57  fof(f158,plain,(
% 0.21/0.57    sK3 = k1_setfam_1(k2_tarski(sK3,k2_struct_0(sK2))) | ~spl8_17),
% 0.21/0.57    inference(avatar_component_clause,[],[f156])).
% 0.21/0.57  fof(f333,plain,(
% 0.21/0.57    k1_setfam_1(k2_tarski(sK3,k2_struct_0(sK2))) = k1_setfam_1(k2_tarski(k2_struct_0(sK2),sK3)) | (~spl8_9 | ~spl8_20)),
% 0.21/0.57    inference(superposition,[],[f276,f187])).
% 0.21/0.57  fof(f187,plain,(
% 0.21/0.57    ( ! [X2] : (k9_subset_1(k2_struct_0(sK0),X2,k2_struct_0(sK2)) = k1_setfam_1(k2_tarski(X2,k2_struct_0(sK2)))) ) | ~spl8_20),
% 0.21/0.57    inference(resolution,[],[f59,f178])).
% 0.21/0.57  fof(f178,plain,(
% 0.21/0.57    m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK0))) | ~spl8_20),
% 0.21/0.57    inference(avatar_component_clause,[],[f176])).
% 0.21/0.57  fof(f276,plain,(
% 0.21/0.57    ( ! [X0] : (k9_subset_1(k2_struct_0(sK0),sK3,X0) = k1_setfam_1(k2_tarski(X0,sK3))) ) | ~spl8_9),
% 0.21/0.57    inference(forward_demodulation,[],[f182,f185])).
% 0.21/0.57  fof(f185,plain,(
% 0.21/0.57    ( ! [X0] : (k9_subset_1(k2_struct_0(sK0),X0,sK3) = k1_setfam_1(k2_tarski(X0,sK3))) ) | ~spl8_9),
% 0.21/0.57    inference(resolution,[],[f59,f108])).
% 0.21/0.57  fof(f108,plain,(
% 0.21/0.57    m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK0))) | ~spl8_9),
% 0.21/0.57    inference(avatar_component_clause,[],[f106])).
% 0.21/0.57  fof(f182,plain,(
% 0.21/0.57    ( ! [X0] : (k9_subset_1(k2_struct_0(sK0),X0,sK3) = k9_subset_1(k2_struct_0(sK0),sK3,X0)) ) | ~spl8_9),
% 0.21/0.57    inference(resolution,[],[f55,f108])).
% 0.21/0.57  fof(f286,plain,(
% 0.21/0.57    ~spl8_1 | spl8_30 | ~spl8_4 | ~spl8_8 | ~spl8_12),
% 0.21/0.57    inference(avatar_split_clause,[],[f282,f124,f100,f78,f284,f63])).
% 0.21/0.57  fof(f63,plain,(
% 0.21/0.57    spl8_1 <=> l1_pre_topc(sK0)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.21/0.57  fof(f78,plain,(
% 0.21/0.57    spl8_4 <=> m1_pre_topc(sK2,sK0)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.21/0.57  fof(f100,plain,(
% 0.21/0.57    spl8_8 <=> u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 0.21/0.57  fof(f124,plain,(
% 0.21/0.57    spl8_12 <=> u1_struct_0(sK2) = k2_struct_0(sK2)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).
% 0.21/0.57  fof(f282,plain,(
% 0.21/0.57    ( ! [X0] : (v4_pre_topc(k9_subset_1(k2_struct_0(sK2),X0,k2_struct_0(sK2)),sK2) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(k9_subset_1(k2_struct_0(sK2),X0,k2_struct_0(sK2)),k1_zfmisc_1(k2_struct_0(sK2))) | ~l1_pre_topc(sK0) | ~v4_pre_topc(X0,sK0)) ) | (~spl8_4 | ~spl8_8 | ~spl8_12)),
% 0.21/0.57    inference(forward_demodulation,[],[f281,f126])).
% 0.21/0.57  fof(f126,plain,(
% 0.21/0.57    u1_struct_0(sK2) = k2_struct_0(sK2) | ~spl8_12),
% 0.21/0.57    inference(avatar_component_clause,[],[f124])).
% 0.21/0.57  fof(f281,plain,(
% 0.21/0.57    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(k9_subset_1(k2_struct_0(sK2),X0,k2_struct_0(sK2)),k1_zfmisc_1(k2_struct_0(sK2))) | ~l1_pre_topc(sK0) | ~v4_pre_topc(X0,sK0) | v4_pre_topc(k9_subset_1(u1_struct_0(sK2),X0,k2_struct_0(sK2)),sK2)) ) | (~spl8_4 | ~spl8_8 | ~spl8_12)),
% 0.21/0.57    inference(forward_demodulation,[],[f280,f102])).
% 0.21/0.57  fof(f102,plain,(
% 0.21/0.57    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl8_8),
% 0.21/0.57    inference(avatar_component_clause,[],[f100])).
% 0.21/0.57  fof(f280,plain,(
% 0.21/0.57    ( ! [X0] : (~m1_subset_1(k9_subset_1(k2_struct_0(sK2),X0,k2_struct_0(sK2)),k1_zfmisc_1(k2_struct_0(sK2))) | ~l1_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(X0,sK0) | v4_pre_topc(k9_subset_1(u1_struct_0(sK2),X0,k2_struct_0(sK2)),sK2)) ) | (~spl8_4 | ~spl8_12)),
% 0.21/0.57    inference(forward_demodulation,[],[f279,f126])).
% 0.21/0.57  fof(f279,plain,(
% 0.21/0.57    ( ! [X0] : (~l1_pre_topc(sK0) | ~m1_subset_1(k9_subset_1(u1_struct_0(sK2),X0,k2_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK2))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(X0,sK0) | v4_pre_topc(k9_subset_1(u1_struct_0(sK2),X0,k2_struct_0(sK2)),sK2)) ) | ~spl8_4),
% 0.21/0.57    inference(resolution,[],[f61,f80])).
% 0.21/0.57  fof(f80,plain,(
% 0.21/0.57    m1_pre_topc(sK2,sK0) | ~spl8_4),
% 0.21/0.57    inference(avatar_component_clause,[],[f78])).
% 0.21/0.57  fof(f61,plain,(
% 0.21/0.57    ( ! [X0,X3,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~m1_subset_1(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X3,X0) | v4_pre_topc(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),X1)) )),
% 0.21/0.57    inference(equality_resolution,[],[f48])).
% 0.21/0.57  fof(f48,plain,(
% 0.21/0.57    ( ! [X2,X0,X3,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X3,X0) | k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | v4_pre_topc(X2,X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f20])).
% 0.21/0.57  fof(f20,plain,(
% 0.21/0.57    ! [X0] : (! [X1] : (! [X2] : ((v4_pre_topc(X2,X1) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.57    inference(ennf_transformation,[],[f11])).
% 0.21/0.57  fof(f11,axiom,(
% 0.21/0.57    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => (v4_pre_topc(X2,X1) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))))))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_pre_topc)).
% 0.21/0.57  fof(f179,plain,(
% 0.21/0.57    spl8_20 | ~spl8_18),
% 0.21/0.57    inference(avatar_split_clause,[],[f169,f164,f176])).
% 0.21/0.57  fof(f164,plain,(
% 0.21/0.57    spl8_18 <=> r1_tarski(k2_struct_0(sK2),k2_struct_0(sK0))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).
% 0.21/0.57  fof(f169,plain,(
% 0.21/0.57    m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK0))) | ~spl8_18),
% 0.21/0.57    inference(resolution,[],[f166,f51])).
% 0.21/0.57  fof(f51,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f6])).
% 0.21/0.57  fof(f6,axiom,(
% 0.21/0.57    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.57  fof(f166,plain,(
% 0.21/0.57    r1_tarski(k2_struct_0(sK2),k2_struct_0(sK0)) | ~spl8_18),
% 0.21/0.57    inference(avatar_component_clause,[],[f164])).
% 0.21/0.57  fof(f167,plain,(
% 0.21/0.57    ~spl8_1 | spl8_18 | ~spl8_10 | ~spl8_4),
% 0.21/0.57    inference(avatar_split_clause,[],[f162,f78,f112,f164,f63])).
% 0.21/0.57  fof(f112,plain,(
% 0.21/0.57    spl8_10 <=> l1_pre_topc(sK2)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 0.21/0.57  fof(f162,plain,(
% 0.21/0.57    ~l1_pre_topc(sK2) | r1_tarski(k2_struct_0(sK2),k2_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~spl8_4),
% 0.21/0.57    inference(resolution,[],[f43,f80])).
% 0.21/0.57  fof(f43,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X1) | r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) | ~l1_pre_topc(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f18])).
% 0.21/0.57  fof(f18,plain,(
% 0.21/0.57    ! [X0] : (! [X1] : ((m1_pre_topc(X1,X0) <=> (! [X2] : ((r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.21/0.57    inference(ennf_transformation,[],[f8])).
% 0.21/0.57  fof(f8,axiom,(
% 0.21/0.57    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => (r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))))))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_pre_topc)).
% 0.21/0.57  fof(f159,plain,(
% 0.21/0.57    spl8_17 | ~spl8_15),
% 0.21/0.57    inference(avatar_split_clause,[],[f153,f142,f156])).
% 0.21/0.57  fof(f142,plain,(
% 0.21/0.57    spl8_15 <=> r1_tarski(sK3,k2_struct_0(sK2))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).
% 0.21/0.57  fof(f153,plain,(
% 0.21/0.57    sK3 = k1_setfam_1(k2_tarski(sK3,k2_struct_0(sK2))) | ~spl8_15),
% 0.21/0.57    inference(resolution,[],[f144,f58])).
% 0.21/0.57  fof(f58,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_setfam_1(k2_tarski(X0,X1)) = X0) )),
% 0.21/0.57    inference(definition_unfolding,[],[f50,f49])).
% 0.21/0.57  fof(f50,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.21/0.57    inference(cnf_transformation,[],[f21])).
% 0.21/0.57  fof(f21,plain,(
% 0.21/0.57    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.57    inference(ennf_transformation,[],[f1])).
% 0.21/0.57  fof(f1,axiom,(
% 0.21/0.57    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.21/0.57  fof(f144,plain,(
% 0.21/0.57    r1_tarski(sK3,k2_struct_0(sK2)) | ~spl8_15),
% 0.21/0.57    inference(avatar_component_clause,[],[f142])).
% 0.21/0.57  fof(f145,plain,(
% 0.21/0.57    spl8_15 | ~spl8_13),
% 0.21/0.57    inference(avatar_split_clause,[],[f135,f130,f142])).
% 0.21/0.57  fof(f135,plain,(
% 0.21/0.57    r1_tarski(sK3,k2_struct_0(sK2)) | ~spl8_13),
% 0.21/0.57    inference(resolution,[],[f52,f132])).
% 0.21/0.57  fof(f52,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f6])).
% 0.21/0.57  fof(f133,plain,(
% 0.21/0.57    spl8_13 | ~spl8_6 | ~spl8_12),
% 0.21/0.57    inference(avatar_split_clause,[],[f128,f124,f88,f130])).
% 0.21/0.57  fof(f88,plain,(
% 0.21/0.57    spl8_6 <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.21/0.57  fof(f128,plain,(
% 0.21/0.57    m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK2))) | (~spl8_6 | ~spl8_12)),
% 0.21/0.57    inference(backward_demodulation,[],[f90,f126])).
% 0.21/0.57  fof(f90,plain,(
% 0.21/0.57    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) | ~spl8_6),
% 0.21/0.57    inference(avatar_component_clause,[],[f88])).
% 0.21/0.57  fof(f127,plain,(
% 0.21/0.57    spl8_12 | ~spl8_11),
% 0.21/0.57    inference(avatar_split_clause,[],[f122,f118,f124])).
% 0.21/0.57  fof(f118,plain,(
% 0.21/0.57    spl8_11 <=> l1_struct_0(sK2)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).
% 0.21/0.57  fof(f122,plain,(
% 0.21/0.57    u1_struct_0(sK2) = k2_struct_0(sK2) | ~spl8_11),
% 0.21/0.57    inference(resolution,[],[f120,f32])).
% 0.21/0.57  fof(f32,plain,(
% 0.21/0.57    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f16])).
% 0.21/0.57  fof(f16,plain,(
% 0.21/0.57    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.21/0.57    inference(ennf_transformation,[],[f7])).
% 0.21/0.57  fof(f7,axiom,(
% 0.21/0.57    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.21/0.57  fof(f120,plain,(
% 0.21/0.57    l1_struct_0(sK2) | ~spl8_11),
% 0.21/0.57    inference(avatar_component_clause,[],[f118])).
% 0.21/0.57  fof(f121,plain,(
% 0.21/0.57    spl8_11 | ~spl8_10),
% 0.21/0.57    inference(avatar_split_clause,[],[f116,f112,f118])).
% 0.21/0.57  fof(f116,plain,(
% 0.21/0.57    l1_struct_0(sK2) | ~spl8_10),
% 0.21/0.57    inference(resolution,[],[f114,f33])).
% 0.21/0.57  fof(f33,plain,(
% 0.21/0.57    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f17])).
% 0.21/0.57  fof(f17,plain,(
% 0.21/0.57    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.57    inference(ennf_transformation,[],[f9])).
% 0.21/0.57  fof(f9,axiom,(
% 0.21/0.57    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.57  fof(f114,plain,(
% 0.21/0.57    l1_pre_topc(sK2) | ~spl8_10),
% 0.21/0.57    inference(avatar_component_clause,[],[f112])).
% 0.21/0.57  fof(f115,plain,(
% 0.21/0.57    spl8_10 | ~spl8_1 | ~spl8_4),
% 0.21/0.57    inference(avatar_split_clause,[],[f110,f78,f63,f112])).
% 0.21/0.57  fof(f110,plain,(
% 0.21/0.57    ~l1_pre_topc(sK0) | l1_pre_topc(sK2) | ~spl8_4),
% 0.21/0.57    inference(resolution,[],[f44,f80])).
% 0.21/0.57  fof(f44,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | l1_pre_topc(X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f19])).
% 0.21/0.57  fof(f19,plain,(
% 0.21/0.57    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.57    inference(ennf_transformation,[],[f10])).
% 0.21/0.57  fof(f10,axiom,(
% 0.21/0.57    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.21/0.57  fof(f109,plain,(
% 0.21/0.57    spl8_9 | ~spl8_2 | ~spl8_8),
% 0.21/0.57    inference(avatar_split_clause,[],[f104,f100,f68,f106])).
% 0.21/0.57  fof(f68,plain,(
% 0.21/0.57    spl8_2 <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.21/0.57  fof(f104,plain,(
% 0.21/0.57    m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK0))) | (~spl8_2 | ~spl8_8)),
% 0.21/0.57    inference(backward_demodulation,[],[f70,f102])).
% 0.21/0.57  fof(f70,plain,(
% 0.21/0.57    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl8_2),
% 0.21/0.57    inference(avatar_component_clause,[],[f68])).
% 0.21/0.57  fof(f103,plain,(
% 0.21/0.57    spl8_8 | ~spl8_7),
% 0.21/0.57    inference(avatar_split_clause,[],[f98,f94,f100])).
% 0.21/0.57  fof(f94,plain,(
% 0.21/0.57    spl8_7 <=> l1_struct_0(sK0)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 0.21/0.57  fof(f98,plain,(
% 0.21/0.57    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl8_7),
% 0.21/0.57    inference(resolution,[],[f32,f96])).
% 0.21/0.57  fof(f96,plain,(
% 0.21/0.57    l1_struct_0(sK0) | ~spl8_7),
% 0.21/0.57    inference(avatar_component_clause,[],[f94])).
% 0.21/0.57  fof(f97,plain,(
% 0.21/0.57    spl8_7 | ~spl8_1),
% 0.21/0.57    inference(avatar_split_clause,[],[f92,f63,f94])).
% 0.21/0.57  fof(f92,plain,(
% 0.21/0.57    l1_struct_0(sK0) | ~spl8_1),
% 0.21/0.57    inference(resolution,[],[f33,f65])).
% 0.21/0.57  fof(f65,plain,(
% 0.21/0.57    l1_pre_topc(sK0) | ~spl8_1),
% 0.21/0.57    inference(avatar_component_clause,[],[f63])).
% 0.21/0.57  fof(f91,plain,(
% 0.21/0.57    spl8_6),
% 0.21/0.57    inference(avatar_split_clause,[],[f25,f88])).
% 0.21/0.57  fof(f25,plain,(
% 0.21/0.57    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.21/0.57    inference(cnf_transformation,[],[f15])).
% 0.21/0.57  fof(f15,plain,(
% 0.21/0.57    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~v4_pre_topc(X3,X2) & X1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v4_pre_topc(X1,X0) & m1_pre_topc(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.21/0.57    inference(flattening,[],[f14])).
% 0.21/0.57  fof(f14,plain,(
% 0.21/0.57    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : ((~v4_pre_topc(X3,X2) & X1 = X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v4_pre_topc(X1,X0)) & m1_pre_topc(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.21/0.57    inference(ennf_transformation,[],[f13])).
% 0.21/0.57  fof(f13,negated_conjecture,(
% 0.21/0.57    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_pre_topc(X2,X0) => (v4_pre_topc(X1,X0) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) => (X1 = X3 => v4_pre_topc(X3,X2)))))))),
% 0.21/0.57    inference(negated_conjecture,[],[f12])).
% 0.21/0.57  fof(f12,conjecture,(
% 0.21/0.57    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_pre_topc(X2,X0) => (v4_pre_topc(X1,X0) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) => (X1 = X3 => v4_pre_topc(X3,X2)))))))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_tops_2)).
% 0.21/0.57  fof(f86,plain,(
% 0.21/0.57    ~spl8_5),
% 0.21/0.57    inference(avatar_split_clause,[],[f27,f83])).
% 0.21/0.57  fof(f27,plain,(
% 0.21/0.57    ~v4_pre_topc(sK3,sK2)),
% 0.21/0.57    inference(cnf_transformation,[],[f15])).
% 0.21/0.57  fof(f81,plain,(
% 0.21/0.57    spl8_4),
% 0.21/0.57    inference(avatar_split_clause,[],[f28,f78])).
% 0.21/0.57  fof(f28,plain,(
% 0.21/0.57    m1_pre_topc(sK2,sK0)),
% 0.21/0.57    inference(cnf_transformation,[],[f15])).
% 0.21/0.57  fof(f76,plain,(
% 0.21/0.57    spl8_3),
% 0.21/0.57    inference(avatar_split_clause,[],[f57,f73])).
% 0.21/0.57  fof(f57,plain,(
% 0.21/0.57    v4_pre_topc(sK3,sK0)),
% 0.21/0.57    inference(definition_unfolding,[],[f29,f26])).
% 0.21/0.57  fof(f26,plain,(
% 0.21/0.57    sK1 = sK3),
% 0.21/0.57    inference(cnf_transformation,[],[f15])).
% 0.21/0.57  fof(f29,plain,(
% 0.21/0.57    v4_pre_topc(sK1,sK0)),
% 0.21/0.57    inference(cnf_transformation,[],[f15])).
% 0.21/0.57  fof(f71,plain,(
% 0.21/0.57    spl8_2),
% 0.21/0.57    inference(avatar_split_clause,[],[f56,f68])).
% 0.21/0.57  fof(f56,plain,(
% 0.21/0.57    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.57    inference(definition_unfolding,[],[f30,f26])).
% 0.21/0.57  fof(f30,plain,(
% 0.21/0.57    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.57    inference(cnf_transformation,[],[f15])).
% 0.21/0.57  fof(f66,plain,(
% 0.21/0.57    spl8_1),
% 0.21/0.57    inference(avatar_split_clause,[],[f31,f63])).
% 0.21/0.57  fof(f31,plain,(
% 0.21/0.57    l1_pre_topc(sK0)),
% 0.21/0.57    inference(cnf_transformation,[],[f15])).
% 0.21/0.57  % SZS output end Proof for theBenchmark
% 0.21/0.57  % (6480)------------------------------
% 0.21/0.57  % (6480)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (6480)Termination reason: Refutation
% 0.21/0.57  
% 0.21/0.57  % (6480)Memory used [KB]: 10874
% 0.21/0.57  % (6480)Time elapsed: 0.153 s
% 0.21/0.57  % (6480)------------------------------
% 0.21/0.57  % (6480)------------------------------
% 0.21/0.57  % (6463)Success in time 0.215 s
%------------------------------------------------------------------------------
