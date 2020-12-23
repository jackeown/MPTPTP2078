%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:13:46 EST 2020

% Result     : Theorem 1.53s
% Output     : Refutation 1.53s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 241 expanded)
%              Number of leaves         :   28 (  93 expanded)
%              Depth                    :   12
%              Number of atoms          :  341 ( 721 expanded)
%              Number of equality atoms :   42 ( 109 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f866,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f69,f74,f79,f84,f89,f94,f100,f106,f112,f118,f124,f130,f136,f148,f248,f781,f787,f865])).

fof(f865,plain,
    ( ~ spl7_9
    | spl7_5
    | ~ spl7_3
    | ~ spl7_13
    | ~ spl7_19
    | ~ spl7_32 ),
    inference(avatar_split_clause,[],[f844,f778,f246,f133,f76,f86,f109])).

fof(f109,plain,
    ( spl7_9
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f86,plain,
    ( spl7_5
  <=> v4_pre_topc(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f76,plain,
    ( spl7_3
  <=> v4_pre_topc(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f133,plain,
    ( spl7_13
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f246,plain,
    ( spl7_19
  <=> ! [X0] :
        ( v4_pre_topc(k1_setfam_1(k2_tarski(X0,k2_struct_0(sK2))),sK2)
        | ~ v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(k1_setfam_1(k2_tarski(X0,k2_struct_0(sK2))),k1_zfmisc_1(k2_struct_0(sK2)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f778,plain,
    ( spl7_32
  <=> sK3 = k1_setfam_1(k2_tarski(sK3,k2_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_32])])).

fof(f844,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK2)))
    | ~ v4_pre_topc(sK3,sK0)
    | v4_pre_topc(sK3,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl7_19
    | ~ spl7_32 ),
    inference(superposition,[],[f247,f780])).

fof(f780,plain,
    ( sK3 = k1_setfam_1(k2_tarski(sK3,k2_struct_0(sK2)))
    | ~ spl7_32 ),
    inference(avatar_component_clause,[],[f778])).

fof(f247,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k1_setfam_1(k2_tarski(X0,k2_struct_0(sK2))),k1_zfmisc_1(k2_struct_0(sK2)))
        | ~ v4_pre_topc(X0,sK0)
        | v4_pre_topc(k1_setfam_1(k2_tarski(X0,k2_struct_0(sK2))),sK2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) )
    | ~ spl7_19 ),
    inference(avatar_component_clause,[],[f246])).

fof(f787,plain,
    ( spl7_32
    | spl7_31 ),
    inference(avatar_split_clause,[],[f786,f774,f778])).

fof(f774,plain,
    ( spl7_31
  <=> r2_hidden(sK6(k2_struct_0(sK2),sK3,sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).

fof(f786,plain,
    ( sK3 = k1_setfam_1(k2_tarski(sK3,k2_struct_0(sK2)))
    | spl7_31 ),
    inference(forward_demodulation,[],[f782,f37])).

fof(f37,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f782,plain,
    ( sK3 = k1_setfam_1(k2_tarski(k2_struct_0(sK2),sK3))
    | spl7_31 ),
    inference(resolution,[],[f776,f178])).

fof(f178,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1,X1),X1)
      | k1_setfam_1(k2_tarski(X0,X1)) = X1 ) ),
    inference(factoring,[],[f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK6(X0,X1,X2),X1)
      | r2_hidden(sK6(X0,X1,X2),X2)
      | k1_setfam_1(k2_tarski(X0,X1)) = X2 ) ),
    inference(definition_unfolding,[],[f48,f38])).

fof(f38,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK6(X0,X1,X2),X1)
      | r2_hidden(sK6(X0,X1,X2),X2)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f776,plain,
    ( ~ r2_hidden(sK6(k2_struct_0(sK2),sK3,sK3),sK3)
    | spl7_31 ),
    inference(avatar_component_clause,[],[f774])).

fof(f781,plain,
    ( ~ spl7_31
    | spl7_32
    | ~ spl7_15 ),
    inference(avatar_split_clause,[],[f772,f145,f778,f774])).

fof(f145,plain,
    ( spl7_15
  <=> r1_tarski(sK3,k2_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f772,plain,
    ( sK3 = k1_setfam_1(k2_tarski(sK3,k2_struct_0(sK2)))
    | ~ r2_hidden(sK6(k2_struct_0(sK2),sK3,sK3),sK3)
    | ~ spl7_15 ),
    inference(forward_demodulation,[],[f771,f37])).

fof(f771,plain,
    ( sK3 = k1_setfam_1(k2_tarski(k2_struct_0(sK2),sK3))
    | ~ r2_hidden(sK6(k2_struct_0(sK2),sK3,sK3),sK3)
    | ~ spl7_15 ),
    inference(duplicate_literal_removal,[],[f762])).

fof(f762,plain,
    ( sK3 = k1_setfam_1(k2_tarski(k2_struct_0(sK2),sK3))
    | ~ r2_hidden(sK6(k2_struct_0(sK2),sK3,sK3),sK3)
    | ~ r2_hidden(sK6(k2_struct_0(sK2),sK3,sK3),sK3)
    | sK3 = k1_setfam_1(k2_tarski(k2_struct_0(sK2),sK3))
    | ~ spl7_15 ),
    inference(resolution,[],[f570,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK6(X0,X1,X2),X0)
      | ~ r2_hidden(sK6(X0,X1,X2),X1)
      | ~ r2_hidden(sK6(X0,X1,X2),X2)
      | k1_setfam_1(k2_tarski(X0,X1)) = X2 ) ),
    inference(definition_unfolding,[],[f46,f38])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK6(X0,X1,X2),X0)
      | ~ r2_hidden(sK6(X0,X1,X2),X1)
      | ~ r2_hidden(sK6(X0,X1,X2),X2)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f570,plain,
    ( ! [X11] :
        ( r2_hidden(sK6(X11,sK3,sK3),k2_struct_0(sK2))
        | sK3 = k1_setfam_1(k2_tarski(X11,sK3)) )
    | ~ spl7_15 ),
    inference(resolution,[],[f250,f147])).

fof(f147,plain,
    ( r1_tarski(sK3,k2_struct_0(sK2))
    | ~ spl7_15 ),
    inference(avatar_component_clause,[],[f145])).

fof(f250,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_tarski(X4,X5)
      | r2_hidden(sK6(X3,X4,X4),X5)
      | k1_setfam_1(k2_tarski(X3,X4)) = X4 ) ),
    inference(resolution,[],[f178,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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

fof(f248,plain,
    ( ~ spl7_1
    | spl7_19
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f244,f127,f103,f81,f246,f66])).

fof(f66,plain,
    ( spl7_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f81,plain,
    ( spl7_4
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f103,plain,
    ( spl7_8
  <=> u1_struct_0(sK0) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f127,plain,
    ( spl7_12
  <=> u1_struct_0(sK2) = k2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f244,plain,
    ( ! [X0] :
        ( v4_pre_topc(k1_setfam_1(k2_tarski(X0,k2_struct_0(sK2))),sK2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(k1_setfam_1(k2_tarski(X0,k2_struct_0(sK2))),k1_zfmisc_1(k2_struct_0(sK2)))
        | ~ l1_pre_topc(sK0)
        | ~ v4_pre_topc(X0,sK0) )
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_12 ),
    inference(forward_demodulation,[],[f243,f168])).

fof(f168,plain,(
    ! [X2,X3] : k9_subset_1(X2,X3,X2) = k1_setfam_1(k2_tarski(X3,X2)) ),
    inference(resolution,[],[f54,f154])).

fof(f154,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(resolution,[],[f152,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f152,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(duplicate_literal_removal,[],[f151])).

fof(f151,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f41,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) ) ),
    inference(definition_unfolding,[],[f44,f38])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f243,plain,
    ( ! [X0] :
        ( v4_pre_topc(k9_subset_1(k2_struct_0(sK2),X0,k2_struct_0(sK2)),sK2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(k1_setfam_1(k2_tarski(X0,k2_struct_0(sK2))),k1_zfmisc_1(k2_struct_0(sK2)))
        | ~ l1_pre_topc(sK0)
        | ~ v4_pre_topc(X0,sK0) )
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_12 ),
    inference(forward_demodulation,[],[f242,f129])).

fof(f129,plain,
    ( u1_struct_0(sK2) = k2_struct_0(sK2)
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f127])).

fof(f242,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(k1_setfam_1(k2_tarski(X0,k2_struct_0(sK2))),k1_zfmisc_1(k2_struct_0(sK2)))
        | ~ l1_pre_topc(sK0)
        | ~ v4_pre_topc(X0,sK0)
        | v4_pre_topc(k9_subset_1(u1_struct_0(sK2),X0,k2_struct_0(sK2)),sK2) )
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_12 ),
    inference(forward_demodulation,[],[f241,f105])).

fof(f105,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f103])).

fof(f241,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k1_setfam_1(k2_tarski(X0,k2_struct_0(sK2))),k1_zfmisc_1(k2_struct_0(sK2)))
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v4_pre_topc(X0,sK0)
        | v4_pre_topc(k9_subset_1(u1_struct_0(sK2),X0,k2_struct_0(sK2)),sK2) )
    | ~ spl7_4
    | ~ spl7_12 ),
    inference(forward_demodulation,[],[f240,f168])).

fof(f240,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k9_subset_1(k2_struct_0(sK2),X0,k2_struct_0(sK2)),k1_zfmisc_1(k2_struct_0(sK2)))
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v4_pre_topc(X0,sK0)
        | v4_pre_topc(k9_subset_1(u1_struct_0(sK2),X0,k2_struct_0(sK2)),sK2) )
    | ~ spl7_4
    | ~ spl7_12 ),
    inference(forward_demodulation,[],[f239,f129])).

fof(f239,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK2),X0,k2_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v4_pre_topc(X0,sK0)
        | v4_pre_topc(k9_subset_1(u1_struct_0(sK2),X0,k2_struct_0(sK2)),sK2) )
    | ~ spl7_4 ),
    inference(resolution,[],[f61,f83])).

fof(f83,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f81])).

fof(f61,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X3,X0)
      | v4_pre_topc(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),X1) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X3,X0)
      | k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
      | v4_pre_topc(X2,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_pre_topc)).

fof(f148,plain,
    ( spl7_15
    | ~ spl7_13 ),
    inference(avatar_split_clause,[],[f138,f133,f145])).

fof(f138,plain,
    ( r1_tarski(sK3,k2_struct_0(sK2))
    | ~ spl7_13 ),
    inference(resolution,[],[f43,f135])).

fof(f135,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK2)))
    | ~ spl7_13 ),
    inference(avatar_component_clause,[],[f133])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f136,plain,
    ( spl7_13
    | ~ spl7_6
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f131,f127,f91,f133])).

fof(f91,plain,
    ( spl7_6
  <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f131,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK2)))
    | ~ spl7_6
    | ~ spl7_12 ),
    inference(backward_demodulation,[],[f93,f129])).

fof(f93,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f91])).

fof(f130,plain,
    ( spl7_12
    | ~ spl7_11 ),
    inference(avatar_split_clause,[],[f125,f121,f127])).

fof(f121,plain,
    ( spl7_11
  <=> l1_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f125,plain,
    ( u1_struct_0(sK2) = k2_struct_0(sK2)
    | ~ spl7_11 ),
    inference(resolution,[],[f123,f30])).

fof(f30,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f123,plain,
    ( l1_struct_0(sK2)
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f121])).

fof(f124,plain,
    ( spl7_11
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f119,f115,f121])).

fof(f115,plain,
    ( spl7_10
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f119,plain,
    ( l1_struct_0(sK2)
    | ~ spl7_10 ),
    inference(resolution,[],[f117,f31])).

fof(f31,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f117,plain,
    ( l1_pre_topc(sK2)
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f115])).

fof(f118,plain,
    ( spl7_10
    | ~ spl7_1
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f113,f81,f66,f115])).

fof(f113,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK2)
    | ~ spl7_4 ),
    inference(resolution,[],[f32,f83])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f112,plain,
    ( spl7_9
    | ~ spl7_2
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f107,f103,f71,f109])).

fof(f71,plain,
    ( spl7_2
  <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f107,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl7_2
    | ~ spl7_8 ),
    inference(backward_demodulation,[],[f73,f105])).

fof(f73,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f71])).

fof(f106,plain,
    ( spl7_8
    | ~ spl7_7 ),
    inference(avatar_split_clause,[],[f101,f97,f103])).

fof(f97,plain,
    ( spl7_7
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f101,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl7_7 ),
    inference(resolution,[],[f30,f99])).

fof(f99,plain,
    ( l1_struct_0(sK0)
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f97])).

fof(f100,plain,
    ( spl7_7
    | ~ spl7_1 ),
    inference(avatar_split_clause,[],[f95,f66,f97])).

fof(f95,plain,
    ( l1_struct_0(sK0)
    | ~ spl7_1 ),
    inference(resolution,[],[f31,f68])).

fof(f68,plain,
    ( l1_pre_topc(sK0)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f66])).

fof(f94,plain,(
    spl7_6 ),
    inference(avatar_split_clause,[],[f23,f91])).

fof(f23,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_tops_2)).

fof(f89,plain,(
    ~ spl7_5 ),
    inference(avatar_split_clause,[],[f25,f86])).

fof(f25,plain,(
    ~ v4_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f84,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f26,f81])).

fof(f26,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f79,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f53,f76])).

fof(f53,plain,(
    v4_pre_topc(sK3,sK0) ),
    inference(definition_unfolding,[],[f27,f24])).

fof(f24,plain,(
    sK1 = sK3 ),
    inference(cnf_transformation,[],[f15])).

fof(f27,plain,(
    v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f74,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f52,f71])).

fof(f52,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(definition_unfolding,[],[f28,f24])).

fof(f28,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f15])).

fof(f69,plain,(
    spl7_1 ),
    inference(avatar_split_clause,[],[f29,f66])).

fof(f29,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:44:31 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.50  % (15213)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.50  % (15202)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.50  % (15205)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.51  % (15217)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.51  % (15197)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.51  % (15213)Refutation not found, incomplete strategy% (15213)------------------------------
% 0.20/0.51  % (15213)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (15213)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (15213)Memory used [KB]: 10746
% 0.20/0.51  % (15209)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.51  % (15213)Time elapsed: 0.057 s
% 0.20/0.51  % (15213)------------------------------
% 0.20/0.51  % (15213)------------------------------
% 0.20/0.51  % (15195)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (15191)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.53  % (15194)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.53  % (15208)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.53  % (15218)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.29/0.53  % (15201)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.29/0.53  % (15193)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.29/0.53  % (15220)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.29/0.54  % (15195)Refutation not found, incomplete strategy% (15195)------------------------------
% 1.29/0.54  % (15195)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.54  % (15219)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.29/0.54  % (15196)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.29/0.54  % (15217)Refutation not found, incomplete strategy% (15217)------------------------------
% 1.29/0.54  % (15217)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.54  % (15208)Refutation not found, incomplete strategy% (15208)------------------------------
% 1.29/0.54  % (15208)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.54  % (15208)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.54  
% 1.29/0.54  % (15208)Memory used [KB]: 10618
% 1.29/0.54  % (15208)Time elapsed: 0.132 s
% 1.29/0.54  % (15208)------------------------------
% 1.29/0.54  % (15208)------------------------------
% 1.29/0.54  % (15217)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.54  % (15192)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.29/0.54  
% 1.29/0.54  % (15217)Memory used [KB]: 10746
% 1.29/0.54  % (15217)Time elapsed: 0.117 s
% 1.29/0.54  % (15217)------------------------------
% 1.29/0.54  % (15217)------------------------------
% 1.29/0.54  % (15214)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.29/0.54  % (15193)Refutation not found, incomplete strategy% (15193)------------------------------
% 1.29/0.54  % (15193)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.54  % (15193)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.54  
% 1.29/0.54  % (15193)Memory used [KB]: 10874
% 1.29/0.54  % (15193)Time elapsed: 0.129 s
% 1.29/0.54  % (15193)------------------------------
% 1.29/0.54  % (15193)------------------------------
% 1.29/0.54  % (15200)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.29/0.54  % (15201)Refutation not found, incomplete strategy% (15201)------------------------------
% 1.29/0.54  % (15201)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.54  % (15216)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.29/0.54  % (15195)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.54  
% 1.29/0.54  % (15195)Memory used [KB]: 6268
% 1.29/0.54  % (15195)Time elapsed: 0.129 s
% 1.29/0.54  % (15195)------------------------------
% 1.29/0.54  % (15195)------------------------------
% 1.29/0.54  % (15199)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.29/0.54  % (15212)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.29/0.54  % (15210)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.29/0.54  % (15211)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.29/0.55  % (15215)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.29/0.55  % (15201)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.55  
% 1.29/0.55  % (15201)Memory used [KB]: 10746
% 1.29/0.55  % (15201)Time elapsed: 0.134 s
% 1.29/0.55  % (15201)------------------------------
% 1.29/0.55  % (15201)------------------------------
% 1.29/0.55  % (15206)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.29/0.55  % (15204)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.29/0.55  % (15203)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.29/0.55  % (15207)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.29/0.55  % (15199)Refutation not found, incomplete strategy% (15199)------------------------------
% 1.29/0.55  % (15199)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.55  % (15199)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.55  
% 1.29/0.55  % (15199)Memory used [KB]: 10746
% 1.29/0.55  % (15199)Time elapsed: 0.147 s
% 1.29/0.55  % (15199)------------------------------
% 1.29/0.55  % (15199)------------------------------
% 1.29/0.55  % (15198)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.53/0.57  % (15200)Refutation not found, incomplete strategy% (15200)------------------------------
% 1.53/0.57  % (15200)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.57  % (15200)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.57  
% 1.53/0.57  % (15200)Memory used [KB]: 10874
% 1.53/0.57  % (15200)Time elapsed: 0.156 s
% 1.53/0.57  % (15200)------------------------------
% 1.53/0.57  % (15200)------------------------------
% 1.53/0.61  % (15207)Refutation found. Thanks to Tanya!
% 1.53/0.61  % SZS status Theorem for theBenchmark
% 1.53/0.62  % SZS output start Proof for theBenchmark
% 1.53/0.62  fof(f866,plain,(
% 1.53/0.62    $false),
% 1.53/0.62    inference(avatar_sat_refutation,[],[f69,f74,f79,f84,f89,f94,f100,f106,f112,f118,f124,f130,f136,f148,f248,f781,f787,f865])).
% 1.53/0.62  fof(f865,plain,(
% 1.53/0.62    ~spl7_9 | spl7_5 | ~spl7_3 | ~spl7_13 | ~spl7_19 | ~spl7_32),
% 1.53/0.62    inference(avatar_split_clause,[],[f844,f778,f246,f133,f76,f86,f109])).
% 1.53/0.62  fof(f109,plain,(
% 1.53/0.62    spl7_9 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK0)))),
% 1.53/0.62    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 1.53/0.62  fof(f86,plain,(
% 1.53/0.62    spl7_5 <=> v4_pre_topc(sK3,sK2)),
% 1.53/0.62    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 1.53/0.62  fof(f76,plain,(
% 1.53/0.62    spl7_3 <=> v4_pre_topc(sK3,sK0)),
% 1.53/0.62    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 1.53/0.62  fof(f133,plain,(
% 1.53/0.62    spl7_13 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK2)))),
% 1.53/0.62    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 1.53/0.62  fof(f246,plain,(
% 1.53/0.62    spl7_19 <=> ! [X0] : (v4_pre_topc(k1_setfam_1(k2_tarski(X0,k2_struct_0(sK2))),sK2) | ~v4_pre_topc(X0,sK0) | ~m1_subset_1(k1_setfam_1(k2_tarski(X0,k2_struct_0(sK2))),k1_zfmisc_1(k2_struct_0(sK2))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))))),
% 1.53/0.62    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).
% 1.53/0.62  fof(f778,plain,(
% 1.53/0.62    spl7_32 <=> sK3 = k1_setfam_1(k2_tarski(sK3,k2_struct_0(sK2)))),
% 1.53/0.62    introduced(avatar_definition,[new_symbols(naming,[spl7_32])])).
% 1.53/0.62  fof(f844,plain,(
% 1.53/0.62    ~m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK2))) | ~v4_pre_topc(sK3,sK0) | v4_pre_topc(sK3,sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK0))) | (~spl7_19 | ~spl7_32)),
% 1.53/0.62    inference(superposition,[],[f247,f780])).
% 1.53/0.62  fof(f780,plain,(
% 1.53/0.62    sK3 = k1_setfam_1(k2_tarski(sK3,k2_struct_0(sK2))) | ~spl7_32),
% 1.53/0.62    inference(avatar_component_clause,[],[f778])).
% 1.53/0.62  fof(f247,plain,(
% 1.53/0.62    ( ! [X0] : (~m1_subset_1(k1_setfam_1(k2_tarski(X0,k2_struct_0(sK2))),k1_zfmisc_1(k2_struct_0(sK2))) | ~v4_pre_topc(X0,sK0) | v4_pre_topc(k1_setfam_1(k2_tarski(X0,k2_struct_0(sK2))),sK2) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))) ) | ~spl7_19),
% 1.53/0.62    inference(avatar_component_clause,[],[f246])).
% 1.53/0.62  fof(f787,plain,(
% 1.53/0.62    spl7_32 | spl7_31),
% 1.53/0.62    inference(avatar_split_clause,[],[f786,f774,f778])).
% 1.53/0.62  fof(f774,plain,(
% 1.53/0.62    spl7_31 <=> r2_hidden(sK6(k2_struct_0(sK2),sK3,sK3),sK3)),
% 1.53/0.62    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).
% 1.53/0.62  fof(f786,plain,(
% 1.53/0.62    sK3 = k1_setfam_1(k2_tarski(sK3,k2_struct_0(sK2))) | spl7_31),
% 1.53/0.62    inference(forward_demodulation,[],[f782,f37])).
% 1.53/0.62  fof(f37,plain,(
% 1.53/0.62    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.53/0.62    inference(cnf_transformation,[],[f3])).
% 1.53/0.62  fof(f3,axiom,(
% 1.53/0.62    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.53/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.53/0.62  fof(f782,plain,(
% 1.53/0.62    sK3 = k1_setfam_1(k2_tarski(k2_struct_0(sK2),sK3)) | spl7_31),
% 1.53/0.62    inference(resolution,[],[f776,f178])).
% 1.53/0.62  fof(f178,plain,(
% 1.53/0.62    ( ! [X0,X1] : (r2_hidden(sK6(X0,X1,X1),X1) | k1_setfam_1(k2_tarski(X0,X1)) = X1) )),
% 1.53/0.62    inference(factoring,[],[f58])).
% 1.53/0.62  fof(f58,plain,(
% 1.53/0.62    ( ! [X2,X0,X1] : (r2_hidden(sK6(X0,X1,X2),X1) | r2_hidden(sK6(X0,X1,X2),X2) | k1_setfam_1(k2_tarski(X0,X1)) = X2) )),
% 1.53/0.62    inference(definition_unfolding,[],[f48,f38])).
% 1.53/0.62  fof(f38,plain,(
% 1.53/0.62    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.53/0.62    inference(cnf_transformation,[],[f6])).
% 1.53/0.62  fof(f6,axiom,(
% 1.53/0.62    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.53/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.53/0.62  fof(f48,plain,(
% 1.53/0.62    ( ! [X2,X0,X1] : (r2_hidden(sK6(X0,X1,X2),X1) | r2_hidden(sK6(X0,X1,X2),X2) | k3_xboole_0(X0,X1) = X2) )),
% 1.53/0.62    inference(cnf_transformation,[],[f2])).
% 1.53/0.62  fof(f2,axiom,(
% 1.53/0.62    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.53/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).
% 1.53/0.62  fof(f776,plain,(
% 1.53/0.62    ~r2_hidden(sK6(k2_struct_0(sK2),sK3,sK3),sK3) | spl7_31),
% 1.53/0.62    inference(avatar_component_clause,[],[f774])).
% 1.53/0.62  fof(f781,plain,(
% 1.53/0.62    ~spl7_31 | spl7_32 | ~spl7_15),
% 1.53/0.62    inference(avatar_split_clause,[],[f772,f145,f778,f774])).
% 1.53/0.62  fof(f145,plain,(
% 1.53/0.62    spl7_15 <=> r1_tarski(sK3,k2_struct_0(sK2))),
% 1.53/0.62    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 1.53/0.62  fof(f772,plain,(
% 1.53/0.62    sK3 = k1_setfam_1(k2_tarski(sK3,k2_struct_0(sK2))) | ~r2_hidden(sK6(k2_struct_0(sK2),sK3,sK3),sK3) | ~spl7_15),
% 1.53/0.62    inference(forward_demodulation,[],[f771,f37])).
% 1.53/0.62  fof(f771,plain,(
% 1.53/0.62    sK3 = k1_setfam_1(k2_tarski(k2_struct_0(sK2),sK3)) | ~r2_hidden(sK6(k2_struct_0(sK2),sK3,sK3),sK3) | ~spl7_15),
% 1.53/0.62    inference(duplicate_literal_removal,[],[f762])).
% 1.53/0.62  fof(f762,plain,(
% 1.53/0.62    sK3 = k1_setfam_1(k2_tarski(k2_struct_0(sK2),sK3)) | ~r2_hidden(sK6(k2_struct_0(sK2),sK3,sK3),sK3) | ~r2_hidden(sK6(k2_struct_0(sK2),sK3,sK3),sK3) | sK3 = k1_setfam_1(k2_tarski(k2_struct_0(sK2),sK3)) | ~spl7_15),
% 1.53/0.62    inference(resolution,[],[f570,f60])).
% 1.53/0.62  fof(f60,plain,(
% 1.53/0.62    ( ! [X2,X0,X1] : (~r2_hidden(sK6(X0,X1,X2),X0) | ~r2_hidden(sK6(X0,X1,X2),X1) | ~r2_hidden(sK6(X0,X1,X2),X2) | k1_setfam_1(k2_tarski(X0,X1)) = X2) )),
% 1.53/0.62    inference(definition_unfolding,[],[f46,f38])).
% 1.53/0.62  fof(f46,plain,(
% 1.53/0.62    ( ! [X2,X0,X1] : (~r2_hidden(sK6(X0,X1,X2),X0) | ~r2_hidden(sK6(X0,X1,X2),X1) | ~r2_hidden(sK6(X0,X1,X2),X2) | k3_xboole_0(X0,X1) = X2) )),
% 1.53/0.62    inference(cnf_transformation,[],[f2])).
% 1.53/0.62  fof(f570,plain,(
% 1.53/0.62    ( ! [X11] : (r2_hidden(sK6(X11,sK3,sK3),k2_struct_0(sK2)) | sK3 = k1_setfam_1(k2_tarski(X11,sK3))) ) | ~spl7_15),
% 1.53/0.62    inference(resolution,[],[f250,f147])).
% 1.53/0.62  fof(f147,plain,(
% 1.53/0.62    r1_tarski(sK3,k2_struct_0(sK2)) | ~spl7_15),
% 1.53/0.62    inference(avatar_component_clause,[],[f145])).
% 1.53/0.62  fof(f250,plain,(
% 1.53/0.62    ( ! [X4,X5,X3] : (~r1_tarski(X4,X5) | r2_hidden(sK6(X3,X4,X4),X5) | k1_setfam_1(k2_tarski(X3,X4)) = X4) )),
% 1.53/0.62    inference(resolution,[],[f178,f39])).
% 1.53/0.62  fof(f39,plain,(
% 1.53/0.62    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 1.53/0.62    inference(cnf_transformation,[],[f20])).
% 1.53/0.62  fof(f20,plain,(
% 1.53/0.62    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.53/0.62    inference(ennf_transformation,[],[f1])).
% 1.53/0.62  fof(f1,axiom,(
% 1.53/0.62    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.53/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.53/0.62  fof(f248,plain,(
% 1.53/0.62    ~spl7_1 | spl7_19 | ~spl7_4 | ~spl7_8 | ~spl7_12),
% 1.53/0.62    inference(avatar_split_clause,[],[f244,f127,f103,f81,f246,f66])).
% 1.53/0.62  fof(f66,plain,(
% 1.53/0.62    spl7_1 <=> l1_pre_topc(sK0)),
% 1.53/0.62    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 1.53/0.62  fof(f81,plain,(
% 1.53/0.62    spl7_4 <=> m1_pre_topc(sK2,sK0)),
% 1.53/0.62    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 1.53/0.62  fof(f103,plain,(
% 1.53/0.62    spl7_8 <=> u1_struct_0(sK0) = k2_struct_0(sK0)),
% 1.53/0.62    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 1.53/0.62  fof(f127,plain,(
% 1.53/0.62    spl7_12 <=> u1_struct_0(sK2) = k2_struct_0(sK2)),
% 1.53/0.62    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 1.53/0.62  fof(f244,plain,(
% 1.53/0.62    ( ! [X0] : (v4_pre_topc(k1_setfam_1(k2_tarski(X0,k2_struct_0(sK2))),sK2) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(k1_setfam_1(k2_tarski(X0,k2_struct_0(sK2))),k1_zfmisc_1(k2_struct_0(sK2))) | ~l1_pre_topc(sK0) | ~v4_pre_topc(X0,sK0)) ) | (~spl7_4 | ~spl7_8 | ~spl7_12)),
% 1.53/0.62    inference(forward_demodulation,[],[f243,f168])).
% 1.53/0.62  fof(f168,plain,(
% 1.53/0.62    ( ! [X2,X3] : (k9_subset_1(X2,X3,X2) = k1_setfam_1(k2_tarski(X3,X2))) )),
% 1.53/0.62    inference(resolution,[],[f54,f154])).
% 1.53/0.62  fof(f154,plain,(
% 1.53/0.62    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 1.53/0.62    inference(resolution,[],[f152,f42])).
% 1.53/0.62  fof(f42,plain,(
% 1.53/0.62    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.53/0.62    inference(cnf_transformation,[],[f7])).
% 1.53/0.62  fof(f7,axiom,(
% 1.53/0.62    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.53/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.53/0.62  fof(f152,plain,(
% 1.53/0.62    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 1.53/0.62    inference(duplicate_literal_removal,[],[f151])).
% 1.53/0.62  fof(f151,plain,(
% 1.53/0.62    ( ! [X0] : (r1_tarski(X0,X0) | r1_tarski(X0,X0)) )),
% 1.53/0.62    inference(resolution,[],[f41,f40])).
% 1.53/0.62  fof(f40,plain,(
% 1.53/0.62    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.53/0.62    inference(cnf_transformation,[],[f20])).
% 1.53/0.62  fof(f41,plain,(
% 1.53/0.62    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.53/0.62    inference(cnf_transformation,[],[f20])).
% 1.53/0.62  fof(f54,plain,(
% 1.53/0.62    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))) )),
% 1.53/0.62    inference(definition_unfolding,[],[f44,f38])).
% 1.53/0.62  fof(f44,plain,(
% 1.53/0.62    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)) )),
% 1.53/0.62    inference(cnf_transformation,[],[f21])).
% 1.53/0.62  fof(f21,plain,(
% 1.53/0.62    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.53/0.62    inference(ennf_transformation,[],[f5])).
% 1.53/0.62  fof(f5,axiom,(
% 1.53/0.62    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 1.53/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 1.53/0.62  fof(f243,plain,(
% 1.53/0.62    ( ! [X0] : (v4_pre_topc(k9_subset_1(k2_struct_0(sK2),X0,k2_struct_0(sK2)),sK2) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(k1_setfam_1(k2_tarski(X0,k2_struct_0(sK2))),k1_zfmisc_1(k2_struct_0(sK2))) | ~l1_pre_topc(sK0) | ~v4_pre_topc(X0,sK0)) ) | (~spl7_4 | ~spl7_8 | ~spl7_12)),
% 1.53/0.62    inference(forward_demodulation,[],[f242,f129])).
% 1.53/0.62  fof(f129,plain,(
% 1.53/0.62    u1_struct_0(sK2) = k2_struct_0(sK2) | ~spl7_12),
% 1.53/0.62    inference(avatar_component_clause,[],[f127])).
% 1.53/0.62  fof(f242,plain,(
% 1.53/0.62    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(k1_setfam_1(k2_tarski(X0,k2_struct_0(sK2))),k1_zfmisc_1(k2_struct_0(sK2))) | ~l1_pre_topc(sK0) | ~v4_pre_topc(X0,sK0) | v4_pre_topc(k9_subset_1(u1_struct_0(sK2),X0,k2_struct_0(sK2)),sK2)) ) | (~spl7_4 | ~spl7_8 | ~spl7_12)),
% 1.53/0.62    inference(forward_demodulation,[],[f241,f105])).
% 1.53/0.62  fof(f105,plain,(
% 1.53/0.62    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl7_8),
% 1.53/0.62    inference(avatar_component_clause,[],[f103])).
% 1.53/0.62  fof(f241,plain,(
% 1.53/0.62    ( ! [X0] : (~m1_subset_1(k1_setfam_1(k2_tarski(X0,k2_struct_0(sK2))),k1_zfmisc_1(k2_struct_0(sK2))) | ~l1_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(X0,sK0) | v4_pre_topc(k9_subset_1(u1_struct_0(sK2),X0,k2_struct_0(sK2)),sK2)) ) | (~spl7_4 | ~spl7_12)),
% 1.53/0.62    inference(forward_demodulation,[],[f240,f168])).
% 1.53/0.62  fof(f240,plain,(
% 1.53/0.62    ( ! [X0] : (~m1_subset_1(k9_subset_1(k2_struct_0(sK2),X0,k2_struct_0(sK2)),k1_zfmisc_1(k2_struct_0(sK2))) | ~l1_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(X0,sK0) | v4_pre_topc(k9_subset_1(u1_struct_0(sK2),X0,k2_struct_0(sK2)),sK2)) ) | (~spl7_4 | ~spl7_12)),
% 1.53/0.62    inference(forward_demodulation,[],[f239,f129])).
% 1.53/0.62  fof(f239,plain,(
% 1.53/0.62    ( ! [X0] : (~l1_pre_topc(sK0) | ~m1_subset_1(k9_subset_1(u1_struct_0(sK2),X0,k2_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK2))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(X0,sK0) | v4_pre_topc(k9_subset_1(u1_struct_0(sK2),X0,k2_struct_0(sK2)),sK2)) ) | ~spl7_4),
% 1.53/0.62    inference(resolution,[],[f61,f83])).
% 1.53/0.62  fof(f83,plain,(
% 1.53/0.62    m1_pre_topc(sK2,sK0) | ~spl7_4),
% 1.53/0.62    inference(avatar_component_clause,[],[f81])).
% 1.53/0.62  fof(f61,plain,(
% 1.53/0.62    ( ! [X0,X3,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~m1_subset_1(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X3,X0) | v4_pre_topc(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),X1)) )),
% 1.53/0.62    inference(equality_resolution,[],[f36])).
% 1.53/0.62  fof(f36,plain,(
% 1.53/0.62    ( ! [X2,X0,X3,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X3,X0) | k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | v4_pre_topc(X2,X1)) )),
% 1.53/0.62    inference(cnf_transformation,[],[f19])).
% 1.53/0.62  fof(f19,plain,(
% 1.53/0.62    ! [X0] : (! [X1] : (! [X2] : ((v4_pre_topc(X2,X1) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.53/0.62    inference(ennf_transformation,[],[f11])).
% 1.53/0.62  fof(f11,axiom,(
% 1.53/0.62    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => (v4_pre_topc(X2,X1) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))))))),
% 1.53/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_pre_topc)).
% 1.53/0.62  fof(f148,plain,(
% 1.53/0.62    spl7_15 | ~spl7_13),
% 1.53/0.62    inference(avatar_split_clause,[],[f138,f133,f145])).
% 1.53/0.62  fof(f138,plain,(
% 1.53/0.62    r1_tarski(sK3,k2_struct_0(sK2)) | ~spl7_13),
% 1.53/0.62    inference(resolution,[],[f43,f135])).
% 1.53/0.62  fof(f135,plain,(
% 1.53/0.62    m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK2))) | ~spl7_13),
% 1.53/0.62    inference(avatar_component_clause,[],[f133])).
% 1.53/0.62  fof(f43,plain,(
% 1.53/0.62    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.53/0.62    inference(cnf_transformation,[],[f7])).
% 1.53/0.62  fof(f136,plain,(
% 1.53/0.62    spl7_13 | ~spl7_6 | ~spl7_12),
% 1.53/0.62    inference(avatar_split_clause,[],[f131,f127,f91,f133])).
% 1.53/0.62  fof(f91,plain,(
% 1.53/0.62    spl7_6 <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))),
% 1.53/0.62    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 1.53/0.62  fof(f131,plain,(
% 1.53/0.62    m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK2))) | (~spl7_6 | ~spl7_12)),
% 1.53/0.62    inference(backward_demodulation,[],[f93,f129])).
% 1.53/0.62  fof(f93,plain,(
% 1.53/0.62    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) | ~spl7_6),
% 1.53/0.62    inference(avatar_component_clause,[],[f91])).
% 1.53/0.62  fof(f130,plain,(
% 1.53/0.62    spl7_12 | ~spl7_11),
% 1.53/0.62    inference(avatar_split_clause,[],[f125,f121,f127])).
% 1.53/0.62  fof(f121,plain,(
% 1.53/0.62    spl7_11 <=> l1_struct_0(sK2)),
% 1.53/0.62    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 1.53/0.62  fof(f125,plain,(
% 1.53/0.62    u1_struct_0(sK2) = k2_struct_0(sK2) | ~spl7_11),
% 1.53/0.62    inference(resolution,[],[f123,f30])).
% 1.53/0.62  fof(f30,plain,(
% 1.53/0.62    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 1.53/0.62    inference(cnf_transformation,[],[f16])).
% 1.53/0.62  fof(f16,plain,(
% 1.53/0.62    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 1.53/0.62    inference(ennf_transformation,[],[f8])).
% 1.53/0.62  fof(f8,axiom,(
% 1.53/0.62    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 1.53/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 1.53/0.62  fof(f123,plain,(
% 1.53/0.62    l1_struct_0(sK2) | ~spl7_11),
% 1.53/0.62    inference(avatar_component_clause,[],[f121])).
% 1.53/0.62  fof(f124,plain,(
% 1.53/0.62    spl7_11 | ~spl7_10),
% 1.53/0.62    inference(avatar_split_clause,[],[f119,f115,f121])).
% 1.53/0.62  fof(f115,plain,(
% 1.53/0.62    spl7_10 <=> l1_pre_topc(sK2)),
% 1.53/0.62    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 1.53/0.62  fof(f119,plain,(
% 1.53/0.62    l1_struct_0(sK2) | ~spl7_10),
% 1.53/0.62    inference(resolution,[],[f117,f31])).
% 1.53/0.62  fof(f31,plain,(
% 1.53/0.62    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 1.53/0.62    inference(cnf_transformation,[],[f17])).
% 1.53/0.62  fof(f17,plain,(
% 1.53/0.62    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.53/0.62    inference(ennf_transformation,[],[f9])).
% 1.53/0.62  fof(f9,axiom,(
% 1.53/0.62    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.53/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 1.53/0.62  fof(f117,plain,(
% 1.53/0.62    l1_pre_topc(sK2) | ~spl7_10),
% 1.53/0.62    inference(avatar_component_clause,[],[f115])).
% 1.53/0.62  fof(f118,plain,(
% 1.53/0.62    spl7_10 | ~spl7_1 | ~spl7_4),
% 1.53/0.62    inference(avatar_split_clause,[],[f113,f81,f66,f115])).
% 1.53/0.62  fof(f113,plain,(
% 1.53/0.62    ~l1_pre_topc(sK0) | l1_pre_topc(sK2) | ~spl7_4),
% 1.53/0.62    inference(resolution,[],[f32,f83])).
% 1.53/0.62  fof(f32,plain,(
% 1.53/0.62    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | l1_pre_topc(X1)) )),
% 1.53/0.62    inference(cnf_transformation,[],[f18])).
% 1.53/0.62  fof(f18,plain,(
% 1.53/0.62    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.53/0.62    inference(ennf_transformation,[],[f10])).
% 1.53/0.62  fof(f10,axiom,(
% 1.53/0.62    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.53/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 1.53/0.62  fof(f112,plain,(
% 1.53/0.62    spl7_9 | ~spl7_2 | ~spl7_8),
% 1.53/0.62    inference(avatar_split_clause,[],[f107,f103,f71,f109])).
% 1.53/0.62  fof(f71,plain,(
% 1.53/0.62    spl7_2 <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.53/0.62    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 1.53/0.62  fof(f107,plain,(
% 1.53/0.62    m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK0))) | (~spl7_2 | ~spl7_8)),
% 1.53/0.62    inference(backward_demodulation,[],[f73,f105])).
% 1.53/0.62  fof(f73,plain,(
% 1.53/0.62    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl7_2),
% 1.53/0.62    inference(avatar_component_clause,[],[f71])).
% 1.53/0.62  fof(f106,plain,(
% 1.53/0.62    spl7_8 | ~spl7_7),
% 1.53/0.62    inference(avatar_split_clause,[],[f101,f97,f103])).
% 1.53/0.62  fof(f97,plain,(
% 1.53/0.62    spl7_7 <=> l1_struct_0(sK0)),
% 1.53/0.62    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 1.53/0.62  fof(f101,plain,(
% 1.53/0.62    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl7_7),
% 1.53/0.62    inference(resolution,[],[f30,f99])).
% 1.53/0.62  fof(f99,plain,(
% 1.53/0.62    l1_struct_0(sK0) | ~spl7_7),
% 1.53/0.62    inference(avatar_component_clause,[],[f97])).
% 1.53/0.62  fof(f100,plain,(
% 1.53/0.62    spl7_7 | ~spl7_1),
% 1.53/0.62    inference(avatar_split_clause,[],[f95,f66,f97])).
% 1.53/0.62  fof(f95,plain,(
% 1.53/0.62    l1_struct_0(sK0) | ~spl7_1),
% 1.53/0.62    inference(resolution,[],[f31,f68])).
% 1.53/0.62  fof(f68,plain,(
% 1.53/0.62    l1_pre_topc(sK0) | ~spl7_1),
% 1.53/0.62    inference(avatar_component_clause,[],[f66])).
% 1.53/0.62  fof(f94,plain,(
% 1.53/0.62    spl7_6),
% 1.53/0.62    inference(avatar_split_clause,[],[f23,f91])).
% 1.53/0.62  fof(f23,plain,(
% 1.53/0.62    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))),
% 1.53/0.62    inference(cnf_transformation,[],[f15])).
% 1.53/0.62  fof(f15,plain,(
% 1.53/0.62    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~v4_pre_topc(X3,X2) & X1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v4_pre_topc(X1,X0) & m1_pre_topc(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.53/0.62    inference(flattening,[],[f14])).
% 1.53/0.62  fof(f14,plain,(
% 1.53/0.62    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : ((~v4_pre_topc(X3,X2) & X1 = X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v4_pre_topc(X1,X0)) & m1_pre_topc(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.53/0.62    inference(ennf_transformation,[],[f13])).
% 1.53/0.62  fof(f13,negated_conjecture,(
% 1.53/0.62    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_pre_topc(X2,X0) => (v4_pre_topc(X1,X0) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) => (X1 = X3 => v4_pre_topc(X3,X2)))))))),
% 1.53/0.62    inference(negated_conjecture,[],[f12])).
% 1.53/0.62  fof(f12,conjecture,(
% 1.53/0.62    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_pre_topc(X2,X0) => (v4_pre_topc(X1,X0) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) => (X1 = X3 => v4_pre_topc(X3,X2)))))))),
% 1.53/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_tops_2)).
% 1.53/0.62  fof(f89,plain,(
% 1.53/0.62    ~spl7_5),
% 1.53/0.62    inference(avatar_split_clause,[],[f25,f86])).
% 1.53/0.62  fof(f25,plain,(
% 1.53/0.62    ~v4_pre_topc(sK3,sK2)),
% 1.53/0.62    inference(cnf_transformation,[],[f15])).
% 1.53/0.62  fof(f84,plain,(
% 1.53/0.62    spl7_4),
% 1.53/0.62    inference(avatar_split_clause,[],[f26,f81])).
% 1.53/0.62  fof(f26,plain,(
% 1.53/0.62    m1_pre_topc(sK2,sK0)),
% 1.53/0.62    inference(cnf_transformation,[],[f15])).
% 1.53/0.62  fof(f79,plain,(
% 1.53/0.62    spl7_3),
% 1.53/0.62    inference(avatar_split_clause,[],[f53,f76])).
% 1.53/0.62  fof(f53,plain,(
% 1.53/0.62    v4_pre_topc(sK3,sK0)),
% 1.53/0.62    inference(definition_unfolding,[],[f27,f24])).
% 1.53/0.62  fof(f24,plain,(
% 1.53/0.62    sK1 = sK3),
% 1.53/0.62    inference(cnf_transformation,[],[f15])).
% 1.53/0.62  fof(f27,plain,(
% 1.53/0.62    v4_pre_topc(sK1,sK0)),
% 1.53/0.62    inference(cnf_transformation,[],[f15])).
% 1.53/0.62  fof(f74,plain,(
% 1.53/0.62    spl7_2),
% 1.53/0.62    inference(avatar_split_clause,[],[f52,f71])).
% 1.53/0.62  fof(f52,plain,(
% 1.53/0.62    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.53/0.62    inference(definition_unfolding,[],[f28,f24])).
% 1.53/0.62  fof(f28,plain,(
% 1.53/0.62    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.53/0.62    inference(cnf_transformation,[],[f15])).
% 1.53/0.62  fof(f69,plain,(
% 1.53/0.62    spl7_1),
% 1.53/0.62    inference(avatar_split_clause,[],[f29,f66])).
% 1.53/0.62  fof(f29,plain,(
% 1.53/0.62    l1_pre_topc(sK0)),
% 1.53/0.62    inference(cnf_transformation,[],[f15])).
% 1.53/0.62  % SZS output end Proof for theBenchmark
% 1.53/0.62  % (15207)------------------------------
% 1.53/0.62  % (15207)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.62  % (15207)Termination reason: Refutation
% 1.53/0.62  
% 1.53/0.62  % (15207)Memory used [KB]: 11385
% 1.53/0.62  % (15207)Time elapsed: 0.191 s
% 1.53/0.62  % (15207)------------------------------
% 1.53/0.62  % (15207)------------------------------
% 1.53/0.63  % (15190)Success in time 0.255 s
%------------------------------------------------------------------------------
