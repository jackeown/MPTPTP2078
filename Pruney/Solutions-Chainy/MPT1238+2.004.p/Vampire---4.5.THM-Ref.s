%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:04 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 235 expanded)
%              Number of leaves         :   28 ( 101 expanded)
%              Depth                    :    8
%              Number of atoms          :  282 ( 651 expanded)
%              Number of equality atoms :    9 (  38 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f194,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f65,f81,f84,f91,f93,f97,f109,f125,f138,f140,f147,f159,f163,f177,f187,f191,f193])).

fof(f193,plain,(
    spl3_21 ),
    inference(avatar_contradiction_clause,[],[f192])).

fof(f192,plain,
    ( $false
    | spl3_21 ),
    inference(resolution,[],[f186,f46])).

fof(f46,plain,(
    r1_tarski(sK2,u1_struct_0(sK0)) ),
    inference(resolution,[],[f34,f27])).

fof(f27,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f22,f21,f20])).

fof(f20,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2)))
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X1),k1_tops_1(sK0,X2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),X1,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X1),k1_tops_1(sK0,X2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),X1,X2)))
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,X2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,X2)))
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,X2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,X2)))
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_tops_1)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f186,plain,
    ( ~ r1_tarski(sK2,u1_struct_0(sK0))
    | spl3_21 ),
    inference(avatar_component_clause,[],[f184])).

fof(f184,plain,
    ( spl3_21
  <=> r1_tarski(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f191,plain,(
    spl3_20 ),
    inference(avatar_contradiction_clause,[],[f190])).

fof(f190,plain,
    ( $false
    | spl3_20 ),
    inference(resolution,[],[f182,f45])).

fof(f45,plain,(
    r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(resolution,[],[f34,f26])).

fof(f26,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f23])).

fof(f182,plain,
    ( ~ r1_tarski(sK1,u1_struct_0(sK0))
    | spl3_20 ),
    inference(avatar_component_clause,[],[f180])).

fof(f180,plain,
    ( spl3_20
  <=> r1_tarski(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f187,plain,
    ( ~ spl3_20
    | ~ spl3_21
    | spl3_19 ),
    inference(avatar_split_clause,[],[f178,f174,f184,f180])).

fof(f174,plain,
    ( spl3_19
  <=> r1_tarski(k3_tarski(k2_tarski(sK1,sK2)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f178,plain,
    ( ~ r1_tarski(sK2,u1_struct_0(sK0))
    | ~ r1_tarski(sK1,u1_struct_0(sK0))
    | spl3_19 ),
    inference(resolution,[],[f176,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_tarski(k2_tarski(X0,X2)),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f36,f32])).

fof(f32,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

fof(f176,plain,
    ( ~ r1_tarski(k3_tarski(k2_tarski(sK1,sK2)),u1_struct_0(sK0))
    | spl3_19 ),
    inference(avatar_component_clause,[],[f174])).

fof(f177,plain,
    ( ~ spl3_4
    | ~ spl3_5
    | ~ spl3_19
    | spl3_11 ),
    inference(avatar_split_clause,[],[f172,f118,f174,f71,f67])).

fof(f67,plain,
    ( spl3_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f71,plain,
    ( spl3_5
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f118,plain,
    ( spl3_11
  <=> m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f172,plain,
    ( ~ r1_tarski(k3_tarski(k2_tarski(sK1,sK2)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_11 ),
    inference(superposition,[],[f165,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f37,f32])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f165,plain,
    ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),sK1,sK2),u1_struct_0(sK0))
    | spl3_11 ),
    inference(resolution,[],[f120,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f120,plain,
    ( ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_11 ),
    inference(avatar_component_clause,[],[f118])).

fof(f163,plain,(
    spl3_17 ),
    inference(avatar_contradiction_clause,[],[f162])).

fof(f162,plain,
    ( $false
    | spl3_17 ),
    inference(resolution,[],[f158,f41])).

fof(f41,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k2_tarski(X1,X0))) ),
    inference(superposition,[],[f38,f31])).

fof(f31,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f38,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f30,f32])).

fof(f30,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f158,plain,
    ( ~ r1_tarski(sK2,k3_tarski(k2_tarski(sK1,sK2)))
    | spl3_17 ),
    inference(avatar_component_clause,[],[f156])).

fof(f156,plain,
    ( spl3_17
  <=> r1_tarski(sK2,k3_tarski(k2_tarski(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f159,plain,
    ( ~ spl3_4
    | ~ spl3_5
    | ~ spl3_17
    | spl3_15 ),
    inference(avatar_split_clause,[],[f154,f144,f156,f71,f67])).

fof(f144,plain,
    ( spl3_15
  <=> r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f154,plain,
    ( ~ r1_tarski(sK2,k3_tarski(k2_tarski(sK1,sK2)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_15 ),
    inference(superposition,[],[f146,f40])).

fof(f146,plain,
    ( ~ r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
    | spl3_15 ),
    inference(avatar_component_clause,[],[f144])).

fof(f147,plain,
    ( ~ spl3_7
    | ~ spl3_5
    | ~ spl3_11
    | ~ spl3_15
    | spl3_9 ),
    inference(avatar_split_clause,[],[f141,f106,f144,f118,f71,f88])).

fof(f88,plain,
    ( spl3_7
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f106,plain,
    ( spl3_9
  <=> r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f141,plain,
    ( ~ r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl3_9 ),
    inference(resolution,[],[f108,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).

fof(f108,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | spl3_9 ),
    inference(avatar_component_clause,[],[f106])).

fof(f140,plain,(
    spl3_14 ),
    inference(avatar_contradiction_clause,[],[f139])).

fof(f139,plain,
    ( $false
    | spl3_14 ),
    inference(resolution,[],[f137,f38])).

fof(f137,plain,
    ( ~ r1_tarski(sK1,k3_tarski(k2_tarski(sK1,sK2)))
    | spl3_14 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl3_14
  <=> r1_tarski(sK1,k3_tarski(k2_tarski(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f138,plain,
    ( ~ spl3_4
    | ~ spl3_5
    | ~ spl3_14
    | spl3_12 ),
    inference(avatar_split_clause,[],[f133,f122,f135,f71,f67])).

fof(f122,plain,
    ( spl3_12
  <=> r1_tarski(sK1,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f133,plain,
    ( ~ r1_tarski(sK1,k3_tarski(k2_tarski(sK1,sK2)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_12 ),
    inference(superposition,[],[f124,f40])).

fof(f124,plain,
    ( ~ r1_tarski(sK1,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
    | spl3_12 ),
    inference(avatar_component_clause,[],[f122])).

fof(f125,plain,
    ( ~ spl3_7
    | ~ spl3_4
    | ~ spl3_11
    | ~ spl3_12
    | spl3_8 ),
    inference(avatar_split_clause,[],[f115,f102,f122,f118,f67,f88])).

fof(f102,plain,
    ( spl3_8
  <=> r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f115,plain,
    ( ~ r1_tarski(sK1,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl3_8 ),
    inference(resolution,[],[f104,f29])).

fof(f104,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | spl3_8 ),
    inference(avatar_component_clause,[],[f102])).

% (2183)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
fof(f109,plain,
    ( ~ spl3_8
    | ~ spl3_9
    | spl3_3 ),
    inference(avatar_split_clause,[],[f99,f62,f106,f102])).

fof(f62,plain,
    ( spl3_3
  <=> r1_tarski(k3_tarski(k2_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f99,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | spl3_3 ),
    inference(resolution,[],[f64,f39])).

fof(f64,plain,
    ( ~ r1_tarski(k3_tarski(k2_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f62])).

fof(f97,plain,
    ( ~ spl3_7
    | ~ spl3_5
    | spl3_2 ),
    inference(avatar_split_clause,[],[f95,f58,f71,f88])).

fof(f58,plain,
    ( spl3_2
  <=> m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f95,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl3_2 ),
    inference(resolution,[],[f60,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tops_1)).

fof(f60,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f58])).

fof(f93,plain,(
    spl3_7 ),
    inference(avatar_contradiction_clause,[],[f92])).

fof(f92,plain,
    ( $false
    | spl3_7 ),
    inference(resolution,[],[f90,f25])).

fof(f25,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f90,plain,
    ( ~ l1_pre_topc(sK0)
    | spl3_7 ),
    inference(avatar_component_clause,[],[f88])).

fof(f91,plain,
    ( ~ spl3_7
    | ~ spl3_4
    | spl3_1 ),
    inference(avatar_split_clause,[],[f85,f54,f67,f88])).

fof(f54,plain,
    ( spl3_1
  <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f85,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl3_1 ),
    inference(resolution,[],[f56,f33])).

fof(f56,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f54])).

fof(f84,plain,(
    spl3_5 ),
    inference(avatar_contradiction_clause,[],[f82])).

fof(f82,plain,
    ( $false
    | spl3_5 ),
    inference(resolution,[],[f73,f27])).

fof(f73,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_5 ),
    inference(avatar_component_clause,[],[f71])).

fof(f81,plain,(
    spl3_4 ),
    inference(avatar_contradiction_clause,[],[f79])).

fof(f79,plain,
    ( $false
    | spl3_4 ),
    inference(resolution,[],[f69,f26])).

fof(f69,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_4 ),
    inference(avatar_component_clause,[],[f67])).

fof(f65,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f51,f62,f58,f54])).

fof(f51,plain,
    ( ~ r1_tarski(k3_tarski(k2_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f28,f40])).

fof(f28,plain,(
    ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:05:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.43  % (2168)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.46  % (2172)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.46  % (2173)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.47  % (2171)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.47  % (2172)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f194,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(avatar_sat_refutation,[],[f65,f81,f84,f91,f93,f97,f109,f125,f138,f140,f147,f159,f163,f177,f187,f191,f193])).
% 0.20/0.47  fof(f193,plain,(
% 0.20/0.47    spl3_21),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f192])).
% 0.20/0.47  fof(f192,plain,(
% 0.20/0.47    $false | spl3_21),
% 0.20/0.47    inference(resolution,[],[f186,f46])).
% 0.20/0.47  fof(f46,plain,(
% 0.20/0.47    r1_tarski(sK2,u1_struct_0(sK0))),
% 0.20/0.47    inference(resolution,[],[f34,f27])).
% 0.20/0.47  fof(f27,plain,(
% 0.20/0.47    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.47    inference(cnf_transformation,[],[f23])).
% 0.20/0.47  fof(f23,plain,(
% 0.20/0.47    ((~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f22,f21,f20])).
% 0.20/0.47  fof(f20,plain,(
% 0.20/0.47    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X1),k1_tops_1(sK0,X2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f21,plain,(
% 0.20/0.47    ? [X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X1),k1_tops_1(sK0,X2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,X2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f22,plain,(
% 0.20/0.47    ? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,X2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f11,plain,(
% 0.20/0.47    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f10])).
% 0.20/0.47  fof(f10,negated_conjecture,(
% 0.20/0.47    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))))))),
% 0.20/0.47    inference(negated_conjecture,[],[f9])).
% 0.20/0.47  fof(f9,conjecture,(
% 0.20/0.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_tops_1)).
% 0.20/0.47  fof(f34,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f24])).
% 0.20/0.47  fof(f24,plain,(
% 0.20/0.47    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.20/0.47    inference(nnf_transformation,[],[f6])).
% 0.20/0.47  fof(f6,axiom,(
% 0.20/0.47    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.47  fof(f186,plain,(
% 0.20/0.47    ~r1_tarski(sK2,u1_struct_0(sK0)) | spl3_21),
% 0.20/0.47    inference(avatar_component_clause,[],[f184])).
% 0.20/0.47  fof(f184,plain,(
% 0.20/0.47    spl3_21 <=> r1_tarski(sK2,u1_struct_0(sK0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.20/0.47  fof(f191,plain,(
% 0.20/0.47    spl3_20),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f190])).
% 0.20/0.47  fof(f190,plain,(
% 0.20/0.47    $false | spl3_20),
% 0.20/0.47    inference(resolution,[],[f182,f45])).
% 0.20/0.47  fof(f45,plain,(
% 0.20/0.47    r1_tarski(sK1,u1_struct_0(sK0))),
% 0.20/0.47    inference(resolution,[],[f34,f26])).
% 0.20/0.47  fof(f26,plain,(
% 0.20/0.47    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.47    inference(cnf_transformation,[],[f23])).
% 0.20/0.47  fof(f182,plain,(
% 0.20/0.47    ~r1_tarski(sK1,u1_struct_0(sK0)) | spl3_20),
% 0.20/0.47    inference(avatar_component_clause,[],[f180])).
% 0.20/0.47  fof(f180,plain,(
% 0.20/0.47    spl3_20 <=> r1_tarski(sK1,u1_struct_0(sK0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.20/0.47  fof(f187,plain,(
% 0.20/0.47    ~spl3_20 | ~spl3_21 | spl3_19),
% 0.20/0.47    inference(avatar_split_clause,[],[f178,f174,f184,f180])).
% 0.20/0.47  fof(f174,plain,(
% 0.20/0.47    spl3_19 <=> r1_tarski(k3_tarski(k2_tarski(sK1,sK2)),u1_struct_0(sK0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.20/0.47  fof(f178,plain,(
% 0.20/0.47    ~r1_tarski(sK2,u1_struct_0(sK0)) | ~r1_tarski(sK1,u1_struct_0(sK0)) | spl3_19),
% 0.20/0.47    inference(resolution,[],[f176,f39])).
% 0.20/0.47  fof(f39,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (r1_tarski(k3_tarski(k2_tarski(X0,X2)),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.20/0.47    inference(definition_unfolding,[],[f36,f32])).
% 0.20/0.47  fof(f32,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f4])).
% 0.20/0.47  fof(f4,axiom,(
% 0.20/0.47    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.20/0.47  fof(f36,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f17])).
% 0.20/0.47  fof(f17,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 0.20/0.47    inference(flattening,[],[f16])).
% 0.20/0.47  fof(f16,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 0.20/0.47    inference(ennf_transformation,[],[f2])).
% 0.20/0.47  fof(f2,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).
% 0.20/0.47  fof(f176,plain,(
% 0.20/0.47    ~r1_tarski(k3_tarski(k2_tarski(sK1,sK2)),u1_struct_0(sK0)) | spl3_19),
% 0.20/0.47    inference(avatar_component_clause,[],[f174])).
% 0.20/0.47  fof(f177,plain,(
% 0.20/0.47    ~spl3_4 | ~spl3_5 | ~spl3_19 | spl3_11),
% 0.20/0.47    inference(avatar_split_clause,[],[f172,f118,f174,f71,f67])).
% 0.20/0.47  fof(f67,plain,(
% 0.20/0.47    spl3_4 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.47  fof(f71,plain,(
% 0.20/0.47    spl3_5 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.47  fof(f118,plain,(
% 0.20/0.47    spl3_11 <=> m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.20/0.47  fof(f172,plain,(
% 0.20/0.47    ~r1_tarski(k3_tarski(k2_tarski(sK1,sK2)),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl3_11),
% 0.20/0.47    inference(superposition,[],[f165,f40])).
% 0.20/0.47  fof(f40,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.47    inference(definition_unfolding,[],[f37,f32])).
% 0.20/0.47  fof(f37,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f19])).
% 0.20/0.47  fof(f19,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.47    inference(flattening,[],[f18])).
% 0.20/0.47  fof(f18,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.20/0.47    inference(ennf_transformation,[],[f5])).
% 0.20/0.47  fof(f5,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 0.20/0.47  fof(f165,plain,(
% 0.20/0.47    ~r1_tarski(k4_subset_1(u1_struct_0(sK0),sK1,sK2),u1_struct_0(sK0)) | spl3_11),
% 0.20/0.47    inference(resolution,[],[f120,f35])).
% 0.20/0.47  fof(f35,plain,(
% 0.20/0.47    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f24])).
% 0.20/0.47  fof(f120,plain,(
% 0.20/0.47    ~m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_11),
% 0.20/0.47    inference(avatar_component_clause,[],[f118])).
% 0.20/0.47  fof(f163,plain,(
% 0.20/0.47    spl3_17),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f162])).
% 0.20/0.47  fof(f162,plain,(
% 0.20/0.47    $false | spl3_17),
% 0.20/0.47    inference(resolution,[],[f158,f41])).
% 0.20/0.47  fof(f41,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k2_tarski(X1,X0)))) )),
% 0.20/0.47    inference(superposition,[],[f38,f31])).
% 0.20/0.47  fof(f31,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f3])).
% 0.20/0.47  fof(f3,axiom,(
% 0.20/0.47    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.20/0.47  fof(f38,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) )),
% 0.20/0.47    inference(definition_unfolding,[],[f30,f32])).
% 0.20/0.47  fof(f30,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f1])).
% 0.20/0.47  fof(f1,axiom,(
% 0.20/0.47    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.20/0.47  fof(f158,plain,(
% 0.20/0.47    ~r1_tarski(sK2,k3_tarski(k2_tarski(sK1,sK2))) | spl3_17),
% 0.20/0.47    inference(avatar_component_clause,[],[f156])).
% 0.20/0.47  fof(f156,plain,(
% 0.20/0.47    spl3_17 <=> r1_tarski(sK2,k3_tarski(k2_tarski(sK1,sK2)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.20/0.47  fof(f159,plain,(
% 0.20/0.47    ~spl3_4 | ~spl3_5 | ~spl3_17 | spl3_15),
% 0.20/0.47    inference(avatar_split_clause,[],[f154,f144,f156,f71,f67])).
% 0.20/0.47  fof(f144,plain,(
% 0.20/0.47    spl3_15 <=> r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK1,sK2))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.20/0.47  fof(f154,plain,(
% 0.20/0.47    ~r1_tarski(sK2,k3_tarski(k2_tarski(sK1,sK2))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl3_15),
% 0.20/0.47    inference(superposition,[],[f146,f40])).
% 0.20/0.47  fof(f146,plain,(
% 0.20/0.47    ~r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) | spl3_15),
% 0.20/0.47    inference(avatar_component_clause,[],[f144])).
% 0.20/0.47  fof(f147,plain,(
% 0.20/0.47    ~spl3_7 | ~spl3_5 | ~spl3_11 | ~spl3_15 | spl3_9),
% 0.20/0.47    inference(avatar_split_clause,[],[f141,f106,f144,f118,f71,f88])).
% 0.20/0.47  fof(f88,plain,(
% 0.20/0.47    spl3_7 <=> l1_pre_topc(sK0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.20/0.47  fof(f106,plain,(
% 0.20/0.47    spl3_9 <=> r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.20/0.47  fof(f141,plain,(
% 0.20/0.47    ~r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) | ~m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl3_9),
% 0.20/0.47    inference(resolution,[],[f108,f29])).
% 0.20/0.47  fof(f29,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f13])).
% 0.20/0.47  fof(f13,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.47    inference(flattening,[],[f12])).
% 0.20/0.47  fof(f12,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f8])).
% 0.20/0.47  fof(f8,axiom,(
% 0.20/0.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).
% 0.20/0.47  fof(f108,plain,(
% 0.20/0.47    ~r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) | spl3_9),
% 0.20/0.47    inference(avatar_component_clause,[],[f106])).
% 0.20/0.47  fof(f140,plain,(
% 0.20/0.47    spl3_14),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f139])).
% 0.20/0.47  fof(f139,plain,(
% 0.20/0.47    $false | spl3_14),
% 0.20/0.47    inference(resolution,[],[f137,f38])).
% 0.20/0.47  fof(f137,plain,(
% 0.20/0.47    ~r1_tarski(sK1,k3_tarski(k2_tarski(sK1,sK2))) | spl3_14),
% 0.20/0.47    inference(avatar_component_clause,[],[f135])).
% 0.20/0.47  fof(f135,plain,(
% 0.20/0.47    spl3_14 <=> r1_tarski(sK1,k3_tarski(k2_tarski(sK1,sK2)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.20/0.47  fof(f138,plain,(
% 0.20/0.47    ~spl3_4 | ~spl3_5 | ~spl3_14 | spl3_12),
% 0.20/0.47    inference(avatar_split_clause,[],[f133,f122,f135,f71,f67])).
% 0.20/0.47  fof(f122,plain,(
% 0.20/0.47    spl3_12 <=> r1_tarski(sK1,k4_subset_1(u1_struct_0(sK0),sK1,sK2))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.20/0.47  fof(f133,plain,(
% 0.20/0.47    ~r1_tarski(sK1,k3_tarski(k2_tarski(sK1,sK2))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl3_12),
% 0.20/0.47    inference(superposition,[],[f124,f40])).
% 0.20/0.47  fof(f124,plain,(
% 0.20/0.47    ~r1_tarski(sK1,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) | spl3_12),
% 0.20/0.47    inference(avatar_component_clause,[],[f122])).
% 0.20/0.47  fof(f125,plain,(
% 0.20/0.47    ~spl3_7 | ~spl3_4 | ~spl3_11 | ~spl3_12 | spl3_8),
% 0.20/0.47    inference(avatar_split_clause,[],[f115,f102,f122,f118,f67,f88])).
% 0.20/0.47  fof(f102,plain,(
% 0.20/0.47    spl3_8 <=> r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.20/0.47  fof(f115,plain,(
% 0.20/0.47    ~r1_tarski(sK1,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) | ~m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl3_8),
% 0.20/0.47    inference(resolution,[],[f104,f29])).
% 0.20/0.47  fof(f104,plain,(
% 0.20/0.47    ~r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) | spl3_8),
% 0.20/0.47    inference(avatar_component_clause,[],[f102])).
% 0.20/0.47  % (2183)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.47  fof(f109,plain,(
% 0.20/0.47    ~spl3_8 | ~spl3_9 | spl3_3),
% 0.20/0.47    inference(avatar_split_clause,[],[f99,f62,f106,f102])).
% 0.20/0.47  fof(f62,plain,(
% 0.20/0.47    spl3_3 <=> r1_tarski(k3_tarski(k2_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.47  fof(f99,plain,(
% 0.20/0.47    ~r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) | ~r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) | spl3_3),
% 0.20/0.47    inference(resolution,[],[f64,f39])).
% 0.20/0.47  fof(f64,plain,(
% 0.20/0.47    ~r1_tarski(k3_tarski(k2_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) | spl3_3),
% 0.20/0.47    inference(avatar_component_clause,[],[f62])).
% 0.20/0.47  fof(f97,plain,(
% 0.20/0.47    ~spl3_7 | ~spl3_5 | spl3_2),
% 0.20/0.47    inference(avatar_split_clause,[],[f95,f58,f71,f88])).
% 0.20/0.47  fof(f58,plain,(
% 0.20/0.47    spl3_2 <=> m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.47  fof(f95,plain,(
% 0.20/0.47    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl3_2),
% 0.20/0.47    inference(resolution,[],[f60,f33])).
% 0.20/0.47  fof(f33,plain,(
% 0.20/0.47    ( ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f15])).
% 0.20/0.47  fof(f15,plain,(
% 0.20/0.47    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.20/0.47    inference(flattening,[],[f14])).
% 0.20/0.47  fof(f14,plain,(
% 0.20/0.47    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f7])).
% 0.20/0.47  fof(f7,axiom,(
% 0.20/0.47    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tops_1)).
% 0.20/0.47  fof(f60,plain,(
% 0.20/0.47    ~m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_2),
% 0.20/0.47    inference(avatar_component_clause,[],[f58])).
% 0.20/0.47  fof(f93,plain,(
% 0.20/0.47    spl3_7),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f92])).
% 0.20/0.47  fof(f92,plain,(
% 0.20/0.47    $false | spl3_7),
% 0.20/0.47    inference(resolution,[],[f90,f25])).
% 0.20/0.47  fof(f25,plain,(
% 0.20/0.47    l1_pre_topc(sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f23])).
% 0.20/0.47  fof(f90,plain,(
% 0.20/0.47    ~l1_pre_topc(sK0) | spl3_7),
% 0.20/0.47    inference(avatar_component_clause,[],[f88])).
% 0.20/0.47  fof(f91,plain,(
% 0.20/0.47    ~spl3_7 | ~spl3_4 | spl3_1),
% 0.20/0.47    inference(avatar_split_clause,[],[f85,f54,f67,f88])).
% 0.20/0.47  fof(f54,plain,(
% 0.20/0.47    spl3_1 <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.47  fof(f85,plain,(
% 0.20/0.47    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl3_1),
% 0.20/0.47    inference(resolution,[],[f56,f33])).
% 0.20/0.47  fof(f56,plain,(
% 0.20/0.47    ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_1),
% 0.20/0.47    inference(avatar_component_clause,[],[f54])).
% 0.20/0.47  fof(f84,plain,(
% 0.20/0.47    spl3_5),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f82])).
% 0.20/0.47  fof(f82,plain,(
% 0.20/0.47    $false | spl3_5),
% 0.20/0.47    inference(resolution,[],[f73,f27])).
% 0.20/0.47  fof(f73,plain,(
% 0.20/0.47    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | spl3_5),
% 0.20/0.47    inference(avatar_component_clause,[],[f71])).
% 0.20/0.47  fof(f81,plain,(
% 0.20/0.47    spl3_4),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f79])).
% 0.20/0.47  fof(f79,plain,(
% 0.20/0.47    $false | spl3_4),
% 0.20/0.47    inference(resolution,[],[f69,f26])).
% 0.20/0.47  fof(f69,plain,(
% 0.20/0.47    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl3_4),
% 0.20/0.47    inference(avatar_component_clause,[],[f67])).
% 0.20/0.47  fof(f65,plain,(
% 0.20/0.47    ~spl3_1 | ~spl3_2 | ~spl3_3),
% 0.20/0.47    inference(avatar_split_clause,[],[f51,f62,f58,f54])).
% 0.20/0.47  fof(f51,plain,(
% 0.20/0.47    ~r1_tarski(k3_tarski(k2_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) | ~m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.47    inference(superposition,[],[f28,f40])).
% 0.20/0.47  fof(f28,plain,(
% 0.20/0.47    ~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))),
% 0.20/0.47    inference(cnf_transformation,[],[f23])).
% 0.20/0.47  % SZS output end Proof for theBenchmark
% 0.20/0.47  % (2172)------------------------------
% 0.20/0.47  % (2172)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (2172)Termination reason: Refutation
% 0.20/0.47  
% 0.20/0.47  % (2172)Memory used [KB]: 6140
% 0.20/0.47  % (2172)Time elapsed: 0.065 s
% 0.20/0.47  % (2172)------------------------------
% 0.20/0.47  % (2172)------------------------------
% 0.20/0.47  % (2167)Success in time 0.114 s
%------------------------------------------------------------------------------
