%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:08 EST 2020

% Result     : Theorem 3.93s
% Output     : Refutation 3.93s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 303 expanded)
%              Number of leaves         :   29 (  99 expanded)
%              Depth                    :   10
%              Number of atoms          :  309 ( 732 expanded)
%              Number of equality atoms :   23 (  95 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5018,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f128,f133,f135,f259,f266,f597,f1465,f1539,f3191,f3757,f4006,f4067,f4979,f5007])).

fof(f5007,plain,
    ( ~ spl3_12
    | ~ spl3_13
    | ~ spl3_29
    | spl3_182 ),
    inference(avatar_split_clause,[],[f5006,f3520,f558,f247,f243])).

fof(f243,plain,
    ( spl3_12
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f247,plain,
    ( spl3_13
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f558,plain,
    ( spl3_29
  <=> r1_tarski(k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f3520,plain,
    ( spl3_182
  <=> r1_tarski(sK1,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_182])])).

fof(f5006,plain,
    ( ~ r1_tarski(k1_xboole_0,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_182 ),
    inference(forward_demodulation,[],[f4993,f189])).

fof(f189,plain,(
    ! [X2] : k1_xboole_0 = k4_xboole_0(X2,X2) ),
    inference(superposition,[],[f182,f35])).

fof(f35,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f182,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X0),X1) ),
    inference(superposition,[],[f54,f53])).

fof(f53,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k3_tarski(k1_enumset1(X0,X0,X1))) ),
    inference(definition_unfolding,[],[f38,f52])).

fof(f52,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f39,f40])).

fof(f40,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f39,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f38,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f54,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k3_tarski(k1_enumset1(X1,X1,X2))) ),
    inference(definition_unfolding,[],[f46,f52])).

fof(f46,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f4993,plain,
    ( ~ r1_tarski(k4_xboole_0(sK1,sK1),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_182 ),
    inference(resolution,[],[f3522,f233])).

fof(f233,plain,(
    ! [X10,X8,X7,X9] :
      ( r1_tarski(X10,k4_subset_1(X9,X7,X8))
      | ~ r1_tarski(k4_xboole_0(X10,X7),X8)
      | ~ m1_subset_1(X8,k1_zfmisc_1(X9))
      | ~ m1_subset_1(X7,k1_zfmisc_1(X9)) ) ),
    inference(superposition,[],[f56,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k3_tarski(k1_enumset1(X1,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f51,f52])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X2)))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f48,f52])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k4_xboole_0(X0,X1),X2)
      | r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f3522,plain,
    ( ~ r1_tarski(sK1,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
    | spl3_182 ),
    inference(avatar_component_clause,[],[f3520])).

fof(f4979,plain,
    ( ~ spl3_6
    | ~ spl3_182
    | ~ spl3_170
    | ~ spl3_12
    | spl3_155 ),
    inference(avatar_split_clause,[],[f4972,f3188,f243,f3452,f3520,f125])).

fof(f125,plain,
    ( spl3_6
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f3452,plain,
    ( spl3_170
  <=> m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_170])])).

fof(f3188,plain,
    ( spl3_155
  <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_155])])).

fof(f4972,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(sK1,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ l1_pre_topc(sK0)
    | spl3_155 ),
    inference(resolution,[],[f4960,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X1,X2)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).

fof(f4960,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | spl3_155 ),
    inference(resolution,[],[f3190,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f3190,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))))
    | spl3_155 ),
    inference(avatar_component_clause,[],[f3188])).

fof(f4067,plain,(
    spl3_190 ),
    inference(avatar_contradiction_clause,[],[f4058])).

fof(f4058,plain,
    ( $false
    | spl3_190 ),
    inference(unit_resulting_resolution,[],[f58,f32,f30,f3618,f234])).

fof(f234,plain,(
    ! [X14,X12,X13,X11] :
      ( r1_tarski(X14,k4_subset_1(X13,X11,X12))
      | ~ r1_tarski(X14,X12)
      | ~ m1_subset_1(X12,k1_zfmisc_1(X13))
      | ~ m1_subset_1(X11,k1_zfmisc_1(X13)) ) ),
    inference(superposition,[],[f55,f57])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_tarski(k1_enumset1(X2,X2,X1)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f47,f52])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f3618,plain,
    ( ~ r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
    | spl3_190 ),
    inference(avatar_component_clause,[],[f3616])).

fof(f3616,plain,
    ( spl3_190
  <=> r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_190])])).

fof(f30,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_tops_1)).

fof(f32,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f58,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f4006,plain,
    ( ~ spl3_6
    | ~ spl3_190
    | ~ spl3_170
    | ~ spl3_13
    | spl3_154 ),
    inference(avatar_split_clause,[],[f3999,f3184,f247,f3452,f3616,f125])).

fof(f3184,plain,
    ( spl3_154
  <=> m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_154])])).

fof(f3999,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ l1_pre_topc(sK0)
    | spl3_154 ),
    inference(resolution,[],[f3990,f37])).

fof(f3990,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | spl3_154 ),
    inference(resolution,[],[f3186,f44])).

fof(f3186,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))))
    | spl3_154 ),
    inference(avatar_component_clause,[],[f3184])).

fof(f3757,plain,(
    spl3_170 ),
    inference(avatar_contradiction_clause,[],[f3747])).

fof(f3747,plain,
    ( $false
    | spl3_170 ),
    inference(unit_resulting_resolution,[],[f32,f30,f32,f30,f3454,f503])).

fof(f503,plain,(
    ! [X6,X4,X7,X5] :
      ( m1_subset_1(k4_subset_1(X6,X4,X5),k1_zfmisc_1(X7))
      | ~ m1_subset_1(X5,k1_zfmisc_1(X7))
      | ~ m1_subset_1(X4,k1_zfmisc_1(X7))
      | ~ m1_subset_1(X5,k1_zfmisc_1(X6))
      | ~ m1_subset_1(X4,k1_zfmisc_1(X6)) ) ),
    inference(superposition,[],[f240,f57])).

fof(f240,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k3_tarski(k1_enumset1(X1,X1,X2)),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f229])).

fof(f229,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k3_tarski(k1_enumset1(X1,X1,X2)),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(superposition,[],[f50,f57])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).

fof(f3454,plain,
    ( ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_170 ),
    inference(avatar_component_clause,[],[f3452])).

fof(f3191,plain,
    ( ~ spl3_65
    | ~ spl3_66
    | ~ spl3_154
    | ~ spl3_155 ),
    inference(avatar_split_clause,[],[f3138,f3188,f3184,f1410,f1406])).

fof(f1406,plain,
    ( spl3_65
  <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_65])])).

fof(f1410,plain,
    ( spl3_66
  <=> m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_66])])).

fof(f3138,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))))
    | ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))))
    | ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f1354,f31])).

fof(f31,plain,(
    ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    inference(cnf_transformation,[],[f18])).

fof(f1354,plain,(
    ! [X10,X8,X11,X9] :
      ( r1_tarski(k4_subset_1(X11,X9,X10),X8)
      | ~ m1_subset_1(X9,k1_zfmisc_1(X8))
      | ~ m1_subset_1(X10,k1_zfmisc_1(X8))
      | ~ m1_subset_1(X10,k1_zfmisc_1(X11))
      | ~ m1_subset_1(X9,k1_zfmisc_1(X11)) ) ),
    inference(duplicate_literal_removal,[],[f1325])).

fof(f1325,plain,(
    ! [X10,X8,X11,X9] :
      ( r1_tarski(k4_subset_1(X11,X9,X10),X8)
      | ~ m1_subset_1(X9,k1_zfmisc_1(X8))
      | ~ m1_subset_1(X10,k1_zfmisc_1(X8))
      | ~ m1_subset_1(X10,k1_zfmisc_1(X8))
      | ~ m1_subset_1(X9,k1_zfmisc_1(X8))
      | ~ m1_subset_1(X10,k1_zfmisc_1(X11))
      | ~ m1_subset_1(X9,k1_zfmisc_1(X11)) ) ),
    inference(superposition,[],[f184,f228])).

fof(f228,plain,(
    ! [X4,X2,X3,X1] :
      ( k4_subset_1(X3,X1,X2) = k4_subset_1(X4,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X4))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X4))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X3)) ) ),
    inference(superposition,[],[f57,f57])).

fof(f184,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_subset_1(X1,X2,X0),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(resolution,[],[f50,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f1539,plain,
    ( ~ spl3_5
    | spl3_66 ),
    inference(avatar_contradiction_clause,[],[f1526])).

fof(f1526,plain,
    ( $false
    | ~ spl3_5
    | spl3_66 ),
    inference(unit_resulting_resolution,[],[f60,f123,f1519,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f1519,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0))
    | spl3_66 ),
    inference(resolution,[],[f1412,f44])).

fof(f1412,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_66 ),
    inference(avatar_component_clause,[],[f1410])).

fof(f123,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f121])).

fof(f121,plain,
    ( spl3_5
  <=> r1_tarski(k1_tops_1(sK0,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f60,plain,(
    r1_tarski(sK2,u1_struct_0(sK0)) ),
    inference(resolution,[],[f45,f30])).

fof(f1465,plain,
    ( ~ spl3_7
    | spl3_65 ),
    inference(avatar_contradiction_clause,[],[f1452])).

fof(f1452,plain,
    ( $false
    | ~ spl3_7
    | spl3_65 ),
    inference(unit_resulting_resolution,[],[f61,f132,f1445,f49])).

fof(f1445,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))
    | spl3_65 ),
    inference(resolution,[],[f1408,f44])).

fof(f1408,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_65 ),
    inference(avatar_component_clause,[],[f1406])).

fof(f132,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f130])).

fof(f130,plain,
    ( spl3_7
  <=> r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f61,plain,(
    r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(resolution,[],[f45,f32])).

fof(f597,plain,(
    spl3_29 ),
    inference(avatar_contradiction_clause,[],[f588])).

fof(f588,plain,
    ( $false
    | spl3_29 ),
    inference(unit_resulting_resolution,[],[f34,f58,f560,f49])).

fof(f560,plain,
    ( ~ r1_tarski(k1_xboole_0,sK2)
    | spl3_29 ),
    inference(avatar_component_clause,[],[f558])).

fof(f34,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f266,plain,(
    spl3_13 ),
    inference(avatar_contradiction_clause,[],[f262])).

fof(f262,plain,
    ( $false
    | spl3_13 ),
    inference(subsumption_resolution,[],[f30,f249])).

fof(f249,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_13 ),
    inference(avatar_component_clause,[],[f247])).

fof(f259,plain,(
    spl3_12 ),
    inference(avatar_contradiction_clause,[],[f255])).

fof(f255,plain,
    ( $false
    | spl3_12 ),
    inference(subsumption_resolution,[],[f32,f245])).

fof(f245,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_12 ),
    inference(avatar_component_clause,[],[f243])).

fof(f135,plain,(
    spl3_6 ),
    inference(avatar_contradiction_clause,[],[f134])).

fof(f134,plain,
    ( $false
    | spl3_6 ),
    inference(subsumption_resolution,[],[f33,f127])).

fof(f127,plain,
    ( ~ l1_pre_topc(sK0)
    | spl3_6 ),
    inference(avatar_component_clause,[],[f125])).

fof(f33,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f133,plain,
    ( spl3_7
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f118,f125,f130])).

fof(f118,plain,
    ( ~ l1_pre_topc(sK0)
    | r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    inference(resolution,[],[f36,f32])).

fof(f36,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

fof(f128,plain,
    ( spl3_5
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f117,f125,f121])).

fof(f117,plain,
    ( ~ l1_pre_topc(sK0)
    | r1_tarski(k1_tops_1(sK0,sK2),sK2) ),
    inference(resolution,[],[f36,f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:33:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.50  % (15542)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.50  % (15558)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.51  % (15550)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.51  % (15556)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.51  % (15539)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.51  % (15548)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.51  % (15538)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.51  % (15536)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.52  % (15547)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.52  % (15540)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (15563)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.53  % (15561)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.53  % (15534)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.53  % (15562)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.53  % (15541)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.53  % (15552)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.44/0.54  % (15537)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.44/0.54  % (15560)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.44/0.54  % (15557)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.44/0.54  % (15553)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.44/0.54  % (15543)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.44/0.54  % (15555)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.44/0.54  % (15535)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.44/0.54  % (15554)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.44/0.55  % (15544)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.44/0.55  % (15545)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.44/0.55  % (15549)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.44/0.55  % (15546)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.56/0.55  % (15559)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.56/0.56  % (15551)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 3.24/0.81  % (15558)Time limit reached!
% 3.24/0.81  % (15558)------------------------------
% 3.24/0.81  % (15558)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.24/0.82  % (15536)Time limit reached!
% 3.24/0.82  % (15536)------------------------------
% 3.24/0.82  % (15536)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.24/0.82  % (15536)Termination reason: Time limit
% 3.24/0.82  
% 3.24/0.82  % (15536)Memory used [KB]: 6524
% 3.24/0.82  % (15536)Time elapsed: 0.414 s
% 3.24/0.82  % (15536)------------------------------
% 3.24/0.82  % (15536)------------------------------
% 3.24/0.82  % (15558)Termination reason: Time limit
% 3.24/0.82  
% 3.24/0.82  % (15558)Memory used [KB]: 12920
% 3.24/0.82  % (15558)Time elapsed: 0.405 s
% 3.24/0.82  % (15558)------------------------------
% 3.24/0.82  % (15558)------------------------------
% 3.93/0.92  % (15547)Refutation found. Thanks to Tanya!
% 3.93/0.92  % SZS status Theorem for theBenchmark
% 3.93/0.92  % SZS output start Proof for theBenchmark
% 3.93/0.92  fof(f5018,plain,(
% 3.93/0.92    $false),
% 3.93/0.92    inference(avatar_sat_refutation,[],[f128,f133,f135,f259,f266,f597,f1465,f1539,f3191,f3757,f4006,f4067,f4979,f5007])).
% 3.93/0.92  fof(f5007,plain,(
% 3.93/0.92    ~spl3_12 | ~spl3_13 | ~spl3_29 | spl3_182),
% 3.93/0.92    inference(avatar_split_clause,[],[f5006,f3520,f558,f247,f243])).
% 3.93/0.92  fof(f243,plain,(
% 3.93/0.92    spl3_12 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.93/0.92    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 3.93/0.92  fof(f247,plain,(
% 3.93/0.92    spl3_13 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.93/0.92    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 3.93/0.92  fof(f558,plain,(
% 3.93/0.92    spl3_29 <=> r1_tarski(k1_xboole_0,sK2)),
% 3.93/0.92    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 3.93/0.92  fof(f3520,plain,(
% 3.93/0.92    spl3_182 <=> r1_tarski(sK1,k4_subset_1(u1_struct_0(sK0),sK1,sK2))),
% 3.93/0.92    introduced(avatar_definition,[new_symbols(naming,[spl3_182])])).
% 3.93/0.92  fof(f5006,plain,(
% 3.93/0.92    ~r1_tarski(k1_xboole_0,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl3_182),
% 3.93/0.92    inference(forward_demodulation,[],[f4993,f189])).
% 3.93/0.92  fof(f189,plain,(
% 3.93/0.92    ( ! [X2] : (k1_xboole_0 = k4_xboole_0(X2,X2)) )),
% 3.93/0.92    inference(superposition,[],[f182,f35])).
% 3.93/0.92  fof(f35,plain,(
% 3.93/0.92    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.93/0.92    inference(cnf_transformation,[],[f5])).
% 3.93/0.92  fof(f5,axiom,(
% 3.93/0.92    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 3.93/0.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 3.93/0.92  fof(f182,plain,(
% 3.93/0.92    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X0),X1)) )),
% 3.93/0.92    inference(superposition,[],[f54,f53])).
% 3.93/0.92  fof(f53,plain,(
% 3.93/0.92    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k3_tarski(k1_enumset1(X0,X0,X1)))) )),
% 3.93/0.92    inference(definition_unfolding,[],[f38,f52])).
% 3.93/0.92  fof(f52,plain,(
% 3.93/0.92    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 3.93/0.92    inference(definition_unfolding,[],[f39,f40])).
% 3.93/0.92  fof(f40,plain,(
% 3.93/0.92    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.93/0.92    inference(cnf_transformation,[],[f9])).
% 3.93/0.92  fof(f9,axiom,(
% 3.93/0.92    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.93/0.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 3.93/0.92  fof(f39,plain,(
% 3.93/0.92    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.93/0.92    inference(cnf_transformation,[],[f10])).
% 3.93/0.92  fof(f10,axiom,(
% 3.93/0.92    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.93/0.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 3.93/0.92  fof(f38,plain,(
% 3.93/0.92    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 3.93/0.92    inference(cnf_transformation,[],[f8])).
% 3.93/0.92  fof(f8,axiom,(
% 3.93/0.92    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 3.93/0.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
% 3.93/0.92  fof(f54,plain,(
% 3.93/0.92    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k3_tarski(k1_enumset1(X1,X1,X2)))) )),
% 3.93/0.92    inference(definition_unfolding,[],[f46,f52])).
% 3.93/0.92  fof(f46,plain,(
% 3.93/0.92    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 3.93/0.92    inference(cnf_transformation,[],[f6])).
% 3.93/0.92  fof(f6,axiom,(
% 3.93/0.92    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 3.93/0.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 3.93/0.92  fof(f4993,plain,(
% 3.93/0.92    ~r1_tarski(k4_xboole_0(sK1,sK1),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl3_182),
% 3.93/0.92    inference(resolution,[],[f3522,f233])).
% 3.93/0.92  fof(f233,plain,(
% 3.93/0.92    ( ! [X10,X8,X7,X9] : (r1_tarski(X10,k4_subset_1(X9,X7,X8)) | ~r1_tarski(k4_xboole_0(X10,X7),X8) | ~m1_subset_1(X8,k1_zfmisc_1(X9)) | ~m1_subset_1(X7,k1_zfmisc_1(X9))) )),
% 3.93/0.92    inference(superposition,[],[f56,f57])).
% 3.93/0.92  fof(f57,plain,(
% 3.93/0.92    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k3_tarski(k1_enumset1(X1,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.93/0.92    inference(definition_unfolding,[],[f51,f52])).
% 3.93/0.92  fof(f51,plain,(
% 3.93/0.92    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)) )),
% 3.93/0.92    inference(cnf_transformation,[],[f29])).
% 3.93/0.92  fof(f29,plain,(
% 3.93/0.92    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.93/0.92    inference(flattening,[],[f28])).
% 3.93/0.92  fof(f28,plain,(
% 3.93/0.92    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 3.93/0.92    inference(ennf_transformation,[],[f12])).
% 3.93/0.92  fof(f12,axiom,(
% 3.93/0.92    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 3.93/0.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 3.93/0.92  fof(f56,plain,(
% 3.93/0.92    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X2))) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 3.93/0.92    inference(definition_unfolding,[],[f48,f52])).
% 3.93/0.92  fof(f48,plain,(
% 3.93/0.92    ( ! [X2,X0,X1] : (~r1_tarski(k4_xboole_0(X0,X1),X2) | r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 3.93/0.92    inference(cnf_transformation,[],[f23])).
% 3.93/0.92  fof(f23,plain,(
% 3.93/0.92    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 3.93/0.92    inference(ennf_transformation,[],[f7])).
% 3.93/0.92  fof(f7,axiom,(
% 3.93/0.92    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 3.93/0.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).
% 3.93/0.92  fof(f3522,plain,(
% 3.93/0.92    ~r1_tarski(sK1,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) | spl3_182),
% 3.93/0.92    inference(avatar_component_clause,[],[f3520])).
% 3.93/0.92  fof(f4979,plain,(
% 3.93/0.92    ~spl3_6 | ~spl3_182 | ~spl3_170 | ~spl3_12 | spl3_155),
% 3.93/0.92    inference(avatar_split_clause,[],[f4972,f3188,f243,f3452,f3520,f125])).
% 3.93/0.92  fof(f125,plain,(
% 3.93/0.92    spl3_6 <=> l1_pre_topc(sK0)),
% 3.93/0.92    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 3.93/0.92  fof(f3452,plain,(
% 3.93/0.92    spl3_170 <=> m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.93/0.92    introduced(avatar_definition,[new_symbols(naming,[spl3_170])])).
% 3.93/0.92  fof(f3188,plain,(
% 3.93/0.92    spl3_155 <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))))),
% 3.93/0.92    introduced(avatar_definition,[new_symbols(naming,[spl3_155])])).
% 3.93/0.92  fof(f4972,plain,(
% 3.93/0.92    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(sK1,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) | ~l1_pre_topc(sK0) | spl3_155),
% 3.93/0.92    inference(resolution,[],[f4960,f37])).
% 3.93/0.92  fof(f37,plain,(
% 3.93/0.92    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X1,X2) | ~l1_pre_topc(X0)) )),
% 3.93/0.92    inference(cnf_transformation,[],[f21])).
% 3.93/0.92  fof(f21,plain,(
% 3.93/0.92    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.93/0.92    inference(flattening,[],[f20])).
% 3.93/0.92  fof(f20,plain,(
% 3.93/0.92    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.93/0.92    inference(ennf_transformation,[],[f15])).
% 3.93/0.92  fof(f15,axiom,(
% 3.93/0.92    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 3.93/0.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).
% 3.93/0.92  fof(f4960,plain,(
% 3.93/0.92    ~r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) | spl3_155),
% 3.93/0.92    inference(resolution,[],[f3190,f44])).
% 3.93/0.92  fof(f44,plain,(
% 3.93/0.92    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.93/0.92    inference(cnf_transformation,[],[f13])).
% 3.93/0.92  fof(f13,axiom,(
% 3.93/0.92    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.93/0.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 3.93/0.92  fof(f3190,plain,(
% 3.93/0.92    ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))) | spl3_155),
% 3.93/0.92    inference(avatar_component_clause,[],[f3188])).
% 3.93/0.92  fof(f4067,plain,(
% 3.93/0.92    spl3_190),
% 3.93/0.92    inference(avatar_contradiction_clause,[],[f4058])).
% 3.93/0.92  fof(f4058,plain,(
% 3.93/0.92    $false | spl3_190),
% 3.93/0.92    inference(unit_resulting_resolution,[],[f58,f32,f30,f3618,f234])).
% 3.93/0.92  fof(f234,plain,(
% 3.93/0.92    ( ! [X14,X12,X13,X11] : (r1_tarski(X14,k4_subset_1(X13,X11,X12)) | ~r1_tarski(X14,X12) | ~m1_subset_1(X12,k1_zfmisc_1(X13)) | ~m1_subset_1(X11,k1_zfmisc_1(X13))) )),
% 3.93/0.92    inference(superposition,[],[f55,f57])).
% 3.93/0.92  fof(f55,plain,(
% 3.93/0.92    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_tarski(k1_enumset1(X2,X2,X1))) | ~r1_tarski(X0,X1)) )),
% 3.93/0.92    inference(definition_unfolding,[],[f47,f52])).
% 3.93/0.92  fof(f47,plain,(
% 3.93/0.92    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(X0,k2_xboole_0(X2,X1))) )),
% 3.93/0.92    inference(cnf_transformation,[],[f22])).
% 3.93/0.92  fof(f22,plain,(
% 3.93/0.92    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 3.93/0.92    inference(ennf_transformation,[],[f2])).
% 3.93/0.92  fof(f2,axiom,(
% 3.93/0.92    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 3.93/0.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).
% 3.93/0.92  fof(f3618,plain,(
% 3.93/0.92    ~r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) | spl3_190),
% 3.93/0.92    inference(avatar_component_clause,[],[f3616])).
% 3.93/0.92  fof(f3616,plain,(
% 3.93/0.92    spl3_190 <=> r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK1,sK2))),
% 3.93/0.92    introduced(avatar_definition,[new_symbols(naming,[spl3_190])])).
% 3.93/0.92  fof(f30,plain,(
% 3.93/0.92    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.93/0.92    inference(cnf_transformation,[],[f18])).
% 3.93/0.92  fof(f18,plain,(
% 3.93/0.92    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 3.93/0.92    inference(ennf_transformation,[],[f17])).
% 3.93/0.92  fof(f17,negated_conjecture,(
% 3.93/0.92    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))))))),
% 3.93/0.92    inference(negated_conjecture,[],[f16])).
% 3.93/0.92  fof(f16,conjecture,(
% 3.93/0.92    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))))))),
% 3.93/0.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_tops_1)).
% 3.93/0.92  fof(f32,plain,(
% 3.93/0.92    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.93/0.92    inference(cnf_transformation,[],[f18])).
% 3.93/0.92  fof(f58,plain,(
% 3.93/0.92    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.93/0.92    inference(equality_resolution,[],[f42])).
% 3.93/0.92  fof(f42,plain,(
% 3.93/0.92    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.93/0.92    inference(cnf_transformation,[],[f1])).
% 3.93/0.92  fof(f1,axiom,(
% 3.93/0.92    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.93/0.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 3.93/0.92  fof(f4006,plain,(
% 3.93/0.92    ~spl3_6 | ~spl3_190 | ~spl3_170 | ~spl3_13 | spl3_154),
% 3.93/0.92    inference(avatar_split_clause,[],[f3999,f3184,f247,f3452,f3616,f125])).
% 3.93/0.92  fof(f3184,plain,(
% 3.93/0.92    spl3_154 <=> m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))))),
% 3.93/0.92    introduced(avatar_definition,[new_symbols(naming,[spl3_154])])).
% 3.93/0.92  fof(f3999,plain,(
% 3.93/0.92    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) | ~l1_pre_topc(sK0) | spl3_154),
% 3.93/0.92    inference(resolution,[],[f3990,f37])).
% 3.93/0.92  fof(f3990,plain,(
% 3.93/0.92    ~r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) | spl3_154),
% 3.93/0.92    inference(resolution,[],[f3186,f44])).
% 3.93/0.92  fof(f3186,plain,(
% 3.93/0.92    ~m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))) | spl3_154),
% 3.93/0.92    inference(avatar_component_clause,[],[f3184])).
% 3.93/0.92  fof(f3757,plain,(
% 3.93/0.92    spl3_170),
% 3.93/0.92    inference(avatar_contradiction_clause,[],[f3747])).
% 3.93/0.92  fof(f3747,plain,(
% 3.93/0.92    $false | spl3_170),
% 3.93/0.92    inference(unit_resulting_resolution,[],[f32,f30,f32,f30,f3454,f503])).
% 3.93/0.92  fof(f503,plain,(
% 3.93/0.92    ( ! [X6,X4,X7,X5] : (m1_subset_1(k4_subset_1(X6,X4,X5),k1_zfmisc_1(X7)) | ~m1_subset_1(X5,k1_zfmisc_1(X7)) | ~m1_subset_1(X4,k1_zfmisc_1(X7)) | ~m1_subset_1(X5,k1_zfmisc_1(X6)) | ~m1_subset_1(X4,k1_zfmisc_1(X6))) )),
% 3.93/0.92    inference(superposition,[],[f240,f57])).
% 3.93/0.92  fof(f240,plain,(
% 3.93/0.92    ( ! [X2,X0,X1] : (m1_subset_1(k3_tarski(k1_enumset1(X1,X1,X2)),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.93/0.92    inference(duplicate_literal_removal,[],[f229])).
% 3.93/0.92  fof(f229,plain,(
% 3.93/0.92    ( ! [X2,X0,X1] : (m1_subset_1(k3_tarski(k1_enumset1(X1,X1,X2)),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.93/0.92    inference(superposition,[],[f50,f57])).
% 3.93/0.92  fof(f50,plain,(
% 3.93/0.92    ( ! [X2,X0,X1] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.93/0.92    inference(cnf_transformation,[],[f27])).
% 3.93/0.92  fof(f27,plain,(
% 3.93/0.92    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.93/0.92    inference(flattening,[],[f26])).
% 3.93/0.92  fof(f26,plain,(
% 3.93/0.92    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 3.93/0.92    inference(ennf_transformation,[],[f11])).
% 3.93/0.92  fof(f11,axiom,(
% 3.93/0.92    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 3.93/0.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).
% 3.93/0.92  fof(f3454,plain,(
% 3.93/0.92    ~m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_170),
% 3.93/0.92    inference(avatar_component_clause,[],[f3452])).
% 3.93/0.92  fof(f3191,plain,(
% 3.93/0.92    ~spl3_65 | ~spl3_66 | ~spl3_154 | ~spl3_155),
% 3.93/0.92    inference(avatar_split_clause,[],[f3138,f3188,f3184,f1410,f1406])).
% 3.93/0.92  fof(f1406,plain,(
% 3.93/0.92    spl3_65 <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.93/0.92    introduced(avatar_definition,[new_symbols(naming,[spl3_65])])).
% 3.93/0.92  fof(f1410,plain,(
% 3.93/0.92    spl3_66 <=> m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.93/0.92    introduced(avatar_definition,[new_symbols(naming,[spl3_66])])).
% 3.93/0.92  fof(f3138,plain,(
% 3.93/0.92    ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))) | ~m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))) | ~m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.93/0.92    inference(resolution,[],[f1354,f31])).
% 3.93/0.92  fof(f31,plain,(
% 3.93/0.92    ~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))),
% 3.93/0.92    inference(cnf_transformation,[],[f18])).
% 3.93/0.92  fof(f1354,plain,(
% 3.93/0.92    ( ! [X10,X8,X11,X9] : (r1_tarski(k4_subset_1(X11,X9,X10),X8) | ~m1_subset_1(X9,k1_zfmisc_1(X8)) | ~m1_subset_1(X10,k1_zfmisc_1(X8)) | ~m1_subset_1(X10,k1_zfmisc_1(X11)) | ~m1_subset_1(X9,k1_zfmisc_1(X11))) )),
% 3.93/0.92    inference(duplicate_literal_removal,[],[f1325])).
% 3.93/0.92  fof(f1325,plain,(
% 3.93/0.92    ( ! [X10,X8,X11,X9] : (r1_tarski(k4_subset_1(X11,X9,X10),X8) | ~m1_subset_1(X9,k1_zfmisc_1(X8)) | ~m1_subset_1(X10,k1_zfmisc_1(X8)) | ~m1_subset_1(X10,k1_zfmisc_1(X8)) | ~m1_subset_1(X9,k1_zfmisc_1(X8)) | ~m1_subset_1(X10,k1_zfmisc_1(X11)) | ~m1_subset_1(X9,k1_zfmisc_1(X11))) )),
% 3.93/0.92    inference(superposition,[],[f184,f228])).
% 3.93/0.92  fof(f228,plain,(
% 3.93/0.92    ( ! [X4,X2,X3,X1] : (k4_subset_1(X3,X1,X2) = k4_subset_1(X4,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X4)) | ~m1_subset_1(X1,k1_zfmisc_1(X4)) | ~m1_subset_1(X2,k1_zfmisc_1(X3)) | ~m1_subset_1(X1,k1_zfmisc_1(X3))) )),
% 3.93/0.92    inference(superposition,[],[f57,f57])).
% 3.93/0.92  fof(f184,plain,(
% 3.93/0.92    ( ! [X2,X0,X1] : (r1_tarski(k4_subset_1(X1,X2,X0),X1) | ~m1_subset_1(X2,k1_zfmisc_1(X1)) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.93/0.92    inference(resolution,[],[f50,f45])).
% 3.93/0.92  fof(f45,plain,(
% 3.93/0.92    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 3.93/0.92    inference(cnf_transformation,[],[f13])).
% 3.93/0.92  fof(f1539,plain,(
% 3.93/0.92    ~spl3_5 | spl3_66),
% 3.93/0.92    inference(avatar_contradiction_clause,[],[f1526])).
% 3.93/0.92  fof(f1526,plain,(
% 3.93/0.92    $false | (~spl3_5 | spl3_66)),
% 3.93/0.92    inference(unit_resulting_resolution,[],[f60,f123,f1519,f49])).
% 3.93/0.92  fof(f49,plain,(
% 3.93/0.92    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1) | r1_tarski(X0,X2)) )),
% 3.93/0.92    inference(cnf_transformation,[],[f25])).
% 3.93/0.92  fof(f25,plain,(
% 3.93/0.92    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 3.93/0.92    inference(flattening,[],[f24])).
% 3.93/0.92  fof(f24,plain,(
% 3.93/0.92    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 3.93/0.92    inference(ennf_transformation,[],[f3])).
% 3.93/0.92  fof(f3,axiom,(
% 3.93/0.92    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 3.93/0.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 3.93/0.92  fof(f1519,plain,(
% 3.93/0.92    ~r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0)) | spl3_66),
% 3.93/0.92    inference(resolution,[],[f1412,f44])).
% 3.93/0.92  fof(f1412,plain,(
% 3.93/0.92    ~m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_66),
% 3.93/0.92    inference(avatar_component_clause,[],[f1410])).
% 3.93/0.92  fof(f123,plain,(
% 3.93/0.92    r1_tarski(k1_tops_1(sK0,sK2),sK2) | ~spl3_5),
% 3.93/0.92    inference(avatar_component_clause,[],[f121])).
% 3.93/0.92  fof(f121,plain,(
% 3.93/0.92    spl3_5 <=> r1_tarski(k1_tops_1(sK0,sK2),sK2)),
% 3.93/0.92    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 3.93/0.92  fof(f60,plain,(
% 3.93/0.92    r1_tarski(sK2,u1_struct_0(sK0))),
% 3.93/0.92    inference(resolution,[],[f45,f30])).
% 3.93/0.92  fof(f1465,plain,(
% 3.93/0.92    ~spl3_7 | spl3_65),
% 3.93/0.92    inference(avatar_contradiction_clause,[],[f1452])).
% 3.93/0.92  fof(f1452,plain,(
% 3.93/0.92    $false | (~spl3_7 | spl3_65)),
% 3.93/0.92    inference(unit_resulting_resolution,[],[f61,f132,f1445,f49])).
% 3.93/0.92  fof(f1445,plain,(
% 3.93/0.92    ~r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) | spl3_65),
% 3.93/0.92    inference(resolution,[],[f1408,f44])).
% 3.93/0.92  fof(f1408,plain,(
% 3.93/0.92    ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_65),
% 3.93/0.92    inference(avatar_component_clause,[],[f1406])).
% 3.93/0.92  fof(f132,plain,(
% 3.93/0.92    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~spl3_7),
% 3.93/0.92    inference(avatar_component_clause,[],[f130])).
% 3.93/0.92  fof(f130,plain,(
% 3.93/0.92    spl3_7 <=> r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 3.93/0.92    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 3.93/0.92  fof(f61,plain,(
% 3.93/0.92    r1_tarski(sK1,u1_struct_0(sK0))),
% 3.93/0.92    inference(resolution,[],[f45,f32])).
% 3.93/0.92  fof(f597,plain,(
% 3.93/0.92    spl3_29),
% 3.93/0.92    inference(avatar_contradiction_clause,[],[f588])).
% 3.93/0.92  fof(f588,plain,(
% 3.93/0.92    $false | spl3_29),
% 3.93/0.92    inference(unit_resulting_resolution,[],[f34,f58,f560,f49])).
% 3.93/0.92  fof(f560,plain,(
% 3.93/0.92    ~r1_tarski(k1_xboole_0,sK2) | spl3_29),
% 3.93/0.92    inference(avatar_component_clause,[],[f558])).
% 3.93/0.92  fof(f34,plain,(
% 3.93/0.92    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.93/0.92    inference(cnf_transformation,[],[f4])).
% 3.93/0.92  fof(f4,axiom,(
% 3.93/0.92    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.93/0.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 3.93/0.92  fof(f266,plain,(
% 3.93/0.92    spl3_13),
% 3.93/0.92    inference(avatar_contradiction_clause,[],[f262])).
% 3.93/0.92  fof(f262,plain,(
% 3.93/0.92    $false | spl3_13),
% 3.93/0.92    inference(subsumption_resolution,[],[f30,f249])).
% 3.93/0.92  fof(f249,plain,(
% 3.93/0.92    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | spl3_13),
% 3.93/0.92    inference(avatar_component_clause,[],[f247])).
% 3.93/0.92  fof(f259,plain,(
% 3.93/0.92    spl3_12),
% 3.93/0.92    inference(avatar_contradiction_clause,[],[f255])).
% 3.93/0.92  fof(f255,plain,(
% 3.93/0.92    $false | spl3_12),
% 3.93/0.92    inference(subsumption_resolution,[],[f32,f245])).
% 3.93/0.92  fof(f245,plain,(
% 3.93/0.92    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl3_12),
% 3.93/0.92    inference(avatar_component_clause,[],[f243])).
% 3.93/0.92  fof(f135,plain,(
% 3.93/0.92    spl3_6),
% 3.93/0.92    inference(avatar_contradiction_clause,[],[f134])).
% 3.93/0.92  fof(f134,plain,(
% 3.93/0.92    $false | spl3_6),
% 3.93/0.92    inference(subsumption_resolution,[],[f33,f127])).
% 3.93/0.92  fof(f127,plain,(
% 3.93/0.92    ~l1_pre_topc(sK0) | spl3_6),
% 3.93/0.92    inference(avatar_component_clause,[],[f125])).
% 3.93/0.92  fof(f33,plain,(
% 3.93/0.92    l1_pre_topc(sK0)),
% 3.93/0.92    inference(cnf_transformation,[],[f18])).
% 3.93/0.92  fof(f133,plain,(
% 3.93/0.92    spl3_7 | ~spl3_6),
% 3.93/0.92    inference(avatar_split_clause,[],[f118,f125,f130])).
% 3.93/0.92  fof(f118,plain,(
% 3.93/0.92    ~l1_pre_topc(sK0) | r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 3.93/0.92    inference(resolution,[],[f36,f32])).
% 3.93/0.92  fof(f36,plain,(
% 3.93/0.92    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | r1_tarski(k1_tops_1(X0,X1),X1)) )),
% 3.93/0.92    inference(cnf_transformation,[],[f19])).
% 3.93/0.92  fof(f19,plain,(
% 3.93/0.92    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.93/0.92    inference(ennf_transformation,[],[f14])).
% 3.93/0.92  fof(f14,axiom,(
% 3.93/0.92    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 3.93/0.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).
% 3.93/0.92  fof(f128,plain,(
% 3.93/0.92    spl3_5 | ~spl3_6),
% 3.93/0.92    inference(avatar_split_clause,[],[f117,f125,f121])).
% 3.93/0.92  fof(f117,plain,(
% 3.93/0.92    ~l1_pre_topc(sK0) | r1_tarski(k1_tops_1(sK0,sK2),sK2)),
% 3.93/0.92    inference(resolution,[],[f36,f30])).
% 3.93/0.92  % SZS output end Proof for theBenchmark
% 3.93/0.92  % (15547)------------------------------
% 3.93/0.92  % (15547)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.93/0.92  % (15547)Termination reason: Refutation
% 3.93/0.92  
% 3.93/0.92  % (15547)Memory used [KB]: 8955
% 3.93/0.92  % (15547)Time elapsed: 0.499 s
% 3.93/0.92  % (15547)------------------------------
% 3.93/0.92  % (15547)------------------------------
% 3.93/0.92  % (15533)Success in time 0.564 s
%------------------------------------------------------------------------------
