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
% DateTime   : Thu Dec  3 13:11:33 EST 2020

% Result     : Theorem 7.42s
% Output     : Refutation 7.42s
% Verified   : 
% Statistics : Number of formulae       :  204 ( 374 expanded)
%              Number of leaves         :   45 ( 134 expanded)
%              Depth                    :   13
%              Number of atoms          :  612 (1182 expanded)
%              Number of equality atoms :   95 ( 218 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4031,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f118,f119,f124,f129,f134,f154,f262,f588,f1813,f1900,f2520,f2540,f2638,f2692,f2702,f2739,f2742,f2757,f3901,f3946,f4024,f4030])).

fof(f4030,plain,
    ( sK1 != k1_tops_1(sK0,sK1)
    | v3_pre_topc(sK1,sK0)
    | ~ v3_pre_topc(k1_tops_1(sK0,sK1),sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f4024,plain,(
    ~ spl3_80 ),
    inference(avatar_contradiction_clause,[],[f3997])).

fof(f3997,plain,
    ( $false
    | ~ spl3_80 ),
    inference(unit_resulting_resolution,[],[f156,f93,f2792,f104])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).

fof(f2792,plain,
    ( ! [X2] : ~ m1_subset_1(X2,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl3_80 ),
    inference(avatar_component_clause,[],[f2791])).

fof(f2791,plain,
    ( spl3_80
  <=> ! [X2] : ~ m1_subset_1(X2,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_80])])).

fof(f93,plain,(
    ! [X0] : m1_subset_1(sK2(X0),X0) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0] : m1_subset_1(sK2(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f16,f68])).

fof(f68,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f16,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(f156,plain,(
    ! [X0,X1] : m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0)) ),
    inference(backward_demodulation,[],[f107,f97])).

fof(f97,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f107,plain,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).

fof(f3946,plain,
    ( spl3_77
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_118 ),
    inference(avatar_split_clause,[],[f3945,f3898,f126,f121,f2560])).

fof(f2560,plain,
    ( spl3_77
  <=> sK1 = k1_tops_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_77])])).

fof(f121,plain,
    ( spl3_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f126,plain,
    ( spl3_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f3898,plain,
    ( spl3_118
  <=> sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_118])])).

fof(f3945,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_118 ),
    inference(subsumption_resolution,[],[f3944,f128])).

fof(f128,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f126])).

fof(f3944,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl3_3
    | ~ spl3_118 ),
    inference(subsumption_resolution,[],[f3910,f123])).

fof(f123,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f121])).

fof(f3910,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_118 ),
    inference(superposition,[],[f283,f3900])).

fof(f3900,plain,
    ( sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl3_118 ),
    inference(avatar_component_clause,[],[f3898])).

fof(f283,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f282])).

fof(f282,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(superposition,[],[f75,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f3901,plain,
    ( spl3_80
    | spl3_118
    | ~ spl3_28
    | ~ spl3_33 ),
    inference(avatar_split_clause,[],[f3896,f674,f651,f3898,f2791])).

fof(f651,plain,
    ( spl3_28
  <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f674,plain,
    ( spl3_33
  <=> sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).

fof(f3896,plain,
    ( ! [X9] :
        ( sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
        | ~ m1_subset_1(X9,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) )
    | ~ spl3_28
    | ~ spl3_33 ),
    inference(subsumption_resolution,[],[f3852,f653])).

fof(f653,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl3_28 ),
    inference(avatar_component_clause,[],[f651])).

fof(f3852,plain,
    ( ! [X9] :
        ( sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
        | ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
        | ~ m1_subset_1(X9,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) )
    | ~ spl3_33 ),
    inference(superposition,[],[f782,f676])).

fof(f676,plain,
    ( sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))
    | ~ spl3_33 ),
    inference(avatar_component_clause,[],[f674])).

fof(f782,plain,(
    ! [X4,X2,X3] :
      ( k3_subset_1(X2,X3) = k4_xboole_0(k3_subset_1(X2,X3),X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
      | ~ m1_subset_1(X4,k1_zfmisc_1(X2)) ) ),
    inference(subsumption_resolution,[],[f777,f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f777,plain,(
    ! [X4,X2,X3] :
      ( k3_subset_1(X2,X3) = k4_xboole_0(k3_subset_1(X2,X3),X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
      | ~ m1_subset_1(X4,k1_zfmisc_1(X2))
      | ~ m1_subset_1(k3_subset_1(X2,X3),k1_zfmisc_1(X2)) ) ),
    inference(superposition,[],[f311,f75])).

fof(f311,plain,(
    ! [X4,X5,X3] :
      ( k3_subset_1(X3,X4) = k7_subset_1(X3,k3_subset_1(X3,X4),X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(X3)) ) ),
    inference(subsumption_resolution,[],[f307,f92])).

fof(f307,plain,(
    ! [X4,X5,X3] :
      ( k3_subset_1(X3,X4) = k7_subset_1(X3,k3_subset_1(X3,X4),X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
      | ~ m1_subset_1(k3_subset_1(X3,X4),k1_zfmisc_1(X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(X3)) ) ),
    inference(superposition,[],[f84,f103])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k9_subset_1)).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_subset_1)).

fof(f2757,plain,
    ( ~ spl3_76
    | spl3_77
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f2756,f604,f2560,f2556])).

fof(f2556,plain,
    ( spl3_76
  <=> r1_tarski(sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_76])])).

fof(f604,plain,
    ( spl3_20
  <=> r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f2756,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | ~ spl3_20 ),
    inference(resolution,[],[f605,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f605,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f604])).

fof(f2742,plain,
    ( spl3_33
    | ~ spl3_10
    | ~ spl3_32 ),
    inference(avatar_split_clause,[],[f2741,f670,f237,f674])).

fof(f237,plain,
    ( spl3_10
  <=> k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f670,plain,
    ( spl3_32
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).

fof(f2741,plain,
    ( sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))
    | ~ spl3_10
    | ~ spl3_32 ),
    inference(subsumption_resolution,[],[f2716,f671])).

fof(f671,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl3_32 ),
    inference(avatar_component_clause,[],[f670])).

fof(f2716,plain,
    ( sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl3_10 ),
    inference(superposition,[],[f220,f239])).

fof(f239,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f237])).

fof(f220,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k4_xboole_0(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f216])).

fof(f216,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k4_xboole_0(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(superposition,[],[f79,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f79,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f2739,plain,
    ( spl3_28
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f2711,f237,f651])).

fof(f2711,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl3_10 ),
    inference(superposition,[],[f156,f239])).

fof(f2702,plain,
    ( spl3_10
    | ~ spl3_2
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f2701,f233,f115,f237])).

fof(f115,plain,
    ( spl3_2
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f233,plain,
    ( spl3_9
  <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f2701,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ spl3_2
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f2698,f234])).

fof(f234,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f233])).

fof(f2698,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_2 ),
    inference(superposition,[],[f75,f116])).

fof(f116,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f115])).

fof(f2692,plain,
    ( ~ spl3_3
    | ~ spl3_4
    | spl3_10
    | ~ spl3_77 ),
    inference(avatar_contradiction_clause,[],[f2691])).

fof(f2691,plain,
    ( $false
    | ~ spl3_3
    | ~ spl3_4
    | spl3_10
    | ~ spl3_77 ),
    inference(subsumption_resolution,[],[f2690,f128])).

fof(f2690,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl3_3
    | spl3_10
    | ~ spl3_77 ),
    inference(subsumption_resolution,[],[f2689,f123])).

fof(f2689,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl3_10
    | ~ spl3_77 ),
    inference(subsumption_resolution,[],[f2686,f238])).

fof(f238,plain,
    ( k2_tops_1(sK0,sK1) != k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | spl3_10 ),
    inference(avatar_component_clause,[],[f237])).

fof(f2686,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_77 ),
    inference(superposition,[],[f916,f2562])).

fof(f2562,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ spl3_77 ),
    inference(avatar_component_clause,[],[f2560])).

fof(f916,plain,(
    ! [X2,X3] :
      ( k2_tops_1(X2,X3) = k4_xboole_0(k2_pre_topc(X2,X3),k1_tops_1(X2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2) ) ),
    inference(subsumption_resolution,[],[f316,f298])).

fof(f298,plain,(
    ! [X2,X3] :
      ( m1_subset_1(k2_pre_topc(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2) ) ),
    inference(subsumption_resolution,[],[f291,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(f291,plain,(
    ! [X2,X3] :
      ( m1_subset_1(k2_pre_topc(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2) ) ),
    inference(duplicate_literal_removal,[],[f290])).

fof(f290,plain,(
    ! [X2,X3] :
      ( m1_subset_1(k2_pre_topc(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2) ) ),
    inference(superposition,[],[f104,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

fof(f316,plain,(
    ! [X2,X3] :
      ( k2_tops_1(X2,X3) = k4_xboole_0(k2_pre_topc(X2,X3),k1_tops_1(X2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2)
      | ~ m1_subset_1(k2_pre_topc(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) ) ),
    inference(superposition,[],[f85,f75])).

fof(f85,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

fof(f2638,plain,
    ( ~ spl3_1
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_6
    | spl3_76 ),
    inference(avatar_contradiction_clause,[],[f2637])).

fof(f2637,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_6
    | spl3_76 ),
    inference(subsumption_resolution,[],[f2636,f108])).

fof(f108,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f66])).

fof(f2636,plain,
    ( ~ r1_tarski(sK1,sK1)
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_6
    | spl3_76 ),
    inference(subsumption_resolution,[],[f2628,f112])).

fof(f112,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl3_1
  <=> v3_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f2628,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | ~ r1_tarski(sK1,sK1)
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_6
    | spl3_76 ),
    inference(resolution,[],[f2558,f338])).

fof(f338,plain,
    ( ! [X0] :
        ( r1_tarski(X0,k1_tops_1(sK0,sK1))
        | ~ v3_pre_topc(X0,sK0)
        | ~ r1_tarski(X0,sK1) )
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f331,f189])).

fof(f189,plain,
    ( ! [X13] :
        ( r1_tarski(X13,u1_struct_0(sK0))
        | ~ r1_tarski(X13,sK1) )
    | ~ spl3_6 ),
    inference(resolution,[],[f99,f153])).

fof(f153,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f151])).

fof(f151,plain,
    ( spl3_6
  <=> r1_tarski(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f331,plain,
    ( ! [X0] :
        ( ~ v3_pre_topc(X0,sK0)
        | r1_tarski(X0,k1_tops_1(sK0,sK1))
        | ~ r1_tarski(X0,sK1)
        | ~ r1_tarski(X0,u1_struct_0(sK0)) )
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(resolution,[],[f326,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f326,plain,
    ( ! [X16] :
        ( ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X16,sK0)
        | r1_tarski(X16,k1_tops_1(sK0,sK1))
        | ~ r1_tarski(X16,sK1) )
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f323,f128])).

fof(f323,plain,
    ( ! [X16] :
        ( ~ r1_tarski(X16,sK1)
        | ~ v3_pre_topc(X16,sK0)
        | r1_tarski(X16,k1_tops_1(sK0,sK1))
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl3_3 ),
    inference(resolution,[],[f89,f123])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X1,X2)
      | ~ v3_pre_topc(X1,X0)
      | r1_tarski(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r1_tarski(X1,X2)
                  & v3_pre_topc(X1,X0) )
               => r1_tarski(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_1)).

fof(f2558,plain,
    ( ~ r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | spl3_76 ),
    inference(avatar_component_clause,[],[f2556])).

fof(f2540,plain,
    ( spl3_61
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f2539,f126,f121,f1810])).

fof(f1810,plain,
    ( spl3_61
  <=> r1_tarski(sK1,k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_61])])).

fof(f2539,plain,
    ( r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f2530,f128])).

fof(f2530,plain,
    ( r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_3 ),
    inference(resolution,[],[f714,f123])).

fof(f714,plain,(
    ! [X8,X7] :
      ( ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X8)))
      | r1_tarski(X7,k2_pre_topc(X8,X7))
      | ~ l1_pre_topc(X8) ) ),
    inference(superposition,[],[f100,f296])).

fof(f296,plain,(
    ! [X2,X3] :
      ( k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2) ) ),
    inference(subsumption_resolution,[],[f293,f87])).

fof(f293,plain,(
    ! [X2,X3] :
      ( k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2)
      | ~ m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) ) ),
    inference(duplicate_literal_removal,[],[f288])).

fof(f288,plain,(
    ! [X2,X3] :
      ( k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2)
      | ~ m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ) ),
    inference(superposition,[],[f86,f101])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f100,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f2520,plain,
    ( spl3_20
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f2519,f126,f121,f604])).

fof(f2519,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f2509,f128])).

fof(f2509,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl3_3 ),
    inference(resolution,[],[f697,f123])).

fof(f697,plain,(
    ! [X4,X5] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X5)))
      | r1_tarski(k1_tops_1(X5,X4),X4)
      | ~ l1_pre_topc(X5) ) ),
    inference(superposition,[],[f98,f283])).

fof(f98,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f1900,plain,
    ( ~ spl3_9
    | ~ spl3_10
    | spl3_2 ),
    inference(avatar_split_clause,[],[f1899,f115,f237,f233])).

fof(f1899,plain,
    ( k2_tops_1(sK0,sK1) != k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_2 ),
    inference(superposition,[],[f117,f75])).

fof(f117,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f115])).

fof(f1813,plain,
    ( ~ spl3_61
    | spl3_32 ),
    inference(avatar_split_clause,[],[f1808,f670,f1810])).

fof(f1808,plain,
    ( ~ r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | spl3_32 ),
    inference(resolution,[],[f672,f91])).

fof(f672,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | spl3_32 ),
    inference(avatar_component_clause,[],[f670])).

fof(f588,plain,
    ( ~ spl3_3
    | ~ spl3_4
    | spl3_9 ),
    inference(avatar_contradiction_clause,[],[f587])).

fof(f587,plain,
    ( $false
    | ~ spl3_3
    | ~ spl3_4
    | spl3_9 ),
    inference(subsumption_resolution,[],[f586,f128])).

fof(f586,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl3_3
    | spl3_9 ),
    inference(subsumption_resolution,[],[f579,f123])).

fof(f579,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl3_9 ),
    inference(resolution,[],[f298,f235])).

fof(f235,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_9 ),
    inference(avatar_component_clause,[],[f233])).

fof(f262,plain,
    ( spl3_12
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f257,f131,f126,f121,f259])).

fof(f259,plain,
    ( spl3_12
  <=> v3_pre_topc(k1_tops_1(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f131,plain,
    ( spl3_5
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f257,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f256,f133])).

fof(f133,plain,
    ( v2_pre_topc(sK0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f131])).

fof(f256,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f253,f128])).

fof(f253,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl3_3 ),
    inference(resolution,[],[f88,f123])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

fof(f154,plain,
    ( spl3_6
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f147,f121,f151])).

fof(f147,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl3_3 ),
    inference(resolution,[],[f90,f123])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f134,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f70,f131])).

fof(f70,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,
    ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
      | ~ v3_pre_topc(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
      | v3_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f61,f63,f62])).

fof(f62,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
              | ~ v3_pre_topc(X1,X0) )
            & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
              | v3_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ( k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1)
            | ~ v3_pre_topc(X1,sK0) )
          & ( k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1)
            | v3_pre_topc(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,
    ( ? [X1] :
        ( ( k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1)
          | ~ v3_pre_topc(X1,sK0) )
        & ( k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1)
          | v3_pre_topc(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
        | ~ v3_pre_topc(sK1,sK0) )
      & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
        | v3_pre_topc(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f60])).

fof(f60,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    inference(negated_conjecture,[],[f32])).

fof(f32,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tops_1)).

fof(f129,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f71,f126])).

fof(f71,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f64])).

fof(f124,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f72,f121])).

fof(f72,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f64])).

fof(f119,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f73,f115,f111])).

fof(f73,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f64])).

fof(f118,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f74,f115,f111])).

fof(f74,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f64])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n009.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:12:11 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.21/0.49  % (15423)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.52  % (15445)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.52  % (15426)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.52  % (15428)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.52  % (15437)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.52  % (15431)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.52  % (15425)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.52  % (15429)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (15442)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.53  % (15441)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.53  % (15446)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.54  % (15438)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.54  % (15435)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.54  % (15427)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.54  % (15449)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (15436)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.54  % (15424)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.54  % (15432)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.54  % (15430)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.54  % (15448)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.55  % (15450)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.55  % (15451)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.55  % (15443)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.55  % (15433)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.55  % (15440)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.55  % (15447)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.55  % (15444)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.49/0.56  % (15434)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.49/0.56  % (15439)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.49/0.56  % (15452)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 3.15/0.80  % (15447)Time limit reached!
% 3.15/0.80  % (15447)------------------------------
% 3.15/0.80  % (15447)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.15/0.80  % (15447)Termination reason: Time limit
% 3.15/0.80  % (15447)Termination phase: Saturation
% 3.15/0.80  
% 3.15/0.80  % (15447)Memory used [KB]: 12792
% 3.15/0.80  % (15447)Time elapsed: 0.400 s
% 3.15/0.80  % (15447)------------------------------
% 3.15/0.80  % (15447)------------------------------
% 3.15/0.83  % (15425)Time limit reached!
% 3.15/0.83  % (15425)------------------------------
% 3.15/0.83  % (15425)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.15/0.83  % (15425)Termination reason: Time limit
% 3.15/0.83  % (15425)Termination phase: Saturation
% 3.15/0.83  
% 3.15/0.83  % (15425)Memory used [KB]: 6524
% 3.15/0.83  % (15425)Time elapsed: 0.400 s
% 3.15/0.83  % (15425)------------------------------
% 3.15/0.83  % (15425)------------------------------
% 3.95/0.90  % (15464)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 3.95/0.91  % (15452)Time limit reached!
% 3.95/0.91  % (15452)------------------------------
% 3.95/0.91  % (15452)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.95/0.91  % (15452)Termination reason: Time limit
% 3.95/0.91  
% 3.95/0.91  % (15452)Memory used [KB]: 3454
% 3.95/0.91  % (15452)Time elapsed: 0.509 s
% 3.95/0.91  % (15452)------------------------------
% 3.95/0.91  % (15452)------------------------------
% 3.95/0.92  % (15437)Time limit reached!
% 3.95/0.92  % (15437)------------------------------
% 3.95/0.92  % (15437)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.95/0.92  % (15437)Termination reason: Time limit
% 3.95/0.92  % (15437)Termination phase: Saturation
% 3.95/0.92  
% 3.95/0.92  % (15437)Memory used [KB]: 7164
% 3.95/0.92  % (15437)Time elapsed: 0.507 s
% 3.95/0.92  % (15437)------------------------------
% 3.95/0.92  % (15437)------------------------------
% 3.95/0.92  % (15429)Time limit reached!
% 3.95/0.92  % (15429)------------------------------
% 3.95/0.92  % (15429)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.95/0.92  % (15429)Termination reason: Time limit
% 3.95/0.92  
% 3.95/0.92  % (15429)Memory used [KB]: 15095
% 3.95/0.92  % (15429)Time elapsed: 0.519 s
% 3.95/0.92  % (15429)------------------------------
% 3.95/0.92  % (15429)------------------------------
% 4.49/0.96  % (15465)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 4.49/1.02  % (15467)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 4.96/1.04  % (15430)Time limit reached!
% 4.96/1.04  % (15430)------------------------------
% 4.96/1.04  % (15430)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.96/1.04  % (15430)Termination reason: Time limit
% 4.96/1.04  
% 4.96/1.04  % (15430)Memory used [KB]: 6268
% 4.96/1.04  % (15430)Time elapsed: 0.606 s
% 4.96/1.04  % (15430)------------------------------
% 4.96/1.04  % (15430)------------------------------
% 4.96/1.05  % (15466)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 4.96/1.07  % (15468)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 6.41/1.21  % (15469)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 6.41/1.22  % (15424)Time limit reached!
% 6.41/1.22  % (15424)------------------------------
% 6.41/1.22  % (15424)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.41/1.22  % (15424)Termination reason: Time limit
% 6.41/1.22  
% 6.41/1.22  % (15424)Memory used [KB]: 6780
% 6.41/1.22  % (15424)Time elapsed: 0.818 s
% 6.41/1.22  % (15424)------------------------------
% 6.41/1.22  % (15424)------------------------------
% 7.42/1.32  % (15470)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 7.42/1.33  % (15426)Time limit reached!
% 7.42/1.33  % (15426)------------------------------
% 7.42/1.33  % (15426)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.42/1.33  % (15426)Termination reason: Time limit
% 7.42/1.33  
% 7.42/1.33  % (15426)Memory used [KB]: 7291
% 7.42/1.33  % (15426)Time elapsed: 0.927 s
% 7.42/1.33  % (15426)------------------------------
% 7.42/1.33  % (15426)------------------------------
% 7.42/1.36  % (15444)Refutation found. Thanks to Tanya!
% 7.42/1.36  % SZS status Theorem for theBenchmark
% 7.42/1.36  % SZS output start Proof for theBenchmark
% 7.42/1.36  fof(f4031,plain,(
% 7.42/1.36    $false),
% 7.42/1.36    inference(avatar_sat_refutation,[],[f118,f119,f124,f129,f134,f154,f262,f588,f1813,f1900,f2520,f2540,f2638,f2692,f2702,f2739,f2742,f2757,f3901,f3946,f4024,f4030])).
% 7.42/1.36  fof(f4030,plain,(
% 7.42/1.36    sK1 != k1_tops_1(sK0,sK1) | v3_pre_topc(sK1,sK0) | ~v3_pre_topc(k1_tops_1(sK0,sK1),sK0)),
% 7.42/1.36    introduced(theory_tautology_sat_conflict,[])).
% 7.42/1.36  fof(f4024,plain,(
% 7.42/1.36    ~spl3_80),
% 7.42/1.36    inference(avatar_contradiction_clause,[],[f3997])).
% 7.42/1.36  fof(f3997,plain,(
% 7.42/1.36    $false | ~spl3_80),
% 7.42/1.36    inference(unit_resulting_resolution,[],[f156,f93,f2792,f104])).
% 7.42/1.36  fof(f104,plain,(
% 7.42/1.36    ( ! [X2,X0,X1] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.42/1.36    inference(cnf_transformation,[],[f59])).
% 7.42/1.36  fof(f59,plain,(
% 7.42/1.36    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.42/1.36    inference(flattening,[],[f58])).
% 7.42/1.36  fof(f58,plain,(
% 7.42/1.36    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 7.42/1.36    inference(ennf_transformation,[],[f14])).
% 7.42/1.36  fof(f14,axiom,(
% 7.42/1.36    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 7.42/1.36    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).
% 7.42/1.36  fof(f2792,plain,(
% 7.42/1.36    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))) ) | ~spl3_80),
% 7.42/1.36    inference(avatar_component_clause,[],[f2791])).
% 7.42/1.36  fof(f2791,plain,(
% 7.42/1.36    spl3_80 <=> ! [X2] : ~m1_subset_1(X2,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))),
% 7.42/1.36    introduced(avatar_definition,[new_symbols(naming,[spl3_80])])).
% 7.42/1.36  fof(f93,plain,(
% 7.42/1.36    ( ! [X0] : (m1_subset_1(sK2(X0),X0)) )),
% 7.42/1.36    inference(cnf_transformation,[],[f69])).
% 7.42/1.36  fof(f69,plain,(
% 7.42/1.36    ! [X0] : m1_subset_1(sK2(X0),X0)),
% 7.42/1.36    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f16,f68])).
% 7.42/1.36  fof(f68,plain,(
% 7.42/1.36    ! [X0] : (? [X1] : m1_subset_1(X1,X0) => m1_subset_1(sK2(X0),X0))),
% 7.42/1.36    introduced(choice_axiom,[])).
% 7.42/1.36  fof(f16,axiom,(
% 7.42/1.36    ! [X0] : ? [X1] : m1_subset_1(X1,X0)),
% 7.42/1.36    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).
% 7.42/1.36  fof(f156,plain,(
% 7.42/1.36    ( ! [X0,X1] : (m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0))) )),
% 7.42/1.36    inference(backward_demodulation,[],[f107,f97])).
% 7.42/1.36  fof(f97,plain,(
% 7.42/1.36    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 7.42/1.36    inference(cnf_transformation,[],[f20])).
% 7.42/1.36  fof(f20,axiom,(
% 7.42/1.36    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 7.42/1.36    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 7.42/1.36  fof(f107,plain,(
% 7.42/1.36    ( ! [X0,X1] : (m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 7.42/1.36    inference(cnf_transformation,[],[f15])).
% 7.42/1.36  fof(f15,axiom,(
% 7.42/1.36    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))),
% 7.42/1.36    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).
% 7.42/1.36  fof(f3946,plain,(
% 7.42/1.36    spl3_77 | ~spl3_3 | ~spl3_4 | ~spl3_118),
% 7.42/1.36    inference(avatar_split_clause,[],[f3945,f3898,f126,f121,f2560])).
% 7.42/1.36  fof(f2560,plain,(
% 7.42/1.36    spl3_77 <=> sK1 = k1_tops_1(sK0,sK1)),
% 7.42/1.36    introduced(avatar_definition,[new_symbols(naming,[spl3_77])])).
% 7.42/1.36  fof(f121,plain,(
% 7.42/1.36    spl3_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 7.42/1.36    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 7.42/1.36  fof(f126,plain,(
% 7.42/1.36    spl3_4 <=> l1_pre_topc(sK0)),
% 7.42/1.36    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 7.42/1.36  fof(f3898,plain,(
% 7.42/1.36    spl3_118 <=> sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 7.42/1.36    introduced(avatar_definition,[new_symbols(naming,[spl3_118])])).
% 7.42/1.36  fof(f3945,plain,(
% 7.42/1.36    sK1 = k1_tops_1(sK0,sK1) | (~spl3_3 | ~spl3_4 | ~spl3_118)),
% 7.42/1.36    inference(subsumption_resolution,[],[f3944,f128])).
% 7.42/1.36  fof(f128,plain,(
% 7.42/1.36    l1_pre_topc(sK0) | ~spl3_4),
% 7.42/1.36    inference(avatar_component_clause,[],[f126])).
% 7.42/1.36  fof(f3944,plain,(
% 7.42/1.36    sK1 = k1_tops_1(sK0,sK1) | ~l1_pre_topc(sK0) | (~spl3_3 | ~spl3_118)),
% 7.42/1.36    inference(subsumption_resolution,[],[f3910,f123])).
% 7.42/1.36  fof(f123,plain,(
% 7.42/1.36    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_3),
% 7.42/1.36    inference(avatar_component_clause,[],[f121])).
% 7.42/1.36  fof(f3910,plain,(
% 7.42/1.36    sK1 = k1_tops_1(sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl3_118),
% 7.42/1.36    inference(superposition,[],[f283,f3900])).
% 7.42/1.36  fof(f3900,plain,(
% 7.42/1.36    sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl3_118),
% 7.42/1.36    inference(avatar_component_clause,[],[f3898])).
% 7.42/1.36  fof(f283,plain,(
% 7.42/1.36    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.42/1.36    inference(duplicate_literal_removal,[],[f282])).
% 7.42/1.36  fof(f282,plain,(
% 7.42/1.36    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.42/1.36    inference(superposition,[],[f75,f82])).
% 7.42/1.36  fof(f82,plain,(
% 7.42/1.36    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.42/1.36    inference(cnf_transformation,[],[f39])).
% 7.42/1.36  fof(f39,plain,(
% 7.42/1.36    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.42/1.36    inference(ennf_transformation,[],[f31])).
% 7.42/1.36  fof(f31,axiom,(
% 7.42/1.36    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 7.42/1.36    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).
% 7.42/1.36  fof(f75,plain,(
% 7.42/1.36    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.42/1.36    inference(cnf_transformation,[],[f36])).
% 7.42/1.36  fof(f36,plain,(
% 7.42/1.36    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.42/1.36    inference(ennf_transformation,[],[f21])).
% 7.42/1.36  fof(f21,axiom,(
% 7.42/1.36    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 7.42/1.36    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 7.42/1.36  fof(f3901,plain,(
% 7.42/1.36    spl3_80 | spl3_118 | ~spl3_28 | ~spl3_33),
% 7.42/1.36    inference(avatar_split_clause,[],[f3896,f674,f651,f3898,f2791])).
% 7.42/1.36  fof(f651,plain,(
% 7.42/1.36    spl3_28 <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))),
% 7.42/1.36    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 7.42/1.36  fof(f674,plain,(
% 7.42/1.36    spl3_33 <=> sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))),
% 7.42/1.36    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).
% 7.42/1.36  fof(f3896,plain,(
% 7.42/1.36    ( ! [X9] : (sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~m1_subset_1(X9,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))) ) | (~spl3_28 | ~spl3_33)),
% 7.42/1.36    inference(subsumption_resolution,[],[f3852,f653])).
% 7.42/1.36  fof(f653,plain,(
% 7.42/1.36    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~spl3_28),
% 7.42/1.36    inference(avatar_component_clause,[],[f651])).
% 7.42/1.36  fof(f3852,plain,(
% 7.42/1.36    ( ! [X9] : (sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~m1_subset_1(X9,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))) ) | ~spl3_33),
% 7.42/1.36    inference(superposition,[],[f782,f676])).
% 7.42/1.36  fof(f676,plain,(
% 7.42/1.36    sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) | ~spl3_33),
% 7.42/1.36    inference(avatar_component_clause,[],[f674])).
% 7.42/1.36  fof(f782,plain,(
% 7.42/1.36    ( ! [X4,X2,X3] : (k3_subset_1(X2,X3) = k4_xboole_0(k3_subset_1(X2,X3),X3) | ~m1_subset_1(X3,k1_zfmisc_1(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(X2))) )),
% 7.42/1.36    inference(subsumption_resolution,[],[f777,f92])).
% 7.42/1.36  fof(f92,plain,(
% 7.42/1.36    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.42/1.36    inference(cnf_transformation,[],[f50])).
% 7.42/1.36  fof(f50,plain,(
% 7.42/1.36    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.42/1.36    inference(ennf_transformation,[],[f13])).
% 7.42/1.36  fof(f13,axiom,(
% 7.42/1.36    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 7.42/1.36    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 7.42/1.36  fof(f777,plain,(
% 7.42/1.36    ( ! [X4,X2,X3] : (k3_subset_1(X2,X3) = k4_xboole_0(k3_subset_1(X2,X3),X3) | ~m1_subset_1(X3,k1_zfmisc_1(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(X2)) | ~m1_subset_1(k3_subset_1(X2,X3),k1_zfmisc_1(X2))) )),
% 7.42/1.36    inference(superposition,[],[f311,f75])).
% 7.42/1.36  fof(f311,plain,(
% 7.42/1.36    ( ! [X4,X5,X3] : (k3_subset_1(X3,X4) = k7_subset_1(X3,k3_subset_1(X3,X4),X4) | ~m1_subset_1(X4,k1_zfmisc_1(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(X3))) )),
% 7.42/1.36    inference(subsumption_resolution,[],[f307,f92])).
% 7.42/1.36  fof(f307,plain,(
% 7.42/1.36    ( ! [X4,X5,X3] : (k3_subset_1(X3,X4) = k7_subset_1(X3,k3_subset_1(X3,X4),X4) | ~m1_subset_1(X4,k1_zfmisc_1(X3)) | ~m1_subset_1(k3_subset_1(X3,X4),k1_zfmisc_1(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(X3))) )),
% 7.42/1.36    inference(superposition,[],[f84,f103])).
% 7.42/1.36  fof(f103,plain,(
% 7.42/1.36    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X1) = X1 | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 7.42/1.36    inference(cnf_transformation,[],[f57])).
% 7.42/1.36  fof(f57,plain,(
% 7.42/1.36    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X1) = X1 | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 7.42/1.36    inference(ennf_transformation,[],[f17])).
% 7.42/1.36  fof(f17,axiom,(
% 7.42/1.36    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X1) = X1)),
% 7.42/1.36    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k9_subset_1)).
% 7.42/1.36  fof(f84,plain,(
% 7.42/1.36    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.42/1.36    inference(cnf_transformation,[],[f41])).
% 7.42/1.36  fof(f41,plain,(
% 7.42/1.36    ! [X0,X1] : (! [X2] : (k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.42/1.36    inference(ennf_transformation,[],[f22])).
% 7.42/1.36  fof(f22,axiom,(
% 7.42/1.36    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))))),
% 7.42/1.36    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_subset_1)).
% 7.42/1.36  fof(f2757,plain,(
% 7.42/1.36    ~spl3_76 | spl3_77 | ~spl3_20),
% 7.42/1.36    inference(avatar_split_clause,[],[f2756,f604,f2560,f2556])).
% 7.42/1.36  fof(f2556,plain,(
% 7.42/1.36    spl3_76 <=> r1_tarski(sK1,k1_tops_1(sK0,sK1))),
% 7.42/1.36    introduced(avatar_definition,[new_symbols(naming,[spl3_76])])).
% 7.42/1.36  fof(f604,plain,(
% 7.42/1.36    spl3_20 <=> r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 7.42/1.36    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 7.42/1.36  fof(f2756,plain,(
% 7.42/1.36    sK1 = k1_tops_1(sK0,sK1) | ~r1_tarski(sK1,k1_tops_1(sK0,sK1)) | ~spl3_20),
% 7.42/1.36    inference(resolution,[],[f605,f78])).
% 7.42/1.36  fof(f78,plain,(
% 7.42/1.36    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 7.42/1.36    inference(cnf_transformation,[],[f66])).
% 7.42/1.36  fof(f66,plain,(
% 7.42/1.36    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.42/1.36    inference(flattening,[],[f65])).
% 7.42/1.36  fof(f65,plain,(
% 7.42/1.36    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.42/1.36    inference(nnf_transformation,[],[f2])).
% 7.42/1.36  fof(f2,axiom,(
% 7.42/1.36    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.42/1.36    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 7.42/1.36  fof(f605,plain,(
% 7.42/1.36    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~spl3_20),
% 7.42/1.36    inference(avatar_component_clause,[],[f604])).
% 7.42/1.36  fof(f2742,plain,(
% 7.42/1.36    spl3_33 | ~spl3_10 | ~spl3_32),
% 7.42/1.36    inference(avatar_split_clause,[],[f2741,f670,f237,f674])).
% 7.42/1.36  fof(f237,plain,(
% 7.42/1.36    spl3_10 <=> k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)),
% 7.42/1.36    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 7.42/1.36  fof(f670,plain,(
% 7.42/1.36    spl3_32 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))),
% 7.42/1.36    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).
% 7.42/1.36  fof(f2741,plain,(
% 7.42/1.36    sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) | (~spl3_10 | ~spl3_32)),
% 7.42/1.36    inference(subsumption_resolution,[],[f2716,f671])).
% 7.42/1.36  fof(f671,plain,(
% 7.42/1.36    m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~spl3_32),
% 7.42/1.36    inference(avatar_component_clause,[],[f670])).
% 7.42/1.36  fof(f2716,plain,(
% 7.42/1.36    sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~spl3_10),
% 7.42/1.36    inference(superposition,[],[f220,f239])).
% 7.42/1.36  fof(f239,plain,(
% 7.42/1.36    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~spl3_10),
% 7.42/1.36    inference(avatar_component_clause,[],[f237])).
% 7.42/1.36  fof(f220,plain,(
% 7.42/1.36    ( ! [X0,X1] : (k3_subset_1(X0,k4_xboole_0(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.42/1.36    inference(duplicate_literal_removal,[],[f216])).
% 7.42/1.36  fof(f216,plain,(
% 7.42/1.36    ( ! [X0,X1] : (k3_subset_1(X0,k4_xboole_0(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.42/1.36    inference(superposition,[],[f79,f80])).
% 7.42/1.36  fof(f80,plain,(
% 7.42/1.36    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.42/1.36    inference(cnf_transformation,[],[f38])).
% 7.42/1.36  fof(f38,plain,(
% 7.42/1.36    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.42/1.36    inference(ennf_transformation,[],[f12])).
% 7.42/1.36  fof(f12,axiom,(
% 7.42/1.36    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 7.42/1.36    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 7.42/1.36  fof(f79,plain,(
% 7.42/1.36    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.42/1.36    inference(cnf_transformation,[],[f37])).
% 7.42/1.36  fof(f37,plain,(
% 7.42/1.36    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.42/1.36    inference(ennf_transformation,[],[f18])).
% 7.42/1.36  fof(f18,axiom,(
% 7.42/1.36    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 7.42/1.36    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 7.42/1.36  fof(f2739,plain,(
% 7.42/1.36    spl3_28 | ~spl3_10),
% 7.42/1.36    inference(avatar_split_clause,[],[f2711,f237,f651])).
% 7.42/1.36  fof(f2711,plain,(
% 7.42/1.36    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~spl3_10),
% 7.42/1.36    inference(superposition,[],[f156,f239])).
% 7.42/1.36  fof(f2702,plain,(
% 7.42/1.36    spl3_10 | ~spl3_2 | ~spl3_9),
% 7.42/1.36    inference(avatar_split_clause,[],[f2701,f233,f115,f237])).
% 7.42/1.36  fof(f115,plain,(
% 7.42/1.36    spl3_2 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)),
% 7.42/1.36    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 7.42/1.36  fof(f233,plain,(
% 7.42/1.36    spl3_9 <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 7.42/1.36    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 7.42/1.36  fof(f2701,plain,(
% 7.42/1.36    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | (~spl3_2 | ~spl3_9)),
% 7.42/1.36    inference(subsumption_resolution,[],[f2698,f234])).
% 7.42/1.36  fof(f234,plain,(
% 7.42/1.36    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_9),
% 7.42/1.36    inference(avatar_component_clause,[],[f233])).
% 7.42/1.36  fof(f2698,plain,(
% 7.42/1.36    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_2),
% 7.42/1.36    inference(superposition,[],[f75,f116])).
% 7.42/1.36  fof(f116,plain,(
% 7.42/1.36    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~spl3_2),
% 7.42/1.36    inference(avatar_component_clause,[],[f115])).
% 7.42/1.36  fof(f2692,plain,(
% 7.42/1.36    ~spl3_3 | ~spl3_4 | spl3_10 | ~spl3_77),
% 7.42/1.36    inference(avatar_contradiction_clause,[],[f2691])).
% 7.42/1.36  fof(f2691,plain,(
% 7.42/1.36    $false | (~spl3_3 | ~spl3_4 | spl3_10 | ~spl3_77)),
% 7.42/1.36    inference(subsumption_resolution,[],[f2690,f128])).
% 7.42/1.36  fof(f2690,plain,(
% 7.42/1.36    ~l1_pre_topc(sK0) | (~spl3_3 | spl3_10 | ~spl3_77)),
% 7.42/1.36    inference(subsumption_resolution,[],[f2689,f123])).
% 7.42/1.36  fof(f2689,plain,(
% 7.42/1.36    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (spl3_10 | ~spl3_77)),
% 7.42/1.36    inference(subsumption_resolution,[],[f2686,f238])).
% 7.42/1.36  fof(f238,plain,(
% 7.42/1.36    k2_tops_1(sK0,sK1) != k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | spl3_10),
% 7.42/1.36    inference(avatar_component_clause,[],[f237])).
% 7.42/1.36  fof(f2686,plain,(
% 7.42/1.36    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl3_77),
% 7.42/1.36    inference(superposition,[],[f916,f2562])).
% 7.42/1.36  fof(f2562,plain,(
% 7.42/1.36    sK1 = k1_tops_1(sK0,sK1) | ~spl3_77),
% 7.42/1.36    inference(avatar_component_clause,[],[f2560])).
% 7.42/1.36  fof(f916,plain,(
% 7.42/1.36    ( ! [X2,X3] : (k2_tops_1(X2,X3) = k4_xboole_0(k2_pre_topc(X2,X3),k1_tops_1(X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2)) )),
% 7.42/1.36    inference(subsumption_resolution,[],[f316,f298])).
% 7.42/1.36  fof(f298,plain,(
% 7.42/1.36    ( ! [X2,X3] : (m1_subset_1(k2_pre_topc(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2)) )),
% 7.42/1.36    inference(subsumption_resolution,[],[f291,f87])).
% 7.42/1.36  fof(f87,plain,(
% 7.42/1.36    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.42/1.36    inference(cnf_transformation,[],[f45])).
% 7.42/1.36  fof(f45,plain,(
% 7.42/1.36    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 7.42/1.36    inference(flattening,[],[f44])).
% 7.42/1.36  fof(f44,plain,(
% 7.42/1.36    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 7.42/1.36    inference(ennf_transformation,[],[f25])).
% 7.42/1.36  fof(f25,axiom,(
% 7.42/1.36    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 7.42/1.36    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).
% 7.42/1.36  fof(f291,plain,(
% 7.42/1.36    ( ! [X2,X3] : (m1_subset_1(k2_pre_topc(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) | ~m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2)) )),
% 7.42/1.36    inference(duplicate_literal_removal,[],[f290])).
% 7.42/1.36  fof(f290,plain,(
% 7.42/1.36    ( ! [X2,X3] : (m1_subset_1(k2_pre_topc(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) | ~m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2)) )),
% 7.42/1.36    inference(superposition,[],[f104,f86])).
% 7.42/1.36  fof(f86,plain,(
% 7.42/1.36    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.42/1.36    inference(cnf_transformation,[],[f43])).
% 7.42/1.36  fof(f43,plain,(
% 7.42/1.36    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.42/1.36    inference(ennf_transformation,[],[f30])).
% 7.42/1.36  fof(f30,axiom,(
% 7.42/1.36    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 7.42/1.36    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).
% 7.42/1.36  fof(f316,plain,(
% 7.42/1.36    ( ! [X2,X3] : (k2_tops_1(X2,X3) = k4_xboole_0(k2_pre_topc(X2,X3),k1_tops_1(X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2) | ~m1_subset_1(k2_pre_topc(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))) )),
% 7.42/1.36    inference(superposition,[],[f85,f75])).
% 7.42/1.36  fof(f85,plain,(
% 7.42/1.36    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.42/1.36    inference(cnf_transformation,[],[f42])).
% 7.42/1.36  fof(f42,plain,(
% 7.42/1.36    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.42/1.36    inference(ennf_transformation,[],[f27])).
% 7.42/1.36  fof(f27,axiom,(
% 7.42/1.36    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 7.42/1.36    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).
% 7.42/1.36  fof(f2638,plain,(
% 7.42/1.36    ~spl3_1 | ~spl3_3 | ~spl3_4 | ~spl3_6 | spl3_76),
% 7.42/1.36    inference(avatar_contradiction_clause,[],[f2637])).
% 7.42/1.36  fof(f2637,plain,(
% 7.42/1.36    $false | (~spl3_1 | ~spl3_3 | ~spl3_4 | ~spl3_6 | spl3_76)),
% 7.42/1.36    inference(subsumption_resolution,[],[f2636,f108])).
% 7.42/1.36  fof(f108,plain,(
% 7.42/1.36    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.42/1.36    inference(equality_resolution,[],[f77])).
% 7.42/1.36  fof(f77,plain,(
% 7.42/1.36    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 7.42/1.36    inference(cnf_transformation,[],[f66])).
% 7.42/1.36  fof(f2636,plain,(
% 7.42/1.36    ~r1_tarski(sK1,sK1) | (~spl3_1 | ~spl3_3 | ~spl3_4 | ~spl3_6 | spl3_76)),
% 7.42/1.36    inference(subsumption_resolution,[],[f2628,f112])).
% 7.42/1.36  fof(f112,plain,(
% 7.42/1.36    v3_pre_topc(sK1,sK0) | ~spl3_1),
% 7.42/1.36    inference(avatar_component_clause,[],[f111])).
% 7.42/1.36  fof(f111,plain,(
% 7.42/1.36    spl3_1 <=> v3_pre_topc(sK1,sK0)),
% 7.42/1.36    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 7.42/1.36  fof(f2628,plain,(
% 7.42/1.36    ~v3_pre_topc(sK1,sK0) | ~r1_tarski(sK1,sK1) | (~spl3_3 | ~spl3_4 | ~spl3_6 | spl3_76)),
% 7.42/1.36    inference(resolution,[],[f2558,f338])).
% 7.42/1.36  fof(f338,plain,(
% 7.42/1.36    ( ! [X0] : (r1_tarski(X0,k1_tops_1(sK0,sK1)) | ~v3_pre_topc(X0,sK0) | ~r1_tarski(X0,sK1)) ) | (~spl3_3 | ~spl3_4 | ~spl3_6)),
% 7.42/1.36    inference(subsumption_resolution,[],[f331,f189])).
% 7.42/1.36  fof(f189,plain,(
% 7.42/1.36    ( ! [X13] : (r1_tarski(X13,u1_struct_0(sK0)) | ~r1_tarski(X13,sK1)) ) | ~spl3_6),
% 7.42/1.36    inference(resolution,[],[f99,f153])).
% 7.42/1.36  fof(f153,plain,(
% 7.42/1.36    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl3_6),
% 7.42/1.36    inference(avatar_component_clause,[],[f151])).
% 7.42/1.36  fof(f151,plain,(
% 7.42/1.36    spl3_6 <=> r1_tarski(sK1,u1_struct_0(sK0))),
% 7.42/1.36    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 7.42/1.36  fof(f99,plain,(
% 7.42/1.36    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 7.42/1.36    inference(cnf_transformation,[],[f54])).
% 7.42/1.36  fof(f54,plain,(
% 7.42/1.36    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 7.42/1.36    inference(flattening,[],[f53])).
% 7.42/1.36  fof(f53,plain,(
% 7.42/1.36    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 7.42/1.36    inference(ennf_transformation,[],[f5])).
% 7.42/1.36  fof(f5,axiom,(
% 7.42/1.36    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 7.42/1.36    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 7.42/1.36  fof(f331,plain,(
% 7.42/1.36    ( ! [X0] : (~v3_pre_topc(X0,sK0) | r1_tarski(X0,k1_tops_1(sK0,sK1)) | ~r1_tarski(X0,sK1) | ~r1_tarski(X0,u1_struct_0(sK0))) ) | (~spl3_3 | ~spl3_4)),
% 7.42/1.36    inference(resolution,[],[f326,f91])).
% 7.42/1.36  fof(f91,plain,(
% 7.42/1.36    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 7.42/1.36    inference(cnf_transformation,[],[f67])).
% 7.42/1.36  fof(f67,plain,(
% 7.42/1.36    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 7.42/1.36    inference(nnf_transformation,[],[f24])).
% 7.42/1.36  fof(f24,axiom,(
% 7.42/1.36    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.42/1.36    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 7.42/1.36  fof(f326,plain,(
% 7.42/1.36    ( ! [X16] : (~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X16,sK0) | r1_tarski(X16,k1_tops_1(sK0,sK1)) | ~r1_tarski(X16,sK1)) ) | (~spl3_3 | ~spl3_4)),
% 7.42/1.36    inference(subsumption_resolution,[],[f323,f128])).
% 7.42/1.36  fof(f323,plain,(
% 7.42/1.36    ( ! [X16] : (~r1_tarski(X16,sK1) | ~v3_pre_topc(X16,sK0) | r1_tarski(X16,k1_tops_1(sK0,sK1)) | ~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) ) | ~spl3_3),
% 7.42/1.36    inference(resolution,[],[f89,f123])).
% 7.42/1.36  fof(f89,plain,(
% 7.42/1.36    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | r1_tarski(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.42/1.36    inference(cnf_transformation,[],[f49])).
% 7.42/1.36  fof(f49,plain,(
% 7.42/1.36    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.42/1.36    inference(flattening,[],[f48])).
% 7.42/1.36  fof(f48,plain,(
% 7.42/1.36    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(X1,k1_tops_1(X0,X2)) | (~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.42/1.36    inference(ennf_transformation,[],[f28])).
% 7.42/1.36  fof(f28,axiom,(
% 7.42/1.36    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v3_pre_topc(X1,X0)) => r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 7.42/1.36    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_1)).
% 7.42/1.36  fof(f2558,plain,(
% 7.42/1.36    ~r1_tarski(sK1,k1_tops_1(sK0,sK1)) | spl3_76),
% 7.42/1.36    inference(avatar_component_clause,[],[f2556])).
% 7.42/1.36  fof(f2540,plain,(
% 7.42/1.36    spl3_61 | ~spl3_3 | ~spl3_4),
% 7.42/1.36    inference(avatar_split_clause,[],[f2539,f126,f121,f1810])).
% 7.42/1.36  fof(f1810,plain,(
% 7.42/1.36    spl3_61 <=> r1_tarski(sK1,k2_pre_topc(sK0,sK1))),
% 7.42/1.36    introduced(avatar_definition,[new_symbols(naming,[spl3_61])])).
% 7.42/1.36  fof(f2539,plain,(
% 7.42/1.36    r1_tarski(sK1,k2_pre_topc(sK0,sK1)) | (~spl3_3 | ~spl3_4)),
% 7.42/1.36    inference(subsumption_resolution,[],[f2530,f128])).
% 7.42/1.36  fof(f2530,plain,(
% 7.42/1.36    r1_tarski(sK1,k2_pre_topc(sK0,sK1)) | ~l1_pre_topc(sK0) | ~spl3_3),
% 7.42/1.36    inference(resolution,[],[f714,f123])).
% 7.42/1.36  fof(f714,plain,(
% 7.42/1.36    ( ! [X8,X7] : (~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X8))) | r1_tarski(X7,k2_pre_topc(X8,X7)) | ~l1_pre_topc(X8)) )),
% 7.42/1.36    inference(superposition,[],[f100,f296])).
% 7.42/1.36  fof(f296,plain,(
% 7.42/1.36    ( ! [X2,X3] : (k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2)) )),
% 7.42/1.36    inference(subsumption_resolution,[],[f293,f87])).
% 7.42/1.36  fof(f293,plain,(
% 7.42/1.36    ( ! [X2,X3] : (k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2) | ~m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))) )),
% 7.42/1.36    inference(duplicate_literal_removal,[],[f288])).
% 7.42/1.36  fof(f288,plain,(
% 7.42/1.36    ( ! [X2,X3] : (k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2) | ~m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) )),
% 7.42/1.36    inference(superposition,[],[f86,f101])).
% 7.42/1.36  fof(f101,plain,(
% 7.42/1.36    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.42/1.36    inference(cnf_transformation,[],[f56])).
% 7.42/1.36  fof(f56,plain,(
% 7.42/1.36    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.42/1.36    inference(flattening,[],[f55])).
% 7.42/1.36  fof(f55,plain,(
% 7.42/1.36    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 7.42/1.36    inference(ennf_transformation,[],[f19])).
% 7.42/1.36  fof(f19,axiom,(
% 7.42/1.36    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 7.42/1.36    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 7.42/1.36  fof(f100,plain,(
% 7.42/1.36    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 7.42/1.36    inference(cnf_transformation,[],[f10])).
% 7.42/1.36  fof(f10,axiom,(
% 7.42/1.36    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 7.42/1.36    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 7.42/1.36  fof(f2520,plain,(
% 7.42/1.36    spl3_20 | ~spl3_3 | ~spl3_4),
% 7.42/1.36    inference(avatar_split_clause,[],[f2519,f126,f121,f604])).
% 7.42/1.36  fof(f2519,plain,(
% 7.42/1.36    r1_tarski(k1_tops_1(sK0,sK1),sK1) | (~spl3_3 | ~spl3_4)),
% 7.42/1.36    inference(subsumption_resolution,[],[f2509,f128])).
% 7.42/1.36  fof(f2509,plain,(
% 7.42/1.36    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~l1_pre_topc(sK0) | ~spl3_3),
% 7.42/1.36    inference(resolution,[],[f697,f123])).
% 7.42/1.36  fof(f697,plain,(
% 7.42/1.36    ( ! [X4,X5] : (~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X5))) | r1_tarski(k1_tops_1(X5,X4),X4) | ~l1_pre_topc(X5)) )),
% 7.42/1.36    inference(superposition,[],[f98,f283])).
% 7.42/1.36  fof(f98,plain,(
% 7.42/1.36    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 7.42/1.36    inference(cnf_transformation,[],[f6])).
% 7.42/1.36  fof(f6,axiom,(
% 7.42/1.36    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 7.42/1.36    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 7.42/1.36  fof(f1900,plain,(
% 7.42/1.36    ~spl3_9 | ~spl3_10 | spl3_2),
% 7.42/1.36    inference(avatar_split_clause,[],[f1899,f115,f237,f233])).
% 7.42/1.36  fof(f1899,plain,(
% 7.42/1.36    k2_tops_1(sK0,sK1) != k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_2),
% 7.42/1.36    inference(superposition,[],[f117,f75])).
% 7.42/1.36  fof(f117,plain,(
% 7.42/1.36    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | spl3_2),
% 7.42/1.36    inference(avatar_component_clause,[],[f115])).
% 7.42/1.36  fof(f1813,plain,(
% 7.42/1.36    ~spl3_61 | spl3_32),
% 7.42/1.36    inference(avatar_split_clause,[],[f1808,f670,f1810])).
% 7.42/1.36  fof(f1808,plain,(
% 7.42/1.36    ~r1_tarski(sK1,k2_pre_topc(sK0,sK1)) | spl3_32),
% 7.42/1.36    inference(resolution,[],[f672,f91])).
% 7.42/1.36  fof(f672,plain,(
% 7.42/1.36    ~m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | spl3_32),
% 7.42/1.36    inference(avatar_component_clause,[],[f670])).
% 7.42/1.36  fof(f588,plain,(
% 7.42/1.36    ~spl3_3 | ~spl3_4 | spl3_9),
% 7.42/1.36    inference(avatar_contradiction_clause,[],[f587])).
% 7.42/1.36  fof(f587,plain,(
% 7.42/1.36    $false | (~spl3_3 | ~spl3_4 | spl3_9)),
% 7.42/1.36    inference(subsumption_resolution,[],[f586,f128])).
% 7.42/1.36  fof(f586,plain,(
% 7.42/1.36    ~l1_pre_topc(sK0) | (~spl3_3 | spl3_9)),
% 7.42/1.36    inference(subsumption_resolution,[],[f579,f123])).
% 7.42/1.36  fof(f579,plain,(
% 7.42/1.36    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl3_9),
% 7.42/1.36    inference(resolution,[],[f298,f235])).
% 7.42/1.36  fof(f235,plain,(
% 7.42/1.36    ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_9),
% 7.42/1.36    inference(avatar_component_clause,[],[f233])).
% 7.42/1.36  fof(f262,plain,(
% 7.42/1.36    spl3_12 | ~spl3_3 | ~spl3_4 | ~spl3_5),
% 7.42/1.36    inference(avatar_split_clause,[],[f257,f131,f126,f121,f259])).
% 7.42/1.36  fof(f259,plain,(
% 7.42/1.36    spl3_12 <=> v3_pre_topc(k1_tops_1(sK0,sK1),sK0)),
% 7.42/1.36    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 7.42/1.36  fof(f131,plain,(
% 7.42/1.36    spl3_5 <=> v2_pre_topc(sK0)),
% 7.42/1.36    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 7.42/1.36  fof(f257,plain,(
% 7.42/1.36    v3_pre_topc(k1_tops_1(sK0,sK1),sK0) | (~spl3_3 | ~spl3_4 | ~spl3_5)),
% 7.42/1.36    inference(subsumption_resolution,[],[f256,f133])).
% 7.42/1.36  fof(f133,plain,(
% 7.42/1.36    v2_pre_topc(sK0) | ~spl3_5),
% 7.42/1.36    inference(avatar_component_clause,[],[f131])).
% 7.42/1.36  fof(f256,plain,(
% 7.42/1.36    v3_pre_topc(k1_tops_1(sK0,sK1),sK0) | ~v2_pre_topc(sK0) | (~spl3_3 | ~spl3_4)),
% 7.42/1.36    inference(subsumption_resolution,[],[f253,f128])).
% 7.42/1.36  fof(f253,plain,(
% 7.42/1.36    v3_pre_topc(k1_tops_1(sK0,sK1),sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~spl3_3),
% 7.42/1.36    inference(resolution,[],[f88,f123])).
% 7.42/1.36  fof(f88,plain,(
% 7.42/1.36    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(k1_tops_1(X0,X1),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.42/1.36    inference(cnf_transformation,[],[f47])).
% 7.42/1.36  fof(f47,plain,(
% 7.42/1.36    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.42/1.36    inference(flattening,[],[f46])).
% 7.42/1.36  fof(f46,plain,(
% 7.42/1.36    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 7.42/1.36    inference(ennf_transformation,[],[f26])).
% 7.42/1.36  fof(f26,axiom,(
% 7.42/1.36    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 7.42/1.36    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).
% 7.42/1.36  fof(f154,plain,(
% 7.42/1.36    spl3_6 | ~spl3_3),
% 7.42/1.36    inference(avatar_split_clause,[],[f147,f121,f151])).
% 7.42/1.36  fof(f147,plain,(
% 7.42/1.36    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl3_3),
% 7.42/1.36    inference(resolution,[],[f90,f123])).
% 7.42/1.36  fof(f90,plain,(
% 7.42/1.36    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 7.42/1.36    inference(cnf_transformation,[],[f67])).
% 7.42/1.36  fof(f134,plain,(
% 7.42/1.36    spl3_5),
% 7.42/1.36    inference(avatar_split_clause,[],[f70,f131])).
% 7.42/1.36  fof(f70,plain,(
% 7.42/1.36    v2_pre_topc(sK0)),
% 7.42/1.36    inference(cnf_transformation,[],[f64])).
% 7.42/1.36  fof(f64,plain,(
% 7.42/1.36    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 7.42/1.36    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f61,f63,f62])).
% 7.42/1.36  fof(f62,plain,(
% 7.42/1.36    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | ~v3_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 7.42/1.36    introduced(choice_axiom,[])).
% 7.42/1.36  fof(f63,plain,(
% 7.42/1.36    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | ~v3_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 7.42/1.36    introduced(choice_axiom,[])).
% 7.42/1.36  fof(f61,plain,(
% 7.42/1.36    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 7.42/1.36    inference(flattening,[],[f60])).
% 7.42/1.36  fof(f60,plain,(
% 7.42/1.36    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 7.42/1.36    inference(nnf_transformation,[],[f35])).
% 7.42/1.36  fof(f35,plain,(
% 7.42/1.36    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 7.42/1.36    inference(flattening,[],[f34])).
% 7.42/1.36  fof(f34,plain,(
% 7.42/1.36    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 7.42/1.36    inference(ennf_transformation,[],[f33])).
% 7.42/1.36  fof(f33,negated_conjecture,(
% 7.42/1.36    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 7.42/1.36    inference(negated_conjecture,[],[f32])).
% 7.42/1.36  fof(f32,conjecture,(
% 7.42/1.36    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 7.42/1.36    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tops_1)).
% 7.42/1.36  fof(f129,plain,(
% 7.42/1.36    spl3_4),
% 7.42/1.36    inference(avatar_split_clause,[],[f71,f126])).
% 7.42/1.36  fof(f71,plain,(
% 7.42/1.36    l1_pre_topc(sK0)),
% 7.42/1.36    inference(cnf_transformation,[],[f64])).
% 7.42/1.36  fof(f124,plain,(
% 7.42/1.36    spl3_3),
% 7.42/1.36    inference(avatar_split_clause,[],[f72,f121])).
% 7.42/1.36  fof(f72,plain,(
% 7.42/1.36    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 7.42/1.36    inference(cnf_transformation,[],[f64])).
% 7.42/1.36  fof(f119,plain,(
% 7.42/1.36    spl3_1 | spl3_2),
% 7.42/1.36    inference(avatar_split_clause,[],[f73,f115,f111])).
% 7.42/1.36  fof(f73,plain,(
% 7.42/1.36    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)),
% 7.42/1.36    inference(cnf_transformation,[],[f64])).
% 7.42/1.36  fof(f118,plain,(
% 7.42/1.36    ~spl3_1 | ~spl3_2),
% 7.42/1.36    inference(avatar_split_clause,[],[f74,f115,f111])).
% 7.42/1.36  fof(f74,plain,(
% 7.42/1.36    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)),
% 7.42/1.36    inference(cnf_transformation,[],[f64])).
% 7.42/1.36  % SZS output end Proof for theBenchmark
% 7.42/1.36  % (15444)------------------------------
% 7.42/1.36  % (15444)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.42/1.36  % (15444)Termination reason: Refutation
% 7.42/1.36  
% 7.42/1.36  % (15444)Memory used [KB]: 16758
% 7.42/1.36  % (15444)Time elapsed: 0.950 s
% 7.42/1.36  % (15444)------------------------------
% 7.42/1.36  % (15444)------------------------------
% 7.84/1.38  % (15422)Success in time 1.011 s
%------------------------------------------------------------------------------
