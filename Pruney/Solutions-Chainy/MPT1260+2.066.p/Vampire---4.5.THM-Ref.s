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
% DateTime   : Thu Dec  3 13:11:44 EST 2020

% Result     : Theorem 3.08s
% Output     : Refutation 3.08s
% Verified   : 
% Statistics : Number of formulae       :  205 ( 373 expanded)
%              Number of leaves         :   46 ( 135 expanded)
%              Depth                    :   12
%              Number of atoms          :  591 (1154 expanded)
%              Number of equality atoms :  101 ( 237 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2343,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f101,f102,f107,f112,f117,f205,f224,f246,f301,f310,f312,f319,f429,f478,f493,f722,f726,f747,f748,f2200,f2249,f2309,f2342])).

fof(f2342,plain,
    ( sK1 != k1_tops_1(sK0,sK1)
    | v3_pre_topc(sK1,sK0)
    | ~ v3_pre_topc(k1_tops_1(sK0,sK1),sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f2309,plain,
    ( spl3_15
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_121 ),
    inference(avatar_split_clause,[],[f2308,f2197,f109,f104,f212])).

fof(f212,plain,
    ( spl3_15
  <=> sK1 = k1_tops_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f104,plain,
    ( spl3_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f109,plain,
    ( spl3_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f2197,plain,
    ( spl3_121
  <=> sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_121])])).

fof(f2308,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_121 ),
    inference(subsumption_resolution,[],[f2307,f111])).

fof(f111,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f109])).

fof(f2307,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl3_3
    | ~ spl3_121 ),
    inference(subsumption_resolution,[],[f2282,f106])).

fof(f106,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f104])).

fof(f2282,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_121 ),
    inference(superposition,[],[f251,f2199])).

fof(f2199,plain,
    ( sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl3_121 ),
    inference(avatar_component_clause,[],[f2197])).

fof(f251,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f248])).

fof(f248,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(superposition,[],[f65,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f2249,plain,(
    ~ spl3_57 ),
    inference(avatar_contradiction_clause,[],[f2211])).

fof(f2211,plain,
    ( $false
    | ~ spl3_57 ),
    inference(unit_resulting_resolution,[],[f82,f82,f810,f524])).

fof(f524,plain,(
    ! [X19,X17,X18] :
      ( ~ m1_subset_1(X18,k1_zfmisc_1(X17))
      | ~ m1_subset_1(X17,k1_zfmisc_1(X19))
      | m1_subset_1(X18,k1_zfmisc_1(X19)) ) ),
    inference(superposition,[],[f194,f163])).

fof(f163,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(subsumption_resolution,[],[f157,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f157,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(superposition,[],[f70,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f70,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f194,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_xboole_0(X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f193])).

fof(f193,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_xboole_0(X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(superposition,[],[f73,f65])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_subset_1)).

fof(f810,plain,
    ( ! [X2] : ~ m1_subset_1(X2,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl3_57 ),
    inference(avatar_component_clause,[],[f809])).

fof(f809,plain,
    ( spl3_57
  <=> ! [X2] : ~ m1_subset_1(X2,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_57])])).

fof(f82,plain,(
    ! [X0] : m1_subset_1(sK2(X0),X0) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0] : m1_subset_1(sK2(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f10,f57])).

fof(f57,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f10,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(f2200,plain,
    ( spl3_57
    | spl3_121
    | ~ spl3_42
    | ~ spl3_53 ),
    inference(avatar_split_clause,[],[f2195,f744,f475,f2197,f809])).

fof(f475,plain,
    ( spl3_42
  <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).

fof(f744,plain,
    ( spl3_53
  <=> sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_53])])).

fof(f2195,plain,
    ( ! [X15] :
        ( sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) )
    | ~ spl3_42
    | ~ spl3_53 ),
    inference(subsumption_resolution,[],[f2166,f477])).

fof(f477,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl3_42 ),
    inference(avatar_component_clause,[],[f475])).

fof(f2166,plain,
    ( ! [X15] :
        ( sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
        | ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) )
    | ~ spl3_53 ),
    inference(superposition,[],[f620,f746])).

fof(f746,plain,
    ( sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))
    | ~ spl3_53 ),
    inference(avatar_component_clause,[],[f744])).

fof(f620,plain,(
    ! [X4,X2,X3] :
      ( k3_subset_1(X2,X3) = k4_xboole_0(k3_subset_1(X2,X3),X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
      | ~ m1_subset_1(X4,k1_zfmisc_1(X2)) ) ),
    inference(subsumption_resolution,[],[f612,f81])).

fof(f612,plain,(
    ! [X4,X2,X3] :
      ( k3_subset_1(X2,X3) = k4_xboole_0(k3_subset_1(X2,X3),X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
      | ~ m1_subset_1(X4,k1_zfmisc_1(X2))
      | ~ m1_subset_1(k3_subset_1(X2,X3),k1_zfmisc_1(X2)) ) ),
    inference(superposition,[],[f263,f65])).

fof(f263,plain,(
    ! [X4,X5,X3] :
      ( k3_subset_1(X3,X4) = k7_subset_1(X3,k3_subset_1(X3,X4),X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(X3)) ) ),
    inference(subsumption_resolution,[],[f259,f81])).

fof(f259,plain,(
    ! [X4,X5,X3] :
      ( k3_subset_1(X3,X4) = k7_subset_1(X3,k3_subset_1(X3,X4),X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
      | ~ m1_subset_1(k3_subset_1(X3,X4),k1_zfmisc_1(X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(X3)) ) ),
    inference(superposition,[],[f74,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k9_subset_1)).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_subset_1)).

fof(f748,plain,
    ( spl3_43
    | ~ spl3_49 ),
    inference(avatar_split_clause,[],[f735,f588,f490])).

fof(f490,plain,
    ( spl3_43
  <=> r1_tarski(sK1,k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_43])])).

fof(f588,plain,
    ( spl3_49
  <=> k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_49])])).

fof(f735,plain,
    ( r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | ~ spl3_49 ),
    inference(superposition,[],[f128,f590])).

fof(f590,plain,
    ( k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl3_49 ),
    inference(avatar_component_clause,[],[f588])).

fof(f128,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(trivial_inequality_removal,[],[f127])).

fof(f127,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_tarski(X0,k2_xboole_0(X0,X1)) ) ),
    inference(superposition,[],[f85,f87])).

fof(f87,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f85,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k1_xboole_0
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f747,plain,
    ( ~ spl3_41
    | spl3_53
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f504,f226,f744,f471])).

fof(f471,plain,
    ( spl3_41
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).

fof(f226,plain,
    ( spl3_16
  <=> k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f504,plain,
    ( sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl3_16 ),
    inference(superposition,[],[f162,f228])).

fof(f228,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f226])).

fof(f162,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k4_xboole_0(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f158])).

fof(f158,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k4_xboole_0(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(superposition,[],[f69,f70])).

fof(f726,plain,
    ( spl3_49
    | ~ spl3_36
    | ~ spl3_48 ),
    inference(avatar_split_clause,[],[f725,f584,f426,f588])).

fof(f426,plain,
    ( spl3_36
  <=> r1_tarski(k2_pre_topc(sK0,sK1),k2_xboole_0(sK1,k2_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).

fof(f584,plain,
    ( spl3_48
  <=> r1_tarski(k2_xboole_0(sK1,k2_tops_1(sK0,sK1)),k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_48])])).

fof(f725,plain,
    ( k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl3_36
    | ~ spl3_48 ),
    inference(subsumption_resolution,[],[f723,f428])).

fof(f428,plain,
    ( r1_tarski(k2_pre_topc(sK0,sK1),k2_xboole_0(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl3_36 ),
    inference(avatar_component_clause,[],[f426])).

fof(f723,plain,
    ( k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ r1_tarski(k2_pre_topc(sK0,sK1),k2_xboole_0(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl3_48 ),
    inference(resolution,[],[f585,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f585,plain,
    ( r1_tarski(k2_xboole_0(sK1,k2_tops_1(sK0,sK1)),k2_pre_topc(sK0,sK1))
    | ~ spl3_48 ),
    inference(avatar_component_clause,[],[f584])).

fof(f722,plain,
    ( ~ spl3_3
    | ~ spl3_4
    | spl3_48 ),
    inference(avatar_contradiction_clause,[],[f721])).

fof(f721,plain,
    ( $false
    | ~ spl3_3
    | ~ spl3_4
    | spl3_48 ),
    inference(subsumption_resolution,[],[f720,f111])).

fof(f720,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl3_3
    | spl3_48 ),
    inference(subsumption_resolution,[],[f719,f106])).

fof(f719,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl3_48 ),
    inference(subsumption_resolution,[],[f716,f91])).

fof(f91,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f55])).

fof(f716,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl3_48 ),
    inference(superposition,[],[f586,f709])).

fof(f709,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_xboole_0(X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f255,f291])).

fof(f291,plain,(
    ! [X2,X3] :
      ( m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2) ) ),
    inference(subsumption_resolution,[],[f288,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f288,plain,(
    ! [X2,X3] :
      ( m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(k2_pre_topc(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2) ) ),
    inference(superposition,[],[f73,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

fof(f255,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_xboole_0(X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f254])).

fof(f254,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_xboole_0(X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(superposition,[],[f90,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f586,plain,
    ( ~ r1_tarski(k2_xboole_0(sK1,k2_tops_1(sK0,sK1)),k2_pre_topc(sK0,sK1))
    | spl3_48 ),
    inference(avatar_component_clause,[],[f584])).

fof(f493,plain,
    ( ~ spl3_43
    | spl3_41 ),
    inference(avatar_split_clause,[],[f488,f471,f490])).

fof(f488,plain,
    ( ~ r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | spl3_41 ),
    inference(resolution,[],[f473,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f473,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | spl3_41 ),
    inference(avatar_component_clause,[],[f471])).

fof(f478,plain,
    ( ~ spl3_41
    | spl3_42
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f469,f226,f475,f471])).

fof(f469,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl3_16 ),
    inference(superposition,[],[f161,f228])).

fof(f161,plain,(
    ! [X2,X3] :
      ( m1_subset_1(k4_xboole_0(X2,X3),k1_zfmisc_1(X2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ) ),
    inference(duplicate_literal_removal,[],[f159])).

fof(f159,plain,(
    ! [X2,X3] :
      ( m1_subset_1(k4_xboole_0(X2,X3),k1_zfmisc_1(X2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ) ),
    inference(superposition,[],[f81,f70])).

fof(f429,plain,
    ( spl3_36
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f424,f226,f426])).

fof(f424,plain,
    ( r1_tarski(k2_pre_topc(sK0,sK1),k2_xboole_0(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl3_16 ),
    inference(superposition,[],[f147,f228])).

fof(f147,plain,(
    ! [X2,X3] : r1_tarski(X2,k2_xboole_0(X3,k4_xboole_0(X2,X3))) ),
    inference(resolution,[],[f84,f91])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k4_xboole_0(X0,X1),X2)
      | r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f319,plain,
    ( spl3_16
    | ~ spl3_2
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f318,f177,f98,f226])).

fof(f98,plain,
    ( spl3_2
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f177,plain,
    ( spl3_10
  <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f318,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ spl3_2
    | ~ spl3_10 ),
    inference(subsumption_resolution,[],[f314,f178])).

fof(f178,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f177])).

fof(f314,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_2 ),
    inference(superposition,[],[f65,f99])).

fof(f99,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f98])).

fof(f312,plain,
    ( ~ spl3_14
    | spl3_15
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f311,f202,f212,f208])).

fof(f208,plain,
    ( spl3_14
  <=> r1_tarski(sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f202,plain,
    ( spl3_13
  <=> r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f311,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | ~ spl3_13 ),
    inference(resolution,[],[f204,f68])).

fof(f204,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f202])).

fof(f310,plain,
    ( spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_15 ),
    inference(avatar_contradiction_clause,[],[f309])).

fof(f309,plain,
    ( $false
    | spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_15 ),
    inference(subsumption_resolution,[],[f308,f111])).

fof(f308,plain,
    ( ~ l1_pre_topc(sK0)
    | spl3_2
    | ~ spl3_3
    | ~ spl3_15 ),
    inference(subsumption_resolution,[],[f307,f106])).

fof(f307,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl3_2
    | ~ spl3_15 ),
    inference(subsumption_resolution,[],[f306,f100])).

fof(f100,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f98])).

fof(f306,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_15 ),
    inference(superposition,[],[f71,f214])).

fof(f214,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f212])).

fof(f301,plain,
    ( ~ spl3_1
    | ~ spl3_3
    | ~ spl3_4
    | spl3_14 ),
    inference(avatar_contradiction_clause,[],[f292])).

fof(f292,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_4
    | spl3_14 ),
    inference(unit_resulting_resolution,[],[f111,f95,f91,f106,f210,f106,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X1,X2)
      | ~ v3_pre_topc(X1,X0)
      | r1_tarski(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r1_tarski(X1,X2)
                  & v3_pre_topc(X1,X0) )
               => r1_tarski(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tops_1)).

fof(f210,plain,
    ( ~ r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | spl3_14 ),
    inference(avatar_component_clause,[],[f208])).

fof(f95,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl3_1
  <=> v3_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f246,plain,
    ( spl3_17
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f241,f114,f109,f104,f243])).

fof(f243,plain,
    ( spl3_17
  <=> v3_pre_topc(k1_tops_1(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f114,plain,
    ( spl3_5
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f241,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f240,f116])).

fof(f116,plain,
    ( v2_pre_topc(sK0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f114])).

fof(f240,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f237,f111])).

fof(f237,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl3_3 ),
    inference(resolution,[],[f77,f106])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

fof(f224,plain,
    ( ~ spl3_3
    | ~ spl3_4
    | spl3_10 ),
    inference(avatar_contradiction_clause,[],[f223])).

fof(f223,plain,
    ( $false
    | ~ spl3_3
    | ~ spl3_4
    | spl3_10 ),
    inference(subsumption_resolution,[],[f222,f111])).

fof(f222,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl3_3
    | spl3_10 ),
    inference(subsumption_resolution,[],[f217,f106])).

fof(f217,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl3_10 ),
    inference(resolution,[],[f75,f179])).

fof(f179,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_10 ),
    inference(avatar_component_clause,[],[f177])).

fof(f205,plain,
    ( spl3_13
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f200,f109,f104,f202])).

fof(f200,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f198,f111])).

fof(f198,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl3_3 ),
    inference(resolution,[],[f83,f106])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

fof(f117,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f60,f114])).

fof(f60,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,
    ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
      | ~ v3_pre_topc(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
      | v3_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f50,f52,f51])).

fof(f51,plain,
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

fof(f52,plain,
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

fof(f50,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    inference(negated_conjecture,[],[f25])).

fof(f25,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_tops_1)).

fof(f112,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f61,f109])).

fof(f61,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f53])).

fof(f107,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f62,f104])).

fof(f62,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f53])).

fof(f102,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f63,f98,f94])).

fof(f63,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f53])).

fof(f101,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f64,f98,f94])).

fof(f64,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f53])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n015.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:02:08 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.52  % (11021)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.52  % (10997)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.52  % (11013)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.52  % (11002)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.52  % (11003)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (11005)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.54  % (10999)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.54  % (11020)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.54  % (11000)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.54  % (11001)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.54  % (11012)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.55  % (11023)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (11009)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.55  % (11024)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.55  % (11004)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.55  % (11015)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.55  % (11022)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.55  % (11010)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.55  % (11011)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.55  % (11025)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.55  % (11016)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.56  % (11007)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.56  % (11018)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.56  % (11019)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.56  % (11017)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.56  % (11008)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.56  % (11026)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.78/0.60  % (10998)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.78/0.61  % (11014)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.78/0.61  % (11006)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 3.08/0.79  % (11018)Refutation found. Thanks to Tanya!
% 3.08/0.79  % SZS status Theorem for theBenchmark
% 3.08/0.79  % SZS output start Proof for theBenchmark
% 3.08/0.79  fof(f2343,plain,(
% 3.08/0.79    $false),
% 3.08/0.79    inference(avatar_sat_refutation,[],[f101,f102,f107,f112,f117,f205,f224,f246,f301,f310,f312,f319,f429,f478,f493,f722,f726,f747,f748,f2200,f2249,f2309,f2342])).
% 3.08/0.79  fof(f2342,plain,(
% 3.08/0.79    sK1 != k1_tops_1(sK0,sK1) | v3_pre_topc(sK1,sK0) | ~v3_pre_topc(k1_tops_1(sK0,sK1),sK0)),
% 3.08/0.79    introduced(theory_tautology_sat_conflict,[])).
% 3.08/0.79  fof(f2309,plain,(
% 3.08/0.79    spl3_15 | ~spl3_3 | ~spl3_4 | ~spl3_121),
% 3.08/0.79    inference(avatar_split_clause,[],[f2308,f2197,f109,f104,f212])).
% 3.08/0.79  fof(f212,plain,(
% 3.08/0.79    spl3_15 <=> sK1 = k1_tops_1(sK0,sK1)),
% 3.08/0.79    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 3.08/0.79  fof(f104,plain,(
% 3.08/0.79    spl3_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.08/0.79    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 3.08/0.79  fof(f109,plain,(
% 3.08/0.79    spl3_4 <=> l1_pre_topc(sK0)),
% 3.08/0.79    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 3.08/0.79  fof(f2197,plain,(
% 3.08/0.79    spl3_121 <=> sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 3.08/0.79    introduced(avatar_definition,[new_symbols(naming,[spl3_121])])).
% 3.08/0.79  fof(f2308,plain,(
% 3.08/0.79    sK1 = k1_tops_1(sK0,sK1) | (~spl3_3 | ~spl3_4 | ~spl3_121)),
% 3.08/0.79    inference(subsumption_resolution,[],[f2307,f111])).
% 3.08/0.79  fof(f111,plain,(
% 3.08/0.79    l1_pre_topc(sK0) | ~spl3_4),
% 3.08/0.79    inference(avatar_component_clause,[],[f109])).
% 3.08/0.79  fof(f2307,plain,(
% 3.08/0.79    sK1 = k1_tops_1(sK0,sK1) | ~l1_pre_topc(sK0) | (~spl3_3 | ~spl3_121)),
% 3.08/0.79    inference(subsumption_resolution,[],[f2282,f106])).
% 3.08/0.79  fof(f106,plain,(
% 3.08/0.79    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_3),
% 3.08/0.79    inference(avatar_component_clause,[],[f104])).
% 3.08/0.79  fof(f2282,plain,(
% 3.08/0.79    sK1 = k1_tops_1(sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl3_121),
% 3.08/0.79    inference(superposition,[],[f251,f2199])).
% 3.08/0.79  fof(f2199,plain,(
% 3.08/0.79    sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl3_121),
% 3.08/0.79    inference(avatar_component_clause,[],[f2197])).
% 3.08/0.79  fof(f251,plain,(
% 3.08/0.79    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.08/0.79    inference(duplicate_literal_removal,[],[f248])).
% 3.08/0.79  fof(f248,plain,(
% 3.08/0.79    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.08/0.79    inference(superposition,[],[f65,f72])).
% 3.08/0.79  fof(f72,plain,(
% 3.08/0.79    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.08/0.79    inference(cnf_transformation,[],[f33])).
% 3.08/0.79  fof(f33,plain,(
% 3.08/0.79    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.08/0.79    inference(ennf_transformation,[],[f24])).
% 3.08/0.79  fof(f24,axiom,(
% 3.08/0.79    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 3.08/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).
% 3.08/0.79  fof(f65,plain,(
% 3.08/0.79    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.08/0.79    inference(cnf_transformation,[],[f29])).
% 3.08/0.79  fof(f29,plain,(
% 3.08/0.79    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.08/0.79    inference(ennf_transformation,[],[f14])).
% 3.08/0.79  fof(f14,axiom,(
% 3.08/0.79    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 3.08/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 3.08/0.79  fof(f2249,plain,(
% 3.08/0.79    ~spl3_57),
% 3.08/0.79    inference(avatar_contradiction_clause,[],[f2211])).
% 3.08/0.79  fof(f2211,plain,(
% 3.08/0.79    $false | ~spl3_57),
% 3.08/0.79    inference(unit_resulting_resolution,[],[f82,f82,f810,f524])).
% 3.08/0.79  fof(f524,plain,(
% 3.08/0.79    ( ! [X19,X17,X18] : (~m1_subset_1(X18,k1_zfmisc_1(X17)) | ~m1_subset_1(X17,k1_zfmisc_1(X19)) | m1_subset_1(X18,k1_zfmisc_1(X19))) )),
% 3.08/0.79    inference(superposition,[],[f194,f163])).
% 3.08/0.79  fof(f163,plain,(
% 3.08/0.79    ( ! [X0,X1] : (k4_xboole_0(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.08/0.79    inference(subsumption_resolution,[],[f157,f81])).
% 3.08/0.79  fof(f81,plain,(
% 3.08/0.79    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.08/0.79    inference(cnf_transformation,[],[f43])).
% 3.08/0.79  fof(f43,plain,(
% 3.08/0.79    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.08/0.79    inference(ennf_transformation,[],[f8])).
% 3.08/0.79  fof(f8,axiom,(
% 3.08/0.79    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 3.08/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 3.08/0.79  fof(f157,plain,(
% 3.08/0.79    ( ! [X0,X1] : (k4_xboole_0(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.08/0.79    inference(superposition,[],[f70,f69])).
% 3.08/0.79  fof(f69,plain,(
% 3.08/0.79    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.08/0.79    inference(cnf_transformation,[],[f30])).
% 3.08/0.79  fof(f30,plain,(
% 3.08/0.79    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.08/0.79    inference(ennf_transformation,[],[f12])).
% 3.08/0.79  fof(f12,axiom,(
% 3.08/0.79    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 3.08/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 3.08/0.79  fof(f70,plain,(
% 3.08/0.79    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.08/0.79    inference(cnf_transformation,[],[f31])).
% 3.08/0.79  fof(f31,plain,(
% 3.08/0.79    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.08/0.79    inference(ennf_transformation,[],[f7])).
% 3.08/0.79  fof(f7,axiom,(
% 3.08/0.79    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 3.08/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 3.08/0.79  fof(f194,plain,(
% 3.08/0.79    ( ! [X2,X0,X1] : (m1_subset_1(k4_xboole_0(X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.08/0.79    inference(duplicate_literal_removal,[],[f193])).
% 3.08/0.79  fof(f193,plain,(
% 3.08/0.79    ( ! [X2,X0,X1] : (m1_subset_1(k4_xboole_0(X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.08/0.79    inference(superposition,[],[f73,f65])).
% 3.08/0.79  fof(f73,plain,(
% 3.08/0.79    ( ! [X2,X0,X1] : (m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.08/0.79    inference(cnf_transformation,[],[f34])).
% 3.08/0.79  fof(f34,plain,(
% 3.08/0.79    ! [X0,X1,X2] : (m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.08/0.79    inference(ennf_transformation,[],[f9])).
% 3.08/0.79  fof(f9,axiom,(
% 3.08/0.79    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 3.08/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_subset_1)).
% 3.08/0.79  fof(f810,plain,(
% 3.08/0.79    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))) ) | ~spl3_57),
% 3.08/0.79    inference(avatar_component_clause,[],[f809])).
% 3.08/0.79  fof(f809,plain,(
% 3.08/0.79    spl3_57 <=> ! [X2] : ~m1_subset_1(X2,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))),
% 3.08/0.79    introduced(avatar_definition,[new_symbols(naming,[spl3_57])])).
% 3.08/0.79  fof(f82,plain,(
% 3.08/0.79    ( ! [X0] : (m1_subset_1(sK2(X0),X0)) )),
% 3.08/0.79    inference(cnf_transformation,[],[f58])).
% 3.08/0.79  fof(f58,plain,(
% 3.08/0.79    ! [X0] : m1_subset_1(sK2(X0),X0)),
% 3.08/0.79    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f10,f57])).
% 3.08/0.79  fof(f57,plain,(
% 3.08/0.79    ! [X0] : (? [X1] : m1_subset_1(X1,X0) => m1_subset_1(sK2(X0),X0))),
% 3.08/0.79    introduced(choice_axiom,[])).
% 3.08/0.79  fof(f10,axiom,(
% 3.08/0.79    ! [X0] : ? [X1] : m1_subset_1(X1,X0)),
% 3.08/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).
% 3.08/0.79  fof(f2200,plain,(
% 3.08/0.79    spl3_57 | spl3_121 | ~spl3_42 | ~spl3_53),
% 3.08/0.79    inference(avatar_split_clause,[],[f2195,f744,f475,f2197,f809])).
% 3.08/0.79  fof(f475,plain,(
% 3.08/0.79    spl3_42 <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))),
% 3.08/0.79    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).
% 3.08/0.79  fof(f744,plain,(
% 3.08/0.79    spl3_53 <=> sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))),
% 3.08/0.79    introduced(avatar_definition,[new_symbols(naming,[spl3_53])])).
% 3.08/0.79  fof(f2195,plain,(
% 3.08/0.79    ( ! [X15] : (sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~m1_subset_1(X15,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))) ) | (~spl3_42 | ~spl3_53)),
% 3.08/0.79    inference(subsumption_resolution,[],[f2166,f477])).
% 3.08/0.79  fof(f477,plain,(
% 3.08/0.79    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~spl3_42),
% 3.08/0.79    inference(avatar_component_clause,[],[f475])).
% 3.08/0.79  fof(f2166,plain,(
% 3.08/0.79    ( ! [X15] : (sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~m1_subset_1(X15,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))) ) | ~spl3_53),
% 3.08/0.79    inference(superposition,[],[f620,f746])).
% 3.08/0.79  fof(f746,plain,(
% 3.08/0.79    sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) | ~spl3_53),
% 3.08/0.79    inference(avatar_component_clause,[],[f744])).
% 3.08/0.79  fof(f620,plain,(
% 3.08/0.79    ( ! [X4,X2,X3] : (k3_subset_1(X2,X3) = k4_xboole_0(k3_subset_1(X2,X3),X3) | ~m1_subset_1(X3,k1_zfmisc_1(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(X2))) )),
% 3.08/0.79    inference(subsumption_resolution,[],[f612,f81])).
% 3.08/0.79  fof(f612,plain,(
% 3.08/0.79    ( ! [X4,X2,X3] : (k3_subset_1(X2,X3) = k4_xboole_0(k3_subset_1(X2,X3),X3) | ~m1_subset_1(X3,k1_zfmisc_1(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(X2)) | ~m1_subset_1(k3_subset_1(X2,X3),k1_zfmisc_1(X2))) )),
% 3.08/0.79    inference(superposition,[],[f263,f65])).
% 3.08/0.79  fof(f263,plain,(
% 3.08/0.79    ( ! [X4,X5,X3] : (k3_subset_1(X3,X4) = k7_subset_1(X3,k3_subset_1(X3,X4),X4) | ~m1_subset_1(X4,k1_zfmisc_1(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(X3))) )),
% 3.08/0.79    inference(subsumption_resolution,[],[f259,f81])).
% 3.08/0.79  fof(f259,plain,(
% 3.08/0.79    ( ! [X4,X5,X3] : (k3_subset_1(X3,X4) = k7_subset_1(X3,k3_subset_1(X3,X4),X4) | ~m1_subset_1(X4,k1_zfmisc_1(X3)) | ~m1_subset_1(k3_subset_1(X3,X4),k1_zfmisc_1(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(X3))) )),
% 3.08/0.79    inference(superposition,[],[f74,f89])).
% 3.08/0.79  fof(f89,plain,(
% 3.08/0.79    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X1) = X1 | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 3.08/0.79    inference(cnf_transformation,[],[f46])).
% 3.08/0.79  fof(f46,plain,(
% 3.08/0.79    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X1) = X1 | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 3.08/0.79    inference(ennf_transformation,[],[f11])).
% 3.08/0.79  fof(f11,axiom,(
% 3.08/0.79    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X1) = X1)),
% 3.08/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k9_subset_1)).
% 3.08/0.79  fof(f74,plain,(
% 3.08/0.79    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.08/0.79    inference(cnf_transformation,[],[f35])).
% 3.08/0.79  fof(f35,plain,(
% 3.08/0.79    ! [X0,X1] : (! [X2] : (k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.08/0.79    inference(ennf_transformation,[],[f15])).
% 3.08/0.79  fof(f15,axiom,(
% 3.08/0.79    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))))),
% 3.08/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_subset_1)).
% 3.08/0.79  fof(f748,plain,(
% 3.08/0.79    spl3_43 | ~spl3_49),
% 3.08/0.79    inference(avatar_split_clause,[],[f735,f588,f490])).
% 3.08/0.79  fof(f490,plain,(
% 3.08/0.79    spl3_43 <=> r1_tarski(sK1,k2_pre_topc(sK0,sK1))),
% 3.08/0.79    introduced(avatar_definition,[new_symbols(naming,[spl3_43])])).
% 3.08/0.79  fof(f588,plain,(
% 3.08/0.79    spl3_49 <=> k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 3.08/0.79    introduced(avatar_definition,[new_symbols(naming,[spl3_49])])).
% 3.08/0.79  fof(f735,plain,(
% 3.08/0.79    r1_tarski(sK1,k2_pre_topc(sK0,sK1)) | ~spl3_49),
% 3.08/0.79    inference(superposition,[],[f128,f590])).
% 3.08/0.79  fof(f590,plain,(
% 3.08/0.79    k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl3_49),
% 3.08/0.79    inference(avatar_component_clause,[],[f588])).
% 3.08/0.79  fof(f128,plain,(
% 3.08/0.79    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 3.08/0.79    inference(trivial_inequality_removal,[],[f127])).
% 3.08/0.79  fof(f127,plain,(
% 3.08/0.79    ( ! [X0,X1] : (k1_xboole_0 != k1_xboole_0 | r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 3.08/0.79    inference(superposition,[],[f85,f87])).
% 3.08/0.79  fof(f87,plain,(
% 3.08/0.79    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 3.08/0.79    inference(cnf_transformation,[],[f6])).
% 3.08/0.79  fof(f6,axiom,(
% 3.08/0.79    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 3.08/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).
% 3.08/0.79  fof(f85,plain,(
% 3.08/0.79    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1)) )),
% 3.08/0.79    inference(cnf_transformation,[],[f59])).
% 3.08/0.79  fof(f59,plain,(
% 3.08/0.79    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 3.08/0.79    inference(nnf_transformation,[],[f2])).
% 3.08/0.79  fof(f2,axiom,(
% 3.08/0.79    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 3.08/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 3.08/0.79  fof(f747,plain,(
% 3.08/0.79    ~spl3_41 | spl3_53 | ~spl3_16),
% 3.08/0.79    inference(avatar_split_clause,[],[f504,f226,f744,f471])).
% 3.08/0.79  fof(f471,plain,(
% 3.08/0.79    spl3_41 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))),
% 3.08/0.79    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).
% 3.08/0.79  fof(f226,plain,(
% 3.08/0.79    spl3_16 <=> k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)),
% 3.08/0.79    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 3.08/0.79  fof(f504,plain,(
% 3.08/0.79    sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~spl3_16),
% 3.08/0.79    inference(superposition,[],[f162,f228])).
% 3.08/0.79  fof(f228,plain,(
% 3.08/0.79    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~spl3_16),
% 3.08/0.79    inference(avatar_component_clause,[],[f226])).
% 3.08/0.79  fof(f162,plain,(
% 3.08/0.79    ( ! [X0,X1] : (k3_subset_1(X0,k4_xboole_0(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.08/0.79    inference(duplicate_literal_removal,[],[f158])).
% 3.08/0.79  fof(f158,plain,(
% 3.08/0.79    ( ! [X0,X1] : (k3_subset_1(X0,k4_xboole_0(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.08/0.79    inference(superposition,[],[f69,f70])).
% 3.08/0.79  fof(f726,plain,(
% 3.08/0.79    spl3_49 | ~spl3_36 | ~spl3_48),
% 3.08/0.79    inference(avatar_split_clause,[],[f725,f584,f426,f588])).
% 3.08/0.79  fof(f426,plain,(
% 3.08/0.79    spl3_36 <=> r1_tarski(k2_pre_topc(sK0,sK1),k2_xboole_0(sK1,k2_tops_1(sK0,sK1)))),
% 3.08/0.79    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).
% 3.08/0.79  fof(f584,plain,(
% 3.08/0.79    spl3_48 <=> r1_tarski(k2_xboole_0(sK1,k2_tops_1(sK0,sK1)),k2_pre_topc(sK0,sK1))),
% 3.08/0.79    introduced(avatar_definition,[new_symbols(naming,[spl3_48])])).
% 3.08/0.79  fof(f725,plain,(
% 3.08/0.79    k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | (~spl3_36 | ~spl3_48)),
% 3.08/0.79    inference(subsumption_resolution,[],[f723,f428])).
% 3.08/0.79  fof(f428,plain,(
% 3.08/0.79    r1_tarski(k2_pre_topc(sK0,sK1),k2_xboole_0(sK1,k2_tops_1(sK0,sK1))) | ~spl3_36),
% 3.08/0.79    inference(avatar_component_clause,[],[f426])).
% 3.08/0.79  fof(f723,plain,(
% 3.08/0.79    k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~r1_tarski(k2_pre_topc(sK0,sK1),k2_xboole_0(sK1,k2_tops_1(sK0,sK1))) | ~spl3_48),
% 3.08/0.79    inference(resolution,[],[f585,f68])).
% 3.08/0.79  fof(f68,plain,(
% 3.08/0.79    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 3.08/0.79    inference(cnf_transformation,[],[f55])).
% 3.08/0.79  fof(f55,plain,(
% 3.08/0.79    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.08/0.79    inference(flattening,[],[f54])).
% 3.08/0.79  fof(f54,plain,(
% 3.08/0.79    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.08/0.79    inference(nnf_transformation,[],[f1])).
% 3.08/0.79  fof(f1,axiom,(
% 3.08/0.79    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.08/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 3.08/0.79  fof(f585,plain,(
% 3.08/0.79    r1_tarski(k2_xboole_0(sK1,k2_tops_1(sK0,sK1)),k2_pre_topc(sK0,sK1)) | ~spl3_48),
% 3.08/0.79    inference(avatar_component_clause,[],[f584])).
% 3.08/0.79  fof(f722,plain,(
% 3.08/0.79    ~spl3_3 | ~spl3_4 | spl3_48),
% 3.08/0.79    inference(avatar_contradiction_clause,[],[f721])).
% 3.08/0.79  fof(f721,plain,(
% 3.08/0.79    $false | (~spl3_3 | ~spl3_4 | spl3_48)),
% 3.08/0.79    inference(subsumption_resolution,[],[f720,f111])).
% 3.08/0.79  fof(f720,plain,(
% 3.08/0.79    ~l1_pre_topc(sK0) | (~spl3_3 | spl3_48)),
% 3.08/0.79    inference(subsumption_resolution,[],[f719,f106])).
% 3.08/0.79  fof(f719,plain,(
% 3.08/0.79    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl3_48),
% 3.08/0.79    inference(subsumption_resolution,[],[f716,f91])).
% 3.08/0.79  fof(f91,plain,(
% 3.08/0.79    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.08/0.79    inference(equality_resolution,[],[f67])).
% 3.08/0.79  fof(f67,plain,(
% 3.08/0.79    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.08/0.79    inference(cnf_transformation,[],[f55])).
% 3.08/0.79  fof(f716,plain,(
% 3.08/0.79    ~r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl3_48),
% 3.08/0.79    inference(superposition,[],[f586,f709])).
% 3.08/0.79  fof(f709,plain,(
% 3.08/0.79    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_xboole_0(X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.08/0.79    inference(subsumption_resolution,[],[f255,f291])).
% 3.08/0.79  fof(f291,plain,(
% 3.08/0.79    ( ! [X2,X3] : (m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2)) )),
% 3.08/0.79    inference(subsumption_resolution,[],[f288,f75])).
% 3.08/0.79  fof(f75,plain,(
% 3.08/0.79    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.08/0.79    inference(cnf_transformation,[],[f37])).
% 3.08/0.79  fof(f37,plain,(
% 3.08/0.79    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.08/0.79    inference(flattening,[],[f36])).
% 3.08/0.79  fof(f36,plain,(
% 3.08/0.79    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 3.08/0.79    inference(ennf_transformation,[],[f18])).
% 3.08/0.79  fof(f18,axiom,(
% 3.08/0.79    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 3.08/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 3.08/0.79  fof(f288,plain,(
% 3.08/0.79    ( ! [X2,X3] : (m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) | ~m1_subset_1(k2_pre_topc(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2)) )),
% 3.08/0.79    inference(superposition,[],[f73,f71])).
% 3.08/0.79  fof(f71,plain,(
% 3.08/0.79    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.08/0.79    inference(cnf_transformation,[],[f32])).
% 3.08/0.79  fof(f32,plain,(
% 3.08/0.79    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.08/0.79    inference(ennf_transformation,[],[f20])).
% 3.08/0.79  fof(f20,axiom,(
% 3.08/0.79    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 3.08/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).
% 3.08/0.79  fof(f255,plain,(
% 3.08/0.79    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_xboole_0(X1,k2_tops_1(X0,X1)) | ~m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.08/0.79    inference(duplicate_literal_removal,[],[f254])).
% 3.08/0.79  fof(f254,plain,(
% 3.08/0.79    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_xboole_0(X1,k2_tops_1(X0,X1)) | ~m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.08/0.79    inference(superposition,[],[f90,f76])).
% 3.08/0.79  fof(f76,plain,(
% 3.08/0.79    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.08/0.79    inference(cnf_transformation,[],[f38])).
% 3.08/0.79  fof(f38,plain,(
% 3.08/0.79    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.08/0.79    inference(ennf_transformation,[],[f23])).
% 3.08/0.79  fof(f23,axiom,(
% 3.08/0.79    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 3.08/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).
% 3.08/0.79  fof(f90,plain,(
% 3.08/0.79    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.08/0.79    inference(cnf_transformation,[],[f48])).
% 3.08/0.79  fof(f48,plain,(
% 3.08/0.79    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.08/0.79    inference(flattening,[],[f47])).
% 3.08/0.79  fof(f47,plain,(
% 3.08/0.79    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 3.08/0.79    inference(ennf_transformation,[],[f13])).
% 3.08/0.79  fof(f13,axiom,(
% 3.08/0.79    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 3.08/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 3.08/0.79  fof(f586,plain,(
% 3.08/0.79    ~r1_tarski(k2_xboole_0(sK1,k2_tops_1(sK0,sK1)),k2_pre_topc(sK0,sK1)) | spl3_48),
% 3.08/0.79    inference(avatar_component_clause,[],[f584])).
% 3.08/0.79  fof(f493,plain,(
% 3.08/0.79    ~spl3_43 | spl3_41),
% 3.08/0.79    inference(avatar_split_clause,[],[f488,f471,f490])).
% 3.08/0.79  fof(f488,plain,(
% 3.08/0.79    ~r1_tarski(sK1,k2_pre_topc(sK0,sK1)) | spl3_41),
% 3.08/0.79    inference(resolution,[],[f473,f80])).
% 3.08/0.79  fof(f80,plain,(
% 3.08/0.79    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.08/0.79    inference(cnf_transformation,[],[f56])).
% 3.08/0.79  fof(f56,plain,(
% 3.08/0.79    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.08/0.79    inference(nnf_transformation,[],[f17])).
% 3.08/0.79  fof(f17,axiom,(
% 3.08/0.79    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.08/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 3.08/0.79  fof(f473,plain,(
% 3.08/0.79    ~m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | spl3_41),
% 3.08/0.79    inference(avatar_component_clause,[],[f471])).
% 3.08/0.79  fof(f478,plain,(
% 3.08/0.79    ~spl3_41 | spl3_42 | ~spl3_16),
% 3.08/0.79    inference(avatar_split_clause,[],[f469,f226,f475,f471])).
% 3.08/0.79  fof(f469,plain,(
% 3.08/0.79    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~spl3_16),
% 3.08/0.79    inference(superposition,[],[f161,f228])).
% 3.08/0.79  fof(f161,plain,(
% 3.08/0.79    ( ! [X2,X3] : (m1_subset_1(k4_xboole_0(X2,X3),k1_zfmisc_1(X2)) | ~m1_subset_1(X3,k1_zfmisc_1(X2))) )),
% 3.08/0.79    inference(duplicate_literal_removal,[],[f159])).
% 3.08/0.79  fof(f159,plain,(
% 3.08/0.79    ( ! [X2,X3] : (m1_subset_1(k4_xboole_0(X2,X3),k1_zfmisc_1(X2)) | ~m1_subset_1(X3,k1_zfmisc_1(X2)) | ~m1_subset_1(X3,k1_zfmisc_1(X2))) )),
% 3.08/0.79    inference(superposition,[],[f81,f70])).
% 3.08/0.79  fof(f429,plain,(
% 3.08/0.79    spl3_36 | ~spl3_16),
% 3.08/0.79    inference(avatar_split_clause,[],[f424,f226,f426])).
% 3.08/0.79  fof(f424,plain,(
% 3.08/0.79    r1_tarski(k2_pre_topc(sK0,sK1),k2_xboole_0(sK1,k2_tops_1(sK0,sK1))) | ~spl3_16),
% 3.08/0.79    inference(superposition,[],[f147,f228])).
% 3.08/0.79  fof(f147,plain,(
% 3.08/0.79    ( ! [X2,X3] : (r1_tarski(X2,k2_xboole_0(X3,k4_xboole_0(X2,X3)))) )),
% 3.08/0.79    inference(resolution,[],[f84,f91])).
% 3.08/0.79  fof(f84,plain,(
% 3.08/0.79    ( ! [X2,X0,X1] : (~r1_tarski(k4_xboole_0(X0,X1),X2) | r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 3.08/0.79    inference(cnf_transformation,[],[f45])).
% 3.08/0.79  fof(f45,plain,(
% 3.08/0.79    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 3.08/0.79    inference(ennf_transformation,[],[f5])).
% 3.08/0.79  fof(f5,axiom,(
% 3.08/0.79    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 3.08/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).
% 3.08/0.79  fof(f319,plain,(
% 3.08/0.79    spl3_16 | ~spl3_2 | ~spl3_10),
% 3.08/0.79    inference(avatar_split_clause,[],[f318,f177,f98,f226])).
% 3.08/0.79  fof(f98,plain,(
% 3.08/0.79    spl3_2 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)),
% 3.08/0.79    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 3.08/0.79  fof(f177,plain,(
% 3.08/0.79    spl3_10 <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.08/0.79    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 3.08/0.79  fof(f318,plain,(
% 3.08/0.79    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | (~spl3_2 | ~spl3_10)),
% 3.08/0.79    inference(subsumption_resolution,[],[f314,f178])).
% 3.08/0.79  fof(f178,plain,(
% 3.08/0.79    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_10),
% 3.08/0.79    inference(avatar_component_clause,[],[f177])).
% 3.08/0.79  fof(f314,plain,(
% 3.08/0.79    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_2),
% 3.08/0.79    inference(superposition,[],[f65,f99])).
% 3.08/0.79  fof(f99,plain,(
% 3.08/0.79    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~spl3_2),
% 3.08/0.79    inference(avatar_component_clause,[],[f98])).
% 3.08/0.79  fof(f312,plain,(
% 3.08/0.79    ~spl3_14 | spl3_15 | ~spl3_13),
% 3.08/0.79    inference(avatar_split_clause,[],[f311,f202,f212,f208])).
% 3.08/0.79  fof(f208,plain,(
% 3.08/0.79    spl3_14 <=> r1_tarski(sK1,k1_tops_1(sK0,sK1))),
% 3.08/0.79    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 3.08/0.79  fof(f202,plain,(
% 3.08/0.79    spl3_13 <=> r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 3.08/0.79    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 3.08/0.79  fof(f311,plain,(
% 3.08/0.79    sK1 = k1_tops_1(sK0,sK1) | ~r1_tarski(sK1,k1_tops_1(sK0,sK1)) | ~spl3_13),
% 3.08/0.79    inference(resolution,[],[f204,f68])).
% 3.08/0.79  fof(f204,plain,(
% 3.08/0.79    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~spl3_13),
% 3.08/0.79    inference(avatar_component_clause,[],[f202])).
% 3.08/0.79  fof(f310,plain,(
% 3.08/0.79    spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_15),
% 3.08/0.79    inference(avatar_contradiction_clause,[],[f309])).
% 3.08/0.79  fof(f309,plain,(
% 3.08/0.79    $false | (spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_15)),
% 3.08/0.79    inference(subsumption_resolution,[],[f308,f111])).
% 3.08/0.79  fof(f308,plain,(
% 3.08/0.79    ~l1_pre_topc(sK0) | (spl3_2 | ~spl3_3 | ~spl3_15)),
% 3.08/0.79    inference(subsumption_resolution,[],[f307,f106])).
% 3.08/0.79  fof(f307,plain,(
% 3.08/0.79    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (spl3_2 | ~spl3_15)),
% 3.08/0.79    inference(subsumption_resolution,[],[f306,f100])).
% 3.08/0.79  fof(f100,plain,(
% 3.08/0.79    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | spl3_2),
% 3.08/0.79    inference(avatar_component_clause,[],[f98])).
% 3.08/0.79  fof(f306,plain,(
% 3.08/0.79    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl3_15),
% 3.08/0.79    inference(superposition,[],[f71,f214])).
% 3.08/0.79  fof(f214,plain,(
% 3.08/0.79    sK1 = k1_tops_1(sK0,sK1) | ~spl3_15),
% 3.08/0.79    inference(avatar_component_clause,[],[f212])).
% 3.08/0.79  fof(f301,plain,(
% 3.08/0.79    ~spl3_1 | ~spl3_3 | ~spl3_4 | spl3_14),
% 3.08/0.79    inference(avatar_contradiction_clause,[],[f292])).
% 3.08/0.79  fof(f292,plain,(
% 3.08/0.79    $false | (~spl3_1 | ~spl3_3 | ~spl3_4 | spl3_14)),
% 3.08/0.79    inference(unit_resulting_resolution,[],[f111,f95,f91,f106,f210,f106,f78])).
% 3.08/0.79  fof(f78,plain,(
% 3.08/0.79    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | r1_tarski(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.08/0.79    inference(cnf_transformation,[],[f42])).
% 3.08/0.79  fof(f42,plain,(
% 3.08/0.79    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.08/0.79    inference(flattening,[],[f41])).
% 3.08/0.79  fof(f41,plain,(
% 3.08/0.79    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(X1,k1_tops_1(X0,X2)) | (~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.08/0.79    inference(ennf_transformation,[],[f22])).
% 3.08/0.79  fof(f22,axiom,(
% 3.08/0.79    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v3_pre_topc(X1,X0)) => r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 3.08/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tops_1)).
% 3.08/0.79  fof(f210,plain,(
% 3.08/0.79    ~r1_tarski(sK1,k1_tops_1(sK0,sK1)) | spl3_14),
% 3.08/0.79    inference(avatar_component_clause,[],[f208])).
% 3.08/0.79  fof(f95,plain,(
% 3.08/0.79    v3_pre_topc(sK1,sK0) | ~spl3_1),
% 3.08/0.79    inference(avatar_component_clause,[],[f94])).
% 3.08/0.79  fof(f94,plain,(
% 3.08/0.79    spl3_1 <=> v3_pre_topc(sK1,sK0)),
% 3.08/0.79    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 3.08/0.79  fof(f246,plain,(
% 3.08/0.79    spl3_17 | ~spl3_3 | ~spl3_4 | ~spl3_5),
% 3.08/0.79    inference(avatar_split_clause,[],[f241,f114,f109,f104,f243])).
% 3.08/0.79  fof(f243,plain,(
% 3.08/0.79    spl3_17 <=> v3_pre_topc(k1_tops_1(sK0,sK1),sK0)),
% 3.08/0.79    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 3.08/0.79  fof(f114,plain,(
% 3.08/0.79    spl3_5 <=> v2_pre_topc(sK0)),
% 3.08/0.79    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 3.08/0.79  fof(f241,plain,(
% 3.08/0.79    v3_pre_topc(k1_tops_1(sK0,sK1),sK0) | (~spl3_3 | ~spl3_4 | ~spl3_5)),
% 3.08/0.79    inference(subsumption_resolution,[],[f240,f116])).
% 3.08/0.79  fof(f116,plain,(
% 3.08/0.79    v2_pre_topc(sK0) | ~spl3_5),
% 3.08/0.79    inference(avatar_component_clause,[],[f114])).
% 3.08/0.79  fof(f240,plain,(
% 3.08/0.79    v3_pre_topc(k1_tops_1(sK0,sK1),sK0) | ~v2_pre_topc(sK0) | (~spl3_3 | ~spl3_4)),
% 3.08/0.79    inference(subsumption_resolution,[],[f237,f111])).
% 3.08/0.79  fof(f237,plain,(
% 3.08/0.79    v3_pre_topc(k1_tops_1(sK0,sK1),sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~spl3_3),
% 3.08/0.79    inference(resolution,[],[f77,f106])).
% 3.08/0.79  fof(f77,plain,(
% 3.08/0.79    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(k1_tops_1(X0,X1),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.08/0.79    inference(cnf_transformation,[],[f40])).
% 3.08/0.79  fof(f40,plain,(
% 3.08/0.79    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.08/0.79    inference(flattening,[],[f39])).
% 3.08/0.79  fof(f39,plain,(
% 3.08/0.79    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.08/0.79    inference(ennf_transformation,[],[f19])).
% 3.08/0.79  fof(f19,axiom,(
% 3.08/0.79    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 3.08/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).
% 3.08/0.79  fof(f224,plain,(
% 3.08/0.79    ~spl3_3 | ~spl3_4 | spl3_10),
% 3.08/0.79    inference(avatar_contradiction_clause,[],[f223])).
% 3.08/0.79  fof(f223,plain,(
% 3.08/0.79    $false | (~spl3_3 | ~spl3_4 | spl3_10)),
% 3.08/0.79    inference(subsumption_resolution,[],[f222,f111])).
% 3.08/0.79  fof(f222,plain,(
% 3.08/0.79    ~l1_pre_topc(sK0) | (~spl3_3 | spl3_10)),
% 3.08/0.79    inference(subsumption_resolution,[],[f217,f106])).
% 3.08/0.79  fof(f217,plain,(
% 3.08/0.79    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl3_10),
% 3.08/0.79    inference(resolution,[],[f75,f179])).
% 3.08/0.79  fof(f179,plain,(
% 3.08/0.79    ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_10),
% 3.08/0.79    inference(avatar_component_clause,[],[f177])).
% 3.08/0.79  fof(f205,plain,(
% 3.08/0.79    spl3_13 | ~spl3_3 | ~spl3_4),
% 3.08/0.79    inference(avatar_split_clause,[],[f200,f109,f104,f202])).
% 3.08/0.79  fof(f200,plain,(
% 3.08/0.79    r1_tarski(k1_tops_1(sK0,sK1),sK1) | (~spl3_3 | ~spl3_4)),
% 3.08/0.79    inference(subsumption_resolution,[],[f198,f111])).
% 3.08/0.79  fof(f198,plain,(
% 3.08/0.79    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~l1_pre_topc(sK0) | ~spl3_3),
% 3.08/0.79    inference(resolution,[],[f83,f106])).
% 3.08/0.79  fof(f83,plain,(
% 3.08/0.79    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k1_tops_1(X0,X1),X1) | ~l1_pre_topc(X0)) )),
% 3.08/0.79    inference(cnf_transformation,[],[f44])).
% 3.08/0.79  fof(f44,plain,(
% 3.08/0.79    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.08/0.79    inference(ennf_transformation,[],[f21])).
% 3.08/0.79  fof(f21,axiom,(
% 3.08/0.79    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 3.08/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).
% 3.08/0.79  fof(f117,plain,(
% 3.08/0.79    spl3_5),
% 3.08/0.79    inference(avatar_split_clause,[],[f60,f114])).
% 3.08/0.79  fof(f60,plain,(
% 3.08/0.79    v2_pre_topc(sK0)),
% 3.08/0.79    inference(cnf_transformation,[],[f53])).
% 3.08/0.79  fof(f53,plain,(
% 3.08/0.79    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 3.08/0.79    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f50,f52,f51])).
% 3.08/0.79  fof(f51,plain,(
% 3.08/0.79    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | ~v3_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 3.08/0.79    introduced(choice_axiom,[])).
% 3.08/0.79  fof(f52,plain,(
% 3.08/0.79    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | ~v3_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 3.08/0.79    introduced(choice_axiom,[])).
% 3.08/0.79  fof(f50,plain,(
% 3.08/0.79    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.08/0.79    inference(flattening,[],[f49])).
% 3.08/0.79  fof(f49,plain,(
% 3.08/0.79    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.08/0.79    inference(nnf_transformation,[],[f28])).
% 3.08/0.79  fof(f28,plain,(
% 3.08/0.79    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.08/0.79    inference(flattening,[],[f27])).
% 3.08/0.79  fof(f27,plain,(
% 3.08/0.79    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 3.08/0.79    inference(ennf_transformation,[],[f26])).
% 3.08/0.79  fof(f26,negated_conjecture,(
% 3.08/0.79    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 3.08/0.79    inference(negated_conjecture,[],[f25])).
% 3.08/0.79  fof(f25,conjecture,(
% 3.08/0.79    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 3.08/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_tops_1)).
% 3.08/0.79  fof(f112,plain,(
% 3.08/0.79    spl3_4),
% 3.08/0.79    inference(avatar_split_clause,[],[f61,f109])).
% 3.08/0.79  fof(f61,plain,(
% 3.08/0.79    l1_pre_topc(sK0)),
% 3.08/0.79    inference(cnf_transformation,[],[f53])).
% 3.08/0.79  fof(f107,plain,(
% 3.08/0.79    spl3_3),
% 3.08/0.79    inference(avatar_split_clause,[],[f62,f104])).
% 3.08/0.79  fof(f62,plain,(
% 3.08/0.79    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.08/0.79    inference(cnf_transformation,[],[f53])).
% 3.08/0.79  fof(f102,plain,(
% 3.08/0.79    spl3_1 | spl3_2),
% 3.08/0.79    inference(avatar_split_clause,[],[f63,f98,f94])).
% 3.08/0.79  fof(f63,plain,(
% 3.08/0.79    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)),
% 3.08/0.79    inference(cnf_transformation,[],[f53])).
% 3.08/0.79  fof(f101,plain,(
% 3.08/0.79    ~spl3_1 | ~spl3_2),
% 3.08/0.79    inference(avatar_split_clause,[],[f64,f98,f94])).
% 3.08/0.79  fof(f64,plain,(
% 3.08/0.79    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)),
% 3.08/0.79    inference(cnf_transformation,[],[f53])).
% 3.08/0.79  % SZS output end Proof for theBenchmark
% 3.08/0.79  % (11018)------------------------------
% 3.08/0.79  % (11018)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.08/0.79  % (11018)Termination reason: Refutation
% 3.08/0.79  
% 3.08/0.79  % (11018)Memory used [KB]: 8187
% 3.08/0.79  % (11018)Time elapsed: 0.383 s
% 3.08/0.79  % (11018)------------------------------
% 3.08/0.79  % (11018)------------------------------
% 3.35/0.81  % (10996)Success in time 0.448 s
%------------------------------------------------------------------------------
