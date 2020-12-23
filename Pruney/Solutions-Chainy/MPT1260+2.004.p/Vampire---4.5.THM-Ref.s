%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:33 EST 2020

% Result     : Theorem 3.86s
% Output     : Refutation 3.86s
% Verified   : 
% Statistics : Number of formulae       :  181 ( 336 expanded)
%              Number of leaves         :   40 ( 126 expanded)
%              Depth                    :   11
%              Number of atoms          :  543 (1052 expanded)
%              Number of equality atoms :   95 ( 214 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3072,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f116,f117,f122,f127,f132,f239,f264,f392,f422,f1917,f1957,f1995,f2005,f2011,f2038,f2049,f2092,f2929,f2972,f3065,f3071])).

fof(f3071,plain,
    ( sK1 != k1_tops_1(sK0,sK1)
    | v3_pre_topc(sK1,sK0)
    | ~ v3_pre_topc(k1_tops_1(sK0,sK1),sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f3065,plain,(
    ~ spl3_65 ),
    inference(avatar_contradiction_clause,[],[f3048])).

fof(f3048,plain,
    ( $false
    | ~ spl3_65 ),
    inference(unit_resulting_resolution,[],[f149,f2133,f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f2133,plain,
    ( ! [X2] : ~ m1_subset_1(X2,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl3_65 ),
    inference(avatar_component_clause,[],[f2132])).

fof(f2132,plain,
    ( spl3_65
  <=> ! [X2] : ~ m1_subset_1(X2,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_65])])).

fof(f149,plain,(
    ! [X0,X1] : m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0)) ),
    inference(backward_demodulation,[],[f105,f97])).

fof(f97,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f105,plain,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).

fof(f2972,plain,
    ( spl3_27
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_96 ),
    inference(avatar_split_clause,[],[f2971,f2926,f124,f119,f430])).

fof(f430,plain,
    ( spl3_27
  <=> sK1 = k1_tops_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f119,plain,
    ( spl3_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f124,plain,
    ( spl3_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f2926,plain,
    ( spl3_96
  <=> sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_96])])).

fof(f2971,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_96 ),
    inference(subsumption_resolution,[],[f2970,f126])).

fof(f126,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f124])).

fof(f2970,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl3_3
    | ~ spl3_96 ),
    inference(subsumption_resolution,[],[f2946,f121])).

fof(f121,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f119])).

fof(f2946,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_96 ),
    inference(superposition,[],[f273,f2928])).

fof(f2928,plain,
    ( sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl3_96 ),
    inference(avatar_component_clause,[],[f2926])).

fof(f273,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f272])).

fof(f272,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(superposition,[],[f74,f82])).

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
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f2929,plain,
    ( spl3_65
    | spl3_96
    | ~ spl3_20
    | ~ spl3_57 ),
    inference(avatar_split_clause,[],[f2924,f2046,f353,f2926,f2132])).

fof(f353,plain,
    ( spl3_20
  <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f2046,plain,
    ( spl3_57
  <=> sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_57])])).

fof(f2924,plain,
    ( ! [X9] :
        ( sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
        | ~ m1_subset_1(X9,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) )
    | ~ spl3_20
    | ~ spl3_57 ),
    inference(subsumption_resolution,[],[f2890,f355])).

fof(f355,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f353])).

fof(f2890,plain,
    ( ! [X9] :
        ( sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
        | ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
        | ~ m1_subset_1(X9,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) )
    | ~ spl3_57 ),
    inference(superposition,[],[f708,f2048])).

fof(f2048,plain,
    ( sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))
    | ~ spl3_57 ),
    inference(avatar_component_clause,[],[f2046])).

fof(f708,plain,(
    ! [X4,X2,X3] :
      ( k3_subset_1(X2,X3) = k4_xboole_0(k3_subset_1(X2,X3),X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
      | ~ m1_subset_1(X4,k1_zfmisc_1(X2)) ) ),
    inference(subsumption_resolution,[],[f703,f92])).

fof(f703,plain,(
    ! [X4,X2,X3] :
      ( k3_subset_1(X2,X3) = k4_xboole_0(k3_subset_1(X2,X3),X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
      | ~ m1_subset_1(X4,k1_zfmisc_1(X2))
      | ~ m1_subset_1(k3_subset_1(X2,X3),k1_zfmisc_1(X2)) ) ),
    inference(superposition,[],[f306,f74])).

fof(f306,plain,(
    ! [X4,X5,X3] :
      ( k3_subset_1(X3,X4) = k7_subset_1(X3,k3_subset_1(X3,X4),X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(X3)) ) ),
    inference(subsumption_resolution,[],[f302,f92])).

fof(f302,plain,(
    ! [X4,X5,X3] :
      ( k3_subset_1(X3,X4) = k7_subset_1(X3,k3_subset_1(X3,X4),X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
      | ~ m1_subset_1(k3_subset_1(X3,X4),k1_zfmisc_1(X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(X3)) ) ),
    inference(superposition,[],[f84,f102])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
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
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_subset_1)).

fof(f2092,plain,
    ( ~ spl3_54
    | spl3_56 ),
    inference(avatar_split_clause,[],[f2091,f2042,f1954])).

fof(f1954,plain,
    ( spl3_54
  <=> r1_tarski(sK1,k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_54])])).

fof(f2042,plain,
    ( spl3_56
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_56])])).

fof(f2091,plain,
    ( ~ r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | spl3_56 ),
    inference(resolution,[],[f2044,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f2044,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | spl3_56 ),
    inference(avatar_component_clause,[],[f2042])).

fof(f2049,plain,
    ( ~ spl3_56
    | spl3_57
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f2024,f222,f2046,f2042])).

fof(f222,plain,
    ( spl3_10
  <=> k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f2024,plain,
    ( sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl3_10 ),
    inference(superposition,[],[f206,f224])).

fof(f224,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f222])).

fof(f206,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k4_xboole_0(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f202])).

fof(f202,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k4_xboole_0(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(superposition,[],[f78,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f78,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f2038,plain,
    ( spl3_20
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f2020,f222,f353])).

fof(f2020,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl3_10 ),
    inference(superposition,[],[f149,f224])).

fof(f2011,plain,
    ( spl3_10
    | ~ spl3_2
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f2010,f218,f113,f222])).

fof(f113,plain,
    ( spl3_2
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f218,plain,
    ( spl3_9
  <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f2010,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ spl3_2
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f2007,f219])).

fof(f219,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f218])).

fof(f2007,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_2 ),
    inference(superposition,[],[f74,f114])).

fof(f114,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f113])).

fof(f2005,plain,
    ( ~ spl3_21
    | spl3_27
    | ~ spl3_26 ),
    inference(avatar_split_clause,[],[f1933,f426,f430,f374])).

fof(f374,plain,
    ( spl3_21
  <=> r1_tarski(sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f426,plain,
    ( spl3_26
  <=> r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f1933,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | ~ spl3_26 ),
    inference(resolution,[],[f427,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f64])).

fof(f64,plain,(
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

fof(f427,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl3_26 ),
    inference(avatar_component_clause,[],[f426])).

fof(f1995,plain,
    ( ~ spl3_3
    | ~ spl3_4
    | spl3_10
    | ~ spl3_27 ),
    inference(avatar_contradiction_clause,[],[f1994])).

fof(f1994,plain,
    ( $false
    | ~ spl3_3
    | ~ spl3_4
    | spl3_10
    | ~ spl3_27 ),
    inference(subsumption_resolution,[],[f1993,f126])).

fof(f1993,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl3_3
    | spl3_10
    | ~ spl3_27 ),
    inference(subsumption_resolution,[],[f1992,f121])).

fof(f1992,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl3_10
    | ~ spl3_27 ),
    inference(subsumption_resolution,[],[f1989,f223])).

fof(f223,plain,
    ( k2_tops_1(sK0,sK1) != k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | spl3_10 ),
    inference(avatar_component_clause,[],[f222])).

fof(f1989,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_27 ),
    inference(superposition,[],[f321,f432])).

fof(f432,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ spl3_27 ),
    inference(avatar_component_clause,[],[f430])).

fof(f321,plain,(
    ! [X2,X3] :
      ( k2_tops_1(X2,X3) = k4_xboole_0(k2_pre_topc(X2,X3),k1_tops_1(X2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2) ) ),
    inference(subsumption_resolution,[],[f319,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f319,plain,(
    ! [X2,X3] :
      ( k2_tops_1(X2,X3) = k4_xboole_0(k2_pre_topc(X2,X3),k1_tops_1(X2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2)
      | ~ m1_subset_1(k2_pre_topc(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) ) ),
    inference(superposition,[],[f81,f74])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

fof(f1957,plain,
    ( spl3_54
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f1952,f124,f119,f1954])).

fof(f1952,plain,
    ( r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f1942,f126])).

fof(f1942,plain,
    ( r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_3 ),
    inference(resolution,[],[f648,f121])).

fof(f648,plain,(
    ! [X8,X7] :
      ( ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X8)))
      | r1_tarski(X7,k2_pre_topc(X8,X7))
      | ~ l1_pre_topc(X8) ) ),
    inference(superposition,[],[f99,f298])).

fof(f298,plain,(
    ! [X2,X3] :
      ( k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2) ) ),
    inference(subsumption_resolution,[],[f295,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(f295,plain,(
    ! [X2,X3] :
      ( k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2)
      | ~ m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) ) ),
    inference(duplicate_literal_removal,[],[f292])).

fof(f292,plain,(
    ! [X2,X3] :
      ( k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2)
      | ~ m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ) ),
    inference(superposition,[],[f86,f100])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f86,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

fof(f99,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f1917,plain,
    ( spl3_26
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f1916,f124,f119,f426])).

fof(f1916,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f1907,f126])).

fof(f1907,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl3_3 ),
    inference(resolution,[],[f626,f121])).

fof(f626,plain,(
    ! [X6,X7] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X7)))
      | r1_tarski(k1_tops_1(X7,X6),X6)
      | ~ l1_pre_topc(X7) ) ),
    inference(superposition,[],[f155,f273])).

fof(f155,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(resolution,[],[f149,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f422,plain,
    ( ~ spl3_10
    | spl3_2
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f421,f218,f113,f222])).

fof(f421,plain,
    ( k2_tops_1(sK0,sK1) != k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | spl3_2
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f420,f219])).

fof(f420,plain,
    ( k2_tops_1(sK0,sK1) != k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_2 ),
    inference(superposition,[],[f115,f74])).

fof(f115,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f113])).

fof(f392,plain,
    ( spl3_21
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f391,f124,f119,f109,f374])).

fof(f109,plain,
    ( spl3_1
  <=> v3_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f391,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f366,f106])).

fof(f106,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f65])).

fof(f366,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | ~ r1_tarski(sK1,sK1)
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(resolution,[],[f334,f121])).

fof(f334,plain,
    ( ! [X16] :
        ( ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X16,sK0)
        | r1_tarski(X16,k1_tops_1(sK0,sK1))
        | ~ r1_tarski(X16,sK1) )
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f329,f126])).

fof(f329,plain,
    ( ! [X16] :
        ( ~ r1_tarski(X16,sK1)
        | ~ v3_pre_topc(X16,sK0)
        | r1_tarski(X16,k1_tops_1(sK0,sK1))
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl3_3 ),
    inference(resolution,[],[f89,f121])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X1,X2)
      | ~ v3_pre_topc(X1,X0)
      | r1_tarski(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f49])).

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
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
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

fof(f264,plain,
    ( spl3_13
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f259,f129,f124,f119,f261])).

fof(f261,plain,
    ( spl3_13
  <=> v3_pre_topc(k1_tops_1(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f129,plain,
    ( spl3_5
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f259,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f258,f131])).

fof(f131,plain,
    ( v2_pre_topc(sK0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f129])).

fof(f258,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f254,f126])).

fof(f254,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl3_3 ),
    inference(resolution,[],[f88,f121])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

fof(f239,plain,
    ( ~ spl3_3
    | ~ spl3_4
    | spl3_9 ),
    inference(avatar_contradiction_clause,[],[f238])).

fof(f238,plain,
    ( $false
    | ~ spl3_3
    | ~ spl3_4
    | spl3_9 ),
    inference(subsumption_resolution,[],[f237,f126])).

fof(f237,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl3_3
    | spl3_9 ),
    inference(subsumption_resolution,[],[f234,f121])).

fof(f234,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl3_9 ),
    inference(resolution,[],[f85,f220])).

fof(f220,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_9 ),
    inference(avatar_component_clause,[],[f218])).

fof(f132,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f69,f129])).

fof(f69,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,
    ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
      | ~ v3_pre_topc(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
      | v3_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f60,f62,f61])).

fof(f61,plain,
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

fof(f62,plain,
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
    inference(flattening,[],[f59])).

fof(f59,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    inference(negated_conjecture,[],[f31])).

fof(f31,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tops_1)).

fof(f127,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f70,f124])).

fof(f70,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f63])).

fof(f122,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f71,f119])).

fof(f71,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f63])).

fof(f117,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f72,f113,f109])).

fof(f72,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f63])).

fof(f116,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f73,f113,f109])).

fof(f73,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f63])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:05:14 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.49  % (10090)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.49  % (10111)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.51  % (10104)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.52  % (10105)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.52  % (10112)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.52  % (10096)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.52  % (10088)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (10087)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.53  % (10086)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.53  % (10101)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.53  % (10095)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.53  % (10082)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.54  % (10099)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.54  % (10089)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.37/0.54  % (10085)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.37/0.54  % (10108)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.37/0.55  % (10103)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.37/0.55  % (10091)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.37/0.55  % (10110)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.37/0.55  % (10107)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.37/0.55  % (10084)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.37/0.55  % (10094)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.37/0.55  % (10083)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.37/0.55  % (10098)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.37/0.55  % (10102)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.55/0.56  % (10109)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.55/0.56  % (10093)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.55/0.57  % (10097)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.55/0.58  % (10106)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.55/0.59  % (10092)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 3.20/0.79  % (10107)Time limit reached!
% 3.20/0.79  % (10107)------------------------------
% 3.20/0.79  % (10107)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.20/0.79  % (10107)Termination reason: Time limit
% 3.20/0.79  % (10107)Termination phase: Saturation
% 3.20/0.79  
% 3.20/0.79  % (10107)Memory used [KB]: 12153
% 3.20/0.79  % (10107)Time elapsed: 0.400 s
% 3.20/0.79  % (10107)------------------------------
% 3.20/0.79  % (10107)------------------------------
% 3.20/0.81  % (10084)Time limit reached!
% 3.20/0.81  % (10084)------------------------------
% 3.20/0.81  % (10084)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.20/0.81  % (10084)Termination reason: Time limit
% 3.20/0.81  
% 3.20/0.81  % (10084)Memory used [KB]: 6396
% 3.20/0.81  % (10084)Time elapsed: 0.406 s
% 3.20/0.81  % (10084)------------------------------
% 3.20/0.81  % (10084)------------------------------
% 3.86/0.86  % (10104)Refutation found. Thanks to Tanya!
% 3.86/0.86  % SZS status Theorem for theBenchmark
% 3.86/0.87  % SZS output start Proof for theBenchmark
% 3.86/0.87  fof(f3072,plain,(
% 3.86/0.87    $false),
% 3.86/0.87    inference(avatar_sat_refutation,[],[f116,f117,f122,f127,f132,f239,f264,f392,f422,f1917,f1957,f1995,f2005,f2011,f2038,f2049,f2092,f2929,f2972,f3065,f3071])).
% 3.86/0.87  fof(f3071,plain,(
% 3.86/0.87    sK1 != k1_tops_1(sK0,sK1) | v3_pre_topc(sK1,sK0) | ~v3_pre_topc(k1_tops_1(sK0,sK1),sK0)),
% 3.86/0.87    introduced(theory_tautology_sat_conflict,[])).
% 3.86/0.87  fof(f3065,plain,(
% 3.86/0.87    ~spl3_65),
% 3.86/0.87    inference(avatar_contradiction_clause,[],[f3048])).
% 3.86/0.87  fof(f3048,plain,(
% 3.86/0.87    $false | ~spl3_65),
% 3.86/0.87    inference(unit_resulting_resolution,[],[f149,f2133,f92])).
% 3.86/0.87  fof(f92,plain,(
% 3.86/0.87    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.86/0.87    inference(cnf_transformation,[],[f51])).
% 3.86/0.87  fof(f51,plain,(
% 3.86/0.87    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.86/0.87    inference(ennf_transformation,[],[f12])).
% 3.86/0.87  fof(f12,axiom,(
% 3.86/0.87    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 3.86/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 3.86/0.87  fof(f2133,plain,(
% 3.86/0.87    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))) ) | ~spl3_65),
% 3.86/0.87    inference(avatar_component_clause,[],[f2132])).
% 3.86/0.87  fof(f2132,plain,(
% 3.86/0.87    spl3_65 <=> ! [X2] : ~m1_subset_1(X2,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))),
% 3.86/0.87    introduced(avatar_definition,[new_symbols(naming,[spl3_65])])).
% 3.86/0.87  fof(f149,plain,(
% 3.86/0.87    ( ! [X0,X1] : (m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0))) )),
% 3.86/0.87    inference(backward_demodulation,[],[f105,f97])).
% 3.86/0.87  fof(f97,plain,(
% 3.86/0.87    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 3.86/0.87    inference(cnf_transformation,[],[f18])).
% 3.86/0.87  fof(f18,axiom,(
% 3.86/0.87    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 3.86/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 3.86/0.87  fof(f105,plain,(
% 3.86/0.87    ( ! [X0,X1] : (m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 3.86/0.87    inference(cnf_transformation,[],[f13])).
% 3.86/0.87  fof(f13,axiom,(
% 3.86/0.87    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))),
% 3.86/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).
% 3.86/0.87  fof(f2972,plain,(
% 3.86/0.87    spl3_27 | ~spl3_3 | ~spl3_4 | ~spl3_96),
% 3.86/0.87    inference(avatar_split_clause,[],[f2971,f2926,f124,f119,f430])).
% 3.86/0.87  fof(f430,plain,(
% 3.86/0.87    spl3_27 <=> sK1 = k1_tops_1(sK0,sK1)),
% 3.86/0.87    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 3.86/0.87  fof(f119,plain,(
% 3.86/0.87    spl3_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.86/0.87    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 3.86/0.87  fof(f124,plain,(
% 3.86/0.87    spl3_4 <=> l1_pre_topc(sK0)),
% 3.86/0.87    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 3.86/0.87  fof(f2926,plain,(
% 3.86/0.87    spl3_96 <=> sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 3.86/0.87    introduced(avatar_definition,[new_symbols(naming,[spl3_96])])).
% 3.86/0.87  fof(f2971,plain,(
% 3.86/0.87    sK1 = k1_tops_1(sK0,sK1) | (~spl3_3 | ~spl3_4 | ~spl3_96)),
% 3.86/0.87    inference(subsumption_resolution,[],[f2970,f126])).
% 3.86/0.87  fof(f126,plain,(
% 3.86/0.87    l1_pre_topc(sK0) | ~spl3_4),
% 3.86/0.87    inference(avatar_component_clause,[],[f124])).
% 3.86/0.87  fof(f2970,plain,(
% 3.86/0.87    sK1 = k1_tops_1(sK0,sK1) | ~l1_pre_topc(sK0) | (~spl3_3 | ~spl3_96)),
% 3.86/0.87    inference(subsumption_resolution,[],[f2946,f121])).
% 3.86/0.87  fof(f121,plain,(
% 3.86/0.87    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_3),
% 3.86/0.87    inference(avatar_component_clause,[],[f119])).
% 3.86/0.87  fof(f2946,plain,(
% 3.86/0.87    sK1 = k1_tops_1(sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl3_96),
% 3.86/0.87    inference(superposition,[],[f273,f2928])).
% 3.86/0.87  fof(f2928,plain,(
% 3.86/0.87    sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl3_96),
% 3.86/0.87    inference(avatar_component_clause,[],[f2926])).
% 3.86/0.87  fof(f273,plain,(
% 3.86/0.87    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.86/0.87    inference(duplicate_literal_removal,[],[f272])).
% 3.86/0.87  fof(f272,plain,(
% 3.86/0.87    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.86/0.87    inference(superposition,[],[f74,f82])).
% 3.86/0.87  fof(f82,plain,(
% 3.86/0.87    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.86/0.87    inference(cnf_transformation,[],[f39])).
% 3.86/0.87  fof(f39,plain,(
% 3.86/0.87    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.86/0.87    inference(ennf_transformation,[],[f30])).
% 3.86/0.87  fof(f30,axiom,(
% 3.86/0.87    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 3.86/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).
% 3.86/0.87  fof(f74,plain,(
% 3.86/0.87    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.86/0.87    inference(cnf_transformation,[],[f35])).
% 3.86/0.87  fof(f35,plain,(
% 3.86/0.87    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.86/0.87    inference(ennf_transformation,[],[f19])).
% 3.86/0.87  fof(f19,axiom,(
% 3.86/0.87    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 3.86/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 3.86/0.87  fof(f2929,plain,(
% 3.86/0.87    spl3_65 | spl3_96 | ~spl3_20 | ~spl3_57),
% 3.86/0.87    inference(avatar_split_clause,[],[f2924,f2046,f353,f2926,f2132])).
% 3.86/0.87  fof(f353,plain,(
% 3.86/0.87    spl3_20 <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))),
% 3.86/0.87    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 3.86/0.87  fof(f2046,plain,(
% 3.86/0.87    spl3_57 <=> sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))),
% 3.86/0.87    introduced(avatar_definition,[new_symbols(naming,[spl3_57])])).
% 3.86/0.87  fof(f2924,plain,(
% 3.86/0.87    ( ! [X9] : (sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~m1_subset_1(X9,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))) ) | (~spl3_20 | ~spl3_57)),
% 3.86/0.87    inference(subsumption_resolution,[],[f2890,f355])).
% 3.86/0.87  fof(f355,plain,(
% 3.86/0.87    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~spl3_20),
% 3.86/0.87    inference(avatar_component_clause,[],[f353])).
% 3.86/0.87  fof(f2890,plain,(
% 3.86/0.87    ( ! [X9] : (sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~m1_subset_1(X9,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))) ) | ~spl3_57),
% 3.86/0.87    inference(superposition,[],[f708,f2048])).
% 3.86/0.87  fof(f2048,plain,(
% 3.86/0.87    sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) | ~spl3_57),
% 3.86/0.87    inference(avatar_component_clause,[],[f2046])).
% 3.86/0.87  fof(f708,plain,(
% 3.86/0.87    ( ! [X4,X2,X3] : (k3_subset_1(X2,X3) = k4_xboole_0(k3_subset_1(X2,X3),X3) | ~m1_subset_1(X3,k1_zfmisc_1(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(X2))) )),
% 3.86/0.87    inference(subsumption_resolution,[],[f703,f92])).
% 3.86/0.87  fof(f703,plain,(
% 3.86/0.87    ( ! [X4,X2,X3] : (k3_subset_1(X2,X3) = k4_xboole_0(k3_subset_1(X2,X3),X3) | ~m1_subset_1(X3,k1_zfmisc_1(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(X2)) | ~m1_subset_1(k3_subset_1(X2,X3),k1_zfmisc_1(X2))) )),
% 3.86/0.87    inference(superposition,[],[f306,f74])).
% 3.86/0.87  fof(f306,plain,(
% 3.86/0.87    ( ! [X4,X5,X3] : (k3_subset_1(X3,X4) = k7_subset_1(X3,k3_subset_1(X3,X4),X4) | ~m1_subset_1(X4,k1_zfmisc_1(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(X3))) )),
% 3.86/0.87    inference(subsumption_resolution,[],[f302,f92])).
% 3.86/0.87  fof(f302,plain,(
% 3.86/0.87    ( ! [X4,X5,X3] : (k3_subset_1(X3,X4) = k7_subset_1(X3,k3_subset_1(X3,X4),X4) | ~m1_subset_1(X4,k1_zfmisc_1(X3)) | ~m1_subset_1(k3_subset_1(X3,X4),k1_zfmisc_1(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(X3))) )),
% 3.86/0.87    inference(superposition,[],[f84,f102])).
% 3.86/0.87  fof(f102,plain,(
% 3.86/0.87    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X1) = X1 | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 3.86/0.87    inference(cnf_transformation,[],[f58])).
% 3.86/0.87  fof(f58,plain,(
% 3.86/0.87    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X1) = X1 | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 3.86/0.87    inference(ennf_transformation,[],[f15])).
% 3.86/0.87  fof(f15,axiom,(
% 3.86/0.87    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X1) = X1)),
% 3.86/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k9_subset_1)).
% 3.86/0.87  fof(f84,plain,(
% 3.86/0.87    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.86/0.87    inference(cnf_transformation,[],[f41])).
% 3.86/0.87  fof(f41,plain,(
% 3.86/0.87    ! [X0,X1] : (! [X2] : (k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.86/0.87    inference(ennf_transformation,[],[f20])).
% 3.86/0.87  fof(f20,axiom,(
% 3.86/0.87    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))))),
% 3.86/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_subset_1)).
% 3.86/0.87  fof(f2092,plain,(
% 3.86/0.87    ~spl3_54 | spl3_56),
% 3.86/0.87    inference(avatar_split_clause,[],[f2091,f2042,f1954])).
% 3.86/0.87  fof(f1954,plain,(
% 3.86/0.87    spl3_54 <=> r1_tarski(sK1,k2_pre_topc(sK0,sK1))),
% 3.86/0.87    introduced(avatar_definition,[new_symbols(naming,[spl3_54])])).
% 3.86/0.87  fof(f2042,plain,(
% 3.86/0.87    spl3_56 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))),
% 3.86/0.87    introduced(avatar_definition,[new_symbols(naming,[spl3_56])])).
% 3.86/0.87  fof(f2091,plain,(
% 3.86/0.87    ~r1_tarski(sK1,k2_pre_topc(sK0,sK1)) | spl3_56),
% 3.86/0.87    inference(resolution,[],[f2044,f91])).
% 3.86/0.87  fof(f91,plain,(
% 3.86/0.87    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.86/0.87    inference(cnf_transformation,[],[f66])).
% 3.86/0.87  fof(f66,plain,(
% 3.86/0.87    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.86/0.87    inference(nnf_transformation,[],[f22])).
% 3.86/0.87  fof(f22,axiom,(
% 3.86/0.87    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.86/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 3.86/0.87  fof(f2044,plain,(
% 3.86/0.87    ~m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | spl3_56),
% 3.86/0.87    inference(avatar_component_clause,[],[f2042])).
% 3.86/0.87  fof(f2049,plain,(
% 3.86/0.87    ~spl3_56 | spl3_57 | ~spl3_10),
% 3.86/0.87    inference(avatar_split_clause,[],[f2024,f222,f2046,f2042])).
% 3.86/0.87  fof(f222,plain,(
% 3.86/0.87    spl3_10 <=> k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)),
% 3.86/0.87    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 3.86/0.87  fof(f2024,plain,(
% 3.86/0.87    sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~spl3_10),
% 3.86/0.87    inference(superposition,[],[f206,f224])).
% 3.86/0.87  fof(f224,plain,(
% 3.86/0.87    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~spl3_10),
% 3.86/0.87    inference(avatar_component_clause,[],[f222])).
% 3.86/0.87  fof(f206,plain,(
% 3.86/0.87    ( ! [X0,X1] : (k3_subset_1(X0,k4_xboole_0(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.86/0.87    inference(duplicate_literal_removal,[],[f202])).
% 3.86/0.87  fof(f202,plain,(
% 3.86/0.87    ( ! [X0,X1] : (k3_subset_1(X0,k4_xboole_0(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.86/0.87    inference(superposition,[],[f78,f79])).
% 3.86/0.87  fof(f79,plain,(
% 3.86/0.87    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.86/0.87    inference(cnf_transformation,[],[f37])).
% 3.86/0.87  fof(f37,plain,(
% 3.86/0.87    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.86/0.87    inference(ennf_transformation,[],[f11])).
% 3.86/0.87  fof(f11,axiom,(
% 3.86/0.87    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 3.86/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 3.86/0.87  fof(f78,plain,(
% 3.86/0.87    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.86/0.87    inference(cnf_transformation,[],[f36])).
% 3.86/0.87  fof(f36,plain,(
% 3.86/0.87    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.86/0.87    inference(ennf_transformation,[],[f16])).
% 3.86/0.87  fof(f16,axiom,(
% 3.86/0.87    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 3.86/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 3.86/0.87  fof(f2038,plain,(
% 3.86/0.87    spl3_20 | ~spl3_10),
% 3.86/0.87    inference(avatar_split_clause,[],[f2020,f222,f353])).
% 3.86/0.87  fof(f2020,plain,(
% 3.86/0.87    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~spl3_10),
% 3.86/0.87    inference(superposition,[],[f149,f224])).
% 3.86/0.87  fof(f2011,plain,(
% 3.86/0.87    spl3_10 | ~spl3_2 | ~spl3_9),
% 3.86/0.87    inference(avatar_split_clause,[],[f2010,f218,f113,f222])).
% 3.86/0.87  fof(f113,plain,(
% 3.86/0.87    spl3_2 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)),
% 3.86/0.87    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 3.86/0.87  fof(f218,plain,(
% 3.86/0.87    spl3_9 <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.86/0.87    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 3.86/0.87  fof(f2010,plain,(
% 3.86/0.87    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | (~spl3_2 | ~spl3_9)),
% 3.86/0.87    inference(subsumption_resolution,[],[f2007,f219])).
% 3.86/0.87  fof(f219,plain,(
% 3.86/0.87    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_9),
% 3.86/0.87    inference(avatar_component_clause,[],[f218])).
% 3.86/0.87  fof(f2007,plain,(
% 3.86/0.87    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_2),
% 3.86/0.87    inference(superposition,[],[f74,f114])).
% 3.86/0.87  fof(f114,plain,(
% 3.86/0.87    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~spl3_2),
% 3.86/0.87    inference(avatar_component_clause,[],[f113])).
% 3.86/0.87  fof(f2005,plain,(
% 3.86/0.87    ~spl3_21 | spl3_27 | ~spl3_26),
% 3.86/0.87    inference(avatar_split_clause,[],[f1933,f426,f430,f374])).
% 3.86/0.87  fof(f374,plain,(
% 3.86/0.87    spl3_21 <=> r1_tarski(sK1,k1_tops_1(sK0,sK1))),
% 3.86/0.87    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 3.86/0.87  fof(f426,plain,(
% 3.86/0.87    spl3_26 <=> r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 3.86/0.87    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 3.86/0.87  fof(f1933,plain,(
% 3.86/0.87    sK1 = k1_tops_1(sK0,sK1) | ~r1_tarski(sK1,k1_tops_1(sK0,sK1)) | ~spl3_26),
% 3.86/0.87    inference(resolution,[],[f427,f77])).
% 3.86/0.87  fof(f77,plain,(
% 3.86/0.87    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 3.86/0.87    inference(cnf_transformation,[],[f65])).
% 3.86/0.87  fof(f65,plain,(
% 3.86/0.87    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.86/0.87    inference(flattening,[],[f64])).
% 3.86/0.87  fof(f64,plain,(
% 3.86/0.87    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.86/0.87    inference(nnf_transformation,[],[f2])).
% 3.86/0.88  fof(f2,axiom,(
% 3.86/0.88    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.86/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 3.86/0.89  fof(f427,plain,(
% 3.86/0.89    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~spl3_26),
% 3.86/0.89    inference(avatar_component_clause,[],[f426])).
% 3.86/0.89  fof(f1995,plain,(
% 3.86/0.89    ~spl3_3 | ~spl3_4 | spl3_10 | ~spl3_27),
% 3.86/0.89    inference(avatar_contradiction_clause,[],[f1994])).
% 3.86/0.89  fof(f1994,plain,(
% 3.86/0.89    $false | (~spl3_3 | ~spl3_4 | spl3_10 | ~spl3_27)),
% 3.86/0.89    inference(subsumption_resolution,[],[f1993,f126])).
% 3.86/0.89  fof(f1993,plain,(
% 3.86/0.89    ~l1_pre_topc(sK0) | (~spl3_3 | spl3_10 | ~spl3_27)),
% 3.86/0.89    inference(subsumption_resolution,[],[f1992,f121])).
% 3.86/0.89  fof(f1992,plain,(
% 3.86/0.89    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (spl3_10 | ~spl3_27)),
% 3.86/0.89    inference(subsumption_resolution,[],[f1989,f223])).
% 3.86/0.89  fof(f223,plain,(
% 3.86/0.89    k2_tops_1(sK0,sK1) != k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | spl3_10),
% 3.86/0.89    inference(avatar_component_clause,[],[f222])).
% 3.86/0.89  fof(f1989,plain,(
% 3.86/0.89    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl3_27),
% 3.86/0.89    inference(superposition,[],[f321,f432])).
% 3.86/0.89  fof(f432,plain,(
% 3.86/0.89    sK1 = k1_tops_1(sK0,sK1) | ~spl3_27),
% 3.86/0.89    inference(avatar_component_clause,[],[f430])).
% 3.86/0.89  fof(f321,plain,(
% 3.86/0.89    ( ! [X2,X3] : (k2_tops_1(X2,X3) = k4_xboole_0(k2_pre_topc(X2,X3),k1_tops_1(X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2)) )),
% 3.86/0.89    inference(subsumption_resolution,[],[f319,f85])).
% 3.86/0.89  fof(f85,plain,(
% 3.86/0.89    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.86/0.89    inference(cnf_transformation,[],[f43])).
% 3.86/0.89  fof(f43,plain,(
% 3.86/0.89    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.86/0.89    inference(flattening,[],[f42])).
% 3.86/0.89  fof(f42,plain,(
% 3.86/0.89    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 3.86/0.89    inference(ennf_transformation,[],[f23])).
% 3.86/0.89  fof(f23,axiom,(
% 3.86/0.89    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 3.86/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 3.86/0.89  fof(f319,plain,(
% 3.86/0.89    ( ! [X2,X3] : (k2_tops_1(X2,X3) = k4_xboole_0(k2_pre_topc(X2,X3),k1_tops_1(X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2) | ~m1_subset_1(k2_pre_topc(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))) )),
% 3.86/0.89    inference(superposition,[],[f81,f74])).
% 3.86/0.89  fof(f81,plain,(
% 3.86/0.89    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.86/0.89    inference(cnf_transformation,[],[f38])).
% 3.86/0.89  fof(f38,plain,(
% 3.86/0.89    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.86/0.89    inference(ennf_transformation,[],[f26])).
% 3.86/0.89  fof(f26,axiom,(
% 3.86/0.89    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 3.86/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).
% 3.86/0.89  fof(f1957,plain,(
% 3.86/0.89    spl3_54 | ~spl3_3 | ~spl3_4),
% 3.86/0.89    inference(avatar_split_clause,[],[f1952,f124,f119,f1954])).
% 3.86/0.89  fof(f1952,plain,(
% 3.86/0.89    r1_tarski(sK1,k2_pre_topc(sK0,sK1)) | (~spl3_3 | ~spl3_4)),
% 3.86/0.89    inference(subsumption_resolution,[],[f1942,f126])).
% 3.86/0.89  fof(f1942,plain,(
% 3.86/0.89    r1_tarski(sK1,k2_pre_topc(sK0,sK1)) | ~l1_pre_topc(sK0) | ~spl3_3),
% 3.86/0.89    inference(resolution,[],[f648,f121])).
% 3.86/0.89  fof(f648,plain,(
% 3.86/0.89    ( ! [X8,X7] : (~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X8))) | r1_tarski(X7,k2_pre_topc(X8,X7)) | ~l1_pre_topc(X8)) )),
% 3.86/0.89    inference(superposition,[],[f99,f298])).
% 3.86/0.89  fof(f298,plain,(
% 3.86/0.89    ( ! [X2,X3] : (k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2)) )),
% 3.86/0.89    inference(subsumption_resolution,[],[f295,f87])).
% 3.86/0.89  fof(f87,plain,(
% 3.86/0.89    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.86/0.89    inference(cnf_transformation,[],[f46])).
% 3.86/0.89  fof(f46,plain,(
% 3.86/0.89    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.86/0.89    inference(flattening,[],[f45])).
% 3.86/0.89  fof(f45,plain,(
% 3.86/0.89    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 3.86/0.89    inference(ennf_transformation,[],[f24])).
% 3.86/0.89  fof(f24,axiom,(
% 3.86/0.89    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 3.86/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).
% 3.86/0.89  fof(f295,plain,(
% 3.86/0.89    ( ! [X2,X3] : (k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2) | ~m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))) )),
% 3.86/0.89    inference(duplicate_literal_removal,[],[f292])).
% 3.86/0.89  fof(f292,plain,(
% 3.86/0.89    ( ! [X2,X3] : (k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2) | ~m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) )),
% 3.86/0.89    inference(superposition,[],[f86,f100])).
% 3.86/0.89  fof(f100,plain,(
% 3.86/0.89    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.86/0.89    inference(cnf_transformation,[],[f57])).
% 3.86/0.89  fof(f57,plain,(
% 3.86/0.89    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.86/0.89    inference(flattening,[],[f56])).
% 3.86/0.89  fof(f56,plain,(
% 3.86/0.89    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 3.86/0.89    inference(ennf_transformation,[],[f17])).
% 3.86/0.89  fof(f17,axiom,(
% 3.86/0.89    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 3.86/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 3.86/0.89  fof(f86,plain,(
% 3.86/0.89    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.86/0.89    inference(cnf_transformation,[],[f44])).
% 3.86/0.89  fof(f44,plain,(
% 3.86/0.89    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.86/0.89    inference(ennf_transformation,[],[f29])).
% 3.86/0.89  fof(f29,axiom,(
% 3.86/0.89    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 3.86/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).
% 3.86/0.89  fof(f99,plain,(
% 3.86/0.89    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 3.86/0.89    inference(cnf_transformation,[],[f9])).
% 3.86/0.89  fof(f9,axiom,(
% 3.86/0.89    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 3.86/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 3.86/0.89  fof(f1917,plain,(
% 3.86/0.89    spl3_26 | ~spl3_3 | ~spl3_4),
% 3.86/0.89    inference(avatar_split_clause,[],[f1916,f124,f119,f426])).
% 3.86/0.89  fof(f1916,plain,(
% 3.86/0.89    r1_tarski(k1_tops_1(sK0,sK1),sK1) | (~spl3_3 | ~spl3_4)),
% 3.86/0.89    inference(subsumption_resolution,[],[f1907,f126])).
% 3.86/0.89  fof(f1907,plain,(
% 3.86/0.89    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~l1_pre_topc(sK0) | ~spl3_3),
% 3.86/0.89    inference(resolution,[],[f626,f121])).
% 3.86/0.89  fof(f626,plain,(
% 3.86/0.89    ( ! [X6,X7] : (~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X7))) | r1_tarski(k1_tops_1(X7,X6),X6) | ~l1_pre_topc(X7)) )),
% 3.86/0.89    inference(superposition,[],[f155,f273])).
% 3.86/0.89  fof(f155,plain,(
% 3.86/0.89    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 3.86/0.89    inference(resolution,[],[f149,f90])).
% 3.86/0.89  fof(f90,plain,(
% 3.86/0.89    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 3.86/0.89    inference(cnf_transformation,[],[f66])).
% 3.86/0.89  fof(f422,plain,(
% 3.86/0.89    ~spl3_10 | spl3_2 | ~spl3_9),
% 3.86/0.89    inference(avatar_split_clause,[],[f421,f218,f113,f222])).
% 3.86/0.89  fof(f421,plain,(
% 3.86/0.89    k2_tops_1(sK0,sK1) != k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | (spl3_2 | ~spl3_9)),
% 3.86/0.89    inference(subsumption_resolution,[],[f420,f219])).
% 3.86/0.89  fof(f420,plain,(
% 3.86/0.89    k2_tops_1(sK0,sK1) != k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_2),
% 3.86/0.89    inference(superposition,[],[f115,f74])).
% 3.86/0.89  fof(f115,plain,(
% 3.86/0.89    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | spl3_2),
% 3.86/0.89    inference(avatar_component_clause,[],[f113])).
% 3.86/0.89  fof(f392,plain,(
% 3.86/0.89    spl3_21 | ~spl3_1 | ~spl3_3 | ~spl3_4),
% 3.86/0.89    inference(avatar_split_clause,[],[f391,f124,f119,f109,f374])).
% 3.86/0.89  fof(f109,plain,(
% 3.86/0.89    spl3_1 <=> v3_pre_topc(sK1,sK0)),
% 3.86/0.89    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 3.86/0.89  fof(f391,plain,(
% 3.86/0.89    ~v3_pre_topc(sK1,sK0) | r1_tarski(sK1,k1_tops_1(sK0,sK1)) | (~spl3_3 | ~spl3_4)),
% 3.86/0.89    inference(subsumption_resolution,[],[f366,f106])).
% 3.86/0.89  fof(f106,plain,(
% 3.86/0.89    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.86/0.89    inference(equality_resolution,[],[f76])).
% 3.86/0.89  fof(f76,plain,(
% 3.86/0.89    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.86/0.89    inference(cnf_transformation,[],[f65])).
% 3.86/0.89  fof(f366,plain,(
% 3.86/0.89    ~v3_pre_topc(sK1,sK0) | r1_tarski(sK1,k1_tops_1(sK0,sK1)) | ~r1_tarski(sK1,sK1) | (~spl3_3 | ~spl3_4)),
% 3.86/0.89    inference(resolution,[],[f334,f121])).
% 3.86/0.89  fof(f334,plain,(
% 3.86/0.89    ( ! [X16] : (~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X16,sK0) | r1_tarski(X16,k1_tops_1(sK0,sK1)) | ~r1_tarski(X16,sK1)) ) | (~spl3_3 | ~spl3_4)),
% 3.86/0.89    inference(subsumption_resolution,[],[f329,f126])).
% 3.86/0.89  fof(f329,plain,(
% 3.86/0.89    ( ! [X16] : (~r1_tarski(X16,sK1) | ~v3_pre_topc(X16,sK0) | r1_tarski(X16,k1_tops_1(sK0,sK1)) | ~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) ) | ~spl3_3),
% 3.86/0.89    inference(resolution,[],[f89,f121])).
% 3.86/0.89  fof(f89,plain,(
% 3.86/0.89    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | r1_tarski(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.86/0.89    inference(cnf_transformation,[],[f50])).
% 3.86/0.89  fof(f50,plain,(
% 3.86/0.89    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.86/0.89    inference(flattening,[],[f49])).
% 3.86/0.89  fof(f49,plain,(
% 3.86/0.89    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(X1,k1_tops_1(X0,X2)) | (~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.86/0.89    inference(ennf_transformation,[],[f27])).
% 3.86/0.89  fof(f27,axiom,(
% 3.86/0.89    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v3_pre_topc(X1,X0)) => r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 3.86/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_1)).
% 3.86/0.89  fof(f264,plain,(
% 3.86/0.89    spl3_13 | ~spl3_3 | ~spl3_4 | ~spl3_5),
% 3.86/0.89    inference(avatar_split_clause,[],[f259,f129,f124,f119,f261])).
% 3.86/0.89  fof(f261,plain,(
% 3.86/0.89    spl3_13 <=> v3_pre_topc(k1_tops_1(sK0,sK1),sK0)),
% 3.86/0.89    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 3.86/0.89  fof(f129,plain,(
% 3.86/0.89    spl3_5 <=> v2_pre_topc(sK0)),
% 3.86/0.89    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 3.86/0.89  fof(f259,plain,(
% 3.86/0.89    v3_pre_topc(k1_tops_1(sK0,sK1),sK0) | (~spl3_3 | ~spl3_4 | ~spl3_5)),
% 3.86/0.89    inference(subsumption_resolution,[],[f258,f131])).
% 3.86/0.89  fof(f131,plain,(
% 3.86/0.89    v2_pre_topc(sK0) | ~spl3_5),
% 3.86/0.89    inference(avatar_component_clause,[],[f129])).
% 3.86/0.89  fof(f258,plain,(
% 3.86/0.89    v3_pre_topc(k1_tops_1(sK0,sK1),sK0) | ~v2_pre_topc(sK0) | (~spl3_3 | ~spl3_4)),
% 3.86/0.89    inference(subsumption_resolution,[],[f254,f126])).
% 3.86/0.89  fof(f254,plain,(
% 3.86/0.89    v3_pre_topc(k1_tops_1(sK0,sK1),sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~spl3_3),
% 3.86/0.89    inference(resolution,[],[f88,f121])).
% 3.86/0.89  fof(f88,plain,(
% 3.86/0.89    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(k1_tops_1(X0,X1),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.86/0.89    inference(cnf_transformation,[],[f48])).
% 3.86/0.89  fof(f48,plain,(
% 3.86/0.89    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.86/0.89    inference(flattening,[],[f47])).
% 3.86/0.89  fof(f47,plain,(
% 3.86/0.89    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.86/0.89    inference(ennf_transformation,[],[f25])).
% 3.86/0.89  fof(f25,axiom,(
% 3.86/0.89    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 3.86/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).
% 3.86/0.89  fof(f239,plain,(
% 3.86/0.89    ~spl3_3 | ~spl3_4 | spl3_9),
% 3.86/0.89    inference(avatar_contradiction_clause,[],[f238])).
% 3.86/0.89  fof(f238,plain,(
% 3.86/0.89    $false | (~spl3_3 | ~spl3_4 | spl3_9)),
% 3.86/0.89    inference(subsumption_resolution,[],[f237,f126])).
% 3.86/0.89  fof(f237,plain,(
% 3.86/0.89    ~l1_pre_topc(sK0) | (~spl3_3 | spl3_9)),
% 3.86/0.89    inference(subsumption_resolution,[],[f234,f121])).
% 3.86/0.89  fof(f234,plain,(
% 3.86/0.89    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl3_9),
% 3.86/0.89    inference(resolution,[],[f85,f220])).
% 3.86/0.89  fof(f220,plain,(
% 3.86/0.89    ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_9),
% 3.86/0.89    inference(avatar_component_clause,[],[f218])).
% 3.86/0.89  fof(f132,plain,(
% 3.86/0.89    spl3_5),
% 3.86/0.89    inference(avatar_split_clause,[],[f69,f129])).
% 3.86/0.89  fof(f69,plain,(
% 3.86/0.89    v2_pre_topc(sK0)),
% 3.86/0.89    inference(cnf_transformation,[],[f63])).
% 3.86/0.89  fof(f63,plain,(
% 3.86/0.89    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 3.86/0.89    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f60,f62,f61])).
% 3.86/0.89  fof(f61,plain,(
% 3.86/0.89    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | ~v3_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 3.86/0.89    introduced(choice_axiom,[])).
% 3.86/0.89  fof(f62,plain,(
% 3.86/0.89    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | ~v3_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 3.86/0.89    introduced(choice_axiom,[])).
% 3.86/0.89  fof(f60,plain,(
% 3.86/0.89    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.86/0.89    inference(flattening,[],[f59])).
% 3.86/0.89  fof(f59,plain,(
% 3.86/0.89    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.86/0.89    inference(nnf_transformation,[],[f34])).
% 3.86/0.89  fof(f34,plain,(
% 3.86/0.89    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.86/0.89    inference(flattening,[],[f33])).
% 3.86/0.89  fof(f33,plain,(
% 3.86/0.89    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 3.86/0.89    inference(ennf_transformation,[],[f32])).
% 3.86/0.89  fof(f32,negated_conjecture,(
% 3.86/0.89    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 3.86/0.89    inference(negated_conjecture,[],[f31])).
% 3.86/0.89  fof(f31,conjecture,(
% 3.86/0.89    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 3.86/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tops_1)).
% 3.86/0.89  fof(f127,plain,(
% 3.86/0.89    spl3_4),
% 3.86/0.89    inference(avatar_split_clause,[],[f70,f124])).
% 3.86/0.89  fof(f70,plain,(
% 3.86/0.89    l1_pre_topc(sK0)),
% 3.86/0.89    inference(cnf_transformation,[],[f63])).
% 3.86/0.89  fof(f122,plain,(
% 3.86/0.89    spl3_3),
% 3.86/0.89    inference(avatar_split_clause,[],[f71,f119])).
% 3.86/0.89  fof(f71,plain,(
% 3.86/0.89    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.86/0.89    inference(cnf_transformation,[],[f63])).
% 3.86/0.89  fof(f117,plain,(
% 3.86/0.89    spl3_1 | spl3_2),
% 3.86/0.89    inference(avatar_split_clause,[],[f72,f113,f109])).
% 3.86/0.89  fof(f72,plain,(
% 3.86/0.89    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)),
% 3.86/0.89    inference(cnf_transformation,[],[f63])).
% 3.86/0.89  fof(f116,plain,(
% 3.86/0.89    ~spl3_1 | ~spl3_2),
% 3.86/0.89    inference(avatar_split_clause,[],[f73,f113,f109])).
% 3.86/0.89  fof(f73,plain,(
% 3.86/0.89    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)),
% 3.86/0.89    inference(cnf_transformation,[],[f63])).
% 3.86/0.89  % SZS output end Proof for theBenchmark
% 3.86/0.89  % (10104)------------------------------
% 3.86/0.89  % (10104)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.86/0.89  % (10104)Termination reason: Refutation
% 3.86/0.89  
% 3.86/0.89  % (10104)Memory used [KB]: 12153
% 3.86/0.89  % (10104)Time elapsed: 0.469 s
% 3.86/0.89  % (10104)------------------------------
% 3.86/0.89  % (10104)------------------------------
% 3.86/0.89  % (10081)Success in time 0.532 s
%------------------------------------------------------------------------------
