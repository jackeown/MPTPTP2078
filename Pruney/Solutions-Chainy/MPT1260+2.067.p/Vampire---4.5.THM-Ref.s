%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:44 EST 2020

% Result     : Theorem 3.22s
% Output     : Refutation 3.22s
% Verified   : 
% Statistics : Number of formulae       :  157 ( 279 expanded)
%              Number of leaves         :   39 ( 112 expanded)
%              Depth                    :   11
%              Number of atoms          :  463 ( 896 expanded)
%              Number of equality atoms :   85 ( 207 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3337,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f91,f96,f101,f110,f113,f166,f186,f196,f243,f273,f378,f445,f446,f983,f986,f1061,f2026,f2045,f3170,f3182,f3336])).

fof(f3336,plain,
    ( ~ spl2_2
    | ~ spl2_3
    | spl2_14
    | ~ spl2_89 ),
    inference(avatar_split_clause,[],[f3237,f3167,f193,f98,f93])).

fof(f93,plain,
    ( spl2_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f98,plain,
    ( spl2_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f193,plain,
    ( spl2_14
  <=> sK1 = k1_tops_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f3167,plain,
    ( spl2_89
  <=> sK1 = k5_xboole_0(sK1,k3_xboole_0(sK1,k2_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_89])])).

fof(f3237,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_89 ),
    inference(superposition,[],[f3169,f300])).

fof(f300,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k5_xboole_0(X1,k3_xboole_0(X1,k2_tops_1(X0,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f297])).

fof(f297,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k5_xboole_0(X1,k3_xboole_0(X1,k2_tops_1(X0,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(superposition,[],[f81,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f57,f78])).

fof(f78,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f3169,plain,
    ( sK1 = k5_xboole_0(sK1,k3_xboole_0(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_89 ),
    inference(avatar_component_clause,[],[f3167])).

fof(f3182,plain,
    ( ~ spl2_52
    | spl2_88 ),
    inference(avatar_contradiction_clause,[],[f3171])).

fof(f3171,plain,
    ( $false
    | ~ spl2_52
    | spl2_88 ),
    inference(unit_resulting_resolution,[],[f977,f3165,f283])).

fof(f283,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f278])).

fof(f278,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(superposition,[],[f63,f81])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_subset_1)).

fof(f3165,plain,
    ( ~ m1_subset_1(k5_xboole_0(sK1,k3_xboole_0(sK1,k2_tops_1(sK0,sK1))),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | spl2_88 ),
    inference(avatar_component_clause,[],[f3163])).

fof(f3163,plain,
    ( spl2_88
  <=> m1_subset_1(k5_xboole_0(sK1,k3_xboole_0(sK1,k2_tops_1(sK0,sK1))),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_88])])).

fof(f977,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl2_52 ),
    inference(avatar_component_clause,[],[f976])).

fof(f976,plain,
    ( spl2_52
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_52])])).

fof(f3170,plain,
    ( ~ spl2_88
    | spl2_89
    | ~ spl2_58
    | ~ spl2_78 ),
    inference(avatar_split_clause,[],[f2063,f2042,f1058,f3167,f3163])).

fof(f1058,plain,
    ( spl2_58
  <=> sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_58])])).

fof(f2042,plain,
    ( spl2_78
  <=> k2_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),k5_xboole_0(sK1,k3_xboole_0(sK1,k2_tops_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_78])])).

fof(f2063,plain,
    ( sK1 = k5_xboole_0(sK1,k3_xboole_0(sK1,k2_tops_1(sK0,sK1)))
    | ~ m1_subset_1(k5_xboole_0(sK1,k3_xboole_0(sK1,k2_tops_1(sK0,sK1))),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl2_58
    | ~ spl2_78 ),
    inference(forward_demodulation,[],[f2052,f1060])).

fof(f1060,plain,
    ( sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))
    | ~ spl2_58 ),
    inference(avatar_component_clause,[],[f1058])).

fof(f2052,plain,
    ( k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k3_xboole_0(sK1,k2_tops_1(sK0,sK1)))
    | ~ m1_subset_1(k5_xboole_0(sK1,k3_xboole_0(sK1,k2_tops_1(sK0,sK1))),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl2_78 ),
    inference(superposition,[],[f61,f2044])).

fof(f2044,plain,
    ( k2_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),k5_xboole_0(sK1,k3_xboole_0(sK1,k2_tops_1(sK0,sK1))))
    | ~ spl2_78 ),
    inference(avatar_component_clause,[],[f2042])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f2045,plain,
    ( ~ spl2_52
    | spl2_78
    | ~ spl2_77 ),
    inference(avatar_split_clause,[],[f2030,f2023,f2042,f976])).

fof(f2023,plain,
    ( spl2_77
  <=> k2_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),k7_subset_1(k2_pre_topc(sK0,sK1),sK1,k2_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_77])])).

fof(f2030,plain,
    ( k2_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),k5_xboole_0(sK1,k3_xboole_0(sK1,k2_tops_1(sK0,sK1))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl2_77 ),
    inference(superposition,[],[f2025,f81])).

fof(f2025,plain,
    ( k2_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),k7_subset_1(k2_pre_topc(sK0,sK1),sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_77 ),
    inference(avatar_component_clause,[],[f2023])).

fof(f2026,plain,
    ( ~ spl2_52
    | spl2_77
    | ~ spl2_53 ),
    inference(avatar_split_clause,[],[f1099,f980,f2023,f976])).

fof(f980,plain,
    ( spl2_53
  <=> k2_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_53])])).

fof(f1099,plain,
    ( k2_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),k7_subset_1(k2_pre_topc(sK0,sK1),sK1,k2_tops_1(sK0,sK1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl2_53 ),
    inference(superposition,[],[f357,f982])).

fof(f982,plain,
    ( k2_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),sK1)
    | ~ spl2_53 ),
    inference(avatar_component_clause,[],[f980])).

fof(f357,plain,(
    ! [X4,X3] :
      ( k3_subset_1(X3,X4) = k3_subset_1(X3,k7_subset_1(X3,X4,k3_subset_1(X3,X4)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(X3)) ) ),
    inference(global_subsumption,[],[f76,f352])).

fof(f352,plain,(
    ! [X4,X3] :
      ( k3_subset_1(X3,X4) = k3_subset_1(X3,k7_subset_1(X3,X4,k3_subset_1(X3,X4)))
      | ~ m1_subset_1(k3_subset_1(X3,X4),k1_zfmisc_1(X3))
      | ~ m1_subset_1(X4,k1_zfmisc_1(X3)) ) ),
    inference(duplicate_literal_removal,[],[f349])).

fof(f349,plain,(
    ! [X4,X3] :
      ( k3_subset_1(X3,X4) = k3_subset_1(X3,k7_subset_1(X3,X4,k3_subset_1(X3,X4)))
      | ~ m1_subset_1(k3_subset_1(X3,X4),k1_zfmisc_1(X3))
      | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
      | ~ m1_subset_1(k3_subset_1(X3,X4),k1_zfmisc_1(X3)) ) ),
    inference(superposition,[],[f64,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( k4_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(condensation,[],[f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k4_subset_1)).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_subset_1)).

fof(f76,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f1061,plain,
    ( ~ spl2_52
    | spl2_58
    | ~ spl2_53 ),
    inference(avatar_split_clause,[],[f990,f980,f1058,f976])).

fof(f990,plain,
    ( sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl2_53 ),
    inference(superposition,[],[f61,f982])).

fof(f986,plain,
    ( ~ spl2_9
    | spl2_52 ),
    inference(avatar_contradiction_clause,[],[f984])).

fof(f984,plain,
    ( $false
    | ~ spl2_9
    | spl2_52 ),
    inference(unit_resulting_resolution,[],[f165,f978,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f978,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | spl2_52 ),
    inference(avatar_component_clause,[],[f976])).

fof(f165,plain,
    ( r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f163])).

fof(f163,plain,
    ( spl2_9
  <=> r1_tarski(sK1,k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f983,plain,
    ( ~ spl2_52
    | ~ spl2_15
    | spl2_53
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f942,f107,f980,f200,f976])).

fof(f200,plain,
    ( spl2_15
  <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f107,plain,
    ( spl2_5
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f942,plain,
    ( k2_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),sK1)
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl2_5 ),
    inference(superposition,[],[f277,f109])).

fof(f109,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f107])).

fof(f277,plain,(
    ! [X10,X11,X9] :
      ( k3_subset_1(X9,X10) = k7_subset_1(X11,X9,X10)
      | ~ m1_subset_1(X9,k1_zfmisc_1(X11))
      | ~ m1_subset_1(X10,k1_zfmisc_1(X9)) ) ),
    inference(superposition,[],[f81,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f62,f78])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f446,plain,
    ( sK1 != k1_tops_1(sK0,sK1)
    | v3_pre_topc(sK1,sK0)
    | ~ v3_pre_topc(k1_tops_1(sK0,sK1),sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f445,plain,
    ( ~ spl2_2
    | ~ spl2_3
    | spl2_5
    | ~ spl2_14 ),
    inference(avatar_split_clause,[],[f383,f193,f107,f98,f93])).

fof(f383,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_14 ),
    inference(superposition,[],[f65,f195])).

fof(f195,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f193])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

fof(f378,plain,
    ( ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4
    | spl2_13 ),
    inference(avatar_contradiction_clause,[],[f368])).

fof(f368,plain,
    ( $false
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4
    | spl2_13 ),
    inference(unit_resulting_resolution,[],[f95,f105,f84,f100,f191,f100,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X1,X2)
      | ~ v3_pre_topc(X1,X0)
      | r1_tarski(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
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

fof(f191,plain,
    ( ~ r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | spl2_13 ),
    inference(avatar_component_clause,[],[f189])).

fof(f189,plain,
    ( spl2_13
  <=> r1_tarski(sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f100,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f98])).

fof(f84,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f105,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl2_4
  <=> v3_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f95,plain,
    ( l1_pre_topc(sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f93])).

fof(f273,plain,
    ( ~ spl2_1
    | ~ spl2_2
    | spl2_19
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f261,f98,f270,f93,f88])).

fof(f88,plain,
    ( spl2_1
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f270,plain,
    ( spl2_19
  <=> v3_pre_topc(k1_tops_1(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f261,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl2_3 ),
    inference(resolution,[],[f69,f100])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

fof(f243,plain,
    ( ~ spl2_2
    | ~ spl2_3
    | spl2_15 ),
    inference(avatar_contradiction_clause,[],[f236])).

fof(f236,plain,
    ( $false
    | ~ spl2_2
    | ~ spl2_3
    | spl2_15 ),
    inference(unit_resulting_resolution,[],[f95,f100,f202,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f202,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_15 ),
    inference(avatar_component_clause,[],[f200])).

fof(f196,plain,
    ( ~ spl2_13
    | spl2_14
    | ~ spl2_12 ),
    inference(avatar_split_clause,[],[f187,f183,f193,f189])).

fof(f183,plain,
    ( spl2_12
  <=> r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f187,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_12 ),
    inference(resolution,[],[f185,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f185,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f183])).

fof(f186,plain,
    ( ~ spl2_2
    | spl2_12
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f181,f98,f183,f93])).

fof(f181,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl2_3 ),
    inference(resolution,[],[f71,f100])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

fof(f166,plain,
    ( ~ spl2_2
    | spl2_9
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f161,f98,f163,f93])).

fof(f161,plain,
    ( r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_3 ),
    inference(resolution,[],[f68,f100])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(X1,k2_pre_topc(X0,X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,k2_pre_topc(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).

fof(f113,plain,
    ( ~ spl2_4
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f112,f107,f103])).

fof(f112,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | ~ spl2_5 ),
    inference(trivial_inequality_removal,[],[f111])).

fof(f111,plain,
    ( k2_tops_1(sK0,sK1) != k2_tops_1(sK0,sK1)
    | ~ v3_pre_topc(sK1,sK0)
    | ~ spl2_5 ),
    inference(forward_demodulation,[],[f56,f109])).

fof(f56,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,
    ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
      | ~ v3_pre_topc(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
      | v3_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f45,f47,f46])).

fof(f46,plain,
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

fof(f47,plain,
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

fof(f45,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tops_1)).

fof(f110,plain,
    ( spl2_4
    | spl2_5 ),
    inference(avatar_split_clause,[],[f55,f107,f103])).

fof(f55,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f101,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f54,f98])).

fof(f54,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f48])).

fof(f96,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f53,f93])).

fof(f53,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f91,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f52,f88])).

fof(f52,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f48])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:21:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.48  % (5479)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.50  % (5459)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.50  % (5463)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.51  % (5483)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.51  % (5475)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.51  % (5462)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.52  % (5458)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.53  % (5465)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.53  % (5470)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.53  % (5461)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (5482)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.53  % (5456)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.53  % (5481)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (5457)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.54  % (5478)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.54  % (5468)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.54  % (5472)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.55  % (5460)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.55  % (5474)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.55  % (5464)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.55  % (5471)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.55  % (5477)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.55  % (5473)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.55  % (5455)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.56  % (5466)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.56  % (5476)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.56  % (5467)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.56  % (5469)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.57  % (5480)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.57  % (5471)Refutation not found, incomplete strategy% (5471)------------------------------
% 0.21/0.57  % (5471)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (5471)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (5471)Memory used [KB]: 10746
% 0.21/0.57  % (5471)Time elapsed: 0.151 s
% 0.21/0.57  % (5471)------------------------------
% 0.21/0.57  % (5471)------------------------------
% 0.21/0.58  % (5465)Refutation not found, incomplete strategy% (5465)------------------------------
% 0.21/0.58  % (5465)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.59  % (5484)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.82/0.60  % (5465)Termination reason: Refutation not found, incomplete strategy
% 1.82/0.60  
% 1.82/0.60  % (5465)Memory used [KB]: 11129
% 1.82/0.60  % (5465)Time elapsed: 0.190 s
% 1.82/0.60  % (5465)------------------------------
% 1.82/0.60  % (5465)------------------------------
% 2.06/0.71  % (5486)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.68/0.74  % (5485)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 3.22/0.83  % (5457)Time limit reached!
% 3.22/0.83  % (5457)------------------------------
% 3.22/0.83  % (5457)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.22/0.83  % (5457)Termination reason: Time limit
% 3.22/0.83  
% 3.22/0.83  % (5457)Memory used [KB]: 6524
% 3.22/0.83  % (5457)Time elapsed: 0.425 s
% 3.22/0.83  % (5457)------------------------------
% 3.22/0.83  % (5457)------------------------------
% 3.22/0.84  % (5478)Refutation found. Thanks to Tanya!
% 3.22/0.84  % SZS status Theorem for theBenchmark
% 3.22/0.84  % (5479)Time limit reached!
% 3.22/0.84  % (5479)------------------------------
% 3.22/0.84  % (5479)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.22/0.84  % (5479)Termination reason: Time limit
% 3.22/0.84  % (5479)Termination phase: Saturation
% 3.22/0.84  
% 3.22/0.84  % (5479)Memory used [KB]: 14200
% 3.22/0.84  % (5479)Time elapsed: 0.400 s
% 3.22/0.84  % (5479)------------------------------
% 3.22/0.84  % (5479)------------------------------
% 3.22/0.84  % SZS output start Proof for theBenchmark
% 3.22/0.84  fof(f3337,plain,(
% 3.22/0.84    $false),
% 3.22/0.84    inference(avatar_sat_refutation,[],[f91,f96,f101,f110,f113,f166,f186,f196,f243,f273,f378,f445,f446,f983,f986,f1061,f2026,f2045,f3170,f3182,f3336])).
% 3.22/0.85  fof(f3336,plain,(
% 3.22/0.85    ~spl2_2 | ~spl2_3 | spl2_14 | ~spl2_89),
% 3.22/0.85    inference(avatar_split_clause,[],[f3237,f3167,f193,f98,f93])).
% 3.22/0.85  fof(f93,plain,(
% 3.22/0.85    spl2_2 <=> l1_pre_topc(sK0)),
% 3.22/0.85    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 3.22/0.85  fof(f98,plain,(
% 3.22/0.85    spl2_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.22/0.85    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 3.22/0.85  fof(f193,plain,(
% 3.22/0.85    spl2_14 <=> sK1 = k1_tops_1(sK0,sK1)),
% 3.22/0.85    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 3.22/0.85  fof(f3167,plain,(
% 3.22/0.85    spl2_89 <=> sK1 = k5_xboole_0(sK1,k3_xboole_0(sK1,k2_tops_1(sK0,sK1)))),
% 3.22/0.85    introduced(avatar_definition,[new_symbols(naming,[spl2_89])])).
% 3.22/0.85  fof(f3237,plain,(
% 3.22/0.85    sK1 = k1_tops_1(sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl2_89),
% 3.22/0.85    inference(superposition,[],[f3169,f300])).
% 3.22/0.85  fof(f300,plain,(
% 3.22/0.85    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k5_xboole_0(X1,k3_xboole_0(X1,k2_tops_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.22/0.85    inference(duplicate_literal_removal,[],[f297])).
% 3.22/0.85  fof(f297,plain,(
% 3.22/0.85    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k5_xboole_0(X1,k3_xboole_0(X1,k2_tops_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.22/0.85    inference(superposition,[],[f81,f66])).
% 3.22/0.85  fof(f66,plain,(
% 3.22/0.85    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.22/0.85    inference(cnf_transformation,[],[f32])).
% 3.22/0.85  fof(f32,plain,(
% 3.22/0.85    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.22/0.85    inference(ennf_transformation,[],[f21])).
% 3.22/0.85  fof(f21,axiom,(
% 3.22/0.85    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 3.22/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).
% 3.22/0.85  fof(f81,plain,(
% 3.22/0.85    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.22/0.85    inference(definition_unfolding,[],[f57,f78])).
% 3.22/0.85  fof(f78,plain,(
% 3.22/0.85    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.22/0.85    inference(cnf_transformation,[],[f2])).
% 3.22/0.85  fof(f2,axiom,(
% 3.22/0.85    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.22/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 3.22/0.85  fof(f57,plain,(
% 3.22/0.85    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.22/0.85    inference(cnf_transformation,[],[f26])).
% 3.22/0.85  fof(f26,plain,(
% 3.22/0.85    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.22/0.85    inference(ennf_transformation,[],[f10])).
% 3.22/0.85  fof(f10,axiom,(
% 3.22/0.85    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 3.22/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 3.22/0.85  fof(f3169,plain,(
% 3.22/0.85    sK1 = k5_xboole_0(sK1,k3_xboole_0(sK1,k2_tops_1(sK0,sK1))) | ~spl2_89),
% 3.22/0.85    inference(avatar_component_clause,[],[f3167])).
% 3.22/0.85  fof(f3182,plain,(
% 3.22/0.85    ~spl2_52 | spl2_88),
% 3.22/0.85    inference(avatar_contradiction_clause,[],[f3171])).
% 3.22/0.85  fof(f3171,plain,(
% 3.22/0.85    $false | (~spl2_52 | spl2_88)),
% 3.22/0.85    inference(unit_resulting_resolution,[],[f977,f3165,f283])).
% 3.22/0.85  fof(f283,plain,(
% 3.22/0.85    ( ! [X2,X0,X1] : (m1_subset_1(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.22/0.85    inference(duplicate_literal_removal,[],[f278])).
% 3.22/0.85  fof(f278,plain,(
% 3.22/0.85    ( ! [X2,X0,X1] : (m1_subset_1(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.22/0.85    inference(superposition,[],[f63,f81])).
% 3.22/0.85  fof(f63,plain,(
% 3.22/0.85    ( ! [X2,X0,X1] : (m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.22/0.85    inference(cnf_transformation,[],[f29])).
% 3.22/0.85  fof(f29,plain,(
% 3.22/0.85    ! [X0,X1,X2] : (m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.22/0.85    inference(ennf_transformation,[],[f7])).
% 3.22/0.85  fof(f7,axiom,(
% 3.22/0.85    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 3.22/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_subset_1)).
% 3.22/0.85  fof(f3165,plain,(
% 3.22/0.85    ~m1_subset_1(k5_xboole_0(sK1,k3_xboole_0(sK1,k2_tops_1(sK0,sK1))),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | spl2_88),
% 3.22/0.85    inference(avatar_component_clause,[],[f3163])).
% 3.22/0.85  fof(f3163,plain,(
% 3.22/0.85    spl2_88 <=> m1_subset_1(k5_xboole_0(sK1,k3_xboole_0(sK1,k2_tops_1(sK0,sK1))),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))),
% 3.22/0.85    introduced(avatar_definition,[new_symbols(naming,[spl2_88])])).
% 3.22/0.85  fof(f977,plain,(
% 3.22/0.85    m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~spl2_52),
% 3.22/0.85    inference(avatar_component_clause,[],[f976])).
% 3.22/0.85  fof(f976,plain,(
% 3.22/0.85    spl2_52 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))),
% 3.22/0.85    introduced(avatar_definition,[new_symbols(naming,[spl2_52])])).
% 3.22/0.85  fof(f3170,plain,(
% 3.22/0.85    ~spl2_88 | spl2_89 | ~spl2_58 | ~spl2_78),
% 3.22/0.85    inference(avatar_split_clause,[],[f2063,f2042,f1058,f3167,f3163])).
% 3.22/0.85  fof(f1058,plain,(
% 3.22/0.85    spl2_58 <=> sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))),
% 3.22/0.85    introduced(avatar_definition,[new_symbols(naming,[spl2_58])])).
% 3.22/0.85  fof(f2042,plain,(
% 3.22/0.85    spl2_78 <=> k2_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),k5_xboole_0(sK1,k3_xboole_0(sK1,k2_tops_1(sK0,sK1))))),
% 3.22/0.85    introduced(avatar_definition,[new_symbols(naming,[spl2_78])])).
% 3.22/0.85  fof(f2063,plain,(
% 3.22/0.85    sK1 = k5_xboole_0(sK1,k3_xboole_0(sK1,k2_tops_1(sK0,sK1))) | ~m1_subset_1(k5_xboole_0(sK1,k3_xboole_0(sK1,k2_tops_1(sK0,sK1))),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | (~spl2_58 | ~spl2_78)),
% 3.22/0.85    inference(forward_demodulation,[],[f2052,f1060])).
% 3.22/0.85  fof(f1060,plain,(
% 3.22/0.85    sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) | ~spl2_58),
% 3.22/0.85    inference(avatar_component_clause,[],[f1058])).
% 3.22/0.85  fof(f2052,plain,(
% 3.22/0.85    k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k3_xboole_0(sK1,k2_tops_1(sK0,sK1))) | ~m1_subset_1(k5_xboole_0(sK1,k3_xboole_0(sK1,k2_tops_1(sK0,sK1))),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~spl2_78),
% 3.22/0.85    inference(superposition,[],[f61,f2044])).
% 3.22/0.85  fof(f2044,plain,(
% 3.22/0.85    k2_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),k5_xboole_0(sK1,k3_xboole_0(sK1,k2_tops_1(sK0,sK1)))) | ~spl2_78),
% 3.22/0.85    inference(avatar_component_clause,[],[f2042])).
% 3.22/0.85  fof(f61,plain,(
% 3.22/0.85    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.22/0.85    inference(cnf_transformation,[],[f27])).
% 3.22/0.85  fof(f27,plain,(
% 3.22/0.85    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.22/0.85    inference(ennf_transformation,[],[f9])).
% 3.22/0.85  fof(f9,axiom,(
% 3.22/0.85    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 3.22/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 3.22/0.85  fof(f2045,plain,(
% 3.22/0.85    ~spl2_52 | spl2_78 | ~spl2_77),
% 3.22/0.85    inference(avatar_split_clause,[],[f2030,f2023,f2042,f976])).
% 3.22/0.85  fof(f2023,plain,(
% 3.22/0.85    spl2_77 <=> k2_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),k7_subset_1(k2_pre_topc(sK0,sK1),sK1,k2_tops_1(sK0,sK1)))),
% 3.22/0.85    introduced(avatar_definition,[new_symbols(naming,[spl2_77])])).
% 3.22/0.85  fof(f2030,plain,(
% 3.22/0.85    k2_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),k5_xboole_0(sK1,k3_xboole_0(sK1,k2_tops_1(sK0,sK1)))) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~spl2_77),
% 3.22/0.85    inference(superposition,[],[f2025,f81])).
% 3.22/0.85  fof(f2025,plain,(
% 3.22/0.85    k2_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),k7_subset_1(k2_pre_topc(sK0,sK1),sK1,k2_tops_1(sK0,sK1))) | ~spl2_77),
% 3.22/0.85    inference(avatar_component_clause,[],[f2023])).
% 3.22/0.85  fof(f2026,plain,(
% 3.22/0.85    ~spl2_52 | spl2_77 | ~spl2_53),
% 3.22/0.85    inference(avatar_split_clause,[],[f1099,f980,f2023,f976])).
% 3.22/0.85  fof(f980,plain,(
% 3.22/0.85    spl2_53 <=> k2_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),sK1)),
% 3.22/0.85    introduced(avatar_definition,[new_symbols(naming,[spl2_53])])).
% 3.22/0.85  fof(f1099,plain,(
% 3.22/0.85    k2_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),k7_subset_1(k2_pre_topc(sK0,sK1),sK1,k2_tops_1(sK0,sK1))) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~spl2_53),
% 3.22/0.85    inference(superposition,[],[f357,f982])).
% 3.22/0.85  fof(f982,plain,(
% 3.22/0.85    k2_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),sK1) | ~spl2_53),
% 3.22/0.85    inference(avatar_component_clause,[],[f980])).
% 3.22/0.85  fof(f357,plain,(
% 3.22/0.85    ( ! [X4,X3] : (k3_subset_1(X3,X4) = k3_subset_1(X3,k7_subset_1(X3,X4,k3_subset_1(X3,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(X3))) )),
% 3.22/0.85    inference(global_subsumption,[],[f76,f352])).
% 3.22/0.85  fof(f352,plain,(
% 3.22/0.85    ( ! [X4,X3] : (k3_subset_1(X3,X4) = k3_subset_1(X3,k7_subset_1(X3,X4,k3_subset_1(X3,X4))) | ~m1_subset_1(k3_subset_1(X3,X4),k1_zfmisc_1(X3)) | ~m1_subset_1(X4,k1_zfmisc_1(X3))) )),
% 3.22/0.85    inference(duplicate_literal_removal,[],[f349])).
% 3.22/0.85  fof(f349,plain,(
% 3.22/0.85    ( ! [X4,X3] : (k3_subset_1(X3,X4) = k3_subset_1(X3,k7_subset_1(X3,X4,k3_subset_1(X3,X4))) | ~m1_subset_1(k3_subset_1(X3,X4),k1_zfmisc_1(X3)) | ~m1_subset_1(X4,k1_zfmisc_1(X3)) | ~m1_subset_1(k3_subset_1(X3,X4),k1_zfmisc_1(X3))) )),
% 3.22/0.85    inference(superposition,[],[f64,f86])).
% 3.22/0.85  fof(f86,plain,(
% 3.22/0.85    ( ! [X0,X1] : (k4_subset_1(X0,X1,X1) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.22/0.85    inference(condensation,[],[f77])).
% 3.22/0.85  fof(f77,plain,(
% 3.22/0.85    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X1) = X1 | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.22/0.85    inference(cnf_transformation,[],[f43])).
% 3.22/0.85  fof(f43,plain,(
% 3.22/0.85    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X1) = X1 | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.22/0.85    inference(flattening,[],[f42])).
% 3.22/0.85  fof(f42,plain,(
% 3.22/0.85    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X1) = X1 | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 3.22/0.85    inference(ennf_transformation,[],[f8])).
% 3.22/0.85  fof(f8,axiom,(
% 3.22/0.85    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X1) = X1)),
% 3.22/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k4_subset_1)).
% 3.22/0.85  fof(f64,plain,(
% 3.22/0.85    ( ! [X2,X0,X1] : (k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.22/0.85    inference(cnf_transformation,[],[f30])).
% 3.22/0.85  fof(f30,plain,(
% 3.22/0.85    ! [X0,X1] : (! [X2] : (k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.22/0.85    inference(ennf_transformation,[],[f11])).
% 3.22/0.85  fof(f11,axiom,(
% 3.22/0.85    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2)))),
% 3.22/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_subset_1)).
% 3.22/0.85  fof(f76,plain,(
% 3.22/0.85    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.22/0.85    inference(cnf_transformation,[],[f41])).
% 3.22/0.85  fof(f41,plain,(
% 3.22/0.85    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.22/0.85    inference(ennf_transformation,[],[f6])).
% 3.22/0.85  fof(f6,axiom,(
% 3.22/0.85    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 3.22/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 3.22/0.85  fof(f1061,plain,(
% 3.22/0.85    ~spl2_52 | spl2_58 | ~spl2_53),
% 3.22/0.85    inference(avatar_split_clause,[],[f990,f980,f1058,f976])).
% 3.22/0.85  fof(f990,plain,(
% 3.22/0.85    sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~spl2_53),
% 3.22/0.85    inference(superposition,[],[f61,f982])).
% 3.22/0.85  fof(f986,plain,(
% 3.22/0.85    ~spl2_9 | spl2_52),
% 3.22/0.85    inference(avatar_contradiction_clause,[],[f984])).
% 3.22/0.85  fof(f984,plain,(
% 3.22/0.85    $false | (~spl2_9 | spl2_52)),
% 3.22/0.85    inference(unit_resulting_resolution,[],[f165,f978,f75])).
% 3.22/0.85  fof(f75,plain,(
% 3.22/0.85    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.22/0.85    inference(cnf_transformation,[],[f51])).
% 3.22/0.85  fof(f51,plain,(
% 3.22/0.85    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.22/0.85    inference(nnf_transformation,[],[f13])).
% 3.22/0.85  fof(f13,axiom,(
% 3.22/0.85    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.22/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 3.22/0.85  fof(f978,plain,(
% 3.22/0.85    ~m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | spl2_52),
% 3.22/0.85    inference(avatar_component_clause,[],[f976])).
% 3.22/0.85  fof(f165,plain,(
% 3.22/0.85    r1_tarski(sK1,k2_pre_topc(sK0,sK1)) | ~spl2_9),
% 3.22/0.85    inference(avatar_component_clause,[],[f163])).
% 3.22/0.85  fof(f163,plain,(
% 3.22/0.85    spl2_9 <=> r1_tarski(sK1,k2_pre_topc(sK0,sK1))),
% 3.22/0.85    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 3.22/0.85  fof(f983,plain,(
% 3.22/0.85    ~spl2_52 | ~spl2_15 | spl2_53 | ~spl2_5),
% 3.22/0.85    inference(avatar_split_clause,[],[f942,f107,f980,f200,f976])).
% 3.22/0.85  fof(f200,plain,(
% 3.22/0.85    spl2_15 <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.22/0.85    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 3.22/0.85  fof(f107,plain,(
% 3.22/0.85    spl2_5 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)),
% 3.22/0.85    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 3.22/0.85  fof(f942,plain,(
% 3.22/0.85    k2_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),sK1) | ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~spl2_5),
% 3.22/0.85    inference(superposition,[],[f277,f109])).
% 3.22/0.85  fof(f109,plain,(
% 3.22/0.85    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~spl2_5),
% 3.22/0.85    inference(avatar_component_clause,[],[f107])).
% 3.22/0.85  fof(f277,plain,(
% 3.22/0.85    ( ! [X10,X11,X9] : (k3_subset_1(X9,X10) = k7_subset_1(X11,X9,X10) | ~m1_subset_1(X9,k1_zfmisc_1(X11)) | ~m1_subset_1(X10,k1_zfmisc_1(X9))) )),
% 3.22/0.85    inference(superposition,[],[f81,f82])).
% 3.22/0.85  fof(f82,plain,(
% 3.22/0.85    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.22/0.85    inference(definition_unfolding,[],[f62,f78])).
% 3.22/0.85  fof(f62,plain,(
% 3.22/0.85    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.22/0.85    inference(cnf_transformation,[],[f28])).
% 3.22/0.85  fof(f28,plain,(
% 3.22/0.85    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.22/0.85    inference(ennf_transformation,[],[f5])).
% 3.22/0.85  fof(f5,axiom,(
% 3.22/0.85    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 3.22/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 3.22/0.85  fof(f446,plain,(
% 3.22/0.85    sK1 != k1_tops_1(sK0,sK1) | v3_pre_topc(sK1,sK0) | ~v3_pre_topc(k1_tops_1(sK0,sK1),sK0)),
% 3.22/0.85    introduced(theory_tautology_sat_conflict,[])).
% 3.22/0.85  fof(f445,plain,(
% 3.22/0.85    ~spl2_2 | ~spl2_3 | spl2_5 | ~spl2_14),
% 3.22/0.85    inference(avatar_split_clause,[],[f383,f193,f107,f98,f93])).
% 3.22/0.85  fof(f383,plain,(
% 3.22/0.85    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl2_14),
% 3.22/0.85    inference(superposition,[],[f65,f195])).
% 3.22/0.85  fof(f195,plain,(
% 3.22/0.85    sK1 = k1_tops_1(sK0,sK1) | ~spl2_14),
% 3.22/0.85    inference(avatar_component_clause,[],[f193])).
% 3.22/0.85  fof(f65,plain,(
% 3.22/0.85    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.22/0.85    inference(cnf_transformation,[],[f31])).
% 3.22/0.85  fof(f31,plain,(
% 3.22/0.85    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.22/0.85    inference(ennf_transformation,[],[f18])).
% 3.22/0.85  fof(f18,axiom,(
% 3.22/0.85    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 3.22/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).
% 3.22/0.85  fof(f378,plain,(
% 3.22/0.85    ~spl2_2 | ~spl2_3 | ~spl2_4 | spl2_13),
% 3.22/0.85    inference(avatar_contradiction_clause,[],[f368])).
% 3.22/0.85  fof(f368,plain,(
% 3.22/0.85    $false | (~spl2_2 | ~spl2_3 | ~spl2_4 | spl2_13)),
% 3.22/0.85    inference(unit_resulting_resolution,[],[f95,f105,f84,f100,f191,f100,f70])).
% 3.22/0.85  fof(f70,plain,(
% 3.22/0.85    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | r1_tarski(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.22/0.85    inference(cnf_transformation,[],[f39])).
% 3.22/0.85  fof(f39,plain,(
% 3.22/0.85    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.22/0.85    inference(flattening,[],[f38])).
% 3.22/0.85  fof(f38,plain,(
% 3.22/0.85    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(X1,k1_tops_1(X0,X2)) | (~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.22/0.85    inference(ennf_transformation,[],[f20])).
% 3.22/0.85  fof(f20,axiom,(
% 3.22/0.85    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v3_pre_topc(X1,X0)) => r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 3.22/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_1)).
% 3.22/0.85  fof(f191,plain,(
% 3.22/0.85    ~r1_tarski(sK1,k1_tops_1(sK0,sK1)) | spl2_13),
% 3.22/0.85    inference(avatar_component_clause,[],[f189])).
% 3.22/0.85  fof(f189,plain,(
% 3.22/0.85    spl2_13 <=> r1_tarski(sK1,k1_tops_1(sK0,sK1))),
% 3.22/0.85    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 3.22/0.85  fof(f100,plain,(
% 3.22/0.85    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_3),
% 3.22/0.85    inference(avatar_component_clause,[],[f98])).
% 3.22/0.85  fof(f84,plain,(
% 3.22/0.85    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.22/0.85    inference(equality_resolution,[],[f59])).
% 3.22/0.85  fof(f59,plain,(
% 3.22/0.85    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.22/0.85    inference(cnf_transformation,[],[f50])).
% 3.22/0.85  fof(f50,plain,(
% 3.22/0.85    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.22/0.85    inference(flattening,[],[f49])).
% 3.22/0.85  fof(f49,plain,(
% 3.22/0.85    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.22/0.85    inference(nnf_transformation,[],[f1])).
% 3.22/0.85  fof(f1,axiom,(
% 3.22/0.85    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.22/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 3.22/0.85  fof(f105,plain,(
% 3.22/0.85    v3_pre_topc(sK1,sK0) | ~spl2_4),
% 3.22/0.85    inference(avatar_component_clause,[],[f103])).
% 3.22/0.85  fof(f103,plain,(
% 3.22/0.85    spl2_4 <=> v3_pre_topc(sK1,sK0)),
% 3.22/0.85    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 3.22/0.85  fof(f95,plain,(
% 3.22/0.85    l1_pre_topc(sK0) | ~spl2_2),
% 3.22/0.85    inference(avatar_component_clause,[],[f93])).
% 3.22/0.85  fof(f273,plain,(
% 3.22/0.85    ~spl2_1 | ~spl2_2 | spl2_19 | ~spl2_3),
% 3.22/0.85    inference(avatar_split_clause,[],[f261,f98,f270,f93,f88])).
% 3.22/0.85  fof(f88,plain,(
% 3.22/0.85    spl2_1 <=> v2_pre_topc(sK0)),
% 3.22/0.85    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 3.22/0.85  fof(f270,plain,(
% 3.22/0.85    spl2_19 <=> v3_pre_topc(k1_tops_1(sK0,sK1),sK0)),
% 3.22/0.85    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 3.22/0.85  fof(f261,plain,(
% 3.22/0.85    v3_pre_topc(k1_tops_1(sK0,sK1),sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~spl2_3),
% 3.22/0.85    inference(resolution,[],[f69,f100])).
% 3.22/0.85  fof(f69,plain,(
% 3.22/0.85    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(k1_tops_1(X0,X1),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.22/0.85    inference(cnf_transformation,[],[f37])).
% 3.22/0.85  fof(f37,plain,(
% 3.22/0.85    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.22/0.85    inference(flattening,[],[f36])).
% 3.22/0.85  fof(f36,plain,(
% 3.22/0.85    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.22/0.85    inference(ennf_transformation,[],[f17])).
% 3.22/0.85  fof(f17,axiom,(
% 3.22/0.85    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 3.22/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).
% 3.22/0.85  fof(f243,plain,(
% 3.22/0.85    ~spl2_2 | ~spl2_3 | spl2_15),
% 3.22/0.85    inference(avatar_contradiction_clause,[],[f236])).
% 3.22/0.85  fof(f236,plain,(
% 3.22/0.85    $false | (~spl2_2 | ~spl2_3 | spl2_15)),
% 3.22/0.85    inference(unit_resulting_resolution,[],[f95,f100,f202,f67])).
% 3.22/0.85  fof(f67,plain,(
% 3.22/0.85    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.22/0.85    inference(cnf_transformation,[],[f34])).
% 3.22/0.85  fof(f34,plain,(
% 3.22/0.85    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.22/0.85    inference(flattening,[],[f33])).
% 3.22/0.85  fof(f33,plain,(
% 3.22/0.85    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 3.22/0.85    inference(ennf_transformation,[],[f15])).
% 3.22/0.85  fof(f15,axiom,(
% 3.22/0.85    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 3.22/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 3.22/0.85  fof(f202,plain,(
% 3.22/0.85    ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl2_15),
% 3.22/0.85    inference(avatar_component_clause,[],[f200])).
% 3.22/0.85  fof(f196,plain,(
% 3.22/0.85    ~spl2_13 | spl2_14 | ~spl2_12),
% 3.22/0.85    inference(avatar_split_clause,[],[f187,f183,f193,f189])).
% 3.22/0.85  fof(f183,plain,(
% 3.22/0.85    spl2_12 <=> r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 3.22/0.85    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 3.22/0.85  fof(f187,plain,(
% 3.22/0.85    sK1 = k1_tops_1(sK0,sK1) | ~r1_tarski(sK1,k1_tops_1(sK0,sK1)) | ~spl2_12),
% 3.22/0.85    inference(resolution,[],[f185,f60])).
% 3.22/0.85  fof(f60,plain,(
% 3.22/0.85    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 3.22/0.85    inference(cnf_transformation,[],[f50])).
% 3.22/0.85  fof(f185,plain,(
% 3.22/0.85    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~spl2_12),
% 3.22/0.85    inference(avatar_component_clause,[],[f183])).
% 3.22/0.85  fof(f186,plain,(
% 3.22/0.85    ~spl2_2 | spl2_12 | ~spl2_3),
% 3.22/0.85    inference(avatar_split_clause,[],[f181,f98,f183,f93])).
% 3.22/0.85  fof(f181,plain,(
% 3.22/0.85    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~l1_pre_topc(sK0) | ~spl2_3),
% 3.22/0.85    inference(resolution,[],[f71,f100])).
% 3.22/0.86  fof(f71,plain,(
% 3.22/0.86    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k1_tops_1(X0,X1),X1) | ~l1_pre_topc(X0)) )),
% 3.22/0.86    inference(cnf_transformation,[],[f40])).
% 3.22/0.86  fof(f40,plain,(
% 3.22/0.86    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.22/0.86    inference(ennf_transformation,[],[f19])).
% 3.22/0.86  fof(f19,axiom,(
% 3.22/0.86    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 3.22/0.86    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).
% 3.22/0.86  fof(f166,plain,(
% 3.22/0.86    ~spl2_2 | spl2_9 | ~spl2_3),
% 3.22/0.86    inference(avatar_split_clause,[],[f161,f98,f163,f93])).
% 3.22/0.86  fof(f161,plain,(
% 3.22/0.86    r1_tarski(sK1,k2_pre_topc(sK0,sK1)) | ~l1_pre_topc(sK0) | ~spl2_3),
% 3.22/0.86    inference(resolution,[],[f68,f100])).
% 3.22/0.86  fof(f68,plain,(
% 3.22/0.86    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(X1,k2_pre_topc(X0,X1)) | ~l1_pre_topc(X0)) )),
% 3.22/0.86    inference(cnf_transformation,[],[f35])).
% 3.22/0.86  fof(f35,plain,(
% 3.22/0.86    ! [X0] : (! [X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.22/0.86    inference(ennf_transformation,[],[f16])).
% 3.22/0.86  fof(f16,axiom,(
% 3.22/0.86    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(X1,k2_pre_topc(X0,X1))))),
% 3.22/0.86    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).
% 3.22/0.86  fof(f113,plain,(
% 3.22/0.86    ~spl2_4 | ~spl2_5),
% 3.22/0.86    inference(avatar_split_clause,[],[f112,f107,f103])).
% 3.22/0.86  fof(f112,plain,(
% 3.22/0.86    ~v3_pre_topc(sK1,sK0) | ~spl2_5),
% 3.22/0.86    inference(trivial_inequality_removal,[],[f111])).
% 3.22/0.86  fof(f111,plain,(
% 3.22/0.86    k2_tops_1(sK0,sK1) != k2_tops_1(sK0,sK1) | ~v3_pre_topc(sK1,sK0) | ~spl2_5),
% 3.22/0.86    inference(forward_demodulation,[],[f56,f109])).
% 3.22/0.86  fof(f56,plain,(
% 3.22/0.86    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)),
% 3.22/0.86    inference(cnf_transformation,[],[f48])).
% 3.22/0.86  fof(f48,plain,(
% 3.22/0.86    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 3.22/0.86    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f45,f47,f46])).
% 3.22/0.86  fof(f46,plain,(
% 3.22/0.86    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | ~v3_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 3.22/0.86    introduced(choice_axiom,[])).
% 3.22/0.86  fof(f47,plain,(
% 3.22/0.86    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | ~v3_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 3.22/0.86    introduced(choice_axiom,[])).
% 3.22/0.86  fof(f45,plain,(
% 3.22/0.86    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.22/0.86    inference(flattening,[],[f44])).
% 3.22/0.86  fof(f44,plain,(
% 3.22/0.86    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.22/0.86    inference(nnf_transformation,[],[f25])).
% 3.22/0.86  fof(f25,plain,(
% 3.22/0.86    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.22/0.86    inference(flattening,[],[f24])).
% 3.22/0.86  fof(f24,plain,(
% 3.22/0.86    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 3.22/0.86    inference(ennf_transformation,[],[f23])).
% 3.22/0.86  fof(f23,negated_conjecture,(
% 3.22/0.86    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 3.22/0.86    inference(negated_conjecture,[],[f22])).
% 3.22/0.86  fof(f22,conjecture,(
% 3.22/0.86    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 3.22/0.86    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tops_1)).
% 3.22/0.86  fof(f110,plain,(
% 3.22/0.86    spl2_4 | spl2_5),
% 3.22/0.86    inference(avatar_split_clause,[],[f55,f107,f103])).
% 3.22/0.86  fof(f55,plain,(
% 3.22/0.86    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)),
% 3.22/0.86    inference(cnf_transformation,[],[f48])).
% 3.22/0.86  fof(f101,plain,(
% 3.22/0.86    spl2_3),
% 3.22/0.86    inference(avatar_split_clause,[],[f54,f98])).
% 3.22/0.86  fof(f54,plain,(
% 3.22/0.86    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.22/0.86    inference(cnf_transformation,[],[f48])).
% 3.22/0.86  fof(f96,plain,(
% 3.22/0.86    spl2_2),
% 3.22/0.86    inference(avatar_split_clause,[],[f53,f93])).
% 3.22/0.86  fof(f53,plain,(
% 3.22/0.86    l1_pre_topc(sK0)),
% 3.22/0.86    inference(cnf_transformation,[],[f48])).
% 3.22/0.86  fof(f91,plain,(
% 3.22/0.86    spl2_1),
% 3.22/0.86    inference(avatar_split_clause,[],[f52,f88])).
% 3.22/0.86  fof(f52,plain,(
% 3.22/0.86    v2_pre_topc(sK0)),
% 3.22/0.86    inference(cnf_transformation,[],[f48])).
% 3.22/0.86  % SZS output end Proof for theBenchmark
% 3.22/0.86  % (5478)------------------------------
% 3.22/0.86  % (5478)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.22/0.86  % (5478)Termination reason: Refutation
% 3.22/0.86  
% 3.22/0.86  % (5478)Memory used [KB]: 13688
% 3.22/0.86  % (5478)Time elapsed: 0.428 s
% 3.22/0.86  % (5478)------------------------------
% 3.22/0.86  % (5478)------------------------------
% 3.22/0.86  % (5454)Success in time 0.497 s
%------------------------------------------------------------------------------
