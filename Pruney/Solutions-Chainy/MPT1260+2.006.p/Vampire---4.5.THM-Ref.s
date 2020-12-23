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
% DateTime   : Thu Dec  3 13:11:33 EST 2020

% Result     : Theorem 5.09s
% Output     : Refutation 5.09s
% Verified   : 
% Statistics : Number of formulae       :  193 ( 363 expanded)
%              Number of leaves         :   43 ( 130 expanded)
%              Depth                    :   13
%              Number of atoms          :  570 (1133 expanded)
%              Number of equality atoms :   96 ( 220 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4817,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f124,f125,f130,f135,f140,f647,f2049,f2096,f2135,f2152,f2240,f3115,f3189,f3194,f3203,f3221,f3295,f4638,f4709,f4810,f4816])).

fof(f4816,plain,
    ( sK1 != k1_tops_1(sK0,sK1)
    | ~ v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | v3_pre_topc(sK1,sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f4810,plain,(
    ~ spl3_129 ),
    inference(avatar_contradiction_clause,[],[f4771])).

fof(f4771,plain,
    ( $false
    | ~ spl3_129 ),
    inference(unit_resulting_resolution,[],[f161,f97,f3287,f110])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f61])).

fof(f61,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).

fof(f3287,plain,
    ( ! [X2] : ~ m1_subset_1(X2,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl3_129 ),
    inference(avatar_component_clause,[],[f3286])).

fof(f3286,plain,
    ( spl3_129
  <=> ! [X2] : ~ m1_subset_1(X2,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_129])])).

fof(f97,plain,(
    ! [X0] : m1_subset_1(sK2(X0),X0) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,(
    ! [X0] : m1_subset_1(sK2(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f18,f71])).

fof(f71,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f18,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(f161,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(superposition,[],[f153,f101])).

fof(f101,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f153,plain,(
    ! [X0,X1] : m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0)) ),
    inference(backward_demodulation,[],[f112,f100])).

fof(f100,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f112,plain,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).

fof(f4709,plain,
    ( ~ spl3_3
    | ~ spl3_4
    | spl3_104
    | ~ spl3_177 ),
    inference(avatar_contradiction_clause,[],[f4708])).

fof(f4708,plain,
    ( $false
    | ~ spl3_3
    | ~ spl3_4
    | spl3_104
    | ~ spl3_177 ),
    inference(subsumption_resolution,[],[f4707,f134])).

fof(f134,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f132])).

fof(f132,plain,
    ( spl3_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f4707,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl3_3
    | spl3_104
    | ~ spl3_177 ),
    inference(subsumption_resolution,[],[f4706,f129])).

fof(f129,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl3_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f4706,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl3_104
    | ~ spl3_177 ),
    inference(subsumption_resolution,[],[f4685,f2249])).

fof(f2249,plain,
    ( sK1 != k1_tops_1(sK0,sK1)
    | spl3_104 ),
    inference(avatar_component_clause,[],[f2248])).

fof(f2248,plain,
    ( spl3_104
  <=> sK1 = k1_tops_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_104])])).

fof(f4685,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_177 ),
    inference(superposition,[],[f302,f4637])).

fof(f4637,plain,
    ( sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl3_177 ),
    inference(avatar_component_clause,[],[f4635])).

fof(f4635,plain,
    ( spl3_177
  <=> sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_177])])).

fof(f302,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f301])).

fof(f301,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(superposition,[],[f78,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f4638,plain,
    ( spl3_129
    | spl3_177
    | ~ spl3_26
    | ~ spl3_34 ),
    inference(avatar_split_clause,[],[f4633,f732,f695,f4635,f3286])).

fof(f695,plain,
    ( spl3_26
  <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f732,plain,
    ( spl3_34
  <=> sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).

fof(f4633,plain,
    ( ! [X18] :
        ( sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) )
    | ~ spl3_26
    | ~ spl3_34 ),
    inference(subsumption_resolution,[],[f4607,f697])).

fof(f697,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl3_26 ),
    inference(avatar_component_clause,[],[f695])).

fof(f4607,plain,
    ( ! [X18] :
        ( sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
        | ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) )
    | ~ spl3_34 ),
    inference(superposition,[],[f862,f734])).

fof(f734,plain,
    ( sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))
    | ~ spl3_34 ),
    inference(avatar_component_clause,[],[f732])).

fof(f862,plain,(
    ! [X4,X2,X3] :
      ( k3_subset_1(X2,X3) = k4_xboole_0(k3_subset_1(X2,X3),X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
      | ~ m1_subset_1(X4,k1_zfmisc_1(X2)) ) ),
    inference(subsumption_resolution,[],[f857,f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f857,plain,(
    ! [X4,X2,X3] :
      ( k3_subset_1(X2,X3) = k4_xboole_0(k3_subset_1(X2,X3),X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
      | ~ m1_subset_1(X4,k1_zfmisc_1(X2))
      | ~ m1_subset_1(k3_subset_1(X2,X3),k1_zfmisc_1(X2)) ) ),
    inference(superposition,[],[f330,f78])).

fof(f330,plain,(
    ! [X4,X5,X3] :
      ( k3_subset_1(X3,X4) = k7_subset_1(X3,k3_subset_1(X3,X4),X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(X3)) ) ),
    inference(subsumption_resolution,[],[f326,f96])).

fof(f326,plain,(
    ! [X4,X5,X3] :
      ( k3_subset_1(X3,X4) = k7_subset_1(X3,k3_subset_1(X3,X4),X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
      | ~ m1_subset_1(k3_subset_1(X3,X4),k1_zfmisc_1(X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(X3)) ) ),
    inference(superposition,[],[f87,f108])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k9_subset_1)).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_subset_1)).

fof(f3295,plain,
    ( spl3_93
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f3294,f132,f127,f2149])).

fof(f2149,plain,
    ( spl3_93
  <=> r1_tarski(sK1,k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_93])])).

fof(f3294,plain,
    ( r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f3136,f134])).

fof(f3136,plain,
    ( r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_3 ),
    inference(resolution,[],[f781,f129])).

fof(f781,plain,(
    ! [X4,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))
      | r1_tarski(X3,k2_pre_topc(X4,X3))
      | ~ l1_pre_topc(X4) ) ),
    inference(superposition,[],[f104,f315])).

fof(f315,plain,(
    ! [X2,X3] :
      ( k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2) ) ),
    inference(subsumption_resolution,[],[f312,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(f312,plain,(
    ! [X2,X3] :
      ( k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2)
      | ~ m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) ) ),
    inference(duplicate_literal_removal,[],[f307])).

fof(f307,plain,(
    ! [X2,X3] :
      ( k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2)
      | ~ m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ) ),
    inference(superposition,[],[f90,f109])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f90,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

fof(f104,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f3221,plain,
    ( spl3_26
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f3207,f255,f695])).

fof(f255,plain,
    ( spl3_11
  <=> k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f3207,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl3_11 ),
    inference(superposition,[],[f153,f257])).

fof(f257,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f255])).

fof(f3203,plain,
    ( spl3_11
    | ~ spl3_2
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f3202,f251,f121,f255])).

fof(f121,plain,
    ( spl3_2
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f251,plain,
    ( spl3_10
  <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f3202,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ spl3_2
    | ~ spl3_10 ),
    inference(subsumption_resolution,[],[f3199,f252])).

fof(f252,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f251])).

fof(f3199,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_2 ),
    inference(superposition,[],[f78,f122])).

fof(f122,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f121])).

fof(f3194,plain,
    ( ~ spl3_89
    | spl3_104
    | ~ spl3_103 ),
    inference(avatar_split_clause,[],[f3122,f2244,f2248,f2090])).

fof(f2090,plain,
    ( spl3_89
  <=> r1_tarski(sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_89])])).

fof(f2244,plain,
    ( spl3_103
  <=> r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_103])])).

fof(f3122,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | ~ spl3_103 ),
    inference(resolution,[],[f2245,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f68])).

fof(f68,plain,(
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

fof(f2245,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl3_103 ),
    inference(avatar_component_clause,[],[f2244])).

fof(f3189,plain,
    ( ~ spl3_3
    | ~ spl3_4
    | spl3_11
    | ~ spl3_104 ),
    inference(avatar_contradiction_clause,[],[f3188])).

fof(f3188,plain,
    ( $false
    | ~ spl3_3
    | ~ spl3_4
    | spl3_11
    | ~ spl3_104 ),
    inference(subsumption_resolution,[],[f3187,f134])).

fof(f3187,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl3_3
    | spl3_11
    | ~ spl3_104 ),
    inference(subsumption_resolution,[],[f3186,f129])).

fof(f3186,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl3_11
    | ~ spl3_104 ),
    inference(subsumption_resolution,[],[f3177,f256])).

fof(f256,plain,
    ( k2_tops_1(sK0,sK1) != k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | spl3_11 ),
    inference(avatar_component_clause,[],[f255])).

fof(f3177,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_104 ),
    inference(superposition,[],[f1009,f2250])).

fof(f2250,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ spl3_104 ),
    inference(avatar_component_clause,[],[f2248])).

fof(f1009,plain,(
    ! [X2,X3] :
      ( k2_tops_1(X2,X3) = k4_xboole_0(k2_pre_topc(X2,X3),k1_tops_1(X2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2) ) ),
    inference(subsumption_resolution,[],[f334,f317])).

fof(f317,plain,(
    ! [X2,X3] :
      ( m1_subset_1(k2_pre_topc(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2) ) ),
    inference(subsumption_resolution,[],[f310,f91])).

fof(f310,plain,(
    ! [X2,X3] :
      ( m1_subset_1(k2_pre_topc(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2) ) ),
    inference(duplicate_literal_removal,[],[f309])).

fof(f309,plain,(
    ! [X2,X3] :
      ( m1_subset_1(k2_pre_topc(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2) ) ),
    inference(superposition,[],[f110,f90])).

fof(f334,plain,(
    ! [X2,X3] :
      ( k2_tops_1(X2,X3) = k4_xboole_0(k2_pre_topc(X2,X3),k1_tops_1(X2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2)
      | ~ m1_subset_1(k2_pre_topc(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) ) ),
    inference(superposition,[],[f88,f78])).

fof(f88,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

fof(f3115,plain,
    ( spl3_103
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f3114,f132,f127,f2244])).

fof(f3114,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f3105,f134])).

fof(f3105,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl3_3 ),
    inference(resolution,[],[f756,f129])).

fof(f756,plain,(
    ! [X6,X7] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X7)))
      | r1_tarski(k1_tops_1(X7,X6),X6)
      | ~ l1_pre_topc(X7) ) ),
    inference(superposition,[],[f160,f302])).

fof(f160,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(resolution,[],[f153,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f2240,plain,
    ( ~ spl3_11
    | spl3_2
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f2239,f251,f121,f255])).

fof(f2239,plain,
    ( k2_tops_1(sK0,sK1) != k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | spl3_2
    | ~ spl3_10 ),
    inference(subsumption_resolution,[],[f2238,f252])).

fof(f2238,plain,
    ( k2_tops_1(sK0,sK1) != k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_2 ),
    inference(superposition,[],[f123,f78])).

fof(f123,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f121])).

fof(f2152,plain,
    ( ~ spl3_93
    | spl3_33 ),
    inference(avatar_split_clause,[],[f2147,f728,f2149])).

fof(f728,plain,
    ( spl3_33
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).

fof(f2147,plain,
    ( ~ r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | spl3_33 ),
    inference(resolution,[],[f730,f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f730,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | spl3_33 ),
    inference(avatar_component_clause,[],[f728])).

fof(f2135,plain,
    ( ~ spl3_33
    | spl3_34
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f2115,f255,f732,f728])).

fof(f2115,plain,
    ( sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl3_11 ),
    inference(superposition,[],[f238,f257])).

fof(f238,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k4_xboole_0(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f234])).

fof(f234,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k4_xboole_0(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(superposition,[],[f82,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f82,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f2096,plain,
    ( spl3_89
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f2095,f132,f127,f117,f2090])).

fof(f117,plain,
    ( spl3_1
  <=> v3_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f2095,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f2078,f114])).

fof(f114,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f69])).

fof(f2078,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | ~ r1_tarski(sK1,sK1)
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(resolution,[],[f2046,f129])).

fof(f2046,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X1,sK0)
        | r1_tarski(X1,k1_tops_1(sK0,sK1))
        | ~ r1_tarski(X1,sK1) )
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f2040,f134])).

fof(f2040,plain,
    ( ! [X1] :
        ( ~ r1_tarski(X1,sK1)
        | ~ v3_pre_topc(X1,sK0)
        | r1_tarski(X1,k1_tops_1(sK0,sK1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl3_3 ),
    inference(resolution,[],[f129,f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X1,X2)
      | ~ v3_pre_topc(X1,X0)
      | r1_tarski(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f50])).

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
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
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

fof(f2049,plain,
    ( spl3_13
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f2048,f137,f132,f127,f278])).

fof(f278,plain,
    ( spl3_13
  <=> v3_pre_topc(k1_tops_1(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f137,plain,
    ( spl3_5
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f2048,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f2047,f139])).

fof(f139,plain,
    ( v2_pre_topc(sK0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f137])).

fof(f2047,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f2041,f134])).

fof(f2041,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl3_3 ),
    inference(resolution,[],[f129,f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

fof(f647,plain,
    ( ~ spl3_3
    | ~ spl3_4
    | spl3_10 ),
    inference(avatar_contradiction_clause,[],[f646])).

fof(f646,plain,
    ( $false
    | ~ spl3_3
    | ~ spl3_4
    | spl3_10 ),
    inference(subsumption_resolution,[],[f645,f134])).

fof(f645,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl3_3
    | spl3_10 ),
    inference(subsumption_resolution,[],[f638,f129])).

fof(f638,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl3_10 ),
    inference(resolution,[],[f317,f253])).

fof(f253,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_10 ),
    inference(avatar_component_clause,[],[f251])).

fof(f140,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f73,f137])).

fof(f73,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,
    ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
      | ~ v3_pre_topc(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
      | v3_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f64,f66,f65])).

fof(f65,plain,
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

fof(f66,plain,
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

fof(f64,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f63])).

fof(f63,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f35])).

fof(f35,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    inference(negated_conjecture,[],[f34])).

fof(f34,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tops_1)).

fof(f135,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f74,f132])).

fof(f74,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f67])).

fof(f130,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f75,f127])).

fof(f75,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f67])).

fof(f125,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f76,f121,f117])).

fof(f76,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f67])).

fof(f124,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f77,f121,f117])).

fof(f77,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f67])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:43:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.51  % (23268)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.51  % (23265)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.52  % (23279)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.52  % (23273)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.52  % (23287)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.53  % (23281)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.53  % (23293)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.53  % (23289)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.53  % (23270)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.53  % (23280)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.53  % (23292)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.53  % (23271)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.53  % (23291)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.53  % (23269)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.54  % (23266)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.54  % (23267)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.54  % (23272)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.54  % (23284)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.54  % (23294)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.54  % (23286)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.54  % (23283)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.55  % (23274)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.55  % (23282)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.55  % (23276)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.55  % (23285)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.55  % (23278)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.55  % (23275)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.47/0.55  % (23295)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.47/0.55  % (23277)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.47/0.55  % (23290)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 3.13/0.84  % (23267)Time limit reached!
% 3.13/0.84  % (23267)------------------------------
% 3.13/0.84  % (23267)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.71/0.84  % (23267)Termination reason: Time limit
% 3.71/0.84  
% 3.71/0.84  % (23267)Memory used [KB]: 6780
% 3.71/0.84  % (23267)Time elapsed: 0.429 s
% 3.71/0.84  % (23267)------------------------------
% 3.71/0.84  % (23267)------------------------------
% 3.95/0.88  % (23290)Time limit reached!
% 3.95/0.88  % (23290)------------------------------
% 3.95/0.88  % (23290)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.95/0.88  % (23290)Termination reason: Time limit
% 3.95/0.88  
% 3.95/0.88  % (23290)Memory used [KB]: 13432
% 3.95/0.88  % (23290)Time elapsed: 0.432 s
% 3.95/0.88  % (23290)------------------------------
% 3.95/0.88  % (23290)------------------------------
% 3.95/0.92  % (23279)Time limit reached!
% 3.95/0.92  % (23279)------------------------------
% 3.95/0.92  % (23279)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.95/0.93  % (23271)Time limit reached!
% 3.95/0.93  % (23271)------------------------------
% 3.95/0.93  % (23271)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.95/0.93  % (23271)Termination reason: Time limit
% 4.39/0.93  
% 4.39/0.93  % (23271)Memory used [KB]: 15223
% 4.39/0.93  % (23271)Time elapsed: 0.514 s
% 4.39/0.93  % (23271)------------------------------
% 4.39/0.93  % (23271)------------------------------
% 4.39/0.93  % (23279)Termination reason: Time limit
% 4.39/0.93  
% 4.39/0.93  % (23279)Memory used [KB]: 6652
% 4.39/0.93  % (23279)Time elapsed: 0.505 s
% 4.39/0.93  % (23279)------------------------------
% 4.39/0.93  % (23279)------------------------------
% 4.39/0.93  % (23295)Time limit reached!
% 4.39/0.93  % (23295)------------------------------
% 4.39/0.93  % (23295)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.39/0.93  % (23295)Termination reason: Time limit
% 4.39/0.93  
% 4.39/0.93  % (23295)Memory used [KB]: 3837
% 4.39/0.93  % (23295)Time elapsed: 0.515 s
% 4.39/0.93  % (23295)------------------------------
% 4.39/0.93  % (23295)------------------------------
% 4.61/0.96  % (23495)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 4.61/1.00  % (23501)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 5.09/1.03  % (23502)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 5.09/1.04  % (23286)Refutation found. Thanks to Tanya!
% 5.09/1.04  % SZS status Theorem for theBenchmark
% 5.09/1.04  % SZS output start Proof for theBenchmark
% 5.09/1.04  fof(f4817,plain,(
% 5.09/1.04    $false),
% 5.09/1.04    inference(avatar_sat_refutation,[],[f124,f125,f130,f135,f140,f647,f2049,f2096,f2135,f2152,f2240,f3115,f3189,f3194,f3203,f3221,f3295,f4638,f4709,f4810,f4816])).
% 5.09/1.04  fof(f4816,plain,(
% 5.09/1.04    sK1 != k1_tops_1(sK0,sK1) | ~v3_pre_topc(k1_tops_1(sK0,sK1),sK0) | v3_pre_topc(sK1,sK0)),
% 5.09/1.04    introduced(theory_tautology_sat_conflict,[])).
% 5.09/1.04  fof(f4810,plain,(
% 5.09/1.04    ~spl3_129),
% 5.09/1.04    inference(avatar_contradiction_clause,[],[f4771])).
% 5.09/1.04  fof(f4771,plain,(
% 5.09/1.04    $false | ~spl3_129),
% 5.09/1.04    inference(unit_resulting_resolution,[],[f161,f97,f3287,f110])).
% 5.09/1.04  fof(f110,plain,(
% 5.09/1.04    ( ! [X2,X0,X1] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 5.09/1.04    inference(cnf_transformation,[],[f62])).
% 5.09/1.04  fof(f62,plain,(
% 5.09/1.04    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 5.09/1.04    inference(flattening,[],[f61])).
% 5.09/1.04  fof(f61,plain,(
% 5.09/1.04    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 5.09/1.04    inference(ennf_transformation,[],[f16])).
% 5.09/1.04  fof(f16,axiom,(
% 5.09/1.04    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 5.09/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).
% 5.09/1.04  fof(f3287,plain,(
% 5.09/1.04    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))) ) | ~spl3_129),
% 5.09/1.04    inference(avatar_component_clause,[],[f3286])).
% 5.09/1.04  fof(f3286,plain,(
% 5.09/1.04    spl3_129 <=> ! [X2] : ~m1_subset_1(X2,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))),
% 5.09/1.04    introduced(avatar_definition,[new_symbols(naming,[spl3_129])])).
% 5.09/1.04  fof(f97,plain,(
% 5.09/1.04    ( ! [X0] : (m1_subset_1(sK2(X0),X0)) )),
% 5.09/1.04    inference(cnf_transformation,[],[f72])).
% 5.09/1.04  fof(f72,plain,(
% 5.09/1.04    ! [X0] : m1_subset_1(sK2(X0),X0)),
% 5.09/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f18,f71])).
% 5.09/1.04  fof(f71,plain,(
% 5.09/1.04    ! [X0] : (? [X1] : m1_subset_1(X1,X0) => m1_subset_1(sK2(X0),X0))),
% 5.09/1.04    introduced(choice_axiom,[])).
% 5.09/1.04  fof(f18,axiom,(
% 5.09/1.04    ! [X0] : ? [X1] : m1_subset_1(X1,X0)),
% 5.09/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).
% 5.09/1.04  fof(f161,plain,(
% 5.09/1.04    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 5.09/1.04    inference(superposition,[],[f153,f101])).
% 5.09/1.04  fof(f101,plain,(
% 5.09/1.04    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 5.09/1.04    inference(cnf_transformation,[],[f7])).
% 5.09/1.04  fof(f7,axiom,(
% 5.09/1.04    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 5.09/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 5.09/1.04  fof(f153,plain,(
% 5.09/1.04    ( ! [X0,X1] : (m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0))) )),
% 5.09/1.04    inference(backward_demodulation,[],[f112,f100])).
% 5.09/1.04  fof(f100,plain,(
% 5.09/1.04    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 5.09/1.04    inference(cnf_transformation,[],[f22])).
% 5.09/1.04  fof(f22,axiom,(
% 5.09/1.04    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 5.09/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 5.09/1.04  fof(f112,plain,(
% 5.09/1.04    ( ! [X0,X1] : (m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 5.09/1.04    inference(cnf_transformation,[],[f17])).
% 5.09/1.04  fof(f17,axiom,(
% 5.09/1.04    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))),
% 5.09/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).
% 5.09/1.04  fof(f4709,plain,(
% 5.09/1.04    ~spl3_3 | ~spl3_4 | spl3_104 | ~spl3_177),
% 5.09/1.04    inference(avatar_contradiction_clause,[],[f4708])).
% 5.09/1.04  fof(f4708,plain,(
% 5.09/1.04    $false | (~spl3_3 | ~spl3_4 | spl3_104 | ~spl3_177)),
% 5.09/1.04    inference(subsumption_resolution,[],[f4707,f134])).
% 5.09/1.04  fof(f134,plain,(
% 5.09/1.04    l1_pre_topc(sK0) | ~spl3_4),
% 5.09/1.04    inference(avatar_component_clause,[],[f132])).
% 5.09/1.04  fof(f132,plain,(
% 5.09/1.04    spl3_4 <=> l1_pre_topc(sK0)),
% 5.09/1.04    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 5.09/1.04  fof(f4707,plain,(
% 5.09/1.04    ~l1_pre_topc(sK0) | (~spl3_3 | spl3_104 | ~spl3_177)),
% 5.09/1.04    inference(subsumption_resolution,[],[f4706,f129])).
% 5.09/1.04  fof(f129,plain,(
% 5.09/1.04    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_3),
% 5.09/1.04    inference(avatar_component_clause,[],[f127])).
% 5.09/1.04  fof(f127,plain,(
% 5.09/1.04    spl3_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 5.09/1.04    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 5.09/1.04  fof(f4706,plain,(
% 5.09/1.04    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (spl3_104 | ~spl3_177)),
% 5.09/1.04    inference(subsumption_resolution,[],[f4685,f2249])).
% 5.09/1.04  fof(f2249,plain,(
% 5.09/1.04    sK1 != k1_tops_1(sK0,sK1) | spl3_104),
% 5.09/1.04    inference(avatar_component_clause,[],[f2248])).
% 5.09/1.04  fof(f2248,plain,(
% 5.09/1.04    spl3_104 <=> sK1 = k1_tops_1(sK0,sK1)),
% 5.09/1.04    introduced(avatar_definition,[new_symbols(naming,[spl3_104])])).
% 5.09/1.04  fof(f4685,plain,(
% 5.09/1.04    sK1 = k1_tops_1(sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl3_177),
% 5.09/1.04    inference(superposition,[],[f302,f4637])).
% 5.09/1.04  fof(f4637,plain,(
% 5.09/1.04    sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl3_177),
% 5.09/1.04    inference(avatar_component_clause,[],[f4635])).
% 5.09/1.04  fof(f4635,plain,(
% 5.09/1.04    spl3_177 <=> sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 5.09/1.04    introduced(avatar_definition,[new_symbols(naming,[spl3_177])])).
% 5.09/1.04  fof(f302,plain,(
% 5.09/1.04    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 5.09/1.04    inference(duplicate_literal_removal,[],[f301])).
% 5.09/1.04  fof(f301,plain,(
% 5.09/1.04    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 5.09/1.04    inference(superposition,[],[f78,f89])).
% 5.09/1.04  fof(f89,plain,(
% 5.09/1.04    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 5.09/1.04    inference(cnf_transformation,[],[f44])).
% 5.09/1.04  fof(f44,plain,(
% 5.09/1.04    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 5.09/1.04    inference(ennf_transformation,[],[f33])).
% 5.09/1.04  fof(f33,axiom,(
% 5.09/1.04    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 5.09/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).
% 5.09/1.04  fof(f78,plain,(
% 5.09/1.04    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 5.09/1.04    inference(cnf_transformation,[],[f38])).
% 5.09/1.04  fof(f38,plain,(
% 5.09/1.04    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 5.09/1.04    inference(ennf_transformation,[],[f23])).
% 5.09/1.04  fof(f23,axiom,(
% 5.09/1.04    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 5.09/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 5.09/1.04  fof(f4638,plain,(
% 5.09/1.04    spl3_129 | spl3_177 | ~spl3_26 | ~spl3_34),
% 5.09/1.04    inference(avatar_split_clause,[],[f4633,f732,f695,f4635,f3286])).
% 5.09/1.04  fof(f695,plain,(
% 5.09/1.04    spl3_26 <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))),
% 5.09/1.04    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 5.09/1.04  fof(f732,plain,(
% 5.09/1.04    spl3_34 <=> sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))),
% 5.09/1.04    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).
% 5.09/1.04  fof(f4633,plain,(
% 5.09/1.04    ( ! [X18] : (sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~m1_subset_1(X18,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))) ) | (~spl3_26 | ~spl3_34)),
% 5.09/1.04    inference(subsumption_resolution,[],[f4607,f697])).
% 5.09/1.04  fof(f697,plain,(
% 5.09/1.04    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~spl3_26),
% 5.09/1.04    inference(avatar_component_clause,[],[f695])).
% 5.09/1.04  fof(f4607,plain,(
% 5.09/1.04    ( ! [X18] : (sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~m1_subset_1(X18,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))) ) | ~spl3_34),
% 5.09/1.04    inference(superposition,[],[f862,f734])).
% 5.09/1.04  fof(f734,plain,(
% 5.09/1.04    sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) | ~spl3_34),
% 5.09/1.04    inference(avatar_component_clause,[],[f732])).
% 5.09/1.04  fof(f862,plain,(
% 5.09/1.04    ( ! [X4,X2,X3] : (k3_subset_1(X2,X3) = k4_xboole_0(k3_subset_1(X2,X3),X3) | ~m1_subset_1(X3,k1_zfmisc_1(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(X2))) )),
% 5.09/1.04    inference(subsumption_resolution,[],[f857,f96])).
% 5.09/1.04  fof(f96,plain,(
% 5.09/1.04    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 5.09/1.04    inference(cnf_transformation,[],[f52])).
% 5.09/1.04  fof(f52,plain,(
% 5.09/1.04    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 5.09/1.04    inference(ennf_transformation,[],[f15])).
% 5.09/1.04  fof(f15,axiom,(
% 5.09/1.04    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 5.09/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 5.09/1.04  fof(f857,plain,(
% 5.09/1.04    ( ! [X4,X2,X3] : (k3_subset_1(X2,X3) = k4_xboole_0(k3_subset_1(X2,X3),X3) | ~m1_subset_1(X3,k1_zfmisc_1(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(X2)) | ~m1_subset_1(k3_subset_1(X2,X3),k1_zfmisc_1(X2))) )),
% 5.09/1.04    inference(superposition,[],[f330,f78])).
% 5.09/1.04  fof(f330,plain,(
% 5.09/1.04    ( ! [X4,X5,X3] : (k3_subset_1(X3,X4) = k7_subset_1(X3,k3_subset_1(X3,X4),X4) | ~m1_subset_1(X4,k1_zfmisc_1(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(X3))) )),
% 5.09/1.04    inference(subsumption_resolution,[],[f326,f96])).
% 5.09/1.04  fof(f326,plain,(
% 5.09/1.04    ( ! [X4,X5,X3] : (k3_subset_1(X3,X4) = k7_subset_1(X3,k3_subset_1(X3,X4),X4) | ~m1_subset_1(X4,k1_zfmisc_1(X3)) | ~m1_subset_1(k3_subset_1(X3,X4),k1_zfmisc_1(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(X3))) )),
% 5.09/1.04    inference(superposition,[],[f87,f108])).
% 5.09/1.04  fof(f108,plain,(
% 5.09/1.04    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X1) = X1 | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 5.09/1.04    inference(cnf_transformation,[],[f58])).
% 5.09/1.04  fof(f58,plain,(
% 5.09/1.04    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X1) = X1 | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 5.09/1.04    inference(ennf_transformation,[],[f19])).
% 5.09/1.04  fof(f19,axiom,(
% 5.09/1.04    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X1) = X1)),
% 5.09/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k9_subset_1)).
% 5.09/1.04  fof(f87,plain,(
% 5.09/1.04    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 5.09/1.04    inference(cnf_transformation,[],[f42])).
% 5.09/1.04  fof(f42,plain,(
% 5.09/1.04    ! [X0,X1] : (! [X2] : (k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 5.09/1.04    inference(ennf_transformation,[],[f24])).
% 5.09/1.04  fof(f24,axiom,(
% 5.09/1.04    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))))),
% 5.09/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_subset_1)).
% 5.09/1.04  fof(f3295,plain,(
% 5.09/1.04    spl3_93 | ~spl3_3 | ~spl3_4),
% 5.09/1.04    inference(avatar_split_clause,[],[f3294,f132,f127,f2149])).
% 5.09/1.04  fof(f2149,plain,(
% 5.09/1.04    spl3_93 <=> r1_tarski(sK1,k2_pre_topc(sK0,sK1))),
% 5.09/1.04    introduced(avatar_definition,[new_symbols(naming,[spl3_93])])).
% 5.09/1.04  fof(f3294,plain,(
% 5.09/1.04    r1_tarski(sK1,k2_pre_topc(sK0,sK1)) | (~spl3_3 | ~spl3_4)),
% 5.09/1.04    inference(subsumption_resolution,[],[f3136,f134])).
% 5.09/1.04  fof(f3136,plain,(
% 5.09/1.04    r1_tarski(sK1,k2_pre_topc(sK0,sK1)) | ~l1_pre_topc(sK0) | ~spl3_3),
% 5.09/1.04    inference(resolution,[],[f781,f129])).
% 5.09/1.04  fof(f781,plain,(
% 5.09/1.04    ( ! [X4,X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4))) | r1_tarski(X3,k2_pre_topc(X4,X3)) | ~l1_pre_topc(X4)) )),
% 5.09/1.04    inference(superposition,[],[f104,f315])).
% 5.09/1.04  fof(f315,plain,(
% 5.09/1.04    ( ! [X2,X3] : (k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2)) )),
% 5.09/1.04    inference(subsumption_resolution,[],[f312,f91])).
% 5.09/1.04  fof(f91,plain,(
% 5.09/1.04    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 5.09/1.04    inference(cnf_transformation,[],[f47])).
% 5.09/1.04  fof(f47,plain,(
% 5.09/1.04    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 5.09/1.04    inference(flattening,[],[f46])).
% 5.09/1.04  fof(f46,plain,(
% 5.09/1.04    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 5.09/1.04    inference(ennf_transformation,[],[f27])).
% 5.09/1.04  fof(f27,axiom,(
% 5.09/1.04    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 5.09/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).
% 5.09/1.04  fof(f312,plain,(
% 5.09/1.04    ( ! [X2,X3] : (k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2) | ~m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))) )),
% 5.09/1.04    inference(duplicate_literal_removal,[],[f307])).
% 5.09/1.04  fof(f307,plain,(
% 5.09/1.04    ( ! [X2,X3] : (k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2) | ~m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) )),
% 5.09/1.04    inference(superposition,[],[f90,f109])).
% 5.09/1.04  fof(f109,plain,(
% 5.09/1.04    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 5.09/1.04    inference(cnf_transformation,[],[f60])).
% 5.09/1.04  fof(f60,plain,(
% 5.09/1.04    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 5.09/1.04    inference(flattening,[],[f59])).
% 5.09/1.04  fof(f59,plain,(
% 5.09/1.04    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 5.09/1.04    inference(ennf_transformation,[],[f21])).
% 5.09/1.04  fof(f21,axiom,(
% 5.09/1.04    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 5.09/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 5.09/1.04  fof(f90,plain,(
% 5.09/1.04    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 5.09/1.04    inference(cnf_transformation,[],[f45])).
% 5.09/1.04  fof(f45,plain,(
% 5.09/1.04    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 5.09/1.04    inference(ennf_transformation,[],[f32])).
% 5.09/1.04  fof(f32,axiom,(
% 5.09/1.04    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 5.09/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).
% 5.09/1.04  fof(f104,plain,(
% 5.09/1.04    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 5.09/1.04    inference(cnf_transformation,[],[f12])).
% 5.09/1.04  fof(f12,axiom,(
% 5.09/1.04    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 5.09/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 5.09/1.04  fof(f3221,plain,(
% 5.09/1.04    spl3_26 | ~spl3_11),
% 5.09/1.04    inference(avatar_split_clause,[],[f3207,f255,f695])).
% 5.09/1.04  fof(f255,plain,(
% 5.09/1.04    spl3_11 <=> k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)),
% 5.09/1.04    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 5.09/1.04  fof(f3207,plain,(
% 5.09/1.04    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~spl3_11),
% 5.09/1.04    inference(superposition,[],[f153,f257])).
% 5.09/1.04  fof(f257,plain,(
% 5.09/1.04    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~spl3_11),
% 5.09/1.04    inference(avatar_component_clause,[],[f255])).
% 5.09/1.04  fof(f3203,plain,(
% 5.09/1.04    spl3_11 | ~spl3_2 | ~spl3_10),
% 5.09/1.04    inference(avatar_split_clause,[],[f3202,f251,f121,f255])).
% 5.09/1.04  fof(f121,plain,(
% 5.09/1.04    spl3_2 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)),
% 5.09/1.04    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 5.09/1.04  fof(f251,plain,(
% 5.09/1.04    spl3_10 <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 5.09/1.04    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 5.09/1.04  fof(f3202,plain,(
% 5.09/1.04    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | (~spl3_2 | ~spl3_10)),
% 5.09/1.04    inference(subsumption_resolution,[],[f3199,f252])).
% 5.09/1.04  fof(f252,plain,(
% 5.09/1.04    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_10),
% 5.09/1.04    inference(avatar_component_clause,[],[f251])).
% 5.09/1.04  fof(f3199,plain,(
% 5.09/1.04    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_2),
% 5.09/1.04    inference(superposition,[],[f78,f122])).
% 5.09/1.04  fof(f122,plain,(
% 5.09/1.04    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~spl3_2),
% 5.09/1.04    inference(avatar_component_clause,[],[f121])).
% 5.09/1.04  fof(f3194,plain,(
% 5.09/1.04    ~spl3_89 | spl3_104 | ~spl3_103),
% 5.09/1.04    inference(avatar_split_clause,[],[f3122,f2244,f2248,f2090])).
% 5.09/1.04  fof(f2090,plain,(
% 5.09/1.04    spl3_89 <=> r1_tarski(sK1,k1_tops_1(sK0,sK1))),
% 5.09/1.04    introduced(avatar_definition,[new_symbols(naming,[spl3_89])])).
% 5.09/1.04  fof(f2244,plain,(
% 5.09/1.04    spl3_103 <=> r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 5.09/1.04    introduced(avatar_definition,[new_symbols(naming,[spl3_103])])).
% 5.09/1.04  fof(f3122,plain,(
% 5.09/1.04    sK1 = k1_tops_1(sK0,sK1) | ~r1_tarski(sK1,k1_tops_1(sK0,sK1)) | ~spl3_103),
% 5.09/1.04    inference(resolution,[],[f2245,f81])).
% 5.09/1.04  fof(f81,plain,(
% 5.09/1.04    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 5.09/1.04    inference(cnf_transformation,[],[f69])).
% 5.09/1.04  fof(f69,plain,(
% 5.09/1.04    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 5.09/1.04    inference(flattening,[],[f68])).
% 5.09/1.04  fof(f68,plain,(
% 5.09/1.04    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 5.09/1.04    inference(nnf_transformation,[],[f2])).
% 5.09/1.04  fof(f2,axiom,(
% 5.09/1.04    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 5.09/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 5.09/1.04  fof(f2245,plain,(
% 5.09/1.04    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~spl3_103),
% 5.09/1.04    inference(avatar_component_clause,[],[f2244])).
% 5.09/1.04  fof(f3189,plain,(
% 5.09/1.04    ~spl3_3 | ~spl3_4 | spl3_11 | ~spl3_104),
% 5.09/1.04    inference(avatar_contradiction_clause,[],[f3188])).
% 5.09/1.04  fof(f3188,plain,(
% 5.09/1.04    $false | (~spl3_3 | ~spl3_4 | spl3_11 | ~spl3_104)),
% 5.09/1.04    inference(subsumption_resolution,[],[f3187,f134])).
% 5.09/1.04  fof(f3187,plain,(
% 5.09/1.04    ~l1_pre_topc(sK0) | (~spl3_3 | spl3_11 | ~spl3_104)),
% 5.09/1.04    inference(subsumption_resolution,[],[f3186,f129])).
% 5.09/1.04  fof(f3186,plain,(
% 5.09/1.04    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (spl3_11 | ~spl3_104)),
% 5.09/1.04    inference(subsumption_resolution,[],[f3177,f256])).
% 5.09/1.04  fof(f256,plain,(
% 5.09/1.04    k2_tops_1(sK0,sK1) != k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | spl3_11),
% 5.09/1.04    inference(avatar_component_clause,[],[f255])).
% 5.09/1.04  fof(f3177,plain,(
% 5.09/1.04    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl3_104),
% 5.09/1.04    inference(superposition,[],[f1009,f2250])).
% 5.09/1.04  fof(f2250,plain,(
% 5.09/1.04    sK1 = k1_tops_1(sK0,sK1) | ~spl3_104),
% 5.09/1.04    inference(avatar_component_clause,[],[f2248])).
% 5.09/1.04  fof(f1009,plain,(
% 5.09/1.04    ( ! [X2,X3] : (k2_tops_1(X2,X3) = k4_xboole_0(k2_pre_topc(X2,X3),k1_tops_1(X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2)) )),
% 5.09/1.04    inference(subsumption_resolution,[],[f334,f317])).
% 5.09/1.04  fof(f317,plain,(
% 5.09/1.04    ( ! [X2,X3] : (m1_subset_1(k2_pre_topc(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2)) )),
% 5.09/1.04    inference(subsumption_resolution,[],[f310,f91])).
% 5.09/1.04  fof(f310,plain,(
% 5.09/1.04    ( ! [X2,X3] : (m1_subset_1(k2_pre_topc(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) | ~m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2)) )),
% 5.09/1.04    inference(duplicate_literal_removal,[],[f309])).
% 5.09/1.04  fof(f309,plain,(
% 5.09/1.04    ( ! [X2,X3] : (m1_subset_1(k2_pre_topc(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) | ~m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2)) )),
% 5.09/1.04    inference(superposition,[],[f110,f90])).
% 5.09/1.04  fof(f334,plain,(
% 5.09/1.04    ( ! [X2,X3] : (k2_tops_1(X2,X3) = k4_xboole_0(k2_pre_topc(X2,X3),k1_tops_1(X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2) | ~m1_subset_1(k2_pre_topc(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))) )),
% 5.09/1.04    inference(superposition,[],[f88,f78])).
% 5.09/1.04  fof(f88,plain,(
% 5.09/1.04    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 5.09/1.04    inference(cnf_transformation,[],[f43])).
% 5.09/1.04  fof(f43,plain,(
% 5.09/1.04    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 5.09/1.04    inference(ennf_transformation,[],[f29])).
% 5.09/1.04  fof(f29,axiom,(
% 5.09/1.04    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 5.09/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).
% 5.09/1.04  fof(f3115,plain,(
% 5.09/1.04    spl3_103 | ~spl3_3 | ~spl3_4),
% 5.09/1.04    inference(avatar_split_clause,[],[f3114,f132,f127,f2244])).
% 5.09/1.04  fof(f3114,plain,(
% 5.09/1.04    r1_tarski(k1_tops_1(sK0,sK1),sK1) | (~spl3_3 | ~spl3_4)),
% 5.09/1.04    inference(subsumption_resolution,[],[f3105,f134])).
% 5.09/1.04  fof(f3105,plain,(
% 5.09/1.04    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~l1_pre_topc(sK0) | ~spl3_3),
% 5.09/1.04    inference(resolution,[],[f756,f129])).
% 5.09/1.04  fof(f756,plain,(
% 5.09/1.04    ( ! [X6,X7] : (~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X7))) | r1_tarski(k1_tops_1(X7,X6),X6) | ~l1_pre_topc(X7)) )),
% 5.09/1.04    inference(superposition,[],[f160,f302])).
% 5.09/1.04  fof(f160,plain,(
% 5.09/1.04    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 5.09/1.04    inference(resolution,[],[f153,f94])).
% 5.09/1.04  fof(f94,plain,(
% 5.09/1.04    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 5.09/1.04    inference(cnf_transformation,[],[f70])).
% 5.09/1.04  fof(f70,plain,(
% 5.09/1.04    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 5.09/1.04    inference(nnf_transformation,[],[f26])).
% 5.09/1.04  fof(f26,axiom,(
% 5.09/1.04    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 5.09/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 5.09/1.04  fof(f2240,plain,(
% 5.09/1.04    ~spl3_11 | spl3_2 | ~spl3_10),
% 5.09/1.04    inference(avatar_split_clause,[],[f2239,f251,f121,f255])).
% 5.09/1.04  fof(f2239,plain,(
% 5.09/1.04    k2_tops_1(sK0,sK1) != k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | (spl3_2 | ~spl3_10)),
% 5.09/1.04    inference(subsumption_resolution,[],[f2238,f252])).
% 5.09/1.04  fof(f2238,plain,(
% 5.09/1.04    k2_tops_1(sK0,sK1) != k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_2),
% 5.09/1.04    inference(superposition,[],[f123,f78])).
% 5.09/1.04  fof(f123,plain,(
% 5.09/1.04    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | spl3_2),
% 5.09/1.04    inference(avatar_component_clause,[],[f121])).
% 5.09/1.04  fof(f2152,plain,(
% 5.09/1.04    ~spl3_93 | spl3_33),
% 5.09/1.04    inference(avatar_split_clause,[],[f2147,f728,f2149])).
% 5.09/1.04  fof(f728,plain,(
% 5.09/1.04    spl3_33 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))),
% 5.09/1.04    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).
% 5.09/1.04  fof(f2147,plain,(
% 5.09/1.04    ~r1_tarski(sK1,k2_pre_topc(sK0,sK1)) | spl3_33),
% 5.09/1.04    inference(resolution,[],[f730,f95])).
% 5.09/1.04  fof(f95,plain,(
% 5.09/1.04    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 5.09/1.04    inference(cnf_transformation,[],[f70])).
% 5.09/1.04  fof(f730,plain,(
% 5.09/1.04    ~m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | spl3_33),
% 5.09/1.04    inference(avatar_component_clause,[],[f728])).
% 5.09/1.04  fof(f2135,plain,(
% 5.09/1.04    ~spl3_33 | spl3_34 | ~spl3_11),
% 5.09/1.04    inference(avatar_split_clause,[],[f2115,f255,f732,f728])).
% 5.09/1.04  fof(f2115,plain,(
% 5.09/1.04    sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~spl3_11),
% 5.09/1.04    inference(superposition,[],[f238,f257])).
% 5.09/1.04  fof(f238,plain,(
% 5.09/1.04    ( ! [X0,X1] : (k3_subset_1(X0,k4_xboole_0(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 5.09/1.04    inference(duplicate_literal_removal,[],[f234])).
% 5.09/1.04  fof(f234,plain,(
% 5.09/1.04    ( ! [X0,X1] : (k3_subset_1(X0,k4_xboole_0(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 5.09/1.04    inference(superposition,[],[f82,f83])).
% 5.09/1.04  fof(f83,plain,(
% 5.09/1.04    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 5.09/1.04    inference(cnf_transformation,[],[f40])).
% 5.09/1.04  fof(f40,plain,(
% 5.09/1.04    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 5.09/1.04    inference(ennf_transformation,[],[f14])).
% 5.09/1.04  fof(f14,axiom,(
% 5.09/1.04    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 5.09/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 5.09/1.04  fof(f82,plain,(
% 5.09/1.04    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 5.09/1.04    inference(cnf_transformation,[],[f39])).
% 5.09/1.04  fof(f39,plain,(
% 5.09/1.04    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 5.09/1.04    inference(ennf_transformation,[],[f20])).
% 5.09/1.04  fof(f20,axiom,(
% 5.09/1.04    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 5.09/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 5.09/1.04  fof(f2096,plain,(
% 5.09/1.04    spl3_89 | ~spl3_1 | ~spl3_3 | ~spl3_4),
% 5.09/1.04    inference(avatar_split_clause,[],[f2095,f132,f127,f117,f2090])).
% 5.09/1.04  fof(f117,plain,(
% 5.09/1.04    spl3_1 <=> v3_pre_topc(sK1,sK0)),
% 5.09/1.04    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 5.09/1.04  fof(f2095,plain,(
% 5.09/1.04    ~v3_pre_topc(sK1,sK0) | r1_tarski(sK1,k1_tops_1(sK0,sK1)) | (~spl3_3 | ~spl3_4)),
% 5.09/1.04    inference(subsumption_resolution,[],[f2078,f114])).
% 5.09/1.04  fof(f114,plain,(
% 5.09/1.04    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 5.09/1.04    inference(equality_resolution,[],[f80])).
% 5.09/1.04  fof(f80,plain,(
% 5.09/1.04    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 5.09/1.04    inference(cnf_transformation,[],[f69])).
% 5.09/1.04  fof(f2078,plain,(
% 5.09/1.04    ~v3_pre_topc(sK1,sK0) | r1_tarski(sK1,k1_tops_1(sK0,sK1)) | ~r1_tarski(sK1,sK1) | (~spl3_3 | ~spl3_4)),
% 5.09/1.04    inference(resolution,[],[f2046,f129])).
% 5.09/1.04  fof(f2046,plain,(
% 5.09/1.04    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X1,sK0) | r1_tarski(X1,k1_tops_1(sK0,sK1)) | ~r1_tarski(X1,sK1)) ) | (~spl3_3 | ~spl3_4)),
% 5.09/1.04    inference(subsumption_resolution,[],[f2040,f134])).
% 5.09/1.04  fof(f2040,plain,(
% 5.09/1.04    ( ! [X1] : (~r1_tarski(X1,sK1) | ~v3_pre_topc(X1,sK0) | r1_tarski(X1,k1_tops_1(sK0,sK1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) ) | ~spl3_3),
% 5.09/1.04    inference(resolution,[],[f129,f93])).
% 5.09/1.04  fof(f93,plain,(
% 5.09/1.04    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | r1_tarski(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 5.09/1.04    inference(cnf_transformation,[],[f51])).
% 5.09/1.04  fof(f51,plain,(
% 5.09/1.04    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 5.09/1.04    inference(flattening,[],[f50])).
% 5.09/1.04  fof(f50,plain,(
% 5.09/1.04    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(X1,k1_tops_1(X0,X2)) | (~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 5.09/1.04    inference(ennf_transformation,[],[f30])).
% 5.09/1.04  fof(f30,axiom,(
% 5.09/1.04    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v3_pre_topc(X1,X0)) => r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 5.09/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_1)).
% 5.09/1.04  fof(f2049,plain,(
% 5.09/1.04    spl3_13 | ~spl3_3 | ~spl3_4 | ~spl3_5),
% 5.09/1.04    inference(avatar_split_clause,[],[f2048,f137,f132,f127,f278])).
% 5.09/1.04  fof(f278,plain,(
% 5.09/1.04    spl3_13 <=> v3_pre_topc(k1_tops_1(sK0,sK1),sK0)),
% 5.09/1.04    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 5.09/1.04  fof(f137,plain,(
% 5.09/1.04    spl3_5 <=> v2_pre_topc(sK0)),
% 5.09/1.04    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 5.09/1.04  fof(f2048,plain,(
% 5.09/1.04    v3_pre_topc(k1_tops_1(sK0,sK1),sK0) | (~spl3_3 | ~spl3_4 | ~spl3_5)),
% 5.09/1.04    inference(subsumption_resolution,[],[f2047,f139])).
% 5.09/1.04  fof(f139,plain,(
% 5.09/1.04    v2_pre_topc(sK0) | ~spl3_5),
% 5.09/1.04    inference(avatar_component_clause,[],[f137])).
% 5.09/1.04  fof(f2047,plain,(
% 5.09/1.04    v3_pre_topc(k1_tops_1(sK0,sK1),sK0) | ~v2_pre_topc(sK0) | (~spl3_3 | ~spl3_4)),
% 5.09/1.04    inference(subsumption_resolution,[],[f2041,f134])).
% 5.09/1.04  fof(f2041,plain,(
% 5.09/1.04    v3_pre_topc(k1_tops_1(sK0,sK1),sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~spl3_3),
% 5.09/1.04    inference(resolution,[],[f129,f92])).
% 5.09/1.04  fof(f92,plain,(
% 5.09/1.04    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(k1_tops_1(X0,X1),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 5.09/1.04    inference(cnf_transformation,[],[f49])).
% 5.09/1.04  fof(f49,plain,(
% 5.09/1.04    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 5.09/1.04    inference(flattening,[],[f48])).
% 5.09/1.04  fof(f48,plain,(
% 5.09/1.04    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 5.09/1.04    inference(ennf_transformation,[],[f28])).
% 5.09/1.04  fof(f28,axiom,(
% 5.09/1.04    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 5.09/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).
% 5.09/1.04  fof(f647,plain,(
% 5.09/1.04    ~spl3_3 | ~spl3_4 | spl3_10),
% 5.09/1.04    inference(avatar_contradiction_clause,[],[f646])).
% 5.09/1.04  fof(f646,plain,(
% 5.09/1.04    $false | (~spl3_3 | ~spl3_4 | spl3_10)),
% 5.09/1.04    inference(subsumption_resolution,[],[f645,f134])).
% 5.09/1.04  fof(f645,plain,(
% 5.09/1.04    ~l1_pre_topc(sK0) | (~spl3_3 | spl3_10)),
% 5.09/1.04    inference(subsumption_resolution,[],[f638,f129])).
% 5.09/1.04  fof(f638,plain,(
% 5.09/1.04    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl3_10),
% 5.09/1.04    inference(resolution,[],[f317,f253])).
% 5.09/1.04  fof(f253,plain,(
% 5.09/1.04    ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_10),
% 5.09/1.04    inference(avatar_component_clause,[],[f251])).
% 5.09/1.04  fof(f140,plain,(
% 5.09/1.04    spl3_5),
% 5.09/1.04    inference(avatar_split_clause,[],[f73,f137])).
% 5.09/1.04  fof(f73,plain,(
% 5.09/1.04    v2_pre_topc(sK0)),
% 5.09/1.04    inference(cnf_transformation,[],[f67])).
% 5.09/1.04  fof(f67,plain,(
% 5.09/1.04    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 5.09/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f64,f66,f65])).
% 5.09/1.04  fof(f65,plain,(
% 5.09/1.04    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | ~v3_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 5.09/1.04    introduced(choice_axiom,[])).
% 5.09/1.04  fof(f66,plain,(
% 5.09/1.04    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | ~v3_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 5.09/1.04    introduced(choice_axiom,[])).
% 5.09/1.04  fof(f64,plain,(
% 5.09/1.04    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 5.09/1.04    inference(flattening,[],[f63])).
% 5.09/1.04  fof(f63,plain,(
% 5.09/1.04    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 5.09/1.04    inference(nnf_transformation,[],[f37])).
% 5.09/1.04  fof(f37,plain,(
% 5.09/1.04    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 5.09/1.04    inference(flattening,[],[f36])).
% 5.09/1.04  fof(f36,plain,(
% 5.09/1.04    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 5.09/1.04    inference(ennf_transformation,[],[f35])).
% 5.09/1.04  fof(f35,negated_conjecture,(
% 5.09/1.04    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 5.09/1.04    inference(negated_conjecture,[],[f34])).
% 5.09/1.04  fof(f34,conjecture,(
% 5.09/1.04    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 5.09/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tops_1)).
% 5.09/1.04  fof(f135,plain,(
% 5.09/1.04    spl3_4),
% 5.09/1.04    inference(avatar_split_clause,[],[f74,f132])).
% 5.09/1.04  fof(f74,plain,(
% 5.09/1.04    l1_pre_topc(sK0)),
% 5.09/1.04    inference(cnf_transformation,[],[f67])).
% 5.09/1.04  fof(f130,plain,(
% 5.09/1.04    spl3_3),
% 5.09/1.04    inference(avatar_split_clause,[],[f75,f127])).
% 5.09/1.04  fof(f75,plain,(
% 5.09/1.04    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 5.09/1.04    inference(cnf_transformation,[],[f67])).
% 5.09/1.04  fof(f125,plain,(
% 5.09/1.04    spl3_1 | spl3_2),
% 5.09/1.04    inference(avatar_split_clause,[],[f76,f121,f117])).
% 5.09/1.04  fof(f76,plain,(
% 5.09/1.04    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)),
% 5.09/1.04    inference(cnf_transformation,[],[f67])).
% 5.09/1.04  fof(f124,plain,(
% 5.09/1.04    ~spl3_1 | ~spl3_2),
% 5.09/1.04    inference(avatar_split_clause,[],[f77,f121,f117])).
% 5.09/1.04  fof(f77,plain,(
% 5.09/1.04    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)),
% 5.09/1.04    inference(cnf_transformation,[],[f67])).
% 5.09/1.04  % SZS output end Proof for theBenchmark
% 5.09/1.04  % (23286)------------------------------
% 5.09/1.04  % (23286)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.09/1.04  % (23286)Termination reason: Refutation
% 5.09/1.04  
% 5.09/1.04  % (23286)Memory used [KB]: 11513
% 5.09/1.04  % (23286)Time elapsed: 0.634 s
% 5.09/1.04  % (23286)------------------------------
% 5.09/1.04  % (23286)------------------------------
% 5.09/1.04  % (23261)Success in time 0.682 s
%------------------------------------------------------------------------------
