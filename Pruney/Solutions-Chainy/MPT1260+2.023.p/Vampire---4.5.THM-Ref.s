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
% DateTime   : Thu Dec  3 13:11:36 EST 2020

% Result     : Theorem 8.67s
% Output     : Refutation 8.67s
% Verified   : 
% Statistics : Number of formulae       :  195 ( 366 expanded)
%              Number of leaves         :   43 ( 131 expanded)
%              Depth                    :   13
%              Number of atoms          :  575 (1140 expanded)
%              Number of equality atoms :   97 ( 221 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6454,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f126,f127,f132,f137,f142,f281,f674,f782,f811,f2249,f2288,f2291,f2306,f4371,f5777,f6087,f6111,f6118,f6392,f6447,f6453])).

fof(f6453,plain,
    ( sK1 != k1_tops_1(sK0,sK1)
    | v3_pre_topc(sK1,sK0)
    | ~ v3_pre_topc(k1_tops_1(sK0,sK1),sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f6447,plain,(
    ~ spl3_106 ),
    inference(avatar_contradiction_clause,[],[f6416])).

fof(f6416,plain,
    ( $false
    | ~ spl3_106 ),
    inference(unit_resulting_resolution,[],[f170,f98,f2560,f112])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f62])).

fof(f62,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).

fof(f2560,plain,
    ( ! [X2] : ~ m1_subset_1(X2,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl3_106 ),
    inference(avatar_component_clause,[],[f2559])).

fof(f2559,plain,
    ( spl3_106
  <=> ! [X2] : ~ m1_subset_1(X2,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_106])])).

fof(f98,plain,(
    ! [X0] : m1_subset_1(sK2(X0),X0) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0] : m1_subset_1(sK2(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f19,f72])).

fof(f72,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f19,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(f170,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(superposition,[],[f168,f104])).

fof(f104,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f168,plain,(
    ! [X0,X1] : m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0)) ),
    inference(backward_demodulation,[],[f113,f103])).

fof(f103,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f113,plain,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).

fof(f6392,plain,
    ( spl3_106
    | spl3_171
    | ~ spl3_41
    | ~ spl3_47 ),
    inference(avatar_split_clause,[],[f6391,f773,f745,f4063,f2559])).

fof(f4063,plain,
    ( spl3_171
  <=> sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_171])])).

fof(f745,plain,
    ( spl3_41
  <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).

fof(f773,plain,
    ( spl3_47
  <=> sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).

fof(f6391,plain,
    ( ! [X16] :
        ( sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) )
    | ~ spl3_41
    | ~ spl3_47 ),
    inference(subsumption_resolution,[],[f6364,f747])).

fof(f747,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl3_41 ),
    inference(avatar_component_clause,[],[f745])).

fof(f6364,plain,
    ( ! [X16] :
        ( sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
        | ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) )
    | ~ spl3_47 ),
    inference(superposition,[],[f872,f775])).

fof(f775,plain,
    ( sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))
    | ~ spl3_47 ),
    inference(avatar_component_clause,[],[f773])).

fof(f872,plain,(
    ! [X4,X2,X3] :
      ( k3_subset_1(X2,X3) = k4_xboole_0(k3_subset_1(X2,X3),X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
      | ~ m1_subset_1(X4,k1_zfmisc_1(X2)) ) ),
    inference(subsumption_resolution,[],[f867,f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f867,plain,(
    ! [X4,X2,X3] :
      ( k3_subset_1(X2,X3) = k4_xboole_0(k3_subset_1(X2,X3),X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
      | ~ m1_subset_1(X4,k1_zfmisc_1(X2))
      | ~ m1_subset_1(k3_subset_1(X2,X3),k1_zfmisc_1(X2)) ) ),
    inference(superposition,[],[f322,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f322,plain,(
    ! [X4,X5,X3] :
      ( k3_subset_1(X3,X4) = k7_subset_1(X3,k3_subset_1(X3,X4),X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(X3)) ) ),
    inference(subsumption_resolution,[],[f318,f97])).

fof(f318,plain,(
    ! [X4,X5,X3] :
      ( k3_subset_1(X3,X4) = k7_subset_1(X3,k3_subset_1(X3,X4),X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
      | ~ m1_subset_1(k3_subset_1(X3,X4),k1_zfmisc_1(X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(X3)) ) ),
    inference(superposition,[],[f88,f111])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k9_subset_1)).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_subset_1)).

fof(f6118,plain,
    ( spl3_47
    | ~ spl3_12
    | ~ spl3_46 ),
    inference(avatar_split_clause,[],[f6117,f769,f247,f773])).

fof(f247,plain,
    ( spl3_12
  <=> k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f769,plain,
    ( spl3_46
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).

fof(f6117,plain,
    ( sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))
    | ~ spl3_12
    | ~ spl3_46 ),
    inference(subsumption_resolution,[],[f6097,f770])).

fof(f770,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl3_46 ),
    inference(avatar_component_clause,[],[f769])).

fof(f6097,plain,
    ( sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl3_12 ),
    inference(superposition,[],[f237,f249])).

fof(f249,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f247])).

fof(f237,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k4_xboole_0(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f233])).

fof(f233,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k4_xboole_0(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(superposition,[],[f83,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f83,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f6111,plain,
    ( spl3_41
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f6092,f247,f745])).

fof(f6092,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl3_12 ),
    inference(superposition,[],[f168,f249])).

fof(f6087,plain,
    ( spl3_12
    | ~ spl3_2
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f6086,f243,f123,f247])).

fof(f123,plain,
    ( spl3_2
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f243,plain,
    ( spl3_11
  <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f6086,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ spl3_2
    | ~ spl3_11 ),
    inference(subsumption_resolution,[],[f6083,f244])).

fof(f244,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f243])).

fof(f6083,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_2 ),
    inference(superposition,[],[f79,f124])).

fof(f124,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f123])).

fof(f5777,plain,
    ( ~ spl3_3
    | ~ spl3_4
    | spl3_85
    | ~ spl3_171 ),
    inference(avatar_contradiction_clause,[],[f5776])).

fof(f5776,plain,
    ( $false
    | ~ spl3_3
    | ~ spl3_4
    | spl3_85
    | ~ spl3_171 ),
    inference(subsumption_resolution,[],[f5775,f136])).

fof(f136,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f134])).

fof(f134,plain,
    ( spl3_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f5775,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl3_3
    | spl3_85
    | ~ spl3_171 ),
    inference(subsumption_resolution,[],[f5774,f131])).

fof(f131,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f129])).

fof(f129,plain,
    ( spl3_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f5774,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl3_85
    | ~ spl3_171 ),
    inference(subsumption_resolution,[],[f5750,f2252])).

fof(f2252,plain,
    ( sK1 != k1_tops_1(sK0,sK1)
    | spl3_85 ),
    inference(avatar_component_clause,[],[f2251])).

fof(f2251,plain,
    ( spl3_85
  <=> sK1 = k1_tops_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_85])])).

fof(f5750,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_171 ),
    inference(superposition,[],[f294,f4065])).

fof(f4065,plain,
    ( sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl3_171 ),
    inference(avatar_component_clause,[],[f4063])).

fof(f294,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f293])).

fof(f293,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(superposition,[],[f79,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

fof(f4371,plain,
    ( spl3_49
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f4370,f134,f129,f808])).

fof(f808,plain,
    ( spl3_49
  <=> r1_tarski(sK1,k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_49])])).

fof(f4370,plain,
    ( r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f4365,f136])).

fof(f4365,plain,
    ( r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_3 ),
    inference(resolution,[],[f131,f828])).

fof(f828,plain,(
    ! [X4,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))
      | r1_tarski(X3,k2_pre_topc(X4,X3))
      | ~ l1_pre_topc(X4) ) ),
    inference(superposition,[],[f107,f312])).

fof(f312,plain,(
    ! [X2,X3] :
      ( k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2) ) ),
    inference(subsumption_resolution,[],[f309,f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(f309,plain,(
    ! [X2,X3] :
      ( k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2)
      | ~ m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) ) ),
    inference(duplicate_literal_removal,[],[f304])).

fof(f304,plain,(
    ! [X2,X3] :
      ( k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2)
      | ~ m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ) ),
    inference(superposition,[],[f91,f110])).

fof(f110,plain,(
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
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f91,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

fof(f107,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f2306,plain,
    ( ~ spl3_3
    | ~ spl3_4
    | spl3_12
    | ~ spl3_85 ),
    inference(avatar_contradiction_clause,[],[f2305])).

fof(f2305,plain,
    ( $false
    | ~ spl3_3
    | ~ spl3_4
    | spl3_12
    | ~ spl3_85 ),
    inference(subsumption_resolution,[],[f2304,f136])).

fof(f2304,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl3_3
    | spl3_12
    | ~ spl3_85 ),
    inference(subsumption_resolution,[],[f2303,f131])).

fof(f2303,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl3_12
    | ~ spl3_85 ),
    inference(subsumption_resolution,[],[f2299,f248])).

fof(f248,plain,
    ( k2_tops_1(sK0,sK1) != k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | spl3_12 ),
    inference(avatar_component_clause,[],[f247])).

fof(f2299,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_85 ),
    inference(superposition,[],[f1015,f2253])).

fof(f2253,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ spl3_85 ),
    inference(avatar_component_clause,[],[f2251])).

fof(f1015,plain,(
    ! [X2,X3] :
      ( k2_tops_1(X2,X3) = k4_xboole_0(k2_pre_topc(X2,X3),k1_tops_1(X2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2) ) ),
    inference(subsumption_resolution,[],[f324,f314])).

fof(f314,plain,(
    ! [X2,X3] :
      ( m1_subset_1(k2_pre_topc(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2) ) ),
    inference(subsumption_resolution,[],[f307,f92])).

fof(f307,plain,(
    ! [X2,X3] :
      ( m1_subset_1(k2_pre_topc(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2) ) ),
    inference(duplicate_literal_removal,[],[f306])).

fof(f306,plain,(
    ! [X2,X3] :
      ( m1_subset_1(k2_pre_topc(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2) ) ),
    inference(superposition,[],[f112,f91])).

fof(f324,plain,(
    ! [X2,X3] :
      ( k2_tops_1(X2,X3) = k4_xboole_0(k2_pre_topc(X2,X3),k1_tops_1(X2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2)
      | ~ m1_subset_1(k2_pre_topc(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) ) ),
    inference(superposition,[],[f89,f79])).

fof(f89,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

fof(f2291,plain,
    ( ~ spl3_20
    | spl3_85
    | ~ spl3_48 ),
    inference(avatar_split_clause,[],[f2290,f779,f2251,f443])).

fof(f443,plain,
    ( spl3_20
  <=> r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f779,plain,
    ( spl3_48
  <=> r1_tarski(sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_48])])).

fof(f2290,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl3_48 ),
    inference(resolution,[],[f781,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f69])).

fof(f69,plain,(
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

fof(f781,plain,
    ( r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | ~ spl3_48 ),
    inference(avatar_component_clause,[],[f779])).

fof(f2288,plain,
    ( ~ spl3_12
    | spl3_2
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f2287,f243,f123,f247])).

fof(f2287,plain,
    ( k2_tops_1(sK0,sK1) != k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | spl3_2
    | ~ spl3_11 ),
    inference(subsumption_resolution,[],[f2286,f244])).

fof(f2286,plain,
    ( k2_tops_1(sK0,sK1) != k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_2 ),
    inference(superposition,[],[f125,f79])).

fof(f125,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f123])).

fof(f2249,plain,
    ( spl3_20
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f2248,f134,f129,f443])).

fof(f2248,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f2239,f136])).

fof(f2239,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl3_3 ),
    inference(resolution,[],[f816,f131])).

fof(f816,plain,(
    ! [X6,X7] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X7)))
      | r1_tarski(k1_tops_1(X7,X6),X6)
      | ~ l1_pre_topc(X7) ) ),
    inference(superposition,[],[f169,f294])).

fof(f169,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(resolution,[],[f168,f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f811,plain,
    ( ~ spl3_49
    | spl3_46 ),
    inference(avatar_split_clause,[],[f806,f769,f808])).

fof(f806,plain,
    ( ~ r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | spl3_46 ),
    inference(resolution,[],[f771,f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f771,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | spl3_46 ),
    inference(avatar_component_clause,[],[f769])).

fof(f782,plain,
    ( spl3_48
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f777,f134,f129,f119,f779])).

fof(f119,plain,
    ( spl3_1
  <=> v3_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f777,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f354,f116])).

fof(f116,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f70])).

fof(f354,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | ~ r1_tarski(sK1,sK1)
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(resolution,[],[f341,f131])).

fof(f341,plain,
    ( ! [X18] :
        ( ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X18,sK0)
        | r1_tarski(X18,k1_tops_1(sK0,sK1))
        | ~ r1_tarski(X18,sK1) )
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f337,f136])).

fof(f337,plain,
    ( ! [X18] :
        ( ~ r1_tarski(X18,sK1)
        | ~ v3_pre_topc(X18,sK0)
        | r1_tarski(X18,k1_tops_1(sK0,sK1))
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl3_3 ),
    inference(resolution,[],[f94,f131])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X1,X2)
      | ~ v3_pre_topc(X1,X0)
      | r1_tarski(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f51])).

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
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
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

fof(f674,plain,
    ( ~ spl3_3
    | ~ spl3_4
    | spl3_11 ),
    inference(avatar_contradiction_clause,[],[f673])).

fof(f673,plain,
    ( $false
    | ~ spl3_3
    | ~ spl3_4
    | spl3_11 ),
    inference(subsumption_resolution,[],[f672,f136])).

fof(f672,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl3_3
    | spl3_11 ),
    inference(subsumption_resolution,[],[f665,f131])).

fof(f665,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl3_11 ),
    inference(resolution,[],[f314,f245])).

fof(f245,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_11 ),
    inference(avatar_component_clause,[],[f243])).

fof(f281,plain,
    ( spl3_15
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f276,f139,f134,f129,f278])).

fof(f278,plain,
    ( spl3_15
  <=> v3_pre_topc(k1_tops_1(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f139,plain,
    ( spl3_5
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f276,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f275,f141])).

fof(f141,plain,
    ( v2_pre_topc(sK0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f139])).

fof(f275,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f272,f136])).

fof(f272,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl3_3 ),
    inference(resolution,[],[f93,f131])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

fof(f142,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f74,f139])).

fof(f74,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,
    ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
      | ~ v3_pre_topc(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
      | v3_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f65,f67,f66])).

fof(f66,plain,
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

fof(f67,plain,
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

fof(f65,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f64])).

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
    inference(nnf_transformation,[],[f38])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    inference(negated_conjecture,[],[f35])).

fof(f35,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tops_1)).

fof(f137,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f75,f134])).

fof(f75,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f68])).

fof(f132,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f76,f129])).

fof(f76,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f68])).

fof(f127,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f77,f123,f119])).

fof(f77,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f68])).

fof(f126,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f78,f123,f119])).

fof(f78,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f68])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:22:16 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.51  % (31060)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.52  % (31057)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.52  % (31076)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.52  % (31064)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.52  % (31068)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.52  % (31059)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.53  % (31074)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.53  % (31063)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.54  % (31066)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.54  % (31083)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.55  % (31081)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.43/0.56  % (31075)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.43/0.56  % (31078)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.43/0.56  % (31079)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.43/0.56  % (31071)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.43/0.56  % (31056)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.43/0.56  % (31065)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.43/0.56  % (31067)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.43/0.56  % (31073)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.57/0.57  % (31058)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.57/0.57  % (31062)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.57/0.57  % (31082)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.57/0.57  % (31077)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.57/0.57  % (31069)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.57/0.58  % (31072)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.57/0.58  % (31085)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.57/0.58  % (31070)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.57/0.58  % (31061)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.57/0.59  % (31084)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.57/0.59  % (31080)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 3.68/0.84  % (31080)Time limit reached!
% 3.68/0.84  % (31080)------------------------------
% 3.68/0.84  % (31080)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.68/0.84  % (31080)Termination reason: Time limit
% 3.68/0.84  
% 3.68/0.84  % (31080)Memory used [KB]: 12153
% 3.68/0.84  % (31080)Time elapsed: 0.417 s
% 3.68/0.84  % (31080)------------------------------
% 3.68/0.84  % (31080)------------------------------
% 3.68/0.84  % (31058)Time limit reached!
% 3.68/0.84  % (31058)------------------------------
% 3.68/0.84  % (31058)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.68/0.84  % (31058)Termination reason: Time limit
% 3.68/0.84  
% 3.68/0.84  % (31058)Memory used [KB]: 6524
% 3.68/0.84  % (31058)Time elapsed: 0.426 s
% 3.68/0.84  % (31058)------------------------------
% 3.68/0.84  % (31058)------------------------------
% 3.89/0.92  % (31062)Time limit reached!
% 3.89/0.92  % (31062)------------------------------
% 3.89/0.92  % (31062)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.35/0.93  % (31062)Termination reason: Time limit
% 4.35/0.93  
% 4.35/0.93  % (31062)Memory used [KB]: 15223
% 4.35/0.93  % (31062)Time elapsed: 0.501 s
% 4.35/0.93  % (31062)------------------------------
% 4.35/0.93  % (31062)------------------------------
% 4.35/0.95  % (31070)Time limit reached!
% 4.35/0.95  % (31070)------------------------------
% 4.35/0.95  % (31070)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.35/0.95  % (31070)Termination reason: Time limit
% 4.35/0.95  % (31070)Termination phase: Saturation
% 4.35/0.95  
% 4.35/0.95  % (31070)Memory used [KB]: 4861
% 4.35/0.95  % (31070)Time elapsed: 0.507 s
% 4.35/0.95  % (31070)------------------------------
% 4.35/0.95  % (31070)------------------------------
% 4.56/0.96  % (31085)Time limit reached!
% 4.56/0.96  % (31085)------------------------------
% 4.56/0.96  % (31085)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.56/0.96  % (31085)Termination reason: Time limit
% 4.56/0.96  
% 4.56/0.96  % (31085)Memory used [KB]: 3454
% 4.56/0.96  % (31085)Time elapsed: 0.518 s
% 4.56/0.96  % (31085)------------------------------
% 4.56/0.96  % (31085)------------------------------
% 4.56/0.98  % (31088)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 4.56/1.01  % (31087)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 5.09/1.03  % (31089)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 5.09/1.04  % (31063)Time limit reached!
% 5.09/1.04  % (31063)------------------------------
% 5.09/1.04  % (31063)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.09/1.05  % (31063)Termination reason: Time limit
% 5.09/1.05  
% 5.09/1.05  % (31063)Memory used [KB]: 6012
% 5.09/1.05  % (31063)Time elapsed: 0.609 s
% 5.09/1.05  % (31063)------------------------------
% 5.09/1.05  % (31063)------------------------------
% 5.57/1.10  % (31090)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 5.57/1.12  % (31091)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 6.34/1.20  % (31092)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 6.75/1.24  % (31057)Time limit reached!
% 6.75/1.24  % (31057)------------------------------
% 6.75/1.24  % (31057)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.75/1.24  % (31057)Termination reason: Time limit
% 6.75/1.24  
% 6.75/1.24  % (31057)Memory used [KB]: 8187
% 6.75/1.24  % (31057)Time elapsed: 0.822 s
% 6.75/1.24  % (31057)------------------------------
% 6.75/1.24  % (31057)------------------------------
% 7.52/1.32  % (31059)Time limit reached!
% 7.52/1.32  % (31059)------------------------------
% 7.52/1.32  % (31059)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.52/1.33  % (31059)Termination reason: Time limit
% 7.52/1.33  % (31059)Termination phase: Saturation
% 7.52/1.33  
% 7.52/1.33  % (31059)Memory used [KB]: 7419
% 7.52/1.33  % (31059)Time elapsed: 0.900 s
% 7.52/1.33  % (31059)------------------------------
% 7.52/1.33  % (31059)------------------------------
% 7.91/1.38  % (31093)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 7.91/1.42  % (31083)Time limit reached!
% 7.91/1.42  % (31083)------------------------------
% 7.91/1.42  % (31083)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.91/1.42  % (31083)Termination reason: Time limit
% 7.91/1.42  % (31083)Termination phase: Saturation
% 7.91/1.42  
% 7.91/1.42  % (31083)Memory used [KB]: 13048
% 7.91/1.42  % (31083)Time elapsed: 1.0000 s
% 7.91/1.42  % (31083)------------------------------
% 7.91/1.42  % (31083)------------------------------
% 7.91/1.43  % (31068)Time limit reached!
% 7.91/1.43  % (31068)------------------------------
% 7.91/1.43  % (31068)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.91/1.44  % (31068)Termination reason: Time limit
% 7.91/1.44  
% 7.91/1.44  % (31068)Memory used [KB]: 18421
% 7.91/1.44  % (31068)Time elapsed: 1.023 s
% 7.91/1.44  % (31068)------------------------------
% 7.91/1.44  % (31068)------------------------------
% 8.48/1.46  % (31094)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 8.67/1.51  % (31077)Refutation found. Thanks to Tanya!
% 8.67/1.51  % SZS status Theorem for theBenchmark
% 8.67/1.51  % SZS output start Proof for theBenchmark
% 8.67/1.51  fof(f6454,plain,(
% 8.67/1.51    $false),
% 8.67/1.51    inference(avatar_sat_refutation,[],[f126,f127,f132,f137,f142,f281,f674,f782,f811,f2249,f2288,f2291,f2306,f4371,f5777,f6087,f6111,f6118,f6392,f6447,f6453])).
% 8.67/1.51  fof(f6453,plain,(
% 8.67/1.51    sK1 != k1_tops_1(sK0,sK1) | v3_pre_topc(sK1,sK0) | ~v3_pre_topc(k1_tops_1(sK0,sK1),sK0)),
% 8.67/1.51    introduced(theory_tautology_sat_conflict,[])).
% 8.67/1.51  fof(f6447,plain,(
% 8.67/1.51    ~spl3_106),
% 8.67/1.51    inference(avatar_contradiction_clause,[],[f6416])).
% 8.67/1.51  fof(f6416,plain,(
% 8.67/1.51    $false | ~spl3_106),
% 8.67/1.51    inference(unit_resulting_resolution,[],[f170,f98,f2560,f112])).
% 8.67/1.51  fof(f112,plain,(
% 8.67/1.51    ( ! [X2,X0,X1] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 8.67/1.51    inference(cnf_transformation,[],[f63])).
% 8.67/1.51  fof(f63,plain,(
% 8.67/1.51    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 8.67/1.51    inference(flattening,[],[f62])).
% 8.67/1.51  fof(f62,plain,(
% 8.67/1.51    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 8.67/1.51    inference(ennf_transformation,[],[f17])).
% 8.67/1.51  fof(f17,axiom,(
% 8.67/1.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 8.67/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).
% 8.67/1.51  fof(f2560,plain,(
% 8.67/1.51    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))) ) | ~spl3_106),
% 8.67/1.51    inference(avatar_component_clause,[],[f2559])).
% 8.67/1.51  fof(f2559,plain,(
% 8.67/1.51    spl3_106 <=> ! [X2] : ~m1_subset_1(X2,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))),
% 8.67/1.51    introduced(avatar_definition,[new_symbols(naming,[spl3_106])])).
% 8.67/1.51  fof(f98,plain,(
% 8.67/1.51    ( ! [X0] : (m1_subset_1(sK2(X0),X0)) )),
% 8.67/1.51    inference(cnf_transformation,[],[f73])).
% 8.67/1.51  fof(f73,plain,(
% 8.67/1.51    ! [X0] : m1_subset_1(sK2(X0),X0)),
% 8.67/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f19,f72])).
% 8.67/1.51  fof(f72,plain,(
% 8.67/1.51    ! [X0] : (? [X1] : m1_subset_1(X1,X0) => m1_subset_1(sK2(X0),X0))),
% 8.67/1.51    introduced(choice_axiom,[])).
% 8.67/1.51  fof(f19,axiom,(
% 8.67/1.51    ! [X0] : ? [X1] : m1_subset_1(X1,X0)),
% 8.67/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).
% 8.67/1.51  fof(f170,plain,(
% 8.67/1.51    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 8.67/1.51    inference(superposition,[],[f168,f104])).
% 8.67/1.51  fof(f104,plain,(
% 8.67/1.51    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 8.67/1.51    inference(cnf_transformation,[],[f7])).
% 8.67/1.51  fof(f7,axiom,(
% 8.67/1.51    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 8.67/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 8.67/1.51  fof(f168,plain,(
% 8.67/1.51    ( ! [X0,X1] : (m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0))) )),
% 8.67/1.51    inference(backward_demodulation,[],[f113,f103])).
% 8.67/1.51  fof(f103,plain,(
% 8.67/1.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 8.67/1.51    inference(cnf_transformation,[],[f23])).
% 8.67/1.51  fof(f23,axiom,(
% 8.67/1.51    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 8.67/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 8.67/1.51  fof(f113,plain,(
% 8.67/1.51    ( ! [X0,X1] : (m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 8.67/1.51    inference(cnf_transformation,[],[f18])).
% 8.67/1.51  fof(f18,axiom,(
% 8.67/1.51    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))),
% 8.67/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).
% 8.67/1.51  fof(f6392,plain,(
% 8.67/1.51    spl3_106 | spl3_171 | ~spl3_41 | ~spl3_47),
% 8.67/1.51    inference(avatar_split_clause,[],[f6391,f773,f745,f4063,f2559])).
% 8.67/1.51  fof(f4063,plain,(
% 8.67/1.51    spl3_171 <=> sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 8.67/1.51    introduced(avatar_definition,[new_symbols(naming,[spl3_171])])).
% 8.67/1.51  fof(f745,plain,(
% 8.67/1.51    spl3_41 <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))),
% 8.67/1.51    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).
% 8.67/1.51  fof(f773,plain,(
% 8.67/1.51    spl3_47 <=> sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))),
% 8.67/1.51    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).
% 8.67/1.51  fof(f6391,plain,(
% 8.67/1.51    ( ! [X16] : (sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~m1_subset_1(X16,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))) ) | (~spl3_41 | ~spl3_47)),
% 8.67/1.51    inference(subsumption_resolution,[],[f6364,f747])).
% 8.67/1.51  fof(f747,plain,(
% 8.67/1.51    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~spl3_41),
% 8.67/1.51    inference(avatar_component_clause,[],[f745])).
% 8.67/1.51  fof(f6364,plain,(
% 8.67/1.51    ( ! [X16] : (sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~m1_subset_1(X16,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))) ) | ~spl3_47),
% 8.67/1.51    inference(superposition,[],[f872,f775])).
% 8.67/1.51  fof(f775,plain,(
% 8.67/1.51    sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) | ~spl3_47),
% 8.67/1.51    inference(avatar_component_clause,[],[f773])).
% 8.67/1.51  fof(f872,plain,(
% 8.67/1.51    ( ! [X4,X2,X3] : (k3_subset_1(X2,X3) = k4_xboole_0(k3_subset_1(X2,X3),X3) | ~m1_subset_1(X3,k1_zfmisc_1(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(X2))) )),
% 8.67/1.51    inference(subsumption_resolution,[],[f867,f97])).
% 8.67/1.51  fof(f97,plain,(
% 8.67/1.51    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 8.67/1.51    inference(cnf_transformation,[],[f53])).
% 8.67/1.51  fof(f53,plain,(
% 8.67/1.51    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 8.67/1.51    inference(ennf_transformation,[],[f16])).
% 8.67/1.51  fof(f16,axiom,(
% 8.67/1.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 8.67/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 8.67/1.51  fof(f867,plain,(
% 8.67/1.51    ( ! [X4,X2,X3] : (k3_subset_1(X2,X3) = k4_xboole_0(k3_subset_1(X2,X3),X3) | ~m1_subset_1(X3,k1_zfmisc_1(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(X2)) | ~m1_subset_1(k3_subset_1(X2,X3),k1_zfmisc_1(X2))) )),
% 8.67/1.51    inference(superposition,[],[f322,f79])).
% 8.67/1.51  fof(f79,plain,(
% 8.67/1.51    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 8.67/1.51    inference(cnf_transformation,[],[f39])).
% 8.67/1.51  fof(f39,plain,(
% 8.67/1.51    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 8.67/1.51    inference(ennf_transformation,[],[f24])).
% 8.67/1.51  fof(f24,axiom,(
% 8.67/1.51    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 8.67/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 8.67/1.51  fof(f322,plain,(
% 8.67/1.51    ( ! [X4,X5,X3] : (k3_subset_1(X3,X4) = k7_subset_1(X3,k3_subset_1(X3,X4),X4) | ~m1_subset_1(X4,k1_zfmisc_1(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(X3))) )),
% 8.67/1.51    inference(subsumption_resolution,[],[f318,f97])).
% 8.67/1.51  fof(f318,plain,(
% 8.67/1.51    ( ! [X4,X5,X3] : (k3_subset_1(X3,X4) = k7_subset_1(X3,k3_subset_1(X3,X4),X4) | ~m1_subset_1(X4,k1_zfmisc_1(X3)) | ~m1_subset_1(k3_subset_1(X3,X4),k1_zfmisc_1(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(X3))) )),
% 8.67/1.51    inference(superposition,[],[f88,f111])).
% 8.67/1.51  fof(f111,plain,(
% 8.67/1.51    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X1) = X1 | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 8.67/1.51    inference(cnf_transformation,[],[f61])).
% 8.67/1.51  fof(f61,plain,(
% 8.67/1.51    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X1) = X1 | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 8.67/1.51    inference(ennf_transformation,[],[f20])).
% 8.67/1.51  fof(f20,axiom,(
% 8.67/1.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X1) = X1)),
% 8.67/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k9_subset_1)).
% 8.67/1.51  fof(f88,plain,(
% 8.67/1.51    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 8.67/1.51    inference(cnf_transformation,[],[f43])).
% 8.67/1.51  fof(f43,plain,(
% 8.67/1.51    ! [X0,X1] : (! [X2] : (k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 8.67/1.51    inference(ennf_transformation,[],[f25])).
% 8.67/1.51  fof(f25,axiom,(
% 8.67/1.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))))),
% 8.67/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_subset_1)).
% 8.67/1.51  fof(f6118,plain,(
% 8.67/1.51    spl3_47 | ~spl3_12 | ~spl3_46),
% 8.67/1.51    inference(avatar_split_clause,[],[f6117,f769,f247,f773])).
% 8.67/1.51  fof(f247,plain,(
% 8.67/1.51    spl3_12 <=> k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)),
% 8.67/1.51    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 8.67/1.51  fof(f769,plain,(
% 8.67/1.51    spl3_46 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))),
% 8.67/1.51    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).
% 8.67/1.51  fof(f6117,plain,(
% 8.67/1.51    sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) | (~spl3_12 | ~spl3_46)),
% 8.67/1.51    inference(subsumption_resolution,[],[f6097,f770])).
% 8.67/1.51  fof(f770,plain,(
% 8.67/1.51    m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~spl3_46),
% 8.67/1.51    inference(avatar_component_clause,[],[f769])).
% 8.67/1.51  fof(f6097,plain,(
% 8.67/1.51    sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~spl3_12),
% 8.67/1.51    inference(superposition,[],[f237,f249])).
% 8.67/1.51  fof(f249,plain,(
% 8.67/1.51    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~spl3_12),
% 8.67/1.51    inference(avatar_component_clause,[],[f247])).
% 8.67/1.51  fof(f237,plain,(
% 8.67/1.51    ( ! [X0,X1] : (k3_subset_1(X0,k4_xboole_0(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 8.67/1.51    inference(duplicate_literal_removal,[],[f233])).
% 8.67/1.51  fof(f233,plain,(
% 8.67/1.51    ( ! [X0,X1] : (k3_subset_1(X0,k4_xboole_0(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 8.67/1.51    inference(superposition,[],[f83,f84])).
% 8.67/1.51  fof(f84,plain,(
% 8.67/1.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 8.67/1.51    inference(cnf_transformation,[],[f41])).
% 8.67/1.51  fof(f41,plain,(
% 8.67/1.51    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 8.67/1.51    inference(ennf_transformation,[],[f15])).
% 8.67/1.51  fof(f15,axiom,(
% 8.67/1.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 8.67/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 8.67/1.51  fof(f83,plain,(
% 8.67/1.51    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 8.67/1.51    inference(cnf_transformation,[],[f40])).
% 8.67/1.51  fof(f40,plain,(
% 8.67/1.51    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 8.67/1.51    inference(ennf_transformation,[],[f21])).
% 8.67/1.51  fof(f21,axiom,(
% 8.67/1.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 8.67/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 8.67/1.51  fof(f6111,plain,(
% 8.67/1.51    spl3_41 | ~spl3_12),
% 8.67/1.51    inference(avatar_split_clause,[],[f6092,f247,f745])).
% 8.67/1.51  fof(f6092,plain,(
% 8.67/1.51    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~spl3_12),
% 8.67/1.51    inference(superposition,[],[f168,f249])).
% 8.67/1.51  fof(f6087,plain,(
% 8.67/1.51    spl3_12 | ~spl3_2 | ~spl3_11),
% 8.67/1.51    inference(avatar_split_clause,[],[f6086,f243,f123,f247])).
% 8.67/1.51  fof(f123,plain,(
% 8.67/1.51    spl3_2 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)),
% 8.67/1.51    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 8.67/1.51  fof(f243,plain,(
% 8.67/1.51    spl3_11 <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 8.67/1.51    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 8.67/1.51  fof(f6086,plain,(
% 8.67/1.51    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | (~spl3_2 | ~spl3_11)),
% 8.67/1.51    inference(subsumption_resolution,[],[f6083,f244])).
% 8.67/1.51  fof(f244,plain,(
% 8.67/1.51    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_11),
% 8.67/1.51    inference(avatar_component_clause,[],[f243])).
% 8.67/1.51  fof(f6083,plain,(
% 8.67/1.51    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_2),
% 8.67/1.51    inference(superposition,[],[f79,f124])).
% 8.67/1.51  fof(f124,plain,(
% 8.67/1.51    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~spl3_2),
% 8.67/1.51    inference(avatar_component_clause,[],[f123])).
% 8.67/1.51  fof(f5777,plain,(
% 8.67/1.51    ~spl3_3 | ~spl3_4 | spl3_85 | ~spl3_171),
% 8.67/1.51    inference(avatar_contradiction_clause,[],[f5776])).
% 8.67/1.51  fof(f5776,plain,(
% 8.67/1.51    $false | (~spl3_3 | ~spl3_4 | spl3_85 | ~spl3_171)),
% 8.67/1.51    inference(subsumption_resolution,[],[f5775,f136])).
% 8.67/1.51  fof(f136,plain,(
% 8.67/1.51    l1_pre_topc(sK0) | ~spl3_4),
% 8.67/1.51    inference(avatar_component_clause,[],[f134])).
% 8.67/1.51  fof(f134,plain,(
% 8.67/1.51    spl3_4 <=> l1_pre_topc(sK0)),
% 8.67/1.51    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 8.67/1.51  fof(f5775,plain,(
% 8.67/1.51    ~l1_pre_topc(sK0) | (~spl3_3 | spl3_85 | ~spl3_171)),
% 8.67/1.51    inference(subsumption_resolution,[],[f5774,f131])).
% 8.67/1.51  fof(f131,plain,(
% 8.67/1.51    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_3),
% 8.67/1.51    inference(avatar_component_clause,[],[f129])).
% 8.67/1.51  fof(f129,plain,(
% 8.67/1.51    spl3_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 8.67/1.51    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 8.67/1.51  fof(f5774,plain,(
% 8.67/1.51    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (spl3_85 | ~spl3_171)),
% 8.67/1.51    inference(subsumption_resolution,[],[f5750,f2252])).
% 8.67/1.51  fof(f2252,plain,(
% 8.67/1.51    sK1 != k1_tops_1(sK0,sK1) | spl3_85),
% 8.67/1.51    inference(avatar_component_clause,[],[f2251])).
% 8.67/1.51  fof(f2251,plain,(
% 8.67/1.51    spl3_85 <=> sK1 = k1_tops_1(sK0,sK1)),
% 8.67/1.51    introduced(avatar_definition,[new_symbols(naming,[spl3_85])])).
% 8.67/1.51  fof(f5750,plain,(
% 8.67/1.51    sK1 = k1_tops_1(sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl3_171),
% 8.67/1.51    inference(superposition,[],[f294,f4065])).
% 8.67/1.51  fof(f4065,plain,(
% 8.67/1.51    sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl3_171),
% 8.67/1.51    inference(avatar_component_clause,[],[f4063])).
% 8.67/1.51  fof(f294,plain,(
% 8.67/1.51    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 8.67/1.51    inference(duplicate_literal_removal,[],[f293])).
% 8.67/1.51  fof(f293,plain,(
% 8.67/1.51    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 8.67/1.51    inference(superposition,[],[f79,f90])).
% 8.67/1.51  fof(f90,plain,(
% 8.67/1.51    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 8.67/1.51    inference(cnf_transformation,[],[f45])).
% 8.67/1.51  fof(f45,plain,(
% 8.67/1.51    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 8.67/1.51    inference(ennf_transformation,[],[f34])).
% 8.67/1.51  fof(f34,axiom,(
% 8.67/1.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 8.67/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).
% 8.67/1.51  fof(f4371,plain,(
% 8.67/1.51    spl3_49 | ~spl3_3 | ~spl3_4),
% 8.67/1.51    inference(avatar_split_clause,[],[f4370,f134,f129,f808])).
% 8.67/1.51  fof(f808,plain,(
% 8.67/1.51    spl3_49 <=> r1_tarski(sK1,k2_pre_topc(sK0,sK1))),
% 8.67/1.51    introduced(avatar_definition,[new_symbols(naming,[spl3_49])])).
% 8.67/1.51  fof(f4370,plain,(
% 8.67/1.51    r1_tarski(sK1,k2_pre_topc(sK0,sK1)) | (~spl3_3 | ~spl3_4)),
% 8.67/1.51    inference(subsumption_resolution,[],[f4365,f136])).
% 8.67/1.51  fof(f4365,plain,(
% 8.67/1.51    r1_tarski(sK1,k2_pre_topc(sK0,sK1)) | ~l1_pre_topc(sK0) | ~spl3_3),
% 8.67/1.51    inference(resolution,[],[f131,f828])).
% 8.67/1.51  fof(f828,plain,(
% 8.67/1.51    ( ! [X4,X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4))) | r1_tarski(X3,k2_pre_topc(X4,X3)) | ~l1_pre_topc(X4)) )),
% 8.67/1.51    inference(superposition,[],[f107,f312])).
% 8.67/1.51  fof(f312,plain,(
% 8.67/1.51    ( ! [X2,X3] : (k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2)) )),
% 8.67/1.51    inference(subsumption_resolution,[],[f309,f92])).
% 8.67/1.51  fof(f92,plain,(
% 8.67/1.51    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 8.67/1.51    inference(cnf_transformation,[],[f48])).
% 8.67/1.51  fof(f48,plain,(
% 8.67/1.51    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 8.67/1.51    inference(flattening,[],[f47])).
% 8.67/1.51  fof(f47,plain,(
% 8.67/1.51    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 8.67/1.51    inference(ennf_transformation,[],[f28])).
% 8.67/1.51  fof(f28,axiom,(
% 8.67/1.51    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 8.67/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).
% 8.67/1.51  fof(f309,plain,(
% 8.67/1.51    ( ! [X2,X3] : (k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2) | ~m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))) )),
% 8.67/1.51    inference(duplicate_literal_removal,[],[f304])).
% 8.67/1.51  fof(f304,plain,(
% 8.67/1.51    ( ! [X2,X3] : (k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2) | ~m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) )),
% 8.67/1.51    inference(superposition,[],[f91,f110])).
% 8.67/1.51  fof(f110,plain,(
% 8.67/1.51    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 8.67/1.51    inference(cnf_transformation,[],[f60])).
% 8.67/1.51  fof(f60,plain,(
% 8.67/1.51    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 8.67/1.51    inference(flattening,[],[f59])).
% 8.67/1.51  fof(f59,plain,(
% 8.67/1.51    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 8.67/1.51    inference(ennf_transformation,[],[f22])).
% 8.67/1.51  fof(f22,axiom,(
% 8.67/1.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 8.67/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 8.67/1.51  fof(f91,plain,(
% 8.67/1.51    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 8.67/1.51    inference(cnf_transformation,[],[f46])).
% 8.67/1.51  fof(f46,plain,(
% 8.67/1.51    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 8.67/1.51    inference(ennf_transformation,[],[f33])).
% 8.67/1.51  fof(f33,axiom,(
% 8.67/1.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 8.67/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).
% 8.67/1.51  fof(f107,plain,(
% 8.67/1.51    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 8.67/1.51    inference(cnf_transformation,[],[f11])).
% 8.67/1.51  fof(f11,axiom,(
% 8.67/1.51    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 8.67/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 8.67/1.51  fof(f2306,plain,(
% 8.67/1.51    ~spl3_3 | ~spl3_4 | spl3_12 | ~spl3_85),
% 8.67/1.51    inference(avatar_contradiction_clause,[],[f2305])).
% 8.67/1.51  fof(f2305,plain,(
% 8.67/1.51    $false | (~spl3_3 | ~spl3_4 | spl3_12 | ~spl3_85)),
% 8.67/1.51    inference(subsumption_resolution,[],[f2304,f136])).
% 8.67/1.51  fof(f2304,plain,(
% 8.67/1.51    ~l1_pre_topc(sK0) | (~spl3_3 | spl3_12 | ~spl3_85)),
% 8.67/1.51    inference(subsumption_resolution,[],[f2303,f131])).
% 8.67/1.51  fof(f2303,plain,(
% 8.67/1.51    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (spl3_12 | ~spl3_85)),
% 8.67/1.51    inference(subsumption_resolution,[],[f2299,f248])).
% 8.67/1.51  fof(f248,plain,(
% 8.67/1.51    k2_tops_1(sK0,sK1) != k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | spl3_12),
% 8.67/1.51    inference(avatar_component_clause,[],[f247])).
% 8.67/1.51  fof(f2299,plain,(
% 8.67/1.51    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl3_85),
% 8.67/1.51    inference(superposition,[],[f1015,f2253])).
% 8.67/1.51  fof(f2253,plain,(
% 8.67/1.51    sK1 = k1_tops_1(sK0,sK1) | ~spl3_85),
% 8.67/1.51    inference(avatar_component_clause,[],[f2251])).
% 8.67/1.51  fof(f1015,plain,(
% 8.67/1.51    ( ! [X2,X3] : (k2_tops_1(X2,X3) = k4_xboole_0(k2_pre_topc(X2,X3),k1_tops_1(X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2)) )),
% 8.67/1.51    inference(subsumption_resolution,[],[f324,f314])).
% 8.67/1.51  fof(f314,plain,(
% 8.67/1.51    ( ! [X2,X3] : (m1_subset_1(k2_pre_topc(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2)) )),
% 8.67/1.51    inference(subsumption_resolution,[],[f307,f92])).
% 8.67/1.51  fof(f307,plain,(
% 8.67/1.51    ( ! [X2,X3] : (m1_subset_1(k2_pre_topc(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) | ~m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2)) )),
% 8.67/1.51    inference(duplicate_literal_removal,[],[f306])).
% 8.67/1.51  fof(f306,plain,(
% 8.67/1.51    ( ! [X2,X3] : (m1_subset_1(k2_pre_topc(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) | ~m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2)) )),
% 8.67/1.51    inference(superposition,[],[f112,f91])).
% 8.67/1.51  fof(f324,plain,(
% 8.67/1.51    ( ! [X2,X3] : (k2_tops_1(X2,X3) = k4_xboole_0(k2_pre_topc(X2,X3),k1_tops_1(X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2) | ~m1_subset_1(k2_pre_topc(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))) )),
% 8.67/1.51    inference(superposition,[],[f89,f79])).
% 8.67/1.51  fof(f89,plain,(
% 8.67/1.51    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 8.67/1.51    inference(cnf_transformation,[],[f44])).
% 8.67/1.51  fof(f44,plain,(
% 8.67/1.51    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 8.67/1.51    inference(ennf_transformation,[],[f30])).
% 8.67/1.51  fof(f30,axiom,(
% 8.67/1.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 8.67/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).
% 8.67/1.51  fof(f2291,plain,(
% 8.67/1.51    ~spl3_20 | spl3_85 | ~spl3_48),
% 8.67/1.51    inference(avatar_split_clause,[],[f2290,f779,f2251,f443])).
% 8.67/1.51  fof(f443,plain,(
% 8.67/1.51    spl3_20 <=> r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 8.67/1.51    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 8.67/1.51  fof(f779,plain,(
% 8.67/1.51    spl3_48 <=> r1_tarski(sK1,k1_tops_1(sK0,sK1))),
% 8.67/1.51    introduced(avatar_definition,[new_symbols(naming,[spl3_48])])).
% 8.67/1.51  fof(f2290,plain,(
% 8.67/1.51    sK1 = k1_tops_1(sK0,sK1) | ~r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~spl3_48),
% 8.67/1.51    inference(resolution,[],[f781,f82])).
% 8.67/1.51  fof(f82,plain,(
% 8.67/1.51    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 8.67/1.51    inference(cnf_transformation,[],[f70])).
% 8.67/1.51  fof(f70,plain,(
% 8.67/1.51    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 8.67/1.51    inference(flattening,[],[f69])).
% 8.67/1.51  fof(f69,plain,(
% 8.67/1.51    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 8.67/1.51    inference(nnf_transformation,[],[f1])).
% 8.67/1.51  fof(f1,axiom,(
% 8.67/1.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 8.67/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 8.67/1.51  fof(f781,plain,(
% 8.67/1.51    r1_tarski(sK1,k1_tops_1(sK0,sK1)) | ~spl3_48),
% 8.67/1.51    inference(avatar_component_clause,[],[f779])).
% 8.67/1.51  fof(f2288,plain,(
% 8.67/1.51    ~spl3_12 | spl3_2 | ~spl3_11),
% 8.67/1.51    inference(avatar_split_clause,[],[f2287,f243,f123,f247])).
% 8.67/1.51  fof(f2287,plain,(
% 8.67/1.51    k2_tops_1(sK0,sK1) != k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | (spl3_2 | ~spl3_11)),
% 8.67/1.51    inference(subsumption_resolution,[],[f2286,f244])).
% 8.67/1.51  fof(f2286,plain,(
% 8.67/1.51    k2_tops_1(sK0,sK1) != k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_2),
% 8.67/1.51    inference(superposition,[],[f125,f79])).
% 8.67/1.51  fof(f125,plain,(
% 8.67/1.51    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | spl3_2),
% 8.67/1.51    inference(avatar_component_clause,[],[f123])).
% 8.67/1.51  fof(f2249,plain,(
% 8.67/1.51    spl3_20 | ~spl3_3 | ~spl3_4),
% 8.67/1.51    inference(avatar_split_clause,[],[f2248,f134,f129,f443])).
% 8.67/1.51  fof(f2248,plain,(
% 8.67/1.51    r1_tarski(k1_tops_1(sK0,sK1),sK1) | (~spl3_3 | ~spl3_4)),
% 8.67/1.51    inference(subsumption_resolution,[],[f2239,f136])).
% 8.67/1.51  fof(f2239,plain,(
% 8.67/1.51    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~l1_pre_topc(sK0) | ~spl3_3),
% 8.67/1.51    inference(resolution,[],[f816,f131])).
% 8.67/1.51  fof(f816,plain,(
% 8.67/1.51    ( ! [X6,X7] : (~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X7))) | r1_tarski(k1_tops_1(X7,X6),X6) | ~l1_pre_topc(X7)) )),
% 8.67/1.51    inference(superposition,[],[f169,f294])).
% 8.67/1.51  fof(f169,plain,(
% 8.67/1.51    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 8.67/1.51    inference(resolution,[],[f168,f95])).
% 8.67/1.51  fof(f95,plain,(
% 8.67/1.51    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 8.67/1.51    inference(cnf_transformation,[],[f71])).
% 8.67/1.51  fof(f71,plain,(
% 8.67/1.51    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 8.67/1.51    inference(nnf_transformation,[],[f27])).
% 8.67/1.51  fof(f27,axiom,(
% 8.67/1.51    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 8.67/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 8.67/1.51  fof(f811,plain,(
% 8.67/1.51    ~spl3_49 | spl3_46),
% 8.67/1.51    inference(avatar_split_clause,[],[f806,f769,f808])).
% 8.67/1.51  fof(f806,plain,(
% 8.67/1.51    ~r1_tarski(sK1,k2_pre_topc(sK0,sK1)) | spl3_46),
% 8.67/1.51    inference(resolution,[],[f771,f96])).
% 8.67/1.51  fof(f96,plain,(
% 8.67/1.51    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 8.67/1.51    inference(cnf_transformation,[],[f71])).
% 8.67/1.51  fof(f771,plain,(
% 8.67/1.51    ~m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | spl3_46),
% 8.67/1.51    inference(avatar_component_clause,[],[f769])).
% 8.67/1.51  fof(f782,plain,(
% 8.67/1.51    spl3_48 | ~spl3_1 | ~spl3_3 | ~spl3_4),
% 8.67/1.51    inference(avatar_split_clause,[],[f777,f134,f129,f119,f779])).
% 8.67/1.51  fof(f119,plain,(
% 8.67/1.51    spl3_1 <=> v3_pre_topc(sK1,sK0)),
% 8.67/1.51    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 8.67/1.51  fof(f777,plain,(
% 8.67/1.51    ~v3_pre_topc(sK1,sK0) | r1_tarski(sK1,k1_tops_1(sK0,sK1)) | (~spl3_3 | ~spl3_4)),
% 8.67/1.51    inference(subsumption_resolution,[],[f354,f116])).
% 8.67/1.51  fof(f116,plain,(
% 8.67/1.51    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 8.67/1.51    inference(equality_resolution,[],[f81])).
% 8.67/1.51  fof(f81,plain,(
% 8.67/1.51    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 8.67/1.51    inference(cnf_transformation,[],[f70])).
% 8.67/1.51  fof(f354,plain,(
% 8.67/1.51    ~v3_pre_topc(sK1,sK0) | r1_tarski(sK1,k1_tops_1(sK0,sK1)) | ~r1_tarski(sK1,sK1) | (~spl3_3 | ~spl3_4)),
% 8.67/1.51    inference(resolution,[],[f341,f131])).
% 8.67/1.51  fof(f341,plain,(
% 8.67/1.51    ( ! [X18] : (~m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X18,sK0) | r1_tarski(X18,k1_tops_1(sK0,sK1)) | ~r1_tarski(X18,sK1)) ) | (~spl3_3 | ~spl3_4)),
% 8.67/1.51    inference(subsumption_resolution,[],[f337,f136])).
% 8.67/1.51  fof(f337,plain,(
% 8.67/1.51    ( ! [X18] : (~r1_tarski(X18,sK1) | ~v3_pre_topc(X18,sK0) | r1_tarski(X18,k1_tops_1(sK0,sK1)) | ~m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) ) | ~spl3_3),
% 8.67/1.51    inference(resolution,[],[f94,f131])).
% 8.67/1.51  fof(f94,plain,(
% 8.67/1.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | r1_tarski(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 8.67/1.51    inference(cnf_transformation,[],[f52])).
% 8.67/1.51  fof(f52,plain,(
% 8.67/1.51    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 8.67/1.51    inference(flattening,[],[f51])).
% 8.67/1.51  fof(f51,plain,(
% 8.67/1.51    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(X1,k1_tops_1(X0,X2)) | (~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 8.67/1.51    inference(ennf_transformation,[],[f31])).
% 8.67/1.51  fof(f31,axiom,(
% 8.67/1.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v3_pre_topc(X1,X0)) => r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 8.67/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_1)).
% 8.67/1.51  fof(f674,plain,(
% 8.67/1.51    ~spl3_3 | ~spl3_4 | spl3_11),
% 8.67/1.51    inference(avatar_contradiction_clause,[],[f673])).
% 8.67/1.51  fof(f673,plain,(
% 8.67/1.51    $false | (~spl3_3 | ~spl3_4 | spl3_11)),
% 8.67/1.51    inference(subsumption_resolution,[],[f672,f136])).
% 8.67/1.51  fof(f672,plain,(
% 8.67/1.51    ~l1_pre_topc(sK0) | (~spl3_3 | spl3_11)),
% 8.67/1.51    inference(subsumption_resolution,[],[f665,f131])).
% 8.67/1.51  fof(f665,plain,(
% 8.67/1.51    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl3_11),
% 8.67/1.51    inference(resolution,[],[f314,f245])).
% 8.67/1.51  fof(f245,plain,(
% 8.67/1.51    ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_11),
% 8.67/1.51    inference(avatar_component_clause,[],[f243])).
% 8.67/1.51  fof(f281,plain,(
% 8.67/1.51    spl3_15 | ~spl3_3 | ~spl3_4 | ~spl3_5),
% 8.67/1.51    inference(avatar_split_clause,[],[f276,f139,f134,f129,f278])).
% 8.67/1.51  fof(f278,plain,(
% 8.67/1.51    spl3_15 <=> v3_pre_topc(k1_tops_1(sK0,sK1),sK0)),
% 8.67/1.51    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 8.67/1.51  fof(f139,plain,(
% 8.67/1.51    spl3_5 <=> v2_pre_topc(sK0)),
% 8.67/1.51    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 8.67/1.51  fof(f276,plain,(
% 8.67/1.51    v3_pre_topc(k1_tops_1(sK0,sK1),sK0) | (~spl3_3 | ~spl3_4 | ~spl3_5)),
% 8.67/1.51    inference(subsumption_resolution,[],[f275,f141])).
% 8.67/1.51  fof(f141,plain,(
% 8.67/1.51    v2_pre_topc(sK0) | ~spl3_5),
% 8.67/1.51    inference(avatar_component_clause,[],[f139])).
% 8.67/1.51  fof(f275,plain,(
% 8.67/1.51    v3_pre_topc(k1_tops_1(sK0,sK1),sK0) | ~v2_pre_topc(sK0) | (~spl3_3 | ~spl3_4)),
% 8.67/1.51    inference(subsumption_resolution,[],[f272,f136])).
% 8.67/1.51  fof(f272,plain,(
% 8.67/1.51    v3_pre_topc(k1_tops_1(sK0,sK1),sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~spl3_3),
% 8.67/1.51    inference(resolution,[],[f93,f131])).
% 8.67/1.51  fof(f93,plain,(
% 8.67/1.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(k1_tops_1(X0,X1),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 8.67/1.51    inference(cnf_transformation,[],[f50])).
% 8.67/1.51  fof(f50,plain,(
% 8.67/1.51    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 8.67/1.51    inference(flattening,[],[f49])).
% 8.67/1.51  fof(f49,plain,(
% 8.67/1.51    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 8.67/1.51    inference(ennf_transformation,[],[f29])).
% 8.67/1.51  fof(f29,axiom,(
% 8.67/1.51    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 8.67/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).
% 8.67/1.51  fof(f142,plain,(
% 8.67/1.51    spl3_5),
% 8.67/1.51    inference(avatar_split_clause,[],[f74,f139])).
% 8.67/1.51  fof(f74,plain,(
% 8.67/1.51    v2_pre_topc(sK0)),
% 8.67/1.51    inference(cnf_transformation,[],[f68])).
% 8.67/1.51  fof(f68,plain,(
% 8.67/1.51    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 8.67/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f65,f67,f66])).
% 8.67/1.51  fof(f66,plain,(
% 8.67/1.51    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | ~v3_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 8.67/1.51    introduced(choice_axiom,[])).
% 8.67/1.51  fof(f67,plain,(
% 8.67/1.51    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | ~v3_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 8.67/1.51    introduced(choice_axiom,[])).
% 8.67/1.51  fof(f65,plain,(
% 8.67/1.51    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 8.67/1.51    inference(flattening,[],[f64])).
% 8.67/1.51  fof(f64,plain,(
% 8.67/1.51    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 8.67/1.51    inference(nnf_transformation,[],[f38])).
% 8.67/1.51  fof(f38,plain,(
% 8.67/1.51    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 8.67/1.51    inference(flattening,[],[f37])).
% 8.67/1.51  fof(f37,plain,(
% 8.67/1.51    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 8.67/1.51    inference(ennf_transformation,[],[f36])).
% 8.67/1.51  fof(f36,negated_conjecture,(
% 8.67/1.51    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 8.67/1.51    inference(negated_conjecture,[],[f35])).
% 8.67/1.51  fof(f35,conjecture,(
% 8.67/1.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 8.67/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tops_1)).
% 8.67/1.51  fof(f137,plain,(
% 8.67/1.51    spl3_4),
% 8.67/1.51    inference(avatar_split_clause,[],[f75,f134])).
% 8.67/1.51  fof(f75,plain,(
% 8.67/1.51    l1_pre_topc(sK0)),
% 8.67/1.51    inference(cnf_transformation,[],[f68])).
% 8.67/1.51  fof(f132,plain,(
% 8.67/1.51    spl3_3),
% 8.67/1.51    inference(avatar_split_clause,[],[f76,f129])).
% 8.67/1.51  fof(f76,plain,(
% 8.67/1.51    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 8.67/1.51    inference(cnf_transformation,[],[f68])).
% 8.67/1.51  fof(f127,plain,(
% 8.67/1.51    spl3_1 | spl3_2),
% 8.67/1.51    inference(avatar_split_clause,[],[f77,f123,f119])).
% 8.67/1.51  fof(f77,plain,(
% 8.67/1.51    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)),
% 8.67/1.51    inference(cnf_transformation,[],[f68])).
% 8.67/1.51  fof(f126,plain,(
% 8.67/1.51    ~spl3_1 | ~spl3_2),
% 8.67/1.51    inference(avatar_split_clause,[],[f78,f123,f119])).
% 8.67/1.51  fof(f78,plain,(
% 8.67/1.51    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)),
% 8.67/1.51    inference(cnf_transformation,[],[f68])).
% 8.67/1.51  % SZS output end Proof for theBenchmark
% 8.67/1.51  % (31077)------------------------------
% 8.67/1.51  % (31077)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.67/1.51  % (31077)Termination reason: Refutation
% 8.67/1.51  
% 8.67/1.51  % (31077)Memory used [KB]: 14456
% 8.67/1.51  % (31077)Time elapsed: 1.054 s
% 8.67/1.51  % (31077)------------------------------
% 8.67/1.51  % (31077)------------------------------
% 8.67/1.52  % (31055)Success in time 1.141 s
%------------------------------------------------------------------------------
