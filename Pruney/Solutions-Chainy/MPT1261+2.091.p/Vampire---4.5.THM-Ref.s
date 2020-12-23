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
% DateTime   : Thu Dec  3 13:12:02 EST 2020

% Result     : Theorem 2.10s
% Output     : Refutation 2.36s
% Verified   : 
% Statistics : Number of formulae       :  160 ( 400 expanded)
%              Number of leaves         :   45 ( 163 expanded)
%              Depth                    :    9
%              Number of atoms          :  417 (1017 expanded)
%              Number of equality atoms :  101 ( 287 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3786,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f117,f118,f123,f128,f133,f150,f642,f665,f703,f760,f804,f1819,f1824,f1826,f1835,f1858,f1870,f2084,f2557,f2965,f3609,f3612,f3778,f3779,f3784,f3785])).

fof(f3785,plain,
    ( k2_pre_topc(sK0,sK1) != k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) != k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | sK1 != k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | sK1 = k2_pre_topc(sK0,sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f3784,plain,
    ( k3_subset_1(sK1,k2_tops_1(sK0,sK1)) != k7_subset_1(sK1,sK1,k2_tops_1(sK0,sK1))
    | k1_tops_1(sK0,sK1) != k7_subset_1(sK1,sK1,k2_tops_1(sK0,sK1))
    | k3_subset_1(sK1,k1_tops_1(sK0,sK1)) != k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1))
    | k2_tops_1(sK0,sK1) != k3_subset_1(sK1,k3_subset_1(sK1,k2_tops_1(sK0,sK1)))
    | k2_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f3779,plain,
    ( spl2_305
    | ~ spl2_3
    | ~ spl2_52 ),
    inference(avatar_split_clause,[],[f3766,f662,f120,f3770])).

fof(f3770,plain,
    ( spl2_305
  <=> k1_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_305])])).

fof(f120,plain,
    ( spl2_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f662,plain,
    ( spl2_52
  <=> k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_52])])).

fof(f3766,plain,
    ( k1_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_52 ),
    inference(superposition,[],[f664,f3431])).

fof(f3431,plain,
    ( ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0)
    | ~ spl2_3 ),
    inference(backward_demodulation,[],[f364,f360])).

fof(f360,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k7_subset_1(X0,X0,X1) ),
    inference(unit_resulting_resolution,[],[f134,f108])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) ) ),
    inference(definition_unfolding,[],[f95,f99])).

fof(f99,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f83,f80])).

fof(f80,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f83,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f134,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f70,f67])).

fof(f67,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f70,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f364,plain,
    ( ! [X0] : k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X0))) = k7_subset_1(u1_struct_0(sK0),sK1,X0)
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f122,f108])).

fof(f122,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f120])).

fof(f664,plain,
    ( k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_52 ),
    inference(avatar_component_clause,[],[f662])).

fof(f3778,plain,
    ( ~ spl2_306
    | spl2_2
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f3765,f120,f114,f3775])).

fof(f3775,plain,
    ( spl2_306
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_306])])).

fof(f114,plain,
    ( spl2_2
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f3765,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1))
    | spl2_2
    | ~ spl2_3 ),
    inference(superposition,[],[f116,f3431])).

fof(f116,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f114])).

fof(f3612,plain,
    ( spl2_290
    | ~ spl2_192 ),
    inference(avatar_split_clause,[],[f3552,f2081,f3560])).

fof(f3560,plain,
    ( spl2_290
  <=> k3_subset_1(sK1,k1_tops_1(sK0,sK1)) = k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_290])])).

fof(f2081,plain,
    ( spl2_192
  <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_192])])).

fof(f3552,plain,
    ( k3_subset_1(sK1,k1_tops_1(sK0,sK1)) = k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_192 ),
    inference(resolution,[],[f3425,f2083])).

fof(f2083,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ spl2_192 ),
    inference(avatar_component_clause,[],[f2081])).

fof(f3425,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,X1) = k7_subset_1(X0,X0,X1) ) ),
    inference(backward_demodulation,[],[f105,f360])).

fof(f105,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ) ),
    inference(definition_unfolding,[],[f87,f99])).

fof(f87,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f3609,plain,
    ( spl2_293
    | ~ spl2_50 ),
    inference(avatar_split_clause,[],[f3549,f633,f3575])).

fof(f3575,plain,
    ( spl2_293
  <=> k3_subset_1(sK1,k2_tops_1(sK0,sK1)) = k7_subset_1(sK1,sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_293])])).

fof(f633,plain,
    ( spl2_50
  <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_50])])).

fof(f3549,plain,
    ( k3_subset_1(sK1,k2_tops_1(sK0,sK1)) = k7_subset_1(sK1,sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_50 ),
    inference(resolution,[],[f3425,f635])).

fof(f635,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ spl2_50 ),
    inference(avatar_component_clause,[],[f633])).

fof(f2965,plain,
    ( spl2_207
    | ~ spl2_48 ),
    inference(avatar_split_clause,[],[f2940,f611,f2190])).

fof(f2190,plain,
    ( spl2_207
  <=> k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k3_subset_1(sK1,k2_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_207])])).

fof(f611,plain,
    ( spl2_48
  <=> r1_tarski(k2_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_48])])).

fof(f2940,plain,
    ( k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k3_subset_1(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_48 ),
    inference(resolution,[],[f210,f613])).

fof(f613,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_48 ),
    inference(avatar_component_clause,[],[f611])).

fof(f210,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X2,X1)
      | k3_subset_1(X1,k3_subset_1(X1,X2)) = X2 ) ),
    inference(resolution,[],[f88,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
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

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f2557,plain,
    ( spl2_132
    | ~ spl2_51 ),
    inference(avatar_split_clause,[],[f2553,f638,f1436])).

fof(f1436,plain,
    ( spl2_132
  <=> sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_132])])).

fof(f638,plain,
    ( spl2_51
  <=> sK1 = k2_xboole_0(k2_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_51])])).

fof(f2553,plain,
    ( sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_51 ),
    inference(superposition,[],[f79,f640])).

fof(f640,plain,
    ( sK1 = k2_xboole_0(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_51 ),
    inference(avatar_component_clause,[],[f638])).

fof(f79,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f2084,plain,
    ( spl2_192
    | ~ spl2_181 ),
    inference(avatar_split_clause,[],[f2077,f1821,f2081])).

fof(f1821,plain,
    ( spl2_181
  <=> r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_181])])).

fof(f2077,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ spl2_181 ),
    inference(unit_resulting_resolution,[],[f1823,f90])).

fof(f1823,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl2_181 ),
    inference(avatar_component_clause,[],[f1821])).

fof(f1870,plain,
    ( spl2_51
    | ~ spl2_48 ),
    inference(avatar_split_clause,[],[f1857,f611,f638])).

fof(f1857,plain,
    ( sK1 = k2_xboole_0(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_48 ),
    inference(resolution,[],[f613,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f1858,plain,
    ( spl2_50
    | ~ spl2_48 ),
    inference(avatar_split_clause,[],[f1855,f611,f633])).

fof(f1855,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ spl2_48 ),
    inference(unit_resulting_resolution,[],[f613,f90])).

fof(f1835,plain,
    ( ~ spl2_4
    | ~ spl2_3
    | spl2_48
    | ~ spl2_1 ),
    inference(avatar_split_clause,[],[f1831,f110,f611,f120,f125])).

fof(f125,plain,
    ( spl2_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f110,plain,
    ( spl2_1
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f1831,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_1 ),
    inference(resolution,[],[f111,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ v4_pre_topc(X1,X0)
      | r1_tarski(k2_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => r1_tarski(k2_tops_1(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_tops_1)).

fof(f111,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f110])).

fof(f1826,plain,
    ( spl2_1
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_47 ),
    inference(avatar_split_clause,[],[f617,f606,f130,f125,f120,f110])).

fof(f130,plain,
    ( spl2_5
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f606,plain,
    ( spl2_47
  <=> sK1 = k2_pre_topc(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_47])])).

fof(f617,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_47 ),
    inference(unit_resulting_resolution,[],[f127,f132,f122,f608,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | k2_pre_topc(X0,X1) != X1
      | v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

fof(f608,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl2_47 ),
    inference(avatar_component_clause,[],[f606])).

fof(f132,plain,
    ( v2_pre_topc(sK0)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f130])).

fof(f127,plain,
    ( l1_pre_topc(sK0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f125])).

fof(f1824,plain,
    ( spl2_181
    | ~ spl2_3
    | ~ spl2_52 ),
    inference(avatar_split_clause,[],[f1818,f662,f120,f1821])).

fof(f1818,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl2_3
    | ~ spl2_52 ),
    inference(superposition,[],[f1015,f664])).

fof(f1015,plain,
    ( ! [X4] : r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,X4),sK1)
    | ~ spl2_3 ),
    inference(superposition,[],[f100,f364])).

fof(f100,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0) ),
    inference(definition_unfolding,[],[f77,f99])).

fof(f77,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f1819,plain,
    ( spl2_48
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f1817,f120,f114,f611])).

fof(f1817,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(superposition,[],[f1015,f115])).

fof(f115,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f114])).

fof(f804,plain,
    ( spl2_27
    | ~ spl2_3
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f792,f228,f120,f437])).

fof(f437,plain,
    ( spl2_27
  <=> k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).

fof(f228,plain,
    ( spl2_10
  <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f792,plain,
    ( k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_10 ),
    inference(unit_resulting_resolution,[],[f122,f230,f98])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
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

fof(f230,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f228])).

fof(f760,plain,
    ( spl2_10
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f757,f241,f228])).

fof(f241,plain,
    ( spl2_11
  <=> r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f757,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_11 ),
    inference(unit_resulting_resolution,[],[f243,f90])).

fof(f243,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0))
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f241])).

fof(f703,plain,
    ( spl2_57
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f697,f125,f120,f700])).

fof(f700,plain,
    ( spl2_57
  <=> k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_57])])).

fof(f697,plain,
    ( k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(unit_resulting_resolution,[],[f127,f122,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

fof(f665,plain,
    ( spl2_52
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f659,f125,f120,f662])).

fof(f659,plain,
    ( k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(unit_resulting_resolution,[],[f127,f122,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
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

fof(f642,plain,
    ( spl2_11
    | ~ spl2_6
    | ~ spl2_48 ),
    inference(avatar_split_clause,[],[f626,f611,f146,f241])).

fof(f146,plain,
    ( spl2_6
  <=> r1_tarski(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f626,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0))
    | ~ spl2_6
    | ~ spl2_48 ),
    inference(unit_resulting_resolution,[],[f148,f613,f97])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f148,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f146])).

fof(f150,plain,
    ( spl2_6
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f142,f120,f146])).

fof(f142,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl2_3 ),
    inference(resolution,[],[f89,f122])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f133,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f62,f130])).

fof(f62,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,
    ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | ~ v4_pre_topc(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | v4_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f57,f59,f58])).

fof(f58,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
              | ~ v4_pre_topc(X1,X0) )
            & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
              | v4_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ( k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1))
            | ~ v4_pre_topc(X1,sK0) )
          & ( k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1))
            | v4_pre_topc(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,
    ( ? [X1] :
        ( ( k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1))
          | ~ v4_pre_topc(X1,sK0) )
        & ( k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1))
          | v4_pre_topc(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
        | ~ v4_pre_topc(sK1,sK0) )
      & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
        | v4_pre_topc(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
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
           => ( v4_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f31])).

fof(f31,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).

fof(f128,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f63,f125])).

fof(f63,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f60])).

fof(f123,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f64,f120])).

fof(f64,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f60])).

fof(f118,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f65,f114,f110])).

fof(f65,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f60])).

fof(f117,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f66,f114,f110])).

fof(f66,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f60])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n003.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:56:57 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.44  % (4632)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.45  % (4624)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.46  % (4617)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.48  % (4618)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.48  % (4625)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.48  % (4626)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.48  % (4615)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.49  % (4619)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.49  % (4623)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.50  % (4628)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.50  % (4627)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.50  % (4620)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.51  % (4631)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.51  % (4622)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.51  % (4630)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.52  % (4616)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.52  % (4629)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.53  % (4621)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 2.10/0.65  % (4621)Refutation found. Thanks to Tanya!
% 2.10/0.65  % SZS status Theorem for theBenchmark
% 2.10/0.65  % SZS output start Proof for theBenchmark
% 2.36/0.66  fof(f3786,plain,(
% 2.36/0.66    $false),
% 2.36/0.66    inference(avatar_sat_refutation,[],[f117,f118,f123,f128,f133,f150,f642,f665,f703,f760,f804,f1819,f1824,f1826,f1835,f1858,f1870,f2084,f2557,f2965,f3609,f3612,f3778,f3779,f3784,f3785])).
% 2.36/0.66  fof(f3785,plain,(
% 2.36/0.66    k2_pre_topc(sK0,sK1) != k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) != k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | sK1 != k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | sK1 = k2_pre_topc(sK0,sK1)),
% 2.36/0.66    introduced(theory_tautology_sat_conflict,[])).
% 2.36/0.66  fof(f3784,plain,(
% 2.36/0.66    k3_subset_1(sK1,k2_tops_1(sK0,sK1)) != k7_subset_1(sK1,sK1,k2_tops_1(sK0,sK1)) | k1_tops_1(sK0,sK1) != k7_subset_1(sK1,sK1,k2_tops_1(sK0,sK1)) | k3_subset_1(sK1,k1_tops_1(sK0,sK1)) != k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1)) | k2_tops_1(sK0,sK1) != k3_subset_1(sK1,k3_subset_1(sK1,k2_tops_1(sK0,sK1))) | k2_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1))),
% 2.36/0.66    introduced(theory_tautology_sat_conflict,[])).
% 2.36/0.66  fof(f3779,plain,(
% 2.36/0.66    spl2_305 | ~spl2_3 | ~spl2_52),
% 2.36/0.66    inference(avatar_split_clause,[],[f3766,f662,f120,f3770])).
% 2.36/0.66  fof(f3770,plain,(
% 2.36/0.66    spl2_305 <=> k1_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k2_tops_1(sK0,sK1))),
% 2.36/0.66    introduced(avatar_definition,[new_symbols(naming,[spl2_305])])).
% 2.36/0.66  fof(f120,plain,(
% 2.36/0.66    spl2_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.36/0.66    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 2.36/0.66  fof(f662,plain,(
% 2.36/0.66    spl2_52 <=> k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 2.36/0.66    introduced(avatar_definition,[new_symbols(naming,[spl2_52])])).
% 2.36/0.66  fof(f3766,plain,(
% 2.36/0.66    k1_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k2_tops_1(sK0,sK1)) | (~spl2_3 | ~spl2_52)),
% 2.36/0.66    inference(superposition,[],[f664,f3431])).
% 2.36/0.67  fof(f3431,plain,(
% 2.36/0.67    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0)) ) | ~spl2_3),
% 2.36/0.67    inference(backward_demodulation,[],[f364,f360])).
% 2.36/0.67  fof(f360,plain,(
% 2.36/0.67    ( ! [X0,X1] : (k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k7_subset_1(X0,X0,X1)) )),
% 2.36/0.67    inference(unit_resulting_resolution,[],[f134,f108])).
% 2.36/0.67  fof(f108,plain,(
% 2.36/0.67    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))) )),
% 2.36/0.67    inference(definition_unfolding,[],[f95,f99])).
% 2.36/0.67  fof(f99,plain,(
% 2.36/0.67    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 2.36/0.67    inference(definition_unfolding,[],[f83,f80])).
% 2.36/0.67  fof(f80,plain,(
% 2.36/0.67    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.36/0.67    inference(cnf_transformation,[],[f23])).
% 2.36/0.67  fof(f23,axiom,(
% 2.36/0.67    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 2.36/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 2.36/0.67  fof(f83,plain,(
% 2.36/0.67    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.36/0.67    inference(cnf_transformation,[],[f3])).
% 2.36/0.67  fof(f3,axiom,(
% 2.36/0.67    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.36/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.36/0.67  fof(f95,plain,(
% 2.36/0.67    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.36/0.67    inference(cnf_transformation,[],[f49])).
% 2.36/0.67  fof(f49,plain,(
% 2.36/0.67    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.36/0.67    inference(ennf_transformation,[],[f20])).
% 2.36/0.67  fof(f20,axiom,(
% 2.36/0.67    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 2.36/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 2.36/0.67  fof(f134,plain,(
% 2.36/0.67    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 2.36/0.67    inference(forward_demodulation,[],[f70,f67])).
% 2.36/0.67  fof(f67,plain,(
% 2.36/0.67    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 2.36/0.67    inference(cnf_transformation,[],[f12])).
% 2.36/0.67  fof(f12,axiom,(
% 2.36/0.67    ! [X0] : k2_subset_1(X0) = X0),
% 2.36/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 2.36/0.67  fof(f70,plain,(
% 2.36/0.67    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 2.36/0.67    inference(cnf_transformation,[],[f14])).
% 2.36/0.67  fof(f14,axiom,(
% 2.36/0.67    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 2.36/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 2.36/0.67  fof(f364,plain,(
% 2.36/0.67    ( ! [X0] : (k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X0))) = k7_subset_1(u1_struct_0(sK0),sK1,X0)) ) | ~spl2_3),
% 2.36/0.67    inference(unit_resulting_resolution,[],[f122,f108])).
% 2.36/0.67  fof(f122,plain,(
% 2.36/0.67    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_3),
% 2.36/0.67    inference(avatar_component_clause,[],[f120])).
% 2.36/0.67  fof(f664,plain,(
% 2.36/0.67    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | ~spl2_52),
% 2.36/0.67    inference(avatar_component_clause,[],[f662])).
% 2.36/0.67  fof(f3778,plain,(
% 2.36/0.67    ~spl2_306 | spl2_2 | ~spl2_3),
% 2.36/0.67    inference(avatar_split_clause,[],[f3765,f120,f114,f3775])).
% 2.36/0.67  fof(f3775,plain,(
% 2.36/0.67    spl2_306 <=> k2_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1))),
% 2.36/0.67    introduced(avatar_definition,[new_symbols(naming,[spl2_306])])).
% 2.36/0.67  fof(f114,plain,(
% 2.36/0.67    spl2_2 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),
% 2.36/0.67    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 2.36/0.67  fof(f3765,plain,(
% 2.36/0.67    k2_tops_1(sK0,sK1) != k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1)) | (spl2_2 | ~spl2_3)),
% 2.36/0.67    inference(superposition,[],[f116,f3431])).
% 2.36/0.67  fof(f116,plain,(
% 2.36/0.67    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | spl2_2),
% 2.36/0.67    inference(avatar_component_clause,[],[f114])).
% 2.36/0.67  fof(f3612,plain,(
% 2.36/0.67    spl2_290 | ~spl2_192),
% 2.36/0.67    inference(avatar_split_clause,[],[f3552,f2081,f3560])).
% 2.36/0.67  fof(f3560,plain,(
% 2.36/0.67    spl2_290 <=> k3_subset_1(sK1,k1_tops_1(sK0,sK1)) = k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1))),
% 2.36/0.67    introduced(avatar_definition,[new_symbols(naming,[spl2_290])])).
% 2.36/0.67  fof(f2081,plain,(
% 2.36/0.67    spl2_192 <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1))),
% 2.36/0.67    introduced(avatar_definition,[new_symbols(naming,[spl2_192])])).
% 2.36/0.67  fof(f3552,plain,(
% 2.36/0.67    k3_subset_1(sK1,k1_tops_1(sK0,sK1)) = k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1)) | ~spl2_192),
% 2.36/0.67    inference(resolution,[],[f3425,f2083])).
% 2.36/0.67  fof(f2083,plain,(
% 2.36/0.67    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | ~spl2_192),
% 2.36/0.67    inference(avatar_component_clause,[],[f2081])).
% 2.36/0.67  fof(f3425,plain,(
% 2.36/0.67    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,X1) = k7_subset_1(X0,X0,X1)) )),
% 2.36/0.67    inference(backward_demodulation,[],[f105,f360])).
% 2.36/0.67  fof(f105,plain,(
% 2.36/0.67    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 2.36/0.67    inference(definition_unfolding,[],[f87,f99])).
% 2.36/0.67  fof(f87,plain,(
% 2.36/0.67    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.36/0.67    inference(cnf_transformation,[],[f44])).
% 2.36/0.67  fof(f44,plain,(
% 2.36/0.67    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.36/0.67    inference(ennf_transformation,[],[f13])).
% 2.36/0.67  fof(f13,axiom,(
% 2.36/0.67    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 2.36/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 2.36/0.67  fof(f3609,plain,(
% 2.36/0.67    spl2_293 | ~spl2_50),
% 2.36/0.67    inference(avatar_split_clause,[],[f3549,f633,f3575])).
% 2.36/0.67  fof(f3575,plain,(
% 2.36/0.67    spl2_293 <=> k3_subset_1(sK1,k2_tops_1(sK0,sK1)) = k7_subset_1(sK1,sK1,k2_tops_1(sK0,sK1))),
% 2.36/0.67    introduced(avatar_definition,[new_symbols(naming,[spl2_293])])).
% 2.36/0.67  fof(f633,plain,(
% 2.36/0.67    spl2_50 <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1))),
% 2.36/0.67    introduced(avatar_definition,[new_symbols(naming,[spl2_50])])).
% 2.36/0.67  fof(f3549,plain,(
% 2.36/0.67    k3_subset_1(sK1,k2_tops_1(sK0,sK1)) = k7_subset_1(sK1,sK1,k2_tops_1(sK0,sK1)) | ~spl2_50),
% 2.36/0.67    inference(resolution,[],[f3425,f635])).
% 2.36/0.67  fof(f635,plain,(
% 2.36/0.67    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | ~spl2_50),
% 2.36/0.67    inference(avatar_component_clause,[],[f633])).
% 2.36/0.67  fof(f2965,plain,(
% 2.36/0.67    spl2_207 | ~spl2_48),
% 2.36/0.67    inference(avatar_split_clause,[],[f2940,f611,f2190])).
% 2.36/0.67  fof(f2190,plain,(
% 2.36/0.67    spl2_207 <=> k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k3_subset_1(sK1,k2_tops_1(sK0,sK1)))),
% 2.36/0.67    introduced(avatar_definition,[new_symbols(naming,[spl2_207])])).
% 2.36/0.67  fof(f611,plain,(
% 2.36/0.67    spl2_48 <=> r1_tarski(k2_tops_1(sK0,sK1),sK1)),
% 2.36/0.67    introduced(avatar_definition,[new_symbols(naming,[spl2_48])])).
% 2.36/0.67  fof(f2940,plain,(
% 2.36/0.67    k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k3_subset_1(sK1,k2_tops_1(sK0,sK1))) | ~spl2_48),
% 2.36/0.67    inference(resolution,[],[f210,f613])).
% 2.36/0.67  fof(f613,plain,(
% 2.36/0.67    r1_tarski(k2_tops_1(sK0,sK1),sK1) | ~spl2_48),
% 2.36/0.67    inference(avatar_component_clause,[],[f611])).
% 2.36/0.67  fof(f210,plain,(
% 2.36/0.67    ( ! [X2,X1] : (~r1_tarski(X2,X1) | k3_subset_1(X1,k3_subset_1(X1,X2)) = X2) )),
% 2.36/0.67    inference(resolution,[],[f88,f90])).
% 2.36/0.67  fof(f90,plain,(
% 2.36/0.67    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.36/0.67    inference(cnf_transformation,[],[f61])).
% 2.36/0.67  fof(f61,plain,(
% 2.36/0.67    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.36/0.67    inference(nnf_transformation,[],[f24])).
% 2.36/0.67  fof(f24,axiom,(
% 2.36/0.67    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.36/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 2.36/0.67  fof(f88,plain,(
% 2.36/0.67    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 2.36/0.67    inference(cnf_transformation,[],[f45])).
% 2.36/0.67  fof(f45,plain,(
% 2.36/0.67    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.36/0.67    inference(ennf_transformation,[],[f18])).
% 2.36/0.67  fof(f18,axiom,(
% 2.36/0.67    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 2.36/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 2.36/0.67  fof(f2557,plain,(
% 2.36/0.67    spl2_132 | ~spl2_51),
% 2.36/0.67    inference(avatar_split_clause,[],[f2553,f638,f1436])).
% 2.36/0.67  fof(f1436,plain,(
% 2.36/0.67    spl2_132 <=> sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 2.36/0.67    introduced(avatar_definition,[new_symbols(naming,[spl2_132])])).
% 2.36/0.67  fof(f638,plain,(
% 2.36/0.67    spl2_51 <=> sK1 = k2_xboole_0(k2_tops_1(sK0,sK1),sK1)),
% 2.36/0.67    introduced(avatar_definition,[new_symbols(naming,[spl2_51])])).
% 2.36/0.67  fof(f2553,plain,(
% 2.36/0.67    sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl2_51),
% 2.36/0.67    inference(superposition,[],[f79,f640])).
% 2.36/0.67  fof(f640,plain,(
% 2.36/0.67    sK1 = k2_xboole_0(k2_tops_1(sK0,sK1),sK1) | ~spl2_51),
% 2.36/0.67    inference(avatar_component_clause,[],[f638])).
% 2.36/0.67  fof(f79,plain,(
% 2.36/0.67    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 2.36/0.67    inference(cnf_transformation,[],[f1])).
% 2.36/0.67  fof(f1,axiom,(
% 2.36/0.67    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 2.36/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 2.36/0.67  fof(f2084,plain,(
% 2.36/0.67    spl2_192 | ~spl2_181),
% 2.36/0.67    inference(avatar_split_clause,[],[f2077,f1821,f2081])).
% 2.36/0.67  fof(f1821,plain,(
% 2.36/0.67    spl2_181 <=> r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 2.36/0.67    introduced(avatar_definition,[new_symbols(naming,[spl2_181])])).
% 2.36/0.67  fof(f2077,plain,(
% 2.36/0.67    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | ~spl2_181),
% 2.36/0.67    inference(unit_resulting_resolution,[],[f1823,f90])).
% 2.36/0.67  fof(f1823,plain,(
% 2.36/0.67    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~spl2_181),
% 2.36/0.67    inference(avatar_component_clause,[],[f1821])).
% 2.36/0.67  fof(f1870,plain,(
% 2.36/0.67    spl2_51 | ~spl2_48),
% 2.36/0.67    inference(avatar_split_clause,[],[f1857,f611,f638])).
% 2.36/0.67  fof(f1857,plain,(
% 2.36/0.67    sK1 = k2_xboole_0(k2_tops_1(sK0,sK1),sK1) | ~spl2_48),
% 2.36/0.67    inference(resolution,[],[f613,f85])).
% 2.36/0.67  fof(f85,plain,(
% 2.36/0.67    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 2.36/0.67    inference(cnf_transformation,[],[f42])).
% 2.36/0.67  fof(f42,plain,(
% 2.36/0.67    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 2.36/0.67    inference(ennf_transformation,[],[f4])).
% 2.36/0.67  fof(f4,axiom,(
% 2.36/0.67    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 2.36/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 2.36/0.67  fof(f1858,plain,(
% 2.36/0.67    spl2_50 | ~spl2_48),
% 2.36/0.67    inference(avatar_split_clause,[],[f1855,f611,f633])).
% 2.36/0.67  fof(f1855,plain,(
% 2.36/0.67    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | ~spl2_48),
% 2.36/0.67    inference(unit_resulting_resolution,[],[f613,f90])).
% 2.36/0.67  fof(f1835,plain,(
% 2.36/0.67    ~spl2_4 | ~spl2_3 | spl2_48 | ~spl2_1),
% 2.36/0.67    inference(avatar_split_clause,[],[f1831,f110,f611,f120,f125])).
% 2.36/0.67  fof(f125,plain,(
% 2.36/0.67    spl2_4 <=> l1_pre_topc(sK0)),
% 2.36/0.67    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 2.36/0.67  fof(f110,plain,(
% 2.36/0.67    spl2_1 <=> v4_pre_topc(sK1,sK0)),
% 2.36/0.67    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 2.36/0.67  fof(f1831,plain,(
% 2.36/0.67    r1_tarski(k2_tops_1(sK0,sK1),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl2_1),
% 2.36/0.67    inference(resolution,[],[f111,f76])).
% 2.36/0.67  fof(f76,plain,(
% 2.36/0.67    ( ! [X0,X1] : (~v4_pre_topc(X1,X0) | r1_tarski(k2_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.36/0.67    inference(cnf_transformation,[],[f41])).
% 2.36/0.67  fof(f41,plain,(
% 2.36/0.67    ! [X0] : (! [X1] : (r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.36/0.67    inference(flattening,[],[f40])).
% 2.36/0.67  fof(f40,plain,(
% 2.36/0.67    ! [X0] : (! [X1] : ((r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.36/0.67    inference(ennf_transformation,[],[f29])).
% 2.36/0.67  fof(f29,axiom,(
% 2.36/0.67    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => r1_tarski(k2_tops_1(X0,X1),X1))))),
% 2.36/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_tops_1)).
% 2.36/0.67  fof(f111,plain,(
% 2.36/0.67    v4_pre_topc(sK1,sK0) | ~spl2_1),
% 2.36/0.67    inference(avatar_component_clause,[],[f110])).
% 2.36/0.67  fof(f1826,plain,(
% 2.36/0.67    spl2_1 | ~spl2_3 | ~spl2_4 | ~spl2_5 | ~spl2_47),
% 2.36/0.67    inference(avatar_split_clause,[],[f617,f606,f130,f125,f120,f110])).
% 2.36/0.67  fof(f130,plain,(
% 2.36/0.67    spl2_5 <=> v2_pre_topc(sK0)),
% 2.36/0.67    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 2.36/0.67  fof(f606,plain,(
% 2.36/0.67    spl2_47 <=> sK1 = k2_pre_topc(sK0,sK1)),
% 2.36/0.67    introduced(avatar_definition,[new_symbols(naming,[spl2_47])])).
% 2.36/0.67  fof(f617,plain,(
% 2.36/0.67    v4_pre_topc(sK1,sK0) | (~spl2_3 | ~spl2_4 | ~spl2_5 | ~spl2_47)),
% 2.36/0.67    inference(unit_resulting_resolution,[],[f127,f132,f122,f608,f75])).
% 2.36/0.67  fof(f75,plain,(
% 2.36/0.67    ( ! [X0,X1] : (~v2_pre_topc(X0) | k2_pre_topc(X0,X1) != X1 | v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.36/0.67    inference(cnf_transformation,[],[f39])).
% 2.36/0.67  fof(f39,plain,(
% 2.36/0.67    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.36/0.67    inference(flattening,[],[f38])).
% 2.36/0.67  fof(f38,plain,(
% 2.36/0.67    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.36/0.67    inference(ennf_transformation,[],[f26])).
% 2.36/0.67  fof(f26,axiom,(
% 2.36/0.67    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 2.36/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).
% 2.36/0.67  fof(f608,plain,(
% 2.36/0.67    sK1 = k2_pre_topc(sK0,sK1) | ~spl2_47),
% 2.36/0.67    inference(avatar_component_clause,[],[f606])).
% 2.36/0.67  fof(f132,plain,(
% 2.36/0.67    v2_pre_topc(sK0) | ~spl2_5),
% 2.36/0.67    inference(avatar_component_clause,[],[f130])).
% 2.36/0.67  fof(f127,plain,(
% 2.36/0.67    l1_pre_topc(sK0) | ~spl2_4),
% 2.36/0.67    inference(avatar_component_clause,[],[f125])).
% 2.36/0.67  fof(f1824,plain,(
% 2.36/0.67    spl2_181 | ~spl2_3 | ~spl2_52),
% 2.36/0.67    inference(avatar_split_clause,[],[f1818,f662,f120,f1821])).
% 2.36/0.67  fof(f1818,plain,(
% 2.36/0.67    r1_tarski(k1_tops_1(sK0,sK1),sK1) | (~spl2_3 | ~spl2_52)),
% 2.36/0.67    inference(superposition,[],[f1015,f664])).
% 2.36/0.67  fof(f1015,plain,(
% 2.36/0.67    ( ! [X4] : (r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,X4),sK1)) ) | ~spl2_3),
% 2.36/0.67    inference(superposition,[],[f100,f364])).
% 2.36/0.67  fof(f100,plain,(
% 2.36/0.67    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0)) )),
% 2.36/0.67    inference(definition_unfolding,[],[f77,f99])).
% 2.36/0.67  fof(f77,plain,(
% 2.36/0.67    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 2.36/0.67    inference(cnf_transformation,[],[f7])).
% 2.36/0.67  fof(f7,axiom,(
% 2.36/0.67    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 2.36/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 2.36/0.67  fof(f1819,plain,(
% 2.36/0.67    spl2_48 | ~spl2_2 | ~spl2_3),
% 2.36/0.67    inference(avatar_split_clause,[],[f1817,f120,f114,f611])).
% 2.36/0.67  fof(f1817,plain,(
% 2.36/0.67    r1_tarski(k2_tops_1(sK0,sK1),sK1) | (~spl2_2 | ~spl2_3)),
% 2.36/0.67    inference(superposition,[],[f1015,f115])).
% 2.36/0.67  fof(f115,plain,(
% 2.36/0.67    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~spl2_2),
% 2.36/0.67    inference(avatar_component_clause,[],[f114])).
% 2.36/0.67  fof(f804,plain,(
% 2.36/0.67    spl2_27 | ~spl2_3 | ~spl2_10),
% 2.36/0.67    inference(avatar_split_clause,[],[f792,f228,f120,f437])).
% 2.36/0.67  fof(f437,plain,(
% 2.36/0.67    spl2_27 <=> k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 2.36/0.67    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).
% 2.36/0.67  fof(f228,plain,(
% 2.36/0.67    spl2_10 <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.36/0.67    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 2.36/0.67  fof(f792,plain,(
% 2.36/0.67    k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | (~spl2_3 | ~spl2_10)),
% 2.36/0.67    inference(unit_resulting_resolution,[],[f122,f230,f98])).
% 2.36/0.67  fof(f98,plain,(
% 2.36/0.67    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)) )),
% 2.36/0.67    inference(cnf_transformation,[],[f55])).
% 2.36/0.67  fof(f55,plain,(
% 2.36/0.67    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.36/0.67    inference(flattening,[],[f54])).
% 2.36/0.67  fof(f54,plain,(
% 2.36/0.67    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 2.36/0.67    inference(ennf_transformation,[],[f19])).
% 2.36/0.67  fof(f19,axiom,(
% 2.36/0.67    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 2.36/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 2.36/0.67  fof(f230,plain,(
% 2.36/0.67    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_10),
% 2.36/0.67    inference(avatar_component_clause,[],[f228])).
% 2.36/0.67  fof(f760,plain,(
% 2.36/0.67    spl2_10 | ~spl2_11),
% 2.36/0.67    inference(avatar_split_clause,[],[f757,f241,f228])).
% 2.36/0.67  fof(f241,plain,(
% 2.36/0.67    spl2_11 <=> r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0))),
% 2.36/0.67    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 2.36/0.67  fof(f757,plain,(
% 2.36/0.67    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_11),
% 2.36/0.67    inference(unit_resulting_resolution,[],[f243,f90])).
% 2.36/0.67  fof(f243,plain,(
% 2.36/0.67    r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0)) | ~spl2_11),
% 2.36/0.67    inference(avatar_component_clause,[],[f241])).
% 2.36/0.67  fof(f703,plain,(
% 2.36/0.67    spl2_57 | ~spl2_3 | ~spl2_4),
% 2.36/0.67    inference(avatar_split_clause,[],[f697,f125,f120,f700])).
% 2.36/0.67  fof(f700,plain,(
% 2.36/0.67    spl2_57 <=> k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 2.36/0.67    introduced(avatar_definition,[new_symbols(naming,[spl2_57])])).
% 2.36/0.67  fof(f697,plain,(
% 2.36/0.67    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | (~spl2_3 | ~spl2_4)),
% 2.36/0.67    inference(unit_resulting_resolution,[],[f127,f122,f73])).
% 2.36/0.67  fof(f73,plain,(
% 2.36/0.67    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))) )),
% 2.36/0.67    inference(cnf_transformation,[],[f37])).
% 2.36/0.67  fof(f37,plain,(
% 2.36/0.67    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.36/0.67    inference(ennf_transformation,[],[f28])).
% 2.36/0.67  fof(f28,axiom,(
% 2.36/0.67    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 2.36/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).
% 2.36/0.67  fof(f665,plain,(
% 2.36/0.67    spl2_52 | ~spl2_3 | ~spl2_4),
% 2.36/0.67    inference(avatar_split_clause,[],[f659,f125,f120,f662])).
% 2.36/0.67  fof(f659,plain,(
% 2.36/0.67    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | (~spl2_3 | ~spl2_4)),
% 2.36/0.67    inference(unit_resulting_resolution,[],[f127,f122,f72])).
% 2.36/0.67  fof(f72,plain,(
% 2.36/0.67    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))) )),
% 2.36/0.67    inference(cnf_transformation,[],[f36])).
% 2.36/0.67  fof(f36,plain,(
% 2.36/0.67    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.36/0.67    inference(ennf_transformation,[],[f30])).
% 2.36/0.67  fof(f30,axiom,(
% 2.36/0.67    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 2.36/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).
% 2.36/0.67  fof(f642,plain,(
% 2.36/0.67    spl2_11 | ~spl2_6 | ~spl2_48),
% 2.36/0.67    inference(avatar_split_clause,[],[f626,f611,f146,f241])).
% 2.36/0.67  fof(f146,plain,(
% 2.36/0.67    spl2_6 <=> r1_tarski(sK1,u1_struct_0(sK0))),
% 2.36/0.67    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 2.36/0.67  fof(f626,plain,(
% 2.36/0.67    r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0)) | (~spl2_6 | ~spl2_48)),
% 2.36/0.67    inference(unit_resulting_resolution,[],[f148,f613,f97])).
% 2.36/0.67  fof(f97,plain,(
% 2.36/0.67    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X2) | r1_tarski(X0,X2)) )),
% 2.36/0.67    inference(cnf_transformation,[],[f53])).
% 2.36/0.67  fof(f53,plain,(
% 2.36/0.67    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 2.36/0.67    inference(flattening,[],[f52])).
% 2.36/0.67  fof(f52,plain,(
% 2.36/0.67    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 2.36/0.67    inference(ennf_transformation,[],[f6])).
% 2.36/0.67  fof(f6,axiom,(
% 2.36/0.67    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 2.36/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 2.36/0.67  fof(f148,plain,(
% 2.36/0.67    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl2_6),
% 2.36/0.67    inference(avatar_component_clause,[],[f146])).
% 2.36/0.67  fof(f150,plain,(
% 2.36/0.67    spl2_6 | ~spl2_3),
% 2.36/0.67    inference(avatar_split_clause,[],[f142,f120,f146])).
% 2.36/0.67  fof(f142,plain,(
% 2.36/0.67    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl2_3),
% 2.36/0.67    inference(resolution,[],[f89,f122])).
% 2.36/0.67  fof(f89,plain,(
% 2.36/0.67    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 2.36/0.67    inference(cnf_transformation,[],[f61])).
% 2.36/0.67  fof(f133,plain,(
% 2.36/0.67    spl2_5),
% 2.36/0.67    inference(avatar_split_clause,[],[f62,f130])).
% 2.36/0.67  fof(f62,plain,(
% 2.36/0.67    v2_pre_topc(sK0)),
% 2.36/0.67    inference(cnf_transformation,[],[f60])).
% 2.36/0.67  fof(f60,plain,(
% 2.36/0.67    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 2.36/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f57,f59,f58])).
% 2.36/0.67  fof(f58,plain,(
% 2.36/0.67    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 2.36/0.67    introduced(choice_axiom,[])).
% 2.36/0.67  fof(f59,plain,(
% 2.36/0.67    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.36/0.67    introduced(choice_axiom,[])).
% 2.36/0.67  fof(f57,plain,(
% 2.36/0.67    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.36/0.67    inference(flattening,[],[f56])).
% 2.36/0.67  fof(f56,plain,(
% 2.36/0.67    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.36/0.67    inference(nnf_transformation,[],[f34])).
% 2.36/0.67  fof(f34,plain,(
% 2.36/0.67    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.36/0.67    inference(flattening,[],[f33])).
% 2.36/0.67  fof(f33,plain,(
% 2.36/0.67    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 2.36/0.67    inference(ennf_transformation,[],[f32])).
% 2.36/0.67  fof(f32,negated_conjecture,(
% 2.36/0.67    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 2.36/0.67    inference(negated_conjecture,[],[f31])).
% 2.36/0.67  fof(f31,conjecture,(
% 2.36/0.67    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 2.36/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).
% 2.36/0.67  fof(f128,plain,(
% 2.36/0.67    spl2_4),
% 2.36/0.67    inference(avatar_split_clause,[],[f63,f125])).
% 2.36/0.67  fof(f63,plain,(
% 2.36/0.67    l1_pre_topc(sK0)),
% 2.36/0.67    inference(cnf_transformation,[],[f60])).
% 2.36/0.67  fof(f123,plain,(
% 2.36/0.67    spl2_3),
% 2.36/0.67    inference(avatar_split_clause,[],[f64,f120])).
% 2.36/0.67  fof(f64,plain,(
% 2.36/0.67    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.36/0.67    inference(cnf_transformation,[],[f60])).
% 2.36/0.67  fof(f118,plain,(
% 2.36/0.67    spl2_1 | spl2_2),
% 2.36/0.67    inference(avatar_split_clause,[],[f65,f114,f110])).
% 2.36/0.67  fof(f65,plain,(
% 2.36/0.67    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)),
% 2.36/0.67    inference(cnf_transformation,[],[f60])).
% 2.36/0.67  fof(f117,plain,(
% 2.36/0.67    ~spl2_1 | ~spl2_2),
% 2.36/0.67    inference(avatar_split_clause,[],[f66,f114,f110])).
% 2.36/0.67  fof(f66,plain,(
% 2.36/0.67    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)),
% 2.36/0.67    inference(cnf_transformation,[],[f60])).
% 2.36/0.67  % SZS output end Proof for theBenchmark
% 2.36/0.67  % (4621)------------------------------
% 2.36/0.67  % (4621)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.36/0.67  % (4621)Termination reason: Refutation
% 2.36/0.67  
% 2.36/0.67  % (4621)Memory used [KB]: 8699
% 2.36/0.67  % (4621)Time elapsed: 0.234 s
% 2.36/0.67  % (4621)------------------------------
% 2.36/0.67  % (4621)------------------------------
% 2.36/0.67  % (4614)Success in time 0.307 s
%------------------------------------------------------------------------------
