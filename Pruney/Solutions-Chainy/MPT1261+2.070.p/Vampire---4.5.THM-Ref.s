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
% DateTime   : Thu Dec  3 13:11:58 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  143 ( 274 expanded)
%              Number of leaves         :   40 ( 120 expanded)
%              Depth                    :    9
%              Number of atoms          :  380 ( 807 expanded)
%              Number of equality atoms :   93 ( 219 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1637,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f68,f73,f78,f103,f104,f110,f116,f186,f194,f204,f213,f232,f237,f279,f497,f514,f953,f1495,f1496,f1497,f1634,f1636])).

fof(f1636,plain,
    ( k1_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) != k5_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k5_xboole_0(sK1,k2_tops_1(sK0,sK1)))
    | k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1634,plain,
    ( spl2_74
    | ~ spl2_2
    | ~ spl2_63
    | ~ spl2_71 ),
    inference(avatar_split_clause,[],[f1629,f1492,f1274,f70,f1631])).

fof(f1631,plain,
    ( spl2_74
  <=> k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_74])])).

fof(f70,plain,
    ( spl2_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f1274,plain,
    ( spl2_63
  <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_63])])).

fof(f1492,plain,
    ( spl2_71
  <=> sK1 = k2_pre_topc(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_71])])).

fof(f1629,plain,
    ( k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_2
    | ~ spl2_63
    | ~ spl2_71 ),
    inference(forward_demodulation,[],[f1627,f1494])).

fof(f1494,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl2_71 ),
    inference(avatar_component_clause,[],[f1492])).

fof(f1627,plain,
    ( k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_tops_1(sK0,k2_pre_topc(sK0,sK1)))
    | ~ spl2_2
    | ~ spl2_63 ),
    inference(unit_resulting_resolution,[],[f72,f1275,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).

fof(f1275,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_63 ),
    inference(avatar_component_clause,[],[f1274])).

fof(f72,plain,
    ( l1_pre_topc(sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f70])).

fof(f1497,plain,
    ( sK1 != k2_pre_topc(sK0,sK1)
    | m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1496,plain,
    ( sK1 != k2_pre_topc(sK0,sK1)
    | v4_pre_topc(sK1,sK0)
    | ~ v4_pre_topc(k2_pre_topc(sK0,sK1),sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1495,plain,
    ( spl2_71
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_53 ),
    inference(avatar_split_clause,[],[f1490,f950,f75,f70,f1492])).

fof(f75,plain,
    ( spl2_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f950,plain,
    ( spl2_53
  <=> sK1 = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_53])])).

fof(f1490,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_53 ),
    inference(forward_demodulation,[],[f1482,f952])).

fof(f952,plain,
    ( sK1 = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_53 ),
    inference(avatar_component_clause,[],[f950])).

fof(f1482,plain,
    ( k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f72,f77,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

fof(f77,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f75])).

fof(f953,plain,
    ( spl2_53
    | ~ spl2_3
    | ~ spl2_7
    | ~ spl2_21 ),
    inference(avatar_split_clause,[],[f942,f229,f113,f75,f950])).

fof(f113,plain,
    ( spl2_7
  <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f229,plain,
    ( spl2_21
  <=> sK1 = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).

fof(f942,plain,
    ( sK1 = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_7
    | ~ spl2_21 ),
    inference(forward_demodulation,[],[f894,f231])).

fof(f231,plain,
    ( sK1 = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_21 ),
    inference(avatar_component_clause,[],[f229])).

fof(f894,plain,
    ( k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_7 ),
    inference(unit_resulting_resolution,[],[f77,f115,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2)) ) ),
    inference(definition_unfolding,[],[f56,f49])).

fof(f49,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f115,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f113])).

fof(f514,plain,
    ( spl2_38
    | ~ spl2_19
    | ~ spl2_25
    | ~ spl2_37 ),
    inference(avatar_split_clause,[],[f505,f495,f276,f210,f511])).

fof(f511,plain,
    ( spl2_38
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k5_xboole_0(sK1,k2_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_38])])).

fof(f210,plain,
    ( spl2_19
  <=> k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f276,plain,
    ( spl2_25
  <=> k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).

fof(f495,plain,
    ( spl2_37
  <=> ! [X0] : k1_setfam_1(k2_tarski(sK1,X0)) = k7_subset_1(u1_struct_0(sK0),sK1,k7_subset_1(u1_struct_0(sK0),sK1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_37])])).

fof(f505,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k5_xboole_0(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_19
    | ~ spl2_25
    | ~ spl2_37 ),
    inference(forward_demodulation,[],[f499,f212])).

fof(f212,plain,
    ( k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_19 ),
    inference(avatar_component_clause,[],[f210])).

fof(f499,plain,
    ( k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k7_subset_1(u1_struct_0(sK0),sK1,k5_xboole_0(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_25
    | ~ spl2_37 ),
    inference(superposition,[],[f496,f278])).

fof(f278,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_25 ),
    inference(avatar_component_clause,[],[f276])).

fof(f496,plain,
    ( ! [X0] : k1_setfam_1(k2_tarski(sK1,X0)) = k7_subset_1(u1_struct_0(sK0),sK1,k7_subset_1(u1_struct_0(sK0),sK1,X0))
    | ~ spl2_37 ),
    inference(avatar_component_clause,[],[f495])).

fof(f497,plain,
    ( spl2_37
    | ~ spl2_16 ),
    inference(avatar_split_clause,[],[f295,f184,f495])).

fof(f184,plain,
    ( spl2_16
  <=> ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f295,plain,
    ( ! [X0] : k1_setfam_1(k2_tarski(sK1,X0)) = k7_subset_1(u1_struct_0(sK0),sK1,k7_subset_1(u1_struct_0(sK0),sK1,X0))
    | ~ spl2_16 ),
    inference(forward_demodulation,[],[f286,f185])).

fof(f185,plain,
    ( ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X0)))
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f184])).

fof(f286,plain,
    ( ! [X0] : k1_setfam_1(k2_tarski(sK1,X0)) = k7_subset_1(u1_struct_0(sK0),sK1,k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X0))))
    | ~ spl2_16 ),
    inference(superposition,[],[f60,f185])).

fof(f60,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))))) ),
    inference(definition_unfolding,[],[f51,f48,f57,f57])).

fof(f57,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f50,f48])).

fof(f50,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f48,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f51,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f279,plain,
    ( spl2_25
    | ~ spl2_16
    | ~ spl2_19 ),
    inference(avatar_split_clause,[],[f247,f210,f184,f276])).

fof(f247,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_16
    | ~ spl2_19 ),
    inference(superposition,[],[f185,f212])).

fof(f237,plain,
    ( ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4
    | spl2_18 ),
    inference(avatar_contradiction_clause,[],[f236])).

fof(f236,plain,
    ( $false
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4
    | spl2_18 ),
    inference(global_subsumption,[],[f202,f234])).

fof(f234,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(unit_resulting_resolution,[],[f72,f77,f98,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k2_tops_1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => r1_tarski(k2_tops_1(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_tops_1)).

fof(f98,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl2_4
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f202,plain,
    ( ~ r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | spl2_18 ),
    inference(avatar_component_clause,[],[f201])).

fof(f201,plain,
    ( spl2_18
  <=> r1_tarski(k2_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f232,plain,
    ( spl2_21
    | ~ spl2_19 ),
    inference(avatar_split_clause,[],[f216,f210,f229])).

fof(f216,plain,
    ( sK1 = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_19 ),
    inference(superposition,[],[f59,f212])).

fof(f59,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,k1_setfam_1(k2_tarski(X0,X1)))) = X0 ),
    inference(definition_unfolding,[],[f47,f49,f48])).

fof(f47,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f213,plain,
    ( spl2_19
    | ~ spl2_18 ),
    inference(avatar_split_clause,[],[f207,f201,f210])).

fof(f207,plain,
    ( k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_18 ),
    inference(forward_demodulation,[],[f205,f46])).

fof(f46,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f205,plain,
    ( k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),sK1))
    | ~ spl2_18 ),
    inference(unit_resulting_resolution,[],[f203,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_setfam_1(k2_tarski(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f52,f48])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f203,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_18 ),
    inference(avatar_component_clause,[],[f201])).

fof(f204,plain,
    ( spl2_18
    | ~ spl2_5
    | ~ spl2_17 ),
    inference(avatar_split_clause,[],[f197,f192,f100,f201])).

fof(f100,plain,
    ( spl2_5
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f192,plain,
    ( spl2_17
  <=> ! [X0] : r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,X0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f197,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_5
    | ~ spl2_17 ),
    inference(superposition,[],[f193,f102])).

fof(f102,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f100])).

fof(f193,plain,
    ( ! [X0] : r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,X0),sK1)
    | ~ spl2_17 ),
    inference(avatar_component_clause,[],[f192])).

fof(f194,plain,
    ( spl2_17
    | ~ spl2_16 ),
    inference(avatar_split_clause,[],[f189,f184,f192])).

fof(f189,plain,
    ( ! [X0] : r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,X0),sK1)
    | ~ spl2_16 ),
    inference(superposition,[],[f58,f185])).

fof(f58,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0) ),
    inference(definition_unfolding,[],[f45,f57])).

fof(f45,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f186,plain,
    ( spl2_16
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f172,f75,f184])).

fof(f172,plain,
    ( ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X0)))
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f77,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) ) ),
    inference(definition_unfolding,[],[f55,f57])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f116,plain,
    ( spl2_7
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f111,f75,f70,f113])).

fof(f111,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f72,f77,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(f110,plain,
    ( spl2_6
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f105,f75,f70,f65,f107])).

fof(f107,plain,
    ( spl2_6
  <=> v4_pre_topc(k2_pre_topc(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f65,plain,
    ( spl2_1
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f105,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,sK1),sK0)
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f67,f72,f77,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_pre_topc(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_tops_1)).

fof(f67,plain,
    ( v2_pre_topc(sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f65])).

fof(f104,plain,
    ( ~ spl2_4
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f41,f100,f96])).

fof(f41,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | ~ v4_pre_topc(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | v4_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f33,f35,f34])).

fof(f34,plain,
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

fof(f35,plain,
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

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).

fof(f103,plain,
    ( spl2_4
    | spl2_5 ),
    inference(avatar_split_clause,[],[f40,f100,f96])).

fof(f40,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f78,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f39,f75])).

fof(f39,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f36])).

fof(f73,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f38,f70])).

fof(f38,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f68,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f37,f65])).

fof(f37,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:43:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.41  % (5103)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.45  % (5103)Refutation found. Thanks to Tanya!
% 0.21/0.45  % SZS status Theorem for theBenchmark
% 0.21/0.45  % SZS output start Proof for theBenchmark
% 0.21/0.45  fof(f1637,plain,(
% 0.21/0.45    $false),
% 0.21/0.45    inference(avatar_sat_refutation,[],[f68,f73,f78,f103,f104,f110,f116,f186,f194,f204,f213,f232,f237,f279,f497,f514,f953,f1495,f1496,f1497,f1634,f1636])).
% 0.21/0.45  fof(f1636,plain,(
% 0.21/0.45    k1_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) != k5_xboole_0(sK1,k2_tops_1(sK0,sK1)) | k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k5_xboole_0(sK1,k2_tops_1(sK0,sK1))) | k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),
% 0.21/0.45    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.45  fof(f1634,plain,(
% 0.21/0.45    spl2_74 | ~spl2_2 | ~spl2_63 | ~spl2_71),
% 0.21/0.45    inference(avatar_split_clause,[],[f1629,f1492,f1274,f70,f1631])).
% 0.21/0.45  fof(f1631,plain,(
% 0.21/0.45    spl2_74 <=> k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_74])])).
% 0.21/0.45  fof(f70,plain,(
% 0.21/0.45    spl2_2 <=> l1_pre_topc(sK0)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.45  fof(f1274,plain,(
% 0.21/0.45    spl2_63 <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_63])])).
% 0.21/0.45  fof(f1492,plain,(
% 0.21/0.45    spl2_71 <=> sK1 = k2_pre_topc(sK0,sK1)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_71])])).
% 0.21/0.45  fof(f1629,plain,(
% 0.21/0.45    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | (~spl2_2 | ~spl2_63 | ~spl2_71)),
% 0.21/0.45    inference(forward_demodulation,[],[f1627,f1494])).
% 0.21/0.45  fof(f1494,plain,(
% 0.21/0.45    sK1 = k2_pre_topc(sK0,sK1) | ~spl2_71),
% 0.21/0.45    inference(avatar_component_clause,[],[f1492])).
% 0.21/0.45  fof(f1627,plain,(
% 0.21/0.45    k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_tops_1(sK0,k2_pre_topc(sK0,sK1))) | (~spl2_2 | ~spl2_63)),
% 0.21/0.45    inference(unit_resulting_resolution,[],[f72,f1275,f43])).
% 0.21/0.45  fof(f43,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f21])).
% 0.21/0.45  fof(f21,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.45    inference(ennf_transformation,[],[f15])).
% 0.21/0.45  fof(f15,axiom,(
% 0.21/0.45    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).
% 0.21/0.45  fof(f1275,plain,(
% 0.21/0.45    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_63),
% 0.21/0.45    inference(avatar_component_clause,[],[f1274])).
% 0.21/0.45  fof(f72,plain,(
% 0.21/0.45    l1_pre_topc(sK0) | ~spl2_2),
% 0.21/0.45    inference(avatar_component_clause,[],[f70])).
% 0.21/0.45  fof(f1497,plain,(
% 0.21/0.45    sK1 != k2_pre_topc(sK0,sK1) | m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.45    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.45  fof(f1496,plain,(
% 0.21/0.45    sK1 != k2_pre_topc(sK0,sK1) | v4_pre_topc(sK1,sK0) | ~v4_pre_topc(k2_pre_topc(sK0,sK1),sK0)),
% 0.21/0.45    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.45  fof(f1495,plain,(
% 0.21/0.45    spl2_71 | ~spl2_2 | ~spl2_3 | ~spl2_53),
% 0.21/0.45    inference(avatar_split_clause,[],[f1490,f950,f75,f70,f1492])).
% 0.21/0.45  fof(f75,plain,(
% 0.21/0.45    spl2_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.45  fof(f950,plain,(
% 0.21/0.45    spl2_53 <=> sK1 = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_53])])).
% 0.21/0.45  fof(f1490,plain,(
% 0.21/0.45    sK1 = k2_pre_topc(sK0,sK1) | (~spl2_2 | ~spl2_3 | ~spl2_53)),
% 0.21/0.45    inference(forward_demodulation,[],[f1482,f952])).
% 0.21/0.45  fof(f952,plain,(
% 0.21/0.45    sK1 = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | ~spl2_53),
% 0.21/0.45    inference(avatar_component_clause,[],[f950])).
% 0.21/0.45  fof(f1482,plain,(
% 0.21/0.45    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | (~spl2_2 | ~spl2_3)),
% 0.21/0.45    inference(unit_resulting_resolution,[],[f72,f77,f42])).
% 0.21/0.45  fof(f42,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f20])).
% 0.21/0.45  fof(f20,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.45    inference(ennf_transformation,[],[f13])).
% 0.21/0.45  fof(f13,axiom,(
% 0.21/0.45    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).
% 0.21/0.45  fof(f77,plain,(
% 0.21/0.45    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_3),
% 0.21/0.45    inference(avatar_component_clause,[],[f75])).
% 0.21/0.45  fof(f953,plain,(
% 0.21/0.45    spl2_53 | ~spl2_3 | ~spl2_7 | ~spl2_21),
% 0.21/0.45    inference(avatar_split_clause,[],[f942,f229,f113,f75,f950])).
% 0.21/0.45  fof(f113,plain,(
% 0.21/0.45    spl2_7 <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.21/0.45  fof(f229,plain,(
% 0.21/0.45    spl2_21 <=> sK1 = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).
% 0.21/0.45  fof(f942,plain,(
% 0.21/0.45    sK1 = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | (~spl2_3 | ~spl2_7 | ~spl2_21)),
% 0.21/0.45    inference(forward_demodulation,[],[f894,f231])).
% 0.21/0.45  fof(f231,plain,(
% 0.21/0.45    sK1 = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | ~spl2_21),
% 0.21/0.45    inference(avatar_component_clause,[],[f229])).
% 0.21/0.45  fof(f894,plain,(
% 0.21/0.45    k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | (~spl2_3 | ~spl2_7)),
% 0.21/0.45    inference(unit_resulting_resolution,[],[f77,f115,f63])).
% 0.21/0.45  fof(f63,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))) )),
% 0.21/0.45    inference(definition_unfolding,[],[f56,f49])).
% 0.21/0.45  fof(f49,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f7])).
% 0.21/0.45  fof(f7,axiom,(
% 0.21/0.45    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.21/0.45  fof(f56,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f31])).
% 0.21/0.45  fof(f31,plain,(
% 0.21/0.45    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.45    inference(flattening,[],[f30])).
% 0.21/0.45  fof(f30,plain,(
% 0.21/0.45    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.21/0.45    inference(ennf_transformation,[],[f8])).
% 0.21/0.45  fof(f8,axiom,(
% 0.21/0.45    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 0.21/0.45  fof(f115,plain,(
% 0.21/0.45    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_7),
% 0.21/0.45    inference(avatar_component_clause,[],[f113])).
% 0.21/0.45  fof(f514,plain,(
% 0.21/0.45    spl2_38 | ~spl2_19 | ~spl2_25 | ~spl2_37),
% 0.21/0.45    inference(avatar_split_clause,[],[f505,f495,f276,f210,f511])).
% 0.21/0.45  fof(f511,plain,(
% 0.21/0.45    spl2_38 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k5_xboole_0(sK1,k2_tops_1(sK0,sK1)))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_38])])).
% 0.21/0.45  fof(f210,plain,(
% 0.21/0.45    spl2_19 <=> k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1)))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 0.21/0.45  fof(f276,plain,(
% 0.21/0.45    spl2_25 <=> k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).
% 0.21/0.45  fof(f495,plain,(
% 0.21/0.45    spl2_37 <=> ! [X0] : k1_setfam_1(k2_tarski(sK1,X0)) = k7_subset_1(u1_struct_0(sK0),sK1,k7_subset_1(u1_struct_0(sK0),sK1,X0))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_37])])).
% 0.21/0.45  fof(f505,plain,(
% 0.21/0.45    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k5_xboole_0(sK1,k2_tops_1(sK0,sK1))) | (~spl2_19 | ~spl2_25 | ~spl2_37)),
% 0.21/0.45    inference(forward_demodulation,[],[f499,f212])).
% 0.21/0.45  fof(f212,plain,(
% 0.21/0.45    k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | ~spl2_19),
% 0.21/0.45    inference(avatar_component_clause,[],[f210])).
% 0.21/0.45  fof(f499,plain,(
% 0.21/0.45    k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k7_subset_1(u1_struct_0(sK0),sK1,k5_xboole_0(sK1,k2_tops_1(sK0,sK1))) | (~spl2_25 | ~spl2_37)),
% 0.21/0.45    inference(superposition,[],[f496,f278])).
% 0.21/0.45  fof(f278,plain,(
% 0.21/0.45    k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl2_25),
% 0.21/0.45    inference(avatar_component_clause,[],[f276])).
% 0.21/0.45  fof(f496,plain,(
% 0.21/0.45    ( ! [X0] : (k1_setfam_1(k2_tarski(sK1,X0)) = k7_subset_1(u1_struct_0(sK0),sK1,k7_subset_1(u1_struct_0(sK0),sK1,X0))) ) | ~spl2_37),
% 0.21/0.45    inference(avatar_component_clause,[],[f495])).
% 0.21/0.45  fof(f497,plain,(
% 0.21/0.45    spl2_37 | ~spl2_16),
% 0.21/0.45    inference(avatar_split_clause,[],[f295,f184,f495])).
% 0.21/0.45  fof(f184,plain,(
% 0.21/0.45    spl2_16 <=> ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X0)))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 0.21/0.45  fof(f295,plain,(
% 0.21/0.45    ( ! [X0] : (k1_setfam_1(k2_tarski(sK1,X0)) = k7_subset_1(u1_struct_0(sK0),sK1,k7_subset_1(u1_struct_0(sK0),sK1,X0))) ) | ~spl2_16),
% 0.21/0.45    inference(forward_demodulation,[],[f286,f185])).
% 0.21/0.45  fof(f185,plain,(
% 0.21/0.45    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),sK1,X0) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X0)))) ) | ~spl2_16),
% 0.21/0.45    inference(avatar_component_clause,[],[f184])).
% 0.21/0.45  fof(f286,plain,(
% 0.21/0.45    ( ! [X0] : (k1_setfam_1(k2_tarski(sK1,X0)) = k7_subset_1(u1_struct_0(sK0),sK1,k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X0))))) ) | ~spl2_16),
% 0.21/0.45    inference(superposition,[],[f60,f185])).
% 0.21/0.45  fof(f60,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))))))) )),
% 0.21/0.45    inference(definition_unfolding,[],[f51,f48,f57,f57])).
% 0.21/0.45  fof(f57,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 0.21/0.45    inference(definition_unfolding,[],[f50,f48])).
% 0.21/0.45  fof(f50,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f1])).
% 0.21/0.45  fof(f1,axiom,(
% 0.21/0.45    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.45  fof(f48,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f10])).
% 0.21/0.45  fof(f10,axiom,(
% 0.21/0.45    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.21/0.45  fof(f51,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f5])).
% 0.21/0.45  fof(f5,axiom,(
% 0.21/0.45    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.45  fof(f279,plain,(
% 0.21/0.45    spl2_25 | ~spl2_16 | ~spl2_19),
% 0.21/0.45    inference(avatar_split_clause,[],[f247,f210,f184,f276])).
% 0.21/0.45  fof(f247,plain,(
% 0.21/0.45    k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k2_tops_1(sK0,sK1)) | (~spl2_16 | ~spl2_19)),
% 0.21/0.45    inference(superposition,[],[f185,f212])).
% 0.21/0.45  fof(f237,plain,(
% 0.21/0.45    ~spl2_2 | ~spl2_3 | ~spl2_4 | spl2_18),
% 0.21/0.45    inference(avatar_contradiction_clause,[],[f236])).
% 0.21/0.45  fof(f236,plain,(
% 0.21/0.45    $false | (~spl2_2 | ~spl2_3 | ~spl2_4 | spl2_18)),
% 0.21/0.45    inference(global_subsumption,[],[f202,f234])).
% 0.21/0.45  fof(f234,plain,(
% 0.21/0.45    r1_tarski(k2_tops_1(sK0,sK1),sK1) | (~spl2_2 | ~spl2_3 | ~spl2_4)),
% 0.21/0.45    inference(unit_resulting_resolution,[],[f72,f77,f98,f44])).
% 0.21/0.45  fof(f44,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k2_tops_1(X0,X1),X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f23])).
% 0.21/0.45  fof(f23,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : (r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.45    inference(flattening,[],[f22])).
% 0.21/0.45  fof(f22,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : ((r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.45    inference(ennf_transformation,[],[f14])).
% 0.21/0.45  fof(f14,axiom,(
% 0.21/0.45    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => r1_tarski(k2_tops_1(X0,X1),X1))))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_tops_1)).
% 0.21/0.45  fof(f98,plain,(
% 0.21/0.45    v4_pre_topc(sK1,sK0) | ~spl2_4),
% 0.21/0.45    inference(avatar_component_clause,[],[f96])).
% 0.21/0.45  fof(f96,plain,(
% 0.21/0.45    spl2_4 <=> v4_pre_topc(sK1,sK0)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.45  fof(f202,plain,(
% 0.21/0.45    ~r1_tarski(k2_tops_1(sK0,sK1),sK1) | spl2_18),
% 0.21/0.45    inference(avatar_component_clause,[],[f201])).
% 0.21/0.45  fof(f201,plain,(
% 0.21/0.45    spl2_18 <=> r1_tarski(k2_tops_1(sK0,sK1),sK1)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 0.21/0.45  fof(f232,plain,(
% 0.21/0.45    spl2_21 | ~spl2_19),
% 0.21/0.45    inference(avatar_split_clause,[],[f216,f210,f229])).
% 0.21/0.45  fof(f216,plain,(
% 0.21/0.45    sK1 = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | ~spl2_19),
% 0.21/0.45    inference(superposition,[],[f59,f212])).
% 0.21/0.45  fof(f59,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,k1_setfam_1(k2_tarski(X0,X1)))) = X0) )),
% 0.21/0.45    inference(definition_unfolding,[],[f47,f49,f48])).
% 0.21/0.45  fof(f47,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 0.21/0.45    inference(cnf_transformation,[],[f2])).
% 0.21/0.45  fof(f2,axiom,(
% 0.21/0.45    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).
% 0.21/0.45  fof(f213,plain,(
% 0.21/0.45    spl2_19 | ~spl2_18),
% 0.21/0.45    inference(avatar_split_clause,[],[f207,f201,f210])).
% 0.21/0.45  fof(f207,plain,(
% 0.21/0.45    k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | ~spl2_18),
% 0.21/0.45    inference(forward_demodulation,[],[f205,f46])).
% 0.21/0.45  fof(f46,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f6])).
% 0.21/0.45  fof(f6,axiom,(
% 0.21/0.45    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.21/0.45  fof(f205,plain,(
% 0.21/0.45    k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),sK1)) | ~spl2_18),
% 0.21/0.45    inference(unit_resulting_resolution,[],[f203,f61])).
% 0.21/0.45  fof(f61,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_setfam_1(k2_tarski(X0,X1)) = X0) )),
% 0.21/0.45    inference(definition_unfolding,[],[f52,f48])).
% 0.21/0.45  fof(f52,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f24])).
% 0.21/0.45  fof(f24,plain,(
% 0.21/0.45    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.45    inference(ennf_transformation,[],[f3])).
% 0.21/0.45  fof(f3,axiom,(
% 0.21/0.45    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.21/0.45  fof(f203,plain,(
% 0.21/0.45    r1_tarski(k2_tops_1(sK0,sK1),sK1) | ~spl2_18),
% 0.21/0.45    inference(avatar_component_clause,[],[f201])).
% 0.21/0.45  fof(f204,plain,(
% 0.21/0.45    spl2_18 | ~spl2_5 | ~spl2_17),
% 0.21/0.45    inference(avatar_split_clause,[],[f197,f192,f100,f201])).
% 0.21/0.45  fof(f100,plain,(
% 0.21/0.45    spl2_5 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.45  fof(f192,plain,(
% 0.21/0.45    spl2_17 <=> ! [X0] : r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,X0),sK1)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 0.21/0.45  fof(f197,plain,(
% 0.21/0.45    r1_tarski(k2_tops_1(sK0,sK1),sK1) | (~spl2_5 | ~spl2_17)),
% 0.21/0.45    inference(superposition,[],[f193,f102])).
% 0.21/0.45  fof(f102,plain,(
% 0.21/0.45    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~spl2_5),
% 0.21/0.45    inference(avatar_component_clause,[],[f100])).
% 0.21/0.45  fof(f193,plain,(
% 0.21/0.45    ( ! [X0] : (r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,X0),sK1)) ) | ~spl2_17),
% 0.21/0.45    inference(avatar_component_clause,[],[f192])).
% 0.21/0.45  fof(f194,plain,(
% 0.21/0.45    spl2_17 | ~spl2_16),
% 0.21/0.45    inference(avatar_split_clause,[],[f189,f184,f192])).
% 0.21/0.45  fof(f189,plain,(
% 0.21/0.45    ( ! [X0] : (r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,X0),sK1)) ) | ~spl2_16),
% 0.21/0.45    inference(superposition,[],[f58,f185])).
% 0.21/0.45  fof(f58,plain,(
% 0.21/0.45    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0)) )),
% 0.21/0.45    inference(definition_unfolding,[],[f45,f57])).
% 0.21/0.45  fof(f45,plain,(
% 0.21/0.45    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f4])).
% 0.21/0.45  fof(f4,axiom,(
% 0.21/0.45    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.21/0.45  fof(f186,plain,(
% 0.21/0.45    spl2_16 | ~spl2_3),
% 0.21/0.45    inference(avatar_split_clause,[],[f172,f75,f184])).
% 0.21/0.45  fof(f172,plain,(
% 0.21/0.45    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),sK1,X0) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X0)))) ) | ~spl2_3),
% 0.21/0.45    inference(unit_resulting_resolution,[],[f77,f62])).
% 0.21/0.45  fof(f62,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))) )),
% 0.21/0.45    inference(definition_unfolding,[],[f55,f57])).
% 0.21/0.45  fof(f55,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f29])).
% 0.21/0.45  fof(f29,plain,(
% 0.21/0.45    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.45    inference(ennf_transformation,[],[f9])).
% 0.21/0.45  fof(f9,axiom,(
% 0.21/0.45    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 0.21/0.45  fof(f116,plain,(
% 0.21/0.45    spl2_7 | ~spl2_2 | ~spl2_3),
% 0.21/0.45    inference(avatar_split_clause,[],[f111,f75,f70,f113])).
% 0.21/0.45  fof(f111,plain,(
% 0.21/0.45    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_2 | ~spl2_3)),
% 0.21/0.45    inference(unit_resulting_resolution,[],[f72,f77,f54])).
% 0.21/0.45  fof(f54,plain,(
% 0.21/0.45    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f28])).
% 0.21/0.45  fof(f28,plain,(
% 0.21/0.45    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.45    inference(flattening,[],[f27])).
% 0.21/0.45  fof(f27,plain,(
% 0.21/0.45    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.21/0.45    inference(ennf_transformation,[],[f11])).
% 0.21/0.45  fof(f11,axiom,(
% 0.21/0.45    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).
% 0.21/0.45  fof(f110,plain,(
% 0.21/0.45    spl2_6 | ~spl2_1 | ~spl2_2 | ~spl2_3),
% 0.21/0.45    inference(avatar_split_clause,[],[f105,f75,f70,f65,f107])).
% 0.21/0.45  fof(f107,plain,(
% 0.21/0.45    spl2_6 <=> v4_pre_topc(k2_pre_topc(sK0,sK1),sK0)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.45  fof(f65,plain,(
% 0.21/0.45    spl2_1 <=> v2_pre_topc(sK0)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.45  fof(f105,plain,(
% 0.21/0.45    v4_pre_topc(k2_pre_topc(sK0,sK1),sK0) | (~spl2_1 | ~spl2_2 | ~spl2_3)),
% 0.21/0.45    inference(unit_resulting_resolution,[],[f67,f72,f77,f53])).
% 0.21/0.45  fof(f53,plain,(
% 0.21/0.45    ( ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f26])).
% 0.21/0.45  fof(f26,plain,(
% 0.21/0.45    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.45    inference(flattening,[],[f25])).
% 0.21/0.45  fof(f25,plain,(
% 0.21/0.45    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.45    inference(ennf_transformation,[],[f12])).
% 0.21/0.45  fof(f12,axiom,(
% 0.21/0.45    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_pre_topc(X0,X1),X0))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_tops_1)).
% 0.21/0.45  fof(f67,plain,(
% 0.21/0.45    v2_pre_topc(sK0) | ~spl2_1),
% 0.21/0.45    inference(avatar_component_clause,[],[f65])).
% 0.21/0.45  fof(f104,plain,(
% 0.21/0.45    ~spl2_4 | ~spl2_5),
% 0.21/0.45    inference(avatar_split_clause,[],[f41,f100,f96])).
% 0.21/0.45  fof(f41,plain,(
% 0.21/0.45    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)),
% 0.21/0.45    inference(cnf_transformation,[],[f36])).
% 0.21/0.45  fof(f36,plain,(
% 0.21/0.45    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.21/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f33,f35,f34])).
% 0.21/0.45  fof(f34,plain,(
% 0.21/0.45    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f35,plain,(
% 0.21/0.45    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f33,plain,(
% 0.21/0.45    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.21/0.45    inference(flattening,[],[f32])).
% 0.21/0.45  fof(f32,plain,(
% 0.21/0.45    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.21/0.45    inference(nnf_transformation,[],[f19])).
% 0.21/0.45  fof(f19,plain,(
% 0.21/0.45    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.21/0.45    inference(flattening,[],[f18])).
% 0.21/0.45  fof(f18,plain,(
% 0.21/0.45    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.21/0.45    inference(ennf_transformation,[],[f17])).
% 0.21/0.45  fof(f17,negated_conjecture,(
% 0.21/0.45    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 0.21/0.45    inference(negated_conjecture,[],[f16])).
% 0.21/0.45  fof(f16,conjecture,(
% 0.21/0.45    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).
% 0.21/0.45  fof(f103,plain,(
% 0.21/0.45    spl2_4 | spl2_5),
% 0.21/0.45    inference(avatar_split_clause,[],[f40,f100,f96])).
% 0.21/0.45  fof(f40,plain,(
% 0.21/0.45    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)),
% 0.21/0.45    inference(cnf_transformation,[],[f36])).
% 0.21/0.45  fof(f78,plain,(
% 0.21/0.45    spl2_3),
% 0.21/0.45    inference(avatar_split_clause,[],[f39,f75])).
% 0.21/0.45  fof(f39,plain,(
% 0.21/0.45    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.45    inference(cnf_transformation,[],[f36])).
% 0.21/0.45  fof(f73,plain,(
% 0.21/0.45    spl2_2),
% 0.21/0.45    inference(avatar_split_clause,[],[f38,f70])).
% 0.21/0.45  fof(f38,plain,(
% 0.21/0.45    l1_pre_topc(sK0)),
% 0.21/0.45    inference(cnf_transformation,[],[f36])).
% 0.21/0.45  fof(f68,plain,(
% 0.21/0.45    spl2_1),
% 0.21/0.45    inference(avatar_split_clause,[],[f37,f65])).
% 0.21/0.45  fof(f37,plain,(
% 0.21/0.45    v2_pre_topc(sK0)),
% 0.21/0.45    inference(cnf_transformation,[],[f36])).
% 0.21/0.45  % SZS output end Proof for theBenchmark
% 0.21/0.45  % (5103)------------------------------
% 0.21/0.45  % (5103)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.45  % (5103)Termination reason: Refutation
% 0.21/0.45  
% 0.21/0.45  % (5103)Memory used [KB]: 12025
% 0.21/0.45  % (5103)Time elapsed: 0.041 s
% 0.21/0.45  % (5103)------------------------------
% 0.21/0.45  % (5103)------------------------------
% 0.21/0.46  % (5085)Success in time 0.103 s
%------------------------------------------------------------------------------
