%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:12:00 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 204 expanded)
%              Number of leaves         :   30 (  88 expanded)
%              Depth                    :   10
%              Number of atoms          :  285 ( 676 expanded)
%              Number of equality atoms :   90 ( 189 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f582,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f65,f66,f71,f76,f81,f96,f136,f220,f269,f294,f575,f578,f579,f580,f581])).

fof(f581,plain,
    ( k2_pre_topc(sK0,sK1) != k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) != k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | sK1 != k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | sK1 = k2_pre_topc(sK0,sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f580,plain,
    ( sK1 != k2_pre_topc(sK0,sK1)
    | k2_pre_topc(sK0,sK1) != k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) != k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | sK1 = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f579,plain,
    ( sK1 != k2_pre_topc(sK0,sK1)
    | k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
    | k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f578,plain,
    ( ~ spl2_1
    | ~ spl2_3
    | ~ spl2_4
    | spl2_10 ),
    inference(avatar_split_clause,[],[f244,f133,f73,f68,f58])).

fof(f58,plain,
    ( spl2_1
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f68,plain,
    ( spl2_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f73,plain,
    ( spl2_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f133,plain,
    ( spl2_10
  <=> sK1 = k2_pre_topc(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f244,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | ~ spl2_3
    | ~ spl2_4
    | spl2_10 ),
    inference(unit_resulting_resolution,[],[f75,f70,f135,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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

fof(f135,plain,
    ( sK1 != k2_pre_topc(sK0,sK1)
    | spl2_10 ),
    inference(avatar_component_clause,[],[f133])).

fof(f70,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f68])).

fof(f75,plain,
    ( l1_pre_topc(sK0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f73])).

fof(f575,plain,
    ( spl2_58
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f567,f68,f62,f572])).

fof(f572,plain,
    ( spl2_58
  <=> sK1 = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_58])])).

fof(f62,plain,
    ( spl2_2
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f567,plain,
    ( sK1 = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(superposition,[],[f532,f63])).

fof(f63,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f62])).

fof(f532,plain,
    ( ! [X0] : sK1 = k3_tarski(k2_tarski(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X0)))
    | ~ spl2_3 ),
    inference(forward_demodulation,[],[f531,f41])).

fof(f41,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f531,plain,
    ( ! [X0] : sK1 = k3_tarski(k2_tarski(k7_subset_1(u1_struct_0(sK0),sK1,X0),sK1))
    | ~ spl2_3 ),
    inference(forward_demodulation,[],[f514,f52])).

fof(f52,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,k1_setfam_1(k2_tarski(X0,X1)))) = X0 ),
    inference(definition_unfolding,[],[f42,f44,f43])).

fof(f43,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f44,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f42,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f514,plain,
    ( ! [X0] : k3_tarski(k2_tarski(sK1,k1_setfam_1(k2_tarski(sK1,X0)))) = k3_tarski(k2_tarski(k7_subset_1(u1_struct_0(sK0),sK1,X0),k3_tarski(k2_tarski(sK1,k1_setfam_1(k2_tarski(sK1,X0))))))
    | ~ spl2_3 ),
    inference(superposition,[],[f105,f118])).

fof(f118,plain,
    ( ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X0)))
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f70,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) ) ),
    inference(definition_unfolding,[],[f49,f51])).

fof(f51,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f45,f43])).

fof(f45,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f105,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(k5_xboole_0(X0,X1),k3_tarski(k2_tarski(X0,X1)))) ),
    inference(superposition,[],[f53,f54])).

fof(f54,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(k5_xboole_0(X0,X1),k1_setfam_1(k2_tarski(X0,X1)))) ),
    inference(definition_unfolding,[],[f47,f44,f44,f43])).

fof(f47,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_xboole_1)).

fof(f53,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) ),
    inference(definition_unfolding,[],[f46,f44,f44,f44])).

fof(f46,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_1)).

fof(f294,plain,
    ( spl2_34
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f270,f73,f68,f291])).

fof(f291,plain,
    ( spl2_34
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).

fof(f270,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(unit_resulting_resolution,[],[f75,f70,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

fof(f269,plain,
    ( spl2_30
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f245,f73,f68,f266])).

fof(f266,plain,
    ( spl2_30
  <=> k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_30])])).

fof(f245,plain,
    ( k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(unit_resulting_resolution,[],[f75,f70,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

fof(f220,plain,
    ( spl2_22
    | ~ spl2_3
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f141,f93,f68,f217])).

fof(f217,plain,
    ( spl2_22
  <=> k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).

fof(f93,plain,
    ( spl2_6
  <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f141,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_3
    | ~ spl2_6 ),
    inference(unit_resulting_resolution,[],[f70,f95,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2)) ) ),
    inference(definition_unfolding,[],[f50,f44])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f95,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f93])).

fof(f136,plain,
    ( ~ spl2_10
    | spl2_1
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f131,f78,f73,f68,f58,f133])).

fof(f78,plain,
    ( spl2_5
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f131,plain,
    ( sK1 != k2_pre_topc(sK0,sK1)
    | spl2_1
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(unit_resulting_resolution,[],[f75,f80,f60,f70,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) != X1
      | v4_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f60,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f58])).

fof(f80,plain,
    ( v2_pre_topc(sK0)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f78])).

fof(f96,plain,
    ( spl2_6
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f91,f73,f68,f93])).

fof(f91,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(unit_resulting_resolution,[],[f75,f70,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(f81,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f32,f78])).

fof(f32,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | ~ v4_pre_topc(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | v4_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f28,f30,f29])).

fof(f29,plain,
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

fof(f30,plain,
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

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).

fof(f76,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f33,f73])).

fof(f33,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f71,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f34,f68])).

fof(f34,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f31])).

fof(f66,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f35,f62,f58])).

fof(f35,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f65,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f36,f62,f58])).

fof(f36,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:32:27 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.43  % (27392)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.44  % (27392)Refutation found. Thanks to Tanya!
% 0.22/0.44  % SZS status Theorem for theBenchmark
% 0.22/0.44  % SZS output start Proof for theBenchmark
% 0.22/0.44  fof(f582,plain,(
% 0.22/0.44    $false),
% 0.22/0.44    inference(avatar_sat_refutation,[],[f65,f66,f71,f76,f81,f96,f136,f220,f269,f294,f575,f578,f579,f580,f581])).
% 0.22/0.44  fof(f581,plain,(
% 0.22/0.44    k2_pre_topc(sK0,sK1) != k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) != k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | sK1 != k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | sK1 = k2_pre_topc(sK0,sK1)),
% 0.22/0.44    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.44  fof(f580,plain,(
% 0.22/0.44    sK1 != k2_pre_topc(sK0,sK1) | k2_pre_topc(sK0,sK1) != k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) != k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | sK1 = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))),
% 0.22/0.44    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.44  fof(f579,plain,(
% 0.22/0.44    sK1 != k2_pre_topc(sK0,sK1) | k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) | k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),
% 0.22/0.44    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.44  fof(f578,plain,(
% 0.22/0.44    ~spl2_1 | ~spl2_3 | ~spl2_4 | spl2_10),
% 0.22/0.44    inference(avatar_split_clause,[],[f244,f133,f73,f68,f58])).
% 0.22/0.44  fof(f58,plain,(
% 0.22/0.44    spl2_1 <=> v4_pre_topc(sK1,sK0)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.44  fof(f68,plain,(
% 0.22/0.44    spl2_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.22/0.44  fof(f73,plain,(
% 0.22/0.44    spl2_4 <=> l1_pre_topc(sK0)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.22/0.44  fof(f133,plain,(
% 0.22/0.44    spl2_10 <=> sK1 = k2_pre_topc(sK0,sK1)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.22/0.44  fof(f244,plain,(
% 0.22/0.44    ~v4_pre_topc(sK1,sK0) | (~spl2_3 | ~spl2_4 | spl2_10)),
% 0.22/0.44    inference(unit_resulting_resolution,[],[f75,f70,f135,f39])).
% 0.22/0.44  fof(f39,plain,(
% 0.22/0.44    ( ! [X0,X1] : (~v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f21])).
% 0.22/0.44  fof(f21,plain,(
% 0.22/0.44    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.44    inference(flattening,[],[f20])).
% 0.22/0.44  fof(f20,plain,(
% 0.22/0.44    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.44    inference(ennf_transformation,[],[f10])).
% 0.22/0.44  fof(f10,axiom,(
% 0.22/0.44    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).
% 0.22/0.44  fof(f135,plain,(
% 0.22/0.44    sK1 != k2_pre_topc(sK0,sK1) | spl2_10),
% 0.22/0.44    inference(avatar_component_clause,[],[f133])).
% 0.22/0.44  fof(f70,plain,(
% 0.22/0.44    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_3),
% 0.22/0.44    inference(avatar_component_clause,[],[f68])).
% 0.22/0.44  fof(f75,plain,(
% 0.22/0.44    l1_pre_topc(sK0) | ~spl2_4),
% 0.22/0.44    inference(avatar_component_clause,[],[f73])).
% 0.22/0.44  fof(f575,plain,(
% 0.22/0.44    spl2_58 | ~spl2_2 | ~spl2_3),
% 0.22/0.44    inference(avatar_split_clause,[],[f567,f68,f62,f572])).
% 0.22/0.44  fof(f572,plain,(
% 0.22/0.44    spl2_58 <=> sK1 = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_58])])).
% 0.22/0.44  fof(f62,plain,(
% 0.22/0.44    spl2_2 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.44  fof(f567,plain,(
% 0.22/0.44    sK1 = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | (~spl2_2 | ~spl2_3)),
% 0.22/0.44    inference(superposition,[],[f532,f63])).
% 0.22/0.44  fof(f63,plain,(
% 0.22/0.44    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~spl2_2),
% 0.22/0.44    inference(avatar_component_clause,[],[f62])).
% 0.22/0.44  fof(f532,plain,(
% 0.22/0.44    ( ! [X0] : (sK1 = k3_tarski(k2_tarski(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X0)))) ) | ~spl2_3),
% 0.22/0.44    inference(forward_demodulation,[],[f531,f41])).
% 0.22/0.44  fof(f41,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f5])).
% 0.22/0.44  fof(f5,axiom,(
% 0.22/0.44    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.22/0.44  fof(f531,plain,(
% 0.22/0.44    ( ! [X0] : (sK1 = k3_tarski(k2_tarski(k7_subset_1(u1_struct_0(sK0),sK1,X0),sK1))) ) | ~spl2_3),
% 0.22/0.44    inference(forward_demodulation,[],[f514,f52])).
% 0.22/0.44  fof(f52,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,k1_setfam_1(k2_tarski(X0,X1)))) = X0) )),
% 0.22/0.44    inference(definition_unfolding,[],[f42,f44,f43])).
% 0.22/0.44  fof(f43,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f9])).
% 0.22/0.44  fof(f9,axiom,(
% 0.22/0.44    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.22/0.44  fof(f44,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f6])).
% 0.22/0.44  fof(f6,axiom,(
% 0.22/0.44    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.22/0.44  fof(f42,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 0.22/0.44    inference(cnf_transformation,[],[f2])).
% 0.22/0.44  fof(f2,axiom,(
% 0.22/0.44    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).
% 0.22/0.44  fof(f514,plain,(
% 0.22/0.44    ( ! [X0] : (k3_tarski(k2_tarski(sK1,k1_setfam_1(k2_tarski(sK1,X0)))) = k3_tarski(k2_tarski(k7_subset_1(u1_struct_0(sK0),sK1,X0),k3_tarski(k2_tarski(sK1,k1_setfam_1(k2_tarski(sK1,X0))))))) ) | ~spl2_3),
% 0.22/0.44    inference(superposition,[],[f105,f118])).
% 0.22/0.44  fof(f118,plain,(
% 0.22/0.44    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),sK1,X0) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X0)))) ) | ~spl2_3),
% 0.22/0.44    inference(unit_resulting_resolution,[],[f70,f55])).
% 0.22/0.44  fof(f55,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))) )),
% 0.22/0.44    inference(definition_unfolding,[],[f49,f51])).
% 0.22/0.44  fof(f51,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 0.22/0.44    inference(definition_unfolding,[],[f45,f43])).
% 0.22/0.44  fof(f45,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f1])).
% 0.22/0.44  fof(f1,axiom,(
% 0.22/0.44    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.22/0.44  fof(f49,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f24])).
% 0.22/0.44  fof(f24,plain,(
% 0.22/0.44    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.44    inference(ennf_transformation,[],[f8])).
% 0.22/0.44  fof(f8,axiom,(
% 0.22/0.44    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 0.22/0.44  fof(f105,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(k5_xboole_0(X0,X1),k3_tarski(k2_tarski(X0,X1))))) )),
% 0.22/0.44    inference(superposition,[],[f53,f54])).
% 0.22/0.44  fof(f54,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(k5_xboole_0(X0,X1),k1_setfam_1(k2_tarski(X0,X1))))) )),
% 0.22/0.44    inference(definition_unfolding,[],[f47,f44,f44,f43])).
% 0.22/0.44  fof(f47,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f4])).
% 0.22/0.44  fof(f4,axiom,(
% 0.22/0.44    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_xboole_1)).
% 0.22/0.44  fof(f53,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1))))) )),
% 0.22/0.44    inference(definition_unfolding,[],[f46,f44,f44,f44])).
% 0.22/0.44  fof(f46,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f3])).
% 0.22/0.44  fof(f3,axiom,(
% 0.22/0.44    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_1)).
% 0.22/0.44  fof(f294,plain,(
% 0.22/0.44    spl2_34 | ~spl2_3 | ~spl2_4),
% 0.22/0.44    inference(avatar_split_clause,[],[f270,f73,f68,f291])).
% 0.22/0.44  fof(f291,plain,(
% 0.22/0.44    spl2_34 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).
% 0.22/0.44  fof(f270,plain,(
% 0.22/0.44    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) | (~spl2_3 | ~spl2_4)),
% 0.22/0.44    inference(unit_resulting_resolution,[],[f75,f70,f38])).
% 0.22/0.44  fof(f38,plain,(
% 0.22/0.44    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f19])).
% 0.22/0.44  fof(f19,plain,(
% 0.22/0.44    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.44    inference(ennf_transformation,[],[f12])).
% 0.22/0.44  fof(f12,axiom,(
% 0.22/0.44    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).
% 0.22/0.44  fof(f269,plain,(
% 0.22/0.44    spl2_30 | ~spl2_3 | ~spl2_4),
% 0.22/0.44    inference(avatar_split_clause,[],[f245,f73,f68,f266])).
% 0.22/0.44  fof(f266,plain,(
% 0.22/0.44    spl2_30 <=> k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_30])])).
% 0.22/0.44  fof(f245,plain,(
% 0.22/0.44    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | (~spl2_3 | ~spl2_4)),
% 0.22/0.44    inference(unit_resulting_resolution,[],[f75,f70,f37])).
% 0.22/0.45  fof(f37,plain,(
% 0.22/0.45    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))) )),
% 0.22/0.45    inference(cnf_transformation,[],[f18])).
% 0.22/0.45  fof(f18,plain,(
% 0.22/0.45    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.45    inference(ennf_transformation,[],[f13])).
% 0.22/0.45  fof(f13,axiom,(
% 0.22/0.45    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).
% 0.22/0.45  fof(f220,plain,(
% 0.22/0.45    spl2_22 | ~spl2_3 | ~spl2_6),
% 0.22/0.45    inference(avatar_split_clause,[],[f141,f93,f68,f217])).
% 0.22/0.45  fof(f217,plain,(
% 0.22/0.45    spl2_22 <=> k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).
% 0.22/0.45  fof(f93,plain,(
% 0.22/0.45    spl2_6 <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.22/0.45  fof(f141,plain,(
% 0.22/0.45    k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | (~spl2_3 | ~spl2_6)),
% 0.22/0.45    inference(unit_resulting_resolution,[],[f70,f95,f56])).
% 0.22/0.45  fof(f56,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))) )),
% 0.22/0.45    inference(definition_unfolding,[],[f50,f44])).
% 0.22/0.45  fof(f50,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.45    inference(cnf_transformation,[],[f26])).
% 0.22/0.45  fof(f26,plain,(
% 0.22/0.45    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.45    inference(flattening,[],[f25])).
% 0.22/0.45  fof(f25,plain,(
% 0.22/0.45    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.22/0.45    inference(ennf_transformation,[],[f7])).
% 0.22/0.45  fof(f7,axiom,(
% 0.22/0.45    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 0.22/0.45  fof(f95,plain,(
% 0.22/0.45    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_6),
% 0.22/0.45    inference(avatar_component_clause,[],[f93])).
% 0.22/0.45  fof(f136,plain,(
% 0.22/0.45    ~spl2_10 | spl2_1 | ~spl2_3 | ~spl2_4 | ~spl2_5),
% 0.22/0.45    inference(avatar_split_clause,[],[f131,f78,f73,f68,f58,f133])).
% 0.22/0.45  fof(f78,plain,(
% 0.22/0.45    spl2_5 <=> v2_pre_topc(sK0)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.22/0.45  fof(f131,plain,(
% 0.22/0.45    sK1 != k2_pre_topc(sK0,sK1) | (spl2_1 | ~spl2_3 | ~spl2_4 | ~spl2_5)),
% 0.22/0.45    inference(unit_resulting_resolution,[],[f75,f80,f60,f70,f40])).
% 0.22/0.45  fof(f40,plain,(
% 0.22/0.45    ( ! [X0,X1] : (k2_pre_topc(X0,X1) != X1 | v4_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f21])).
% 0.22/0.45  fof(f60,plain,(
% 0.22/0.45    ~v4_pre_topc(sK1,sK0) | spl2_1),
% 0.22/0.45    inference(avatar_component_clause,[],[f58])).
% 0.22/0.45  fof(f80,plain,(
% 0.22/0.45    v2_pre_topc(sK0) | ~spl2_5),
% 0.22/0.45    inference(avatar_component_clause,[],[f78])).
% 0.22/0.45  fof(f96,plain,(
% 0.22/0.45    spl2_6 | ~spl2_3 | ~spl2_4),
% 0.22/0.45    inference(avatar_split_clause,[],[f91,f73,f68,f93])).
% 0.22/0.45  fof(f91,plain,(
% 0.22/0.45    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_3 | ~spl2_4)),
% 0.22/0.45    inference(unit_resulting_resolution,[],[f75,f70,f48])).
% 0.22/0.45  fof(f48,plain,(
% 0.22/0.45    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f23])).
% 0.22/0.45  fof(f23,plain,(
% 0.22/0.45    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.22/0.45    inference(flattening,[],[f22])).
% 0.22/0.45  fof(f22,plain,(
% 0.22/0.45    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.22/0.45    inference(ennf_transformation,[],[f11])).
% 0.22/0.45  fof(f11,axiom,(
% 0.22/0.45    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).
% 0.22/0.45  fof(f81,plain,(
% 0.22/0.45    spl2_5),
% 0.22/0.45    inference(avatar_split_clause,[],[f32,f78])).
% 0.22/0.45  fof(f32,plain,(
% 0.22/0.45    v2_pre_topc(sK0)),
% 0.22/0.45    inference(cnf_transformation,[],[f31])).
% 0.22/0.45  fof(f31,plain,(
% 0.22/0.45    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.22/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f28,f30,f29])).
% 0.22/0.45  fof(f29,plain,(
% 0.22/0.45    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.22/0.45    introduced(choice_axiom,[])).
% 0.22/0.45  fof(f30,plain,(
% 0.22/0.45    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.45    introduced(choice_axiom,[])).
% 0.22/0.45  fof(f28,plain,(
% 0.22/0.45    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.22/0.45    inference(flattening,[],[f27])).
% 0.22/0.45  fof(f27,plain,(
% 0.22/0.45    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.22/0.45    inference(nnf_transformation,[],[f17])).
% 0.22/0.45  fof(f17,plain,(
% 0.22/0.45    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.22/0.45    inference(flattening,[],[f16])).
% 0.22/0.45  fof(f16,plain,(
% 0.22/0.45    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.22/0.45    inference(ennf_transformation,[],[f15])).
% 0.22/0.45  fof(f15,negated_conjecture,(
% 0.22/0.45    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 0.22/0.45    inference(negated_conjecture,[],[f14])).
% 0.22/0.45  fof(f14,conjecture,(
% 0.22/0.45    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).
% 0.22/0.45  fof(f76,plain,(
% 0.22/0.45    spl2_4),
% 0.22/0.45    inference(avatar_split_clause,[],[f33,f73])).
% 0.22/0.45  fof(f33,plain,(
% 0.22/0.45    l1_pre_topc(sK0)),
% 0.22/0.45    inference(cnf_transformation,[],[f31])).
% 0.22/0.45  fof(f71,plain,(
% 0.22/0.45    spl2_3),
% 0.22/0.45    inference(avatar_split_clause,[],[f34,f68])).
% 0.22/0.45  fof(f34,plain,(
% 0.22/0.45    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.45    inference(cnf_transformation,[],[f31])).
% 0.22/0.45  fof(f66,plain,(
% 0.22/0.45    spl2_1 | spl2_2),
% 0.22/0.45    inference(avatar_split_clause,[],[f35,f62,f58])).
% 0.22/0.45  fof(f35,plain,(
% 0.22/0.45    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)),
% 0.22/0.45    inference(cnf_transformation,[],[f31])).
% 0.22/0.45  fof(f65,plain,(
% 0.22/0.45    ~spl2_1 | ~spl2_2),
% 0.22/0.45    inference(avatar_split_clause,[],[f36,f62,f58])).
% 0.22/0.45  fof(f36,plain,(
% 0.22/0.45    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)),
% 0.22/0.45    inference(cnf_transformation,[],[f31])).
% 0.22/0.45  % SZS output end Proof for theBenchmark
% 0.22/0.45  % (27392)------------------------------
% 0.22/0.45  % (27392)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.45  % (27392)Termination reason: Refutation
% 0.22/0.45  
% 0.22/0.45  % (27392)Memory used [KB]: 6652
% 0.22/0.45  % (27392)Time elapsed: 0.016 s
% 0.22/0.45  % (27392)------------------------------
% 0.22/0.45  % (27392)------------------------------
% 0.22/0.45  % (27383)Success in time 0.089 s
%------------------------------------------------------------------------------
