%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:51 EST 2020

% Result     : Theorem 1.63s
% Output     : Refutation 1.63s
% Verified   : 
% Statistics : Number of formulae       :  143 ( 282 expanded)
%              Number of leaves         :   41 ( 122 expanded)
%              Depth                    :    9
%              Number of atoms          :  379 ( 825 expanded)
%              Number of equality atoms :  103 ( 223 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4577,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f121,f122,f127,f132,f137,f377,f518,f578,f710,f952,f996,f4260,f4285,f4298,f4308,f4311,f4379,f4567,f4568,f4570,f4574,f4576])).

fof(f4576,plain,
    ( k3_subset_1(sK1,k2_tops_1(sK0,sK1)) != k6_subset_1(sK1,k2_tops_1(sK0,sK1))
    | k1_tops_1(sK0,sK1) != k6_subset_1(sK1,k2_tops_1(sK0,sK1))
    | k3_subset_1(sK1,k3_subset_1(sK1,k2_tops_1(sK0,sK1))) != k6_subset_1(sK1,k3_subset_1(sK1,k2_tops_1(sK0,sK1)))
    | k2_tops_1(sK0,sK1) != k3_subset_1(sK1,k3_subset_1(sK1,k2_tops_1(sK0,sK1)))
    | k2_tops_1(sK0,sK1) = k6_subset_1(sK1,k1_tops_1(sK0,sK1)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f4574,plain,
    ( k2_pre_topc(sK0,sK1) != k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) != k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | sK1 != k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | sK1 = k2_pre_topc(sK0,sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f4570,plain,
    ( spl2_269
    | ~ spl2_66 ),
    inference(avatar_split_clause,[],[f4461,f825,f4531])).

fof(f4531,plain,
    ( spl2_269
  <=> k3_subset_1(sK1,k3_subset_1(sK1,k2_tops_1(sK0,sK1))) = k6_subset_1(sK1,k3_subset_1(sK1,k2_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_269])])).

fof(f825,plain,
    ( spl2_66
  <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_66])])).

fof(f4461,plain,
    ( k3_subset_1(sK1,k3_subset_1(sK1,k2_tops_1(sK0,sK1))) = k6_subset_1(sK1,k3_subset_1(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_66 ),
    inference(resolution,[],[f827,f225])).

fof(f225,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(X2))
      | k3_subset_1(X2,k3_subset_1(X2,X3)) = k6_subset_1(X2,k3_subset_1(X2,X3)) ) ),
    inference(resolution,[],[f108,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f108,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,X1) = k6_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f87,f78])).

fof(f78,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f87,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f827,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ spl2_66 ),
    inference(avatar_component_clause,[],[f825])).

fof(f4568,plain,
    ( spl2_71
    | ~ spl2_66 ),
    inference(avatar_split_clause,[],[f4457,f825,f928])).

fof(f928,plain,
    ( spl2_71
  <=> k3_subset_1(sK1,k2_tops_1(sK0,sK1)) = k6_subset_1(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_71])])).

fof(f4457,plain,
    ( k3_subset_1(sK1,k2_tops_1(sK0,sK1)) = k6_subset_1(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_66 ),
    inference(resolution,[],[f827,f108])).

fof(f4567,plain,
    ( spl2_72
    | ~ spl2_66 ),
    inference(avatar_split_clause,[],[f4455,f825,f933])).

fof(f933,plain,
    ( spl2_72
  <=> k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k3_subset_1(sK1,k2_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_72])])).

fof(f4455,plain,
    ( k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k3_subset_1(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_66 ),
    inference(resolution,[],[f827,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f4379,plain,
    ( spl2_66
    | ~ spl2_65 ),
    inference(avatar_split_clause,[],[f4317,f806,f825])).

fof(f806,plain,
    ( spl2_65
  <=> r1_tarski(k2_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_65])])).

fof(f4317,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ spl2_65 ),
    inference(unit_resulting_resolution,[],[f808,f92])).

fof(f92,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f808,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_65 ),
    inference(avatar_component_clause,[],[f806])).

fof(f4311,plain,
    ( ~ spl2_64
    | spl2_2
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f4310,f124,f118,f794])).

fof(f794,plain,
    ( spl2_64
  <=> k2_tops_1(sK0,sK1) = k6_subset_1(sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_64])])).

fof(f118,plain,
    ( spl2_2
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f124,plain,
    ( spl2_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f4310,plain,
    ( k2_tops_1(sK0,sK1) != k6_subset_1(sK1,k1_tops_1(sK0,sK1))
    | spl2_2
    | ~ spl2_3 ),
    inference(superposition,[],[f120,f286])).

fof(f286,plain,
    ( ! [X0] : k6_subset_1(sK1,X0) = k7_subset_1(u1_struct_0(sK0),sK1,X0)
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f126,f109])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k6_subset_1(X1,X2) ) ),
    inference(definition_unfolding,[],[f93,f78])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f126,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f124])).

fof(f120,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f118])).

fof(f4308,plain,
    ( ~ spl2_4
    | ~ spl2_3
    | spl2_65
    | ~ spl2_1 ),
    inference(avatar_split_clause,[],[f4304,f114,f806,f124,f129])).

fof(f129,plain,
    ( spl2_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f114,plain,
    ( spl2_1
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f4304,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_1 ),
    inference(resolution,[],[f115,f74])).

fof(f74,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_tops_1)).

fof(f115,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f114])).

fof(f4298,plain,
    ( spl2_1
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_26 ),
    inference(avatar_split_clause,[],[f812,f454,f134,f129,f124,f114])).

fof(f134,plain,
    ( spl2_5
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f454,plain,
    ( spl2_26
  <=> sK1 = k2_pre_topc(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).

fof(f812,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_26 ),
    inference(unit_resulting_resolution,[],[f131,f136,f126,f455,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) != X1
      | v4_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0)
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
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

fof(f455,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl2_26 ),
    inference(avatar_component_clause,[],[f454])).

fof(f136,plain,
    ( v2_pre_topc(sK0)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f134])).

fof(f131,plain,
    ( l1_pre_topc(sK0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f129])).

fof(f4285,plain,
    ( spl2_256
    | ~ spl2_64 ),
    inference(avatar_split_clause,[],[f4239,f794,f4282])).

fof(f4282,plain,
    ( spl2_256
  <=> sK1 = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_256])])).

fof(f4239,plain,
    ( sK1 = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_64 ),
    inference(superposition,[],[f285,f796])).

fof(f796,plain,
    ( k2_tops_1(sK0,sK1) = k6_subset_1(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_64 ),
    inference(avatar_component_clause,[],[f794])).

fof(f285,plain,(
    ! [X6,X7] : k3_tarski(k2_tarski(X6,k6_subset_1(X6,X7))) = X6 ),
    inference(forward_demodulation,[],[f283,f77])).

fof(f77,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f283,plain,(
    ! [X6,X7] : k3_tarski(k2_tarski(k6_subset_1(X6,X7),X6)) = X6 ),
    inference(superposition,[],[f106,f216])).

fof(f216,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(k6_subset_1(X0,X1),k1_setfam_1(k2_tarski(X0,X1)))) = X0 ),
    inference(forward_demodulation,[],[f107,f77])).

fof(f107,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),k6_subset_1(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f84,f81,f80,f78])).

fof(f80,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f81,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f84,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f106,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) ),
    inference(definition_unfolding,[],[f83,f81,f81,f81])).

fof(f83,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_1)).

fof(f4260,plain,
    ( spl2_66
    | ~ spl2_64 ),
    inference(avatar_split_clause,[],[f4226,f794,f825])).

fof(f4226,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ spl2_64 ),
    inference(superposition,[],[f76,f796])).

fof(f76,plain,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_subset_1)).

fof(f996,plain,
    ( spl2_64
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f994,f124,f118,f794])).

fof(f994,plain,
    ( k2_tops_1(sK0,sK1) = k6_subset_1(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(superposition,[],[f286,f119])).

fof(f119,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f118])).

fof(f952,plain,
    ( spl2_74
    | ~ spl2_3
    | ~ spl2_32 ),
    inference(avatar_split_clause,[],[f946,f515,f124,f948])).

fof(f948,plain,
    ( spl2_74
  <=> k1_tops_1(sK0,sK1) = k6_subset_1(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_74])])).

fof(f515,plain,
    ( spl2_32
  <=> k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).

fof(f946,plain,
    ( k1_tops_1(sK0,sK1) = k6_subset_1(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_32 ),
    inference(superposition,[],[f286,f517])).

fof(f517,plain,
    ( k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_32 ),
    inference(avatar_component_clause,[],[f515])).

fof(f710,plain,
    ( spl2_49
    | ~ spl2_3
    | ~ spl2_19 ),
    inference(avatar_split_clause,[],[f693,f374,f124,f707])).

fof(f707,plain,
    ( spl2_49
  <=> k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_49])])).

fof(f374,plain,
    ( spl2_19
  <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f693,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_3
    | ~ spl2_19 ),
    inference(unit_resulting_resolution,[],[f126,f376,f112])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2)) ) ),
    inference(definition_unfolding,[],[f97,f81])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f376,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_19 ),
    inference(avatar_component_clause,[],[f374])).

fof(f578,plain,
    ( spl2_38
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f572,f129,f124,f575])).

fof(f575,plain,
    ( spl2_38
  <=> k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_38])])).

fof(f572,plain,
    ( k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(unit_resulting_resolution,[],[f131,f126,f71])).

fof(f71,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

fof(f518,plain,
    ( spl2_32
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f504,f129,f124,f515])).

fof(f504,plain,
    ( k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(unit_resulting_resolution,[],[f131,f126,f70])).

fof(f70,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).

fof(f377,plain,
    ( spl2_19
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f363,f129,f124,f374])).

fof(f363,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(unit_resulting_resolution,[],[f131,f126,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
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
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(f137,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f62,f134])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).

fof(f132,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f63,f129])).

fof(f63,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f60])).

fof(f127,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f64,f124])).

fof(f64,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f60])).

fof(f122,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f65,f118,f114])).

fof(f65,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f60])).

fof(f121,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f66,f118,f114])).

fof(f66,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f60])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:12:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.43  % (1412)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.46  % (1409)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.47  % (1408)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.48  % (1400)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.48  % (1406)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.48  % (1399)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.48  % (1410)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.48  % (1404)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.49  % (1396)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.49  % (1403)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.49  % (1402)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.49  % (1397)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.49  % (1398)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.50  % (1401)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.50  % (1413)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.50  % (1411)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.51  % (1407)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.51  % (1405)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 1.63/0.60  % (1402)Refutation found. Thanks to Tanya!
% 1.63/0.60  % SZS status Theorem for theBenchmark
% 1.63/0.60  % SZS output start Proof for theBenchmark
% 1.63/0.60  fof(f4577,plain,(
% 1.63/0.60    $false),
% 1.63/0.60    inference(avatar_sat_refutation,[],[f121,f122,f127,f132,f137,f377,f518,f578,f710,f952,f996,f4260,f4285,f4298,f4308,f4311,f4379,f4567,f4568,f4570,f4574,f4576])).
% 1.63/0.60  fof(f4576,plain,(
% 1.63/0.60    k3_subset_1(sK1,k2_tops_1(sK0,sK1)) != k6_subset_1(sK1,k2_tops_1(sK0,sK1)) | k1_tops_1(sK0,sK1) != k6_subset_1(sK1,k2_tops_1(sK0,sK1)) | k3_subset_1(sK1,k3_subset_1(sK1,k2_tops_1(sK0,sK1))) != k6_subset_1(sK1,k3_subset_1(sK1,k2_tops_1(sK0,sK1))) | k2_tops_1(sK0,sK1) != k3_subset_1(sK1,k3_subset_1(sK1,k2_tops_1(sK0,sK1))) | k2_tops_1(sK0,sK1) = k6_subset_1(sK1,k1_tops_1(sK0,sK1))),
% 1.63/0.60    introduced(theory_tautology_sat_conflict,[])).
% 1.63/0.60  fof(f4574,plain,(
% 1.63/0.60    k2_pre_topc(sK0,sK1) != k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) != k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | sK1 != k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | sK1 = k2_pre_topc(sK0,sK1)),
% 1.63/0.60    introduced(theory_tautology_sat_conflict,[])).
% 1.63/0.60  fof(f4570,plain,(
% 1.63/0.60    spl2_269 | ~spl2_66),
% 1.63/0.60    inference(avatar_split_clause,[],[f4461,f825,f4531])).
% 1.63/0.60  fof(f4531,plain,(
% 1.63/0.60    spl2_269 <=> k3_subset_1(sK1,k3_subset_1(sK1,k2_tops_1(sK0,sK1))) = k6_subset_1(sK1,k3_subset_1(sK1,k2_tops_1(sK0,sK1)))),
% 1.63/0.60    introduced(avatar_definition,[new_symbols(naming,[spl2_269])])).
% 1.63/0.60  fof(f825,plain,(
% 1.63/0.60    spl2_66 <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1))),
% 1.63/0.60    introduced(avatar_definition,[new_symbols(naming,[spl2_66])])).
% 1.63/0.60  fof(f4461,plain,(
% 1.63/0.60    k3_subset_1(sK1,k3_subset_1(sK1,k2_tops_1(sK0,sK1))) = k6_subset_1(sK1,k3_subset_1(sK1,k2_tops_1(sK0,sK1))) | ~spl2_66),
% 1.63/0.60    inference(resolution,[],[f827,f225])).
% 1.63/0.60  fof(f225,plain,(
% 1.63/0.60    ( ! [X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(X2)) | k3_subset_1(X2,k3_subset_1(X2,X3)) = k6_subset_1(X2,k3_subset_1(X2,X3))) )),
% 1.63/0.60    inference(resolution,[],[f108,f86])).
% 1.63/0.60  fof(f86,plain,(
% 1.63/0.60    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.63/0.60    inference(cnf_transformation,[],[f42])).
% 1.63/0.60  fof(f42,plain,(
% 1.63/0.60    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.63/0.60    inference(ennf_transformation,[],[f15])).
% 1.63/0.60  fof(f15,axiom,(
% 1.63/0.60    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.63/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 1.63/0.60  fof(f108,plain,(
% 1.63/0.60    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,X1) = k6_subset_1(X0,X1)) )),
% 1.63/0.60    inference(definition_unfolding,[],[f87,f78])).
% 1.63/0.60  fof(f78,plain,(
% 1.63/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 1.63/0.60    inference(cnf_transformation,[],[f19])).
% 1.63/0.60  fof(f19,axiom,(
% 1.63/0.60    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 1.63/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 1.63/0.60  fof(f87,plain,(
% 1.63/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.63/0.60    inference(cnf_transformation,[],[f43])).
% 1.63/0.60  fof(f43,plain,(
% 1.63/0.60    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.63/0.60    inference(ennf_transformation,[],[f14])).
% 1.63/0.60  fof(f14,axiom,(
% 1.63/0.60    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.63/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 1.63/0.60  fof(f827,plain,(
% 1.63/0.60    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | ~spl2_66),
% 1.63/0.60    inference(avatar_component_clause,[],[f825])).
% 1.63/0.60  fof(f4568,plain,(
% 1.63/0.60    spl2_71 | ~spl2_66),
% 1.63/0.60    inference(avatar_split_clause,[],[f4457,f825,f928])).
% 1.63/0.60  fof(f928,plain,(
% 1.63/0.60    spl2_71 <=> k3_subset_1(sK1,k2_tops_1(sK0,sK1)) = k6_subset_1(sK1,k2_tops_1(sK0,sK1))),
% 1.63/0.60    introduced(avatar_definition,[new_symbols(naming,[spl2_71])])).
% 1.63/0.60  fof(f4457,plain,(
% 1.63/0.60    k3_subset_1(sK1,k2_tops_1(sK0,sK1)) = k6_subset_1(sK1,k2_tops_1(sK0,sK1)) | ~spl2_66),
% 1.63/0.60    inference(resolution,[],[f827,f108])).
% 1.63/0.60  fof(f4567,plain,(
% 1.63/0.60    spl2_72 | ~spl2_66),
% 1.63/0.60    inference(avatar_split_clause,[],[f4455,f825,f933])).
% 1.63/0.60  fof(f933,plain,(
% 1.63/0.60    spl2_72 <=> k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k3_subset_1(sK1,k2_tops_1(sK0,sK1)))),
% 1.63/0.60    introduced(avatar_definition,[new_symbols(naming,[spl2_72])])).
% 1.63/0.60  fof(f4455,plain,(
% 1.63/0.60    k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k3_subset_1(sK1,k2_tops_1(sK0,sK1))) | ~spl2_66),
% 1.63/0.60    inference(resolution,[],[f827,f88])).
% 1.63/0.60  fof(f88,plain,(
% 1.63/0.60    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 1.63/0.60    inference(cnf_transformation,[],[f44])).
% 1.63/0.60  fof(f44,plain,(
% 1.63/0.60    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.63/0.60    inference(ennf_transformation,[],[f17])).
% 1.63/0.60  fof(f17,axiom,(
% 1.63/0.60    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 1.63/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 1.63/0.60  fof(f4379,plain,(
% 1.63/0.60    spl2_66 | ~spl2_65),
% 1.63/0.60    inference(avatar_split_clause,[],[f4317,f806,f825])).
% 1.63/0.60  fof(f806,plain,(
% 1.63/0.60    spl2_65 <=> r1_tarski(k2_tops_1(sK0,sK1),sK1)),
% 1.63/0.60    introduced(avatar_definition,[new_symbols(naming,[spl2_65])])).
% 1.63/0.60  fof(f4317,plain,(
% 1.63/0.60    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | ~spl2_65),
% 1.63/0.60    inference(unit_resulting_resolution,[],[f808,f92])).
% 1.63/0.60  fof(f92,plain,(
% 1.63/0.60    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.63/0.60    inference(cnf_transformation,[],[f61])).
% 1.63/0.60  fof(f61,plain,(
% 1.63/0.60    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.63/0.60    inference(nnf_transformation,[],[f23])).
% 1.63/0.60  fof(f23,axiom,(
% 1.63/0.60    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.63/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.63/0.60  fof(f808,plain,(
% 1.63/0.60    r1_tarski(k2_tops_1(sK0,sK1),sK1) | ~spl2_65),
% 1.63/0.60    inference(avatar_component_clause,[],[f806])).
% 1.63/0.60  fof(f4311,plain,(
% 1.63/0.60    ~spl2_64 | spl2_2 | ~spl2_3),
% 1.63/0.60    inference(avatar_split_clause,[],[f4310,f124,f118,f794])).
% 1.63/0.60  fof(f794,plain,(
% 1.63/0.60    spl2_64 <=> k2_tops_1(sK0,sK1) = k6_subset_1(sK1,k1_tops_1(sK0,sK1))),
% 1.63/0.60    introduced(avatar_definition,[new_symbols(naming,[spl2_64])])).
% 1.63/0.60  fof(f118,plain,(
% 1.63/0.60    spl2_2 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),
% 1.63/0.60    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 1.63/0.60  fof(f124,plain,(
% 1.63/0.60    spl2_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.63/0.60    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 1.63/0.60  fof(f4310,plain,(
% 1.63/0.60    k2_tops_1(sK0,sK1) != k6_subset_1(sK1,k1_tops_1(sK0,sK1)) | (spl2_2 | ~spl2_3)),
% 1.63/0.60    inference(superposition,[],[f120,f286])).
% 1.63/0.60  fof(f286,plain,(
% 1.63/0.60    ( ! [X0] : (k6_subset_1(sK1,X0) = k7_subset_1(u1_struct_0(sK0),sK1,X0)) ) | ~spl2_3),
% 1.63/0.60    inference(unit_resulting_resolution,[],[f126,f109])).
% 1.63/0.60  fof(f109,plain,(
% 1.63/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k6_subset_1(X1,X2)) )),
% 1.63/0.60    inference(definition_unfolding,[],[f93,f78])).
% 1.63/0.60  fof(f93,plain,(
% 1.63/0.60    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.63/0.60    inference(cnf_transformation,[],[f48])).
% 1.63/0.60  fof(f48,plain,(
% 1.63/0.60    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.63/0.60    inference(ennf_transformation,[],[f20])).
% 1.63/0.60  fof(f20,axiom,(
% 1.63/0.60    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 1.63/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 1.63/0.60  fof(f126,plain,(
% 1.63/0.60    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_3),
% 1.63/0.60    inference(avatar_component_clause,[],[f124])).
% 1.63/0.60  fof(f120,plain,(
% 1.63/0.60    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | spl2_2),
% 1.63/0.60    inference(avatar_component_clause,[],[f118])).
% 1.63/0.60  fof(f4308,plain,(
% 1.63/0.60    ~spl2_4 | ~spl2_3 | spl2_65 | ~spl2_1),
% 1.63/0.60    inference(avatar_split_clause,[],[f4304,f114,f806,f124,f129])).
% 1.63/0.60  fof(f129,plain,(
% 1.63/0.60    spl2_4 <=> l1_pre_topc(sK0)),
% 1.63/0.60    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 1.63/0.60  fof(f114,plain,(
% 1.63/0.60    spl2_1 <=> v4_pre_topc(sK1,sK0)),
% 1.63/0.60    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 1.63/0.60  fof(f4304,plain,(
% 1.63/0.60    r1_tarski(k2_tops_1(sK0,sK1),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl2_1),
% 1.63/0.60    inference(resolution,[],[f115,f74])).
% 1.63/0.60  fof(f74,plain,(
% 1.63/0.60    ( ! [X0,X1] : (~v4_pre_topc(X1,X0) | r1_tarski(k2_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.63/0.60    inference(cnf_transformation,[],[f41])).
% 1.63/0.60  fof(f41,plain,(
% 1.63/0.60    ! [X0] : (! [X1] : (r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.63/0.60    inference(flattening,[],[f40])).
% 1.63/0.60  fof(f40,plain,(
% 1.63/0.60    ! [X0] : (! [X1] : ((r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.63/0.60    inference(ennf_transformation,[],[f29])).
% 1.63/0.60  fof(f29,axiom,(
% 1.63/0.60    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => r1_tarski(k2_tops_1(X0,X1),X1))))),
% 1.63/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_tops_1)).
% 1.63/0.60  fof(f115,plain,(
% 1.63/0.60    v4_pre_topc(sK1,sK0) | ~spl2_1),
% 1.63/0.60    inference(avatar_component_clause,[],[f114])).
% 1.63/0.60  fof(f4298,plain,(
% 1.63/0.60    spl2_1 | ~spl2_3 | ~spl2_4 | ~spl2_5 | ~spl2_26),
% 1.63/0.60    inference(avatar_split_clause,[],[f812,f454,f134,f129,f124,f114])).
% 1.63/0.60  fof(f134,plain,(
% 1.63/0.60    spl2_5 <=> v2_pre_topc(sK0)),
% 1.63/0.60    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 1.63/0.60  fof(f454,plain,(
% 1.63/0.60    spl2_26 <=> sK1 = k2_pre_topc(sK0,sK1)),
% 1.63/0.60    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).
% 1.63/0.60  fof(f812,plain,(
% 1.63/0.60    v4_pre_topc(sK1,sK0) | (~spl2_3 | ~spl2_4 | ~spl2_5 | ~spl2_26)),
% 1.63/0.60    inference(unit_resulting_resolution,[],[f131,f136,f126,f455,f73])).
% 1.63/0.60  fof(f73,plain,(
% 1.63/0.60    ( ! [X0,X1] : (k2_pre_topc(X0,X1) != X1 | v4_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.63/0.60    inference(cnf_transformation,[],[f39])).
% 1.63/0.60  fof(f39,plain,(
% 1.63/0.60    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.63/0.60    inference(flattening,[],[f38])).
% 1.63/0.60  fof(f38,plain,(
% 1.63/0.60    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.63/0.60    inference(ennf_transformation,[],[f25])).
% 1.63/0.60  fof(f25,axiom,(
% 1.63/0.60    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 1.63/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).
% 1.63/0.60  fof(f455,plain,(
% 1.63/0.60    sK1 = k2_pre_topc(sK0,sK1) | ~spl2_26),
% 1.63/0.60    inference(avatar_component_clause,[],[f454])).
% 1.63/0.60  fof(f136,plain,(
% 1.63/0.60    v2_pre_topc(sK0) | ~spl2_5),
% 1.63/0.60    inference(avatar_component_clause,[],[f134])).
% 1.63/0.60  fof(f131,plain,(
% 1.63/0.60    l1_pre_topc(sK0) | ~spl2_4),
% 1.63/0.60    inference(avatar_component_clause,[],[f129])).
% 1.63/0.60  fof(f4285,plain,(
% 1.63/0.60    spl2_256 | ~spl2_64),
% 1.63/0.60    inference(avatar_split_clause,[],[f4239,f794,f4282])).
% 1.63/0.60  fof(f4282,plain,(
% 1.63/0.60    spl2_256 <=> sK1 = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))),
% 1.63/0.60    introduced(avatar_definition,[new_symbols(naming,[spl2_256])])).
% 1.63/0.60  fof(f4239,plain,(
% 1.63/0.60    sK1 = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | ~spl2_64),
% 1.63/0.60    inference(superposition,[],[f285,f796])).
% 1.63/0.60  fof(f796,plain,(
% 1.63/0.60    k2_tops_1(sK0,sK1) = k6_subset_1(sK1,k1_tops_1(sK0,sK1)) | ~spl2_64),
% 1.63/0.60    inference(avatar_component_clause,[],[f794])).
% 1.63/0.60  fof(f285,plain,(
% 1.63/0.60    ( ! [X6,X7] : (k3_tarski(k2_tarski(X6,k6_subset_1(X6,X7))) = X6) )),
% 1.63/0.60    inference(forward_demodulation,[],[f283,f77])).
% 1.63/0.60  fof(f77,plain,(
% 1.63/0.60    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.63/0.60    inference(cnf_transformation,[],[f11])).
% 1.63/0.60  fof(f11,axiom,(
% 1.63/0.60    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.63/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.63/0.60  fof(f283,plain,(
% 1.63/0.60    ( ! [X6,X7] : (k3_tarski(k2_tarski(k6_subset_1(X6,X7),X6)) = X6) )),
% 1.63/0.60    inference(superposition,[],[f106,f216])).
% 1.63/0.60  fof(f216,plain,(
% 1.63/0.60    ( ! [X0,X1] : (k3_tarski(k2_tarski(k6_subset_1(X0,X1),k1_setfam_1(k2_tarski(X0,X1)))) = X0) )),
% 1.63/0.60    inference(forward_demodulation,[],[f107,f77])).
% 1.63/0.60  fof(f107,plain,(
% 1.63/0.60    ( ! [X0,X1] : (k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),k6_subset_1(X0,X1))) = X0) )),
% 1.63/0.60    inference(definition_unfolding,[],[f84,f81,f80,f78])).
% 1.63/0.60  fof(f80,plain,(
% 1.63/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.63/0.60    inference(cnf_transformation,[],[f22])).
% 1.63/0.60  fof(f22,axiom,(
% 1.63/0.60    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.63/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.63/0.60  fof(f81,plain,(
% 1.63/0.60    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.63/0.60    inference(cnf_transformation,[],[f12])).
% 1.63/0.60  fof(f12,axiom,(
% 1.63/0.60    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.63/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.63/0.60  fof(f84,plain,(
% 1.63/0.60    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 1.63/0.60    inference(cnf_transformation,[],[f9])).
% 1.63/0.60  fof(f9,axiom,(
% 1.63/0.60    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 1.63/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).
% 1.63/0.60  fof(f106,plain,(
% 1.63/0.60    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1))))) )),
% 1.63/0.60    inference(definition_unfolding,[],[f83,f81,f81,f81])).
% 1.63/0.60  fof(f83,plain,(
% 1.63/0.60    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 1.63/0.60    inference(cnf_transformation,[],[f10])).
% 1.63/0.60  fof(f10,axiom,(
% 1.63/0.60    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))),
% 1.63/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_1)).
% 1.63/0.60  fof(f4260,plain,(
% 1.63/0.60    spl2_66 | ~spl2_64),
% 1.63/0.60    inference(avatar_split_clause,[],[f4226,f794,f825])).
% 1.63/0.60  fof(f4226,plain,(
% 1.63/0.60    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | ~spl2_64),
% 1.63/0.60    inference(superposition,[],[f76,f796])).
% 1.63/0.60  fof(f76,plain,(
% 1.63/0.60    ( ! [X0,X1] : (m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 1.63/0.60    inference(cnf_transformation,[],[f16])).
% 1.63/0.60  fof(f16,axiom,(
% 1.63/0.60    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))),
% 1.63/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_subset_1)).
% 1.63/0.60  fof(f996,plain,(
% 1.63/0.60    spl2_64 | ~spl2_2 | ~spl2_3),
% 1.63/0.60    inference(avatar_split_clause,[],[f994,f124,f118,f794])).
% 1.63/0.60  fof(f994,plain,(
% 1.63/0.60    k2_tops_1(sK0,sK1) = k6_subset_1(sK1,k1_tops_1(sK0,sK1)) | (~spl2_2 | ~spl2_3)),
% 1.63/0.60    inference(superposition,[],[f286,f119])).
% 1.63/0.60  fof(f119,plain,(
% 1.63/0.60    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~spl2_2),
% 1.63/0.60    inference(avatar_component_clause,[],[f118])).
% 1.63/0.60  fof(f952,plain,(
% 1.63/0.60    spl2_74 | ~spl2_3 | ~spl2_32),
% 1.63/0.60    inference(avatar_split_clause,[],[f946,f515,f124,f948])).
% 1.63/0.60  fof(f948,plain,(
% 1.63/0.60    spl2_74 <=> k1_tops_1(sK0,sK1) = k6_subset_1(sK1,k2_tops_1(sK0,sK1))),
% 1.63/0.60    introduced(avatar_definition,[new_symbols(naming,[spl2_74])])).
% 1.63/0.60  fof(f515,plain,(
% 1.63/0.60    spl2_32 <=> k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 1.63/0.60    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).
% 1.63/0.60  fof(f946,plain,(
% 1.63/0.60    k1_tops_1(sK0,sK1) = k6_subset_1(sK1,k2_tops_1(sK0,sK1)) | (~spl2_3 | ~spl2_32)),
% 1.63/0.60    inference(superposition,[],[f286,f517])).
% 1.63/0.60  fof(f517,plain,(
% 1.63/0.60    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | ~spl2_32),
% 1.63/0.60    inference(avatar_component_clause,[],[f515])).
% 1.63/0.60  fof(f710,plain,(
% 1.63/0.60    spl2_49 | ~spl2_3 | ~spl2_19),
% 1.63/0.60    inference(avatar_split_clause,[],[f693,f374,f124,f707])).
% 1.63/0.60  fof(f707,plain,(
% 1.63/0.60    spl2_49 <=> k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))),
% 1.63/0.60    introduced(avatar_definition,[new_symbols(naming,[spl2_49])])).
% 1.63/0.60  fof(f374,plain,(
% 1.63/0.60    spl2_19 <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.63/0.60    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 1.63/0.60  fof(f693,plain,(
% 1.63/0.60    k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | (~spl2_3 | ~spl2_19)),
% 1.63/0.60    inference(unit_resulting_resolution,[],[f126,f376,f112])).
% 1.63/0.60  fof(f112,plain,(
% 1.63/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))) )),
% 1.63/0.60    inference(definition_unfolding,[],[f97,f81])).
% 1.63/0.60  fof(f97,plain,(
% 1.63/0.60    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.63/0.60    inference(cnf_transformation,[],[f54])).
% 1.63/0.60  fof(f54,plain,(
% 1.63/0.60    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.63/0.60    inference(flattening,[],[f53])).
% 1.63/0.60  fof(f53,plain,(
% 1.63/0.60    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 1.63/0.60    inference(ennf_transformation,[],[f18])).
% 1.63/0.60  fof(f18,axiom,(
% 1.63/0.60    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 1.63/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 1.63/0.60  fof(f376,plain,(
% 1.63/0.60    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_19),
% 1.63/0.60    inference(avatar_component_clause,[],[f374])).
% 1.63/0.60  fof(f578,plain,(
% 1.63/0.60    spl2_38 | ~spl2_3 | ~spl2_4),
% 1.63/0.60    inference(avatar_split_clause,[],[f572,f129,f124,f575])).
% 1.63/0.60  fof(f575,plain,(
% 1.63/0.60    spl2_38 <=> k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 1.63/0.60    introduced(avatar_definition,[new_symbols(naming,[spl2_38])])).
% 1.63/0.60  fof(f572,plain,(
% 1.63/0.60    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | (~spl2_3 | ~spl2_4)),
% 1.63/0.60    inference(unit_resulting_resolution,[],[f131,f126,f71])).
% 1.63/0.60  fof(f71,plain,(
% 1.63/0.60    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))) )),
% 1.63/0.60    inference(cnf_transformation,[],[f37])).
% 1.63/0.60  fof(f37,plain,(
% 1.63/0.60    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.63/0.60    inference(ennf_transformation,[],[f28])).
% 1.63/0.60  fof(f28,axiom,(
% 1.63/0.60    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 1.63/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).
% 1.63/0.60  fof(f518,plain,(
% 1.63/0.60    spl2_32 | ~spl2_3 | ~spl2_4),
% 1.63/0.60    inference(avatar_split_clause,[],[f504,f129,f124,f515])).
% 1.63/0.60  fof(f504,plain,(
% 1.63/0.60    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | (~spl2_3 | ~spl2_4)),
% 1.63/0.60    inference(unit_resulting_resolution,[],[f131,f126,f70])).
% 1.63/0.60  fof(f70,plain,(
% 1.63/0.60    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))) )),
% 1.63/0.60    inference(cnf_transformation,[],[f36])).
% 1.63/0.60  fof(f36,plain,(
% 1.63/0.60    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.63/0.60    inference(ennf_transformation,[],[f30])).
% 1.63/0.60  fof(f30,axiom,(
% 1.63/0.60    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 1.63/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).
% 1.63/0.60  fof(f377,plain,(
% 1.63/0.60    spl2_19 | ~spl2_3 | ~spl2_4),
% 1.63/0.60    inference(avatar_split_clause,[],[f363,f129,f124,f374])).
% 1.63/0.60  fof(f363,plain,(
% 1.63/0.60    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_3 | ~spl2_4)),
% 1.63/0.60    inference(unit_resulting_resolution,[],[f131,f126,f90])).
% 1.63/0.60  fof(f90,plain,(
% 1.63/0.60    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 1.63/0.60    inference(cnf_transformation,[],[f47])).
% 1.63/0.60  fof(f47,plain,(
% 1.63/0.60    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 1.63/0.60    inference(flattening,[],[f46])).
% 1.63/0.60  fof(f46,plain,(
% 1.63/0.60    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 1.63/0.60    inference(ennf_transformation,[],[f26])).
% 1.63/0.60  fof(f26,axiom,(
% 1.63/0.60    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 1.63/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).
% 1.63/0.60  fof(f137,plain,(
% 1.63/0.60    spl2_5),
% 1.63/0.60    inference(avatar_split_clause,[],[f62,f134])).
% 1.63/0.60  fof(f62,plain,(
% 1.63/0.60    v2_pre_topc(sK0)),
% 1.63/0.60    inference(cnf_transformation,[],[f60])).
% 1.63/0.60  fof(f60,plain,(
% 1.63/0.60    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 1.63/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f57,f59,f58])).
% 1.63/0.60  fof(f58,plain,(
% 1.63/0.60    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 1.63/0.60    introduced(choice_axiom,[])).
% 1.63/0.60  fof(f59,plain,(
% 1.63/0.60    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.63/0.60    introduced(choice_axiom,[])).
% 1.63/0.60  fof(f57,plain,(
% 1.63/0.60    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.63/0.60    inference(flattening,[],[f56])).
% 1.63/0.60  fof(f56,plain,(
% 1.63/0.60    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.63/0.60    inference(nnf_transformation,[],[f34])).
% 1.63/0.60  fof(f34,plain,(
% 1.63/0.60    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.63/0.60    inference(flattening,[],[f33])).
% 1.63/0.60  fof(f33,plain,(
% 1.63/0.60    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 1.63/0.60    inference(ennf_transformation,[],[f32])).
% 1.63/0.60  fof(f32,negated_conjecture,(
% 1.63/0.60    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 1.63/0.60    inference(negated_conjecture,[],[f31])).
% 1.63/0.60  fof(f31,conjecture,(
% 1.63/0.60    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 1.63/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).
% 1.63/0.60  fof(f132,plain,(
% 1.63/0.60    spl2_4),
% 1.63/0.60    inference(avatar_split_clause,[],[f63,f129])).
% 1.63/0.60  fof(f63,plain,(
% 1.63/0.60    l1_pre_topc(sK0)),
% 1.63/0.60    inference(cnf_transformation,[],[f60])).
% 1.63/0.60  fof(f127,plain,(
% 1.63/0.60    spl2_3),
% 1.63/0.60    inference(avatar_split_clause,[],[f64,f124])).
% 1.63/0.60  fof(f64,plain,(
% 1.63/0.60    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.63/0.60    inference(cnf_transformation,[],[f60])).
% 1.63/0.60  fof(f122,plain,(
% 1.63/0.60    spl2_1 | spl2_2),
% 1.63/0.60    inference(avatar_split_clause,[],[f65,f118,f114])).
% 1.63/0.60  fof(f65,plain,(
% 1.63/0.60    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)),
% 1.63/0.60    inference(cnf_transformation,[],[f60])).
% 1.63/0.60  fof(f121,plain,(
% 1.63/0.60    ~spl2_1 | ~spl2_2),
% 1.63/0.60    inference(avatar_split_clause,[],[f66,f118,f114])).
% 1.63/0.60  fof(f66,plain,(
% 1.63/0.60    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)),
% 1.63/0.60    inference(cnf_transformation,[],[f60])).
% 1.63/0.60  % SZS output end Proof for theBenchmark
% 1.63/0.60  % (1402)------------------------------
% 1.63/0.60  % (1402)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.63/0.60  % (1402)Termination reason: Refutation
% 1.63/0.60  
% 1.63/0.60  % (1402)Memory used [KB]: 9210
% 1.63/0.60  % (1402)Time elapsed: 0.135 s
% 1.63/0.60  % (1402)------------------------------
% 1.63/0.60  % (1402)------------------------------
% 1.63/0.61  % (1395)Success in time 0.248 s
%------------------------------------------------------------------------------
