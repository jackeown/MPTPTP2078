%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:12:24 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  193 ( 438 expanded)
%              Number of leaves         :   53 ( 184 expanded)
%              Depth                    :   13
%              Number of atoms          :  502 (1042 expanded)
%              Number of equality atoms :  124 ( 317 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f816,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f100,f101,f106,f111,f119,f128,f134,f142,f150,f184,f233,f264,f383,f479,f527,f657,f695,f697,f698,f699,f764,f768,f769,f770,f772,f808,f815])).

fof(f815,plain,
    ( ~ spl2_4
    | spl2_53
    | ~ spl2_9
    | ~ spl2_6
    | ~ spl2_34 ),
    inference(avatar_split_clause,[],[f814,f380,f124,f147,f524,f108])).

fof(f108,plain,
    ( spl2_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f524,plain,
    ( spl2_53
  <=> k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_53])])).

fof(f147,plain,
    ( spl2_9
  <=> m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f124,plain,
    ( spl2_6
  <=> u1_struct_0(sK0) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f380,plain,
    ( spl2_34
  <=> v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).

fof(f814,plain,
    ( ~ m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0)))
    | k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_6
    | ~ spl2_34 ),
    inference(forward_demodulation,[],[f813,f126])).

fof(f126,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f124])).

fof(f813,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))
    | ~ m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_34 ),
    inference(resolution,[],[f381,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ v1_tops_1(X1,X0)
      | k2_struct_0(X0) = k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | k2_struct_0(X0) != k2_pre_topc(X0,X1) )
            & ( k2_struct_0(X0) = k2_pre_topc(X0,X1)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).

fof(f381,plain,
    ( v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0)
    | ~ spl2_34 ),
    inference(avatar_component_clause,[],[f380])).

fof(f808,plain,
    ( spl2_73
    | ~ spl2_38 ),
    inference(avatar_split_clause,[],[f807,f398,f726])).

fof(f726,plain,
    ( spl2_73
  <=> k2_struct_0(sK0) = k5_xboole_0(k2_struct_0(sK0),k1_setfam_1(k6_enumset1(k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_73])])).

fof(f398,plain,
    ( spl2_38
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_38])])).

fof(f807,plain,
    ( k2_struct_0(sK0) = k5_xboole_0(k2_struct_0(sK0),k1_setfam_1(k6_enumset1(k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0)))
    | ~ spl2_38 ),
    inference(forward_demodulation,[],[f787,f87])).

fof(f87,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f53,f86])).

fof(f86,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f55,f52])).

fof(f52,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

fof(f55,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).

fof(f53,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f787,plain,
    ( k3_subset_1(k2_struct_0(sK0),k1_xboole_0) = k5_xboole_0(k2_struct_0(sK0),k1_setfam_1(k6_enumset1(k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0)))
    | ~ spl2_38 ),
    inference(resolution,[],[f399,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ) ),
    inference(definition_unfolding,[],[f69,f85])).

fof(f85,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f67,f84])).

fof(f84,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f65,f83])).

fof(f83,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f66,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f74,f81])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f75,f80])).

fof(f80,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f76,f79])).

fof(f79,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f77,f78])).

fof(f78,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f77,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f76,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f75,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f74,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f66,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f65,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f67,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f69,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f399,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl2_38 ),
    inference(avatar_component_clause,[],[f398])).

fof(f772,plain,
    ( k2_struct_0(sK0) != k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))
    | k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))) != k5_xboole_0(k2_struct_0(sK0),k1_setfam_1(k6_enumset1(k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)))))
    | k1_xboole_0 != k5_xboole_0(k2_struct_0(sK0),k1_setfam_1(k6_enumset1(k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0))))
    | k1_xboole_0 = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f770,plain,
    ( k1_tops_1(sK0,sK1) != k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)))
    | k1_xboole_0 != k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)))
    | k1_xboole_0 = k1_tops_1(sK0,sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f769,plain,
    ( k1_xboole_0 != k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)))
    | k2_struct_0(sK0) != k5_xboole_0(k2_struct_0(sK0),k1_setfam_1(k6_enumset1(k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0)))
    | k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)) != k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))))
    | k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)))) != k5_xboole_0(k2_struct_0(sK0),k1_setfam_1(k6_enumset1(k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))))))
    | k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f768,plain,
    ( ~ spl2_4
    | spl2_34
    | ~ spl2_7
    | ~ spl2_1
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f767,f124,f93,f131,f380,f108])).

fof(f131,plain,
    ( spl2_7
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f93,plain,
    ( spl2_1
  <=> v2_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f767,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl2_1
    | ~ spl2_6 ),
    inference(forward_demodulation,[],[f766,f126])).

fof(f766,plain,
    ( v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_1
    | ~ spl2_6 ),
    inference(forward_demodulation,[],[f765,f126])).

fof(f765,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_1 ),
    inference(resolution,[],[f94,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ v2_tops_1(X1,X0)
      | v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_1)).

fof(f94,plain,
    ( v2_tops_1(sK1,sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f93])).

fof(f764,plain,
    ( spl2_77
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f440,f131,f124,f108,f760])).

fof(f760,plain,
    ( spl2_77
  <=> k1_tops_1(sK0,sK1) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_77])])).

fof(f440,plain,
    ( k1_tops_1(sK0,sK1) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)))
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_7 ),
    inference(unit_resulting_resolution,[],[f133,f253])).

fof(f253,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | k1_tops_1(sK0,X0) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0))) )
    | ~ spl2_4
    | ~ spl2_6 ),
    inference(forward_demodulation,[],[f252,f126])).

fof(f252,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | k1_tops_1(sK0,X0) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) )
    | ~ spl2_4
    | ~ spl2_6 ),
    inference(forward_demodulation,[],[f245,f126])).

fof(f245,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_tops_1(sK0,X0) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) )
    | ~ spl2_4 ),
    inference(resolution,[],[f60,f110])).

fof(f110,plain,
    ( l1_pre_topc(sK0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f108])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).

fof(f133,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f131])).

fof(f699,plain,
    ( k1_xboole_0 != k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)))
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))),k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f698,plain,
    ( spl2_65
    | ~ spl2_20 ),
    inference(avatar_split_clause,[],[f652,f261,f659])).

fof(f659,plain,
    ( spl2_65
  <=> k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)) = k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_65])])).

fof(f261,plain,
    ( spl2_20
  <=> m1_subset_1(k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)),k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).

fof(f652,plain,
    ( k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)) = k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))))
    | ~ spl2_20 ),
    inference(resolution,[],[f263,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f263,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl2_20 ),
    inference(avatar_component_clause,[],[f261])).

fof(f697,plain,
    ( spl2_66
    | ~ spl2_20 ),
    inference(avatar_split_clause,[],[f651,f261,f664])).

fof(f664,plain,
    ( spl2_66
  <=> k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))) = k5_xboole_0(k2_struct_0(sK0),k1_setfam_1(k6_enumset1(k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_66])])).

fof(f651,plain,
    ( k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))) = k5_xboole_0(k2_struct_0(sK0),k1_setfam_1(k6_enumset1(k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)))))
    | ~ spl2_20 ),
    inference(resolution,[],[f263,f89])).

fof(f695,plain,
    ( spl2_68
    | ~ spl2_20 ),
    inference(avatar_split_clause,[],[f649,f261,f674])).

fof(f674,plain,
    ( spl2_68
  <=> k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)))) = k5_xboole_0(k2_struct_0(sK0),k1_setfam_1(k6_enumset1(k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_68])])).

fof(f649,plain,
    ( k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)))) = k5_xboole_0(k2_struct_0(sK0),k1_setfam_1(k6_enumset1(k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))))))
    | ~ spl2_20 ),
    inference(resolution,[],[f263,f275])).

fof(f275,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X1))
      | k3_subset_1(X1,k3_subset_1(X1,X2)) = k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k3_subset_1(X1,X2)))) ) ),
    inference(resolution,[],[f89,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f657,plain,
    ( spl2_64
    | ~ spl2_20 ),
    inference(avatar_split_clause,[],[f646,f261,f654])).

fof(f654,plain,
    ( spl2_64
  <=> m1_subset_1(k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))),k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_64])])).

fof(f646,plain,
    ( m1_subset_1(k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl2_20 ),
    inference(unit_resulting_resolution,[],[f263,f68])).

fof(f527,plain,
    ( ~ spl2_53
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_9
    | spl2_34 ),
    inference(avatar_split_clause,[],[f522,f380,f147,f124,f108,f524])).

fof(f522,plain,
    ( k2_struct_0(sK0) != k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_9
    | spl2_34 ),
    inference(unit_resulting_resolution,[],[f149,f382,f194])).

fof(f194,plain,
    ( ! [X0] :
        ( k2_struct_0(sK0) != k2_pre_topc(sK0,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | v1_tops_1(X0,sK0) )
    | ~ spl2_4
    | ~ spl2_6 ),
    inference(forward_demodulation,[],[f193,f126])).

fof(f193,plain,
    ( ! [X0] :
        ( k2_struct_0(sK0) != k2_pre_topc(sK0,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_tops_1(X0,sK0) )
    | ~ spl2_4 ),
    inference(resolution,[],[f62,f110])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | k2_struct_0(X0) != k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f382,plain,
    ( ~ v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0)
    | spl2_34 ),
    inference(avatar_component_clause,[],[f380])).

fof(f149,plain,
    ( m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f147])).

fof(f479,plain,
    ( spl2_45
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f478,f131,f124,f108,f97,f450])).

fof(f450,plain,
    ( spl2_45
  <=> k1_xboole_0 = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_45])])).

fof(f97,plain,
    ( spl2_2
  <=> k1_xboole_0 = k1_tops_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f478,plain,
    ( k1_xboole_0 = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)))
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_7 ),
    inference(forward_demodulation,[],[f447,f98])).

fof(f98,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f97])).

fof(f447,plain,
    ( k1_tops_1(sK0,sK1) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)))
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_7 ),
    inference(resolution,[],[f253,f133])).

fof(f383,plain,
    ( ~ spl2_34
    | spl2_1
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f376,f131,f124,f108,f93,f380])).

fof(f376,plain,
    ( ~ v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0)
    | spl2_1
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_7 ),
    inference(unit_resulting_resolution,[],[f95,f133,f218])).

fof(f218,plain,
    ( ! [X0] :
        ( ~ v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | v2_tops_1(X0,sK0) )
    | ~ spl2_4
    | ~ spl2_6 ),
    inference(forward_demodulation,[],[f217,f126])).

fof(f217,plain,
    ( ! [X0] :
        ( ~ v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_tops_1(X0,sK0) )
    | ~ spl2_4
    | ~ spl2_6 ),
    inference(forward_demodulation,[],[f216,f126])).

fof(f216,plain,
    ( ! [X0] :
        ( ~ v1_tops_1(k3_subset_1(u1_struct_0(sK0),X0),sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_tops_1(X0,sK0) )
    | ~ spl2_4 ),
    inference(resolution,[],[f64,f110])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f95,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f93])).

fof(f264,plain,
    ( spl2_20
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f256,f147,f124,f108,f261])).

fof(f256,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_9 ),
    inference(unit_resulting_resolution,[],[f149,f191])).

fof(f191,plain,
    ( ! [X0] :
        ( m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) )
    | ~ spl2_4
    | ~ spl2_6 ),
    inference(forward_demodulation,[],[f190,f126])).

fof(f190,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl2_4
    | ~ spl2_6 ),
    inference(forward_demodulation,[],[f187,f126])).

fof(f187,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl2_4 ),
    inference(resolution,[],[f71,f110])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f233,plain,
    ( spl2_17
    | ~ spl2_13 ),
    inference(avatar_split_clause,[],[f221,f181,f229])).

fof(f229,plain,
    ( spl2_17
  <=> k1_xboole_0 = k5_xboole_0(k2_struct_0(sK0),k1_setfam_1(k6_enumset1(k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f181,plain,
    ( spl2_13
  <=> r1_tarski(k2_struct_0(sK0),k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f221,plain,
    ( k1_xboole_0 = k5_xboole_0(k2_struct_0(sK0),k1_setfam_1(k6_enumset1(k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0))))
    | ~ spl2_13 ),
    inference(resolution,[],[f90,f183])).

fof(f183,plain,
    ( r1_tarski(k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f181])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ) ),
    inference(definition_unfolding,[],[f73,f85])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f184,plain,
    ( spl2_13
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f179,f138,f124,f108,f181])).

fof(f138,plain,
    ( spl2_8
  <=> k2_struct_0(sK0) = k2_pre_topc(sK0,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f179,plain,
    ( r1_tarski(k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_8 ),
    inference(forward_demodulation,[],[f178,f140])).

fof(f140,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,k2_struct_0(sK0))
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f138])).

fof(f178,plain,
    ( r1_tarski(k2_struct_0(sK0),k2_pre_topc(sK0,k2_struct_0(sK0)))
    | ~ spl2_4
    | ~ spl2_6 ),
    inference(forward_demodulation,[],[f176,f126])).

fof(f176,plain,
    ( r1_tarski(u1_struct_0(sK0),k2_pre_topc(sK0,u1_struct_0(sK0)))
    | ~ spl2_4 ),
    inference(unit_resulting_resolution,[],[f110,f120,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(X1,k2_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,k2_pre_topc(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).

fof(f120,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f88,f87])).

fof(f88,plain,(
    ! [X0] : m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) ),
    inference(definition_unfolding,[],[f54,f86])).

fof(f54,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f150,plain,
    ( spl2_9
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f144,f131,f147])).

fof(f144,plain,
    ( m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl2_7 ),
    inference(unit_resulting_resolution,[],[f133,f68])).

fof(f142,plain,
    ( spl2_8
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f136,f108,f138])).

fof(f136,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,k2_struct_0(sK0))
    | ~ spl2_4 ),
    inference(resolution,[],[f58,f110])).

fof(f58,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | k2_struct_0(X0) = k2_pre_topc(X0,k2_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = k2_pre_topc(X0,k2_struct_0(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => k2_struct_0(X0) = k2_pre_topc(X0,k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_tops_1)).

fof(f134,plain,
    ( spl2_7
    | ~ spl2_3
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f129,f124,f103,f131])).

fof(f103,plain,
    ( spl2_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f129,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl2_3
    | ~ spl2_6 ),
    inference(backward_demodulation,[],[f105,f126])).

fof(f105,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f103])).

fof(f128,plain,
    ( spl2_6
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f122,f115,f124])).

fof(f115,plain,
    ( spl2_5
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f122,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl2_5 ),
    inference(resolution,[],[f56,f117])).

fof(f117,plain,
    ( l1_struct_0(sK0)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f115])).

fof(f56,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f119,plain,
    ( spl2_5
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f113,f108,f115])).

fof(f113,plain,
    ( l1_struct_0(sK0)
    | ~ spl2_4 ),
    inference(resolution,[],[f57,f110])).

fof(f57,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f111,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f48,f108])).

fof(f48,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,
    ( ( k1_xboole_0 != k1_tops_1(sK0,sK1)
      | ~ v2_tops_1(sK1,sK0) )
    & ( k1_xboole_0 = k1_tops_1(sK0,sK1)
      | v2_tops_1(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f41,f43,f42])).

fof(f42,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( k1_xboole_0 != k1_tops_1(X0,X1)
              | ~ v2_tops_1(X1,X0) )
            & ( k1_xboole_0 = k1_tops_1(X0,X1)
              | v2_tops_1(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ( k1_xboole_0 != k1_tops_1(sK0,X1)
            | ~ v2_tops_1(X1,sK0) )
          & ( k1_xboole_0 = k1_tops_1(sK0,X1)
            | v2_tops_1(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ? [X1] :
        ( ( k1_xboole_0 != k1_tops_1(sK0,X1)
          | ~ v2_tops_1(X1,sK0) )
        & ( k1_xboole_0 = k1_tops_1(sK0,X1)
          | v2_tops_1(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( k1_xboole_0 != k1_tops_1(sK0,sK1)
        | ~ v2_tops_1(sK1,sK0) )
      & ( k1_xboole_0 = k1_tops_1(sK0,sK1)
        | v2_tops_1(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k1_xboole_0 != k1_tops_1(X0,X1)
            | ~ v2_tops_1(X1,X0) )
          & ( k1_xboole_0 = k1_tops_1(X0,X1)
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k1_xboole_0 != k1_tops_1(X0,X1)
            | ~ v2_tops_1(X1,X0) )
          & ( k1_xboole_0 = k1_tops_1(X0,X1)
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tops_1(X1,X0)
          <~> k1_xboole_0 = k1_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v2_tops_1(X1,X0)
            <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f25])).

fof(f25,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).

fof(f106,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f49,f103])).

fof(f49,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f44])).

fof(f101,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f50,f97,f93])).

fof(f50,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f100,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f51,f97,f93])).

fof(f51,plain,
    ( k1_xboole_0 != k1_tops_1(sK0,sK1)
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f44])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.12  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 19:33:34 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.20/0.44  % (18726)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.46  % (18718)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.47  % (18725)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.49  % (18729)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.50  % (18728)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.50  % (18721)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.50  % (18717)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.51  % (18719)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.51  % (18720)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.51  % (18722)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.51  % (18732)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.51  % (18727)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.52  % (18715)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.52  % (18723)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.52  % (18730)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.53  % (18716)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.53  % (18721)Refutation found. Thanks to Tanya!
% 0.20/0.53  % SZS status Theorem for theBenchmark
% 0.20/0.53  % SZS output start Proof for theBenchmark
% 0.20/0.53  fof(f816,plain,(
% 0.20/0.53    $false),
% 0.20/0.53    inference(avatar_sat_refutation,[],[f100,f101,f106,f111,f119,f128,f134,f142,f150,f184,f233,f264,f383,f479,f527,f657,f695,f697,f698,f699,f764,f768,f769,f770,f772,f808,f815])).
% 0.20/0.53  fof(f815,plain,(
% 0.20/0.53    ~spl2_4 | spl2_53 | ~spl2_9 | ~spl2_6 | ~spl2_34),
% 0.20/0.53    inference(avatar_split_clause,[],[f814,f380,f124,f147,f524,f108])).
% 0.20/0.53  fof(f108,plain,(
% 0.20/0.53    spl2_4 <=> l1_pre_topc(sK0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.20/0.53  fof(f524,plain,(
% 0.20/0.53    spl2_53 <=> k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_53])])).
% 0.20/0.53  fof(f147,plain,(
% 0.20/0.53    spl2_9 <=> m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.20/0.53  fof(f124,plain,(
% 0.20/0.53    spl2_6 <=> u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.20/0.53  fof(f380,plain,(
% 0.20/0.53    spl2_34 <=> v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).
% 0.20/0.53  fof(f814,plain,(
% 0.20/0.53    ~m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) | k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)) | ~l1_pre_topc(sK0) | (~spl2_6 | ~spl2_34)),
% 0.20/0.53    inference(forward_demodulation,[],[f813,f126])).
% 0.20/0.53  fof(f126,plain,(
% 0.20/0.53    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl2_6),
% 0.20/0.53    inference(avatar_component_clause,[],[f124])).
% 0.20/0.53  fof(f813,plain,(
% 0.20/0.53    k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)) | ~m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl2_34),
% 0.20/0.53    inference(resolution,[],[f381,f61])).
% 0.20/0.53  fof(f61,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~v1_tops_1(X1,X0) | k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f45])).
% 0.20/0.53  fof(f45,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | k2_struct_0(X0) != k2_pre_topc(X0,X1)) & (k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.53    inference(nnf_transformation,[],[f33])).
% 0.20/0.53  fof(f33,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f22])).
% 0.20/0.53  fof(f22,axiom,(
% 0.20/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).
% 0.20/0.53  fof(f381,plain,(
% 0.20/0.53    v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0) | ~spl2_34),
% 0.20/0.53    inference(avatar_component_clause,[],[f380])).
% 0.20/0.53  fof(f808,plain,(
% 0.20/0.53    spl2_73 | ~spl2_38),
% 0.20/0.53    inference(avatar_split_clause,[],[f807,f398,f726])).
% 0.20/0.53  fof(f726,plain,(
% 0.20/0.53    spl2_73 <=> k2_struct_0(sK0) = k5_xboole_0(k2_struct_0(sK0),k1_setfam_1(k6_enumset1(k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0)))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_73])])).
% 0.20/0.53  fof(f398,plain,(
% 0.20/0.53    spl2_38 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_38])])).
% 0.20/0.53  fof(f807,plain,(
% 0.20/0.53    k2_struct_0(sK0) = k5_xboole_0(k2_struct_0(sK0),k1_setfam_1(k6_enumset1(k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0))) | ~spl2_38),
% 0.20/0.53    inference(forward_demodulation,[],[f787,f87])).
% 0.20/0.53  fof(f87,plain,(
% 0.20/0.53    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 0.20/0.53    inference(definition_unfolding,[],[f53,f86])).
% 0.20/0.53  fof(f86,plain,(
% 0.20/0.53    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0)) )),
% 0.20/0.53    inference(definition_unfolding,[],[f55,f52])).
% 0.20/0.53  fof(f52,plain,(
% 0.20/0.53    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f9])).
% 0.20/0.53  fof(f9,axiom,(
% 0.20/0.53    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).
% 0.20/0.53  fof(f55,plain,(
% 0.20/0.53    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f15])).
% 0.20/0.53  fof(f15,axiom,(
% 0.20/0.53    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).
% 0.20/0.53  fof(f53,plain,(
% 0.20/0.53    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.20/0.53    inference(cnf_transformation,[],[f10])).
% 0.20/0.53  fof(f10,axiom,(
% 0.20/0.53    ! [X0] : k2_subset_1(X0) = X0),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 0.20/0.53  fof(f787,plain,(
% 0.20/0.53    k3_subset_1(k2_struct_0(sK0),k1_xboole_0) = k5_xboole_0(k2_struct_0(sK0),k1_setfam_1(k6_enumset1(k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0))) | ~spl2_38),
% 0.20/0.53    inference(resolution,[],[f399,f89])).
% 0.20/0.53  fof(f89,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 0.20/0.53    inference(definition_unfolding,[],[f69,f85])).
% 0.20/0.53  fof(f85,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 0.20/0.53    inference(definition_unfolding,[],[f67,f84])).
% 0.20/0.53  fof(f84,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 0.20/0.53    inference(definition_unfolding,[],[f65,f83])).
% 0.20/0.53  fof(f83,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.20/0.53    inference(definition_unfolding,[],[f66,f82])).
% 0.20/0.53  fof(f82,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.20/0.53    inference(definition_unfolding,[],[f74,f81])).
% 0.20/0.53  fof(f81,plain,(
% 0.20/0.53    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.20/0.53    inference(definition_unfolding,[],[f75,f80])).
% 0.20/0.53  fof(f80,plain,(
% 0.20/0.53    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.20/0.53    inference(definition_unfolding,[],[f76,f79])).
% 0.20/0.53  fof(f79,plain,(
% 0.20/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.20/0.53    inference(definition_unfolding,[],[f77,f78])).
% 0.20/0.53  fof(f78,plain,(
% 0.20/0.53    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f8])).
% 0.20/0.53  fof(f8,axiom,(
% 0.20/0.53    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 0.20/0.53  fof(f77,plain,(
% 0.20/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f7])).
% 0.20/0.53  fof(f7,axiom,(
% 0.20/0.53    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 0.20/0.53  fof(f76,plain,(
% 0.20/0.53    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f6])).
% 0.20/0.53  fof(f6,axiom,(
% 0.20/0.53    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 0.20/0.53  fof(f75,plain,(
% 0.20/0.53    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f5])).
% 0.20/0.53  fof(f5,axiom,(
% 0.20/0.53    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.20/0.53  fof(f74,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f4])).
% 0.20/0.53  fof(f4,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.53  fof(f66,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f3])).
% 0.20/0.53  fof(f3,axiom,(
% 0.20/0.53    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.53  fof(f65,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f16])).
% 0.20/0.53  fof(f16,axiom,(
% 0.20/0.53    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.20/0.53  fof(f67,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f2])).
% 0.20/0.53  fof(f2,axiom,(
% 0.20/0.53    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.20/0.53  fof(f69,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f36])).
% 0.20/0.53  fof(f36,plain,(
% 0.20/0.53    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f11])).
% 0.20/0.53  fof(f11,axiom,(
% 0.20/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 0.20/0.53  fof(f399,plain,(
% 0.20/0.53    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_struct_0(sK0))) | ~spl2_38),
% 0.20/0.53    inference(avatar_component_clause,[],[f398])).
% 0.20/0.53  fof(f772,plain,(
% 0.20/0.53    k2_struct_0(sK0) != k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)) | k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))) != k5_xboole_0(k2_struct_0(sK0),k1_setfam_1(k6_enumset1(k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))))) | k1_xboole_0 != k5_xboole_0(k2_struct_0(sK0),k1_setfam_1(k6_enumset1(k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0)))) | k1_xboole_0 = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)))),
% 0.20/0.53    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.53  fof(f770,plain,(
% 0.20/0.53    k1_tops_1(sK0,sK1) != k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))) | k1_xboole_0 != k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))) | k1_xboole_0 = k1_tops_1(sK0,sK1)),
% 0.20/0.53    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.53  fof(f769,plain,(
% 0.20/0.53    k1_xboole_0 != k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))) | k2_struct_0(sK0) != k5_xboole_0(k2_struct_0(sK0),k1_setfam_1(k6_enumset1(k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0))) | k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)) != k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)))) | k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)))) != k5_xboole_0(k2_struct_0(sK0),k1_setfam_1(k6_enumset1(k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)))))) | k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))),
% 0.20/0.53    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.53  fof(f768,plain,(
% 0.20/0.53    ~spl2_4 | spl2_34 | ~spl2_7 | ~spl2_1 | ~spl2_6),
% 0.20/0.53    inference(avatar_split_clause,[],[f767,f124,f93,f131,f380,f108])).
% 0.20/0.53  fof(f131,plain,(
% 0.20/0.53    spl2_7 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.20/0.53  fof(f93,plain,(
% 0.20/0.53    spl2_1 <=> v2_tops_1(sK1,sK0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.20/0.53  fof(f767,plain,(
% 0.20/0.53    ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0) | ~l1_pre_topc(sK0) | (~spl2_1 | ~spl2_6)),
% 0.20/0.53    inference(forward_demodulation,[],[f766,f126])).
% 0.20/0.53  fof(f766,plain,(
% 0.20/0.53    v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl2_1 | ~spl2_6)),
% 0.20/0.53    inference(forward_demodulation,[],[f765,f126])).
% 0.20/0.53  fof(f765,plain,(
% 0.20/0.53    v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl2_1),
% 0.20/0.53    inference(resolution,[],[f94,f63])).
% 0.20/0.53  fof(f63,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~v2_tops_1(X1,X0) | v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f46])).
% 0.20/0.53  fof(f46,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | ~v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.53    inference(nnf_transformation,[],[f34])).
% 0.20/0.53  fof(f34,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f23])).
% 0.20/0.53  fof(f23,axiom,(
% 0.20/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_1)).
% 0.20/0.53  fof(f94,plain,(
% 0.20/0.53    v2_tops_1(sK1,sK0) | ~spl2_1),
% 0.20/0.53    inference(avatar_component_clause,[],[f93])).
% 0.20/0.53  fof(f764,plain,(
% 0.20/0.53    spl2_77 | ~spl2_4 | ~spl2_6 | ~spl2_7),
% 0.20/0.53    inference(avatar_split_clause,[],[f440,f131,f124,f108,f760])).
% 0.20/0.53  fof(f760,plain,(
% 0.20/0.53    spl2_77 <=> k1_tops_1(sK0,sK1) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_77])])).
% 0.20/0.53  fof(f440,plain,(
% 0.20/0.53    k1_tops_1(sK0,sK1) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))) | (~spl2_4 | ~spl2_6 | ~spl2_7)),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f133,f253])).
% 0.20/0.53  fof(f253,plain,(
% 0.20/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k1_tops_1(sK0,X0) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0)))) ) | (~spl2_4 | ~spl2_6)),
% 0.20/0.53    inference(forward_demodulation,[],[f252,f126])).
% 0.20/0.53  fof(f252,plain,(
% 0.20/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k1_tops_1(sK0,X0) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)))) ) | (~spl2_4 | ~spl2_6)),
% 0.20/0.53    inference(forward_demodulation,[],[f245,f126])).
% 0.20/0.53  fof(f245,plain,(
% 0.20/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_tops_1(sK0,X0) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)))) ) | ~spl2_4),
% 0.20/0.53    inference(resolution,[],[f60,f110])).
% 0.20/0.53  fof(f110,plain,(
% 0.20/0.53    l1_pre_topc(sK0) | ~spl2_4),
% 0.20/0.53    inference(avatar_component_clause,[],[f108])).
% 0.20/0.53  fof(f60,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f32])).
% 0.20/0.53  fof(f32,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f21])).
% 0.20/0.53  fof(f21,axiom,(
% 0.20/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).
% 0.20/0.53  fof(f133,plain,(
% 0.20/0.53    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | ~spl2_7),
% 0.20/0.53    inference(avatar_component_clause,[],[f131])).
% 0.20/0.53  fof(f699,plain,(
% 0.20/0.53    k1_xboole_0 != k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))) | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))),k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.20/0.53    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.53  fof(f698,plain,(
% 0.20/0.53    spl2_65 | ~spl2_20),
% 0.20/0.53    inference(avatar_split_clause,[],[f652,f261,f659])).
% 0.20/0.53  fof(f659,plain,(
% 0.20/0.53    spl2_65 <=> k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)) = k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_65])])).
% 0.20/0.53  fof(f261,plain,(
% 0.20/0.53    spl2_20 <=> m1_subset_1(k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)),k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).
% 0.20/0.53  fof(f652,plain,(
% 0.20/0.53    k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)) = k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)))) | ~spl2_20),
% 0.20/0.53    inference(resolution,[],[f263,f70])).
% 0.20/0.53  fof(f70,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 0.20/0.53    inference(cnf_transformation,[],[f37])).
% 0.20/0.53  fof(f37,plain,(
% 0.20/0.53    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f14])).
% 0.20/0.53  fof(f14,axiom,(
% 0.20/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 0.20/0.53  fof(f263,plain,(
% 0.20/0.53    m1_subset_1(k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)),k1_zfmisc_1(k2_struct_0(sK0))) | ~spl2_20),
% 0.20/0.53    inference(avatar_component_clause,[],[f261])).
% 0.20/0.53  fof(f697,plain,(
% 0.20/0.53    spl2_66 | ~spl2_20),
% 0.20/0.53    inference(avatar_split_clause,[],[f651,f261,f664])).
% 0.20/0.53  fof(f664,plain,(
% 0.20/0.53    spl2_66 <=> k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))) = k5_xboole_0(k2_struct_0(sK0),k1_setfam_1(k6_enumset1(k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)))))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_66])])).
% 0.20/0.53  fof(f651,plain,(
% 0.20/0.53    k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))) = k5_xboole_0(k2_struct_0(sK0),k1_setfam_1(k6_enumset1(k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))))) | ~spl2_20),
% 0.20/0.53    inference(resolution,[],[f263,f89])).
% 0.20/0.53  fof(f695,plain,(
% 0.20/0.53    spl2_68 | ~spl2_20),
% 0.20/0.53    inference(avatar_split_clause,[],[f649,f261,f674])).
% 0.20/0.53  fof(f674,plain,(
% 0.20/0.53    spl2_68 <=> k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)))) = k5_xboole_0(k2_struct_0(sK0),k1_setfam_1(k6_enumset1(k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))))))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_68])])).
% 0.20/0.53  fof(f649,plain,(
% 0.20/0.53    k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)))) = k5_xboole_0(k2_struct_0(sK0),k1_setfam_1(k6_enumset1(k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)))))) | ~spl2_20),
% 0.20/0.53    inference(resolution,[],[f263,f275])).
% 0.20/0.53  fof(f275,plain,(
% 0.20/0.53    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X1)) | k3_subset_1(X1,k3_subset_1(X1,X2)) = k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k3_subset_1(X1,X2))))) )),
% 0.20/0.53    inference(resolution,[],[f89,f68])).
% 0.20/0.53  fof(f68,plain,(
% 0.20/0.53    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f35])).
% 0.20/0.53  fof(f35,plain,(
% 0.20/0.53    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f13])).
% 0.20/0.53  fof(f13,axiom,(
% 0.20/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 0.20/0.53  fof(f657,plain,(
% 0.20/0.53    spl2_64 | ~spl2_20),
% 0.20/0.53    inference(avatar_split_clause,[],[f646,f261,f654])).
% 0.20/0.53  fof(f654,plain,(
% 0.20/0.53    spl2_64 <=> m1_subset_1(k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))),k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_64])])).
% 0.20/0.53  fof(f646,plain,(
% 0.20/0.53    m1_subset_1(k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))),k1_zfmisc_1(k2_struct_0(sK0))) | ~spl2_20),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f263,f68])).
% 0.20/0.53  fof(f527,plain,(
% 0.20/0.53    ~spl2_53 | ~spl2_4 | ~spl2_6 | ~spl2_9 | spl2_34),
% 0.20/0.53    inference(avatar_split_clause,[],[f522,f380,f147,f124,f108,f524])).
% 0.20/0.53  fof(f522,plain,(
% 0.20/0.53    k2_struct_0(sK0) != k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)) | (~spl2_4 | ~spl2_6 | ~spl2_9 | spl2_34)),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f149,f382,f194])).
% 0.20/0.53  fof(f194,plain,(
% 0.20/0.53    ( ! [X0] : (k2_struct_0(sK0) != k2_pre_topc(sK0,X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | v1_tops_1(X0,sK0)) ) | (~spl2_4 | ~spl2_6)),
% 0.20/0.53    inference(forward_demodulation,[],[f193,f126])).
% 0.20/0.53  fof(f193,plain,(
% 0.20/0.53    ( ! [X0] : (k2_struct_0(sK0) != k2_pre_topc(sK0,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_tops_1(X0,sK0)) ) | ~spl2_4),
% 0.20/0.53    inference(resolution,[],[f62,f110])).
% 0.20/0.53  fof(f62,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~l1_pre_topc(X0) | k2_struct_0(X0) != k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_tops_1(X1,X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f45])).
% 0.20/0.53  fof(f382,plain,(
% 0.20/0.53    ~v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0) | spl2_34),
% 0.20/0.53    inference(avatar_component_clause,[],[f380])).
% 0.20/0.53  fof(f149,plain,(
% 0.20/0.53    m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) | ~spl2_9),
% 0.20/0.53    inference(avatar_component_clause,[],[f147])).
% 0.20/0.53  fof(f479,plain,(
% 0.20/0.53    spl2_45 | ~spl2_2 | ~spl2_4 | ~spl2_6 | ~spl2_7),
% 0.20/0.53    inference(avatar_split_clause,[],[f478,f131,f124,f108,f97,f450])).
% 0.20/0.53  fof(f450,plain,(
% 0.20/0.53    spl2_45 <=> k1_xboole_0 = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_45])])).
% 0.20/0.53  fof(f97,plain,(
% 0.20/0.53    spl2_2 <=> k1_xboole_0 = k1_tops_1(sK0,sK1)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.20/0.53  fof(f478,plain,(
% 0.20/0.53    k1_xboole_0 = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))) | (~spl2_2 | ~spl2_4 | ~spl2_6 | ~spl2_7)),
% 0.20/0.53    inference(forward_demodulation,[],[f447,f98])).
% 0.20/0.53  fof(f98,plain,(
% 0.20/0.53    k1_xboole_0 = k1_tops_1(sK0,sK1) | ~spl2_2),
% 0.20/0.53    inference(avatar_component_clause,[],[f97])).
% 0.20/0.53  fof(f447,plain,(
% 0.20/0.53    k1_tops_1(sK0,sK1) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))) | (~spl2_4 | ~spl2_6 | ~spl2_7)),
% 0.20/0.53    inference(resolution,[],[f253,f133])).
% 0.20/0.53  fof(f383,plain,(
% 0.20/0.53    ~spl2_34 | spl2_1 | ~spl2_4 | ~spl2_6 | ~spl2_7),
% 0.20/0.53    inference(avatar_split_clause,[],[f376,f131,f124,f108,f93,f380])).
% 0.20/0.53  fof(f376,plain,(
% 0.20/0.53    ~v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0) | (spl2_1 | ~spl2_4 | ~spl2_6 | ~spl2_7)),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f95,f133,f218])).
% 0.20/0.53  fof(f218,plain,(
% 0.20/0.53    ( ! [X0] : (~v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | v2_tops_1(X0,sK0)) ) | (~spl2_4 | ~spl2_6)),
% 0.20/0.53    inference(forward_demodulation,[],[f217,f126])).
% 0.20/0.53  fof(f217,plain,(
% 0.20/0.53    ( ! [X0] : (~v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tops_1(X0,sK0)) ) | (~spl2_4 | ~spl2_6)),
% 0.20/0.53    inference(forward_demodulation,[],[f216,f126])).
% 0.20/0.53  fof(f216,plain,(
% 0.20/0.53    ( ! [X0] : (~v1_tops_1(k3_subset_1(u1_struct_0(sK0),X0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tops_1(X0,sK0)) ) | ~spl2_4),
% 0.20/0.53    inference(resolution,[],[f64,f110])).
% 0.20/0.53  fof(f64,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_tops_1(X1,X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f46])).
% 0.20/0.53  fof(f95,plain,(
% 0.20/0.53    ~v2_tops_1(sK1,sK0) | spl2_1),
% 0.20/0.53    inference(avatar_component_clause,[],[f93])).
% 0.20/0.53  fof(f264,plain,(
% 0.20/0.53    spl2_20 | ~spl2_4 | ~spl2_6 | ~spl2_9),
% 0.20/0.53    inference(avatar_split_clause,[],[f256,f147,f124,f108,f261])).
% 0.20/0.53  fof(f256,plain,(
% 0.20/0.53    m1_subset_1(k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)),k1_zfmisc_1(k2_struct_0(sK0))) | (~spl2_4 | ~spl2_6 | ~spl2_9)),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f149,f191])).
% 0.20/0.53  fof(f191,plain,(
% 0.20/0.53    ( ! [X0] : (m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))) ) | (~spl2_4 | ~spl2_6)),
% 0.20/0.53    inference(forward_demodulation,[],[f190,f126])).
% 0.20/0.53  fof(f190,plain,(
% 0.20/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl2_4 | ~spl2_6)),
% 0.20/0.53    inference(forward_demodulation,[],[f187,f126])).
% 0.20/0.53  fof(f187,plain,(
% 0.20/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl2_4),
% 0.20/0.53    inference(resolution,[],[f71,f110])).
% 0.20/0.53  fof(f71,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f39])).
% 0.20/0.53  fof(f39,plain,(
% 0.20/0.53    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.20/0.53    inference(flattening,[],[f38])).
% 0.20/0.53  fof(f38,plain,(
% 0.20/0.53    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f18])).
% 0.20/0.53  fof(f18,axiom,(
% 0.20/0.53    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 0.20/0.53  fof(f233,plain,(
% 0.20/0.53    spl2_17 | ~spl2_13),
% 0.20/0.53    inference(avatar_split_clause,[],[f221,f181,f229])).
% 0.20/0.53  fof(f229,plain,(
% 0.20/0.53    spl2_17 <=> k1_xboole_0 = k5_xboole_0(k2_struct_0(sK0),k1_setfam_1(k6_enumset1(k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0))))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 0.20/0.53  fof(f181,plain,(
% 0.20/0.53    spl2_13 <=> r1_tarski(k2_struct_0(sK0),k2_struct_0(sK0))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.20/0.53  fof(f221,plain,(
% 0.20/0.53    k1_xboole_0 = k5_xboole_0(k2_struct_0(sK0),k1_setfam_1(k6_enumset1(k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0)))) | ~spl2_13),
% 0.20/0.53    inference(resolution,[],[f90,f183])).
% 0.20/0.53  fof(f183,plain,(
% 0.20/0.53    r1_tarski(k2_struct_0(sK0),k2_struct_0(sK0)) | ~spl2_13),
% 0.20/0.53    inference(avatar_component_clause,[],[f181])).
% 0.20/0.53  fof(f90,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 0.20/0.53    inference(definition_unfolding,[],[f73,f85])).
% 0.20/0.53  fof(f73,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f47])).
% 0.20/0.53  fof(f47,plain,(
% 0.20/0.53    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.20/0.53    inference(nnf_transformation,[],[f1])).
% 0.20/0.53  fof(f1,axiom,(
% 0.20/0.53    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.20/0.53  fof(f184,plain,(
% 0.20/0.53    spl2_13 | ~spl2_4 | ~spl2_6 | ~spl2_8),
% 0.20/0.53    inference(avatar_split_clause,[],[f179,f138,f124,f108,f181])).
% 0.20/0.53  fof(f138,plain,(
% 0.20/0.53    spl2_8 <=> k2_struct_0(sK0) = k2_pre_topc(sK0,k2_struct_0(sK0))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.20/0.53  fof(f179,plain,(
% 0.20/0.53    r1_tarski(k2_struct_0(sK0),k2_struct_0(sK0)) | (~spl2_4 | ~spl2_6 | ~spl2_8)),
% 0.20/0.53    inference(forward_demodulation,[],[f178,f140])).
% 0.20/0.53  fof(f140,plain,(
% 0.20/0.53    k2_struct_0(sK0) = k2_pre_topc(sK0,k2_struct_0(sK0)) | ~spl2_8),
% 0.20/0.53    inference(avatar_component_clause,[],[f138])).
% 0.20/0.53  fof(f178,plain,(
% 0.20/0.53    r1_tarski(k2_struct_0(sK0),k2_pre_topc(sK0,k2_struct_0(sK0))) | (~spl2_4 | ~spl2_6)),
% 0.20/0.53    inference(forward_demodulation,[],[f176,f126])).
% 0.20/0.53  fof(f176,plain,(
% 0.20/0.53    r1_tarski(u1_struct_0(sK0),k2_pre_topc(sK0,u1_struct_0(sK0))) | ~spl2_4),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f110,f120,f59])).
% 0.20/0.53  fof(f59,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(X1,k2_pre_topc(X0,X1))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f31])).
% 0.20/0.53  fof(f31,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f20])).
% 0.20/0.53  fof(f20,axiom,(
% 0.20/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(X1,k2_pre_topc(X0,X1))))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).
% 0.20/0.53  fof(f120,plain,(
% 0.20/0.53    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.20/0.53    inference(forward_demodulation,[],[f88,f87])).
% 0.20/0.53  fof(f88,plain,(
% 0.20/0.53    ( ! [X0] : (m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0))) )),
% 0.20/0.53    inference(definition_unfolding,[],[f54,f86])).
% 0.20/0.53  fof(f54,plain,(
% 0.20/0.53    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f12])).
% 0.20/0.53  fof(f12,axiom,(
% 0.20/0.53    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.20/0.53  fof(f150,plain,(
% 0.20/0.53    spl2_9 | ~spl2_7),
% 0.20/0.53    inference(avatar_split_clause,[],[f144,f131,f147])).
% 0.20/0.53  fof(f144,plain,(
% 0.20/0.53    m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) | ~spl2_7),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f133,f68])).
% 0.20/0.53  fof(f142,plain,(
% 0.20/0.53    spl2_8 | ~spl2_4),
% 0.20/0.53    inference(avatar_split_clause,[],[f136,f108,f138])).
% 0.20/0.53  fof(f136,plain,(
% 0.20/0.53    k2_struct_0(sK0) = k2_pre_topc(sK0,k2_struct_0(sK0)) | ~spl2_4),
% 0.20/0.53    inference(resolution,[],[f58,f110])).
% 0.20/0.53  fof(f58,plain,(
% 0.20/0.53    ( ! [X0] : (~l1_pre_topc(X0) | k2_struct_0(X0) = k2_pre_topc(X0,k2_struct_0(X0))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f30])).
% 0.20/0.53  fof(f30,plain,(
% 0.20/0.53    ! [X0] : (k2_struct_0(X0) = k2_pre_topc(X0,k2_struct_0(X0)) | ~l1_pre_topc(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f24])).
% 0.20/0.53  fof(f24,axiom,(
% 0.20/0.53    ! [X0] : (l1_pre_topc(X0) => k2_struct_0(X0) = k2_pre_topc(X0,k2_struct_0(X0)))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_tops_1)).
% 0.20/0.53  fof(f134,plain,(
% 0.20/0.53    spl2_7 | ~spl2_3 | ~spl2_6),
% 0.20/0.53    inference(avatar_split_clause,[],[f129,f124,f103,f131])).
% 0.20/0.53  fof(f103,plain,(
% 0.20/0.53    spl2_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.20/0.53  fof(f129,plain,(
% 0.20/0.53    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | (~spl2_3 | ~spl2_6)),
% 0.20/0.53    inference(backward_demodulation,[],[f105,f126])).
% 0.20/0.53  fof(f105,plain,(
% 0.20/0.53    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_3),
% 0.20/0.53    inference(avatar_component_clause,[],[f103])).
% 0.20/0.53  fof(f128,plain,(
% 0.20/0.53    spl2_6 | ~spl2_5),
% 0.20/0.53    inference(avatar_split_clause,[],[f122,f115,f124])).
% 0.20/0.53  fof(f115,plain,(
% 0.20/0.53    spl2_5 <=> l1_struct_0(sK0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.20/0.53  fof(f122,plain,(
% 0.20/0.53    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl2_5),
% 0.20/0.53    inference(resolution,[],[f56,f117])).
% 0.20/0.53  fof(f117,plain,(
% 0.20/0.53    l1_struct_0(sK0) | ~spl2_5),
% 0.20/0.53    inference(avatar_component_clause,[],[f115])).
% 0.20/0.53  fof(f56,plain,(
% 0.20/0.53    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f28])).
% 0.20/0.53  fof(f28,plain,(
% 0.20/0.53    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f17])).
% 0.20/0.53  fof(f17,axiom,(
% 0.20/0.53    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.20/0.53  fof(f119,plain,(
% 0.20/0.53    spl2_5 | ~spl2_4),
% 0.20/0.53    inference(avatar_split_clause,[],[f113,f108,f115])).
% 0.20/0.53  fof(f113,plain,(
% 0.20/0.53    l1_struct_0(sK0) | ~spl2_4),
% 0.20/0.53    inference(resolution,[],[f57,f110])).
% 0.20/0.53  fof(f57,plain,(
% 0.20/0.53    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f29])).
% 0.20/0.53  fof(f29,plain,(
% 0.20/0.53    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f19])).
% 0.20/0.53  fof(f19,axiom,(
% 0.20/0.53    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.20/0.53  fof(f111,plain,(
% 0.20/0.53    spl2_4),
% 0.20/0.53    inference(avatar_split_clause,[],[f48,f108])).
% 0.20/0.53  fof(f48,plain,(
% 0.20/0.53    l1_pre_topc(sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f44])).
% 0.20/0.53  fof(f44,plain,(
% 0.20/0.53    ((k1_xboole_0 != k1_tops_1(sK0,sK1) | ~v2_tops_1(sK1,sK0)) & (k1_xboole_0 = k1_tops_1(sK0,sK1) | v2_tops_1(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f41,f43,f42])).
% 0.20/0.53  fof(f42,plain,(
% 0.20/0.53    ? [X0] : (? [X1] : ((k1_xboole_0 != k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0)) & (k1_xboole_0 = k1_tops_1(X0,X1) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : ((k1_xboole_0 != k1_tops_1(sK0,X1) | ~v2_tops_1(X1,sK0)) & (k1_xboole_0 = k1_tops_1(sK0,X1) | v2_tops_1(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f43,plain,(
% 0.20/0.53    ? [X1] : ((k1_xboole_0 != k1_tops_1(sK0,X1) | ~v2_tops_1(X1,sK0)) & (k1_xboole_0 = k1_tops_1(sK0,X1) | v2_tops_1(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k1_xboole_0 != k1_tops_1(sK0,sK1) | ~v2_tops_1(sK1,sK0)) & (k1_xboole_0 = k1_tops_1(sK0,sK1) | v2_tops_1(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f41,plain,(
% 0.20/0.53    ? [X0] : (? [X1] : ((k1_xboole_0 != k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0)) & (k1_xboole_0 = k1_tops_1(X0,X1) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.20/0.53    inference(flattening,[],[f40])).
% 0.20/0.53  fof(f40,plain,(
% 0.20/0.53    ? [X0] : (? [X1] : (((k1_xboole_0 != k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0)) & (k1_xboole_0 = k1_tops_1(X0,X1) | v2_tops_1(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.20/0.53    inference(nnf_transformation,[],[f27])).
% 0.20/0.53  fof(f27,plain,(
% 0.20/0.53    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> k1_xboole_0 = k1_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f26])).
% 0.20/0.53  fof(f26,negated_conjecture,(
% 0.20/0.53    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 0.20/0.53    inference(negated_conjecture,[],[f25])).
% 0.20/0.53  fof(f25,conjecture,(
% 0.20/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).
% 0.20/0.53  fof(f106,plain,(
% 0.20/0.53    spl2_3),
% 0.20/0.53    inference(avatar_split_clause,[],[f49,f103])).
% 0.20/0.53  fof(f49,plain,(
% 0.20/0.53    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.53    inference(cnf_transformation,[],[f44])).
% 0.20/0.53  fof(f101,plain,(
% 0.20/0.53    spl2_1 | spl2_2),
% 0.20/0.53    inference(avatar_split_clause,[],[f50,f97,f93])).
% 0.20/0.53  fof(f50,plain,(
% 0.20/0.53    k1_xboole_0 = k1_tops_1(sK0,sK1) | v2_tops_1(sK1,sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f44])).
% 0.20/0.53  fof(f100,plain,(
% 0.20/0.53    ~spl2_1 | ~spl2_2),
% 0.20/0.53    inference(avatar_split_clause,[],[f51,f97,f93])).
% 0.20/0.53  fof(f51,plain,(
% 0.20/0.53    k1_xboole_0 != k1_tops_1(sK0,sK1) | ~v2_tops_1(sK1,sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f44])).
% 0.20/0.53  % SZS output end Proof for theBenchmark
% 0.20/0.53  % (18721)------------------------------
% 0.20/0.53  % (18721)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (18721)Termination reason: Refutation
% 0.20/0.53  
% 0.20/0.53  % (18721)Memory used [KB]: 6652
% 0.20/0.53  % (18721)Time elapsed: 0.085 s
% 0.20/0.53  % (18721)------------------------------
% 0.20/0.53  % (18721)------------------------------
% 0.20/0.53  % (18731)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.53  % (18713)Success in time 0.188 s
%------------------------------------------------------------------------------
