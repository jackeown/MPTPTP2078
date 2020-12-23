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
% DateTime   : Thu Dec  3 13:11:56 EST 2020

% Result     : Theorem 2.29s
% Output     : Refutation 2.29s
% Verified   : 
% Statistics : Number of formulae       :  165 ( 643 expanded)
%              Number of leaves         :   37 ( 224 expanded)
%              Depth                    :   16
%              Number of atoms          :  416 (1311 expanded)
%              Number of equality atoms :  103 ( 470 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3302,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f103,f108,f113,f137,f168,f220,f404,f2792,f2799,f2809,f3101,f3136,f3189,f3289])).

fof(f3289,plain,
    ( ~ spl2_3
    | ~ spl2_5
    | ~ spl2_48
    | ~ spl2_51
    | ~ spl2_52 ),
    inference(avatar_contradiction_clause,[],[f3288])).

fof(f3288,plain,
    ( $false
    | ~ spl2_3
    | ~ spl2_5
    | ~ spl2_48
    | ~ spl2_51
    | ~ spl2_52 ),
    inference(subsumption_resolution,[],[f3287,f132])).

fof(f132,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f130])).

fof(f130,plain,
    ( spl2_5
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f3287,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | ~ spl2_3
    | ~ spl2_48
    | ~ spl2_51
    | ~ spl2_52 ),
    inference(subsumption_resolution,[],[f3105,f3281])).

fof(f3281,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_48
    | ~ spl2_51
    | ~ spl2_52 ),
    inference(forward_demodulation,[],[f3280,f3178])).

fof(f3178,plain,
    ( k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_48
    | ~ spl2_51 ),
    inference(forward_demodulation,[],[f3153,f3174])).

fof(f3174,plain,
    ( k1_tops_1(sK0,sK1) = k3_subset_1(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_48
    | ~ spl2_51 ),
    inference(forward_demodulation,[],[f3157,f2808])).

fof(f2808,plain,
    ( k1_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_48 ),
    inference(avatar_component_clause,[],[f2806])).

fof(f2806,plain,
    ( spl2_48
  <=> k1_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_48])])).

fof(f3157,plain,
    ( k7_subset_1(sK1,sK1,k2_tops_1(sK0,sK1)) = k3_subset_1(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_51 ),
    inference(unit_resulting_resolution,[],[f3135,f759])).

fof(f759,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | k3_subset_1(X0,X1) = k7_subset_1(X0,X0,X1) ) ),
    inference(backward_demodulation,[],[f170,f696])).

fof(f696,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k7_subset_1(X0,X0,X1) ),
    inference(unit_resulting_resolution,[],[f389,f95])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) ) ),
    inference(definition_unfolding,[],[f82,f87])).

fof(f87,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f71,f68])).

fof(f68,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f71,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f389,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f323,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f323,plain,(
    ! [X5] : r1_tarski(X5,X5) ),
    inference(superposition,[],[f185,f114])).

fof(f114,plain,(
    ! [X0] : k3_tarski(k2_tarski(k1_xboole_0,X0)) = X0 ),
    inference(superposition,[],[f88,f67])).

fof(f67,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f88,plain,(
    ! [X0] : k3_tarski(k2_tarski(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f61,f69])).

fof(f69,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f61,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f185,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k2_tarski(X1,X0))) ),
    inference(unit_resulting_resolution,[],[f89,f97])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X2)
      | r1_tarski(X0,k3_tarski(k2_tarski(X1,X2))) ) ),
    inference(definition_unfolding,[],[f84,f69,f87])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f89,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0) ),
    inference(definition_unfolding,[],[f66,f87])).

fof(f66,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f170,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))
      | ~ r1_tarski(X1,X0) ) ),
    inference(resolution,[],[f93,f81])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ) ),
    inference(definition_unfolding,[],[f75,f87])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f3135,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_51 ),
    inference(avatar_component_clause,[],[f3133])).

fof(f3133,plain,
    ( spl2_51
  <=> r1_tarski(k2_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_51])])).

fof(f3153,plain,
    ( k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k3_subset_1(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_51 ),
    inference(unit_resulting_resolution,[],[f3135,f148])).

fof(f148,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(resolution,[],[f76,f81])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f3280,plain,
    ( k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1)) = k3_subset_1(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_48
    | ~ spl2_51
    | ~ spl2_52 ),
    inference(forward_demodulation,[],[f3234,f3174])).

fof(f3234,plain,
    ( k3_subset_1(sK1,k3_subset_1(sK1,k2_tops_1(sK0,sK1))) = k7_subset_1(sK1,sK1,k3_subset_1(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_52 ),
    inference(resolution,[],[f3188,f785])).

fof(f785,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(X2))
      | k3_subset_1(X2,k3_subset_1(X2,X3)) = k7_subset_1(X2,X2,k3_subset_1(X2,X3)) ) ),
    inference(backward_demodulation,[],[f171,f696])).

fof(f171,plain,(
    ! [X2,X3] :
      ( k3_subset_1(X2,k3_subset_1(X2,X3)) = k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,k3_subset_1(X2,X3))))
      | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ) ),
    inference(resolution,[],[f93,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f3188,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ spl2_52 ),
    inference(avatar_component_clause,[],[f3186])).

fof(f3186,plain,
    ( spl2_52
  <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_52])])).

fof(f3105,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1))
    | ~ v4_pre_topc(sK1,sK0)
    | ~ spl2_3 ),
    inference(forward_demodulation,[],[f60,f804])).

fof(f804,plain,
    ( ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0)
    | ~ spl2_3 ),
    inference(backward_demodulation,[],[f191,f696])).

fof(f191,plain,
    ( ! [X0] : k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X0))) = k7_subset_1(u1_struct_0(sK0),sK1,X0)
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f112,f95])).

fof(f112,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl2_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f60,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,
    ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | ~ v4_pre_topc(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | v4_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f51,f53,f52])).

fof(f52,plain,
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

fof(f53,plain,
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

fof(f51,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f26])).

fof(f26,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).

fof(f3189,plain,
    ( spl2_52
    | ~ spl2_51 ),
    inference(avatar_split_clause,[],[f3138,f3133,f3186])).

fof(f3138,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ spl2_51 ),
    inference(unit_resulting_resolution,[],[f3135,f81])).

fof(f3136,plain,
    ( spl2_51
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f3107,f130,f110,f105,f3133])).

fof(f105,plain,
    ( spl2_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f3107,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(unit_resulting_resolution,[],[f107,f112,f132,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k2_tops_1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => r1_tarski(k2_tops_1(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_tops_1)).

fof(f107,plain,
    ( l1_pre_topc(sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f105])).

fof(f3101,plain,
    ( spl2_5
    | ~ spl2_7
    | ~ spl2_45
    | ~ spl2_46 ),
    inference(avatar_contradiction_clause,[],[f3100])).

fof(f3100,plain,
    ( $false
    | spl2_5
    | ~ spl2_7
    | ~ spl2_45
    | ~ spl2_46 ),
    inference(subsumption_resolution,[],[f3091,f131])).

fof(f131,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | spl2_5 ),
    inference(avatar_component_clause,[],[f130])).

fof(f3091,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ spl2_7
    | ~ spl2_45
    | ~ spl2_46 ),
    inference(backward_demodulation,[],[f167,f3090])).

fof(f3090,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl2_45
    | ~ spl2_46 ),
    inference(backward_demodulation,[],[f2791,f3079])).

fof(f3079,plain,
    ( sK1 = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_46 ),
    inference(superposition,[],[f770,f2798])).

fof(f2798,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_46 ),
    inference(avatar_component_clause,[],[f2796])).

fof(f2796,plain,
    ( spl2_46
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_46])])).

fof(f770,plain,(
    ! [X6,X5] : k3_tarski(k2_tarski(X5,k7_subset_1(X5,X5,X6))) = X5 ),
    inference(backward_demodulation,[],[f208,f696])).

fof(f208,plain,(
    ! [X6,X5] : k3_tarski(k2_tarski(X5,k5_xboole_0(X5,k1_setfam_1(k2_tarski(X5,X6))))) = X5 ),
    inference(forward_demodulation,[],[f207,f92])).

fof(f92,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))))) = X0 ),
    inference(definition_unfolding,[],[f73,f69,f68,f87])).

fof(f73,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f207,plain,(
    ! [X6,X5] : k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(X5,X6)),k5_xboole_0(X5,k1_setfam_1(k2_tarski(X5,X6))))) = k3_tarski(k2_tarski(X5,k5_xboole_0(X5,k1_setfam_1(k2_tarski(X5,X6))))) ),
    inference(forward_demodulation,[],[f206,f67])).

fof(f206,plain,(
    ! [X6,X5] : k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(X5,X6)),k5_xboole_0(X5,k1_setfam_1(k2_tarski(X5,X6))))) = k3_tarski(k2_tarski(k5_xboole_0(X5,k1_setfam_1(k2_tarski(X5,X6))),X5)) ),
    inference(forward_demodulation,[],[f202,f67])).

fof(f202,plain,(
    ! [X6,X5] : k3_tarski(k2_tarski(k5_xboole_0(X5,k1_setfam_1(k2_tarski(X5,X6))),X5)) = k3_tarski(k2_tarski(k5_xboole_0(X5,k1_setfam_1(k2_tarski(X5,X6))),k1_setfam_1(k2_tarski(X5,X6)))) ),
    inference(superposition,[],[f91,f90])).

fof(f90,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))))) ),
    inference(definition_unfolding,[],[f70,f68,f87,f87])).

fof(f70,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f91,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0))))) ),
    inference(definition_unfolding,[],[f72,f69,f87,f69])).

fof(f72,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f2791,plain,
    ( k2_pre_topc(sK0,sK1) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_45 ),
    inference(avatar_component_clause,[],[f2789])).

fof(f2789,plain,
    ( spl2_45
  <=> k2_pre_topc(sK0,sK1) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_45])])).

fof(f167,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,sK1),sK0)
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f165])).

fof(f165,plain,
    ( spl2_7
  <=> v4_pre_topc(k2_pre_topc(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f2809,plain,
    ( spl2_48
    | ~ spl2_3
    | ~ spl2_15 ),
    inference(avatar_split_clause,[],[f929,f401,f110,f2806])).

fof(f401,plain,
    ( spl2_15
  <=> k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f929,plain,
    ( k1_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_15 ),
    inference(superposition,[],[f804,f403])).

fof(f403,plain,
    ( k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f401])).

fof(f2799,plain,
    ( spl2_46
    | ~ spl2_3
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f928,f134,f110,f2796])).

fof(f134,plain,
    ( spl2_6
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f928,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_6 ),
    inference(superposition,[],[f804,f136])).

fof(f136,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f134])).

fof(f2792,plain,
    ( spl2_45
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f244,f217,f110,f105,f2789])).

fof(f217,plain,
    ( spl2_8
  <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f244,plain,
    ( k2_pre_topc(sK0,sK1) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_8 ),
    inference(forward_demodulation,[],[f237,f221])).

fof(f221,plain,
    ( k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f107,f112,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

fof(f237,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_3
    | ~ spl2_8 ),
    inference(unit_resulting_resolution,[],[f112,f219,f98])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f86,f69])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f219,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f217])).

fof(f404,plain,
    ( spl2_15
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f223,f110,f105,f401])).

fof(f223,plain,
    ( k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f107,f112,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

fof(f220,plain,
    ( spl2_8
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f157,f110,f105,f217])).

fof(f157,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f107,f112,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(f168,plain,
    ( spl2_7
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f154,f110,f105,f100,f165])).

fof(f100,plain,
    ( spl2_1
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f154,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,sK1),sK0)
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f102,f107,f112,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v4_pre_topc(k2_pre_topc(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_pre_topc(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tops_1)).

fof(f102,plain,
    ( v2_pre_topc(sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f100])).

fof(f137,plain,
    ( spl2_5
    | spl2_6 ),
    inference(avatar_split_clause,[],[f59,f134,f130])).

fof(f59,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f113,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f58,f110])).

fof(f58,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f54])).

fof(f108,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f57,f105])).

fof(f57,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f103,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f56,f100])).

fof(f56,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f54])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.12  % Command    : run_vampire %s %d
% 0.11/0.33  % Computer   : n021.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 17:15:34 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.19/0.41  % (15785)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.19/0.42  % (15779)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.19/0.43  % (15791)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.19/0.44  % (15788)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.19/0.45  % (15792)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.19/0.45  % (15784)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.19/0.46  % (15780)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.19/0.46  % (15793)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.19/0.46  % (15782)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.19/0.47  % (15794)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.19/0.47  % (15781)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.19/0.47  % (15786)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.19/0.47  % (15789)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.19/0.47  % (15795)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.19/0.48  % (15783)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.19/0.48  % (15797)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.19/0.48  % (15787)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.19/0.49  % (15796)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 2.29/0.65  % (15795)Refutation found. Thanks to Tanya!
% 2.29/0.65  % SZS status Theorem for theBenchmark
% 2.29/0.65  % SZS output start Proof for theBenchmark
% 2.29/0.65  fof(f3302,plain,(
% 2.29/0.65    $false),
% 2.29/0.65    inference(avatar_sat_refutation,[],[f103,f108,f113,f137,f168,f220,f404,f2792,f2799,f2809,f3101,f3136,f3189,f3289])).
% 2.29/0.65  fof(f3289,plain,(
% 2.29/0.65    ~spl2_3 | ~spl2_5 | ~spl2_48 | ~spl2_51 | ~spl2_52),
% 2.29/0.65    inference(avatar_contradiction_clause,[],[f3288])).
% 2.29/0.65  fof(f3288,plain,(
% 2.29/0.65    $false | (~spl2_3 | ~spl2_5 | ~spl2_48 | ~spl2_51 | ~spl2_52)),
% 2.29/0.65    inference(subsumption_resolution,[],[f3287,f132])).
% 2.29/0.65  fof(f132,plain,(
% 2.29/0.65    v4_pre_topc(sK1,sK0) | ~spl2_5),
% 2.29/0.65    inference(avatar_component_clause,[],[f130])).
% 2.29/0.65  fof(f130,plain,(
% 2.29/0.65    spl2_5 <=> v4_pre_topc(sK1,sK0)),
% 2.29/0.65    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 2.29/0.65  fof(f3287,plain,(
% 2.29/0.65    ~v4_pre_topc(sK1,sK0) | (~spl2_3 | ~spl2_48 | ~spl2_51 | ~spl2_52)),
% 2.29/0.65    inference(subsumption_resolution,[],[f3105,f3281])).
% 2.29/0.65  fof(f3281,plain,(
% 2.29/0.65    k2_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1)) | (~spl2_48 | ~spl2_51 | ~spl2_52)),
% 2.29/0.65    inference(forward_demodulation,[],[f3280,f3178])).
% 2.29/0.65  fof(f3178,plain,(
% 2.29/0.65    k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k1_tops_1(sK0,sK1)) | (~spl2_48 | ~spl2_51)),
% 2.29/0.65    inference(forward_demodulation,[],[f3153,f3174])).
% 2.29/0.65  fof(f3174,plain,(
% 2.29/0.65    k1_tops_1(sK0,sK1) = k3_subset_1(sK1,k2_tops_1(sK0,sK1)) | (~spl2_48 | ~spl2_51)),
% 2.29/0.65    inference(forward_demodulation,[],[f3157,f2808])).
% 2.29/0.65  fof(f2808,plain,(
% 2.29/0.65    k1_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k2_tops_1(sK0,sK1)) | ~spl2_48),
% 2.29/0.65    inference(avatar_component_clause,[],[f2806])).
% 2.29/0.65  fof(f2806,plain,(
% 2.29/0.65    spl2_48 <=> k1_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k2_tops_1(sK0,sK1))),
% 2.29/0.65    introduced(avatar_definition,[new_symbols(naming,[spl2_48])])).
% 2.29/0.65  fof(f3157,plain,(
% 2.29/0.65    k7_subset_1(sK1,sK1,k2_tops_1(sK0,sK1)) = k3_subset_1(sK1,k2_tops_1(sK0,sK1)) | ~spl2_51),
% 2.29/0.65    inference(unit_resulting_resolution,[],[f3135,f759])).
% 2.29/0.65  fof(f759,plain,(
% 2.29/0.65    ( ! [X0,X1] : (~r1_tarski(X1,X0) | k3_subset_1(X0,X1) = k7_subset_1(X0,X0,X1)) )),
% 2.29/0.65    inference(backward_demodulation,[],[f170,f696])).
% 2.29/0.65  fof(f696,plain,(
% 2.29/0.65    ( ! [X0,X1] : (k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k7_subset_1(X0,X0,X1)) )),
% 2.29/0.65    inference(unit_resulting_resolution,[],[f389,f95])).
% 2.29/0.65  fof(f95,plain,(
% 2.29/0.65    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))) )),
% 2.29/0.65    inference(definition_unfolding,[],[f82,f87])).
% 2.29/0.65  fof(f87,plain,(
% 2.29/0.65    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 2.29/0.65    inference(definition_unfolding,[],[f71,f68])).
% 2.29/0.65  fof(f68,plain,(
% 2.29/0.65    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.29/0.65    inference(cnf_transformation,[],[f18])).
% 2.29/0.65  fof(f18,axiom,(
% 2.29/0.65    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 2.29/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 2.29/0.65  fof(f71,plain,(
% 2.29/0.65    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.29/0.65    inference(cnf_transformation,[],[f1])).
% 2.29/0.65  fof(f1,axiom,(
% 2.29/0.65    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.29/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.29/0.65  fof(f82,plain,(
% 2.29/0.65    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.29/0.65    inference(cnf_transformation,[],[f43])).
% 2.29/0.65  fof(f43,plain,(
% 2.29/0.65    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.29/0.65    inference(ennf_transformation,[],[f17])).
% 2.29/0.65  fof(f17,axiom,(
% 2.29/0.65    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 2.29/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 2.29/0.65  fof(f389,plain,(
% 2.29/0.65    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 2.29/0.65    inference(unit_resulting_resolution,[],[f323,f81])).
% 2.29/0.65  fof(f81,plain,(
% 2.29/0.65    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.29/0.65    inference(cnf_transformation,[],[f55])).
% 2.29/0.65  fof(f55,plain,(
% 2.29/0.65    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.29/0.65    inference(nnf_transformation,[],[f19])).
% 2.29/0.65  fof(f19,axiom,(
% 2.29/0.65    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.29/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 2.29/0.65  fof(f323,plain,(
% 2.29/0.65    ( ! [X5] : (r1_tarski(X5,X5)) )),
% 2.29/0.65    inference(superposition,[],[f185,f114])).
% 2.29/0.65  fof(f114,plain,(
% 2.29/0.65    ( ! [X0] : (k3_tarski(k2_tarski(k1_xboole_0,X0)) = X0) )),
% 2.29/0.65    inference(superposition,[],[f88,f67])).
% 2.29/0.65  fof(f67,plain,(
% 2.29/0.65    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 2.29/0.65    inference(cnf_transformation,[],[f11])).
% 2.29/0.65  fof(f11,axiom,(
% 2.29/0.65    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 2.29/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 2.29/0.65  fof(f88,plain,(
% 2.29/0.65    ( ! [X0] : (k3_tarski(k2_tarski(X0,k1_xboole_0)) = X0) )),
% 2.29/0.65    inference(definition_unfolding,[],[f61,f69])).
% 2.29/0.65  fof(f69,plain,(
% 2.29/0.65    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.29/0.65    inference(cnf_transformation,[],[f12])).
% 2.29/0.65  fof(f12,axiom,(
% 2.29/0.65    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.29/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 2.29/0.65  fof(f61,plain,(
% 2.29/0.65    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.29/0.65    inference(cnf_transformation,[],[f2])).
% 2.29/0.65  fof(f2,axiom,(
% 2.29/0.65    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 2.29/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 2.29/0.65  fof(f185,plain,(
% 2.29/0.65    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k2_tarski(X1,X0)))) )),
% 2.29/0.65    inference(unit_resulting_resolution,[],[f89,f97])).
% 2.29/0.65  fof(f97,plain,(
% 2.29/0.65    ( ! [X2,X0,X1] : (~r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X2) | r1_tarski(X0,k3_tarski(k2_tarski(X1,X2)))) )),
% 2.29/0.65    inference(definition_unfolding,[],[f84,f69,f87])).
% 2.29/0.65  fof(f84,plain,(
% 2.29/0.65    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 2.29/0.65    inference(cnf_transformation,[],[f45])).
% 2.29/0.65  fof(f45,plain,(
% 2.29/0.65    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 2.29/0.65    inference(ennf_transformation,[],[f8])).
% 2.29/0.65  fof(f8,axiom,(
% 2.29/0.65    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 2.29/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).
% 2.29/0.65  fof(f89,plain,(
% 2.29/0.65    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0)) )),
% 2.29/0.65    inference(definition_unfolding,[],[f66,f87])).
% 2.29/0.65  fof(f66,plain,(
% 2.29/0.65    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 2.29/0.65    inference(cnf_transformation,[],[f4])).
% 2.29/0.65  fof(f4,axiom,(
% 2.29/0.65    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 2.29/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 2.29/0.65  fof(f170,plain,(
% 2.29/0.65    ( ! [X0,X1] : (k3_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) | ~r1_tarski(X1,X0)) )),
% 2.29/0.65    inference(resolution,[],[f93,f81])).
% 2.29/0.65  fof(f93,plain,(
% 2.29/0.65    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 2.29/0.65    inference(definition_unfolding,[],[f75,f87])).
% 2.29/0.65  fof(f75,plain,(
% 2.29/0.65    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.29/0.65    inference(cnf_transformation,[],[f36])).
% 2.29/0.65  fof(f36,plain,(
% 2.29/0.65    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.29/0.65    inference(ennf_transformation,[],[f13])).
% 2.29/0.65  fof(f13,axiom,(
% 2.29/0.65    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 2.29/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 2.29/0.65  fof(f3135,plain,(
% 2.29/0.65    r1_tarski(k2_tops_1(sK0,sK1),sK1) | ~spl2_51),
% 2.29/0.65    inference(avatar_component_clause,[],[f3133])).
% 2.29/0.65  fof(f3133,plain,(
% 2.29/0.65    spl2_51 <=> r1_tarski(k2_tops_1(sK0,sK1),sK1)),
% 2.29/0.65    introduced(avatar_definition,[new_symbols(naming,[spl2_51])])).
% 2.29/0.65  fof(f3153,plain,(
% 2.29/0.65    k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k3_subset_1(sK1,k2_tops_1(sK0,sK1))) | ~spl2_51),
% 2.29/0.65    inference(unit_resulting_resolution,[],[f3135,f148])).
% 2.29/0.65  fof(f148,plain,(
% 2.29/0.65    ( ! [X0,X1] : (~r1_tarski(X1,X0) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 2.29/0.65    inference(resolution,[],[f76,f81])).
% 2.29/0.65  fof(f76,plain,(
% 2.29/0.65    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 2.29/0.65    inference(cnf_transformation,[],[f37])).
% 2.29/0.65  fof(f37,plain,(
% 2.29/0.65    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.29/0.65    inference(ennf_transformation,[],[f15])).
% 2.29/0.65  fof(f15,axiom,(
% 2.29/0.65    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 2.29/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 2.29/0.65  fof(f3280,plain,(
% 2.29/0.65    k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1)) = k3_subset_1(sK1,k1_tops_1(sK0,sK1)) | (~spl2_48 | ~spl2_51 | ~spl2_52)),
% 2.29/0.65    inference(forward_demodulation,[],[f3234,f3174])).
% 2.29/0.65  fof(f3234,plain,(
% 2.29/0.65    k3_subset_1(sK1,k3_subset_1(sK1,k2_tops_1(sK0,sK1))) = k7_subset_1(sK1,sK1,k3_subset_1(sK1,k2_tops_1(sK0,sK1))) | ~spl2_52),
% 2.29/0.65    inference(resolution,[],[f3188,f785])).
% 2.29/0.65  fof(f785,plain,(
% 2.29/0.65    ( ! [X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(X2)) | k3_subset_1(X2,k3_subset_1(X2,X3)) = k7_subset_1(X2,X2,k3_subset_1(X2,X3))) )),
% 2.29/0.65    inference(backward_demodulation,[],[f171,f696])).
% 2.29/0.65  fof(f171,plain,(
% 2.29/0.65    ( ! [X2,X3] : (k3_subset_1(X2,k3_subset_1(X2,X3)) = k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,k3_subset_1(X2,X3)))) | ~m1_subset_1(X3,k1_zfmisc_1(X2))) )),
% 2.29/0.65    inference(resolution,[],[f93,f74])).
% 2.29/0.65  fof(f74,plain,(
% 2.29/0.65    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.29/0.65    inference(cnf_transformation,[],[f35])).
% 2.29/0.65  fof(f35,plain,(
% 2.29/0.65    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.29/0.65    inference(ennf_transformation,[],[f14])).
% 2.29/0.65  fof(f14,axiom,(
% 2.29/0.65    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 2.29/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 2.29/0.65  fof(f3188,plain,(
% 2.29/0.65    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | ~spl2_52),
% 2.29/0.65    inference(avatar_component_clause,[],[f3186])).
% 2.29/0.65  fof(f3186,plain,(
% 2.29/0.65    spl2_52 <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1))),
% 2.29/0.65    introduced(avatar_definition,[new_symbols(naming,[spl2_52])])).
% 2.29/0.65  fof(f3105,plain,(
% 2.29/0.65    k2_tops_1(sK0,sK1) != k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0) | ~spl2_3),
% 2.29/0.65    inference(forward_demodulation,[],[f60,f804])).
% 2.29/0.65  fof(f804,plain,(
% 2.29/0.65    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0)) ) | ~spl2_3),
% 2.29/0.65    inference(backward_demodulation,[],[f191,f696])).
% 2.29/0.65  fof(f191,plain,(
% 2.29/0.65    ( ! [X0] : (k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X0))) = k7_subset_1(u1_struct_0(sK0),sK1,X0)) ) | ~spl2_3),
% 2.29/0.65    inference(unit_resulting_resolution,[],[f112,f95])).
% 2.29/0.65  fof(f112,plain,(
% 2.29/0.65    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_3),
% 2.29/0.65    inference(avatar_component_clause,[],[f110])).
% 2.29/0.65  fof(f110,plain,(
% 2.29/0.65    spl2_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.29/0.65    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 2.29/0.65  fof(f60,plain,(
% 2.29/0.65    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)),
% 2.29/0.65    inference(cnf_transformation,[],[f54])).
% 2.29/0.65  fof(f54,plain,(
% 2.29/0.65    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 2.29/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f51,f53,f52])).
% 2.29/0.65  fof(f52,plain,(
% 2.29/0.65    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 2.29/0.65    introduced(choice_axiom,[])).
% 2.29/0.65  fof(f53,plain,(
% 2.29/0.65    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.29/0.65    introduced(choice_axiom,[])).
% 2.29/0.65  fof(f51,plain,(
% 2.29/0.65    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.29/0.65    inference(flattening,[],[f50])).
% 2.29/0.65  fof(f50,plain,(
% 2.29/0.65    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.29/0.65    inference(nnf_transformation,[],[f29])).
% 2.29/0.65  fof(f29,plain,(
% 2.29/0.65    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.29/0.65    inference(flattening,[],[f28])).
% 2.29/0.65  fof(f28,plain,(
% 2.29/0.65    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 2.29/0.65    inference(ennf_transformation,[],[f27])).
% 2.29/0.65  fof(f27,negated_conjecture,(
% 2.29/0.65    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 2.29/0.65    inference(negated_conjecture,[],[f26])).
% 2.29/0.65  fof(f26,conjecture,(
% 2.29/0.65    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 2.29/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).
% 2.29/0.65  fof(f3189,plain,(
% 2.29/0.65    spl2_52 | ~spl2_51),
% 2.29/0.65    inference(avatar_split_clause,[],[f3138,f3133,f3186])).
% 2.29/0.65  fof(f3138,plain,(
% 2.29/0.65    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | ~spl2_51),
% 2.29/0.65    inference(unit_resulting_resolution,[],[f3135,f81])).
% 2.29/0.65  fof(f3136,plain,(
% 2.29/0.65    spl2_51 | ~spl2_2 | ~spl2_3 | ~spl2_5),
% 2.29/0.65    inference(avatar_split_clause,[],[f3107,f130,f110,f105,f3133])).
% 2.29/0.65  fof(f105,plain,(
% 2.29/0.65    spl2_2 <=> l1_pre_topc(sK0)),
% 2.29/0.65    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 2.29/0.65  fof(f3107,plain,(
% 2.29/0.65    r1_tarski(k2_tops_1(sK0,sK1),sK1) | (~spl2_2 | ~spl2_3 | ~spl2_5)),
% 2.29/0.65    inference(unit_resulting_resolution,[],[f107,f112,f132,f65])).
% 2.29/0.65  fof(f65,plain,(
% 2.29/0.65    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k2_tops_1(X0,X1),X1)) )),
% 2.29/0.65    inference(cnf_transformation,[],[f34])).
% 2.29/0.65  fof(f34,plain,(
% 2.29/0.65    ! [X0] : (! [X1] : (r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.29/0.65    inference(flattening,[],[f33])).
% 2.29/0.65  fof(f33,plain,(
% 2.29/0.65    ! [X0] : (! [X1] : ((r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.29/0.65    inference(ennf_transformation,[],[f24])).
% 2.29/0.65  fof(f24,axiom,(
% 2.29/0.65    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => r1_tarski(k2_tops_1(X0,X1),X1))))),
% 2.29/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_tops_1)).
% 2.29/0.65  fof(f107,plain,(
% 2.29/0.65    l1_pre_topc(sK0) | ~spl2_2),
% 2.29/0.65    inference(avatar_component_clause,[],[f105])).
% 2.29/0.65  fof(f3101,plain,(
% 2.29/0.65    spl2_5 | ~spl2_7 | ~spl2_45 | ~spl2_46),
% 2.29/0.65    inference(avatar_contradiction_clause,[],[f3100])).
% 2.29/0.65  fof(f3100,plain,(
% 2.29/0.65    $false | (spl2_5 | ~spl2_7 | ~spl2_45 | ~spl2_46)),
% 2.29/0.65    inference(subsumption_resolution,[],[f3091,f131])).
% 2.29/0.67  fof(f131,plain,(
% 2.29/0.67    ~v4_pre_topc(sK1,sK0) | spl2_5),
% 2.29/0.67    inference(avatar_component_clause,[],[f130])).
% 2.29/0.67  fof(f3091,plain,(
% 2.29/0.67    v4_pre_topc(sK1,sK0) | (~spl2_7 | ~spl2_45 | ~spl2_46)),
% 2.29/0.67    inference(backward_demodulation,[],[f167,f3090])).
% 2.29/0.67  fof(f3090,plain,(
% 2.29/0.67    sK1 = k2_pre_topc(sK0,sK1) | (~spl2_45 | ~spl2_46)),
% 2.29/0.67    inference(backward_demodulation,[],[f2791,f3079])).
% 2.29/0.67  fof(f3079,plain,(
% 2.29/0.67    sK1 = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | ~spl2_46),
% 2.29/0.67    inference(superposition,[],[f770,f2798])).
% 2.29/0.67  fof(f2798,plain,(
% 2.29/0.67    k2_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1)) | ~spl2_46),
% 2.29/0.67    inference(avatar_component_clause,[],[f2796])).
% 2.29/0.67  fof(f2796,plain,(
% 2.29/0.67    spl2_46 <=> k2_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1))),
% 2.29/0.67    introduced(avatar_definition,[new_symbols(naming,[spl2_46])])).
% 2.29/0.67  fof(f770,plain,(
% 2.29/0.67    ( ! [X6,X5] : (k3_tarski(k2_tarski(X5,k7_subset_1(X5,X5,X6))) = X5) )),
% 2.29/0.67    inference(backward_demodulation,[],[f208,f696])).
% 2.29/0.67  fof(f208,plain,(
% 2.29/0.67    ( ! [X6,X5] : (k3_tarski(k2_tarski(X5,k5_xboole_0(X5,k1_setfam_1(k2_tarski(X5,X6))))) = X5) )),
% 2.29/0.67    inference(forward_demodulation,[],[f207,f92])).
% 2.29/0.67  fof(f92,plain,(
% 2.29/0.67    ( ! [X0,X1] : (k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))))) = X0) )),
% 2.29/0.67    inference(definition_unfolding,[],[f73,f69,f68,f87])).
% 2.29/0.67  fof(f73,plain,(
% 2.29/0.67    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 2.29/0.67    inference(cnf_transformation,[],[f10])).
% 2.29/0.67  fof(f10,axiom,(
% 2.29/0.67    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 2.29/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).
% 2.29/0.67  fof(f207,plain,(
% 2.29/0.67    ( ! [X6,X5] : (k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(X5,X6)),k5_xboole_0(X5,k1_setfam_1(k2_tarski(X5,X6))))) = k3_tarski(k2_tarski(X5,k5_xboole_0(X5,k1_setfam_1(k2_tarski(X5,X6)))))) )),
% 2.29/0.67    inference(forward_demodulation,[],[f206,f67])).
% 2.29/0.67  fof(f206,plain,(
% 2.29/0.67    ( ! [X6,X5] : (k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(X5,X6)),k5_xboole_0(X5,k1_setfam_1(k2_tarski(X5,X6))))) = k3_tarski(k2_tarski(k5_xboole_0(X5,k1_setfam_1(k2_tarski(X5,X6))),X5))) )),
% 2.29/0.67    inference(forward_demodulation,[],[f202,f67])).
% 2.29/0.67  fof(f202,plain,(
% 2.29/0.67    ( ! [X6,X5] : (k3_tarski(k2_tarski(k5_xboole_0(X5,k1_setfam_1(k2_tarski(X5,X6))),X5)) = k3_tarski(k2_tarski(k5_xboole_0(X5,k1_setfam_1(k2_tarski(X5,X6))),k1_setfam_1(k2_tarski(X5,X6))))) )),
% 2.29/0.67    inference(superposition,[],[f91,f90])).
% 2.29/0.67  fof(f90,plain,(
% 2.29/0.67    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))))))) )),
% 2.29/0.67    inference(definition_unfolding,[],[f70,f68,f87,f87])).
% 2.29/0.67  fof(f70,plain,(
% 2.29/0.67    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.29/0.67    inference(cnf_transformation,[],[f9])).
% 2.29/0.67  fof(f9,axiom,(
% 2.29/0.67    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.29/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.29/0.67  fof(f91,plain,(
% 2.29/0.67    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))))) )),
% 2.29/0.67    inference(definition_unfolding,[],[f72,f69,f87,f69])).
% 2.29/0.67  fof(f72,plain,(
% 2.29/0.67    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 2.29/0.67    inference(cnf_transformation,[],[f6])).
% 2.29/0.67  fof(f6,axiom,(
% 2.29/0.67    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 2.29/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 2.29/0.67  fof(f2791,plain,(
% 2.29/0.67    k2_pre_topc(sK0,sK1) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | ~spl2_45),
% 2.29/0.67    inference(avatar_component_clause,[],[f2789])).
% 2.29/0.67  fof(f2789,plain,(
% 2.29/0.67    spl2_45 <=> k2_pre_topc(sK0,sK1) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))),
% 2.29/0.67    introduced(avatar_definition,[new_symbols(naming,[spl2_45])])).
% 2.29/0.67  fof(f167,plain,(
% 2.29/0.67    v4_pre_topc(k2_pre_topc(sK0,sK1),sK0) | ~spl2_7),
% 2.29/0.67    inference(avatar_component_clause,[],[f165])).
% 2.29/0.67  fof(f165,plain,(
% 2.29/0.67    spl2_7 <=> v4_pre_topc(k2_pre_topc(sK0,sK1),sK0)),
% 2.29/0.67    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 2.29/0.67  fof(f2809,plain,(
% 2.29/0.67    spl2_48 | ~spl2_3 | ~spl2_15),
% 2.29/0.67    inference(avatar_split_clause,[],[f929,f401,f110,f2806])).
% 2.29/0.67  fof(f401,plain,(
% 2.29/0.67    spl2_15 <=> k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 2.29/0.67    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 2.29/0.67  fof(f929,plain,(
% 2.29/0.67    k1_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k2_tops_1(sK0,sK1)) | (~spl2_3 | ~spl2_15)),
% 2.29/0.67    inference(superposition,[],[f804,f403])).
% 2.29/0.67  fof(f403,plain,(
% 2.29/0.67    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | ~spl2_15),
% 2.29/0.67    inference(avatar_component_clause,[],[f401])).
% 2.29/0.67  fof(f2799,plain,(
% 2.29/0.67    spl2_46 | ~spl2_3 | ~spl2_6),
% 2.29/0.67    inference(avatar_split_clause,[],[f928,f134,f110,f2796])).
% 2.29/0.67  fof(f134,plain,(
% 2.29/0.67    spl2_6 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),
% 2.29/0.67    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 2.29/0.67  fof(f928,plain,(
% 2.29/0.67    k2_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1)) | (~spl2_3 | ~spl2_6)),
% 2.29/0.67    inference(superposition,[],[f804,f136])).
% 2.29/0.67  fof(f136,plain,(
% 2.29/0.67    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~spl2_6),
% 2.29/0.67    inference(avatar_component_clause,[],[f134])).
% 2.29/0.67  fof(f2792,plain,(
% 2.29/0.67    spl2_45 | ~spl2_2 | ~spl2_3 | ~spl2_8),
% 2.29/0.67    inference(avatar_split_clause,[],[f244,f217,f110,f105,f2789])).
% 2.29/0.67  fof(f217,plain,(
% 2.29/0.67    spl2_8 <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.29/0.67    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 2.29/0.67  fof(f244,plain,(
% 2.29/0.67    k2_pre_topc(sK0,sK1) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | (~spl2_2 | ~spl2_3 | ~spl2_8)),
% 2.29/0.67    inference(forward_demodulation,[],[f237,f221])).
% 2.29/0.67  fof(f221,plain,(
% 2.29/0.67    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | (~spl2_2 | ~spl2_3)),
% 2.29/0.67    inference(unit_resulting_resolution,[],[f107,f112,f63])).
% 2.29/0.67  fof(f63,plain,(
% 2.29/0.67    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))) )),
% 2.29/0.67    inference(cnf_transformation,[],[f31])).
% 2.29/0.67  fof(f31,plain,(
% 2.29/0.67    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.29/0.67    inference(ennf_transformation,[],[f23])).
% 2.29/0.67  fof(f23,axiom,(
% 2.29/0.67    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 2.29/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).
% 2.29/0.67  fof(f237,plain,(
% 2.29/0.67    k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | (~spl2_3 | ~spl2_8)),
% 2.29/0.67    inference(unit_resulting_resolution,[],[f112,f219,f98])).
% 2.29/0.67  fof(f98,plain,(
% 2.29/0.67    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.29/0.67    inference(definition_unfolding,[],[f86,f69])).
% 2.29/0.67  fof(f86,plain,(
% 2.29/0.67    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.29/0.67    inference(cnf_transformation,[],[f49])).
% 2.29/0.67  fof(f49,plain,(
% 2.29/0.67    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.29/0.67    inference(flattening,[],[f48])).
% 2.29/0.67  fof(f48,plain,(
% 2.29/0.67    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 2.29/0.67    inference(ennf_transformation,[],[f16])).
% 2.29/0.67  fof(f16,axiom,(
% 2.29/0.67    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 2.29/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 2.29/0.67  fof(f219,plain,(
% 2.29/0.67    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_8),
% 2.29/0.67    inference(avatar_component_clause,[],[f217])).
% 2.29/0.67  fof(f404,plain,(
% 2.29/0.67    spl2_15 | ~spl2_2 | ~spl2_3),
% 2.29/0.67    inference(avatar_split_clause,[],[f223,f110,f105,f401])).
% 2.29/0.67  fof(f223,plain,(
% 2.29/0.67    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | (~spl2_2 | ~spl2_3)),
% 2.29/0.67    inference(unit_resulting_resolution,[],[f107,f112,f64])).
% 2.29/0.67  fof(f64,plain,(
% 2.29/0.67    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))) )),
% 2.29/0.67    inference(cnf_transformation,[],[f32])).
% 2.29/0.67  fof(f32,plain,(
% 2.29/0.67    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.29/0.67    inference(ennf_transformation,[],[f25])).
% 2.29/0.67  fof(f25,axiom,(
% 2.29/0.67    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 2.29/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).
% 2.29/0.67  fof(f220,plain,(
% 2.29/0.67    spl2_8 | ~spl2_2 | ~spl2_3),
% 2.29/0.67    inference(avatar_split_clause,[],[f157,f110,f105,f217])).
% 2.29/0.67  fof(f157,plain,(
% 2.29/0.67    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_2 | ~spl2_3)),
% 2.29/0.67    inference(unit_resulting_resolution,[],[f107,f112,f79])).
% 2.29/0.67  fof(f79,plain,(
% 2.29/0.67    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.29/0.67    inference(cnf_transformation,[],[f42])).
% 2.29/0.67  fof(f42,plain,(
% 2.29/0.67    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 2.29/0.67    inference(flattening,[],[f41])).
% 2.29/0.67  fof(f41,plain,(
% 2.29/0.67    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 2.29/0.67    inference(ennf_transformation,[],[f20])).
% 2.29/0.67  fof(f20,axiom,(
% 2.29/0.67    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.29/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).
% 2.29/0.67  fof(f168,plain,(
% 2.29/0.67    spl2_7 | ~spl2_1 | ~spl2_2 | ~spl2_3),
% 2.29/0.67    inference(avatar_split_clause,[],[f154,f110,f105,f100,f165])).
% 2.29/0.67  fof(f100,plain,(
% 2.29/0.67    spl2_1 <=> v2_pre_topc(sK0)),
% 2.29/0.67    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 2.29/0.67  fof(f154,plain,(
% 2.29/0.67    v4_pre_topc(k2_pre_topc(sK0,sK1),sK0) | (~spl2_1 | ~spl2_2 | ~spl2_3)),
% 2.29/0.67    inference(unit_resulting_resolution,[],[f102,f107,f112,f78])).
% 2.29/0.67  fof(f78,plain,(
% 2.29/0.67    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v4_pre_topc(k2_pre_topc(X0,X1),X0)) )),
% 2.29/0.67    inference(cnf_transformation,[],[f40])).
% 2.29/0.67  fof(f40,plain,(
% 2.29/0.67    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.29/0.67    inference(flattening,[],[f39])).
% 2.29/0.67  fof(f39,plain,(
% 2.29/0.67    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.29/0.67    inference(ennf_transformation,[],[f21])).
% 2.29/0.67  fof(f21,axiom,(
% 2.29/0.67    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_pre_topc(X0,X1),X0))),
% 2.29/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tops_1)).
% 2.29/0.67  fof(f102,plain,(
% 2.29/0.67    v2_pre_topc(sK0) | ~spl2_1),
% 2.29/0.67    inference(avatar_component_clause,[],[f100])).
% 2.29/0.67  fof(f137,plain,(
% 2.29/0.67    spl2_5 | spl2_6),
% 2.29/0.67    inference(avatar_split_clause,[],[f59,f134,f130])).
% 2.29/0.67  fof(f59,plain,(
% 2.29/0.67    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)),
% 2.29/0.67    inference(cnf_transformation,[],[f54])).
% 2.29/0.67  fof(f113,plain,(
% 2.29/0.67    spl2_3),
% 2.29/0.67    inference(avatar_split_clause,[],[f58,f110])).
% 2.29/0.67  fof(f58,plain,(
% 2.29/0.67    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.29/0.67    inference(cnf_transformation,[],[f54])).
% 2.29/0.67  fof(f108,plain,(
% 2.29/0.67    spl2_2),
% 2.29/0.67    inference(avatar_split_clause,[],[f57,f105])).
% 2.29/0.67  fof(f57,plain,(
% 2.29/0.67    l1_pre_topc(sK0)),
% 2.29/0.67    inference(cnf_transformation,[],[f54])).
% 2.29/0.67  fof(f103,plain,(
% 2.29/0.67    spl2_1),
% 2.29/0.67    inference(avatar_split_clause,[],[f56,f100])).
% 2.29/0.67  fof(f56,plain,(
% 2.29/0.67    v2_pre_topc(sK0)),
% 2.29/0.67    inference(cnf_transformation,[],[f54])).
% 2.29/0.67  % SZS output end Proof for theBenchmark
% 2.29/0.67  % (15795)------------------------------
% 2.29/0.67  % (15795)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.29/0.67  % (15795)Termination reason: Refutation
% 2.29/0.67  
% 2.29/0.67  % (15795)Memory used [KB]: 13432
% 2.29/0.67  % (15795)Time elapsed: 0.212 s
% 2.29/0.67  % (15795)------------------------------
% 2.29/0.67  % (15795)------------------------------
% 2.29/0.67  % (15778)Success in time 0.332 s
%------------------------------------------------------------------------------
