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
% DateTime   : Thu Dec  3 13:11:52 EST 2020

% Result     : Theorem 5.74s
% Output     : Refutation 5.74s
% Verified   : 
% Statistics : Number of formulae       :  163 ( 844 expanded)
%              Number of leaves         :   34 ( 282 expanded)
%              Depth                    :   16
%              Number of atoms          :  424 (1609 expanded)
%              Number of equality atoms :   96 ( 602 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8379,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f117,f122,f127,f168,f208,f275,f531,f4149,f4212,f4222,f5479,f5486,f5501,f8341,f8376,f8378])).

fof(f8378,plain,
    ( ~ spl2_3
    | ~ spl2_5
    | ~ spl2_40
    | ~ spl2_49
    | ~ spl2_50 ),
    inference(avatar_contradiction_clause,[],[f8377])).

fof(f8377,plain,
    ( $false
    | ~ spl2_3
    | ~ spl2_5
    | ~ spl2_40
    | ~ spl2_49
    | ~ spl2_50 ),
    inference(subsumption_resolution,[],[f163,f8370])).

fof(f8370,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | ~ spl2_3
    | ~ spl2_40
    | ~ spl2_49
    | ~ spl2_50 ),
    inference(subsumption_resolution,[],[f5480,f6351])).

fof(f6351,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_40
    | ~ spl2_49
    | ~ spl2_50 ),
    inference(forward_demodulation,[],[f6331,f5846])).

fof(f5846,plain,
    ( k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_40
    | ~ spl2_49 ),
    inference(forward_demodulation,[],[f5807,f5838])).

fof(f5838,plain,
    ( k1_tops_1(sK0,sK1) = k3_subset_1(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_40
    | ~ spl2_49 ),
    inference(forward_demodulation,[],[f5815,f4221])).

fof(f4221,plain,
    ( k1_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_40 ),
    inference(avatar_component_clause,[],[f4219])).

fof(f4219,plain,
    ( spl2_40
  <=> k1_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_40])])).

fof(f5815,plain,
    ( k7_subset_1(sK1,sK1,k2_tops_1(sK0,sK1)) = k3_subset_1(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_49 ),
    inference(unit_resulting_resolution,[],[f5478,f1022])).

fof(f1022,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | k3_subset_1(X0,X1) = k7_subset_1(X0,X0,X1) ) ),
    inference(backward_demodulation,[],[f210,f962])).

fof(f962,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k7_subset_1(X0,X0,X1) ),
    inference(unit_resulting_resolution,[],[f551,f108])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) ) ),
    inference(definition_unfolding,[],[f93,f98])).

fof(f98,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f80,f78])).

fof(f78,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f80,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f551,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f439,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f439,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(superposition,[],[f235,f100])).

fof(f100,plain,(
    ! [X0] : k3_tarski(k2_tarski(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f74,f79])).

fof(f79,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f74,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f235,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k2_tarski(X1,X0))) ),
    inference(unit_resulting_resolution,[],[f102,f110])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X2)
      | r1_tarski(X0,k3_tarski(k2_tarski(X1,X2))) ) ),
    inference(definition_unfolding,[],[f95,f79,f98])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f102,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0) ),
    inference(definition_unfolding,[],[f76,f98])).

fof(f76,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f210,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))
      | ~ r1_tarski(X1,X0) ) ),
    inference(resolution,[],[f105,f91])).

fof(f105,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ) ),
    inference(definition_unfolding,[],[f84,f98])).

fof(f84,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f5478,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_49 ),
    inference(avatar_component_clause,[],[f5476])).

fof(f5476,plain,
    ( spl2_49
  <=> r1_tarski(k2_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_49])])).

fof(f5807,plain,
    ( k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k3_subset_1(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_49 ),
    inference(unit_resulting_resolution,[],[f5478,f182])).

fof(f182,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(resolution,[],[f85,f91])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f6331,plain,
    ( k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1)) = k3_subset_1(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_50 ),
    inference(resolution,[],[f5500,f1022])).

fof(f5500,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl2_50 ),
    inference(avatar_component_clause,[],[f5498])).

fof(f5498,plain,
    ( spl2_50
  <=> r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_50])])).

fof(f5480,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1))
    | ~ v4_pre_topc(sK1,sK0)
    | ~ spl2_3 ),
    inference(forward_demodulation,[],[f67,f1070])).

fof(f1070,plain,
    ( ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0)
    | ~ spl2_3 ),
    inference(backward_demodulation,[],[f256,f962])).

fof(f256,plain,
    ( ! [X0] : k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X0))) = k7_subset_1(u1_struct_0(sK0),sK1,X0)
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f126,f108])).

fof(f126,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl2_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f67,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,
    ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | ~ v4_pre_topc(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | v4_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f58,f60,f59])).

fof(f59,plain,
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

fof(f60,plain,
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

fof(f58,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f57])).

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
    inference(ennf_transformation,[],[f31])).

fof(f31,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f30])).

fof(f30,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).

fof(f163,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f161])).

fof(f161,plain,
    ( spl2_5
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f8376,plain,
    ( spl2_38
    | ~ spl2_40
    | ~ spl2_49
    | ~ spl2_50 ),
    inference(avatar_contradiction_clause,[],[f8375])).

fof(f8375,plain,
    ( $false
    | spl2_38
    | ~ spl2_40
    | ~ spl2_49
    | ~ spl2_50 ),
    inference(subsumption_resolution,[],[f4210,f6351])).

fof(f4210,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1))
    | spl2_38 ),
    inference(avatar_component_clause,[],[f4209])).

fof(f4209,plain,
    ( spl2_38
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_38])])).

fof(f8341,plain,
    ( spl2_5
    | ~ spl2_8
    | ~ spl2_35
    | ~ spl2_38 ),
    inference(avatar_contradiction_clause,[],[f8340])).

fof(f8340,plain,
    ( $false
    | spl2_5
    | ~ spl2_8
    | ~ spl2_35
    | ~ spl2_38 ),
    inference(subsumption_resolution,[],[f8272,f162])).

fof(f162,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | spl2_5 ),
    inference(avatar_component_clause,[],[f161])).

fof(f8272,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ spl2_8
    | ~ spl2_35
    | ~ spl2_38 ),
    inference(backward_demodulation,[],[f207,f8271])).

fof(f8271,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl2_35
    | ~ spl2_38 ),
    inference(backward_demodulation,[],[f4148,f8237])).

fof(f8237,plain,
    ( sK1 = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_38 ),
    inference(superposition,[],[f2483,f4211])).

fof(f4211,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_38 ),
    inference(avatar_component_clause,[],[f4209])).

fof(f2483,plain,(
    ! [X2,X3] : k3_tarski(k2_tarski(X2,k7_subset_1(X2,X2,X3))) = X2 ),
    inference(forward_demodulation,[],[f2463,f1012])).

fof(f1012,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),k7_subset_1(X0,X0,X1))) = X0 ),
    inference(backward_demodulation,[],[f103,f962])).

fof(f103,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))))) = X0 ),
    inference(definition_unfolding,[],[f81,f79,f78,f98])).

fof(f81,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f2463,plain,(
    ! [X2,X3] : k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(X2,X3)),k7_subset_1(X2,X2,X3))) = k3_tarski(k2_tarski(X2,k7_subset_1(X2,X2,X3))) ),
    inference(superposition,[],[f1027,f100])).

fof(f1027,plain,(
    ! [X12,X10,X11] : k3_tarski(k2_tarski(X10,X12)) = k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(X10,X11)),k3_tarski(k2_tarski(k7_subset_1(X10,X10,X11),X12)))) ),
    inference(backward_demodulation,[],[f246,f962])).

fof(f246,plain,(
    ! [X12,X10,X11] : k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(X10,X11)),k3_tarski(k2_tarski(k5_xboole_0(X10,k1_setfam_1(k2_tarski(X10,X11))),X12)))) = k3_tarski(k2_tarski(X10,X12)) ),
    inference(superposition,[],[f107,f103])).

fof(f107,plain,(
    ! [X2,X0,X1] : k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X2)) = k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X1,X2)))) ),
    inference(definition_unfolding,[],[f92,f79,f79,f79,f79])).

fof(f92,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f4148,plain,
    ( k2_pre_topc(sK0,sK1) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_35 ),
    inference(avatar_component_clause,[],[f4146])).

fof(f4146,plain,
    ( spl2_35
  <=> k2_pre_topc(sK0,sK1) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_35])])).

fof(f207,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,sK1),sK0)
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f205])).

fof(f205,plain,
    ( spl2_8
  <=> v4_pre_topc(k2_pre_topc(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f5501,plain,
    ( spl2_50
    | ~ spl2_40 ),
    inference(avatar_split_clause,[],[f4853,f4219,f5498])).

fof(f4853,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl2_40 ),
    inference(superposition,[],[f1011,f4221])).

fof(f1011,plain,(
    ! [X0,X1] : r1_tarski(k7_subset_1(X0,X0,X1),X0) ),
    inference(backward_demodulation,[],[f102,f962])).

fof(f5486,plain,
    ( ~ spl2_2
    | ~ spl2_3
    | ~ spl2_5
    | spl2_49 ),
    inference(avatar_contradiction_clause,[],[f5485])).

fof(f5485,plain,
    ( $false
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_5
    | spl2_49 ),
    inference(subsumption_resolution,[],[f5481,f5477])).

fof(f5477,plain,
    ( ~ r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | spl2_49 ),
    inference(avatar_component_clause,[],[f5476])).

fof(f5481,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(unit_resulting_resolution,[],[f126,f163,f239])).

fof(f239,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v4_pre_topc(X0,sK0)
        | r1_tarski(k2_tops_1(sK0,X0),X0) )
    | ~ spl2_2 ),
    inference(resolution,[],[f73,f121])).

fof(f121,plain,
    ( l1_pre_topc(sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f119])).

fof(f119,plain,
    ( spl2_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k2_tops_1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => r1_tarski(k2_tops_1(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_tops_1)).

fof(f5479,plain,
    ( spl2_49
    | ~ spl2_38 ),
    inference(avatar_split_clause,[],[f4832,f4209,f5476])).

fof(f4832,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_38 ),
    inference(superposition,[],[f1011,f4211])).

fof(f4222,plain,
    ( spl2_40
    | ~ spl2_3
    | ~ spl2_18 ),
    inference(avatar_split_clause,[],[f1223,f528,f124,f4219])).

fof(f528,plain,
    ( spl2_18
  <=> k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f1223,plain,
    ( k1_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_18 ),
    inference(superposition,[],[f1070,f530])).

fof(f530,plain,
    ( k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_18 ),
    inference(avatar_component_clause,[],[f528])).

fof(f4212,plain,
    ( spl2_38
    | ~ spl2_3
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f1222,f165,f124,f4209])).

fof(f165,plain,
    ( spl2_6
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f1222,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_6 ),
    inference(superposition,[],[f1070,f167])).

fof(f167,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f165])).

fof(f4149,plain,
    ( spl2_35
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f307,f272,f124,f119,f4146])).

fof(f272,plain,
    ( spl2_9
  <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f307,plain,
    ( k2_pre_topc(sK0,sK1) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_9 ),
    inference(forward_demodulation,[],[f297,f276])).

fof(f276,plain,
    ( k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f121,f126,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

fof(f297,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_3
    | ~ spl2_9 ),
    inference(unit_resulting_resolution,[],[f126,f274,f111])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f97,f79])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
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

fof(f274,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f272])).

fof(f531,plain,
    ( spl2_18
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f278,f124,f119,f528])).

fof(f278,plain,
    ( k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f121,f126,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

fof(f275,plain,
    ( spl2_9
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f198,f124,f119,f272])).

fof(f198,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f121,f126,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
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

fof(f208,plain,
    ( spl2_8
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f195,f124,f119,f114,f205])).

fof(f114,plain,
    ( spl2_1
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f195,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,sK1),sK0)
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f116,f121,f126,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v4_pre_topc(k2_pre_topc(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_pre_topc(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tops_1)).

fof(f116,plain,
    ( v2_pre_topc(sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f114])).

fof(f168,plain,
    ( spl2_5
    | spl2_6 ),
    inference(avatar_split_clause,[],[f66,f165,f161])).

fof(f66,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f61])).

fof(f127,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f65,f124])).

fof(f65,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f61])).

fof(f122,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f64,f119])).

fof(f64,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f61])).

fof(f117,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f63,f114])).

fof(f63,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f61])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:07:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.42  % (28865)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.44  % (28870)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.46  % (28863)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.47  % (28862)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.47  % (28864)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.48  % (28855)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.48  % (28856)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.48  % (28858)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.49  % (28867)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.49  % (28854)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.49  % (28853)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.49  % (28859)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.49  % (28869)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.49  % (28868)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.50  % (28866)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.50  % (28860)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.50  % (28857)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.50  % (28861)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 5.20/1.01  % (28857)Time limit reached!
% 5.20/1.01  % (28857)------------------------------
% 5.20/1.01  % (28857)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.20/1.01  % (28857)Termination reason: Time limit
% 5.20/1.01  % (28857)Termination phase: Saturation
% 5.20/1.01  
% 5.20/1.01  % (28857)Memory used [KB]: 13048
% 5.20/1.01  % (28857)Time elapsed: 0.600 s
% 5.20/1.01  % (28857)------------------------------
% 5.20/1.01  % (28857)------------------------------
% 5.74/1.11  % (28868)Refutation found. Thanks to Tanya!
% 5.74/1.11  % SZS status Theorem for theBenchmark
% 5.74/1.11  % SZS output start Proof for theBenchmark
% 5.74/1.11  fof(f8379,plain,(
% 5.74/1.11    $false),
% 5.74/1.11    inference(avatar_sat_refutation,[],[f117,f122,f127,f168,f208,f275,f531,f4149,f4212,f4222,f5479,f5486,f5501,f8341,f8376,f8378])).
% 5.74/1.11  fof(f8378,plain,(
% 5.74/1.11    ~spl2_3 | ~spl2_5 | ~spl2_40 | ~spl2_49 | ~spl2_50),
% 5.74/1.11    inference(avatar_contradiction_clause,[],[f8377])).
% 5.74/1.11  fof(f8377,plain,(
% 5.74/1.11    $false | (~spl2_3 | ~spl2_5 | ~spl2_40 | ~spl2_49 | ~spl2_50)),
% 5.74/1.11    inference(subsumption_resolution,[],[f163,f8370])).
% 5.74/1.11  fof(f8370,plain,(
% 5.74/1.11    ~v4_pre_topc(sK1,sK0) | (~spl2_3 | ~spl2_40 | ~spl2_49 | ~spl2_50)),
% 5.74/1.11    inference(subsumption_resolution,[],[f5480,f6351])).
% 5.74/1.11  fof(f6351,plain,(
% 5.74/1.11    k2_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1)) | (~spl2_40 | ~spl2_49 | ~spl2_50)),
% 5.74/1.11    inference(forward_demodulation,[],[f6331,f5846])).
% 5.74/1.11  fof(f5846,plain,(
% 5.74/1.11    k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k1_tops_1(sK0,sK1)) | (~spl2_40 | ~spl2_49)),
% 5.74/1.11    inference(forward_demodulation,[],[f5807,f5838])).
% 5.74/1.11  fof(f5838,plain,(
% 5.74/1.11    k1_tops_1(sK0,sK1) = k3_subset_1(sK1,k2_tops_1(sK0,sK1)) | (~spl2_40 | ~spl2_49)),
% 5.74/1.11    inference(forward_demodulation,[],[f5815,f4221])).
% 5.74/1.11  fof(f4221,plain,(
% 5.74/1.11    k1_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k2_tops_1(sK0,sK1)) | ~spl2_40),
% 5.74/1.11    inference(avatar_component_clause,[],[f4219])).
% 5.74/1.11  fof(f4219,plain,(
% 5.74/1.11    spl2_40 <=> k1_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k2_tops_1(sK0,sK1))),
% 5.74/1.11    introduced(avatar_definition,[new_symbols(naming,[spl2_40])])).
% 5.74/1.11  fof(f5815,plain,(
% 5.74/1.11    k7_subset_1(sK1,sK1,k2_tops_1(sK0,sK1)) = k3_subset_1(sK1,k2_tops_1(sK0,sK1)) | ~spl2_49),
% 5.74/1.11    inference(unit_resulting_resolution,[],[f5478,f1022])).
% 5.74/1.11  fof(f1022,plain,(
% 5.74/1.11    ( ! [X0,X1] : (~r1_tarski(X1,X0) | k3_subset_1(X0,X1) = k7_subset_1(X0,X0,X1)) )),
% 5.74/1.11    inference(backward_demodulation,[],[f210,f962])).
% 5.74/1.11  fof(f962,plain,(
% 5.74/1.11    ( ! [X0,X1] : (k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k7_subset_1(X0,X0,X1)) )),
% 5.74/1.11    inference(unit_resulting_resolution,[],[f551,f108])).
% 5.74/1.11  fof(f108,plain,(
% 5.74/1.11    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))) )),
% 5.74/1.11    inference(definition_unfolding,[],[f93,f98])).
% 5.74/1.11  fof(f98,plain,(
% 5.74/1.11    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 5.74/1.11    inference(definition_unfolding,[],[f80,f78])).
% 5.74/1.11  fof(f78,plain,(
% 5.74/1.11    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 5.74/1.11    inference(cnf_transformation,[],[f22])).
% 5.74/1.11  fof(f22,axiom,(
% 5.74/1.11    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 5.74/1.11    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 5.74/1.11  fof(f80,plain,(
% 5.74/1.11    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 5.74/1.11    inference(cnf_transformation,[],[f2])).
% 5.74/1.11  fof(f2,axiom,(
% 5.74/1.11    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 5.74/1.11    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 5.74/1.11  fof(f93,plain,(
% 5.74/1.11    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 5.74/1.11    inference(cnf_transformation,[],[f50])).
% 5.74/1.11  fof(f50,plain,(
% 5.74/1.11    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 5.74/1.11    inference(ennf_transformation,[],[f20])).
% 5.74/1.11  fof(f20,axiom,(
% 5.74/1.11    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 5.74/1.11    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 5.74/1.11  fof(f551,plain,(
% 5.74/1.11    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 5.74/1.11    inference(unit_resulting_resolution,[],[f439,f91])).
% 5.74/1.11  fof(f91,plain,(
% 5.74/1.11    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 5.74/1.11    inference(cnf_transformation,[],[f62])).
% 5.74/1.11  fof(f62,plain,(
% 5.74/1.11    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 5.74/1.11    inference(nnf_transformation,[],[f23])).
% 5.74/1.11  fof(f23,axiom,(
% 5.74/1.11    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 5.74/1.11    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 5.74/1.11  fof(f439,plain,(
% 5.74/1.11    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 5.74/1.11    inference(superposition,[],[f235,f100])).
% 5.74/1.11  fof(f100,plain,(
% 5.74/1.11    ( ! [X0] : (k3_tarski(k2_tarski(X0,X0)) = X0) )),
% 5.74/1.11    inference(definition_unfolding,[],[f74,f79])).
% 5.74/1.11  fof(f79,plain,(
% 5.74/1.11    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 5.74/1.11    inference(cnf_transformation,[],[f14])).
% 5.74/1.11  fof(f14,axiom,(
% 5.74/1.11    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 5.74/1.11    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 5.74/1.11  fof(f74,plain,(
% 5.74/1.11    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 5.74/1.11    inference(cnf_transformation,[],[f32])).
% 5.74/1.11  fof(f32,plain,(
% 5.74/1.11    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 5.74/1.11    inference(rectify,[],[f1])).
% 5.74/1.11  fof(f1,axiom,(
% 5.74/1.11    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 5.74/1.11    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 5.74/1.11  fof(f235,plain,(
% 5.74/1.11    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k2_tarski(X1,X0)))) )),
% 5.74/1.11    inference(unit_resulting_resolution,[],[f102,f110])).
% 5.74/1.11  fof(f110,plain,(
% 5.74/1.11    ( ! [X2,X0,X1] : (~r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X2) | r1_tarski(X0,k3_tarski(k2_tarski(X1,X2)))) )),
% 5.74/1.11    inference(definition_unfolding,[],[f95,f79,f98])).
% 5.74/1.11  fof(f95,plain,(
% 5.74/1.11    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 5.74/1.11    inference(cnf_transformation,[],[f52])).
% 5.74/1.11  fof(f52,plain,(
% 5.74/1.11    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 5.74/1.11    inference(ennf_transformation,[],[f10])).
% 5.74/1.11  fof(f10,axiom,(
% 5.74/1.11    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 5.74/1.11    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).
% 5.74/1.11  fof(f102,plain,(
% 5.74/1.11    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0)) )),
% 5.74/1.11    inference(definition_unfolding,[],[f76,f98])).
% 5.74/1.11  fof(f76,plain,(
% 5.74/1.11    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 5.74/1.11    inference(cnf_transformation,[],[f7])).
% 5.74/1.11  fof(f7,axiom,(
% 5.74/1.11    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 5.74/1.11    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 5.74/1.11  fof(f210,plain,(
% 5.74/1.11    ( ! [X0,X1] : (k3_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) | ~r1_tarski(X1,X0)) )),
% 5.74/1.11    inference(resolution,[],[f105,f91])).
% 5.74/1.11  fof(f105,plain,(
% 5.74/1.11    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 5.74/1.11    inference(definition_unfolding,[],[f84,f98])).
% 5.74/1.11  fof(f84,plain,(
% 5.74/1.11    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 5.74/1.11    inference(cnf_transformation,[],[f42])).
% 5.74/1.11  fof(f42,plain,(
% 5.74/1.11    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 5.74/1.11    inference(ennf_transformation,[],[f16])).
% 5.74/1.11  fof(f16,axiom,(
% 5.74/1.11    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 5.74/1.11    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 5.74/1.11  fof(f5478,plain,(
% 5.74/1.11    r1_tarski(k2_tops_1(sK0,sK1),sK1) | ~spl2_49),
% 5.74/1.11    inference(avatar_component_clause,[],[f5476])).
% 5.74/1.11  fof(f5476,plain,(
% 5.74/1.11    spl2_49 <=> r1_tarski(k2_tops_1(sK0,sK1),sK1)),
% 5.74/1.11    introduced(avatar_definition,[new_symbols(naming,[spl2_49])])).
% 5.74/1.11  fof(f5807,plain,(
% 5.74/1.11    k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k3_subset_1(sK1,k2_tops_1(sK0,sK1))) | ~spl2_49),
% 5.74/1.11    inference(unit_resulting_resolution,[],[f5478,f182])).
% 5.74/1.11  fof(f182,plain,(
% 5.74/1.11    ( ! [X0,X1] : (~r1_tarski(X1,X0) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 5.74/1.11    inference(resolution,[],[f85,f91])).
% 5.74/1.11  fof(f85,plain,(
% 5.74/1.11    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 5.74/1.11    inference(cnf_transformation,[],[f43])).
% 5.74/1.11  fof(f43,plain,(
% 5.74/1.11    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 5.74/1.11    inference(ennf_transformation,[],[f18])).
% 5.74/1.11  fof(f18,axiom,(
% 5.74/1.11    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 5.74/1.11    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 5.74/1.11  fof(f6331,plain,(
% 5.74/1.11    k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1)) = k3_subset_1(sK1,k1_tops_1(sK0,sK1)) | ~spl2_50),
% 5.74/1.11    inference(resolution,[],[f5500,f1022])).
% 5.74/1.11  fof(f5500,plain,(
% 5.74/1.11    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~spl2_50),
% 5.74/1.11    inference(avatar_component_clause,[],[f5498])).
% 5.74/1.11  fof(f5498,plain,(
% 5.74/1.11    spl2_50 <=> r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 5.74/1.11    introduced(avatar_definition,[new_symbols(naming,[spl2_50])])).
% 5.74/1.11  fof(f5480,plain,(
% 5.74/1.11    k2_tops_1(sK0,sK1) != k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0) | ~spl2_3),
% 5.74/1.11    inference(forward_demodulation,[],[f67,f1070])).
% 5.74/1.11  fof(f1070,plain,(
% 5.74/1.11    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0)) ) | ~spl2_3),
% 5.74/1.11    inference(backward_demodulation,[],[f256,f962])).
% 5.74/1.11  fof(f256,plain,(
% 5.74/1.11    ( ! [X0] : (k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X0))) = k7_subset_1(u1_struct_0(sK0),sK1,X0)) ) | ~spl2_3),
% 5.74/1.11    inference(unit_resulting_resolution,[],[f126,f108])).
% 5.74/1.11  fof(f126,plain,(
% 5.74/1.11    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_3),
% 5.74/1.11    inference(avatar_component_clause,[],[f124])).
% 5.74/1.11  fof(f124,plain,(
% 5.74/1.11    spl2_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 5.74/1.11    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 5.74/1.11  fof(f67,plain,(
% 5.74/1.11    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)),
% 5.74/1.11    inference(cnf_transformation,[],[f61])).
% 5.74/1.11  fof(f61,plain,(
% 5.74/1.11    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 5.74/1.11    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f58,f60,f59])).
% 5.74/1.11  fof(f59,plain,(
% 5.74/1.11    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 5.74/1.11    introduced(choice_axiom,[])).
% 5.74/1.11  fof(f60,plain,(
% 5.74/1.11    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 5.74/1.11    introduced(choice_axiom,[])).
% 5.74/1.11  fof(f58,plain,(
% 5.74/1.11    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 5.74/1.11    inference(flattening,[],[f57])).
% 5.74/1.11  fof(f57,plain,(
% 5.74/1.11    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 5.74/1.11    inference(nnf_transformation,[],[f34])).
% 5.74/1.11  fof(f34,plain,(
% 5.74/1.11    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 5.74/1.11    inference(flattening,[],[f33])).
% 5.74/1.11  fof(f33,plain,(
% 5.74/1.11    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 5.74/1.11    inference(ennf_transformation,[],[f31])).
% 5.74/1.11  fof(f31,negated_conjecture,(
% 5.74/1.11    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 5.74/1.11    inference(negated_conjecture,[],[f30])).
% 5.74/1.11  fof(f30,conjecture,(
% 5.74/1.11    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 5.74/1.11    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).
% 5.74/1.11  fof(f163,plain,(
% 5.74/1.11    v4_pre_topc(sK1,sK0) | ~spl2_5),
% 5.74/1.11    inference(avatar_component_clause,[],[f161])).
% 5.74/1.11  fof(f161,plain,(
% 5.74/1.11    spl2_5 <=> v4_pre_topc(sK1,sK0)),
% 5.74/1.11    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 5.74/1.11  fof(f8376,plain,(
% 5.74/1.11    spl2_38 | ~spl2_40 | ~spl2_49 | ~spl2_50),
% 5.74/1.11    inference(avatar_contradiction_clause,[],[f8375])).
% 5.74/1.11  fof(f8375,plain,(
% 5.74/1.11    $false | (spl2_38 | ~spl2_40 | ~spl2_49 | ~spl2_50)),
% 5.74/1.11    inference(subsumption_resolution,[],[f4210,f6351])).
% 5.74/1.11  fof(f4210,plain,(
% 5.74/1.11    k2_tops_1(sK0,sK1) != k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1)) | spl2_38),
% 5.74/1.11    inference(avatar_component_clause,[],[f4209])).
% 5.74/1.11  fof(f4209,plain,(
% 5.74/1.11    spl2_38 <=> k2_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1))),
% 5.74/1.11    introduced(avatar_definition,[new_symbols(naming,[spl2_38])])).
% 5.74/1.11  fof(f8341,plain,(
% 5.74/1.11    spl2_5 | ~spl2_8 | ~spl2_35 | ~spl2_38),
% 5.74/1.11    inference(avatar_contradiction_clause,[],[f8340])).
% 5.74/1.11  fof(f8340,plain,(
% 5.74/1.11    $false | (spl2_5 | ~spl2_8 | ~spl2_35 | ~spl2_38)),
% 5.74/1.11    inference(subsumption_resolution,[],[f8272,f162])).
% 5.74/1.11  fof(f162,plain,(
% 5.74/1.11    ~v4_pre_topc(sK1,sK0) | spl2_5),
% 5.74/1.11    inference(avatar_component_clause,[],[f161])).
% 5.74/1.11  fof(f8272,plain,(
% 5.74/1.11    v4_pre_topc(sK1,sK0) | (~spl2_8 | ~spl2_35 | ~spl2_38)),
% 5.74/1.11    inference(backward_demodulation,[],[f207,f8271])).
% 5.74/1.11  fof(f8271,plain,(
% 5.74/1.11    sK1 = k2_pre_topc(sK0,sK1) | (~spl2_35 | ~spl2_38)),
% 5.74/1.11    inference(backward_demodulation,[],[f4148,f8237])).
% 5.74/1.11  fof(f8237,plain,(
% 5.74/1.11    sK1 = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | ~spl2_38),
% 5.74/1.11    inference(superposition,[],[f2483,f4211])).
% 5.74/1.11  fof(f4211,plain,(
% 5.74/1.11    k2_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1)) | ~spl2_38),
% 5.74/1.11    inference(avatar_component_clause,[],[f4209])).
% 5.74/1.11  fof(f2483,plain,(
% 5.74/1.11    ( ! [X2,X3] : (k3_tarski(k2_tarski(X2,k7_subset_1(X2,X2,X3))) = X2) )),
% 5.74/1.11    inference(forward_demodulation,[],[f2463,f1012])).
% 5.74/1.11  fof(f1012,plain,(
% 5.74/1.11    ( ! [X0,X1] : (k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),k7_subset_1(X0,X0,X1))) = X0) )),
% 5.74/1.11    inference(backward_demodulation,[],[f103,f962])).
% 5.74/1.11  fof(f103,plain,(
% 5.74/1.11    ( ! [X0,X1] : (k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))))) = X0) )),
% 5.74/1.11    inference(definition_unfolding,[],[f81,f79,f78,f98])).
% 5.74/1.11  fof(f81,plain,(
% 5.74/1.11    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 5.74/1.11    inference(cnf_transformation,[],[f12])).
% 5.74/1.11  fof(f12,axiom,(
% 5.74/1.11    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 5.74/1.11    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).
% 5.74/1.11  fof(f2463,plain,(
% 5.74/1.11    ( ! [X2,X3] : (k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(X2,X3)),k7_subset_1(X2,X2,X3))) = k3_tarski(k2_tarski(X2,k7_subset_1(X2,X2,X3)))) )),
% 5.74/1.11    inference(superposition,[],[f1027,f100])).
% 5.74/1.11  fof(f1027,plain,(
% 5.74/1.11    ( ! [X12,X10,X11] : (k3_tarski(k2_tarski(X10,X12)) = k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(X10,X11)),k3_tarski(k2_tarski(k7_subset_1(X10,X10,X11),X12))))) )),
% 5.74/1.11    inference(backward_demodulation,[],[f246,f962])).
% 5.74/1.11  fof(f246,plain,(
% 5.74/1.11    ( ! [X12,X10,X11] : (k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(X10,X11)),k3_tarski(k2_tarski(k5_xboole_0(X10,k1_setfam_1(k2_tarski(X10,X11))),X12)))) = k3_tarski(k2_tarski(X10,X12))) )),
% 5.74/1.11    inference(superposition,[],[f107,f103])).
% 5.74/1.11  fof(f107,plain,(
% 5.74/1.11    ( ! [X2,X0,X1] : (k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X2)) = k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X1,X2))))) )),
% 5.74/1.11    inference(definition_unfolding,[],[f92,f79,f79,f79,f79])).
% 5.74/1.11  fof(f92,plain,(
% 5.74/1.11    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 5.74/1.11    inference(cnf_transformation,[],[f11])).
% 5.74/1.11  fof(f11,axiom,(
% 5.74/1.11    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 5.74/1.11    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).
% 5.74/1.11  fof(f4148,plain,(
% 5.74/1.11    k2_pre_topc(sK0,sK1) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | ~spl2_35),
% 5.74/1.11    inference(avatar_component_clause,[],[f4146])).
% 5.74/1.11  fof(f4146,plain,(
% 5.74/1.11    spl2_35 <=> k2_pre_topc(sK0,sK1) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))),
% 5.74/1.11    introduced(avatar_definition,[new_symbols(naming,[spl2_35])])).
% 5.74/1.11  fof(f207,plain,(
% 5.74/1.11    v4_pre_topc(k2_pre_topc(sK0,sK1),sK0) | ~spl2_8),
% 5.74/1.11    inference(avatar_component_clause,[],[f205])).
% 5.74/1.11  fof(f205,plain,(
% 5.74/1.11    spl2_8 <=> v4_pre_topc(k2_pre_topc(sK0,sK1),sK0)),
% 5.74/1.11    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 5.74/1.11  fof(f5501,plain,(
% 5.74/1.11    spl2_50 | ~spl2_40),
% 5.74/1.11    inference(avatar_split_clause,[],[f4853,f4219,f5498])).
% 5.74/1.11  fof(f4853,plain,(
% 5.74/1.11    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~spl2_40),
% 5.74/1.11    inference(superposition,[],[f1011,f4221])).
% 5.74/1.11  fof(f1011,plain,(
% 5.74/1.11    ( ! [X0,X1] : (r1_tarski(k7_subset_1(X0,X0,X1),X0)) )),
% 5.74/1.11    inference(backward_demodulation,[],[f102,f962])).
% 5.74/1.11  fof(f5486,plain,(
% 5.74/1.11    ~spl2_2 | ~spl2_3 | ~spl2_5 | spl2_49),
% 5.74/1.11    inference(avatar_contradiction_clause,[],[f5485])).
% 5.74/1.11  fof(f5485,plain,(
% 5.74/1.11    $false | (~spl2_2 | ~spl2_3 | ~spl2_5 | spl2_49)),
% 5.74/1.11    inference(subsumption_resolution,[],[f5481,f5477])).
% 5.74/1.11  fof(f5477,plain,(
% 5.74/1.11    ~r1_tarski(k2_tops_1(sK0,sK1),sK1) | spl2_49),
% 5.74/1.11    inference(avatar_component_clause,[],[f5476])).
% 5.74/1.11  fof(f5481,plain,(
% 5.74/1.11    r1_tarski(k2_tops_1(sK0,sK1),sK1) | (~spl2_2 | ~spl2_3 | ~spl2_5)),
% 5.74/1.11    inference(unit_resulting_resolution,[],[f126,f163,f239])).
% 5.74/1.11  fof(f239,plain,(
% 5.74/1.11    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(X0,sK0) | r1_tarski(k2_tops_1(sK0,X0),X0)) ) | ~spl2_2),
% 5.74/1.11    inference(resolution,[],[f73,f121])).
% 5.74/1.11  fof(f121,plain,(
% 5.74/1.11    l1_pre_topc(sK0) | ~spl2_2),
% 5.74/1.11    inference(avatar_component_clause,[],[f119])).
% 5.74/1.11  fof(f119,plain,(
% 5.74/1.11    spl2_2 <=> l1_pre_topc(sK0)),
% 5.74/1.11    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 5.74/1.11  fof(f73,plain,(
% 5.74/1.11    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k2_tops_1(X0,X1),X1)) )),
% 5.74/1.11    inference(cnf_transformation,[],[f39])).
% 5.74/1.11  fof(f39,plain,(
% 5.74/1.11    ! [X0] : (! [X1] : (r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 5.74/1.11    inference(flattening,[],[f38])).
% 5.74/1.11  fof(f38,plain,(
% 5.74/1.11    ! [X0] : (! [X1] : ((r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 5.74/1.11    inference(ennf_transformation,[],[f28])).
% 5.74/1.11  fof(f28,axiom,(
% 5.74/1.11    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => r1_tarski(k2_tops_1(X0,X1),X1))))),
% 5.74/1.11    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_tops_1)).
% 5.74/1.11  fof(f5479,plain,(
% 5.74/1.11    spl2_49 | ~spl2_38),
% 5.74/1.11    inference(avatar_split_clause,[],[f4832,f4209,f5476])).
% 5.74/1.11  fof(f4832,plain,(
% 5.74/1.11    r1_tarski(k2_tops_1(sK0,sK1),sK1) | ~spl2_38),
% 5.74/1.11    inference(superposition,[],[f1011,f4211])).
% 5.74/1.11  fof(f4222,plain,(
% 5.74/1.11    spl2_40 | ~spl2_3 | ~spl2_18),
% 5.74/1.11    inference(avatar_split_clause,[],[f1223,f528,f124,f4219])).
% 5.74/1.11  fof(f528,plain,(
% 5.74/1.11    spl2_18 <=> k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 5.74/1.11    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 5.74/1.11  fof(f1223,plain,(
% 5.74/1.11    k1_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k2_tops_1(sK0,sK1)) | (~spl2_3 | ~spl2_18)),
% 5.74/1.11    inference(superposition,[],[f1070,f530])).
% 5.74/1.11  fof(f530,plain,(
% 5.74/1.11    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | ~spl2_18),
% 5.74/1.11    inference(avatar_component_clause,[],[f528])).
% 5.74/1.11  fof(f4212,plain,(
% 5.74/1.11    spl2_38 | ~spl2_3 | ~spl2_6),
% 5.74/1.11    inference(avatar_split_clause,[],[f1222,f165,f124,f4209])).
% 5.74/1.11  fof(f165,plain,(
% 5.74/1.11    spl2_6 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),
% 5.74/1.11    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 5.74/1.11  fof(f1222,plain,(
% 5.74/1.11    k2_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1)) | (~spl2_3 | ~spl2_6)),
% 5.74/1.11    inference(superposition,[],[f1070,f167])).
% 5.74/1.11  fof(f167,plain,(
% 5.74/1.11    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~spl2_6),
% 5.74/1.11    inference(avatar_component_clause,[],[f165])).
% 5.74/1.11  fof(f4149,plain,(
% 5.74/1.11    spl2_35 | ~spl2_2 | ~spl2_3 | ~spl2_9),
% 5.74/1.11    inference(avatar_split_clause,[],[f307,f272,f124,f119,f4146])).
% 5.74/1.11  fof(f272,plain,(
% 5.74/1.11    spl2_9 <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 5.74/1.11    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 5.74/1.11  fof(f307,plain,(
% 5.74/1.11    k2_pre_topc(sK0,sK1) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | (~spl2_2 | ~spl2_3 | ~spl2_9)),
% 5.74/1.11    inference(forward_demodulation,[],[f297,f276])).
% 5.74/1.11  fof(f276,plain,(
% 5.74/1.11    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | (~spl2_2 | ~spl2_3)),
% 5.74/1.11    inference(unit_resulting_resolution,[],[f121,f126,f71])).
% 5.74/1.11  fof(f71,plain,(
% 5.74/1.11    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))) )),
% 5.74/1.11    inference(cnf_transformation,[],[f36])).
% 5.74/1.11  fof(f36,plain,(
% 5.74/1.11    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 5.74/1.11    inference(ennf_transformation,[],[f27])).
% 5.74/1.11  fof(f27,axiom,(
% 5.74/1.11    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 5.74/1.11    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).
% 5.74/1.11  fof(f297,plain,(
% 5.74/1.11    k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | (~spl2_3 | ~spl2_9)),
% 5.74/1.11    inference(unit_resulting_resolution,[],[f126,f274,f111])).
% 5.74/1.11  fof(f111,plain,(
% 5.74/1.11    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 5.74/1.11    inference(definition_unfolding,[],[f97,f79])).
% 5.74/1.11  fof(f97,plain,(
% 5.74/1.11    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 5.74/1.11    inference(cnf_transformation,[],[f56])).
% 5.74/1.11  fof(f56,plain,(
% 5.74/1.11    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 5.74/1.11    inference(flattening,[],[f55])).
% 5.74/1.11  fof(f55,plain,(
% 5.74/1.11    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 5.74/1.11    inference(ennf_transformation,[],[f19])).
% 5.74/1.11  fof(f19,axiom,(
% 5.74/1.11    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 5.74/1.11    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 5.74/1.11  fof(f274,plain,(
% 5.74/1.11    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_9),
% 5.74/1.11    inference(avatar_component_clause,[],[f272])).
% 5.74/1.11  fof(f531,plain,(
% 5.74/1.11    spl2_18 | ~spl2_2 | ~spl2_3),
% 5.74/1.11    inference(avatar_split_clause,[],[f278,f124,f119,f528])).
% 5.74/1.11  fof(f278,plain,(
% 5.74/1.11    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | (~spl2_2 | ~spl2_3)),
% 5.74/1.11    inference(unit_resulting_resolution,[],[f121,f126,f72])).
% 5.74/1.11  fof(f72,plain,(
% 5.74/1.11    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))) )),
% 5.74/1.11    inference(cnf_transformation,[],[f37])).
% 5.74/1.11  fof(f37,plain,(
% 5.74/1.11    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 5.74/1.11    inference(ennf_transformation,[],[f29])).
% 5.74/1.11  fof(f29,axiom,(
% 5.74/1.11    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 5.74/1.11    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).
% 5.74/1.11  fof(f275,plain,(
% 5.74/1.11    spl2_9 | ~spl2_2 | ~spl2_3),
% 5.74/1.11    inference(avatar_split_clause,[],[f198,f124,f119,f272])).
% 5.74/1.11  fof(f198,plain,(
% 5.74/1.11    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_2 | ~spl2_3)),
% 5.74/1.11    inference(unit_resulting_resolution,[],[f121,f126,f89])).
% 5.74/1.11  fof(f89,plain,(
% 5.74/1.11    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 5.74/1.11    inference(cnf_transformation,[],[f49])).
% 5.74/1.11  fof(f49,plain,(
% 5.74/1.11    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 5.74/1.11    inference(flattening,[],[f48])).
% 5.74/1.11  fof(f48,plain,(
% 5.74/1.11    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 5.74/1.11    inference(ennf_transformation,[],[f24])).
% 5.74/1.11  fof(f24,axiom,(
% 5.74/1.11    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 5.74/1.11    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).
% 5.74/1.11  fof(f208,plain,(
% 5.74/1.11    spl2_8 | ~spl2_1 | ~spl2_2 | ~spl2_3),
% 5.74/1.11    inference(avatar_split_clause,[],[f195,f124,f119,f114,f205])).
% 5.74/1.11  fof(f114,plain,(
% 5.74/1.11    spl2_1 <=> v2_pre_topc(sK0)),
% 5.74/1.11    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 5.74/1.11  fof(f195,plain,(
% 5.74/1.11    v4_pre_topc(k2_pre_topc(sK0,sK1),sK0) | (~spl2_1 | ~spl2_2 | ~spl2_3)),
% 5.74/1.11    inference(unit_resulting_resolution,[],[f116,f121,f126,f88])).
% 5.74/1.11  fof(f88,plain,(
% 5.74/1.11    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v4_pre_topc(k2_pre_topc(X0,X1),X0)) )),
% 5.74/1.11    inference(cnf_transformation,[],[f47])).
% 5.74/1.11  fof(f47,plain,(
% 5.74/1.11    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 5.74/1.11    inference(flattening,[],[f46])).
% 5.74/1.11  fof(f46,plain,(
% 5.74/1.11    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 5.74/1.11    inference(ennf_transformation,[],[f25])).
% 5.74/1.11  fof(f25,axiom,(
% 5.74/1.11    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_pre_topc(X0,X1),X0))),
% 5.74/1.11    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tops_1)).
% 5.74/1.11  fof(f116,plain,(
% 5.74/1.11    v2_pre_topc(sK0) | ~spl2_1),
% 5.74/1.11    inference(avatar_component_clause,[],[f114])).
% 5.74/1.11  fof(f168,plain,(
% 5.74/1.11    spl2_5 | spl2_6),
% 5.74/1.11    inference(avatar_split_clause,[],[f66,f165,f161])).
% 5.74/1.11  fof(f66,plain,(
% 5.74/1.11    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)),
% 5.74/1.11    inference(cnf_transformation,[],[f61])).
% 5.74/1.11  fof(f127,plain,(
% 5.74/1.11    spl2_3),
% 5.74/1.11    inference(avatar_split_clause,[],[f65,f124])).
% 5.74/1.11  fof(f65,plain,(
% 5.74/1.11    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 5.74/1.11    inference(cnf_transformation,[],[f61])).
% 5.74/1.11  fof(f122,plain,(
% 5.74/1.11    spl2_2),
% 5.74/1.11    inference(avatar_split_clause,[],[f64,f119])).
% 5.74/1.11  fof(f64,plain,(
% 5.74/1.11    l1_pre_topc(sK0)),
% 5.74/1.11    inference(cnf_transformation,[],[f61])).
% 5.74/1.11  fof(f117,plain,(
% 5.74/1.11    spl2_1),
% 5.74/1.11    inference(avatar_split_clause,[],[f63,f114])).
% 5.74/1.11  fof(f63,plain,(
% 5.74/1.11    v2_pre_topc(sK0)),
% 5.74/1.11    inference(cnf_transformation,[],[f61])).
% 5.74/1.11  % SZS output end Proof for theBenchmark
% 5.74/1.11  % (28868)------------------------------
% 5.74/1.11  % (28868)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.74/1.11  % (28868)Termination reason: Refutation
% 5.74/1.11  
% 5.74/1.11  % (28868)Memory used [KB]: 19957
% 5.74/1.11  % (28868)Time elapsed: 0.687 s
% 5.74/1.11  % (28868)------------------------------
% 5.74/1.11  % (28868)------------------------------
% 5.74/1.11  % (28852)Success in time 0.755 s
%------------------------------------------------------------------------------
