%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:49 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 379 expanded)
%              Number of leaves         :   30 ( 135 expanded)
%              Depth                    :   14
%              Number of atoms          :  392 ( 963 expanded)
%              Number of equality atoms :   44 ( 185 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f311,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f65,f70,f77,f86,f95,f100,f105,f115,f143,f176,f198,f248,f293,f310])).

fof(f310,plain,
    ( ~ spl2_1
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_8
    | ~ spl2_9
    | ~ spl2_11
    | ~ spl2_12
    | ~ spl2_15 ),
    inference(avatar_contradiction_clause,[],[f309])).

fof(f309,plain,
    ( $false
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_8
    | ~ spl2_9
    | ~ spl2_11
    | ~ spl2_12
    | ~ spl2_15 ),
    inference(subsumption_resolution,[],[f308,f303])).

fof(f303,plain,
    ( ~ v3_pre_topc(k5_xboole_0(k2_struct_0(sK0),sK1),sK0)
    | ~ spl2_4
    | ~ spl2_8
    | ~ spl2_12 ),
    inference(subsumption_resolution,[],[f299,f81])).

fof(f81,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl2_4
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f299,plain,
    ( ~ v3_pre_topc(k5_xboole_0(k2_struct_0(sK0),sK1),sK0)
    | ~ v4_pre_topc(sK1,sK0)
    | ~ spl2_8
    | ~ spl2_12 ),
    inference(forward_demodulation,[],[f298,f197])).

fof(f197,plain,
    ( k3_subset_1(k2_struct_0(sK0),sK1) = k5_xboole_0(k2_struct_0(sK0),sK1)
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f195])).

fof(f195,plain,
    ( spl2_12
  <=> k3_subset_1(k2_struct_0(sK0),sK1) = k5_xboole_0(k2_struct_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f298,plain,
    ( ~ v3_pre_topc(k3_subset_1(k2_struct_0(sK0),sK1),sK0)
    | ~ v4_pre_topc(sK1,sK0)
    | ~ spl2_8 ),
    inference(forward_demodulation,[],[f37,f104])).

fof(f104,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl2_8
  <=> u1_struct_0(sK0) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f37,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
      | ~ v4_pre_topc(sK1,sK0) )
    & ( v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
      | v4_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f28,f30,f29])).

fof(f29,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v4_pre_topc(X1,X0) )
            & ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
              | v4_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X1),sK0)
            | ~ v4_pre_topc(X1,sK0) )
          & ( v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X1),sK0)
            | v4_pre_topc(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X1] :
        ( ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X1),sK0)
          | ~ v4_pre_topc(X1,sK0) )
        & ( v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X1),sK0)
          | v4_pre_topc(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
        | ~ v4_pre_topc(sK1,sK0) )
      & ( v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
        | v4_pre_topc(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
            | ~ v4_pre_topc(X1,X0) )
          & ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
            | ~ v4_pre_topc(X1,X0) )
          & ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tops_1)).

fof(f308,plain,
    ( v3_pre_topc(k5_xboole_0(k2_struct_0(sK0),sK1),sK0)
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_8
    | ~ spl2_9
    | ~ spl2_11
    | ~ spl2_15 ),
    inference(forward_demodulation,[],[f307,f289])).

fof(f289,plain,
    ( k5_xboole_0(k2_struct_0(sK0),sK1) = k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1)
    | ~ spl2_6
    | ~ spl2_9
    | ~ spl2_11
    | ~ spl2_15 ),
    inference(forward_demodulation,[],[f276,f266])).

fof(f266,plain,
    ( k5_xboole_0(k2_struct_0(sK0),sK1) = k1_setfam_1(k2_tarski(k2_struct_0(sK0),k5_xboole_0(k2_struct_0(sK0),sK1)))
    | ~ spl2_15 ),
    inference(forward_demodulation,[],[f263,f44])).

fof(f44,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f263,plain,
    ( k5_xboole_0(k2_struct_0(sK0),sK1) = k1_setfam_1(k2_tarski(k5_xboole_0(k2_struct_0(sK0),sK1),k2_struct_0(sK0)))
    | ~ spl2_15 ),
    inference(unit_resulting_resolution,[],[f247,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_setfam_1(k2_tarski(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f48,f45])).

fof(f45,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f48,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f247,plain,
    ( r1_tarski(k5_xboole_0(k2_struct_0(sK0),sK1),k2_struct_0(sK0))
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f245])).

fof(f245,plain,
    ( spl2_15
  <=> r1_tarski(k5_xboole_0(k2_struct_0(sK0),sK1),k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f276,plain,
    ( k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1) = k1_setfam_1(k2_tarski(k2_struct_0(sK0),k5_xboole_0(k2_struct_0(sK0),sK1)))
    | ~ spl2_6
    | ~ spl2_9
    | ~ spl2_11 ),
    inference(unit_resulting_resolution,[],[f60,f191])).

fof(f191,plain,
    ( ! [X5] :
        ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_struct_0(sK0)))
        | k7_subset_1(k2_struct_0(sK0),X5,sK1) = k1_setfam_1(k2_tarski(X5,k5_xboole_0(k2_struct_0(sK0),sK1))) )
    | ~ spl2_6
    | ~ spl2_9
    | ~ spl2_11 ),
    inference(backward_demodulation,[],[f171,f184])).

fof(f184,plain,
    ( ! [X0] : k9_subset_1(k2_struct_0(sK0),X0,k5_xboole_0(k2_struct_0(sK0),sK1)) = k1_setfam_1(k2_tarski(X0,k5_xboole_0(k2_struct_0(sK0),sK1)))
    | ~ spl2_11 ),
    inference(unit_resulting_resolution,[],[f175,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) ) ),
    inference(definition_unfolding,[],[f54,f45])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f175,plain,
    ( m1_subset_1(k5_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f173])).

fof(f173,plain,
    ( spl2_11
  <=> m1_subset_1(k5_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f171,plain,
    ( ! [X5] :
        ( k7_subset_1(k2_struct_0(sK0),X5,sK1) = k9_subset_1(k2_struct_0(sK0),X5,k5_xboole_0(k2_struct_0(sK0),sK1))
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_struct_0(sK0))) )
    | ~ spl2_6
    | ~ spl2_9 ),
    inference(forward_demodulation,[],[f164,f136])).

fof(f136,plain,
    ( k3_subset_1(k2_struct_0(sK0),sK1) = k5_xboole_0(k2_struct_0(sK0),sK1)
    | ~ spl2_6
    | ~ spl2_9 ),
    inference(backward_demodulation,[],[f131,f133])).

fof(f133,plain,
    ( sK1 = k1_setfam_1(k2_tarski(sK1,k2_struct_0(sK0)))
    | ~ spl2_9 ),
    inference(unit_resulting_resolution,[],[f114,f57])).

fof(f114,plain,
    ( r1_tarski(sK1,k2_struct_0(sK0))
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl2_9
  <=> r1_tarski(sK1,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f131,plain,
    ( k3_subset_1(k2_struct_0(sK0),sK1) = k5_xboole_0(k2_struct_0(sK0),k1_setfam_1(k2_tarski(sK1,k2_struct_0(sK0))))
    | ~ spl2_6 ),
    inference(forward_demodulation,[],[f126,f44])).

fof(f126,plain,
    ( k3_subset_1(k2_struct_0(sK0),sK1) = k5_xboole_0(k2_struct_0(sK0),k1_setfam_1(k2_tarski(k2_struct_0(sK0),sK1)))
    | ~ spl2_6 ),
    inference(unit_resulting_resolution,[],[f94,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ) ),
    inference(definition_unfolding,[],[f50,f55])).

fof(f55,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f46,f45])).

fof(f46,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f50,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f94,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl2_6
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f164,plain,
    ( ! [X5] :
        ( k7_subset_1(k2_struct_0(sK0),X5,sK1) = k9_subset_1(k2_struct_0(sK0),X5,k3_subset_1(k2_struct_0(sK0),sK1))
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_struct_0(sK0))) )
    | ~ spl2_6 ),
    inference(resolution,[],[f51,f94])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_subset_1)).

fof(f60,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f39,f38])).

fof(f38,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f39,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f307,plain,
    ( v3_pre_topc(k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1),sK0)
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_8 ),
    inference(unit_resulting_resolution,[],[f94,f81,f149])).

fof(f149,plain,
    ( ! [X0] :
        ( v3_pre_topc(k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),X0),sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ v4_pre_topc(X0,sK0) )
    | ~ spl2_1
    | ~ spl2_8 ),
    inference(forward_demodulation,[],[f148,f104])).

fof(f148,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ v4_pre_topc(X0,sK0)
        | v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0),sK0) )
    | ~ spl2_1
    | ~ spl2_8 ),
    inference(forward_demodulation,[],[f147,f104])).

fof(f147,plain,
    ( ! [X0] :
        ( ~ v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0),sK0) )
    | ~ spl2_1 ),
    inference(resolution,[],[f42,f64])).

fof(f64,plain,
    ( l1_pre_topc(sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl2_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | ~ v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) )
            & ( v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_pre_topc)).

fof(f293,plain,
    ( ~ spl2_1
    | spl2_4
    | ~ spl2_6
    | ~ spl2_8
    | ~ spl2_9
    | ~ spl2_10
    | ~ spl2_11
    | ~ spl2_15 ),
    inference(avatar_contradiction_clause,[],[f292])).

fof(f292,plain,
    ( $false
    | ~ spl2_1
    | spl2_4
    | ~ spl2_6
    | ~ spl2_8
    | ~ spl2_9
    | ~ spl2_10
    | ~ spl2_11
    | ~ spl2_15 ),
    inference(subsumption_resolution,[],[f291,f142])).

fof(f142,plain,
    ( v3_pre_topc(k5_xboole_0(k2_struct_0(sK0),sK1),sK0)
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f140])).

fof(f140,plain,
    ( spl2_10
  <=> v3_pre_topc(k5_xboole_0(k2_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f291,plain,
    ( ~ v3_pre_topc(k5_xboole_0(k2_struct_0(sK0),sK1),sK0)
    | ~ spl2_1
    | spl2_4
    | ~ spl2_6
    | ~ spl2_8
    | ~ spl2_9
    | ~ spl2_11
    | ~ spl2_15 ),
    inference(backward_demodulation,[],[f249,f289])).

fof(f249,plain,
    ( ~ v3_pre_topc(k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1),sK0)
    | ~ spl2_1
    | spl2_4
    | ~ spl2_6
    | ~ spl2_8 ),
    inference(unit_resulting_resolution,[],[f80,f94,f157])).

fof(f157,plain,
    ( ! [X0] :
        ( ~ v3_pre_topc(k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),X0),sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | v4_pre_topc(X0,sK0) )
    | ~ spl2_1
    | ~ spl2_8 ),
    inference(forward_demodulation,[],[f156,f104])).

fof(f156,plain,
    ( ! [X0] :
        ( ~ v3_pre_topc(k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),X0),sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v4_pre_topc(X0,sK0) )
    | ~ spl2_1
    | ~ spl2_8 ),
    inference(forward_demodulation,[],[f155,f104])).

fof(f155,plain,
    ( ! [X0] :
        ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0),sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v4_pre_topc(X0,sK0) )
    | ~ spl2_1 ),
    inference(resolution,[],[f43,f64])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v4_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f80,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | spl2_4 ),
    inference(avatar_component_clause,[],[f79])).

fof(f248,plain,
    ( spl2_15
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f186,f173,f245])).

fof(f186,plain,
    ( r1_tarski(k5_xboole_0(k2_struct_0(sK0),sK1),k2_struct_0(sK0))
    | ~ spl2_11 ),
    inference(unit_resulting_resolution,[],[f175,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f198,plain,
    ( spl2_12
    | ~ spl2_6
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f136,f112,f92,f195])).

fof(f176,plain,
    ( spl2_11
    | ~ spl2_6
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f137,f112,f92,f173])).

fof(f137,plain,
    ( m1_subset_1(k5_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl2_6
    | ~ spl2_9 ),
    inference(backward_demodulation,[],[f117,f136])).

fof(f117,plain,
    ( m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl2_6 ),
    inference(unit_resulting_resolution,[],[f94,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f143,plain,
    ( spl2_10
    | ~ spl2_6
    | ~ spl2_7
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f138,f112,f97,f92,f140])).

fof(f97,plain,
    ( spl2_7
  <=> v3_pre_topc(k3_subset_1(k2_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f138,plain,
    ( v3_pre_topc(k5_xboole_0(k2_struct_0(sK0),sK1),sK0)
    | ~ spl2_6
    | ~ spl2_7
    | ~ spl2_9 ),
    inference(backward_demodulation,[],[f99,f136])).

fof(f99,plain,
    ( v3_pre_topc(k3_subset_1(k2_struct_0(sK0),sK1),sK0)
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f97])).

fof(f115,plain,
    ( spl2_9
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f107,f92,f112])).

fof(f107,plain,
    ( r1_tarski(sK1,k2_struct_0(sK0))
    | ~ spl2_6 ),
    inference(unit_resulting_resolution,[],[f94,f52])).

fof(f105,plain,
    ( spl2_8
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f87,f74,f102])).

fof(f74,plain,
    ( spl2_3
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f87,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f76,f40])).

fof(f40,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f76,plain,
    ( l1_struct_0(sK0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f74])).

fof(f100,plain,
    ( spl2_7
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f89,f83,f74,f97])).

fof(f83,plain,
    ( spl2_5
  <=> v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f89,plain,
    ( v3_pre_topc(k3_subset_1(k2_struct_0(sK0),sK1),sK0)
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(backward_demodulation,[],[f85,f87])).

fof(f85,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f83])).

fof(f95,plain,
    ( spl2_6
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f90,f74,f67,f92])).

fof(f67,plain,
    ( spl2_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f90,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(backward_demodulation,[],[f69,f87])).

fof(f69,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f67])).

fof(f86,plain,
    ( spl2_4
    | spl2_5 ),
    inference(avatar_split_clause,[],[f36,f83,f79])).

fof(f36,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f77,plain,
    ( spl2_3
    | ~ spl2_1 ),
    inference(avatar_split_clause,[],[f71,f62,f74])).

fof(f71,plain,
    ( l1_struct_0(sK0)
    | ~ spl2_1 ),
    inference(unit_resulting_resolution,[],[f64,f41])).

fof(f41,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f70,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f35,f67])).

fof(f35,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f31])).

fof(f65,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f34,f62])).

fof(f34,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:21:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.46  % (19726)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.46  % (19722)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.47  % (19725)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.47  % (19727)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.47  % (19737)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.47  % (19729)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.47  % (19724)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.47  % (19733)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.47  % (19736)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.48  % (19737)Refutation found. Thanks to Tanya!
% 0.20/0.48  % SZS status Theorem for theBenchmark
% 0.20/0.48  % (19734)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.48  % (19735)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.48  fof(f311,plain,(
% 0.20/0.48    $false),
% 0.20/0.48    inference(avatar_sat_refutation,[],[f65,f70,f77,f86,f95,f100,f105,f115,f143,f176,f198,f248,f293,f310])).
% 0.20/0.48  fof(f310,plain,(
% 0.20/0.48    ~spl2_1 | ~spl2_4 | ~spl2_6 | ~spl2_8 | ~spl2_9 | ~spl2_11 | ~spl2_12 | ~spl2_15),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f309])).
% 0.20/0.48  fof(f309,plain,(
% 0.20/0.48    $false | (~spl2_1 | ~spl2_4 | ~spl2_6 | ~spl2_8 | ~spl2_9 | ~spl2_11 | ~spl2_12 | ~spl2_15)),
% 0.20/0.48    inference(subsumption_resolution,[],[f308,f303])).
% 0.20/0.48  fof(f303,plain,(
% 0.20/0.48    ~v3_pre_topc(k5_xboole_0(k2_struct_0(sK0),sK1),sK0) | (~spl2_4 | ~spl2_8 | ~spl2_12)),
% 0.20/0.48    inference(subsumption_resolution,[],[f299,f81])).
% 0.20/0.48  fof(f81,plain,(
% 0.20/0.48    v4_pre_topc(sK1,sK0) | ~spl2_4),
% 0.20/0.48    inference(avatar_component_clause,[],[f79])).
% 0.20/0.48  fof(f79,plain,(
% 0.20/0.48    spl2_4 <=> v4_pre_topc(sK1,sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.20/0.48  fof(f299,plain,(
% 0.20/0.48    ~v3_pre_topc(k5_xboole_0(k2_struct_0(sK0),sK1),sK0) | ~v4_pre_topc(sK1,sK0) | (~spl2_8 | ~spl2_12)),
% 0.20/0.48    inference(forward_demodulation,[],[f298,f197])).
% 0.20/0.48  fof(f197,plain,(
% 0.20/0.48    k3_subset_1(k2_struct_0(sK0),sK1) = k5_xboole_0(k2_struct_0(sK0),sK1) | ~spl2_12),
% 0.20/0.48    inference(avatar_component_clause,[],[f195])).
% 0.20/0.48  fof(f195,plain,(
% 0.20/0.48    spl2_12 <=> k3_subset_1(k2_struct_0(sK0),sK1) = k5_xboole_0(k2_struct_0(sK0),sK1)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.20/0.48  fof(f298,plain,(
% 0.20/0.48    ~v3_pre_topc(k3_subset_1(k2_struct_0(sK0),sK1),sK0) | ~v4_pre_topc(sK1,sK0) | ~spl2_8),
% 0.20/0.48    inference(forward_demodulation,[],[f37,f104])).
% 0.20/0.48  fof(f104,plain,(
% 0.20/0.48    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl2_8),
% 0.20/0.48    inference(avatar_component_clause,[],[f102])).
% 0.20/0.48  fof(f102,plain,(
% 0.20/0.48    spl2_8 <=> u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.20/0.48  fof(f37,plain,(
% 0.20/0.48    ~v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | ~v4_pre_topc(sK1,sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f31])).
% 0.20/0.48  fof(f31,plain,(
% 0.20/0.48    ((~v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | ~v4_pre_topc(sK1,sK0)) & (v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f28,f30,f29])).
% 0.20/0.48  fof(f29,plain,(
% 0.20/0.48    ? [X0] : (? [X1] : ((~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0)) & (v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : ((~v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X1),sK0) | ~v4_pre_topc(X1,sK0)) & (v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X1),sK0) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f30,plain,(
% 0.20/0.48    ? [X1] : ((~v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X1),sK0) | ~v4_pre_topc(X1,sK0)) & (v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X1),sK0) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((~v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | ~v4_pre_topc(sK1,sK0)) & (v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f28,plain,(
% 0.20/0.48    ? [X0] : (? [X1] : ((~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0)) & (v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.20/0.48    inference(flattening,[],[f27])).
% 0.20/0.48  fof(f27,plain,(
% 0.20/0.48    ? [X0] : (? [X1] : (((~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0)) & (v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.20/0.48    inference(nnf_transformation,[],[f18])).
% 0.20/0.48  fof(f18,plain,(
% 0.20/0.48    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f17])).
% 0.20/0.48  fof(f17,negated_conjecture,(
% 0.20/0.48    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 0.20/0.48    inference(negated_conjecture,[],[f16])).
% 0.20/0.48  fof(f16,conjecture,(
% 0.20/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tops_1)).
% 0.20/0.48  fof(f308,plain,(
% 0.20/0.48    v3_pre_topc(k5_xboole_0(k2_struct_0(sK0),sK1),sK0) | (~spl2_1 | ~spl2_4 | ~spl2_6 | ~spl2_8 | ~spl2_9 | ~spl2_11 | ~spl2_15)),
% 0.20/0.48    inference(forward_demodulation,[],[f307,f289])).
% 0.20/0.48  fof(f289,plain,(
% 0.20/0.48    k5_xboole_0(k2_struct_0(sK0),sK1) = k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1) | (~spl2_6 | ~spl2_9 | ~spl2_11 | ~spl2_15)),
% 0.20/0.48    inference(forward_demodulation,[],[f276,f266])).
% 0.20/0.48  fof(f266,plain,(
% 0.20/0.48    k5_xboole_0(k2_struct_0(sK0),sK1) = k1_setfam_1(k2_tarski(k2_struct_0(sK0),k5_xboole_0(k2_struct_0(sK0),sK1))) | ~spl2_15),
% 0.20/0.48    inference(forward_demodulation,[],[f263,f44])).
% 0.20/0.48  fof(f44,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f4])).
% 0.20/0.48  fof(f4,axiom,(
% 0.20/0.48    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.20/0.48  fof(f263,plain,(
% 0.20/0.48    k5_xboole_0(k2_struct_0(sK0),sK1) = k1_setfam_1(k2_tarski(k5_xboole_0(k2_struct_0(sK0),sK1),k2_struct_0(sK0))) | ~spl2_15),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f247,f57])).
% 0.20/0.48  fof(f57,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_setfam_1(k2_tarski(X0,X1)) = X0) )),
% 0.20/0.48    inference(definition_unfolding,[],[f48,f45])).
% 0.20/0.48  fof(f45,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f11])).
% 0.20/0.48  fof(f11,axiom,(
% 0.20/0.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.20/0.48  fof(f48,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f22])).
% 0.20/0.48  fof(f22,plain,(
% 0.20/0.48    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.20/0.48    inference(ennf_transformation,[],[f2])).
% 0.20/0.48  fof(f2,axiom,(
% 0.20/0.48    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.20/0.48  fof(f247,plain,(
% 0.20/0.48    r1_tarski(k5_xboole_0(k2_struct_0(sK0),sK1),k2_struct_0(sK0)) | ~spl2_15),
% 0.20/0.48    inference(avatar_component_clause,[],[f245])).
% 0.20/0.48  fof(f245,plain,(
% 0.20/0.48    spl2_15 <=> r1_tarski(k5_xboole_0(k2_struct_0(sK0),sK1),k2_struct_0(sK0))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.20/0.48  fof(f276,plain,(
% 0.20/0.48    k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1) = k1_setfam_1(k2_tarski(k2_struct_0(sK0),k5_xboole_0(k2_struct_0(sK0),sK1))) | (~spl2_6 | ~spl2_9 | ~spl2_11)),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f60,f191])).
% 0.20/0.48  fof(f191,plain,(
% 0.20/0.48    ( ! [X5] : (~m1_subset_1(X5,k1_zfmisc_1(k2_struct_0(sK0))) | k7_subset_1(k2_struct_0(sK0),X5,sK1) = k1_setfam_1(k2_tarski(X5,k5_xboole_0(k2_struct_0(sK0),sK1)))) ) | (~spl2_6 | ~spl2_9 | ~spl2_11)),
% 0.20/0.48    inference(backward_demodulation,[],[f171,f184])).
% 0.20/0.48  fof(f184,plain,(
% 0.20/0.48    ( ! [X0] : (k9_subset_1(k2_struct_0(sK0),X0,k5_xboole_0(k2_struct_0(sK0),sK1)) = k1_setfam_1(k2_tarski(X0,k5_xboole_0(k2_struct_0(sK0),sK1)))) ) | ~spl2_11),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f175,f59])).
% 0.20/0.48  fof(f59,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))) )),
% 0.20/0.48    inference(definition_unfolding,[],[f54,f45])).
% 0.20/0.48  fof(f54,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f26])).
% 0.20/0.48  fof(f26,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f9])).
% 0.20/0.48  fof(f9,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 0.20/0.48  fof(f175,plain,(
% 0.20/0.48    m1_subset_1(k5_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) | ~spl2_11),
% 0.20/0.48    inference(avatar_component_clause,[],[f173])).
% 0.20/0.48  fof(f173,plain,(
% 0.20/0.48    spl2_11 <=> m1_subset_1(k5_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.20/0.48  fof(f171,plain,(
% 0.20/0.48    ( ! [X5] : (k7_subset_1(k2_struct_0(sK0),X5,sK1) = k9_subset_1(k2_struct_0(sK0),X5,k5_xboole_0(k2_struct_0(sK0),sK1)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_struct_0(sK0)))) ) | (~spl2_6 | ~spl2_9)),
% 0.20/0.48    inference(forward_demodulation,[],[f164,f136])).
% 0.20/0.48  fof(f136,plain,(
% 0.20/0.48    k3_subset_1(k2_struct_0(sK0),sK1) = k5_xboole_0(k2_struct_0(sK0),sK1) | (~spl2_6 | ~spl2_9)),
% 0.20/0.48    inference(backward_demodulation,[],[f131,f133])).
% 0.20/0.48  fof(f133,plain,(
% 0.20/0.48    sK1 = k1_setfam_1(k2_tarski(sK1,k2_struct_0(sK0))) | ~spl2_9),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f114,f57])).
% 0.20/0.48  fof(f114,plain,(
% 0.20/0.48    r1_tarski(sK1,k2_struct_0(sK0)) | ~spl2_9),
% 0.20/0.48    inference(avatar_component_clause,[],[f112])).
% 0.20/0.48  fof(f112,plain,(
% 0.20/0.48    spl2_9 <=> r1_tarski(sK1,k2_struct_0(sK0))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.20/0.48  fof(f131,plain,(
% 0.20/0.48    k3_subset_1(k2_struct_0(sK0),sK1) = k5_xboole_0(k2_struct_0(sK0),k1_setfam_1(k2_tarski(sK1,k2_struct_0(sK0)))) | ~spl2_6),
% 0.20/0.48    inference(forward_demodulation,[],[f126,f44])).
% 0.20/0.48  fof(f126,plain,(
% 0.20/0.48    k3_subset_1(k2_struct_0(sK0),sK1) = k5_xboole_0(k2_struct_0(sK0),k1_setfam_1(k2_tarski(k2_struct_0(sK0),sK1))) | ~spl2_6),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f94,f58])).
% 0.20/0.48  fof(f58,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 0.20/0.48    inference(definition_unfolding,[],[f50,f55])).
% 0.20/0.48  fof(f55,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 0.20/0.48    inference(definition_unfolding,[],[f46,f45])).
% 0.20/0.48  fof(f46,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f1])).
% 0.20/0.48  fof(f1,axiom,(
% 0.20/0.48    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.20/0.48  fof(f50,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f24])).
% 0.20/0.48  fof(f24,plain,(
% 0.20/0.48    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f6])).
% 0.20/0.48  fof(f6,axiom,(
% 0.20/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 0.20/0.48  fof(f94,plain,(
% 0.20/0.48    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | ~spl2_6),
% 0.20/0.48    inference(avatar_component_clause,[],[f92])).
% 0.20/0.48  fof(f92,plain,(
% 0.20/0.48    spl2_6 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.20/0.48  fof(f164,plain,(
% 0.20/0.48    ( ! [X5] : (k7_subset_1(k2_struct_0(sK0),X5,sK1) = k9_subset_1(k2_struct_0(sK0),X5,k3_subset_1(k2_struct_0(sK0),sK1)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_struct_0(sK0)))) ) | ~spl2_6),
% 0.20/0.48    inference(resolution,[],[f51,f94])).
% 0.20/0.48  fof(f51,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f25])).
% 0.20/0.48  fof(f25,plain,(
% 0.20/0.48    ! [X0,X1] : (! [X2] : (k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f10])).
% 0.20/0.48  fof(f10,axiom,(
% 0.20/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_subset_1)).
% 0.20/0.48  fof(f60,plain,(
% 0.20/0.48    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.20/0.48    inference(forward_demodulation,[],[f39,f38])).
% 0.20/0.48  fof(f38,plain,(
% 0.20/0.48    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.20/0.48    inference(cnf_transformation,[],[f5])).
% 0.20/0.48  fof(f5,axiom,(
% 0.20/0.48    ! [X0] : k2_subset_1(X0) = X0),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 0.20/0.48  fof(f39,plain,(
% 0.20/0.48    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f7])).
% 0.20/0.48  fof(f7,axiom,(
% 0.20/0.48    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.20/0.48  fof(f307,plain,(
% 0.20/0.48    v3_pre_topc(k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1),sK0) | (~spl2_1 | ~spl2_4 | ~spl2_6 | ~spl2_8)),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f94,f81,f149])).
% 0.20/0.48  fof(f149,plain,(
% 0.20/0.48    ( ! [X0] : (v3_pre_topc(k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),X0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~v4_pre_topc(X0,sK0)) ) | (~spl2_1 | ~spl2_8)),
% 0.20/0.48    inference(forward_demodulation,[],[f148,f104])).
% 0.20/0.48  fof(f148,plain,(
% 0.20/0.48    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~v4_pre_topc(X0,sK0) | v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0),sK0)) ) | (~spl2_1 | ~spl2_8)),
% 0.20/0.48    inference(forward_demodulation,[],[f147,f104])).
% 0.20/0.48  fof(f147,plain,(
% 0.20/0.48    ( ! [X0] : (~v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0),sK0)) ) | ~spl2_1),
% 0.20/0.48    inference(resolution,[],[f42,f64])).
% 0.20/0.48  fof(f64,plain,(
% 0.20/0.48    l1_pre_topc(sK0) | ~spl2_1),
% 0.20/0.48    inference(avatar_component_clause,[],[f62])).
% 0.20/0.48  fof(f62,plain,(
% 0.20/0.48    spl2_1 <=> l1_pre_topc(sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.20/0.48  fof(f42,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f32])).
% 0.20/0.48  fof(f32,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | ~v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)) & (v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.48    inference(nnf_transformation,[],[f21])).
% 0.20/0.48  fof(f21,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f14])).
% 0.20/0.48  fof(f14,axiom,(
% 0.20/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_pre_topc)).
% 0.20/0.48  fof(f293,plain,(
% 0.20/0.48    ~spl2_1 | spl2_4 | ~spl2_6 | ~spl2_8 | ~spl2_9 | ~spl2_10 | ~spl2_11 | ~spl2_15),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f292])).
% 0.20/0.48  fof(f292,plain,(
% 0.20/0.48    $false | (~spl2_1 | spl2_4 | ~spl2_6 | ~spl2_8 | ~spl2_9 | ~spl2_10 | ~spl2_11 | ~spl2_15)),
% 0.20/0.48    inference(subsumption_resolution,[],[f291,f142])).
% 0.20/0.48  fof(f142,plain,(
% 0.20/0.48    v3_pre_topc(k5_xboole_0(k2_struct_0(sK0),sK1),sK0) | ~spl2_10),
% 0.20/0.48    inference(avatar_component_clause,[],[f140])).
% 0.20/0.48  fof(f140,plain,(
% 0.20/0.48    spl2_10 <=> v3_pre_topc(k5_xboole_0(k2_struct_0(sK0),sK1),sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.20/0.48  fof(f291,plain,(
% 0.20/0.48    ~v3_pre_topc(k5_xboole_0(k2_struct_0(sK0),sK1),sK0) | (~spl2_1 | spl2_4 | ~spl2_6 | ~spl2_8 | ~spl2_9 | ~spl2_11 | ~spl2_15)),
% 0.20/0.48    inference(backward_demodulation,[],[f249,f289])).
% 0.20/0.48  fof(f249,plain,(
% 0.20/0.48    ~v3_pre_topc(k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1),sK0) | (~spl2_1 | spl2_4 | ~spl2_6 | ~spl2_8)),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f80,f94,f157])).
% 0.20/0.48  fof(f157,plain,(
% 0.20/0.48    ( ! [X0] : (~v3_pre_topc(k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),X0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | v4_pre_topc(X0,sK0)) ) | (~spl2_1 | ~spl2_8)),
% 0.20/0.48    inference(forward_demodulation,[],[f156,f104])).
% 0.20/0.48  fof(f156,plain,(
% 0.20/0.48    ( ! [X0] : (~v3_pre_topc(k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),X0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(X0,sK0)) ) | (~spl2_1 | ~spl2_8)),
% 0.20/0.48    inference(forward_demodulation,[],[f155,f104])).
% 0.20/0.48  fof(f155,plain,(
% 0.20/0.48    ( ! [X0] : (~v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(X0,sK0)) ) | ~spl2_1),
% 0.20/0.48    inference(resolution,[],[f43,f64])).
% 0.20/0.48  fof(f43,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v4_pre_topc(X1,X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f32])).
% 0.20/0.48  fof(f80,plain,(
% 0.20/0.48    ~v4_pre_topc(sK1,sK0) | spl2_4),
% 0.20/0.48    inference(avatar_component_clause,[],[f79])).
% 0.20/0.48  fof(f248,plain,(
% 0.20/0.48    spl2_15 | ~spl2_11),
% 0.20/0.48    inference(avatar_split_clause,[],[f186,f173,f245])).
% 0.20/0.48  fof(f186,plain,(
% 0.20/0.48    r1_tarski(k5_xboole_0(k2_struct_0(sK0),sK1),k2_struct_0(sK0)) | ~spl2_11),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f175,f52])).
% 0.20/0.48  fof(f52,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f33])).
% 0.20/0.48  fof(f33,plain,(
% 0.20/0.48    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.20/0.48    inference(nnf_transformation,[],[f12])).
% 0.20/0.48  fof(f12,axiom,(
% 0.20/0.48    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.48  fof(f198,plain,(
% 0.20/0.48    spl2_12 | ~spl2_6 | ~spl2_9),
% 0.20/0.48    inference(avatar_split_clause,[],[f136,f112,f92,f195])).
% 0.20/0.48  fof(f176,plain,(
% 0.20/0.48    spl2_11 | ~spl2_6 | ~spl2_9),
% 0.20/0.48    inference(avatar_split_clause,[],[f137,f112,f92,f173])).
% 0.20/0.48  fof(f137,plain,(
% 0.20/0.48    m1_subset_1(k5_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) | (~spl2_6 | ~spl2_9)),
% 0.20/0.48    inference(backward_demodulation,[],[f117,f136])).
% 0.20/0.48  fof(f117,plain,(
% 0.20/0.48    m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) | ~spl2_6),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f94,f49])).
% 0.20/0.48  fof(f49,plain,(
% 0.20/0.48    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f23])).
% 0.20/0.48  fof(f23,plain,(
% 0.20/0.48    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f8])).
% 0.20/0.48  fof(f8,axiom,(
% 0.20/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 0.20/0.48  fof(f143,plain,(
% 0.20/0.48    spl2_10 | ~spl2_6 | ~spl2_7 | ~spl2_9),
% 0.20/0.48    inference(avatar_split_clause,[],[f138,f112,f97,f92,f140])).
% 0.20/0.48  fof(f97,plain,(
% 0.20/0.48    spl2_7 <=> v3_pre_topc(k3_subset_1(k2_struct_0(sK0),sK1),sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.20/0.48  fof(f138,plain,(
% 0.20/0.48    v3_pre_topc(k5_xboole_0(k2_struct_0(sK0),sK1),sK0) | (~spl2_6 | ~spl2_7 | ~spl2_9)),
% 0.20/0.48    inference(backward_demodulation,[],[f99,f136])).
% 0.20/0.48  fof(f99,plain,(
% 0.20/0.48    v3_pre_topc(k3_subset_1(k2_struct_0(sK0),sK1),sK0) | ~spl2_7),
% 0.20/0.48    inference(avatar_component_clause,[],[f97])).
% 0.20/0.48  fof(f115,plain,(
% 0.20/0.48    spl2_9 | ~spl2_6),
% 0.20/0.48    inference(avatar_split_clause,[],[f107,f92,f112])).
% 0.20/0.48  fof(f107,plain,(
% 0.20/0.48    r1_tarski(sK1,k2_struct_0(sK0)) | ~spl2_6),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f94,f52])).
% 0.20/0.48  fof(f105,plain,(
% 0.20/0.48    spl2_8 | ~spl2_3),
% 0.20/0.48    inference(avatar_split_clause,[],[f87,f74,f102])).
% 0.20/0.48  fof(f74,plain,(
% 0.20/0.48    spl2_3 <=> l1_struct_0(sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.20/0.48  fof(f87,plain,(
% 0.20/0.48    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl2_3),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f76,f40])).
% 0.20/0.48  fof(f40,plain,(
% 0.20/0.48    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f19])).
% 0.20/0.48  fof(f19,plain,(
% 0.20/0.48    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f13])).
% 0.20/0.48  fof(f13,axiom,(
% 0.20/0.48    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.20/0.48  fof(f76,plain,(
% 0.20/0.48    l1_struct_0(sK0) | ~spl2_3),
% 0.20/0.48    inference(avatar_component_clause,[],[f74])).
% 0.20/0.48  fof(f100,plain,(
% 0.20/0.48    spl2_7 | ~spl2_3 | ~spl2_5),
% 0.20/0.48    inference(avatar_split_clause,[],[f89,f83,f74,f97])).
% 0.20/0.48  fof(f83,plain,(
% 0.20/0.48    spl2_5 <=> v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.20/0.48  fof(f89,plain,(
% 0.20/0.48    v3_pre_topc(k3_subset_1(k2_struct_0(sK0),sK1),sK0) | (~spl2_3 | ~spl2_5)),
% 0.20/0.48    inference(backward_demodulation,[],[f85,f87])).
% 0.20/0.48  fof(f85,plain,(
% 0.20/0.48    v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | ~spl2_5),
% 0.20/0.48    inference(avatar_component_clause,[],[f83])).
% 0.20/0.48  fof(f95,plain,(
% 0.20/0.48    spl2_6 | ~spl2_2 | ~spl2_3),
% 0.20/0.48    inference(avatar_split_clause,[],[f90,f74,f67,f92])).
% 0.20/0.48  fof(f67,plain,(
% 0.20/0.48    spl2_2 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.20/0.48  fof(f90,plain,(
% 0.20/0.48    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | (~spl2_2 | ~spl2_3)),
% 0.20/0.48    inference(backward_demodulation,[],[f69,f87])).
% 0.20/0.48  fof(f69,plain,(
% 0.20/0.48    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_2),
% 0.20/0.48    inference(avatar_component_clause,[],[f67])).
% 0.20/0.48  fof(f86,plain,(
% 0.20/0.48    spl2_4 | spl2_5),
% 0.20/0.48    inference(avatar_split_clause,[],[f36,f83,f79])).
% 0.20/0.48  fof(f36,plain,(
% 0.20/0.48    v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | v4_pre_topc(sK1,sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f31])).
% 0.20/0.48  fof(f77,plain,(
% 0.20/0.48    spl2_3 | ~spl2_1),
% 0.20/0.48    inference(avatar_split_clause,[],[f71,f62,f74])).
% 0.20/0.48  fof(f71,plain,(
% 0.20/0.48    l1_struct_0(sK0) | ~spl2_1),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f64,f41])).
% 0.20/0.48  fof(f41,plain,(
% 0.20/0.48    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f20])).
% 0.20/0.48  fof(f20,plain,(
% 0.20/0.48    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f15])).
% 0.20/0.48  fof(f15,axiom,(
% 0.20/0.48    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.20/0.48  fof(f70,plain,(
% 0.20/0.48    spl2_2),
% 0.20/0.48    inference(avatar_split_clause,[],[f35,f67])).
% 0.20/0.48  fof(f35,plain,(
% 0.20/0.48    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.48    inference(cnf_transformation,[],[f31])).
% 0.20/0.48  fof(f65,plain,(
% 0.20/0.48    spl2_1),
% 0.20/0.48    inference(avatar_split_clause,[],[f34,f62])).
% 0.20/0.48  fof(f34,plain,(
% 0.20/0.48    l1_pre_topc(sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f31])).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (19737)------------------------------
% 0.20/0.48  % (19737)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (19737)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.48  % (19737)Memory used [KB]: 10874
% 0.20/0.48  % (19737)Time elapsed: 0.017 s
% 0.20/0.48  % (19737)------------------------------
% 0.20/0.48  % (19737)------------------------------
% 0.20/0.49  % (19730)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.49  % (19721)Success in time 0.128 s
%------------------------------------------------------------------------------
