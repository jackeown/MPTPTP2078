%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:50 EST 2020

% Result     : Theorem 1.77s
% Output     : Refutation 1.77s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 812 expanded)
%              Number of leaves         :   25 ( 233 expanded)
%              Depth                    :   21
%              Number of atoms          :  297 (3317 expanded)
%              Number of equality atoms :  103 (1039 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f623,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f98,f99,f556,f574,f610])).

fof(f610,plain,
    ( spl3_2
    | ~ spl3_11 ),
    inference(avatar_contradiction_clause,[],[f609])).

fof(f609,plain,
    ( $false
    | spl3_2
    | ~ spl3_11 ),
    inference(subsumption_resolution,[],[f597,f97])).

fof(f97,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl3_2
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f597,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ spl3_11 ),
    inference(backward_demodulation,[],[f111,f595])).

fof(f595,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl3_11 ),
    inference(backward_demodulation,[],[f282,f594])).

fof(f594,plain,
    ( sK1 = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f592,f155])).

fof(f155,plain,(
    sK1 = k5_xboole_0(sK1,k1_xboole_0) ),
    inference(backward_demodulation,[],[f147,f149])).

fof(f149,plain,(
    sK1 = k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0) ),
    inference(superposition,[],[f106,f82])).

fof(f82,plain,(
    ! [X0] : k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = X0 ),
    inference(definition_unfolding,[],[f57,f79])).

fof(f79,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f68,f66])).

fof(f66,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f68,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f57,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f106,plain,(
    ! [X1] : k7_subset_1(u1_struct_0(sK0),sK1,X1) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X1))) ),
    inference(resolution,[],[f52,f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) ) ),
    inference(definition_unfolding,[],[f77,f79])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f52,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,
    ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | ~ v4_pre_topc(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | v4_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f41,f43,f42])).

fof(f42,plain,
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

fof(f43,plain,
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

fof(f41,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).

fof(f147,plain,(
    k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0) = k5_xboole_0(sK1,k1_xboole_0) ),
    inference(superposition,[],[f106,f80])).

fof(f80,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f55,f66])).

fof(f55,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f592,plain,
    ( k5_xboole_0(sK1,k1_xboole_0) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl3_11 ),
    inference(superposition,[],[f274,f587])).

fof(f587,plain,
    ( k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),sK1)
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f584,f455])).

fof(f455,plain,(
    k1_xboole_0 = k5_xboole_0(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) ),
    inference(backward_demodulation,[],[f270,f453])).

fof(f453,plain,(
    k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) ),
    inference(superposition,[],[f272,f81])).

fof(f81,plain,(
    ! [X0] : k3_tarski(k2_tarski(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f56,f65])).

fof(f65,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f56,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f272,plain,(
    ! [X1] : k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),X1))) ),
    inference(superposition,[],[f120,f85])).

fof(f85,plain,(
    ! [X0,X1] : k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1))))) ),
    inference(definition_unfolding,[],[f63,f79,f65])).

fof(f63,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f120,plain,(
    ! [X1] : k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),X1) = k5_xboole_0(k2_tops_1(sK0,sK1),k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),X1))) ),
    inference(resolution,[],[f108,f88])).

fof(f108,plain,(
    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f100,f51])).

fof(f51,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f100,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f52,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(f270,plain,(
    k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) = k5_xboole_0(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) ),
    inference(superposition,[],[f120,f83])).

fof(f83,plain,(
    ! [X0] : k1_setfam_1(k2_tarski(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f61,f66])).

fof(f61,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f584,plain,
    ( k5_xboole_0(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) = k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),sK1)
    | ~ spl3_11 ),
    inference(superposition,[],[f267,f576])).

fof(f576,plain,
    ( k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f575,f64])).

fof(f64,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f575,plain,
    ( k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),sK1))
    | ~ spl3_11 ),
    inference(resolution,[],[f573,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_setfam_1(k2_tarski(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f69,f66])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f573,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f571])).

fof(f571,plain,
    ( spl3_11
  <=> r1_tarski(k2_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f267,plain,(
    ! [X0] : k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),X0) = k5_xboole_0(k2_tops_1(sK0,sK1),k1_setfam_1(k2_tarski(X0,k2_tops_1(sK0,sK1)))) ),
    inference(superposition,[],[f120,f64])).

fof(f274,plain,(
    ! [X0] : k3_tarski(k2_tarski(X0,k2_tops_1(sK0,sK1))) = k5_xboole_0(X0,k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),X0)) ),
    inference(superposition,[],[f86,f120])).

fof(f86,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))) ),
    inference(definition_unfolding,[],[f67,f65,f79])).

fof(f67,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f282,plain,(
    k2_pre_topc(sK0,sK1) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) ),
    inference(forward_demodulation,[],[f279,f112])).

fof(f112,plain,(
    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f104,f51])).

fof(f104,plain,
    ( k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f52,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

fof(f279,plain,(
    k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) ),
    inference(resolution,[],[f119,f52])).

fof(f119,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(X0,k2_tops_1(sK0,sK1))) ) ),
    inference(resolution,[],[f108,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f78,f65])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f111,plain,(
    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f103,f51])).

fof(f103,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f52,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

fof(f574,plain,
    ( spl3_11
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f569,f91,f571])).

fof(f91,plain,
    ( spl3_1
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f569,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | r1_tarski(k2_tops_1(sK0,sK1),sK1) ),
    inference(subsumption_resolution,[],[f102,f51])).

fof(f102,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f52,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | r1_tarski(k2_tops_1(X0,X1),X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => r1_tarski(k2_tops_1(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_tops_1)).

fof(f556,plain,
    ( spl3_1
    | ~ spl3_2 ),
    inference(avatar_contradiction_clause,[],[f555])).

fof(f555,plain,
    ( $false
    | spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f542,f93])).

fof(f93,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f91])).

fof(f542,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ spl3_2 ),
    inference(backward_demodulation,[],[f110,f541])).

fof(f541,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl3_2 ),
    inference(backward_demodulation,[],[f282,f540])).

fof(f540,plain,
    ( sK1 = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f538,f155])).

fof(f538,plain,
    ( k5_xboole_0(sK1,k1_xboole_0) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl3_2 ),
    inference(superposition,[],[f274,f537])).

fof(f537,plain,
    ( k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),sK1)
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f531,f455])).

fof(f531,plain,
    ( k5_xboole_0(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) = k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),sK1)
    | ~ spl3_2 ),
    inference(superposition,[],[f267,f166])).

fof(f166,plain,
    ( k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f165,f64])).

fof(f165,plain,
    ( k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),sK1))
    | ~ spl3_2 ),
    inference(resolution,[],[f157,f87])).

fof(f157,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ spl3_2 ),
    inference(superposition,[],[f153,f96])).

fof(f96,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f95])).

fof(f153,plain,(
    ! [X1] : r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,X1),sK1) ),
    inference(superposition,[],[f84,f106])).

fof(f84,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0) ),
    inference(definition_unfolding,[],[f62,f79])).

fof(f62,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f110,plain,(
    v4_pre_topc(k2_pre_topc(sK0,sK1),sK0) ),
    inference(subsumption_resolution,[],[f109,f50])).

fof(f50,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f109,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,sK1),sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f101,f51])).

fof(f101,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f52,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_pre_topc(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tops_1)).

fof(f99,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f53,f95,f91])).

fof(f53,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f98,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f54,f95,f91])).

fof(f54,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f44])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n025.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 20:52:06 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.53  % (16621)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.53  % (16621)Refutation not found, incomplete strategy% (16621)------------------------------
% 0.22/0.53  % (16621)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (16605)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.53  % (16612)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.53  % (16621)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (16621)Memory used [KB]: 10746
% 0.22/0.53  % (16621)Time elapsed: 0.009 s
% 0.22/0.53  % (16621)------------------------------
% 0.22/0.53  % (16621)------------------------------
% 0.22/0.54  % (16628)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.54  % (16601)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.55  % (16602)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.55  % (16600)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.55  % (16620)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.55  % (16603)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.55  % (16604)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.56  % (16613)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.56  % (16624)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.56  % (16606)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.56  % (16619)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.56  % (16617)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.57  % (16599)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.57  % (16625)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.57  % (16607)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.57  % (16611)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.57  % (16616)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.58  % (16616)Refutation not found, incomplete strategy% (16616)------------------------------
% 0.22/0.58  % (16616)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.58  % (16616)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.58  
% 0.22/0.58  % (16616)Memory used [KB]: 10618
% 0.22/0.58  % (16616)Time elapsed: 0.152 s
% 0.22/0.58  % (16616)------------------------------
% 0.22/0.58  % (16616)------------------------------
% 0.22/0.58  % (16615)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.58  % (16609)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.58  % (16618)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.58  % (16627)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.58  % (16626)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.58  % (16608)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.58  % (16623)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.59  % (16610)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.77/0.61  % (16622)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.77/0.61  % (16614)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.77/0.62  % (16607)Refutation found. Thanks to Tanya!
% 1.77/0.62  % SZS status Theorem for theBenchmark
% 1.77/0.62  % SZS output start Proof for theBenchmark
% 1.77/0.62  fof(f623,plain,(
% 1.77/0.62    $false),
% 1.77/0.62    inference(avatar_sat_refutation,[],[f98,f99,f556,f574,f610])).
% 1.77/0.62  fof(f610,plain,(
% 1.77/0.62    spl3_2 | ~spl3_11),
% 1.77/0.62    inference(avatar_contradiction_clause,[],[f609])).
% 1.77/0.62  fof(f609,plain,(
% 1.77/0.62    $false | (spl3_2 | ~spl3_11)),
% 1.77/0.62    inference(subsumption_resolution,[],[f597,f97])).
% 1.77/0.62  fof(f97,plain,(
% 1.77/0.62    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | spl3_2),
% 1.77/0.62    inference(avatar_component_clause,[],[f95])).
% 1.77/0.62  fof(f95,plain,(
% 1.77/0.62    spl3_2 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),
% 1.77/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.77/0.62  fof(f597,plain,(
% 1.77/0.62    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~spl3_11),
% 1.77/0.62    inference(backward_demodulation,[],[f111,f595])).
% 1.77/0.62  fof(f595,plain,(
% 1.77/0.62    sK1 = k2_pre_topc(sK0,sK1) | ~spl3_11),
% 1.77/0.62    inference(backward_demodulation,[],[f282,f594])).
% 1.77/0.62  fof(f594,plain,(
% 1.77/0.62    sK1 = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | ~spl3_11),
% 1.77/0.62    inference(forward_demodulation,[],[f592,f155])).
% 1.77/0.62  fof(f155,plain,(
% 1.77/0.62    sK1 = k5_xboole_0(sK1,k1_xboole_0)),
% 1.77/0.62    inference(backward_demodulation,[],[f147,f149])).
% 1.77/0.62  fof(f149,plain,(
% 1.77/0.62    sK1 = k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0)),
% 1.77/0.62    inference(superposition,[],[f106,f82])).
% 1.77/0.62  fof(f82,plain,(
% 1.77/0.62    ( ! [X0] : (k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = X0) )),
% 1.77/0.62    inference(definition_unfolding,[],[f57,f79])).
% 1.77/0.62  fof(f79,plain,(
% 1.77/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 1.77/0.62    inference(definition_unfolding,[],[f68,f66])).
% 1.77/0.62  fof(f66,plain,(
% 1.77/0.62    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.77/0.62    inference(cnf_transformation,[],[f15])).
% 1.77/0.62  fof(f15,axiom,(
% 1.77/0.62    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.77/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.77/0.62  fof(f68,plain,(
% 1.77/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.77/0.62    inference(cnf_transformation,[],[f3])).
% 1.77/0.62  fof(f3,axiom,(
% 1.77/0.62    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.77/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.77/0.62  fof(f57,plain,(
% 1.77/0.62    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.77/0.62    inference(cnf_transformation,[],[f8])).
% 1.77/0.62  fof(f8,axiom,(
% 1.77/0.62    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.77/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 1.77/0.62  fof(f106,plain,(
% 1.77/0.62    ( ! [X1] : (k7_subset_1(u1_struct_0(sK0),sK1,X1) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X1)))) )),
% 1.77/0.62    inference(resolution,[],[f52,f88])).
% 1.77/0.62  fof(f88,plain,(
% 1.77/0.62    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))) )),
% 1.77/0.62    inference(definition_unfolding,[],[f77,f79])).
% 1.77/0.62  fof(f77,plain,(
% 1.77/0.62    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.77/0.62    inference(cnf_transformation,[],[f37])).
% 1.77/0.62  fof(f37,plain,(
% 1.77/0.62    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.77/0.62    inference(ennf_transformation,[],[f14])).
% 1.77/0.62  fof(f14,axiom,(
% 1.77/0.62    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 1.77/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 1.77/0.62  fof(f52,plain,(
% 1.77/0.62    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.77/0.62    inference(cnf_transformation,[],[f44])).
% 1.77/0.62  fof(f44,plain,(
% 1.77/0.62    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 1.77/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f41,f43,f42])).
% 1.77/0.62  fof(f42,plain,(
% 1.77/0.62    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 1.77/0.62    introduced(choice_axiom,[])).
% 1.77/0.62  fof(f43,plain,(
% 1.77/0.62    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.77/0.62    introduced(choice_axiom,[])).
% 1.77/0.62  fof(f41,plain,(
% 1.77/0.62    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.77/0.62    inference(flattening,[],[f40])).
% 1.77/0.62  fof(f40,plain,(
% 1.77/0.62    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.77/0.62    inference(nnf_transformation,[],[f26])).
% 1.77/0.62  fof(f26,plain,(
% 1.77/0.62    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.77/0.62    inference(flattening,[],[f25])).
% 1.77/0.62  fof(f25,plain,(
% 1.77/0.62    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 1.77/0.62    inference(ennf_transformation,[],[f23])).
% 1.77/0.62  fof(f23,negated_conjecture,(
% 1.77/0.62    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 1.77/0.62    inference(negated_conjecture,[],[f22])).
% 1.77/0.62  fof(f22,conjecture,(
% 1.77/0.62    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 1.77/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).
% 1.77/0.62  fof(f147,plain,(
% 1.77/0.62    k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0) = k5_xboole_0(sK1,k1_xboole_0)),
% 1.77/0.62    inference(superposition,[],[f106,f80])).
% 1.77/0.62  fof(f80,plain,(
% 1.77/0.62    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0))) )),
% 1.77/0.62    inference(definition_unfolding,[],[f55,f66])).
% 1.77/0.62  fof(f55,plain,(
% 1.77/0.62    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.77/0.62    inference(cnf_transformation,[],[f6])).
% 1.77/0.62  fof(f6,axiom,(
% 1.77/0.62    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.77/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 1.77/0.62  fof(f592,plain,(
% 1.77/0.62    k5_xboole_0(sK1,k1_xboole_0) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | ~spl3_11),
% 1.77/0.62    inference(superposition,[],[f274,f587])).
% 1.77/0.62  fof(f587,plain,(
% 1.77/0.62    k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),sK1) | ~spl3_11),
% 1.77/0.62    inference(forward_demodulation,[],[f584,f455])).
% 1.77/0.62  fof(f455,plain,(
% 1.77/0.62    k1_xboole_0 = k5_xboole_0(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1))),
% 1.77/0.62    inference(backward_demodulation,[],[f270,f453])).
% 1.77/0.62  fof(f453,plain,(
% 1.77/0.62    k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1))),
% 1.77/0.62    inference(superposition,[],[f272,f81])).
% 1.77/0.62  fof(f81,plain,(
% 1.77/0.62    ( ! [X0] : (k3_tarski(k2_tarski(X0,k1_xboole_0)) = X0) )),
% 1.77/0.62    inference(definition_unfolding,[],[f56,f65])).
% 1.77/0.62  fof(f65,plain,(
% 1.77/0.62    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.77/0.62    inference(cnf_transformation,[],[f12])).
% 1.77/0.62  fof(f12,axiom,(
% 1.77/0.62    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.77/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.77/0.62  fof(f56,plain,(
% 1.77/0.62    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.77/0.62    inference(cnf_transformation,[],[f4])).
% 1.77/0.62  fof(f4,axiom,(
% 1.77/0.62    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 1.77/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 1.77/0.62  fof(f272,plain,(
% 1.77/0.62    ( ! [X1] : (k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),X1)))) )),
% 1.77/0.62    inference(superposition,[],[f120,f85])).
% 1.77/0.62  fof(f85,plain,(
% 1.77/0.62    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))))) )),
% 1.77/0.62    inference(definition_unfolding,[],[f63,f79,f65])).
% 1.77/0.62  fof(f63,plain,(
% 1.77/0.62    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 1.77/0.62    inference(cnf_transformation,[],[f9])).
% 1.77/0.62  fof(f9,axiom,(
% 1.77/0.62    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 1.77/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
% 1.77/0.62  fof(f120,plain,(
% 1.77/0.62    ( ! [X1] : (k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),X1) = k5_xboole_0(k2_tops_1(sK0,sK1),k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),X1)))) )),
% 1.77/0.62    inference(resolution,[],[f108,f88])).
% 1.77/0.62  fof(f108,plain,(
% 1.77/0.62    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.77/0.62    inference(subsumption_resolution,[],[f100,f51])).
% 1.77/0.62  fof(f51,plain,(
% 1.77/0.62    l1_pre_topc(sK0)),
% 1.77/0.62    inference(cnf_transformation,[],[f44])).
% 1.77/0.62  fof(f100,plain,(
% 1.77/0.62    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 1.77/0.62    inference(resolution,[],[f52,f71])).
% 1.77/0.62  fof(f71,plain,(
% 1.77/0.62    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.77/0.62    inference(cnf_transformation,[],[f35])).
% 1.77/0.62  fof(f35,plain,(
% 1.77/0.62    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 1.77/0.62    inference(flattening,[],[f34])).
% 1.77/0.62  fof(f34,plain,(
% 1.77/0.62    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 1.77/0.62    inference(ennf_transformation,[],[f17])).
% 1.77/0.62  fof(f17,axiom,(
% 1.77/0.62    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 1.77/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).
% 1.77/0.62  fof(f270,plain,(
% 1.77/0.62    k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) = k5_xboole_0(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1))),
% 1.77/0.62    inference(superposition,[],[f120,f83])).
% 1.77/0.62  fof(f83,plain,(
% 1.77/0.62    ( ! [X0] : (k1_setfam_1(k2_tarski(X0,X0)) = X0) )),
% 1.77/0.62    inference(definition_unfolding,[],[f61,f66])).
% 1.77/0.62  fof(f61,plain,(
% 1.77/0.62    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.77/0.62    inference(cnf_transformation,[],[f24])).
% 1.77/0.62  fof(f24,plain,(
% 1.77/0.62    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 1.77/0.62    inference(rectify,[],[f2])).
% 1.77/0.62  fof(f2,axiom,(
% 1.77/0.62    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 1.77/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 1.77/0.62  fof(f584,plain,(
% 1.77/0.62    k5_xboole_0(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) = k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),sK1) | ~spl3_11),
% 1.77/0.62    inference(superposition,[],[f267,f576])).
% 1.77/0.62  fof(f576,plain,(
% 1.77/0.62    k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | ~spl3_11),
% 1.77/0.62    inference(forward_demodulation,[],[f575,f64])).
% 1.77/0.62  fof(f64,plain,(
% 1.77/0.62    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.77/0.62    inference(cnf_transformation,[],[f11])).
% 1.77/0.62  fof(f11,axiom,(
% 1.77/0.62    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.77/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.77/0.62  fof(f575,plain,(
% 1.77/0.62    k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),sK1)) | ~spl3_11),
% 1.77/0.62    inference(resolution,[],[f573,f87])).
% 1.77/0.62  fof(f87,plain,(
% 1.77/0.62    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_setfam_1(k2_tarski(X0,X1)) = X0) )),
% 1.77/0.62    inference(definition_unfolding,[],[f69,f66])).
% 1.77/0.62  fof(f69,plain,(
% 1.77/0.62    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.77/0.62    inference(cnf_transformation,[],[f31])).
% 1.77/0.62  fof(f31,plain,(
% 1.77/0.62    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.77/0.62    inference(ennf_transformation,[],[f5])).
% 1.77/0.62  fof(f5,axiom,(
% 1.77/0.62    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.77/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.77/0.62  fof(f573,plain,(
% 1.77/0.62    r1_tarski(k2_tops_1(sK0,sK1),sK1) | ~spl3_11),
% 1.77/0.62    inference(avatar_component_clause,[],[f571])).
% 1.77/0.62  fof(f571,plain,(
% 1.77/0.62    spl3_11 <=> r1_tarski(k2_tops_1(sK0,sK1),sK1)),
% 1.77/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 1.77/0.62  fof(f267,plain,(
% 1.77/0.62    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),X0) = k5_xboole_0(k2_tops_1(sK0,sK1),k1_setfam_1(k2_tarski(X0,k2_tops_1(sK0,sK1))))) )),
% 1.77/0.62    inference(superposition,[],[f120,f64])).
% 1.77/0.62  fof(f274,plain,(
% 1.77/0.62    ( ! [X0] : (k3_tarski(k2_tarski(X0,k2_tops_1(sK0,sK1))) = k5_xboole_0(X0,k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),X0))) )),
% 1.77/0.62    inference(superposition,[],[f86,f120])).
% 1.77/0.62  fof(f86,plain,(
% 1.77/0.62    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0))))) )),
% 1.77/0.62    inference(definition_unfolding,[],[f67,f65,f79])).
% 1.77/0.62  fof(f67,plain,(
% 1.77/0.62    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.77/0.62    inference(cnf_transformation,[],[f10])).
% 1.77/0.62  fof(f10,axiom,(
% 1.77/0.62    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.77/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.77/0.62  fof(f282,plain,(
% 1.77/0.62    k2_pre_topc(sK0,sK1) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))),
% 1.77/0.62    inference(forward_demodulation,[],[f279,f112])).
% 1.77/0.62  fof(f112,plain,(
% 1.77/0.62    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 1.77/0.62    inference(subsumption_resolution,[],[f104,f51])).
% 1.77/0.62  fof(f104,plain,(
% 1.77/0.62    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | ~l1_pre_topc(sK0)),
% 1.77/0.62    inference(resolution,[],[f52,f58])).
% 1.77/0.62  fof(f58,plain,(
% 1.77/0.62    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~l1_pre_topc(X0)) )),
% 1.77/0.62    inference(cnf_transformation,[],[f27])).
% 1.77/0.62  fof(f27,plain,(
% 1.77/0.62    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.77/0.62    inference(ennf_transformation,[],[f20])).
% 1.77/0.62  fof(f20,axiom,(
% 1.77/0.62    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 1.77/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).
% 1.77/0.62  fof(f279,plain,(
% 1.77/0.62    k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))),
% 1.77/0.62    inference(resolution,[],[f119,f52])).
% 1.77/0.62  fof(f119,plain,(
% 1.77/0.62    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(X0,k2_tops_1(sK0,sK1)))) )),
% 1.77/0.62    inference(resolution,[],[f108,f89])).
% 1.77/0.62  fof(f89,plain,(
% 1.77/0.62    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.77/0.62    inference(definition_unfolding,[],[f78,f65])).
% 1.77/0.62  fof(f78,plain,(
% 1.77/0.62    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.77/0.62    inference(cnf_transformation,[],[f39])).
% 1.77/0.62  fof(f39,plain,(
% 1.77/0.62    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.77/0.62    inference(flattening,[],[f38])).
% 1.77/0.62  fof(f38,plain,(
% 1.77/0.62    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 1.77/0.62    inference(ennf_transformation,[],[f13])).
% 1.77/0.62  fof(f13,axiom,(
% 1.77/0.62    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 1.77/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 1.77/0.62  fof(f111,plain,(
% 1.77/0.62    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))),
% 1.77/0.62    inference(subsumption_resolution,[],[f103,f51])).
% 1.77/0.62  fof(f103,plain,(
% 1.77/0.62    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) | ~l1_pre_topc(sK0)),
% 1.77/0.62    inference(resolution,[],[f52,f59])).
% 1.77/0.62  fof(f59,plain,(
% 1.77/0.62    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~l1_pre_topc(X0)) )),
% 1.77/0.62    inference(cnf_transformation,[],[f28])).
% 1.77/0.62  fof(f28,plain,(
% 1.77/0.62    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.77/0.62    inference(ennf_transformation,[],[f19])).
% 1.77/0.62  fof(f19,axiom,(
% 1.77/0.62    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 1.77/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).
% 1.77/0.62  fof(f574,plain,(
% 1.77/0.62    spl3_11 | ~spl3_1),
% 1.77/0.62    inference(avatar_split_clause,[],[f569,f91,f571])).
% 1.77/0.62  fof(f91,plain,(
% 1.77/0.62    spl3_1 <=> v4_pre_topc(sK1,sK0)),
% 1.77/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.77/0.62  fof(f569,plain,(
% 1.77/0.62    ~v4_pre_topc(sK1,sK0) | r1_tarski(k2_tops_1(sK0,sK1),sK1)),
% 1.77/0.62    inference(subsumption_resolution,[],[f102,f51])).
% 1.77/0.62  fof(f102,plain,(
% 1.77/0.62    ~v4_pre_topc(sK1,sK0) | r1_tarski(k2_tops_1(sK0,sK1),sK1) | ~l1_pre_topc(sK0)),
% 1.77/0.62    inference(resolution,[],[f52,f60])).
% 1.77/0.62  fof(f60,plain,(
% 1.77/0.62    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | r1_tarski(k2_tops_1(X0,X1),X1) | ~l1_pre_topc(X0)) )),
% 1.77/0.62    inference(cnf_transformation,[],[f30])).
% 1.77/0.62  fof(f30,plain,(
% 1.77/0.62    ! [X0] : (! [X1] : (r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.77/0.62    inference(flattening,[],[f29])).
% 1.77/0.62  fof(f29,plain,(
% 1.77/0.62    ! [X0] : (! [X1] : ((r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.77/0.62    inference(ennf_transformation,[],[f21])).
% 1.77/0.62  fof(f21,axiom,(
% 1.77/0.62    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => r1_tarski(k2_tops_1(X0,X1),X1))))),
% 1.77/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_tops_1)).
% 1.77/0.62  fof(f556,plain,(
% 1.77/0.62    spl3_1 | ~spl3_2),
% 1.77/0.62    inference(avatar_contradiction_clause,[],[f555])).
% 1.77/0.62  fof(f555,plain,(
% 1.77/0.62    $false | (spl3_1 | ~spl3_2)),
% 1.77/0.62    inference(subsumption_resolution,[],[f542,f93])).
% 1.77/0.62  fof(f93,plain,(
% 1.77/0.62    ~v4_pre_topc(sK1,sK0) | spl3_1),
% 1.77/0.62    inference(avatar_component_clause,[],[f91])).
% 1.77/0.62  fof(f542,plain,(
% 1.77/0.62    v4_pre_topc(sK1,sK0) | ~spl3_2),
% 1.77/0.62    inference(backward_demodulation,[],[f110,f541])).
% 1.77/0.62  fof(f541,plain,(
% 1.77/0.62    sK1 = k2_pre_topc(sK0,sK1) | ~spl3_2),
% 1.77/0.62    inference(backward_demodulation,[],[f282,f540])).
% 1.77/0.62  fof(f540,plain,(
% 1.77/0.62    sK1 = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | ~spl3_2),
% 1.77/0.62    inference(forward_demodulation,[],[f538,f155])).
% 1.77/0.62  fof(f538,plain,(
% 1.77/0.62    k5_xboole_0(sK1,k1_xboole_0) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | ~spl3_2),
% 1.77/0.62    inference(superposition,[],[f274,f537])).
% 1.77/0.62  fof(f537,plain,(
% 1.77/0.62    k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),sK1) | ~spl3_2),
% 1.77/0.62    inference(forward_demodulation,[],[f531,f455])).
% 1.77/0.62  fof(f531,plain,(
% 1.77/0.62    k5_xboole_0(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) = k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),sK1) | ~spl3_2),
% 1.77/0.62    inference(superposition,[],[f267,f166])).
% 1.77/0.62  fof(f166,plain,(
% 1.77/0.62    k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | ~spl3_2),
% 1.77/0.62    inference(forward_demodulation,[],[f165,f64])).
% 1.77/0.62  fof(f165,plain,(
% 1.77/0.62    k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),sK1)) | ~spl3_2),
% 1.77/0.62    inference(resolution,[],[f157,f87])).
% 1.77/0.62  fof(f157,plain,(
% 1.77/0.62    r1_tarski(k2_tops_1(sK0,sK1),sK1) | ~spl3_2),
% 1.77/0.62    inference(superposition,[],[f153,f96])).
% 1.77/0.62  fof(f96,plain,(
% 1.77/0.62    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~spl3_2),
% 1.77/0.62    inference(avatar_component_clause,[],[f95])).
% 1.77/0.62  fof(f153,plain,(
% 1.77/0.62    ( ! [X1] : (r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,X1),sK1)) )),
% 1.77/0.62    inference(superposition,[],[f84,f106])).
% 1.77/0.62  fof(f84,plain,(
% 1.77/0.62    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0)) )),
% 1.77/0.62    inference(definition_unfolding,[],[f62,f79])).
% 1.77/0.62  fof(f62,plain,(
% 1.77/0.62    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.77/0.62    inference(cnf_transformation,[],[f7])).
% 1.77/0.62  fof(f7,axiom,(
% 1.77/0.62    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.77/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.77/0.62  fof(f110,plain,(
% 1.77/0.62    v4_pre_topc(k2_pre_topc(sK0,sK1),sK0)),
% 1.77/0.62    inference(subsumption_resolution,[],[f109,f50])).
% 1.77/0.62  fof(f50,plain,(
% 1.77/0.62    v2_pre_topc(sK0)),
% 1.77/0.62    inference(cnf_transformation,[],[f44])).
% 1.77/0.62  fof(f109,plain,(
% 1.77/0.62    v4_pre_topc(k2_pre_topc(sK0,sK1),sK0) | ~v2_pre_topc(sK0)),
% 1.77/0.62    inference(subsumption_resolution,[],[f101,f51])).
% 1.77/0.62  fof(f101,plain,(
% 1.77/0.62    v4_pre_topc(k2_pre_topc(sK0,sK1),sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 1.77/0.62    inference(resolution,[],[f52,f70])).
% 1.77/0.62  fof(f70,plain,(
% 1.77/0.62    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.77/0.62    inference(cnf_transformation,[],[f33])).
% 1.77/0.62  fof(f33,plain,(
% 1.77/0.62    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.77/0.62    inference(flattening,[],[f32])).
% 1.77/0.62  fof(f32,plain,(
% 1.77/0.62    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.77/0.62    inference(ennf_transformation,[],[f18])).
% 1.77/0.62  fof(f18,axiom,(
% 1.77/0.62    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_pre_topc(X0,X1),X0))),
% 1.77/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tops_1)).
% 1.77/0.62  fof(f99,plain,(
% 1.77/0.62    spl3_1 | spl3_2),
% 1.77/0.62    inference(avatar_split_clause,[],[f53,f95,f91])).
% 1.77/0.62  fof(f53,plain,(
% 1.77/0.62    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)),
% 1.77/0.62    inference(cnf_transformation,[],[f44])).
% 1.77/0.62  fof(f98,plain,(
% 1.77/0.62    ~spl3_1 | ~spl3_2),
% 1.77/0.62    inference(avatar_split_clause,[],[f54,f95,f91])).
% 1.77/0.62  fof(f54,plain,(
% 1.77/0.62    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)),
% 1.77/0.62    inference(cnf_transformation,[],[f44])).
% 1.77/0.62  % SZS output end Proof for theBenchmark
% 1.77/0.62  % (16607)------------------------------
% 1.77/0.62  % (16607)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.77/0.62  % (16607)Termination reason: Refutation
% 1.77/0.62  
% 1.77/0.62  % (16607)Memory used [KB]: 11129
% 1.77/0.62  % (16607)Time elapsed: 0.204 s
% 1.77/0.62  % (16607)------------------------------
% 1.77/0.62  % (16607)------------------------------
% 1.77/0.62  % (16598)Success in time 0.251 s
%------------------------------------------------------------------------------
