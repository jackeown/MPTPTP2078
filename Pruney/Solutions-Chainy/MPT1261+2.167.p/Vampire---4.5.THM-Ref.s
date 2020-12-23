%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:12:14 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  137 (6727 expanded)
%              Number of leaves         :   19 (2022 expanded)
%              Depth                    :   29
%              Number of atoms          :  289 (20176 expanded)
%              Number of equality atoms :  118 (7728 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1663,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1662,f1646])).

fof(f1646,plain,(
    ~ v4_pre_topc(sK1,sK0) ),
    inference(trivial_inequality_removal,[],[f1628])).

fof(f1628,plain,
    ( k2_tops_1(sK0,sK1) != k2_tops_1(sK0,sK1)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(backward_demodulation,[],[f1331,f1624])).

fof(f1624,plain,(
    k2_tops_1(sK0,sK1) = k5_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
    inference(duplicate_literal_removal,[],[f1621])).

fof(f1621,plain,
    ( k2_tops_1(sK0,sK1) = k5_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | k2_tops_1(sK0,sK1) = k5_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
    inference(superposition,[],[f1595,f1327])).

fof(f1327,plain,(
    k3_subset_1(sK1,k1_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
    inference(backward_demodulation,[],[f1313,f1316])).

fof(f1316,plain,(
    k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k5_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
    inference(superposition,[],[f633,f1309])).

fof(f1309,plain,(
    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f1279,f41])).

fof(f41,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,
    ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | ~ v4_pre_topc(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | v4_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f35,f37,f36])).

fof(f36,plain,
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

fof(f37,plain,
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

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).

fof(f1279,plain,
    ( k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f46,f42])).

fof(f42,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f38])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).

fof(f633,plain,(
    ! [X3] : k1_setfam_1(k2_tarski(sK1,X3)) = k5_xboole_0(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X3)) ),
    inference(backward_demodulation,[],[f458,f632])).

fof(f632,plain,(
    ! [X4] : k7_subset_1(u1_struct_0(sK0),sK1,X4) = k1_setfam_1(k2_tarski(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X4))) ),
    inference(forward_demodulation,[],[f631,f629])).

fof(f629,plain,(
    ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(u1_struct_0(sK0),sK1,k1_setfam_1(k2_tarski(sK1,X0))) ),
    inference(backward_demodulation,[],[f378,f622])).

fof(f622,plain,(
    ! [X2] : k3_subset_1(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X2)) = k1_setfam_1(k2_tarski(sK1,X2)) ),
    inference(backward_demodulation,[],[f351,f458])).

fof(f351,plain,(
    ! [X2] : k3_subset_1(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X2)) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X2)))) ),
    inference(resolution,[],[f347,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ) ),
    inference(definition_unfolding,[],[f54,f62])).

fof(f62,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f53,f50])).

fof(f50,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f53,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f54,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f347,plain,(
    ! [X0] : m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,X0),k1_zfmisc_1(sK1)) ),
    inference(superposition,[],[f72,f346])).

fof(f346,plain,(
    ! [X24] : k7_subset_1(u1_struct_0(sK0),sK1,X24) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X24))) ),
    inference(resolution,[],[f67,f42])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) ) ),
    inference(definition_unfolding,[],[f60,f62])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f72,plain,(
    ! [X0,X1] : m1_subset_1(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),k1_zfmisc_1(X0)) ),
    inference(resolution,[],[f63,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f63,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0) ),
    inference(definition_unfolding,[],[f48,f62])).

fof(f48,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f378,plain,(
    ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X0))) ),
    inference(forward_demodulation,[],[f371,f352])).

fof(f352,plain,(
    ! [X3] : k7_subset_1(u1_struct_0(sK0),sK1,X3) = k3_subset_1(sK1,k3_subset_1(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X3))) ),
    inference(resolution,[],[f347,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f371,plain,(
    ! [X0] : k3_subset_1(sK1,k3_subset_1(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X0))) = k7_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X0))) ),
    inference(superposition,[],[f361,f361])).

fof(f361,plain,(
    ! [X1] : k7_subset_1(u1_struct_0(sK0),sK1,k7_subset_1(u1_struct_0(sK0),sK1,X1)) = k3_subset_1(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X1)) ),
    inference(superposition,[],[f351,f346])).

fof(f631,plain,(
    ! [X4] : k1_setfam_1(k2_tarski(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X4))) = k7_subset_1(u1_struct_0(sK0),sK1,k1_setfam_1(k2_tarski(sK1,X4))) ),
    inference(forward_demodulation,[],[f630,f346])).

fof(f630,plain,(
    ! [X4] : k1_setfam_1(k2_tarski(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X4))) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k1_setfam_1(k2_tarski(sK1,X4))))) ),
    inference(forward_demodulation,[],[f459,f622])).

fof(f459,plain,(
    ! [X4] : k1_setfam_1(k2_tarski(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X4))) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k3_subset_1(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X4))))) ),
    inference(superposition,[],[f65,f351])).

fof(f65,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))))) ),
    inference(definition_unfolding,[],[f52,f50,f62,f62])).

fof(f52,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f458,plain,(
    ! [X3] : k1_setfam_1(k2_tarski(sK1,X3)) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X3)))) ),
    inference(superposition,[],[f65,f346])).

fof(f1313,plain,(
    k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k3_subset_1(sK1,k1_tops_1(sK0,sK1)) ),
    inference(superposition,[],[f622,f1309])).

fof(f1595,plain,
    ( k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k1_tops_1(sK0,sK1))
    | k2_tops_1(sK0,sK1) = k5_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
    inference(superposition,[],[f1188,f1455])).

fof(f1455,plain,
    ( k1_tops_1(sK0,sK1) = k3_subset_1(sK1,k2_tops_1(sK0,sK1))
    | k2_tops_1(sK0,sK1) = k5_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f1454,f1349])).

fof(f1349,plain,(
    k1_tops_1(sK0,sK1) = k5_xboole_0(sK1,k5_xboole_0(sK1,k1_tops_1(sK0,sK1))) ),
    inference(superposition,[],[f750,f1315])).

fof(f1315,plain,(
    k1_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1))) ),
    inference(superposition,[],[f632,f1309])).

fof(f750,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) ),
    inference(backward_demodulation,[],[f467,f749])).

fof(f749,plain,(
    ! [X4,X3] : k5_xboole_0(X3,k1_setfam_1(k2_tarski(X3,k1_setfam_1(k2_tarski(X3,X4))))) = k5_xboole_0(X3,k1_setfam_1(k2_tarski(X3,X4))) ),
    inference(forward_demodulation,[],[f739,f130])).

fof(f130,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k3_subset_1(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(backward_demodulation,[],[f75,f129])).

fof(f129,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_subset_1(X0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) ),
    inference(forward_demodulation,[],[f123,f65])).

fof(f123,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))))) = k3_subset_1(X0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) ),
    inference(resolution,[],[f66,f72])).

fof(f75,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k3_subset_1(X0,k3_subset_1(X0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))))) ),
    inference(resolution,[],[f55,f72])).

fof(f739,plain,(
    ! [X4,X3] : k3_subset_1(X3,k1_setfam_1(k2_tarski(X3,X4))) = k5_xboole_0(X3,k1_setfam_1(k2_tarski(X3,k1_setfam_1(k2_tarski(X3,X4))))) ),
    inference(resolution,[],[f463,f66])).

fof(f463,plain,(
    ! [X0,X1] : m1_subset_1(k1_setfam_1(k2_tarski(X0,X1)),k1_zfmisc_1(X0)) ),
    inference(superposition,[],[f72,f65])).

fof(f467,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_setfam_1(k2_tarski(X0,X1)))))) ),
    inference(backward_demodulation,[],[f65,f451])).

fof(f451,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))))) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_setfam_1(k2_tarski(X0,X1))))) ),
    inference(superposition,[],[f65,f65])).

fof(f1454,plain,
    ( k3_subset_1(sK1,k2_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k5_xboole_0(sK1,k1_tops_1(sK0,sK1)))
    | k2_tops_1(sK0,sK1) = k5_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f1451,f1316])).

fof(f1451,plain,
    ( k2_tops_1(sK0,sK1) = k5_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | k3_subset_1(sK1,k2_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1)))) ),
    inference(resolution,[],[f1333,f66])).

fof(f1333,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | k2_tops_1(sK0,sK1) = k5_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
    inference(backward_demodulation,[],[f1323,f1327])).

fof(f1323,plain,
    ( k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k1_tops_1(sK0,sK1))
    | m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) ),
    inference(backward_demodulation,[],[f242,f1319])).

fof(f1319,plain,(
    k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k3_subset_1(sK1,k1_tops_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f1314,f1313])).

fof(f1314,plain,(
    k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) ),
    inference(superposition,[],[f624,f1309])).

fof(f624,plain,(
    ! [X1] : k1_setfam_1(k2_tarski(sK1,X1)) = k7_subset_1(u1_struct_0(sK0),sK1,k7_subset_1(u1_struct_0(sK0),sK1,X1)) ),
    inference(backward_demodulation,[],[f361,f622])).

fof(f242,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) ),
    inference(resolution,[],[f241,f59])).

fof(f241,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) ),
    inference(resolution,[],[f240,f43])).

fof(f43,plain,
    ( v4_pre_topc(sK1,sK0)
    | k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f38])).

fof(f240,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | r1_tarski(k2_tops_1(sK0,sK1),sK1) ),
    inference(subsumption_resolution,[],[f226,f41])).

fof(f226,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f47,f42])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | r1_tarski(k2_tops_1(X0,X1),X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => r1_tarski(k2_tops_1(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_tops_1)).

fof(f1188,plain,(
    k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k3_subset_1(sK1,k2_tops_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f1181,f55])).

fof(f1181,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k3_subset_1(sK1,k2_tops_1(sK0,sK1))) ),
    inference(superposition,[],[f347,f255])).

fof(f255,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k3_subset_1(sK1,k2_tops_1(sK0,sK1))) ),
    inference(resolution,[],[f242,f55])).

fof(f1331,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | k2_tops_1(sK0,sK1) != k5_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
    inference(backward_demodulation,[],[f1321,f1327])).

fof(f1321,plain,
    ( k2_tops_1(sK0,sK1) != k3_subset_1(sK1,k1_tops_1(sK0,sK1))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(backward_demodulation,[],[f44,f1319])).

fof(f44,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f38])).

fof(f1662,plain,(
    v4_pre_topc(sK1,sK0) ),
    inference(backward_demodulation,[],[f79,f1660])).

fof(f1660,plain,(
    sK1 = k2_pre_topc(sK0,sK1) ),
    inference(backward_demodulation,[],[f1142,f1637])).

fof(f1637,plain,(
    sK1 = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) ),
    inference(backward_demodulation,[],[f1376,f1624])).

fof(f1376,plain,(
    sK1 = k3_tarski(k2_tarski(sK1,k5_xboole_0(sK1,k1_tops_1(sK0,sK1)))) ),
    inference(superposition,[],[f64,f1316])).

fof(f64,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,k1_setfam_1(k2_tarski(X0,X1)))) = X0 ),
    inference(definition_unfolding,[],[f49,f51,f50])).

fof(f51,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f49,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f1142,plain,(
    k2_pre_topc(sK0,sK1) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) ),
    inference(backward_demodulation,[],[f992,f1141])).

fof(f1141,plain,(
    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f1115,f41])).

fof(f1115,plain,
    ( k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f45,f42])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

fof(f992,plain,(
    k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) ),
    inference(resolution,[],[f917,f42])).

fof(f917,plain,(
    ! [X13] :
      ( ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(sK0)))
      | k4_subset_1(u1_struct_0(sK0),X13,k2_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(X13,k2_tops_1(sK0,sK1))) ) ),
    inference(resolution,[],[f68,f82])).

fof(f82,plain,(
    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f80,f41])).

fof(f80,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f57,f42])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f61,f51])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
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

fof(f79,plain,(
    v4_pre_topc(k2_pre_topc(sK0,sK1),sK0) ),
    inference(subsumption_resolution,[],[f78,f40])).

fof(f40,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f78,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,sK1),sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f76,f41])).

fof(f76,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f56,f42])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_pre_topc(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_tops_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:48:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.44  % (10072)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.46  % (10071)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.47  % (10067)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.47  % (10059)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.47  % (10073)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.47  % (10064)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.48  % (10062)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.48  % (10063)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.48  % (10076)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.48  % (10061)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.48  % (10070)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.49  % (10065)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.49  % (10068)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.49  % (10074)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.49  % (10069)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.49  % (10072)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f1663,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(subsumption_resolution,[],[f1662,f1646])).
% 0.22/0.49  fof(f1646,plain,(
% 0.22/0.49    ~v4_pre_topc(sK1,sK0)),
% 0.22/0.49    inference(trivial_inequality_removal,[],[f1628])).
% 0.22/0.49  fof(f1628,plain,(
% 0.22/0.49    k2_tops_1(sK0,sK1) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0)),
% 0.22/0.49    inference(backward_demodulation,[],[f1331,f1624])).
% 0.22/0.49  fof(f1624,plain,(
% 0.22/0.49    k2_tops_1(sK0,sK1) = k5_xboole_0(sK1,k1_tops_1(sK0,sK1))),
% 0.22/0.49    inference(duplicate_literal_removal,[],[f1621])).
% 0.22/0.49  fof(f1621,plain,(
% 0.22/0.49    k2_tops_1(sK0,sK1) = k5_xboole_0(sK1,k1_tops_1(sK0,sK1)) | k2_tops_1(sK0,sK1) = k5_xboole_0(sK1,k1_tops_1(sK0,sK1))),
% 0.22/0.49    inference(superposition,[],[f1595,f1327])).
% 0.22/0.49  fof(f1327,plain,(
% 0.22/0.49    k3_subset_1(sK1,k1_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k1_tops_1(sK0,sK1))),
% 0.22/0.49    inference(backward_demodulation,[],[f1313,f1316])).
% 0.22/0.49  fof(f1316,plain,(
% 0.22/0.49    k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k5_xboole_0(sK1,k1_tops_1(sK0,sK1))),
% 0.22/0.49    inference(superposition,[],[f633,f1309])).
% 0.22/0.49  fof(f1309,plain,(
% 0.22/0.49    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 0.22/0.49    inference(subsumption_resolution,[],[f1279,f41])).
% 0.22/0.49  fof(f41,plain,(
% 0.22/0.49    l1_pre_topc(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f38])).
% 0.22/0.49  fof(f38,plain,(
% 0.22/0.49    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f35,f37,f36])).
% 0.22/0.49  fof(f36,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f37,plain,(
% 0.22/0.49    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f35,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.22/0.49    inference(flattening,[],[f34])).
% 0.22/0.49  fof(f34,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.22/0.49    inference(nnf_transformation,[],[f20])).
% 0.22/0.49  fof(f20,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.22/0.49    inference(flattening,[],[f19])).
% 0.22/0.49  fof(f19,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f18])).
% 0.22/0.49  fof(f18,negated_conjecture,(
% 0.22/0.49    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 0.22/0.49    inference(negated_conjecture,[],[f17])).
% 0.22/0.49  fof(f17,conjecture,(
% 0.22/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).
% 0.22/0.49  fof(f1279,plain,(
% 0.22/0.49    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | ~l1_pre_topc(sK0)),
% 0.22/0.49    inference(resolution,[],[f46,f42])).
% 0.22/0.49  fof(f42,plain,(
% 0.22/0.49    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.49    inference(cnf_transformation,[],[f38])).
% 0.22/0.49  fof(f46,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~l1_pre_topc(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f22])).
% 0.22/0.49  fof(f22,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f16])).
% 0.22/0.49  fof(f16,axiom,(
% 0.22/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).
% 0.22/0.49  fof(f633,plain,(
% 0.22/0.49    ( ! [X3] : (k1_setfam_1(k2_tarski(sK1,X3)) = k5_xboole_0(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X3))) )),
% 0.22/0.49    inference(backward_demodulation,[],[f458,f632])).
% 0.22/0.49  fof(f632,plain,(
% 0.22/0.49    ( ! [X4] : (k7_subset_1(u1_struct_0(sK0),sK1,X4) = k1_setfam_1(k2_tarski(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X4)))) )),
% 0.22/0.49    inference(forward_demodulation,[],[f631,f629])).
% 0.22/0.49  fof(f629,plain,(
% 0.22/0.49    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(u1_struct_0(sK0),sK1,k1_setfam_1(k2_tarski(sK1,X0)))) )),
% 0.22/0.49    inference(backward_demodulation,[],[f378,f622])).
% 0.22/0.49  fof(f622,plain,(
% 0.22/0.49    ( ! [X2] : (k3_subset_1(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X2)) = k1_setfam_1(k2_tarski(sK1,X2))) )),
% 0.22/0.49    inference(backward_demodulation,[],[f351,f458])).
% 0.22/0.49  fof(f351,plain,(
% 0.22/0.49    ( ! [X2] : (k3_subset_1(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X2)) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X2))))) )),
% 0.22/0.49    inference(resolution,[],[f347,f66])).
% 0.22/0.49  fof(f66,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 0.22/0.49    inference(definition_unfolding,[],[f54,f62])).
% 0.22/0.49  fof(f62,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 0.22/0.49    inference(definition_unfolding,[],[f53,f50])).
% 0.22/0.49  fof(f50,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f10])).
% 0.22/0.49  fof(f10,axiom,(
% 0.22/0.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.22/0.49  fof(f53,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f1])).
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.22/0.49  fof(f54,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f25])).
% 0.22/0.49  fof(f25,plain,(
% 0.22/0.49    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f6])).
% 0.22/0.49  fof(f6,axiom,(
% 0.22/0.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 0.22/0.49  fof(f347,plain,(
% 0.22/0.49    ( ! [X0] : (m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,X0),k1_zfmisc_1(sK1))) )),
% 0.22/0.49    inference(superposition,[],[f72,f346])).
% 0.22/0.49  fof(f346,plain,(
% 0.22/0.49    ( ! [X24] : (k7_subset_1(u1_struct_0(sK0),sK1,X24) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X24)))) )),
% 0.22/0.49    inference(resolution,[],[f67,f42])).
% 0.22/0.49  fof(f67,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))) )),
% 0.22/0.49    inference(definition_unfolding,[],[f60,f62])).
% 0.22/0.49  fof(f60,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f31])).
% 0.22/0.49  fof(f31,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f9])).
% 0.22/0.49  fof(f9,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 0.22/0.49  fof(f72,plain,(
% 0.22/0.49    ( ! [X0,X1] : (m1_subset_1(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),k1_zfmisc_1(X0))) )),
% 0.22/0.49    inference(resolution,[],[f63,f59])).
% 0.22/0.49  fof(f59,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f39])).
% 0.22/0.49  fof(f39,plain,(
% 0.22/0.49    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.22/0.49    inference(nnf_transformation,[],[f11])).
% 0.22/0.49  fof(f11,axiom,(
% 0.22/0.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.49  fof(f63,plain,(
% 0.22/0.49    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0)) )),
% 0.22/0.49    inference(definition_unfolding,[],[f48,f62])).
% 0.22/0.49  fof(f48,plain,(
% 0.22/0.49    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f3])).
% 0.22/0.49  fof(f3,axiom,(
% 0.22/0.49    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.22/0.49  fof(f378,plain,(
% 0.22/0.49    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X0)))) )),
% 0.22/0.49    inference(forward_demodulation,[],[f371,f352])).
% 0.22/0.49  fof(f352,plain,(
% 0.22/0.49    ( ! [X3] : (k7_subset_1(u1_struct_0(sK0),sK1,X3) = k3_subset_1(sK1,k3_subset_1(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X3)))) )),
% 0.22/0.49    inference(resolution,[],[f347,f55])).
% 0.22/0.49  fof(f55,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 0.22/0.49    inference(cnf_transformation,[],[f26])).
% 0.22/0.49  fof(f26,plain,(
% 0.22/0.49    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f7])).
% 0.22/0.49  fof(f7,axiom,(
% 0.22/0.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 0.22/0.49  fof(f371,plain,(
% 0.22/0.49    ( ! [X0] : (k3_subset_1(sK1,k3_subset_1(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X0))) = k7_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X0)))) )),
% 0.22/0.49    inference(superposition,[],[f361,f361])).
% 0.22/0.49  fof(f361,plain,(
% 0.22/0.49    ( ! [X1] : (k7_subset_1(u1_struct_0(sK0),sK1,k7_subset_1(u1_struct_0(sK0),sK1,X1)) = k3_subset_1(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X1))) )),
% 0.22/0.49    inference(superposition,[],[f351,f346])).
% 0.22/0.49  fof(f631,plain,(
% 0.22/0.49    ( ! [X4] : (k1_setfam_1(k2_tarski(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X4))) = k7_subset_1(u1_struct_0(sK0),sK1,k1_setfam_1(k2_tarski(sK1,X4)))) )),
% 0.22/0.49    inference(forward_demodulation,[],[f630,f346])).
% 0.22/0.49  fof(f630,plain,(
% 0.22/0.49    ( ! [X4] : (k1_setfam_1(k2_tarski(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X4))) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k1_setfam_1(k2_tarski(sK1,X4)))))) )),
% 0.22/0.49    inference(forward_demodulation,[],[f459,f622])).
% 0.22/0.49  fof(f459,plain,(
% 0.22/0.49    ( ! [X4] : (k1_setfam_1(k2_tarski(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X4))) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k3_subset_1(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X4)))))) )),
% 0.22/0.49    inference(superposition,[],[f65,f351])).
% 0.22/0.49  fof(f65,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))))))) )),
% 0.22/0.49    inference(definition_unfolding,[],[f52,f50,f62,f62])).
% 0.22/0.49  fof(f52,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f4])).
% 0.22/0.49  fof(f4,axiom,(
% 0.22/0.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.22/0.49  fof(f458,plain,(
% 0.22/0.49    ( ! [X3] : (k1_setfam_1(k2_tarski(sK1,X3)) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X3))))) )),
% 0.22/0.49    inference(superposition,[],[f65,f346])).
% 0.22/0.49  fof(f1313,plain,(
% 0.22/0.49    k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k3_subset_1(sK1,k1_tops_1(sK0,sK1))),
% 0.22/0.49    inference(superposition,[],[f622,f1309])).
% 0.22/0.49  fof(f1595,plain,(
% 0.22/0.49    k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k1_tops_1(sK0,sK1)) | k2_tops_1(sK0,sK1) = k5_xboole_0(sK1,k1_tops_1(sK0,sK1))),
% 0.22/0.49    inference(superposition,[],[f1188,f1455])).
% 0.22/0.49  fof(f1455,plain,(
% 0.22/0.49    k1_tops_1(sK0,sK1) = k3_subset_1(sK1,k2_tops_1(sK0,sK1)) | k2_tops_1(sK0,sK1) = k5_xboole_0(sK1,k1_tops_1(sK0,sK1))),
% 0.22/0.49    inference(forward_demodulation,[],[f1454,f1349])).
% 0.22/0.49  fof(f1349,plain,(
% 0.22/0.49    k1_tops_1(sK0,sK1) = k5_xboole_0(sK1,k5_xboole_0(sK1,k1_tops_1(sK0,sK1)))),
% 0.22/0.49    inference(superposition,[],[f750,f1315])).
% 0.22/0.49  fof(f1315,plain,(
% 0.22/0.49    k1_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1)))),
% 0.22/0.49    inference(superposition,[],[f632,f1309])).
% 0.22/0.49  fof(f750,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))))) )),
% 0.22/0.49    inference(backward_demodulation,[],[f467,f749])).
% 0.22/0.49  fof(f749,plain,(
% 0.22/0.49    ( ! [X4,X3] : (k5_xboole_0(X3,k1_setfam_1(k2_tarski(X3,k1_setfam_1(k2_tarski(X3,X4))))) = k5_xboole_0(X3,k1_setfam_1(k2_tarski(X3,X4)))) )),
% 0.22/0.49    inference(forward_demodulation,[],[f739,f130])).
% 0.22/0.49  fof(f130,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k3_subset_1(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 0.22/0.49    inference(backward_demodulation,[],[f75,f129])).
% 0.22/0.49  fof(f129,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_subset_1(X0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))))) )),
% 0.22/0.49    inference(forward_demodulation,[],[f123,f65])).
% 0.22/0.49  fof(f123,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))))) = k3_subset_1(X0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))))) )),
% 0.22/0.49    inference(resolution,[],[f66,f72])).
% 0.22/0.49  fof(f75,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k3_subset_1(X0,k3_subset_1(X0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))))) )),
% 0.22/0.49    inference(resolution,[],[f55,f72])).
% 0.22/0.49  fof(f739,plain,(
% 0.22/0.49    ( ! [X4,X3] : (k3_subset_1(X3,k1_setfam_1(k2_tarski(X3,X4))) = k5_xboole_0(X3,k1_setfam_1(k2_tarski(X3,k1_setfam_1(k2_tarski(X3,X4)))))) )),
% 0.22/0.49    inference(resolution,[],[f463,f66])).
% 0.22/0.49  fof(f463,plain,(
% 0.22/0.49    ( ! [X0,X1] : (m1_subset_1(k1_setfam_1(k2_tarski(X0,X1)),k1_zfmisc_1(X0))) )),
% 0.22/0.49    inference(superposition,[],[f72,f65])).
% 0.22/0.49  fof(f467,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_setfam_1(k2_tarski(X0,X1))))))) )),
% 0.22/0.49    inference(backward_demodulation,[],[f65,f451])).
% 0.22/0.49  fof(f451,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))))) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_setfam_1(k2_tarski(X0,X1)))))) )),
% 0.22/0.49    inference(superposition,[],[f65,f65])).
% 0.22/0.49  fof(f1454,plain,(
% 0.22/0.49    k3_subset_1(sK1,k2_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k5_xboole_0(sK1,k1_tops_1(sK0,sK1))) | k2_tops_1(sK0,sK1) = k5_xboole_0(sK1,k1_tops_1(sK0,sK1))),
% 0.22/0.49    inference(forward_demodulation,[],[f1451,f1316])).
% 0.22/0.49  fof(f1451,plain,(
% 0.22/0.49    k2_tops_1(sK0,sK1) = k5_xboole_0(sK1,k1_tops_1(sK0,sK1)) | k3_subset_1(sK1,k2_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))))),
% 0.22/0.49    inference(resolution,[],[f1333,f66])).
% 0.22/0.49  fof(f1333,plain,(
% 0.22/0.49    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | k2_tops_1(sK0,sK1) = k5_xboole_0(sK1,k1_tops_1(sK0,sK1))),
% 0.22/0.49    inference(backward_demodulation,[],[f1323,f1327])).
% 0.22/0.49  fof(f1323,plain,(
% 0.22/0.49    k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k1_tops_1(sK0,sK1)) | m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1))),
% 0.22/0.49    inference(backward_demodulation,[],[f242,f1319])).
% 0.22/0.49  fof(f1319,plain,(
% 0.22/0.49    k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k3_subset_1(sK1,k1_tops_1(sK0,sK1))),
% 0.22/0.49    inference(forward_demodulation,[],[f1314,f1313])).
% 0.22/0.49  fof(f1314,plain,(
% 0.22/0.49    k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1)))),
% 0.22/0.49    inference(superposition,[],[f624,f1309])).
% 0.22/0.49  fof(f624,plain,(
% 0.22/0.49    ( ! [X1] : (k1_setfam_1(k2_tarski(sK1,X1)) = k7_subset_1(u1_struct_0(sK0),sK1,k7_subset_1(u1_struct_0(sK0),sK1,X1))) )),
% 0.22/0.49    inference(backward_demodulation,[],[f361,f622])).
% 0.22/0.49  fof(f242,plain,(
% 0.22/0.49    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),
% 0.22/0.49    inference(resolution,[],[f241,f59])).
% 0.22/0.49  fof(f241,plain,(
% 0.22/0.49    r1_tarski(k2_tops_1(sK0,sK1),sK1) | k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),
% 0.22/0.49    inference(resolution,[],[f240,f43])).
% 0.22/0.49  fof(f43,plain,(
% 0.22/0.49    v4_pre_topc(sK1,sK0) | k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),
% 0.22/0.49    inference(cnf_transformation,[],[f38])).
% 0.22/0.49  fof(f240,plain,(
% 0.22/0.49    ~v4_pre_topc(sK1,sK0) | r1_tarski(k2_tops_1(sK0,sK1),sK1)),
% 0.22/0.49    inference(subsumption_resolution,[],[f226,f41])).
% 0.22/0.49  fof(f226,plain,(
% 0.22/0.49    ~v4_pre_topc(sK1,sK0) | r1_tarski(k2_tops_1(sK0,sK1),sK1) | ~l1_pre_topc(sK0)),
% 0.22/0.49    inference(resolution,[],[f47,f42])).
% 0.22/0.49  fof(f47,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | r1_tarski(k2_tops_1(X0,X1),X1) | ~l1_pre_topc(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f24])).
% 0.22/0.49  fof(f24,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.49    inference(flattening,[],[f23])).
% 0.22/0.49  fof(f23,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : ((r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f15])).
% 0.22/0.49  fof(f15,axiom,(
% 0.22/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => r1_tarski(k2_tops_1(X0,X1),X1))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_tops_1)).
% 0.22/0.49  fof(f1188,plain,(
% 0.22/0.49    k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k3_subset_1(sK1,k2_tops_1(sK0,sK1)))),
% 0.22/0.49    inference(subsumption_resolution,[],[f1181,f55])).
% 0.22/0.49  fof(f1181,plain,(
% 0.22/0.49    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k3_subset_1(sK1,k2_tops_1(sK0,sK1)))),
% 0.22/0.49    inference(superposition,[],[f347,f255])).
% 0.22/0.49  fof(f255,plain,(
% 0.22/0.49    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k3_subset_1(sK1,k2_tops_1(sK0,sK1)))),
% 0.22/0.49    inference(resolution,[],[f242,f55])).
% 0.22/0.49  fof(f1331,plain,(
% 0.22/0.49    ~v4_pre_topc(sK1,sK0) | k2_tops_1(sK0,sK1) != k5_xboole_0(sK1,k1_tops_1(sK0,sK1))),
% 0.22/0.49    inference(backward_demodulation,[],[f1321,f1327])).
% 0.22/0.49  fof(f1321,plain,(
% 0.22/0.49    k2_tops_1(sK0,sK1) != k3_subset_1(sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)),
% 0.22/0.49    inference(backward_demodulation,[],[f44,f1319])).
% 0.22/0.49  fof(f44,plain,(
% 0.22/0.49    ~v4_pre_topc(sK1,sK0) | k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),
% 0.22/0.49    inference(cnf_transformation,[],[f38])).
% 0.22/0.49  fof(f1662,plain,(
% 0.22/0.49    v4_pre_topc(sK1,sK0)),
% 0.22/0.49    inference(backward_demodulation,[],[f79,f1660])).
% 0.22/0.49  fof(f1660,plain,(
% 0.22/0.49    sK1 = k2_pre_topc(sK0,sK1)),
% 0.22/0.49    inference(backward_demodulation,[],[f1142,f1637])).
% 0.22/0.49  fof(f1637,plain,(
% 0.22/0.49    sK1 = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))),
% 0.22/0.49    inference(backward_demodulation,[],[f1376,f1624])).
% 0.22/0.49  fof(f1376,plain,(
% 0.22/0.49    sK1 = k3_tarski(k2_tarski(sK1,k5_xboole_0(sK1,k1_tops_1(sK0,sK1))))),
% 0.22/0.49    inference(superposition,[],[f64,f1316])).
% 0.22/0.49  fof(f64,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,k1_setfam_1(k2_tarski(X0,X1)))) = X0) )),
% 0.22/0.49    inference(definition_unfolding,[],[f49,f51,f50])).
% 0.22/0.49  fof(f51,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f5])).
% 0.22/0.49  fof(f5,axiom,(
% 0.22/0.49    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.22/0.49  fof(f49,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 0.22/0.49    inference(cnf_transformation,[],[f2])).
% 0.22/0.49  fof(f2,axiom,(
% 0.22/0.49    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).
% 0.22/0.49  fof(f1142,plain,(
% 0.22/0.49    k2_pre_topc(sK0,sK1) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))),
% 0.22/0.49    inference(backward_demodulation,[],[f992,f1141])).
% 0.22/0.49  fof(f1141,plain,(
% 0.22/0.49    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 0.22/0.49    inference(subsumption_resolution,[],[f1115,f41])).
% 0.22/0.49  fof(f1115,plain,(
% 0.22/0.49    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | ~l1_pre_topc(sK0)),
% 0.22/0.49    inference(resolution,[],[f45,f42])).
% 0.22/0.49  fof(f45,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~l1_pre_topc(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f21])).
% 0.22/0.49  fof(f21,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f14])).
% 0.22/0.49  fof(f14,axiom,(
% 0.22/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).
% 0.22/0.49  fof(f992,plain,(
% 0.22/0.49    k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))),
% 0.22/0.49    inference(resolution,[],[f917,f42])).
% 0.22/0.49  fof(f917,plain,(
% 0.22/0.49    ( ! [X13] : (~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(sK0))) | k4_subset_1(u1_struct_0(sK0),X13,k2_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(X13,k2_tops_1(sK0,sK1)))) )),
% 0.22/0.49    inference(resolution,[],[f68,f82])).
% 0.22/0.49  fof(f82,plain,(
% 0.22/0.49    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.49    inference(subsumption_resolution,[],[f80,f41])).
% 0.22/0.49  fof(f80,plain,(
% 0.22/0.49    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 0.22/0.49    inference(resolution,[],[f57,f42])).
% 0.22/0.49  fof(f57,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f30])).
% 0.22/0.49  fof(f30,plain,(
% 0.22/0.49    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.22/0.49    inference(flattening,[],[f29])).
% 0.22/0.49  fof(f29,plain,(
% 0.22/0.49    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f12])).
% 0.22/0.49  fof(f12,axiom,(
% 0.22/0.49    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).
% 0.22/0.49  fof(f68,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.49    inference(definition_unfolding,[],[f61,f51])).
% 0.22/0.49  fof(f61,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f33])).
% 0.22/0.49  fof(f33,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.49    inference(flattening,[],[f32])).
% 0.22/0.49  fof(f32,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.22/0.49    inference(ennf_transformation,[],[f8])).
% 0.22/0.49  fof(f8,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 0.22/0.49  fof(f79,plain,(
% 0.22/0.49    v4_pre_topc(k2_pre_topc(sK0,sK1),sK0)),
% 0.22/0.49    inference(subsumption_resolution,[],[f78,f40])).
% 0.22/0.49  fof(f40,plain,(
% 0.22/0.49    v2_pre_topc(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f38])).
% 0.22/0.49  fof(f78,plain,(
% 0.22/0.49    v4_pre_topc(k2_pre_topc(sK0,sK1),sK0) | ~v2_pre_topc(sK0)),
% 0.22/0.49    inference(subsumption_resolution,[],[f76,f41])).
% 0.22/0.49  fof(f76,plain,(
% 0.22/0.49    v4_pre_topc(k2_pre_topc(sK0,sK1),sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.22/0.49    inference(resolution,[],[f56,f42])).
% 0.22/0.49  fof(f56,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f28])).
% 0.22/0.49  fof(f28,plain,(
% 0.22/0.49    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.49    inference(flattening,[],[f27])).
% 0.22/0.49  fof(f27,plain,(
% 0.22/0.49    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f13])).
% 0.22/0.49  fof(f13,axiom,(
% 0.22/0.49    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_pre_topc(X0,X1),X0))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_tops_1)).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (10072)------------------------------
% 0.22/0.49  % (10072)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (10072)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (10072)Memory used [KB]: 3326
% 0.22/0.49  % (10072)Time elapsed: 0.082 s
% 0.22/0.49  % (10072)------------------------------
% 0.22/0.49  % (10072)------------------------------
% 0.22/0.49  % (10060)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.50  % (10058)Success in time 0.134 s
%------------------------------------------------------------------------------
