%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:49 EST 2020

% Result     : Theorem 1.64s
% Output     : Refutation 1.82s
% Verified   : 
% Statistics : Number of formulae       :  100 (1231 expanded)
%              Number of leaves         :   17 ( 360 expanded)
%              Depth                    :   24
%              Number of atoms          :  234 (4236 expanded)
%              Number of equality atoms :  104 (1556 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f987,plain,(
    $false ),
    inference(global_subsumption,[],[f42,f127,f969,f970])).

fof(f970,plain,(
    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) ),
    inference(backward_demodulation,[],[f79,f969])).

fof(f79,plain,(
    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f39,f40,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

fof(f40,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,
    ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | ~ v4_pre_topc(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | v4_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f31,f33,f32])).

fof(f32,plain,
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

fof(f33,plain,
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

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
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

fof(f39,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f969,plain,(
    sK1 = k2_pre_topc(sK0,sK1) ),
    inference(duplicate_literal_removal,[],[f966])).

fof(f966,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | sK1 = k2_pre_topc(sK0,sK1) ),
    inference(superposition,[],[f830,f80])).

fof(f80,plain,(
    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f39,f40,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

fof(f830,plain,
    ( sK1 = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | sK1 = k2_pre_topc(sK0,sK1) ),
    inference(superposition,[],[f827,f137])).

fof(f137,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | sK1 = k2_pre_topc(sK0,sK1) ),
    inference(resolution,[],[f131,f41])).

fof(f41,plain,
    ( v4_pre_topc(sK1,sK0)
    | k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f34])).

fof(f131,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | sK1 = k2_pre_topc(sK0,sK1) ),
    inference(resolution,[],[f76,f40])).

fof(f76,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v4_pre_topc(X0,sK0)
      | k2_pre_topc(sK0,X0) = X0 ) ),
    inference(resolution,[],[f39,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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

fof(f827,plain,(
    ! [X0] : sK1 = k4_subset_1(u1_struct_0(sK0),sK1,k7_subset_1(u1_struct_0(sK0),sK1,X0)) ),
    inference(forward_demodulation,[],[f826,f265])).

fof(f265,plain,(
    sK1 = k5_xboole_0(sK1,k1_xboole_0) ),
    inference(forward_demodulation,[],[f262,f107])).

fof(f107,plain,(
    sK1 = k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0) ),
    inference(superposition,[],[f83,f65])).

fof(f65,plain,(
    ! [X0] : k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = X0 ),
    inference(definition_unfolding,[],[f44,f63])).

fof(f63,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f53,f51])).

fof(f51,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f53,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f44,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f83,plain,(
    ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X0))) ),
    inference(unit_resulting_resolution,[],[f40,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) ) ),
    inference(definition_unfolding,[],[f61,f63])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f262,plain,(
    k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0) = k5_xboole_0(sK1,k1_xboole_0) ),
    inference(superposition,[],[f105,f218])).

fof(f218,plain,(
    k1_xboole_0 = k1_setfam_1(k2_tarski(k1_xboole_0,sK1)) ),
    inference(forward_demodulation,[],[f214,f50])).

fof(f50,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f214,plain,(
    k1_xboole_0 = k1_setfam_1(k2_tarski(sK1,k1_xboole_0)) ),
    inference(superposition,[],[f119,f204])).

fof(f204,plain,(
    k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),sK1,sK1) ),
    inference(forward_demodulation,[],[f200,f172])).

fof(f172,plain,(
    k1_xboole_0 = k5_xboole_0(sK1,sK1) ),
    inference(superposition,[],[f121,f107])).

fof(f121,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(k7_subset_1(u1_struct_0(sK0),sK1,X0),k7_subset_1(u1_struct_0(sK0),sK1,X0)) ),
    inference(forward_demodulation,[],[f120,f119])).

fof(f120,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(k7_subset_1(u1_struct_0(sK0),sK1,X0),k1_setfam_1(k2_tarski(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X0)))) ),
    inference(forward_demodulation,[],[f113,f50])).

fof(f113,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(k7_subset_1(u1_struct_0(sK0),sK1,X0),k1_setfam_1(k2_tarski(k7_subset_1(u1_struct_0(sK0),sK1,X0),sK1))) ),
    inference(unit_resulting_resolution,[],[f110,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ) ),
    inference(definition_unfolding,[],[f59,f63])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f110,plain,(
    ! [X1] : r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,X1),sK1) ),
    inference(superposition,[],[f66,f83])).

fof(f66,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0) ),
    inference(definition_unfolding,[],[f49,f63])).

fof(f49,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f200,plain,(
    k7_subset_1(u1_struct_0(sK0),sK1,sK1) = k5_xboole_0(sK1,sK1) ),
    inference(superposition,[],[f83,f195])).

fof(f195,plain,(
    sK1 = k1_setfam_1(k2_tarski(sK1,sK1)) ),
    inference(superposition,[],[f119,f107])).

fof(f119,plain,(
    ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k1_setfam_1(k2_tarski(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X0))) ),
    inference(forward_demodulation,[],[f114,f50])).

fof(f114,plain,(
    ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k1_setfam_1(k2_tarski(k7_subset_1(u1_struct_0(sK0),sK1,X0),sK1)) ),
    inference(unit_resulting_resolution,[],[f110,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_setfam_1(k2_tarski(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f54,f51])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f105,plain,(
    ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(X0,sK1))) ),
    inference(superposition,[],[f83,f50])).

fof(f826,plain,(
    ! [X0] : k4_subset_1(u1_struct_0(sK0),sK1,k7_subset_1(u1_struct_0(sK0),sK1,X0)) = k5_xboole_0(sK1,k1_xboole_0) ),
    inference(backward_demodulation,[],[f101,f825])).

fof(f825,plain,(
    ! [X0] : k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK1,X0),sK1) ),
    inference(forward_demodulation,[],[f821,f121])).

fof(f821,plain,(
    ! [X0] : k7_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK1,X0),sK1) = k5_xboole_0(k7_subset_1(u1_struct_0(sK0),sK1,X0),k7_subset_1(u1_struct_0(sK0),sK1,X0)) ),
    inference(superposition,[],[f331,f119])).

fof(f331,plain,(
    ! [X0,X1] : k7_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK1,X0),X1) = k5_xboole_0(k7_subset_1(u1_struct_0(sK0),sK1,X0),k1_setfam_1(k2_tarski(X1,k7_subset_1(u1_struct_0(sK0),sK1,X0)))) ),
    inference(superposition,[],[f96,f50])).

fof(f96,plain,(
    ! [X0,X1] : k7_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK1,X0),X1) = k5_xboole_0(k7_subset_1(u1_struct_0(sK0),sK1,X0),k1_setfam_1(k2_tarski(k7_subset_1(u1_struct_0(sK0),sK1,X0),X1))) ),
    inference(unit_resulting_resolution,[],[f84,f70])).

fof(f84,plain,(
    ! [X0] : m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f40,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_subset_1)).

fof(f101,plain,(
    ! [X0] : k4_subset_1(u1_struct_0(sK0),sK1,k7_subset_1(u1_struct_0(sK0),sK1,X0)) = k5_xboole_0(sK1,k7_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK1,X0),sK1)) ),
    inference(forward_demodulation,[],[f94,f96])).

fof(f94,plain,(
    ! [X0] : k4_subset_1(u1_struct_0(sK0),sK1,k7_subset_1(u1_struct_0(sK0),sK1,X0)) = k5_xboole_0(sK1,k5_xboole_0(k7_subset_1(u1_struct_0(sK0),sK1,X0),k1_setfam_1(k2_tarski(k7_subset_1(u1_struct_0(sK0),sK1,X0),sK1)))) ),
    inference(unit_resulting_resolution,[],[f40,f84,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k5_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f62,f64])).

fof(f64,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))) ),
    inference(definition_unfolding,[],[f52,f63])).

fof(f52,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f127,plain,
    ( sK1 != k2_pre_topc(sK0,sK1)
    | v4_pre_topc(sK1,sK0) ),
    inference(resolution,[],[f75,f40])).

fof(f75,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v4_pre_topc(X0,sK0)
      | k2_pre_topc(sK0,X0) != X0 ) ),
    inference(subsumption_resolution,[],[f74,f39])).

fof(f74,plain,(
    ! [X0] :
      ( k2_pre_topc(sK0,X0) != X0
      | v4_pre_topc(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f38,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | k2_pre_topc(X0,X1) != X1
      | v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f38,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f42,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:45:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (32576)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.51  % (32592)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.52  % (32570)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.52  % (32588)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.52  % (32581)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.52  % (32580)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.53  % (32573)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.53  % (32584)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.54  % (32568)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.54  % (32572)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.54  % (32569)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.54  % (32590)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.54  % (32591)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.54  % (32598)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.54  % (32598)Refutation not found, incomplete strategy% (32598)------------------------------
% 0.21/0.54  % (32598)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (32598)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (32598)Memory used [KB]: 1663
% 0.21/0.54  % (32598)Time elapsed: 0.128 s
% 0.21/0.54  % (32598)------------------------------
% 0.21/0.54  % (32598)------------------------------
% 0.21/0.54  % (32583)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.54  % (32571)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.54  % (32577)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.55  % (32585)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.55  % (32574)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.55  % (32589)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.55  % (32587)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.55  % (32575)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.55  % (32593)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.55  % (32595)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.56  % (32594)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.56  % (32582)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.56  % (32597)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.56  % (32579)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.56  % (32596)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.57  % (32586)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.57  % (32597)Refutation not found, incomplete strategy% (32597)------------------------------
% 0.21/0.57  % (32597)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (32579)Refutation not found, incomplete strategy% (32579)------------------------------
% 0.21/0.57  % (32579)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.64/0.58  % (32597)Termination reason: Refutation not found, incomplete strategy
% 1.64/0.58  
% 1.64/0.58  % (32597)Memory used [KB]: 10746
% 1.64/0.58  % (32597)Time elapsed: 0.159 s
% 1.64/0.58  % (32597)------------------------------
% 1.64/0.58  % (32597)------------------------------
% 1.64/0.58  % (32585)Refutation not found, incomplete strategy% (32585)------------------------------
% 1.64/0.58  % (32585)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.64/0.58  % (32579)Termination reason: Refutation not found, incomplete strategy
% 1.64/0.58  
% 1.64/0.58  % (32579)Memory used [KB]: 10746
% 1.64/0.58  % (32579)Time elapsed: 0.156 s
% 1.64/0.58  % (32579)------------------------------
% 1.64/0.58  % (32579)------------------------------
% 1.64/0.58  % (32585)Termination reason: Refutation not found, incomplete strategy
% 1.64/0.58  
% 1.64/0.58  % (32585)Memory used [KB]: 10618
% 1.64/0.58  % (32585)Time elapsed: 0.169 s
% 1.64/0.58  % (32585)------------------------------
% 1.64/0.58  % (32585)------------------------------
% 1.64/0.59  % (32580)Refutation found. Thanks to Tanya!
% 1.64/0.59  % SZS status Theorem for theBenchmark
% 1.64/0.59  % SZS output start Proof for theBenchmark
% 1.64/0.59  fof(f987,plain,(
% 1.64/0.59    $false),
% 1.64/0.59    inference(global_subsumption,[],[f42,f127,f969,f970])).
% 1.64/0.59  fof(f970,plain,(
% 1.64/0.59    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),
% 1.64/0.59    inference(backward_demodulation,[],[f79,f969])).
% 1.64/0.59  fof(f79,plain,(
% 1.64/0.59    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))),
% 1.64/0.59    inference(unit_resulting_resolution,[],[f39,f40,f46])).
% 1.64/0.59  fof(f46,plain,(
% 1.64/0.59    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))) )),
% 1.64/0.59    inference(cnf_transformation,[],[f22])).
% 1.64/0.59  fof(f22,plain,(
% 1.64/0.59    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.64/0.59    inference(ennf_transformation,[],[f15])).
% 1.64/0.59  fof(f15,axiom,(
% 1.64/0.59    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 1.64/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).
% 1.64/0.59  fof(f40,plain,(
% 1.64/0.59    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.64/0.59    inference(cnf_transformation,[],[f34])).
% 1.64/0.59  fof(f34,plain,(
% 1.64/0.59    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 1.64/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f31,f33,f32])).
% 1.64/0.59  fof(f32,plain,(
% 1.64/0.59    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 1.64/0.59    introduced(choice_axiom,[])).
% 1.64/0.59  fof(f33,plain,(
% 1.64/0.59    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.64/0.59    introduced(choice_axiom,[])).
% 1.64/0.59  fof(f31,plain,(
% 1.64/0.59    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.64/0.59    inference(flattening,[],[f30])).
% 1.64/0.59  fof(f30,plain,(
% 1.64/0.59    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.64/0.59    inference(nnf_transformation,[],[f20])).
% 1.64/0.59  fof(f20,plain,(
% 1.64/0.59    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.64/0.59    inference(flattening,[],[f19])).
% 1.64/0.59  fof(f19,plain,(
% 1.64/0.59    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 1.64/0.59    inference(ennf_transformation,[],[f18])).
% 1.64/0.59  fof(f18,negated_conjecture,(
% 1.64/0.59    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 1.64/0.59    inference(negated_conjecture,[],[f17])).
% 1.64/0.59  fof(f17,conjecture,(
% 1.64/0.59    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 1.64/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).
% 1.64/0.59  fof(f39,plain,(
% 1.64/0.59    l1_pre_topc(sK0)),
% 1.64/0.59    inference(cnf_transformation,[],[f34])).
% 1.64/0.59  fof(f969,plain,(
% 1.64/0.59    sK1 = k2_pre_topc(sK0,sK1)),
% 1.64/0.59    inference(duplicate_literal_removal,[],[f966])).
% 1.64/0.59  fof(f966,plain,(
% 1.64/0.59    sK1 = k2_pre_topc(sK0,sK1) | sK1 = k2_pre_topc(sK0,sK1)),
% 1.64/0.59    inference(superposition,[],[f830,f80])).
% 1.64/0.59  fof(f80,plain,(
% 1.64/0.59    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 1.64/0.59    inference(unit_resulting_resolution,[],[f39,f40,f45])).
% 1.64/0.59  fof(f45,plain,(
% 1.64/0.59    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))) )),
% 1.64/0.59    inference(cnf_transformation,[],[f21])).
% 1.64/0.59  fof(f21,plain,(
% 1.64/0.59    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.64/0.59    inference(ennf_transformation,[],[f16])).
% 1.64/0.59  fof(f16,axiom,(
% 1.64/0.59    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 1.64/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).
% 1.64/0.59  fof(f830,plain,(
% 1.64/0.59    sK1 = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | sK1 = k2_pre_topc(sK0,sK1)),
% 1.64/0.59    inference(superposition,[],[f827,f137])).
% 1.64/0.59  fof(f137,plain,(
% 1.64/0.59    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | sK1 = k2_pre_topc(sK0,sK1)),
% 1.64/0.59    inference(resolution,[],[f131,f41])).
% 1.64/0.59  fof(f41,plain,(
% 1.64/0.59    v4_pre_topc(sK1,sK0) | k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),
% 1.64/0.59    inference(cnf_transformation,[],[f34])).
% 1.64/0.59  fof(f131,plain,(
% 1.64/0.59    ~v4_pre_topc(sK1,sK0) | sK1 = k2_pre_topc(sK0,sK1)),
% 1.64/0.59    inference(resolution,[],[f76,f40])).
% 1.64/0.59  fof(f76,plain,(
% 1.64/0.59    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(X0,sK0) | k2_pre_topc(sK0,X0) = X0) )),
% 1.64/0.59    inference(resolution,[],[f39,f47])).
% 1.64/0.59  fof(f47,plain,(
% 1.64/0.59    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = X1) )),
% 1.64/0.59    inference(cnf_transformation,[],[f24])).
% 1.64/0.59  fof(f24,plain,(
% 1.64/0.59    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.64/0.59    inference(flattening,[],[f23])).
% 1.64/0.59  fof(f23,plain,(
% 1.64/0.59    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.64/0.59    inference(ennf_transformation,[],[f14])).
% 1.64/0.59  fof(f14,axiom,(
% 1.64/0.59    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 1.64/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).
% 1.64/0.59  fof(f827,plain,(
% 1.64/0.59    ( ! [X0] : (sK1 = k4_subset_1(u1_struct_0(sK0),sK1,k7_subset_1(u1_struct_0(sK0),sK1,X0))) )),
% 1.64/0.59    inference(forward_demodulation,[],[f826,f265])).
% 1.64/0.59  fof(f265,plain,(
% 1.64/0.59    sK1 = k5_xboole_0(sK1,k1_xboole_0)),
% 1.64/0.59    inference(forward_demodulation,[],[f262,f107])).
% 1.64/0.59  fof(f107,plain,(
% 1.64/0.59    sK1 = k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0)),
% 1.64/0.59    inference(superposition,[],[f83,f65])).
% 1.64/0.59  fof(f65,plain,(
% 1.64/0.59    ( ! [X0] : (k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = X0) )),
% 1.64/0.59    inference(definition_unfolding,[],[f44,f63])).
% 1.64/0.59  fof(f63,plain,(
% 1.64/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 1.64/0.59    inference(definition_unfolding,[],[f53,f51])).
% 1.64/0.59  fof(f51,plain,(
% 1.64/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.64/0.59    inference(cnf_transformation,[],[f13])).
% 1.64/0.59  fof(f13,axiom,(
% 1.64/0.59    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.64/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.64/0.59  fof(f53,plain,(
% 1.64/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.64/0.59    inference(cnf_transformation,[],[f3])).
% 1.64/0.59  fof(f3,axiom,(
% 1.64/0.59    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.64/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.64/0.59  fof(f44,plain,(
% 1.64/0.59    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.64/0.59    inference(cnf_transformation,[],[f7])).
% 1.64/0.59  fof(f7,axiom,(
% 1.64/0.59    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.64/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 1.64/0.59  fof(f83,plain,(
% 1.64/0.59    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),sK1,X0) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X0)))) )),
% 1.64/0.59    inference(unit_resulting_resolution,[],[f40,f70])).
% 1.82/0.59  fof(f70,plain,(
% 1.82/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))) )),
% 1.82/0.59    inference(definition_unfolding,[],[f61,f63])).
% 1.82/0.59  fof(f61,plain,(
% 1.82/0.59    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.82/0.59    inference(cnf_transformation,[],[f27])).
% 1.82/0.59  fof(f27,plain,(
% 1.82/0.59    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.82/0.59    inference(ennf_transformation,[],[f12])).
% 1.82/0.59  fof(f12,axiom,(
% 1.82/0.59    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 1.82/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 1.82/0.59  fof(f262,plain,(
% 1.82/0.59    k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0) = k5_xboole_0(sK1,k1_xboole_0)),
% 1.82/0.59    inference(superposition,[],[f105,f218])).
% 1.82/0.59  fof(f218,plain,(
% 1.82/0.59    k1_xboole_0 = k1_setfam_1(k2_tarski(k1_xboole_0,sK1))),
% 1.82/0.59    inference(forward_demodulation,[],[f214,f50])).
% 1.82/0.59  fof(f50,plain,(
% 1.82/0.59    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.82/0.59    inference(cnf_transformation,[],[f9])).
% 1.82/0.59  fof(f9,axiom,(
% 1.82/0.59    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.82/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.82/0.59  fof(f214,plain,(
% 1.82/0.59    k1_xboole_0 = k1_setfam_1(k2_tarski(sK1,k1_xboole_0))),
% 1.82/0.59    inference(superposition,[],[f119,f204])).
% 1.82/0.59  fof(f204,plain,(
% 1.82/0.59    k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),sK1,sK1)),
% 1.82/0.59    inference(forward_demodulation,[],[f200,f172])).
% 1.82/0.59  fof(f172,plain,(
% 1.82/0.59    k1_xboole_0 = k5_xboole_0(sK1,sK1)),
% 1.82/0.59    inference(superposition,[],[f121,f107])).
% 1.82/0.59  fof(f121,plain,(
% 1.82/0.59    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(k7_subset_1(u1_struct_0(sK0),sK1,X0),k7_subset_1(u1_struct_0(sK0),sK1,X0))) )),
% 1.82/0.59    inference(forward_demodulation,[],[f120,f119])).
% 1.82/0.59  fof(f120,plain,(
% 1.82/0.59    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(k7_subset_1(u1_struct_0(sK0),sK1,X0),k1_setfam_1(k2_tarski(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X0))))) )),
% 1.82/0.59    inference(forward_demodulation,[],[f113,f50])).
% 1.82/0.59  fof(f113,plain,(
% 1.82/0.59    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(k7_subset_1(u1_struct_0(sK0),sK1,X0),k1_setfam_1(k2_tarski(k7_subset_1(u1_struct_0(sK0),sK1,X0),sK1)))) )),
% 1.82/0.59    inference(unit_resulting_resolution,[],[f110,f68])).
% 1.82/0.59  fof(f68,plain,(
% 1.82/0.59    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 1.82/0.59    inference(definition_unfolding,[],[f59,f63])).
% 1.82/0.59  fof(f59,plain,(
% 1.82/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 1.82/0.59    inference(cnf_transformation,[],[f37])).
% 1.82/0.59  fof(f37,plain,(
% 1.82/0.59    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 1.82/0.59    inference(nnf_transformation,[],[f2])).
% 1.82/0.59  fof(f2,axiom,(
% 1.82/0.59    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.82/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.82/0.59  fof(f110,plain,(
% 1.82/0.59    ( ! [X1] : (r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,X1),sK1)) )),
% 1.82/0.59    inference(superposition,[],[f66,f83])).
% 1.82/0.59  fof(f66,plain,(
% 1.82/0.59    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0)) )),
% 1.82/0.59    inference(definition_unfolding,[],[f49,f63])).
% 1.82/0.59  fof(f49,plain,(
% 1.82/0.59    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.82/0.59    inference(cnf_transformation,[],[f6])).
% 1.82/0.59  fof(f6,axiom,(
% 1.82/0.59    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.82/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.82/0.59  fof(f200,plain,(
% 1.82/0.59    k7_subset_1(u1_struct_0(sK0),sK1,sK1) = k5_xboole_0(sK1,sK1)),
% 1.82/0.59    inference(superposition,[],[f83,f195])).
% 1.82/0.59  fof(f195,plain,(
% 1.82/0.59    sK1 = k1_setfam_1(k2_tarski(sK1,sK1))),
% 1.82/0.59    inference(superposition,[],[f119,f107])).
% 1.82/0.59  fof(f119,plain,(
% 1.82/0.59    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),sK1,X0) = k1_setfam_1(k2_tarski(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X0)))) )),
% 1.82/0.59    inference(forward_demodulation,[],[f114,f50])).
% 1.82/0.59  fof(f114,plain,(
% 1.82/0.59    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),sK1,X0) = k1_setfam_1(k2_tarski(k7_subset_1(u1_struct_0(sK0),sK1,X0),sK1))) )),
% 1.82/0.59    inference(unit_resulting_resolution,[],[f110,f67])).
% 1.82/0.59  fof(f67,plain,(
% 1.82/0.59    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_setfam_1(k2_tarski(X0,X1)) = X0) )),
% 1.82/0.59    inference(definition_unfolding,[],[f54,f51])).
% 1.82/0.59  fof(f54,plain,(
% 1.82/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.82/0.59    inference(cnf_transformation,[],[f25])).
% 1.82/0.60  fof(f25,plain,(
% 1.82/0.60    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.82/0.60    inference(ennf_transformation,[],[f4])).
% 1.82/0.60  fof(f4,axiom,(
% 1.82/0.60    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.82/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.82/0.60  fof(f105,plain,(
% 1.82/0.60    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),sK1,X0) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(X0,sK1)))) )),
% 1.82/0.60    inference(superposition,[],[f83,f50])).
% 1.82/0.60  fof(f826,plain,(
% 1.82/0.60    ( ! [X0] : (k4_subset_1(u1_struct_0(sK0),sK1,k7_subset_1(u1_struct_0(sK0),sK1,X0)) = k5_xboole_0(sK1,k1_xboole_0)) )),
% 1.82/0.60    inference(backward_demodulation,[],[f101,f825])).
% 1.82/0.60  fof(f825,plain,(
% 1.82/0.60    ( ! [X0] : (k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK1,X0),sK1)) )),
% 1.82/0.60    inference(forward_demodulation,[],[f821,f121])).
% 1.82/0.60  fof(f821,plain,(
% 1.82/0.60    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK1,X0),sK1) = k5_xboole_0(k7_subset_1(u1_struct_0(sK0),sK1,X0),k7_subset_1(u1_struct_0(sK0),sK1,X0))) )),
% 1.82/0.60    inference(superposition,[],[f331,f119])).
% 1.82/0.60  fof(f331,plain,(
% 1.82/0.60    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK1,X0),X1) = k5_xboole_0(k7_subset_1(u1_struct_0(sK0),sK1,X0),k1_setfam_1(k2_tarski(X1,k7_subset_1(u1_struct_0(sK0),sK1,X0))))) )),
% 1.82/0.60    inference(superposition,[],[f96,f50])).
% 1.82/0.60  fof(f96,plain,(
% 1.82/0.60    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK1,X0),X1) = k5_xboole_0(k7_subset_1(u1_struct_0(sK0),sK1,X0),k1_setfam_1(k2_tarski(k7_subset_1(u1_struct_0(sK0),sK1,X0),X1)))) )),
% 1.82/0.60    inference(unit_resulting_resolution,[],[f84,f70])).
% 1.82/0.60  fof(f84,plain,(
% 1.82/0.60    ( ! [X0] : (m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 1.82/0.60    inference(unit_resulting_resolution,[],[f40,f60])).
% 1.82/0.60  fof(f60,plain,(
% 1.82/0.60    ( ! [X2,X0,X1] : (m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.82/0.60    inference(cnf_transformation,[],[f26])).
% 1.82/0.60  fof(f26,plain,(
% 1.82/0.60    ! [X0,X1,X2] : (m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.82/0.60    inference(ennf_transformation,[],[f10])).
% 1.82/0.60  fof(f10,axiom,(
% 1.82/0.60    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 1.82/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_subset_1)).
% 1.82/0.60  fof(f101,plain,(
% 1.82/0.60    ( ! [X0] : (k4_subset_1(u1_struct_0(sK0),sK1,k7_subset_1(u1_struct_0(sK0),sK1,X0)) = k5_xboole_0(sK1,k7_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK1,X0),sK1))) )),
% 1.82/0.60    inference(forward_demodulation,[],[f94,f96])).
% 1.82/0.60  fof(f94,plain,(
% 1.82/0.60    ( ! [X0] : (k4_subset_1(u1_struct_0(sK0),sK1,k7_subset_1(u1_struct_0(sK0),sK1,X0)) = k5_xboole_0(sK1,k5_xboole_0(k7_subset_1(u1_struct_0(sK0),sK1,X0),k1_setfam_1(k2_tarski(k7_subset_1(u1_struct_0(sK0),sK1,X0),sK1))))) )),
% 1.82/0.60    inference(unit_resulting_resolution,[],[f40,f84,f71])).
% 1.82/0.60  fof(f71,plain,(
% 1.82/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k5_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.82/0.60    inference(definition_unfolding,[],[f62,f64])).
% 1.82/0.60  fof(f64,plain,(
% 1.82/0.60    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0))))) )),
% 1.82/0.60    inference(definition_unfolding,[],[f52,f63])).
% 1.82/0.60  fof(f52,plain,(
% 1.82/0.60    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.82/0.60    inference(cnf_transformation,[],[f8])).
% 1.82/0.60  fof(f8,axiom,(
% 1.82/0.60    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.82/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.82/0.60  fof(f62,plain,(
% 1.82/0.60    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.82/0.60    inference(cnf_transformation,[],[f29])).
% 1.82/0.60  fof(f29,plain,(
% 1.82/0.60    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.82/0.60    inference(flattening,[],[f28])).
% 1.82/0.60  fof(f28,plain,(
% 1.82/0.60    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 1.82/0.60    inference(ennf_transformation,[],[f11])).
% 1.82/0.60  fof(f11,axiom,(
% 1.82/0.60    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 1.82/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 1.82/0.60  fof(f127,plain,(
% 1.82/0.60    sK1 != k2_pre_topc(sK0,sK1) | v4_pre_topc(sK1,sK0)),
% 1.82/0.60    inference(resolution,[],[f75,f40])).
% 1.82/0.60  fof(f75,plain,(
% 1.82/0.60    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(X0,sK0) | k2_pre_topc(sK0,X0) != X0) )),
% 1.82/0.60    inference(subsumption_resolution,[],[f74,f39])).
% 1.82/0.60  fof(f74,plain,(
% 1.82/0.60    ( ! [X0] : (k2_pre_topc(sK0,X0) != X0 | v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) )),
% 1.82/0.60    inference(resolution,[],[f38,f48])).
% 1.82/0.60  fof(f48,plain,(
% 1.82/0.60    ( ! [X0,X1] : (~v2_pre_topc(X0) | k2_pre_topc(X0,X1) != X1 | v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.82/0.60    inference(cnf_transformation,[],[f24])).
% 1.82/0.60  fof(f38,plain,(
% 1.82/0.60    v2_pre_topc(sK0)),
% 1.82/0.60    inference(cnf_transformation,[],[f34])).
% 1.82/0.60  fof(f42,plain,(
% 1.82/0.60    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)),
% 1.82/0.60    inference(cnf_transformation,[],[f34])).
% 1.82/0.60  % SZS output end Proof for theBenchmark
% 1.82/0.60  % (32580)------------------------------
% 1.82/0.60  % (32580)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.82/0.60  % (32580)Termination reason: Refutation
% 1.82/0.60  
% 1.82/0.60  % (32580)Memory used [KB]: 7419
% 1.82/0.60  % (32580)Time elapsed: 0.166 s
% 1.82/0.60  % (32580)------------------------------
% 1.82/0.60  % (32580)------------------------------
% 1.82/0.60  % (32567)Success in time 0.231 s
%------------------------------------------------------------------------------
