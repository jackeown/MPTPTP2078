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
% DateTime   : Thu Dec  3 13:12:17 EST 2020

% Result     : Theorem 2.09s
% Output     : Refutation 2.09s
% Verified   : 
% Statistics : Number of formulae       :  178 (4022 expanded)
%              Number of leaves         :   22 ( 874 expanded)
%              Depth                    :   39
%              Number of atoms          :  616 (18387 expanded)
%              Number of equality atoms :  146 (3152 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f947,plain,(
    $false ),
    inference(subsumption_resolution,[],[f946,f855])).

fof(f855,plain,(
    r2_hidden(sK4(sK0,k1_xboole_0,sK2),u1_struct_0(sK0)) ),
    inference(resolution,[],[f773,f475])).

fof(f475,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f474,f48])).

fof(f48,plain,
    ( ~ v1_tops_1(sK1,sK0)
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tops_1(X1,X0)
          <~> ! [X2] :
                ( ~ r1_xboole_0(X1,X2)
                | ~ v3_pre_topc(X2,X0)
                | k1_xboole_0 = X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tops_1(X1,X0)
          <~> ! [X2] :
                ( ~ r1_xboole_0(X1,X2)
                | ~ v3_pre_topc(X2,X0)
                | k1_xboole_0 = X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v1_tops_1(X1,X0)
            <=> ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ~ ( r1_xboole_0(X1,X2)
                      & v3_pre_topc(X2,X0)
                      & k1_xboole_0 != X2 ) ) ) ) ) ),
    inference(negated_conjecture,[],[f24])).

fof(f24,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ~ ( r1_xboole_0(X1,X2)
                    & v3_pre_topc(X2,X0)
                    & k1_xboole_0 != X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_tops_1)).

fof(f474,plain,(
    v1_tops_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f473,f55])).

fof(f55,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f473,plain,
    ( ~ l1_pre_topc(sK0)
    | v1_tops_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f472,f53])).

fof(f53,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f28])).

fof(f472,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | v1_tops_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f468,f117])).

fof(f117,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(resolution,[],[f113,f55])).

fof(f113,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | u1_struct_0(X0) = k2_struct_0(X0) ) ),
    inference(resolution,[],[f61,f62])).

fof(f62,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f61,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | u1_struct_0(X0) = k2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f468,plain,
    ( u1_struct_0(sK0) != k2_struct_0(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | v1_tops_1(sK1,sK0) ),
    inference(superposition,[],[f66,f465])).

fof(f465,plain,(
    u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) ),
    inference(subsumption_resolution,[],[f464,f53])).

fof(f464,plain,
    ( u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f463,f112])).

fof(f112,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f60,f56])).

fof(f56,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f60,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f463,plain,
    ( u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(duplicate_literal_removal,[],[f459])).

fof(f459,plain,
    ( u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) ),
    inference(resolution,[],[f458,f312])).

fof(f312,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(sK4(sK0,X2,X3),k1_xboole_0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_pre_topc(sK0,X2) = X3 ) ),
    inference(subsumption_resolution,[],[f311,f123])).

fof(f123,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k2_tarski(k1_xboole_0,X0)) ),
    inference(resolution,[],[f102,f115])).

fof(f115,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(resolution,[],[f96,f57])).

fof(f57,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f96,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f102,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_setfam_1(k2_tarski(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f91,f88])).

fof(f88,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f91,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f311,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(sK4(sK0,X2,X3),k1_xboole_0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_pre_topc(sK0,X2) = X3
      | k1_xboole_0 != k1_setfam_1(k2_tarski(k1_xboole_0,u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f306,f57])).

fof(f306,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(sK4(sK0,X2,X3),k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_pre_topc(sK0,X2) = X3
      | k1_xboole_0 != k1_setfam_1(k2_tarski(k1_xboole_0,u1_struct_0(sK0))) ) ),
    inference(superposition,[],[f304,f166])).

fof(f166,plain,(
    k1_xboole_0 = k2_pre_topc(sK0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f165,f55])).

fof(f165,plain,
    ( ~ l1_pre_topc(sK0)
    | k1_xboole_0 = k2_pre_topc(sK0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f164,f57])).

fof(f164,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k1_xboole_0 = k2_pre_topc(sK0,k1_xboole_0) ),
    inference(resolution,[],[f162,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k2_pre_topc(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
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

fof(f162,plain,(
    v4_pre_topc(k1_xboole_0,sK0) ),
    inference(subsumption_resolution,[],[f161,f57])).

fof(f161,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(k1_xboole_0,sK0) ),
    inference(subsumption_resolution,[],[f159,f120])).

fof(f120,plain,(
    v3_pre_topc(u1_struct_0(sK0),sK0) ),
    inference(subsumption_resolution,[],[f119,f54])).

fof(f54,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f119,plain,
    ( v3_pre_topc(u1_struct_0(sK0),sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f118,f55])).

fof(f118,plain,
    ( v3_pre_topc(u1_struct_0(sK0),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(superposition,[],[f87,f117])).

fof(f87,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_tops_1)).

fof(f159,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK0),sK0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(k1_xboole_0,sK0) ),
    inference(superposition,[],[f158,f132])).

fof(f132,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f131,f111])).

fof(f111,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f100,f99])).

fof(f99,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f58,f88])).

fof(f58,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f100,plain,(
    ! [X0] : k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = X0 ),
    inference(definition_unfolding,[],[f59,f98])).

fof(f98,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f89,f88])).

fof(f89,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f59,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f131,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f129,f99])).

fof(f129,plain,(
    ! [X0] : k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = k3_subset_1(X0,k1_xboole_0) ),
    inference(resolution,[],[f103,f57])).

fof(f103,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ) ),
    inference(definition_unfolding,[],[f92,f98])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f158,plain,(
    ! [X0] :
      ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v4_pre_topc(X0,sK0) ) ),
    inference(resolution,[],[f68,f55])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | v4_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tops_1)).

fof(f304,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK4(sK0,X1,X2),k2_pre_topc(sK0,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_pre_topc(sK0,X1) = X2
      | k1_xboole_0 != k1_setfam_1(k2_tarski(X0,u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f303,f105])).

fof(f105,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k1_xboole_0 != k1_setfam_1(k2_tarski(X0,X1)) ) ),
    inference(definition_unfolding,[],[f94,f88])).

fof(f94,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f303,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(sK4(sK0,X1,X2),k2_pre_topc(sK0,X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_pre_topc(sK0,X1) = X2 ) ),
    inference(subsumption_resolution,[],[f302,f120])).

fof(f302,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_pre_topc(u1_struct_0(sK0),sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_xboole_0(X0,u1_struct_0(sK0))
      | ~ r2_hidden(sK4(sK0,X1,X2),k2_pre_topc(sK0,X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_pre_topc(sK0,X1) = X2 ) ),
    inference(subsumption_resolution,[],[f301,f112])).

fof(f301,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(u1_struct_0(sK0),sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_xboole_0(X0,u1_struct_0(sK0))
      | ~ r2_hidden(sK4(sK0,X1,X2),k2_pre_topc(sK0,X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_pre_topc(sK0,X1) = X2 ) ),
    inference(resolution,[],[f300,f254])).

fof(f254,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(sK0,X0,X1),u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_pre_topc(sK0,X0) = X1 ) ),
    inference(resolution,[],[f86,f55])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(sK4(X0,X1,X2),u1_struct_0(X0))
      | k2_pre_topc(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k2_pre_topc(X0,X1) = X2
              <=> ! [X3] :
                    ( ( r2_hidden(X3,X2)
                    <=> ! [X4] :
                          ( ~ r1_xboole_0(X1,X4)
                          | ~ r2_hidden(X3,X4)
                          | ~ v3_pre_topc(X4,X0)
                          | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) ) )
                    | ~ r2_hidden(X3,u1_struct_0(X0)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k2_pre_topc(X0,X1) = X2
              <=> ! [X3] :
                    ( ( r2_hidden(X3,X2)
                    <=> ! [X4] :
                          ( ~ r1_xboole_0(X1,X4)
                          | ~ r2_hidden(X3,X4)
                          | ~ v3_pre_topc(X4,X0)
                          | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) ) )
                    | ~ r2_hidden(X3,u1_struct_0(X0)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( k2_pre_topc(X0,X1) = X2
              <=> ! [X3] :
                    ( r2_hidden(X3,u1_struct_0(X0))
                   => ( r2_hidden(X3,X2)
                    <=> ! [X4] :
                          ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
                         => ~ ( r1_xboole_0(X1,X4)
                              & r2_hidden(X3,X4)
                              & v3_pre_topc(X4,X0) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_pre_topc)).

fof(f300,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X2,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_xboole_0(X0,X2)
      | ~ r2_hidden(X1,k2_pre_topc(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f299,f97])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f299,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X2,sK0)
      | ~ r2_hidden(X1,X2)
      | ~ r1_xboole_0(X0,X2)
      | ~ r2_hidden(X1,k2_pre_topc(sK0,X0)) ) ),
    inference(resolution,[],[f74,f55])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X3,X0)
      | ~ r2_hidden(X2,X3)
      | ~ r1_xboole_0(X1,X3)
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ( ! [X3] :
                      ( ~ r1_xboole_0(X1,X3)
                      | ~ r2_hidden(X2,X3)
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & ~ v2_struct_0(X0) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ( ! [X3] :
                      ( ~ r1_xboole_0(X1,X3)
                      | ~ r2_hidden(X2,X3)
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & ~ v2_struct_0(X0) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ( ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                     => ~ ( r1_xboole_0(X1,X3)
                          & r2_hidden(X2,X3)
                          & v3_pre_topc(X3,X0) ) )
                  & ~ v2_struct_0(X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_pre_topc)).

fof(f458,plain,
    ( r2_hidden(sK4(sK0,sK1,u1_struct_0(sK0)),k1_xboole_0)
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) ),
    inference(subsumption_resolution,[],[f455,f53])).

fof(f455,plain,
    ( r2_hidden(sK4(sK0,sK1,u1_struct_0(sK0)),k1_xboole_0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) ),
    inference(duplicate_literal_removal,[],[f454])).

fof(f454,plain,
    ( r2_hidden(sK4(sK0,sK1,u1_struct_0(sK0)),k1_xboole_0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) ),
    inference(superposition,[],[f450,f356])).

fof(f356,plain,
    ( k1_xboole_0 = sK5(sK0,sK1,u1_struct_0(sK0))
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) ),
    inference(subsumption_resolution,[],[f355,f53])).

fof(f355,plain,
    ( u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | k1_xboole_0 = sK5(sK0,sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(duplicate_literal_removal,[],[f354])).

fof(f354,plain,
    ( u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | k1_xboole_0 = sK5(sK0,sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) ),
    inference(resolution,[],[f349,f154])).

fof(f154,plain,(
    ! [X0] :
      ( ~ v1_tops_1(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | u1_struct_0(sK0) = k2_pre_topc(sK0,X0) ) ),
    inference(forward_demodulation,[],[f153,f117])).

fof(f153,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_struct_0(sK0) = k2_pre_topc(sK0,X0)
      | ~ v1_tops_1(X0,sK0) ) ),
    inference(resolution,[],[f67,f55])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = k2_struct_0(X0)
      | ~ v1_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> k2_pre_topc(X0,X1) = k2_struct_0(X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> k2_pre_topc(X0,X1) = k2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).

fof(f349,plain,
    ( v1_tops_1(sK1,sK0)
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | k1_xboole_0 = sK5(sK0,sK1,u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f348,f53])).

fof(f348,plain,
    ( k1_xboole_0 = sK5(sK0,sK1,u1_struct_0(sK0))
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | v1_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(duplicate_literal_removal,[],[f347])).

fof(f347,plain,
    ( k1_xboole_0 = sK5(sK0,sK1,u1_struct_0(sK0))
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | v1_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) ),
    inference(resolution,[],[f333,f274])).

fof(f274,plain,(
    ! [X0] :
      ( v3_pre_topc(sK5(sK0,X0,u1_struct_0(sK0)),sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | u1_struct_0(sK0) = k2_pre_topc(sK0,X0) ) ),
    inference(subsumption_resolution,[],[f273,f112])).

fof(f273,plain,(
    ! [X0] :
      ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | v3_pre_topc(sK5(sK0,X0,u1_struct_0(sK0)),sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | u1_struct_0(sK0) = k2_pre_topc(sK0,X0) ) ),
    inference(duplicate_literal_removal,[],[f272])).

fof(f272,plain,(
    ! [X0] :
      ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | v3_pre_topc(sK5(sK0,X0,u1_struct_0(sK0)),sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | u1_struct_0(sK0) = k2_pre_topc(sK0,X0)
      | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | u1_struct_0(sK0) = k2_pre_topc(sK0,X0) ) ),
    inference(resolution,[],[f271,f254])).

fof(f271,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(sK0,X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v3_pre_topc(sK5(sK0,X0,X1),sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_pre_topc(sK0,X0) = X1 ) ),
    inference(resolution,[],[f82,f55])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(sK5(X0,X1,X2),X0)
      | ~ r2_hidden(sK4(X0,X1,X2),X2)
      | k2_pre_topc(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f333,plain,
    ( ~ v3_pre_topc(sK5(sK0,sK1,u1_struct_0(sK0)),sK0)
    | k1_xboole_0 = sK5(sK0,sK1,u1_struct_0(sK0))
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | v1_tops_1(sK1,sK0) ),
    inference(duplicate_literal_removal,[],[f327])).

fof(f327,plain,
    ( u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | k1_xboole_0 = sK5(sK0,sK1,u1_struct_0(sK0))
    | ~ v3_pre_topc(sK5(sK0,sK1,u1_struct_0(sK0)),sK0)
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | v1_tops_1(sK1,sK0) ),
    inference(resolution,[],[f317,f283])).

fof(f283,plain,
    ( ~ m1_subset_1(sK5(sK0,sK1,u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = sK5(sK0,sK1,u1_struct_0(sK0))
    | ~ v3_pre_topc(sK5(sK0,sK1,u1_struct_0(sK0)),sK0)
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | v1_tops_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f282,f53])).

fof(f282,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | k1_xboole_0 = sK5(sK0,sK1,u1_struct_0(sK0))
    | ~ v3_pre_topc(sK5(sK0,sK1,u1_struct_0(sK0)),sK0)
    | ~ m1_subset_1(sK5(sK0,sK1,u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_tops_1(sK1,sK0) ),
    inference(resolution,[],[f280,f52])).

fof(f52,plain,(
    ! [X2] :
      ( ~ r1_xboole_0(sK1,X2)
      | k1_xboole_0 = X2
      | ~ v3_pre_topc(X2,sK0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_tops_1(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f280,plain,(
    ! [X0] :
      ( r1_xboole_0(X0,sK5(sK0,X0,u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | u1_struct_0(sK0) = k2_pre_topc(sK0,X0) ) ),
    inference(subsumption_resolution,[],[f279,f112])).

fof(f279,plain,(
    ! [X0] :
      ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | r1_xboole_0(X0,sK5(sK0,X0,u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | u1_struct_0(sK0) = k2_pre_topc(sK0,X0) ) ),
    inference(duplicate_literal_removal,[],[f278])).

fof(f278,plain,(
    ! [X0] :
      ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | r1_xboole_0(X0,sK5(sK0,X0,u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | u1_struct_0(sK0) = k2_pre_topc(sK0,X0)
      | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | u1_struct_0(sK0) = k2_pre_topc(sK0,X0) ) ),
    inference(resolution,[],[f276,f254])).

fof(f276,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(sK0,X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | r1_xboole_0(X0,sK5(sK0,X0,X1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_pre_topc(sK0,X0) = X1 ) ),
    inference(resolution,[],[f84,f55])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_xboole_0(X1,sK5(X0,X1,X2))
      | ~ r2_hidden(sK4(X0,X1,X2),X2)
      | k2_pre_topc(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f317,plain,
    ( m1_subset_1(sK5(sK0,sK1,u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) ),
    inference(resolution,[],[f316,f53])).

fof(f316,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_subset_1(sK5(sK0,X0,u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
      | u1_struct_0(sK0) = k2_pre_topc(sK0,X0) ) ),
    inference(subsumption_resolution,[],[f315,f112])).

fof(f315,plain,(
    ! [X0] :
      ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_subset_1(sK5(sK0,X0,u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | u1_struct_0(sK0) = k2_pre_topc(sK0,X0) ) ),
    inference(duplicate_literal_removal,[],[f314])).

fof(f314,plain,(
    ! [X0] :
      ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_subset_1(sK5(sK0,X0,u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | u1_struct_0(sK0) = k2_pre_topc(sK0,X0)
      | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | u1_struct_0(sK0) = k2_pre_topc(sK0,X0) ) ),
    inference(resolution,[],[f313,f254])).

fof(f313,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(sK0,X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_subset_1(sK5(sK0,X0,X1),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_pre_topc(sK0,X0) = X1 ) ),
    inference(resolution,[],[f81,f55])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(sK4(X0,X1,X2),X2)
      | k2_pre_topc(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f450,plain,(
    ! [X0] :
      ( r2_hidden(sK4(sK0,X0,u1_struct_0(sK0)),sK5(sK0,X0,u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | u1_struct_0(sK0) = k2_pre_topc(sK0,X0) ) ),
    inference(subsumption_resolution,[],[f449,f112])).

fof(f449,plain,(
    ! [X0] :
      ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK4(sK0,X0,u1_struct_0(sK0)),sK5(sK0,X0,u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | u1_struct_0(sK0) = k2_pre_topc(sK0,X0) ) ),
    inference(duplicate_literal_removal,[],[f448])).

fof(f448,plain,(
    ! [X0] :
      ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK4(sK0,X0,u1_struct_0(sK0)),sK5(sK0,X0,u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | u1_struct_0(sK0) = k2_pre_topc(sK0,X0)
      | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | u1_struct_0(sK0) = k2_pre_topc(sK0,X0) ) ),
    inference(resolution,[],[f447,f254])).

fof(f447,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(sK0,X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK4(sK0,X0,X1),sK5(sK0,X0,X1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_pre_topc(sK0,X0) = X1 ) ),
    inference(resolution,[],[f83,f55])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(sK4(X0,X1,X2),sK5(X0,X1,X2))
      | ~ r2_hidden(sK4(X0,X1,X2),X2)
      | k2_pre_topc(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) != k2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v1_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f773,plain,(
    ! [X2] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(X2))
      | r2_hidden(sK4(sK0,k1_xboole_0,sK2),X2) ) ),
    inference(resolution,[],[f766,f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(f766,plain,(
    r2_hidden(sK4(sK0,k1_xboole_0,sK2),sK2) ),
    inference(subsumption_resolution,[],[f760,f478])).

fof(f478,plain,(
    k1_xboole_0 != sK2 ),
    inference(resolution,[],[f474,f49])).

fof(f49,plain,
    ( ~ v1_tops_1(sK1,sK0)
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f28])).

fof(f760,plain,
    ( r2_hidden(sK4(sK0,k1_xboole_0,sK2),sK2)
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f747,f475])).

fof(f747,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK4(sK0,k1_xboole_0,X1),X1)
      | k1_xboole_0 = X1 ) ),
    inference(forward_demodulation,[],[f746,f166])).

fof(f746,plain,(
    ! [X1] :
      ( r2_hidden(sK4(sK0,k1_xboole_0,X1),X1)
      | k2_pre_topc(sK0,k1_xboole_0) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f742,f57])).

fof(f742,plain,(
    ! [X1] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK4(sK0,k1_xboole_0,X1),X1)
      | k2_pre_topc(sK0,k1_xboole_0) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(trivial_inequality_removal,[],[f736])).

fof(f736,plain,(
    ! [X1] :
      ( k1_xboole_0 != k1_xboole_0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK4(sK0,k1_xboole_0,X1),X1)
      | k2_pre_topc(sK0,k1_xboole_0) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(superposition,[],[f724,f123])).

fof(f724,plain,(
    ! [X2,X3] :
      ( k1_xboole_0 != k1_setfam_1(k2_tarski(X3,u1_struct_0(sK0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK4(sK0,X3,X2),X2)
      | k2_pre_topc(sK0,X3) = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f723,f254])).

fof(f723,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(sK4(sK0,X3,X2),u1_struct_0(sK0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK4(sK0,X3,X2),X2)
      | k2_pre_topc(sK0,X3) = X2
      | k1_xboole_0 != k1_setfam_1(k2_tarski(X3,u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f718,f112])).

fof(f718,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(sK4(sK0,X3,X2),u1_struct_0(sK0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK4(sK0,X3,X2),X2)
      | k2_pre_topc(sK0,X3) = X2
      | k1_xboole_0 != k1_setfam_1(k2_tarski(X3,u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f646,f120])).

fof(f646,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_pre_topc(X1,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(sK4(sK0,X2,X0),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK4(sK0,X2,X0),X0)
      | k2_pre_topc(sK0,X2) = X0
      | k1_xboole_0 != k1_setfam_1(k2_tarski(X2,X1)) ) ),
    inference(resolution,[],[f595,f105])).

fof(f595,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X2,sK0)
      | ~ r2_hidden(sK4(sK0,X0,X1),X2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK4(sK0,X0,X1),X1)
      | k2_pre_topc(sK0,X0) = X1 ) ),
    inference(resolution,[],[f85,f55])).

fof(f85,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X4,X0)
      | ~ r2_hidden(sK4(X0,X1,X2),X4)
      | ~ r1_xboole_0(X1,X4)
      | r2_hidden(sK4(X0,X1,X2),X2)
      | k2_pre_topc(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f946,plain,(
    ~ r2_hidden(sK4(sK0,k1_xboole_0,sK2),u1_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f945,f465])).

fof(f945,plain,(
    ~ r2_hidden(sK4(sK0,k1_xboole_0,sK2),k2_pre_topc(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f944,f53])).

fof(f944,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK4(sK0,k1_xboole_0,sK2),k2_pre_topc(sK0,sK1)) ),
    inference(resolution,[],[f791,f476])).

fof(f476,plain,(
    r1_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f474,f51])).

fof(f51,plain,
    ( ~ v1_tops_1(sK1,sK0)
    | r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f791,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,sK2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(sK4(sK0,k1_xboole_0,sK2),k2_pre_topc(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f790,f477])).

fof(f477,plain,(
    v3_pre_topc(sK2,sK0) ),
    inference(resolution,[],[f474,f50])).

fof(f50,plain,
    ( ~ v1_tops_1(sK1,sK0)
    | v3_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f790,plain,(
    ! [X0] :
      ( ~ v3_pre_topc(sK2,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_xboole_0(X0,sK2)
      | ~ r2_hidden(sK4(sK0,k1_xboole_0,sK2),k2_pre_topc(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f771,f475])).

fof(f771,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(sK2,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_xboole_0(X0,sK2)
      | ~ r2_hidden(sK4(sK0,k1_xboole_0,sK2),k2_pre_topc(sK0,X0)) ) ),
    inference(resolution,[],[f766,f300])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:37:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.49  % (3690)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.49  % (3681)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.50  % (3684)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.52  % (3706)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.52  % (3678)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (3704)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.53  % (3698)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.53  % (3700)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.54  % (3694)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.54  % (3705)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.54  % (3679)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (3694)Refutation not found, incomplete strategy% (3694)------------------------------
% 0.21/0.54  % (3694)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (3694)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (3694)Memory used [KB]: 10746
% 0.21/0.54  % (3694)Time elapsed: 0.129 s
% 0.21/0.54  % (3694)------------------------------
% 0.21/0.54  % (3694)------------------------------
% 0.21/0.54  % (3697)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.54  % (3689)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.55  % (3688)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (3703)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.55  % (3699)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.55  % (3680)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.55  % (3702)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.55  % (3677)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.55  % (3676)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.55  % (3695)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.56  % (3685)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.56  % (3686)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.56  % (3682)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.56  % (3683)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.56  % (3696)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.57  % (3693)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.57  % (3692)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.57/0.57  % (3701)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.57/0.58  % (3699)Refutation not found, incomplete strategy% (3699)------------------------------
% 1.57/0.58  % (3699)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.58  % (3699)Termination reason: Refutation not found, incomplete strategy
% 1.57/0.58  
% 1.57/0.58  % (3699)Memory used [KB]: 11001
% 1.57/0.58  % (3699)Time elapsed: 0.144 s
% 1.57/0.58  % (3699)------------------------------
% 1.57/0.58  % (3699)------------------------------
% 1.57/0.58  % (3691)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.77/0.59  % (3686)Refutation not found, incomplete strategy% (3686)------------------------------
% 1.77/0.59  % (3686)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.77/0.59  % (3686)Termination reason: Refutation not found, incomplete strategy
% 1.77/0.59  
% 1.77/0.59  % (3686)Memory used [KB]: 11001
% 1.77/0.59  % (3686)Time elapsed: 0.183 s
% 1.77/0.59  % (3686)------------------------------
% 1.77/0.59  % (3686)------------------------------
% 2.09/0.65  % (3682)Refutation found. Thanks to Tanya!
% 2.09/0.65  % SZS status Theorem for theBenchmark
% 2.09/0.65  % SZS output start Proof for theBenchmark
% 2.09/0.65  fof(f947,plain,(
% 2.09/0.65    $false),
% 2.09/0.65    inference(subsumption_resolution,[],[f946,f855])).
% 2.09/0.65  fof(f855,plain,(
% 2.09/0.65    r2_hidden(sK4(sK0,k1_xboole_0,sK2),u1_struct_0(sK0))),
% 2.09/0.65    inference(resolution,[],[f773,f475])).
% 2.09/0.65  fof(f475,plain,(
% 2.09/0.65    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.09/0.65    inference(resolution,[],[f474,f48])).
% 2.09/0.65  fof(f48,plain,(
% 2.09/0.65    ~v1_tops_1(sK1,sK0) | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.09/0.65    inference(cnf_transformation,[],[f28])).
% 2.09/0.65  fof(f28,plain,(
% 2.09/0.65    ? [X0] : (? [X1] : ((v1_tops_1(X1,X0) <~> ! [X2] : (~r1_xboole_0(X1,X2) | ~v3_pre_topc(X2,X0) | k1_xboole_0 = X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.09/0.65    inference(flattening,[],[f27])).
% 2.09/0.65  fof(f27,plain,(
% 2.09/0.65    ? [X0] : (? [X1] : ((v1_tops_1(X1,X0) <~> ! [X2] : ((~r1_xboole_0(X1,X2) | ~v3_pre_topc(X2,X0) | k1_xboole_0 = X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 2.09/0.65    inference(ennf_transformation,[],[f25])).
% 2.09/0.65  fof(f25,negated_conjecture,(
% 2.09/0.65    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_xboole_0(X1,X2) & v3_pre_topc(X2,X0) & k1_xboole_0 != X2)))))),
% 2.09/0.65    inference(negated_conjecture,[],[f24])).
% 2.09/0.65  fof(f24,conjecture,(
% 2.09/0.65    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_xboole_0(X1,X2) & v3_pre_topc(X2,X0) & k1_xboole_0 != X2)))))),
% 2.09/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_tops_1)).
% 2.09/0.65  fof(f474,plain,(
% 2.09/0.65    v1_tops_1(sK1,sK0)),
% 2.09/0.65    inference(subsumption_resolution,[],[f473,f55])).
% 2.09/0.65  fof(f55,plain,(
% 2.09/0.65    l1_pre_topc(sK0)),
% 2.09/0.65    inference(cnf_transformation,[],[f28])).
% 2.09/0.65  fof(f473,plain,(
% 2.09/0.65    ~l1_pre_topc(sK0) | v1_tops_1(sK1,sK0)),
% 2.09/0.65    inference(subsumption_resolution,[],[f472,f53])).
% 2.09/0.65  fof(f53,plain,(
% 2.09/0.65    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.09/0.65    inference(cnf_transformation,[],[f28])).
% 2.09/0.65  fof(f472,plain,(
% 2.09/0.65    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | v1_tops_1(sK1,sK0)),
% 2.09/0.65    inference(subsumption_resolution,[],[f468,f117])).
% 2.09/0.65  fof(f117,plain,(
% 2.09/0.65    u1_struct_0(sK0) = k2_struct_0(sK0)),
% 2.09/0.65    inference(resolution,[],[f113,f55])).
% 2.09/0.65  fof(f113,plain,(
% 2.09/0.65    ( ! [X0] : (~l1_pre_topc(X0) | u1_struct_0(X0) = k2_struct_0(X0)) )),
% 2.09/0.65    inference(resolution,[],[f61,f62])).
% 2.09/0.65  fof(f62,plain,(
% 2.09/0.65    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 2.09/0.65    inference(cnf_transformation,[],[f30])).
% 2.09/0.65  fof(f30,plain,(
% 2.09/0.65    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.09/0.65    inference(ennf_transformation,[],[f17])).
% 2.09/0.65  fof(f17,axiom,(
% 2.09/0.65    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.09/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 2.09/0.65  fof(f61,plain,(
% 2.09/0.65    ( ! [X0] : (~l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0)) )),
% 2.09/0.65    inference(cnf_transformation,[],[f29])).
% 2.09/0.65  fof(f29,plain,(
% 2.09/0.65    ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0))),
% 2.09/0.65    inference(ennf_transformation,[],[f16])).
% 2.09/0.65  fof(f16,axiom,(
% 2.09/0.65    ! [X0] : (l1_struct_0(X0) => u1_struct_0(X0) = k2_struct_0(X0))),
% 2.09/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 2.09/0.65  fof(f468,plain,(
% 2.09/0.65    u1_struct_0(sK0) != k2_struct_0(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | v1_tops_1(sK1,sK0)),
% 2.09/0.65    inference(superposition,[],[f66,f465])).
% 2.09/0.65  fof(f465,plain,(
% 2.09/0.65    u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)),
% 2.09/0.65    inference(subsumption_resolution,[],[f464,f53])).
% 2.09/0.65  fof(f464,plain,(
% 2.09/0.65    u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.09/0.65    inference(subsumption_resolution,[],[f463,f112])).
% 2.09/0.65  fof(f112,plain,(
% 2.09/0.65    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 2.09/0.65    inference(forward_demodulation,[],[f60,f56])).
% 2.09/0.65  fof(f56,plain,(
% 2.09/0.65    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 2.09/0.65    inference(cnf_transformation,[],[f7])).
% 2.09/0.65  fof(f7,axiom,(
% 2.09/0.65    ! [X0] : k2_subset_1(X0) = X0),
% 2.09/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 2.09/0.65  fof(f60,plain,(
% 2.09/0.65    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 2.09/0.65    inference(cnf_transformation,[],[f9])).
% 2.09/0.65  fof(f9,axiom,(
% 2.09/0.65    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 2.09/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 2.09/0.65  fof(f463,plain,(
% 2.09/0.65    u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.09/0.65    inference(duplicate_literal_removal,[],[f459])).
% 2.09/0.65  fof(f459,plain,(
% 2.09/0.65    u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)),
% 2.09/0.65    inference(resolution,[],[f458,f312])).
% 2.09/0.65  fof(f312,plain,(
% 2.09/0.65    ( ! [X2,X3] : (~r2_hidden(sK4(sK0,X2,X3),k1_xboole_0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X2) = X3) )),
% 2.09/0.65    inference(subsumption_resolution,[],[f311,f123])).
% 2.09/0.65  fof(f123,plain,(
% 2.09/0.65    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k2_tarski(k1_xboole_0,X0))) )),
% 2.09/0.65    inference(resolution,[],[f102,f115])).
% 2.09/0.65  fof(f115,plain,(
% 2.09/0.65    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.09/0.65    inference(resolution,[],[f96,f57])).
% 2.09/0.65  fof(f57,plain,(
% 2.09/0.65    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.09/0.65    inference(cnf_transformation,[],[f11])).
% 2.09/0.65  fof(f11,axiom,(
% 2.09/0.65    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.09/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 2.09/0.65  fof(f96,plain,(
% 2.09/0.65    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 2.09/0.65    inference(cnf_transformation,[],[f45])).
% 2.09/0.65  fof(f45,plain,(
% 2.09/0.65    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 2.09/0.65    inference(ennf_transformation,[],[f26])).
% 2.09/0.65  fof(f26,plain,(
% 2.09/0.65    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 2.09/0.65    inference(unused_predicate_definition_removal,[],[f13])).
% 2.09/0.65  fof(f13,axiom,(
% 2.09/0.65    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.09/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 2.09/0.65  fof(f102,plain,(
% 2.09/0.65    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_setfam_1(k2_tarski(X0,X1)) = X0) )),
% 2.09/0.65    inference(definition_unfolding,[],[f91,f88])).
% 2.09/0.65  fof(f88,plain,(
% 2.09/0.65    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.09/0.65    inference(cnf_transformation,[],[f12])).
% 2.09/0.65  fof(f12,axiom,(
% 2.09/0.65    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 2.09/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 2.09/0.65  fof(f91,plain,(
% 2.09/0.65    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 2.09/0.65    inference(cnf_transformation,[],[f42])).
% 2.09/0.65  fof(f42,plain,(
% 2.09/0.65    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.09/0.65    inference(ennf_transformation,[],[f3])).
% 2.09/0.65  fof(f3,axiom,(
% 2.09/0.65    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.09/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 2.09/0.65  fof(f311,plain,(
% 2.09/0.65    ( ! [X2,X3] : (~r2_hidden(sK4(sK0,X2,X3),k1_xboole_0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X2) = X3 | k1_xboole_0 != k1_setfam_1(k2_tarski(k1_xboole_0,u1_struct_0(sK0)))) )),
% 2.09/0.65    inference(subsumption_resolution,[],[f306,f57])).
% 2.09/0.65  fof(f306,plain,(
% 2.09/0.65    ( ! [X2,X3] : (~r2_hidden(sK4(sK0,X2,X3),k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X2) = X3 | k1_xboole_0 != k1_setfam_1(k2_tarski(k1_xboole_0,u1_struct_0(sK0)))) )),
% 2.09/0.65    inference(superposition,[],[f304,f166])).
% 2.09/0.65  fof(f166,plain,(
% 2.09/0.65    k1_xboole_0 = k2_pre_topc(sK0,k1_xboole_0)),
% 2.09/0.65    inference(subsumption_resolution,[],[f165,f55])).
% 2.09/0.65  fof(f165,plain,(
% 2.09/0.65    ~l1_pre_topc(sK0) | k1_xboole_0 = k2_pre_topc(sK0,k1_xboole_0)),
% 2.09/0.65    inference(subsumption_resolution,[],[f164,f57])).
% 2.09/0.65  fof(f164,plain,(
% 2.09/0.65    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | k1_xboole_0 = k2_pre_topc(sK0,k1_xboole_0)),
% 2.09/0.65    inference(resolution,[],[f162,f65])).
% 2.09/0.65  fof(f65,plain,(
% 2.09/0.65    ( ! [X0,X1] : (~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | k2_pre_topc(X0,X1) = X1) )),
% 2.09/0.65    inference(cnf_transformation,[],[f33])).
% 2.09/0.65  fof(f33,plain,(
% 2.09/0.65    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.09/0.65    inference(flattening,[],[f32])).
% 2.09/0.65  fof(f32,plain,(
% 2.09/0.65    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.09/0.65    inference(ennf_transformation,[],[f18])).
% 2.09/0.65  fof(f18,axiom,(
% 2.09/0.65    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 2.09/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).
% 2.09/0.65  fof(f162,plain,(
% 2.09/0.65    v4_pre_topc(k1_xboole_0,sK0)),
% 2.09/0.65    inference(subsumption_resolution,[],[f161,f57])).
% 2.09/0.65  fof(f161,plain,(
% 2.09/0.65    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(k1_xboole_0,sK0)),
% 2.09/0.65    inference(subsumption_resolution,[],[f159,f120])).
% 2.09/0.65  fof(f120,plain,(
% 2.09/0.65    v3_pre_topc(u1_struct_0(sK0),sK0)),
% 2.09/0.65    inference(subsumption_resolution,[],[f119,f54])).
% 2.09/0.65  fof(f54,plain,(
% 2.09/0.65    v2_pre_topc(sK0)),
% 2.09/0.65    inference(cnf_transformation,[],[f28])).
% 2.09/0.65  fof(f119,plain,(
% 2.09/0.65    v3_pre_topc(u1_struct_0(sK0),sK0) | ~v2_pre_topc(sK0)),
% 2.09/0.65    inference(subsumption_resolution,[],[f118,f55])).
% 2.09/0.65  fof(f118,plain,(
% 2.09/0.65    v3_pre_topc(u1_struct_0(sK0),sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 2.09/0.65    inference(superposition,[],[f87,f117])).
% 2.09/0.65  fof(f87,plain,(
% 2.09/0.65    ( ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.09/0.65    inference(cnf_transformation,[],[f41])).
% 2.09/0.65  fof(f41,plain,(
% 2.09/0.65    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.09/0.65    inference(flattening,[],[f40])).
% 2.09/0.65  fof(f40,plain,(
% 2.09/0.65    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.09/0.65    inference(ennf_transformation,[],[f21])).
% 2.09/0.65  fof(f21,axiom,(
% 2.09/0.65    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k2_struct_0(X0),X0))),
% 2.09/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_tops_1)).
% 2.09/0.65  fof(f159,plain,(
% 2.09/0.65    ~v3_pre_topc(u1_struct_0(sK0),sK0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(k1_xboole_0,sK0)),
% 2.09/0.65    inference(superposition,[],[f158,f132])).
% 2.09/0.65  fof(f132,plain,(
% 2.09/0.65    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 2.09/0.65    inference(forward_demodulation,[],[f131,f111])).
% 2.09/0.65  fof(f111,plain,(
% 2.09/0.65    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.09/0.65    inference(forward_demodulation,[],[f100,f99])).
% 2.09/0.65  fof(f99,plain,(
% 2.09/0.65    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0))) )),
% 2.09/0.65    inference(definition_unfolding,[],[f58,f88])).
% 2.09/0.65  fof(f58,plain,(
% 2.09/0.65    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 2.09/0.65    inference(cnf_transformation,[],[f4])).
% 2.09/0.65  fof(f4,axiom,(
% 2.09/0.65    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 2.09/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 2.09/0.65  fof(f100,plain,(
% 2.09/0.65    ( ! [X0] : (k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = X0) )),
% 2.09/0.65    inference(definition_unfolding,[],[f59,f98])).
% 2.09/0.65  fof(f98,plain,(
% 2.09/0.65    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 2.09/0.65    inference(definition_unfolding,[],[f89,f88])).
% 2.09/0.65  fof(f89,plain,(
% 2.09/0.65    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.09/0.65    inference(cnf_transformation,[],[f2])).
% 2.09/0.65  fof(f2,axiom,(
% 2.09/0.65    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.09/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.09/0.65  fof(f59,plain,(
% 2.09/0.65    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.09/0.65    inference(cnf_transformation,[],[f5])).
% 2.09/0.65  fof(f5,axiom,(
% 2.09/0.65    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 2.09/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 2.09/0.65  fof(f131,plain,(
% 2.09/0.65    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = k3_subset_1(X0,k1_xboole_0)) )),
% 2.09/0.65    inference(forward_demodulation,[],[f129,f99])).
% 2.09/0.65  fof(f129,plain,(
% 2.09/0.65    ( ! [X0] : (k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = k3_subset_1(X0,k1_xboole_0)) )),
% 2.09/0.65    inference(resolution,[],[f103,f57])).
% 2.09/0.65  fof(f103,plain,(
% 2.09/0.65    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 2.09/0.65    inference(definition_unfolding,[],[f92,f98])).
% 2.09/0.65  fof(f92,plain,(
% 2.09/0.65    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 2.09/0.65    inference(cnf_transformation,[],[f43])).
% 2.09/0.65  fof(f43,plain,(
% 2.09/0.65    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.09/0.65    inference(ennf_transformation,[],[f8])).
% 2.09/0.65  fof(f8,axiom,(
% 2.09/0.65    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 2.09/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 2.09/0.65  fof(f158,plain,(
% 2.09/0.65    ( ! [X0] : (~v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(X0,sK0)) )),
% 2.09/0.65    inference(resolution,[],[f68,f55])).
% 2.09/0.65  fof(f68,plain,(
% 2.09/0.65    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | v4_pre_topc(X1,X0)) )),
% 2.09/0.65    inference(cnf_transformation,[],[f35])).
% 2.09/0.65  fof(f35,plain,(
% 2.09/0.65    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.09/0.65    inference(ennf_transformation,[],[f23])).
% 2.09/0.65  fof(f23,axiom,(
% 2.09/0.65    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 2.09/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tops_1)).
% 2.09/0.65  fof(f304,plain,(
% 2.09/0.65    ( ! [X2,X0,X1] : (~r2_hidden(sK4(sK0,X1,X2),k2_pre_topc(sK0,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X1) = X2 | k1_xboole_0 != k1_setfam_1(k2_tarski(X0,u1_struct_0(sK0)))) )),
% 2.09/0.65    inference(resolution,[],[f303,f105])).
% 2.09/0.65  fof(f105,plain,(
% 2.09/0.65    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.09/0.65    inference(definition_unfolding,[],[f94,f88])).
% 2.09/0.65  fof(f94,plain,(
% 2.09/0.65    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) )),
% 2.09/0.65    inference(cnf_transformation,[],[f1])).
% 2.09/0.65  fof(f1,axiom,(
% 2.09/0.65    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 2.09/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 2.09/0.65  fof(f303,plain,(
% 2.09/0.65    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK4(sK0,X1,X2),k2_pre_topc(sK0,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X1) = X2) )),
% 2.09/0.65    inference(subsumption_resolution,[],[f302,f120])).
% 2.09/0.65  fof(f302,plain,(
% 2.09/0.65    ( ! [X2,X0,X1] : (~v3_pre_topc(u1_struct_0(sK0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_xboole_0(X0,u1_struct_0(sK0)) | ~r2_hidden(sK4(sK0,X1,X2),k2_pre_topc(sK0,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X1) = X2) )),
% 2.09/0.65    inference(subsumption_resolution,[],[f301,f112])).
% 2.09/0.65  fof(f301,plain,(
% 2.09/0.65    ( ! [X2,X0,X1] : (~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(u1_struct_0(sK0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_xboole_0(X0,u1_struct_0(sK0)) | ~r2_hidden(sK4(sK0,X1,X2),k2_pre_topc(sK0,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X1) = X2) )),
% 2.09/0.65    inference(resolution,[],[f300,f254])).
% 2.09/0.65  fof(f254,plain,(
% 2.09/0.65    ( ! [X0,X1] : (r2_hidden(sK4(sK0,X0,X1),u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = X1) )),
% 2.09/0.65    inference(resolution,[],[f86,f55])).
% 2.09/0.65  fof(f86,plain,(
% 2.09/0.65    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | r2_hidden(sK4(X0,X1,X2),u1_struct_0(X0)) | k2_pre_topc(X0,X1) = X2) )),
% 2.09/0.65    inference(cnf_transformation,[],[f39])).
% 2.09/0.65  fof(f39,plain,(
% 2.09/0.65    ! [X0] : (! [X1] : (! [X2] : ((k2_pre_topc(X0,X1) = X2 <=> ! [X3] : ((r2_hidden(X3,X2) <=> ! [X4] : (~r1_xboole_0(X1,X4) | ~r2_hidden(X3,X4) | ~v3_pre_topc(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.09/0.65    inference(flattening,[],[f38])).
% 2.09/0.65  fof(f38,plain,(
% 2.09/0.65    ! [X0] : (! [X1] : (! [X2] : ((k2_pre_topc(X0,X1) = X2 <=> ! [X3] : ((r2_hidden(X3,X2) <=> ! [X4] : ((~r1_xboole_0(X1,X4) | ~r2_hidden(X3,X4) | ~v3_pre_topc(X4,X0)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.09/0.65    inference(ennf_transformation,[],[f15])).
% 2.09/0.65  fof(f15,axiom,(
% 2.09/0.65    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (k2_pre_topc(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) <=> ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_xboole_0(X1,X4) & r2_hidden(X3,X4) & v3_pre_topc(X4,X0)))))))))),
% 2.09/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_pre_topc)).
% 2.09/0.65  fof(f300,plain,(
% 2.09/0.65    ( ! [X2,X0,X1] : (~r2_hidden(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X2,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_xboole_0(X0,X2) | ~r2_hidden(X1,k2_pre_topc(sK0,X0))) )),
% 2.09/0.65    inference(subsumption_resolution,[],[f299,f97])).
% 2.09/0.65  fof(f97,plain,(
% 2.09/0.65    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2)) )),
% 2.09/0.65    inference(cnf_transformation,[],[f47])).
% 2.09/0.65  fof(f47,plain,(
% 2.09/0.65    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.09/0.65    inference(flattening,[],[f46])).
% 2.09/0.65  fof(f46,plain,(
% 2.09/0.65    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 2.09/0.65    inference(ennf_transformation,[],[f14])).
% 2.09/0.65  fof(f14,axiom,(
% 2.09/0.65    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 2.09/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 2.09/0.65  fof(f299,plain,(
% 2.09/0.65    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X2,sK0) | ~r2_hidden(X1,X2) | ~r1_xboole_0(X0,X2) | ~r2_hidden(X1,k2_pre_topc(sK0,X0))) )),
% 2.09/0.65    inference(resolution,[],[f74,f55])).
% 2.09/0.65  fof(f74,plain,(
% 2.09/0.65    ( ! [X2,X0,X3,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X3,X0) | ~r2_hidden(X2,X3) | ~r1_xboole_0(X1,X3) | ~r2_hidden(X2,k2_pre_topc(X0,X1))) )),
% 2.09/0.65    inference(cnf_transformation,[],[f37])).
% 2.09/0.65  fof(f37,plain,(
% 2.09/0.65    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k2_pre_topc(X0,X1)) <=> (! [X3] : (~r1_xboole_0(X1,X3) | ~r2_hidden(X2,X3) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & ~v2_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.09/0.65    inference(flattening,[],[f36])).
% 2.09/0.65  fof(f36,plain,(
% 2.09/0.65    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k2_pre_topc(X0,X1)) <=> (! [X3] : ((~r1_xboole_0(X1,X3) | ~r2_hidden(X2,X3) | ~v3_pre_topc(X3,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & ~v2_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.09/0.65    inference(ennf_transformation,[],[f19])).
% 2.09/0.65  fof(f19,axiom,(
% 2.09/0.65    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,k2_pre_topc(X0,X1)) <=> (! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_xboole_0(X1,X3) & r2_hidden(X2,X3) & v3_pre_topc(X3,X0))) & ~v2_struct_0(X0))))))),
% 2.09/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_pre_topc)).
% 2.09/0.65  fof(f458,plain,(
% 2.09/0.65    r2_hidden(sK4(sK0,sK1,u1_struct_0(sK0)),k1_xboole_0) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)),
% 2.09/0.65    inference(subsumption_resolution,[],[f455,f53])).
% 2.09/0.65  fof(f455,plain,(
% 2.09/0.65    r2_hidden(sK4(sK0,sK1,u1_struct_0(sK0)),k1_xboole_0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)),
% 2.09/0.65    inference(duplicate_literal_removal,[],[f454])).
% 2.09/0.65  fof(f454,plain,(
% 2.09/0.65    r2_hidden(sK4(sK0,sK1,u1_struct_0(sK0)),k1_xboole_0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)),
% 2.09/0.65    inference(superposition,[],[f450,f356])).
% 2.09/0.65  fof(f356,plain,(
% 2.09/0.65    k1_xboole_0 = sK5(sK0,sK1,u1_struct_0(sK0)) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)),
% 2.09/0.65    inference(subsumption_resolution,[],[f355,f53])).
% 2.09/0.65  fof(f355,plain,(
% 2.09/0.65    u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) | k1_xboole_0 = sK5(sK0,sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.09/0.65    inference(duplicate_literal_removal,[],[f354])).
% 2.09/0.65  fof(f354,plain,(
% 2.09/0.65    u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) | k1_xboole_0 = sK5(sK0,sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)),
% 2.09/0.65    inference(resolution,[],[f349,f154])).
% 2.09/0.65  fof(f154,plain,(
% 2.09/0.65    ( ! [X0] : (~v1_tops_1(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_pre_topc(sK0,X0)) )),
% 2.09/0.65    inference(forward_demodulation,[],[f153,f117])).
% 2.09/0.65  fof(f153,plain,(
% 2.09/0.65    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_struct_0(sK0) = k2_pre_topc(sK0,X0) | ~v1_tops_1(X0,sK0)) )),
% 2.09/0.65    inference(resolution,[],[f67,f55])).
% 2.09/0.65  fof(f67,plain,(
% 2.09/0.65    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = k2_struct_0(X0) | ~v1_tops_1(X1,X0)) )),
% 2.09/0.65    inference(cnf_transformation,[],[f34])).
% 2.09/0.65  fof(f34,plain,(
% 2.09/0.65    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> k2_pre_topc(X0,X1) = k2_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.09/0.65    inference(ennf_transformation,[],[f20])).
% 2.09/0.65  fof(f20,axiom,(
% 2.09/0.65    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> k2_pre_topc(X0,X1) = k2_struct_0(X0))))),
% 2.09/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).
% 2.09/0.65  fof(f349,plain,(
% 2.09/0.65    v1_tops_1(sK1,sK0) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) | k1_xboole_0 = sK5(sK0,sK1,u1_struct_0(sK0))),
% 2.09/0.65    inference(subsumption_resolution,[],[f348,f53])).
% 2.09/0.65  fof(f348,plain,(
% 2.09/0.65    k1_xboole_0 = sK5(sK0,sK1,u1_struct_0(sK0)) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) | v1_tops_1(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.09/0.65    inference(duplicate_literal_removal,[],[f347])).
% 2.09/0.65  fof(f347,plain,(
% 2.09/0.65    k1_xboole_0 = sK5(sK0,sK1,u1_struct_0(sK0)) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) | v1_tops_1(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)),
% 2.09/0.65    inference(resolution,[],[f333,f274])).
% 2.09/0.65  fof(f274,plain,(
% 2.09/0.65    ( ! [X0] : (v3_pre_topc(sK5(sK0,X0,u1_struct_0(sK0)),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_pre_topc(sK0,X0)) )),
% 2.09/0.65    inference(subsumption_resolution,[],[f273,f112])).
% 2.09/0.65  fof(f273,plain,(
% 2.09/0.65    ( ! [X0] : (~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(sK5(sK0,X0,u1_struct_0(sK0)),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_pre_topc(sK0,X0)) )),
% 2.09/0.65    inference(duplicate_literal_removal,[],[f272])).
% 2.09/0.65  fof(f272,plain,(
% 2.09/0.65    ( ! [X0] : (~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(sK5(sK0,X0,u1_struct_0(sK0)),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_pre_topc(sK0,X0) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_pre_topc(sK0,X0)) )),
% 2.09/0.65    inference(resolution,[],[f271,f254])).
% 2.09/0.65  fof(f271,plain,(
% 2.09/0.65    ( ! [X0,X1] : (~r2_hidden(sK4(sK0,X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(sK5(sK0,X0,X1),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = X1) )),
% 2.09/0.65    inference(resolution,[],[f82,f55])).
% 2.09/0.65  fof(f82,plain,(
% 2.09/0.65    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(sK5(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2) | k2_pre_topc(X0,X1) = X2) )),
% 2.09/0.65    inference(cnf_transformation,[],[f39])).
% 2.09/0.65  fof(f333,plain,(
% 2.09/0.65    ~v3_pre_topc(sK5(sK0,sK1,u1_struct_0(sK0)),sK0) | k1_xboole_0 = sK5(sK0,sK1,u1_struct_0(sK0)) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) | v1_tops_1(sK1,sK0)),
% 2.09/0.65    inference(duplicate_literal_removal,[],[f327])).
% 2.09/0.65  fof(f327,plain,(
% 2.09/0.65    u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) | k1_xboole_0 = sK5(sK0,sK1,u1_struct_0(sK0)) | ~v3_pre_topc(sK5(sK0,sK1,u1_struct_0(sK0)),sK0) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) | v1_tops_1(sK1,sK0)),
% 2.09/0.65    inference(resolution,[],[f317,f283])).
% 2.09/0.65  fof(f283,plain,(
% 2.09/0.65    ~m1_subset_1(sK5(sK0,sK1,u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = sK5(sK0,sK1,u1_struct_0(sK0)) | ~v3_pre_topc(sK5(sK0,sK1,u1_struct_0(sK0)),sK0) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) | v1_tops_1(sK1,sK0)),
% 2.09/0.65    inference(subsumption_resolution,[],[f282,f53])).
% 2.09/0.65  fof(f282,plain,(
% 2.09/0.65    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) | k1_xboole_0 = sK5(sK0,sK1,u1_struct_0(sK0)) | ~v3_pre_topc(sK5(sK0,sK1,u1_struct_0(sK0)),sK0) | ~m1_subset_1(sK5(sK0,sK1,u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) | v1_tops_1(sK1,sK0)),
% 2.09/0.65    inference(resolution,[],[f280,f52])).
% 2.09/0.65  fof(f52,plain,(
% 2.09/0.65    ( ! [X2] : (~r1_xboole_0(sK1,X2) | k1_xboole_0 = X2 | ~v3_pre_topc(X2,sK0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | v1_tops_1(sK1,sK0)) )),
% 2.09/0.65    inference(cnf_transformation,[],[f28])).
% 2.09/0.65  fof(f280,plain,(
% 2.09/0.65    ( ! [X0] : (r1_xboole_0(X0,sK5(sK0,X0,u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_pre_topc(sK0,X0)) )),
% 2.09/0.65    inference(subsumption_resolution,[],[f279,f112])).
% 2.09/0.65  fof(f279,plain,(
% 2.09/0.65    ( ! [X0] : (~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | r1_xboole_0(X0,sK5(sK0,X0,u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_pre_topc(sK0,X0)) )),
% 2.09/0.65    inference(duplicate_literal_removal,[],[f278])).
% 2.09/0.65  fof(f278,plain,(
% 2.09/0.65    ( ! [X0] : (~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | r1_xboole_0(X0,sK5(sK0,X0,u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_pre_topc(sK0,X0) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_pre_topc(sK0,X0)) )),
% 2.09/0.65    inference(resolution,[],[f276,f254])).
% 2.09/0.65  fof(f276,plain,(
% 2.09/0.65    ( ! [X0,X1] : (~r2_hidden(sK4(sK0,X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | r1_xboole_0(X0,sK5(sK0,X0,X1)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = X1) )),
% 2.09/0.65    inference(resolution,[],[f84,f55])).
% 2.09/0.65  fof(f84,plain,(
% 2.09/0.65    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | r1_xboole_0(X1,sK5(X0,X1,X2)) | ~r2_hidden(sK4(X0,X1,X2),X2) | k2_pre_topc(X0,X1) = X2) )),
% 2.09/0.65    inference(cnf_transformation,[],[f39])).
% 2.09/0.65  fof(f317,plain,(
% 2.09/0.65    m1_subset_1(sK5(sK0,sK1,u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)),
% 2.09/0.65    inference(resolution,[],[f316,f53])).
% 2.09/0.65  fof(f316,plain,(
% 2.09/0.65    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(sK5(sK0,X0,u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_pre_topc(sK0,X0)) )),
% 2.09/0.65    inference(subsumption_resolution,[],[f315,f112])).
% 2.09/0.65  fof(f315,plain,(
% 2.09/0.65    ( ! [X0] : (~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(sK5(sK0,X0,u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_pre_topc(sK0,X0)) )),
% 2.09/0.65    inference(duplicate_literal_removal,[],[f314])).
% 2.09/0.65  fof(f314,plain,(
% 2.09/0.65    ( ! [X0] : (~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(sK5(sK0,X0,u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_pre_topc(sK0,X0) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_pre_topc(sK0,X0)) )),
% 2.09/0.65    inference(resolution,[],[f313,f254])).
% 2.09/0.65  fof(f313,plain,(
% 2.09/0.65    ( ! [X0,X1] : (~r2_hidden(sK4(sK0,X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(sK5(sK0,X0,X1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = X1) )),
% 2.09/0.65    inference(resolution,[],[f81,f55])).
% 2.09/0.65  fof(f81,plain,(
% 2.09/0.65    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(sK4(X0,X1,X2),X2) | k2_pre_topc(X0,X1) = X2) )),
% 2.09/0.65    inference(cnf_transformation,[],[f39])).
% 2.09/0.65  fof(f450,plain,(
% 2.09/0.65    ( ! [X0] : (r2_hidden(sK4(sK0,X0,u1_struct_0(sK0)),sK5(sK0,X0,u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_pre_topc(sK0,X0)) )),
% 2.09/0.65    inference(subsumption_resolution,[],[f449,f112])).
% 2.09/0.65  fof(f449,plain,(
% 2.09/0.65    ( ! [X0] : (~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK4(sK0,X0,u1_struct_0(sK0)),sK5(sK0,X0,u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_pre_topc(sK0,X0)) )),
% 2.09/0.65    inference(duplicate_literal_removal,[],[f448])).
% 2.09/0.65  fof(f448,plain,(
% 2.09/0.65    ( ! [X0] : (~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK4(sK0,X0,u1_struct_0(sK0)),sK5(sK0,X0,u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_pre_topc(sK0,X0) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_pre_topc(sK0,X0)) )),
% 2.09/0.65    inference(resolution,[],[f447,f254])).
% 2.09/0.65  fof(f447,plain,(
% 2.09/0.65    ( ! [X0,X1] : (~r2_hidden(sK4(sK0,X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK4(sK0,X0,X1),sK5(sK0,X0,X1)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = X1) )),
% 2.09/0.65    inference(resolution,[],[f83,f55])).
% 2.09/0.65  fof(f83,plain,(
% 2.09/0.65    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | r2_hidden(sK4(X0,X1,X2),sK5(X0,X1,X2)) | ~r2_hidden(sK4(X0,X1,X2),X2) | k2_pre_topc(X0,X1) = X2) )),
% 2.09/0.65    inference(cnf_transformation,[],[f39])).
% 2.09/0.65  fof(f66,plain,(
% 2.09/0.65    ( ! [X0,X1] : (k2_pre_topc(X0,X1) != k2_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v1_tops_1(X1,X0)) )),
% 2.09/0.65    inference(cnf_transformation,[],[f34])).
% 2.09/0.65  fof(f773,plain,(
% 2.09/0.65    ( ! [X2] : (~m1_subset_1(sK2,k1_zfmisc_1(X2)) | r2_hidden(sK4(sK0,k1_xboole_0,sK2),X2)) )),
% 2.09/0.65    inference(resolution,[],[f766,f93])).
% 2.09/0.65  fof(f93,plain,(
% 2.09/0.65    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | r2_hidden(X2,X0)) )),
% 2.09/0.65    inference(cnf_transformation,[],[f44])).
% 2.09/0.65  fof(f44,plain,(
% 2.09/0.65    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.09/0.65    inference(ennf_transformation,[],[f10])).
% 2.09/0.65  fof(f10,axiom,(
% 2.09/0.65    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 2.09/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 2.09/0.65  fof(f766,plain,(
% 2.09/0.65    r2_hidden(sK4(sK0,k1_xboole_0,sK2),sK2)),
% 2.09/0.65    inference(subsumption_resolution,[],[f760,f478])).
% 2.09/0.65  fof(f478,plain,(
% 2.09/0.65    k1_xboole_0 != sK2),
% 2.09/0.65    inference(resolution,[],[f474,f49])).
% 2.09/0.65  fof(f49,plain,(
% 2.09/0.65    ~v1_tops_1(sK1,sK0) | k1_xboole_0 != sK2),
% 2.09/0.65    inference(cnf_transformation,[],[f28])).
% 2.09/0.65  fof(f760,plain,(
% 2.09/0.65    r2_hidden(sK4(sK0,k1_xboole_0,sK2),sK2) | k1_xboole_0 = sK2),
% 2.09/0.65    inference(resolution,[],[f747,f475])).
% 2.09/0.65  fof(f747,plain,(
% 2.09/0.65    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK4(sK0,k1_xboole_0,X1),X1) | k1_xboole_0 = X1) )),
% 2.09/0.65    inference(forward_demodulation,[],[f746,f166])).
% 2.09/0.65  fof(f746,plain,(
% 2.09/0.65    ( ! [X1] : (r2_hidden(sK4(sK0,k1_xboole_0,X1),X1) | k2_pre_topc(sK0,k1_xboole_0) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 2.09/0.65    inference(subsumption_resolution,[],[f742,f57])).
% 2.09/0.65  fof(f742,plain,(
% 2.09/0.65    ( ! [X1] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK4(sK0,k1_xboole_0,X1),X1) | k2_pre_topc(sK0,k1_xboole_0) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 2.09/0.65    inference(trivial_inequality_removal,[],[f736])).
% 2.09/0.65  fof(f736,plain,(
% 2.09/0.65    ( ! [X1] : (k1_xboole_0 != k1_xboole_0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK4(sK0,k1_xboole_0,X1),X1) | k2_pre_topc(sK0,k1_xboole_0) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 2.09/0.65    inference(superposition,[],[f724,f123])).
% 2.09/0.65  fof(f724,plain,(
% 2.09/0.65    ( ! [X2,X3] : (k1_xboole_0 != k1_setfam_1(k2_tarski(X3,u1_struct_0(sK0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK4(sK0,X3,X2),X2) | k2_pre_topc(sK0,X3) = X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 2.09/0.65    inference(subsumption_resolution,[],[f723,f254])).
% 2.09/0.65  fof(f723,plain,(
% 2.09/0.65    ( ! [X2,X3] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK4(sK0,X3,X2),u1_struct_0(sK0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK4(sK0,X3,X2),X2) | k2_pre_topc(sK0,X3) = X2 | k1_xboole_0 != k1_setfam_1(k2_tarski(X3,u1_struct_0(sK0)))) )),
% 2.09/0.65    inference(subsumption_resolution,[],[f718,f112])).
% 2.09/0.65  fof(f718,plain,(
% 2.09/0.65    ( ! [X2,X3] : (~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK4(sK0,X3,X2),u1_struct_0(sK0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK4(sK0,X3,X2),X2) | k2_pre_topc(sK0,X3) = X2 | k1_xboole_0 != k1_setfam_1(k2_tarski(X3,u1_struct_0(sK0)))) )),
% 2.09/0.65    inference(resolution,[],[f646,f120])).
% 2.09/0.65  fof(f646,plain,(
% 2.09/0.65    ( ! [X2,X0,X1] : (~v3_pre_topc(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK4(sK0,X2,X0),X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK4(sK0,X2,X0),X0) | k2_pre_topc(sK0,X2) = X0 | k1_xboole_0 != k1_setfam_1(k2_tarski(X2,X1))) )),
% 2.09/0.65    inference(resolution,[],[f595,f105])).
% 2.09/0.65  fof(f595,plain,(
% 2.09/0.65    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X2,sK0) | ~r2_hidden(sK4(sK0,X0,X1),X2) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK4(sK0,X0,X1),X1) | k2_pre_topc(sK0,X0) = X1) )),
% 2.09/0.65    inference(resolution,[],[f85,f55])).
% 2.09/0.65  fof(f85,plain,(
% 2.09/0.65    ( ! [X4,X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X4,X0) | ~r2_hidden(sK4(X0,X1,X2),X4) | ~r1_xboole_0(X1,X4) | r2_hidden(sK4(X0,X1,X2),X2) | k2_pre_topc(X0,X1) = X2) )),
% 2.09/0.65    inference(cnf_transformation,[],[f39])).
% 2.09/0.65  fof(f946,plain,(
% 2.09/0.65    ~r2_hidden(sK4(sK0,k1_xboole_0,sK2),u1_struct_0(sK0))),
% 2.09/0.65    inference(forward_demodulation,[],[f945,f465])).
% 2.09/0.65  fof(f945,plain,(
% 2.09/0.65    ~r2_hidden(sK4(sK0,k1_xboole_0,sK2),k2_pre_topc(sK0,sK1))),
% 2.09/0.65    inference(subsumption_resolution,[],[f944,f53])).
% 2.09/0.65  fof(f944,plain,(
% 2.09/0.65    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK4(sK0,k1_xboole_0,sK2),k2_pre_topc(sK0,sK1))),
% 2.09/0.65    inference(resolution,[],[f791,f476])).
% 2.09/0.65  fof(f476,plain,(
% 2.09/0.65    r1_xboole_0(sK1,sK2)),
% 2.09/0.65    inference(resolution,[],[f474,f51])).
% 2.09/0.65  fof(f51,plain,(
% 2.09/0.65    ~v1_tops_1(sK1,sK0) | r1_xboole_0(sK1,sK2)),
% 2.09/0.65    inference(cnf_transformation,[],[f28])).
% 2.09/0.65  fof(f791,plain,(
% 2.09/0.65    ( ! [X0] : (~r1_xboole_0(X0,sK2) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK4(sK0,k1_xboole_0,sK2),k2_pre_topc(sK0,X0))) )),
% 2.09/0.65    inference(subsumption_resolution,[],[f790,f477])).
% 2.09/0.65  fof(f477,plain,(
% 2.09/0.65    v3_pre_topc(sK2,sK0)),
% 2.09/0.65    inference(resolution,[],[f474,f50])).
% 2.09/0.65  fof(f50,plain,(
% 2.09/0.65    ~v1_tops_1(sK1,sK0) | v3_pre_topc(sK2,sK0)),
% 2.09/0.65    inference(cnf_transformation,[],[f28])).
% 2.09/0.65  fof(f790,plain,(
% 2.09/0.65    ( ! [X0] : (~v3_pre_topc(sK2,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_xboole_0(X0,sK2) | ~r2_hidden(sK4(sK0,k1_xboole_0,sK2),k2_pre_topc(sK0,X0))) )),
% 2.09/0.65    inference(subsumption_resolution,[],[f771,f475])).
% 2.09/0.65  fof(f771,plain,(
% 2.09/0.65    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(sK2,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_xboole_0(X0,sK2) | ~r2_hidden(sK4(sK0,k1_xboole_0,sK2),k2_pre_topc(sK0,X0))) )),
% 2.09/0.65    inference(resolution,[],[f766,f300])).
% 2.09/0.65  % SZS output end Proof for theBenchmark
% 2.09/0.65  % (3682)------------------------------
% 2.09/0.65  % (3682)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.09/0.65  % (3682)Termination reason: Refutation
% 2.09/0.65  
% 2.09/0.65  % (3682)Memory used [KB]: 7164
% 2.09/0.65  % (3682)Time elapsed: 0.222 s
% 2.09/0.65  % (3682)------------------------------
% 2.09/0.65  % (3682)------------------------------
% 2.09/0.65  % (3675)Success in time 0.287 s
%------------------------------------------------------------------------------
