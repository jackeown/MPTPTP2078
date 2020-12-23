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
% DateTime   : Thu Dec  3 13:12:16 EST 2020

% Result     : Theorem 2.18s
% Output     : Refutation 2.18s
% Verified   : 
% Statistics : Number of formulae       :  191 (4436 expanded)
%              Number of leaves         :   23 ( 944 expanded)
%              Depth                    :   48
%              Number of atoms          :  644 (22099 expanded)
%              Number of equality atoms :  172 (4026 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f651,plain,(
    $false ),
    inference(subsumption_resolution,[],[f650,f440])).

fof(f440,plain,(
    r1_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f438,f47])).

fof(f47,plain,
    ( ~ v1_tops_1(sK1,sK0)
    | r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f24])).

fof(f24,negated_conjecture,(
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
    inference(negated_conjecture,[],[f23])).

fof(f23,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_tops_1)).

fof(f438,plain,(
    v1_tops_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f437,f51])).

fof(f51,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f437,plain,
    ( ~ l1_pre_topc(sK0)
    | v1_tops_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f436,f49])).

fof(f49,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f26])).

fof(f436,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | v1_tops_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f432,f111])).

fof(f111,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(resolution,[],[f110,f51])).

fof(f110,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | u1_struct_0(X0) = k2_struct_0(X0) ) ),
    inference(resolution,[],[f58,f59])).

fof(f59,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f58,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | u1_struct_0(X0) = k2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f432,plain,
    ( u1_struct_0(sK0) != k2_struct_0(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | v1_tops_1(sK1,sK0) ),
    inference(superposition,[],[f62,f424])).

fof(f424,plain,(
    u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) ),
    inference(subsumption_resolution,[],[f423,f108])).

fof(f108,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f97,f95])).

fof(f95,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f54,f84])).

fof(f84,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f54,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f97,plain,(
    ! [X0] : k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = X0 ),
    inference(definition_unfolding,[],[f56,f94])).

fof(f94,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f85,f84])).

fof(f85,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f56,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f423,plain,
    ( u1_struct_0(sK0) != k5_xboole_0(u1_struct_0(sK0),k1_xboole_0)
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) ),
    inference(forward_demodulation,[],[f421,f95])).

fof(f421,plain,
    ( u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | u1_struct_0(sK0) != k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k1_xboole_0))) ),
    inference(resolution,[],[f418,f102])).

fof(f102,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) != X0 ) ),
    inference(definition_unfolding,[],[f91,f94])).

fof(f91,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != X0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f418,plain,
    ( ~ r1_xboole_0(u1_struct_0(sK0),k1_xboole_0)
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) ),
    inference(subsumption_resolution,[],[f417,f316])).

fof(f316,plain,
    ( v3_pre_topc(k1_xboole_0,sK0)
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) ),
    inference(subsumption_resolution,[],[f307,f49])).

fof(f307,plain,
    ( v3_pre_topc(k1_xboole_0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) ),
    inference(duplicate_literal_removal,[],[f306])).

fof(f306,plain,
    ( v3_pre_topc(k1_xboole_0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) ),
    inference(superposition,[],[f188,f298])).

fof(f298,plain,
    ( k1_xboole_0 = sK5(sK0,sK1,u1_struct_0(sK0))
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) ),
    inference(duplicate_literal_removal,[],[f297])).

fof(f297,plain,
    ( u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | k1_xboole_0 = sK5(sK0,sK1,u1_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f296,f111])).

fof(f296,plain,
    ( u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | k1_xboole_0 = sK5(sK0,sK1,u1_struct_0(sK0))
    | k2_struct_0(sK0) = k2_pre_topc(sK0,sK1) ),
    inference(subsumption_resolution,[],[f295,f51])).

fof(f295,plain,
    ( u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | k1_xboole_0 = sK5(sK0,sK1,u1_struct_0(sK0))
    | k2_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f294,f49])).

fof(f294,plain,
    ( u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | k1_xboole_0 = sK5(sK0,sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f289,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = k2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tops_1)).

fof(f289,plain,
    ( v1_tops_1(sK1,sK0)
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | k1_xboole_0 = sK5(sK0,sK1,u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f288,f49])).

fof(f288,plain,
    ( k1_xboole_0 = sK5(sK0,sK1,u1_struct_0(sK0))
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | v1_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(duplicate_literal_removal,[],[f285])).

fof(f285,plain,
    ( k1_xboole_0 = sK5(sK0,sK1,u1_struct_0(sK0))
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | v1_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) ),
    inference(resolution,[],[f267,f192])).

fof(f192,plain,(
    ! [X0] :
      ( r1_xboole_0(X0,sK5(sK0,X0,u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | u1_struct_0(sK0) = k2_pre_topc(sK0,X0) ) ),
    inference(subsumption_resolution,[],[f191,f109])).

fof(f109,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f57,f52])).

fof(f52,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f57,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f191,plain,(
    ! [X0] :
      ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | r1_xboole_0(X0,sK5(sK0,X0,u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | u1_struct_0(sK0) = k2_pre_topc(sK0,X0) ) ),
    inference(duplicate_literal_removal,[],[f190])).

fof(f190,plain,(
    ! [X0] :
      ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | r1_xboole_0(X0,sK5(sK0,X0,u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | u1_struct_0(sK0) = k2_pre_topc(sK0,X0)
      | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | u1_struct_0(sK0) = k2_pre_topc(sK0,X0) ) ),
    inference(resolution,[],[f185,f171])).

fof(f171,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(sK0,X0,X1),u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_pre_topc(sK0,X0) = X1 ) ),
    inference(resolution,[],[f82,f51])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(sK4(X0,X1,X2),u1_struct_0(X0))
      | k2_pre_topc(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f35,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_pre_topc)).

fof(f185,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(sK0,X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | r1_xboole_0(X0,sK5(sK0,X0,X1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_pre_topc(sK0,X0) = X1 ) ),
    inference(resolution,[],[f80,f51])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_xboole_0(X1,sK5(X0,X1,X2))
      | ~ r2_hidden(sK4(X0,X1,X2),X2)
      | k2_pre_topc(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f267,plain,
    ( ~ r1_xboole_0(sK1,sK5(sK0,sK1,u1_struct_0(sK0)))
    | k1_xboole_0 = sK5(sK0,sK1,u1_struct_0(sK0))
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | v1_tops_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f266,f49])).

fof(f266,plain,
    ( u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | k1_xboole_0 = sK5(sK0,sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_xboole_0(sK1,sK5(sK0,sK1,u1_struct_0(sK0)))
    | v1_tops_1(sK1,sK0) ),
    inference(duplicate_literal_removal,[],[f260])).

fof(f260,plain,
    ( u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | k1_xboole_0 = sK5(sK0,sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_xboole_0(sK1,sK5(sK0,sK1,u1_struct_0(sK0)))
    | v1_tops_1(sK1,sK0) ),
    inference(resolution,[],[f247,f189])).

fof(f189,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK5(sK0,X0,u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
      | u1_struct_0(sK0) = k2_pre_topc(sK0,X0)
      | k1_xboole_0 = sK5(sK0,X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_xboole_0(sK1,sK5(sK0,X0,u1_struct_0(sK0)))
      | v1_tops_1(sK1,sK0) ) ),
    inference(resolution,[],[f188,f48])).

fof(f48,plain,(
    ! [X2] :
      ( ~ v3_pre_topc(X2,sK0)
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_xboole_0(sK1,X2)
      | v1_tops_1(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f247,plain,
    ( m1_subset_1(sK5(sK0,sK1,u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) ),
    inference(resolution,[],[f246,f49])).

fof(f246,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_subset_1(sK5(sK0,X0,u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
      | u1_struct_0(sK0) = k2_pre_topc(sK0,X0) ) ),
    inference(subsumption_resolution,[],[f245,f109])).

fof(f245,plain,(
    ! [X0] :
      ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_subset_1(sK5(sK0,X0,u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | u1_struct_0(sK0) = k2_pre_topc(sK0,X0) ) ),
    inference(duplicate_literal_removal,[],[f244])).

fof(f244,plain,(
    ! [X0] :
      ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_subset_1(sK5(sK0,X0,u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | u1_struct_0(sK0) = k2_pre_topc(sK0,X0)
      | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | u1_struct_0(sK0) = k2_pre_topc(sK0,X0) ) ),
    inference(resolution,[],[f243,f171])).

fof(f243,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(sK0,X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_subset_1(sK5(sK0,X0,X1),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_pre_topc(sK0,X0) = X1 ) ),
    inference(resolution,[],[f77,f51])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(sK4(X0,X1,X2),X2)
      | k2_pre_topc(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f188,plain,(
    ! [X0] :
      ( v3_pre_topc(sK5(sK0,X0,u1_struct_0(sK0)),sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | u1_struct_0(sK0) = k2_pre_topc(sK0,X0) ) ),
    inference(subsumption_resolution,[],[f187,f109])).

fof(f187,plain,(
    ! [X0] :
      ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | v3_pre_topc(sK5(sK0,X0,u1_struct_0(sK0)),sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | u1_struct_0(sK0) = k2_pre_topc(sK0,X0) ) ),
    inference(duplicate_literal_removal,[],[f186])).

fof(f186,plain,(
    ! [X0] :
      ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | v3_pre_topc(sK5(sK0,X0,u1_struct_0(sK0)),sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | u1_struct_0(sK0) = k2_pre_topc(sK0,X0)
      | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | u1_struct_0(sK0) = k2_pre_topc(sK0,X0) ) ),
    inference(resolution,[],[f184,f171])).

fof(f184,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(sK0,X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v3_pre_topc(sK5(sK0,X0,X1),sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_pre_topc(sK0,X0) = X1 ) ),
    inference(resolution,[],[f78,f51])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(sK5(X0,X1,X2),X0)
      | ~ r2_hidden(sK4(X0,X1,X2),X2)
      | k2_pre_topc(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f417,plain,
    ( u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | ~ v3_pre_topc(k1_xboole_0,sK0)
    | ~ r1_xboole_0(u1_struct_0(sK0),k1_xboole_0) ),
    inference(subsumption_resolution,[],[f416,f53])).

fof(f53,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f416,plain,
    ( u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | ~ v3_pre_topc(k1_xboole_0,sK0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_xboole_0(u1_struct_0(sK0),k1_xboole_0) ),
    inference(duplicate_literal_removal,[],[f413])).

fof(f413,plain,
    ( u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | ~ v3_pre_topc(k1_xboole_0,sK0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_xboole_0(u1_struct_0(sK0),k1_xboole_0)
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) ),
    inference(resolution,[],[f411,f341])).

fof(f341,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v3_pre_topc(X1,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_xboole_0(u1_struct_0(sK0),X1)
      | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) ) ),
    inference(subsumption_resolution,[],[f340,f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f340,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X1,sK0)
      | ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(u1_struct_0(sK0),X1)
      | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) ) ),
    inference(subsumption_resolution,[],[f328,f109])).

fof(f328,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X1,sK0)
      | ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(u1_struct_0(sK0),X1)
      | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) ) ),
    inference(superposition,[],[f236,f327])).

fof(f327,plain,
    ( u1_struct_0(sK0) = k2_pre_topc(sK0,u1_struct_0(sK0))
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) ),
    inference(subsumption_resolution,[],[f326,f51])).

fof(f326,plain,
    ( u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | u1_struct_0(sK0) = k2_pre_topc(sK0,u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f323,f109])).

fof(f323,plain,
    ( u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | u1_struct_0(sK0) = k2_pre_topc(sK0,u1_struct_0(sK0)) ),
    inference(resolution,[],[f320,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k2_pre_topc(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

fof(f320,plain,
    ( v4_pre_topc(u1_struct_0(sK0),sK0)
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) ),
    inference(resolution,[],[f316,f155])).

fof(f155,plain,
    ( ~ v3_pre_topc(k1_xboole_0,sK0)
    | v4_pre_topc(u1_struct_0(sK0),sK0) ),
    inference(subsumption_resolution,[],[f152,f109])).

fof(f152,plain,
    ( ~ v3_pre_topc(k1_xboole_0,sK0)
    | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(u1_struct_0(sK0),sK0) ),
    inference(superposition,[],[f149,f133])).

fof(f133,plain,(
    ! [X0] : k1_xboole_0 = k3_subset_1(X0,X0) ),
    inference(backward_demodulation,[],[f118,f132])).

fof(f132,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f131,f108])).

fof(f131,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f129,f95])).

fof(f129,plain,(
    ! [X0] : k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = k3_subset_1(X0,k1_xboole_0) ),
    inference(resolution,[],[f98,f53])).

fof(f98,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ) ),
    inference(definition_unfolding,[],[f86,f94])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f118,plain,(
    ! [X0] : k1_xboole_0 = k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0)) ),
    inference(resolution,[],[f87,f53])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f149,plain,(
    ! [X0] :
      ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v4_pre_topc(X0,sK0) ) ),
    inference(resolution,[],[f64,f51])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | v4_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tops_1)).

fof(f236,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,k2_pre_topc(sK0,X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X2,sK0)
      | ~ r2_hidden(X1,X2)
      | ~ r1_xboole_0(X0,X2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f235,f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f235,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X2,sK0)
      | ~ r2_hidden(X1,X2)
      | ~ r1_xboole_0(X0,X2)
      | ~ r2_hidden(X1,k2_pre_topc(sK0,X0)) ) ),
    inference(resolution,[],[f70,f51])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X3,X0)
      | ~ r2_hidden(X2,X3)
      | ~ r1_xboole_0(X1,X3)
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f33,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_pre_topc)).

fof(f411,plain,
    ( r2_hidden(sK4(sK0,sK1,u1_struct_0(sK0)),k1_xboole_0)
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) ),
    inference(subsumption_resolution,[],[f408,f49])).

fof(f408,plain,
    ( r2_hidden(sK4(sK0,sK1,u1_struct_0(sK0)),k1_xboole_0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) ),
    inference(duplicate_literal_removal,[],[f407])).

fof(f407,plain,
    ( r2_hidden(sK4(sK0,sK1,u1_struct_0(sK0)),k1_xboole_0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) ),
    inference(superposition,[],[f403,f298])).

fof(f403,plain,(
    ! [X0] :
      ( r2_hidden(sK4(sK0,X0,u1_struct_0(sK0)),sK5(sK0,X0,u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | u1_struct_0(sK0) = k2_pre_topc(sK0,X0) ) ),
    inference(subsumption_resolution,[],[f402,f109])).

fof(f402,plain,(
    ! [X0] :
      ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK4(sK0,X0,u1_struct_0(sK0)),sK5(sK0,X0,u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | u1_struct_0(sK0) = k2_pre_topc(sK0,X0) ) ),
    inference(duplicate_literal_removal,[],[f401])).

fof(f401,plain,(
    ! [X0] :
      ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK4(sK0,X0,u1_struct_0(sK0)),sK5(sK0,X0,u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | u1_struct_0(sK0) = k2_pre_topc(sK0,X0)
      | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | u1_struct_0(sK0) = k2_pre_topc(sK0,X0) ) ),
    inference(resolution,[],[f352,f171])).

fof(f352,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(sK0,X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK4(sK0,X0,X1),sK5(sK0,X0,X1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_pre_topc(sK0,X0) = X1 ) ),
    inference(resolution,[],[f79,f51])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(sK4(X0,X1,X2),sK5(X0,X1,X2))
      | ~ r2_hidden(sK4(X0,X1,X2),X2)
      | k2_pre_topc(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) != k2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v1_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f650,plain,(
    ~ r1_xboole_0(sK1,sK2) ),
    inference(subsumption_resolution,[],[f649,f439])).

fof(f439,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f438,f44])).

fof(f44,plain,
    ( ~ v1_tops_1(sK1,sK0)
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f26])).

fof(f649,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_xboole_0(sK1,sK2) ),
    inference(subsumption_resolution,[],[f628,f441])).

fof(f441,plain,(
    v3_pre_topc(sK2,sK0) ),
    inference(resolution,[],[f438,f46])).

fof(f46,plain,
    ( ~ v1_tops_1(sK1,sK0)
    | v3_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f628,plain,
    ( ~ v3_pre_topc(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f623,f434])).

fof(f434,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v3_pre_topc(X1,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_xboole_0(sK1,X1) ) ),
    inference(subsumption_resolution,[],[f433,f88])).

fof(f433,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X1,sK0)
      | ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(sK1,X1) ) ),
    inference(subsumption_resolution,[],[f426,f49])).

fof(f426,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X1,sK0)
      | ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(sK1,X1)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(superposition,[],[f236,f424])).

fof(f623,plain,(
    r2_hidden(sK4(sK0,k1_xboole_0,sK2),sK2) ),
    inference(subsumption_resolution,[],[f618,f442])).

fof(f442,plain,(
    k1_xboole_0 != sK2 ),
    inference(resolution,[],[f438,f45])).

fof(f45,plain,
    ( ~ v1_tops_1(sK1,sK0)
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f26])).

fof(f618,plain,
    ( k1_xboole_0 = sK2
    | r2_hidden(sK4(sK0,k1_xboole_0,sK2),sK2) ),
    inference(resolution,[],[f614,f439])).

fof(f614,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | k1_xboole_0 = X1
      | r2_hidden(sK4(sK0,k1_xboole_0,X1),X1) ) ),
    inference(forward_demodulation,[],[f613,f158])).

fof(f158,plain,(
    k1_xboole_0 = k2_pre_topc(sK0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f157,f51])).

fof(f157,plain,
    ( ~ l1_pre_topc(sK0)
    | k1_xboole_0 = k2_pre_topc(sK0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f156,f53])).

fof(f156,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k1_xboole_0 = k2_pre_topc(sK0,k1_xboole_0) ),
    inference(resolution,[],[f154,f61])).

fof(f154,plain,(
    v4_pre_topc(k1_xboole_0,sK0) ),
    inference(subsumption_resolution,[],[f153,f53])).

fof(f153,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(k1_xboole_0,sK0) ),
    inference(subsumption_resolution,[],[f151,f114])).

fof(f114,plain,(
    v3_pre_topc(u1_struct_0(sK0),sK0) ),
    inference(forward_demodulation,[],[f113,f111])).

fof(f113,plain,(
    v3_pre_topc(k2_struct_0(sK0),sK0) ),
    inference(subsumption_resolution,[],[f112,f51])).

fof(f112,plain,
    ( ~ l1_pre_topc(sK0)
    | v3_pre_topc(k2_struct_0(sK0),sK0) ),
    inference(resolution,[],[f83,f50])).

fof(f50,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f83,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v3_pre_topc(k2_struct_0(X0),X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_tops_1)).

fof(f151,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK0),sK0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(k1_xboole_0,sK0) ),
    inference(superposition,[],[f149,f132])).

fof(f613,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK4(sK0,k1_xboole_0,X1),X1)
      | k2_pre_topc(sK0,k1_xboole_0) = X1 ) ),
    inference(subsumption_resolution,[],[f608,f53])).

fof(f608,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK4(sK0,k1_xboole_0,X1),X1)
      | k2_pre_topc(sK0,k1_xboole_0) = X1
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(trivial_inequality_removal,[],[f607])).

fof(f607,plain,(
    ! [X1] :
      ( k1_xboole_0 != k1_xboole_0
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK4(sK0,k1_xboole_0,X1),X1)
      | k2_pre_topc(sK0,k1_xboole_0) = X1
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(superposition,[],[f533,f141])).

fof(f141,plain,(
    ! [X1] : k1_xboole_0 = k1_setfam_1(k2_tarski(k1_xboole_0,X1)) ),
    inference(trivial_inequality_removal,[],[f139])).

fof(f139,plain,(
    ! [X1] :
      ( k1_xboole_0 != k1_xboole_0
      | k1_xboole_0 = k1_setfam_1(k2_tarski(k1_xboole_0,X1)) ) ),
    inference(superposition,[],[f123,f96])).

fof(f96,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_setfam_1(k2_tarski(k1_xboole_0,X0))) ),
    inference(definition_unfolding,[],[f55,f94])).

fof(f55,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(f123,plain,(
    ! [X2,X3] :
      ( k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X3))) != X2
      | k1_xboole_0 = k1_setfam_1(k2_tarski(X2,X3)) ) ),
    inference(resolution,[],[f102,f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1)) ) ),
    inference(definition_unfolding,[],[f90,f84])).

fof(f90,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f533,plain,(
    ! [X2,X3] :
      ( k1_xboole_0 != k1_setfam_1(k2_tarski(X2,u1_struct_0(sK0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK4(sK0,X2,X3),X3)
      | k2_pre_topc(sK0,X2) = X3
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f530,f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k1_xboole_0 != k1_setfam_1(k2_tarski(X0,X1)) ) ),
    inference(definition_unfolding,[],[f89,f84])).

fof(f89,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f530,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK4(sK0,X1,X0),X0)
      | k2_pre_topc(sK0,X1) = X0 ) ),
    inference(subsumption_resolution,[],[f529,f114])).

fof(f529,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(u1_struct_0(sK0),sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_xboole_0(X1,u1_struct_0(sK0))
      | r2_hidden(sK4(sK0,X1,X0),X0)
      | k2_pre_topc(sK0,X1) = X0 ) ),
    inference(subsumption_resolution,[],[f528,f109])).

fof(f528,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(u1_struct_0(sK0),sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_xboole_0(X1,u1_struct_0(sK0))
      | r2_hidden(sK4(sK0,X1,X0),X0)
      | k2_pre_topc(sK0,X1) = X0 ) ),
    inference(duplicate_literal_removal,[],[f523])).

fof(f523,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(u1_struct_0(sK0),sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_xboole_0(X1,u1_struct_0(sK0))
      | r2_hidden(sK4(sK0,X1,X0),X0)
      | k2_pre_topc(sK0,X1) = X0
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_pre_topc(sK0,X1) = X0 ) ),
    inference(resolution,[],[f468,f171])).

fof(f468,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK4(sK0,X0,X1),X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X2,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_xboole_0(X0,X2)
      | r2_hidden(sK4(sK0,X0,X1),X1)
      | k2_pre_topc(sK0,X0) = X1 ) ),
    inference(resolution,[],[f81,f51])).

fof(f81,plain,(
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
    inference(cnf_transformation,[],[f36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:10:20 EST 2020
% 0.14/0.35  % CPUTime    : 
% 1.33/0.57  % (1661)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.61/0.58  % (1659)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.61/0.58  % (1645)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.61/0.58  % (1657)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.61/0.58  % (1647)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.61/0.58  % (1647)Refutation not found, incomplete strategy% (1647)------------------------------
% 1.61/0.58  % (1647)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.61/0.58  % (1640)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.61/0.59  % (1639)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.61/0.59  % (1653)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.61/0.59  % (1639)Refutation not found, incomplete strategy% (1639)------------------------------
% 1.61/0.59  % (1639)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.61/0.59  % (1639)Termination reason: Refutation not found, incomplete strategy
% 1.61/0.59  
% 1.61/0.59  % (1639)Memory used [KB]: 10874
% 1.61/0.59  % (1639)Time elapsed: 0.158 s
% 1.61/0.59  % (1639)------------------------------
% 1.61/0.59  % (1639)------------------------------
% 1.61/0.59  % (1647)Termination reason: Refutation not found, incomplete strategy
% 1.61/0.59  
% 1.61/0.59  % (1647)Memory used [KB]: 10746
% 1.61/0.59  % (1647)Time elapsed: 0.147 s
% 1.61/0.59  % (1647)------------------------------
% 1.61/0.59  % (1647)------------------------------
% 1.61/0.59  % (1643)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.61/0.59  % (1652)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.61/0.59  % (1659)Refutation not found, incomplete strategy% (1659)------------------------------
% 1.61/0.59  % (1659)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.61/0.59  % (1659)Termination reason: Refutation not found, incomplete strategy
% 1.61/0.59  
% 1.61/0.59  % (1659)Memory used [KB]: 10874
% 1.61/0.59  % (1659)Time elapsed: 0.164 s
% 1.61/0.59  % (1659)------------------------------
% 1.61/0.59  % (1659)------------------------------
% 1.61/0.60  % (1651)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.61/0.60  % (1663)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.61/0.60  % (1637)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.61/0.60  % (1641)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.61/0.60  % (1649)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.61/0.60  % (1638)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.61/0.60  % (1645)Refutation not found, incomplete strategy% (1645)------------------------------
% 1.61/0.60  % (1645)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.61/0.60  % (1645)Termination reason: Refutation not found, incomplete strategy
% 1.61/0.60  
% 1.61/0.60  % (1645)Memory used [KB]: 10874
% 1.61/0.60  % (1645)Time elapsed: 0.165 s
% 1.61/0.60  % (1645)------------------------------
% 1.61/0.60  % (1645)------------------------------
% 1.61/0.60  % (1666)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.61/0.61  % (1654)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.61/0.61  % (1667)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.61/0.61  % (1644)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.61/0.61  % (1642)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.61/0.61  % (1646)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.61/0.62  % (1658)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.61/0.62  % (1656)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.61/0.62  % (1648)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.61/0.62  % (1655)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.61/0.62  % (1648)Refutation not found, incomplete strategy% (1648)------------------------------
% 1.61/0.62  % (1648)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.61/0.62  % (1648)Termination reason: Refutation not found, incomplete strategy
% 1.61/0.62  
% 1.61/0.62  % (1648)Memory used [KB]: 10746
% 1.61/0.62  % (1648)Time elapsed: 0.191 s
% 1.61/0.62  % (1648)------------------------------
% 1.61/0.62  % (1648)------------------------------
% 1.61/0.62  % (1650)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.61/0.62  % (1664)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.61/0.62  % (1668)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.61/0.63  % (1654)Refutation not found, incomplete strategy% (1654)------------------------------
% 1.61/0.63  % (1654)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.61/0.63  % (1654)Termination reason: Refutation not found, incomplete strategy
% 1.61/0.63  
% 1.61/0.63  % (1654)Memory used [KB]: 10746
% 1.61/0.63  % (1654)Time elapsed: 0.181 s
% 1.61/0.63  % (1654)------------------------------
% 1.61/0.63  % (1654)------------------------------
% 1.61/0.63  % (1665)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.61/0.64  % (1665)Refutation not found, incomplete strategy% (1665)------------------------------
% 1.61/0.64  % (1665)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.61/0.64  % (1665)Termination reason: Refutation not found, incomplete strategy
% 1.61/0.64  
% 1.61/0.64  % (1665)Memory used [KB]: 10874
% 1.61/0.64  % (1665)Time elapsed: 0.206 s
% 1.61/0.64  % (1665)------------------------------
% 1.61/0.64  % (1665)------------------------------
% 2.18/0.67  % (1693)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.18/0.67  % (1643)Refutation found. Thanks to Tanya!
% 2.18/0.67  % SZS status Theorem for theBenchmark
% 2.18/0.67  % SZS output start Proof for theBenchmark
% 2.18/0.67  fof(f651,plain,(
% 2.18/0.67    $false),
% 2.18/0.67    inference(subsumption_resolution,[],[f650,f440])).
% 2.18/0.67  fof(f440,plain,(
% 2.18/0.67    r1_xboole_0(sK1,sK2)),
% 2.18/0.67    inference(resolution,[],[f438,f47])).
% 2.18/0.67  fof(f47,plain,(
% 2.18/0.67    ~v1_tops_1(sK1,sK0) | r1_xboole_0(sK1,sK2)),
% 2.18/0.67    inference(cnf_transformation,[],[f26])).
% 2.18/0.67  fof(f26,plain,(
% 2.18/0.67    ? [X0] : (? [X1] : ((v1_tops_1(X1,X0) <~> ! [X2] : (~r1_xboole_0(X1,X2) | ~v3_pre_topc(X2,X0) | k1_xboole_0 = X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.18/0.67    inference(flattening,[],[f25])).
% 2.18/0.67  fof(f25,plain,(
% 2.18/0.67    ? [X0] : (? [X1] : ((v1_tops_1(X1,X0) <~> ! [X2] : ((~r1_xboole_0(X1,X2) | ~v3_pre_topc(X2,X0) | k1_xboole_0 = X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 2.18/0.67    inference(ennf_transformation,[],[f24])).
% 2.18/0.67  fof(f24,negated_conjecture,(
% 2.18/0.67    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_xboole_0(X1,X2) & v3_pre_topc(X2,X0) & k1_xboole_0 != X2)))))),
% 2.18/0.67    inference(negated_conjecture,[],[f23])).
% 2.18/0.67  fof(f23,conjecture,(
% 2.18/0.67    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_xboole_0(X1,X2) & v3_pre_topc(X2,X0) & k1_xboole_0 != X2)))))),
% 2.18/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_tops_1)).
% 2.18/0.67  fof(f438,plain,(
% 2.18/0.67    v1_tops_1(sK1,sK0)),
% 2.18/0.67    inference(subsumption_resolution,[],[f437,f51])).
% 2.18/0.67  fof(f51,plain,(
% 2.18/0.67    l1_pre_topc(sK0)),
% 2.18/0.67    inference(cnf_transformation,[],[f26])).
% 2.18/0.67  fof(f437,plain,(
% 2.18/0.67    ~l1_pre_topc(sK0) | v1_tops_1(sK1,sK0)),
% 2.18/0.67    inference(subsumption_resolution,[],[f436,f49])).
% 2.18/0.67  fof(f49,plain,(
% 2.18/0.67    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.18/0.67    inference(cnf_transformation,[],[f26])).
% 2.18/0.67  fof(f436,plain,(
% 2.18/0.67    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | v1_tops_1(sK1,sK0)),
% 2.18/0.67    inference(subsumption_resolution,[],[f432,f111])).
% 2.18/0.67  fof(f111,plain,(
% 2.18/0.67    u1_struct_0(sK0) = k2_struct_0(sK0)),
% 2.18/0.67    inference(resolution,[],[f110,f51])).
% 2.18/0.67  fof(f110,plain,(
% 2.18/0.67    ( ! [X0] : (~l1_pre_topc(X0) | u1_struct_0(X0) = k2_struct_0(X0)) )),
% 2.18/0.67    inference(resolution,[],[f58,f59])).
% 2.18/0.67  fof(f59,plain,(
% 2.18/0.67    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 2.18/0.67    inference(cnf_transformation,[],[f28])).
% 2.18/0.67  fof(f28,plain,(
% 2.18/0.67    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.18/0.67    inference(ennf_transformation,[],[f17])).
% 2.18/0.67  fof(f17,axiom,(
% 2.18/0.67    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.18/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 2.18/0.67  fof(f58,plain,(
% 2.18/0.67    ( ! [X0] : (~l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0)) )),
% 2.18/0.67    inference(cnf_transformation,[],[f27])).
% 2.18/0.67  fof(f27,plain,(
% 2.18/0.67    ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0))),
% 2.18/0.67    inference(ennf_transformation,[],[f16])).
% 2.18/0.67  fof(f16,axiom,(
% 2.18/0.67    ! [X0] : (l1_struct_0(X0) => u1_struct_0(X0) = k2_struct_0(X0))),
% 2.18/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 2.18/0.67  fof(f432,plain,(
% 2.18/0.67    u1_struct_0(sK0) != k2_struct_0(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | v1_tops_1(sK1,sK0)),
% 2.18/0.67    inference(superposition,[],[f62,f424])).
% 2.18/0.67  fof(f424,plain,(
% 2.18/0.67    u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)),
% 2.18/0.67    inference(subsumption_resolution,[],[f423,f108])).
% 2.18/0.67  fof(f108,plain,(
% 2.18/0.67    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.18/0.67    inference(forward_demodulation,[],[f97,f95])).
% 2.18/0.67  fof(f95,plain,(
% 2.18/0.67    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0))) )),
% 2.18/0.67    inference(definition_unfolding,[],[f54,f84])).
% 2.18/0.67  fof(f84,plain,(
% 2.18/0.67    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.18/0.67    inference(cnf_transformation,[],[f13])).
% 2.18/0.67  fof(f13,axiom,(
% 2.18/0.67    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 2.18/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 2.18/0.67  fof(f54,plain,(
% 2.18/0.67    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 2.18/0.67    inference(cnf_transformation,[],[f3])).
% 2.18/0.67  fof(f3,axiom,(
% 2.18/0.67    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 2.18/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 2.18/0.67  fof(f97,plain,(
% 2.18/0.67    ( ! [X0] : (k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = X0) )),
% 2.18/0.67    inference(definition_unfolding,[],[f56,f94])).
% 2.18/0.67  fof(f94,plain,(
% 2.18/0.67    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 2.18/0.67    inference(definition_unfolding,[],[f85,f84])).
% 2.18/0.67  fof(f85,plain,(
% 2.18/0.67    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.18/0.67    inference(cnf_transformation,[],[f2])).
% 2.18/0.67  fof(f2,axiom,(
% 2.18/0.67    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.18/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.18/0.67  fof(f56,plain,(
% 2.18/0.67    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.18/0.67    inference(cnf_transformation,[],[f4])).
% 2.18/0.67  fof(f4,axiom,(
% 2.18/0.67    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 2.18/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 2.18/0.67  fof(f423,plain,(
% 2.18/0.67    u1_struct_0(sK0) != k5_xboole_0(u1_struct_0(sK0),k1_xboole_0) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)),
% 2.18/0.67    inference(forward_demodulation,[],[f421,f95])).
% 2.18/0.67  fof(f421,plain,(
% 2.18/0.67    u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) | u1_struct_0(sK0) != k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k1_xboole_0)))),
% 2.18/0.67    inference(resolution,[],[f418,f102])).
% 2.18/0.67  fof(f102,plain,(
% 2.18/0.67    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) != X0) )),
% 2.18/0.67    inference(definition_unfolding,[],[f91,f94])).
% 2.18/0.67  fof(f91,plain,(
% 2.18/0.67    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1)) )),
% 2.18/0.67    inference(cnf_transformation,[],[f6])).
% 2.18/0.67  fof(f6,axiom,(
% 2.18/0.67    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 2.18/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 2.18/0.67  fof(f418,plain,(
% 2.18/0.67    ~r1_xboole_0(u1_struct_0(sK0),k1_xboole_0) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)),
% 2.18/0.67    inference(subsumption_resolution,[],[f417,f316])).
% 2.18/0.67  fof(f316,plain,(
% 2.18/0.67    v3_pre_topc(k1_xboole_0,sK0) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)),
% 2.18/0.67    inference(subsumption_resolution,[],[f307,f49])).
% 2.18/0.67  fof(f307,plain,(
% 2.18/0.67    v3_pre_topc(k1_xboole_0,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)),
% 2.18/0.67    inference(duplicate_literal_removal,[],[f306])).
% 2.18/0.67  fof(f306,plain,(
% 2.18/0.67    v3_pre_topc(k1_xboole_0,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)),
% 2.18/0.67    inference(superposition,[],[f188,f298])).
% 2.18/0.67  fof(f298,plain,(
% 2.18/0.67    k1_xboole_0 = sK5(sK0,sK1,u1_struct_0(sK0)) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)),
% 2.18/0.67    inference(duplicate_literal_removal,[],[f297])).
% 2.18/0.67  fof(f297,plain,(
% 2.18/0.67    u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) | k1_xboole_0 = sK5(sK0,sK1,u1_struct_0(sK0))),
% 2.18/0.67    inference(forward_demodulation,[],[f296,f111])).
% 2.18/0.67  fof(f296,plain,(
% 2.18/0.67    u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) | k1_xboole_0 = sK5(sK0,sK1,u1_struct_0(sK0)) | k2_struct_0(sK0) = k2_pre_topc(sK0,sK1)),
% 2.18/0.67    inference(subsumption_resolution,[],[f295,f51])).
% 2.18/0.67  fof(f295,plain,(
% 2.18/0.67    u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) | k1_xboole_0 = sK5(sK0,sK1,u1_struct_0(sK0)) | k2_struct_0(sK0) = k2_pre_topc(sK0,sK1) | ~l1_pre_topc(sK0)),
% 2.18/0.67    inference(subsumption_resolution,[],[f294,f49])).
% 2.18/0.67  fof(f294,plain,(
% 2.18/0.67    u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) | k1_xboole_0 = sK5(sK0,sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | k2_struct_0(sK0) = k2_pre_topc(sK0,sK1) | ~l1_pre_topc(sK0)),
% 2.18/0.67    inference(resolution,[],[f289,f63])).
% 2.18/0.67  fof(f63,plain,(
% 2.18/0.67    ( ! [X0,X1] : (~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = k2_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 2.18/0.67    inference(cnf_transformation,[],[f31])).
% 2.18/0.67  fof(f31,plain,(
% 2.18/0.67    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> k2_pre_topc(X0,X1) = k2_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.18/0.67    inference(ennf_transformation,[],[f20])).
% 2.18/0.67  fof(f20,axiom,(
% 2.18/0.67    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> k2_pre_topc(X0,X1) = k2_struct_0(X0))))),
% 2.18/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tops_1)).
% 2.18/0.67  fof(f289,plain,(
% 2.18/0.67    v1_tops_1(sK1,sK0) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) | k1_xboole_0 = sK5(sK0,sK1,u1_struct_0(sK0))),
% 2.18/0.67    inference(subsumption_resolution,[],[f288,f49])).
% 2.18/0.67  fof(f288,plain,(
% 2.18/0.67    k1_xboole_0 = sK5(sK0,sK1,u1_struct_0(sK0)) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) | v1_tops_1(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.18/0.67    inference(duplicate_literal_removal,[],[f285])).
% 2.18/0.67  fof(f285,plain,(
% 2.18/0.67    k1_xboole_0 = sK5(sK0,sK1,u1_struct_0(sK0)) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) | v1_tops_1(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)),
% 2.18/0.67    inference(resolution,[],[f267,f192])).
% 2.18/0.67  fof(f192,plain,(
% 2.18/0.67    ( ! [X0] : (r1_xboole_0(X0,sK5(sK0,X0,u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_pre_topc(sK0,X0)) )),
% 2.18/0.67    inference(subsumption_resolution,[],[f191,f109])).
% 2.18/0.67  fof(f109,plain,(
% 2.18/0.67    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 2.18/0.67    inference(forward_demodulation,[],[f57,f52])).
% 2.18/0.67  fof(f52,plain,(
% 2.18/0.67    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 2.18/0.67    inference(cnf_transformation,[],[f7])).
% 2.18/0.67  fof(f7,axiom,(
% 2.18/0.67    ! [X0] : k2_subset_1(X0) = X0),
% 2.18/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 2.18/0.67  fof(f57,plain,(
% 2.18/0.67    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 2.18/0.67    inference(cnf_transformation,[],[f9])).
% 2.18/0.67  fof(f9,axiom,(
% 2.18/0.67    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 2.18/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 2.18/0.67  fof(f191,plain,(
% 2.18/0.67    ( ! [X0] : (~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | r1_xboole_0(X0,sK5(sK0,X0,u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_pre_topc(sK0,X0)) )),
% 2.18/0.67    inference(duplicate_literal_removal,[],[f190])).
% 2.18/0.67  fof(f190,plain,(
% 2.18/0.67    ( ! [X0] : (~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | r1_xboole_0(X0,sK5(sK0,X0,u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_pre_topc(sK0,X0) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_pre_topc(sK0,X0)) )),
% 2.18/0.67    inference(resolution,[],[f185,f171])).
% 2.18/0.67  fof(f171,plain,(
% 2.18/0.67    ( ! [X0,X1] : (r2_hidden(sK4(sK0,X0,X1),u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = X1) )),
% 2.18/0.67    inference(resolution,[],[f82,f51])).
% 2.18/0.67  fof(f82,plain,(
% 2.18/0.67    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | r2_hidden(sK4(X0,X1,X2),u1_struct_0(X0)) | k2_pre_topc(X0,X1) = X2) )),
% 2.18/0.67    inference(cnf_transformation,[],[f36])).
% 2.18/0.67  fof(f36,plain,(
% 2.18/0.67    ! [X0] : (! [X1] : (! [X2] : ((k2_pre_topc(X0,X1) = X2 <=> ! [X3] : ((r2_hidden(X3,X2) <=> ! [X4] : (~r1_xboole_0(X1,X4) | ~r2_hidden(X3,X4) | ~v3_pre_topc(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.18/0.67    inference(flattening,[],[f35])).
% 2.18/0.67  fof(f35,plain,(
% 2.18/0.67    ! [X0] : (! [X1] : (! [X2] : ((k2_pre_topc(X0,X1) = X2 <=> ! [X3] : ((r2_hidden(X3,X2) <=> ! [X4] : ((~r1_xboole_0(X1,X4) | ~r2_hidden(X3,X4) | ~v3_pre_topc(X4,X0)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.18/0.67    inference(ennf_transformation,[],[f15])).
% 2.18/0.67  fof(f15,axiom,(
% 2.18/0.67    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (k2_pre_topc(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) <=> ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_xboole_0(X1,X4) & r2_hidden(X3,X4) & v3_pre_topc(X4,X0)))))))))),
% 2.18/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_pre_topc)).
% 2.18/0.67  fof(f185,plain,(
% 2.18/0.67    ( ! [X0,X1] : (~r2_hidden(sK4(sK0,X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | r1_xboole_0(X0,sK5(sK0,X0,X1)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = X1) )),
% 2.18/0.67    inference(resolution,[],[f80,f51])).
% 2.18/0.67  fof(f80,plain,(
% 2.18/0.67    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | r1_xboole_0(X1,sK5(X0,X1,X2)) | ~r2_hidden(sK4(X0,X1,X2),X2) | k2_pre_topc(X0,X1) = X2) )),
% 2.18/0.67    inference(cnf_transformation,[],[f36])).
% 2.18/0.67  fof(f267,plain,(
% 2.18/0.67    ~r1_xboole_0(sK1,sK5(sK0,sK1,u1_struct_0(sK0))) | k1_xboole_0 = sK5(sK0,sK1,u1_struct_0(sK0)) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) | v1_tops_1(sK1,sK0)),
% 2.18/0.67    inference(subsumption_resolution,[],[f266,f49])).
% 2.18/0.67  fof(f266,plain,(
% 2.18/0.67    u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) | k1_xboole_0 = sK5(sK0,sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_xboole_0(sK1,sK5(sK0,sK1,u1_struct_0(sK0))) | v1_tops_1(sK1,sK0)),
% 2.18/0.67    inference(duplicate_literal_removal,[],[f260])).
% 2.18/0.67  fof(f260,plain,(
% 2.18/0.67    u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) | k1_xboole_0 = sK5(sK0,sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_xboole_0(sK1,sK5(sK0,sK1,u1_struct_0(sK0))) | v1_tops_1(sK1,sK0)),
% 2.18/0.67    inference(resolution,[],[f247,f189])).
% 2.18/0.67  fof(f189,plain,(
% 2.18/0.67    ( ! [X0] : (~m1_subset_1(sK5(sK0,X0,u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_pre_topc(sK0,X0) | k1_xboole_0 = sK5(sK0,X0,u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_xboole_0(sK1,sK5(sK0,X0,u1_struct_0(sK0))) | v1_tops_1(sK1,sK0)) )),
% 2.18/0.67    inference(resolution,[],[f188,f48])).
% 2.18/0.67  fof(f48,plain,(
% 2.18/0.67    ( ! [X2] : (~v3_pre_topc(X2,sK0) | k1_xboole_0 = X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_xboole_0(sK1,X2) | v1_tops_1(sK1,sK0)) )),
% 2.18/0.67    inference(cnf_transformation,[],[f26])).
% 2.18/0.67  fof(f247,plain,(
% 2.18/0.67    m1_subset_1(sK5(sK0,sK1,u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)),
% 2.18/0.67    inference(resolution,[],[f246,f49])).
% 2.18/0.67  fof(f246,plain,(
% 2.18/0.67    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(sK5(sK0,X0,u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_pre_topc(sK0,X0)) )),
% 2.18/0.67    inference(subsumption_resolution,[],[f245,f109])).
% 2.18/0.67  fof(f245,plain,(
% 2.18/0.67    ( ! [X0] : (~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(sK5(sK0,X0,u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_pre_topc(sK0,X0)) )),
% 2.18/0.67    inference(duplicate_literal_removal,[],[f244])).
% 2.18/0.67  fof(f244,plain,(
% 2.18/0.67    ( ! [X0] : (~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(sK5(sK0,X0,u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_pre_topc(sK0,X0) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_pre_topc(sK0,X0)) )),
% 2.18/0.67    inference(resolution,[],[f243,f171])).
% 2.18/0.67  fof(f243,plain,(
% 2.18/0.67    ( ! [X0,X1] : (~r2_hidden(sK4(sK0,X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(sK5(sK0,X0,X1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = X1) )),
% 2.18/0.67    inference(resolution,[],[f77,f51])).
% 2.18/0.67  fof(f77,plain,(
% 2.18/0.67    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(sK4(X0,X1,X2),X2) | k2_pre_topc(X0,X1) = X2) )),
% 2.18/0.67    inference(cnf_transformation,[],[f36])).
% 2.18/0.67  fof(f188,plain,(
% 2.18/0.67    ( ! [X0] : (v3_pre_topc(sK5(sK0,X0,u1_struct_0(sK0)),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_pre_topc(sK0,X0)) )),
% 2.18/0.67    inference(subsumption_resolution,[],[f187,f109])).
% 2.18/0.67  fof(f187,plain,(
% 2.18/0.67    ( ! [X0] : (~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(sK5(sK0,X0,u1_struct_0(sK0)),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_pre_topc(sK0,X0)) )),
% 2.18/0.67    inference(duplicate_literal_removal,[],[f186])).
% 2.18/0.67  fof(f186,plain,(
% 2.18/0.67    ( ! [X0] : (~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(sK5(sK0,X0,u1_struct_0(sK0)),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_pre_topc(sK0,X0) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_pre_topc(sK0,X0)) )),
% 2.18/0.67    inference(resolution,[],[f184,f171])).
% 2.18/0.67  fof(f184,plain,(
% 2.18/0.67    ( ! [X0,X1] : (~r2_hidden(sK4(sK0,X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(sK5(sK0,X0,X1),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = X1) )),
% 2.18/0.67    inference(resolution,[],[f78,f51])).
% 2.18/0.67  fof(f78,plain,(
% 2.18/0.67    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(sK5(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2) | k2_pre_topc(X0,X1) = X2) )),
% 2.18/0.67    inference(cnf_transformation,[],[f36])).
% 2.18/0.67  fof(f417,plain,(
% 2.18/0.67    u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) | ~v3_pre_topc(k1_xboole_0,sK0) | ~r1_xboole_0(u1_struct_0(sK0),k1_xboole_0)),
% 2.18/0.67    inference(subsumption_resolution,[],[f416,f53])).
% 2.18/0.67  fof(f53,plain,(
% 2.18/0.67    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.18/0.67    inference(cnf_transformation,[],[f12])).
% 2.18/0.67  fof(f12,axiom,(
% 2.18/0.67    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.18/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 2.18/0.67  fof(f416,plain,(
% 2.18/0.67    u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) | ~v3_pre_topc(k1_xboole_0,sK0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_xboole_0(u1_struct_0(sK0),k1_xboole_0)),
% 2.18/0.67    inference(duplicate_literal_removal,[],[f413])).
% 2.18/0.67  fof(f413,plain,(
% 2.18/0.67    u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) | ~v3_pre_topc(k1_xboole_0,sK0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_xboole_0(u1_struct_0(sK0),k1_xboole_0) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)),
% 2.18/0.67    inference(resolution,[],[f411,f341])).
% 2.18/0.67  fof(f341,plain,(
% 2.18/0.67    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~v3_pre_topc(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_xboole_0(u1_struct_0(sK0),X1) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)) )),
% 2.18/0.67    inference(subsumption_resolution,[],[f340,f88])).
% 2.18/0.67  fof(f88,plain,(
% 2.18/0.67    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | r2_hidden(X2,X0)) )),
% 2.18/0.67    inference(cnf_transformation,[],[f41])).
% 2.18/0.67  fof(f41,plain,(
% 2.18/0.67    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.18/0.67    inference(ennf_transformation,[],[f11])).
% 2.18/0.67  fof(f11,axiom,(
% 2.18/0.67    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 2.18/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 2.18/0.67  fof(f340,plain,(
% 2.18/0.67    ( ! [X0,X1] : (~r2_hidden(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X1,sK0) | ~r2_hidden(X0,X1) | ~r1_xboole_0(u1_struct_0(sK0),X1) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)) )),
% 2.18/0.67    inference(subsumption_resolution,[],[f328,f109])).
% 2.18/0.67  fof(f328,plain,(
% 2.18/0.67    ( ! [X0,X1] : (~r2_hidden(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X1,sK0) | ~r2_hidden(X0,X1) | ~r1_xboole_0(u1_struct_0(sK0),X1) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)) )),
% 2.18/0.67    inference(superposition,[],[f236,f327])).
% 2.18/0.67  fof(f327,plain,(
% 2.18/0.67    u1_struct_0(sK0) = k2_pre_topc(sK0,u1_struct_0(sK0)) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)),
% 2.18/0.67    inference(subsumption_resolution,[],[f326,f51])).
% 2.18/0.67  fof(f326,plain,(
% 2.18/0.67    u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) | ~l1_pre_topc(sK0) | u1_struct_0(sK0) = k2_pre_topc(sK0,u1_struct_0(sK0))),
% 2.18/0.67    inference(subsumption_resolution,[],[f323,f109])).
% 2.18/0.67  fof(f323,plain,(
% 2.18/0.67    u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | u1_struct_0(sK0) = k2_pre_topc(sK0,u1_struct_0(sK0))),
% 2.18/0.67    inference(resolution,[],[f320,f61])).
% 2.18/0.67  fof(f61,plain,(
% 2.18/0.67    ( ! [X0,X1] : (~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | k2_pre_topc(X0,X1) = X1) )),
% 2.18/0.67    inference(cnf_transformation,[],[f30])).
% 2.18/0.67  fof(f30,plain,(
% 2.18/0.67    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.18/0.67    inference(flattening,[],[f29])).
% 2.18/0.67  fof(f29,plain,(
% 2.18/0.67    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.18/0.67    inference(ennf_transformation,[],[f18])).
% 2.18/0.67  fof(f18,axiom,(
% 2.18/0.67    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 2.18/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).
% 2.18/0.67  fof(f320,plain,(
% 2.18/0.67    v4_pre_topc(u1_struct_0(sK0),sK0) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)),
% 2.18/0.67    inference(resolution,[],[f316,f155])).
% 2.18/0.67  fof(f155,plain,(
% 2.18/0.67    ~v3_pre_topc(k1_xboole_0,sK0) | v4_pre_topc(u1_struct_0(sK0),sK0)),
% 2.18/0.67    inference(subsumption_resolution,[],[f152,f109])).
% 2.18/0.67  fof(f152,plain,(
% 2.18/0.67    ~v3_pre_topc(k1_xboole_0,sK0) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(u1_struct_0(sK0),sK0)),
% 2.18/0.67    inference(superposition,[],[f149,f133])).
% 2.18/0.67  fof(f133,plain,(
% 2.18/0.67    ( ! [X0] : (k1_xboole_0 = k3_subset_1(X0,X0)) )),
% 2.18/0.67    inference(backward_demodulation,[],[f118,f132])).
% 2.18/0.67  fof(f132,plain,(
% 2.18/0.67    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 2.18/0.67    inference(forward_demodulation,[],[f131,f108])).
% 2.18/0.67  fof(f131,plain,(
% 2.18/0.67    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = k3_subset_1(X0,k1_xboole_0)) )),
% 2.18/0.67    inference(forward_demodulation,[],[f129,f95])).
% 2.18/0.67  fof(f129,plain,(
% 2.18/0.67    ( ! [X0] : (k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = k3_subset_1(X0,k1_xboole_0)) )),
% 2.18/0.67    inference(resolution,[],[f98,f53])).
% 2.18/0.67  fof(f98,plain,(
% 2.18/0.67    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 2.18/0.67    inference(definition_unfolding,[],[f86,f94])).
% 2.18/0.67  fof(f86,plain,(
% 2.18/0.67    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 2.18/0.67    inference(cnf_transformation,[],[f39])).
% 2.18/0.67  fof(f39,plain,(
% 2.18/0.67    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.18/0.67    inference(ennf_transformation,[],[f8])).
% 2.18/0.67  fof(f8,axiom,(
% 2.18/0.67    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 2.18/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 2.18/0.67  fof(f118,plain,(
% 2.18/0.67    ( ! [X0] : (k1_xboole_0 = k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0))) )),
% 2.18/0.67    inference(resolution,[],[f87,f53])).
% 2.18/0.67  fof(f87,plain,(
% 2.18/0.67    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 2.18/0.67    inference(cnf_transformation,[],[f40])).
% 2.18/0.67  fof(f40,plain,(
% 2.18/0.67    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.18/0.67    inference(ennf_transformation,[],[f10])).
% 2.18/0.67  fof(f10,axiom,(
% 2.18/0.67    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 2.18/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 2.18/0.67  fof(f149,plain,(
% 2.18/0.67    ( ! [X0] : (~v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(X0,sK0)) )),
% 2.18/0.67    inference(resolution,[],[f64,f51])).
% 2.18/0.67  fof(f64,plain,(
% 2.18/0.67    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | v4_pre_topc(X1,X0)) )),
% 2.18/0.67    inference(cnf_transformation,[],[f32])).
% 2.18/0.67  fof(f32,plain,(
% 2.18/0.67    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.18/0.67    inference(ennf_transformation,[],[f22])).
% 2.18/0.67  fof(f22,axiom,(
% 2.18/0.67    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 2.18/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tops_1)).
% 2.18/0.67  fof(f236,plain,(
% 2.18/0.67    ( ! [X2,X0,X1] : (~r2_hidden(X1,k2_pre_topc(sK0,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X2,sK0) | ~r2_hidden(X1,X2) | ~r1_xboole_0(X0,X2) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 2.18/0.67    inference(subsumption_resolution,[],[f235,f93])).
% 2.18/0.67  fof(f93,plain,(
% 2.18/0.67    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2)) )),
% 2.18/0.67    inference(cnf_transformation,[],[f43])).
% 2.18/0.67  fof(f43,plain,(
% 2.18/0.67    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.18/0.67    inference(flattening,[],[f42])).
% 2.18/0.67  fof(f42,plain,(
% 2.18/0.67    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 2.18/0.67    inference(ennf_transformation,[],[f14])).
% 2.18/0.67  fof(f14,axiom,(
% 2.18/0.67    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 2.18/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 2.18/0.67  fof(f235,plain,(
% 2.18/0.67    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X2,sK0) | ~r2_hidden(X1,X2) | ~r1_xboole_0(X0,X2) | ~r2_hidden(X1,k2_pre_topc(sK0,X0))) )),
% 2.18/0.67    inference(resolution,[],[f70,f51])).
% 2.18/0.67  fof(f70,plain,(
% 2.18/0.67    ( ! [X2,X0,X3,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X3,X0) | ~r2_hidden(X2,X3) | ~r1_xboole_0(X1,X3) | ~r2_hidden(X2,k2_pre_topc(X0,X1))) )),
% 2.18/0.67    inference(cnf_transformation,[],[f34])).
% 2.18/0.67  fof(f34,plain,(
% 2.18/0.67    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k2_pre_topc(X0,X1)) <=> (! [X3] : (~r1_xboole_0(X1,X3) | ~r2_hidden(X2,X3) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & ~v2_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.18/0.67    inference(flattening,[],[f33])).
% 2.18/0.67  fof(f33,plain,(
% 2.18/0.67    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k2_pre_topc(X0,X1)) <=> (! [X3] : ((~r1_xboole_0(X1,X3) | ~r2_hidden(X2,X3) | ~v3_pre_topc(X3,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & ~v2_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.18/0.67    inference(ennf_transformation,[],[f19])).
% 2.18/0.67  fof(f19,axiom,(
% 2.18/0.67    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,k2_pre_topc(X0,X1)) <=> (! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_xboole_0(X1,X3) & r2_hidden(X2,X3) & v3_pre_topc(X3,X0))) & ~v2_struct_0(X0))))))),
% 2.18/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_pre_topc)).
% 2.18/0.67  fof(f411,plain,(
% 2.18/0.67    r2_hidden(sK4(sK0,sK1,u1_struct_0(sK0)),k1_xboole_0) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)),
% 2.18/0.67    inference(subsumption_resolution,[],[f408,f49])).
% 2.18/0.67  fof(f408,plain,(
% 2.18/0.67    r2_hidden(sK4(sK0,sK1,u1_struct_0(sK0)),k1_xboole_0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)),
% 2.18/0.67    inference(duplicate_literal_removal,[],[f407])).
% 2.18/0.67  fof(f407,plain,(
% 2.18/0.67    r2_hidden(sK4(sK0,sK1,u1_struct_0(sK0)),k1_xboole_0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)),
% 2.18/0.67    inference(superposition,[],[f403,f298])).
% 2.18/0.67  fof(f403,plain,(
% 2.18/0.67    ( ! [X0] : (r2_hidden(sK4(sK0,X0,u1_struct_0(sK0)),sK5(sK0,X0,u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_pre_topc(sK0,X0)) )),
% 2.18/0.67    inference(subsumption_resolution,[],[f402,f109])).
% 2.18/0.67  fof(f402,plain,(
% 2.18/0.67    ( ! [X0] : (~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK4(sK0,X0,u1_struct_0(sK0)),sK5(sK0,X0,u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_pre_topc(sK0,X0)) )),
% 2.18/0.67    inference(duplicate_literal_removal,[],[f401])).
% 2.18/0.67  fof(f401,plain,(
% 2.18/0.67    ( ! [X0] : (~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK4(sK0,X0,u1_struct_0(sK0)),sK5(sK0,X0,u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_pre_topc(sK0,X0) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_pre_topc(sK0,X0)) )),
% 2.18/0.67    inference(resolution,[],[f352,f171])).
% 2.18/0.67  fof(f352,plain,(
% 2.18/0.67    ( ! [X0,X1] : (~r2_hidden(sK4(sK0,X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK4(sK0,X0,X1),sK5(sK0,X0,X1)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = X1) )),
% 2.18/0.67    inference(resolution,[],[f79,f51])).
% 2.18/0.67  fof(f79,plain,(
% 2.18/0.67    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | r2_hidden(sK4(X0,X1,X2),sK5(X0,X1,X2)) | ~r2_hidden(sK4(X0,X1,X2),X2) | k2_pre_topc(X0,X1) = X2) )),
% 2.18/0.67    inference(cnf_transformation,[],[f36])).
% 2.18/0.67  fof(f62,plain,(
% 2.18/0.67    ( ! [X0,X1] : (k2_pre_topc(X0,X1) != k2_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v1_tops_1(X1,X0)) )),
% 2.18/0.67    inference(cnf_transformation,[],[f31])).
% 2.18/0.67  fof(f650,plain,(
% 2.18/0.67    ~r1_xboole_0(sK1,sK2)),
% 2.18/0.67    inference(subsumption_resolution,[],[f649,f439])).
% 2.18/0.67  fof(f439,plain,(
% 2.18/0.67    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.18/0.67    inference(resolution,[],[f438,f44])).
% 2.18/0.67  fof(f44,plain,(
% 2.18/0.67    ~v1_tops_1(sK1,sK0) | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.18/0.67    inference(cnf_transformation,[],[f26])).
% 2.18/0.67  fof(f649,plain,(
% 2.18/0.67    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_xboole_0(sK1,sK2)),
% 2.18/0.67    inference(subsumption_resolution,[],[f628,f441])).
% 2.18/0.67  fof(f441,plain,(
% 2.18/0.67    v3_pre_topc(sK2,sK0)),
% 2.18/0.67    inference(resolution,[],[f438,f46])).
% 2.18/0.67  fof(f46,plain,(
% 2.18/0.67    ~v1_tops_1(sK1,sK0) | v3_pre_topc(sK2,sK0)),
% 2.18/0.67    inference(cnf_transformation,[],[f26])).
% 2.18/0.67  fof(f628,plain,(
% 2.18/0.67    ~v3_pre_topc(sK2,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_xboole_0(sK1,sK2)),
% 2.18/0.67    inference(resolution,[],[f623,f434])).
% 2.18/0.67  fof(f434,plain,(
% 2.18/0.67    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~v3_pre_topc(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_xboole_0(sK1,X1)) )),
% 2.18/0.67    inference(subsumption_resolution,[],[f433,f88])).
% 2.18/0.67  fof(f433,plain,(
% 2.18/0.67    ( ! [X0,X1] : (~r2_hidden(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X1,sK0) | ~r2_hidden(X0,X1) | ~r1_xboole_0(sK1,X1)) )),
% 2.18/0.67    inference(subsumption_resolution,[],[f426,f49])).
% 2.18/0.67  fof(f426,plain,(
% 2.18/0.67    ( ! [X0,X1] : (~r2_hidden(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X1,sK0) | ~r2_hidden(X0,X1) | ~r1_xboole_0(sK1,X1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 2.18/0.67    inference(superposition,[],[f236,f424])).
% 2.18/0.67  fof(f623,plain,(
% 2.18/0.67    r2_hidden(sK4(sK0,k1_xboole_0,sK2),sK2)),
% 2.18/0.67    inference(subsumption_resolution,[],[f618,f442])).
% 2.18/0.67  fof(f442,plain,(
% 2.18/0.67    k1_xboole_0 != sK2),
% 2.18/0.67    inference(resolution,[],[f438,f45])).
% 2.18/0.67  fof(f45,plain,(
% 2.18/0.67    ~v1_tops_1(sK1,sK0) | k1_xboole_0 != sK2),
% 2.18/0.67    inference(cnf_transformation,[],[f26])).
% 2.18/0.67  fof(f618,plain,(
% 2.18/0.67    k1_xboole_0 = sK2 | r2_hidden(sK4(sK0,k1_xboole_0,sK2),sK2)),
% 2.18/0.67    inference(resolution,[],[f614,f439])).
% 2.18/0.67  fof(f614,plain,(
% 2.18/0.67    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = X1 | r2_hidden(sK4(sK0,k1_xboole_0,X1),X1)) )),
% 2.18/0.67    inference(forward_demodulation,[],[f613,f158])).
% 2.18/0.67  fof(f158,plain,(
% 2.18/0.67    k1_xboole_0 = k2_pre_topc(sK0,k1_xboole_0)),
% 2.18/0.67    inference(subsumption_resolution,[],[f157,f51])).
% 2.18/0.67  fof(f157,plain,(
% 2.18/0.67    ~l1_pre_topc(sK0) | k1_xboole_0 = k2_pre_topc(sK0,k1_xboole_0)),
% 2.18/0.67    inference(subsumption_resolution,[],[f156,f53])).
% 2.18/0.67  fof(f156,plain,(
% 2.18/0.67    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | k1_xboole_0 = k2_pre_topc(sK0,k1_xboole_0)),
% 2.18/0.67    inference(resolution,[],[f154,f61])).
% 2.18/0.67  fof(f154,plain,(
% 2.18/0.67    v4_pre_topc(k1_xboole_0,sK0)),
% 2.18/0.67    inference(subsumption_resolution,[],[f153,f53])).
% 2.18/0.67  fof(f153,plain,(
% 2.18/0.67    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(k1_xboole_0,sK0)),
% 2.18/0.67    inference(subsumption_resolution,[],[f151,f114])).
% 2.18/0.67  fof(f114,plain,(
% 2.18/0.67    v3_pre_topc(u1_struct_0(sK0),sK0)),
% 2.18/0.67    inference(forward_demodulation,[],[f113,f111])).
% 2.18/0.67  fof(f113,plain,(
% 2.18/0.67    v3_pre_topc(k2_struct_0(sK0),sK0)),
% 2.18/0.67    inference(subsumption_resolution,[],[f112,f51])).
% 2.18/0.67  fof(f112,plain,(
% 2.18/0.67    ~l1_pre_topc(sK0) | v3_pre_topc(k2_struct_0(sK0),sK0)),
% 2.18/0.67    inference(resolution,[],[f83,f50])).
% 2.18/0.67  fof(f50,plain,(
% 2.18/0.67    v2_pre_topc(sK0)),
% 2.18/0.67    inference(cnf_transformation,[],[f26])).
% 2.18/0.67  fof(f83,plain,(
% 2.18/0.67    ( ! [X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v3_pre_topc(k2_struct_0(X0),X0)) )),
% 2.18/0.67    inference(cnf_transformation,[],[f38])).
% 2.18/0.67  fof(f38,plain,(
% 2.18/0.67    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.18/0.67    inference(flattening,[],[f37])).
% 2.18/0.67  fof(f37,plain,(
% 2.18/0.67    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.18/0.67    inference(ennf_transformation,[],[f21])).
% 2.18/0.67  fof(f21,axiom,(
% 2.18/0.67    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k2_struct_0(X0),X0))),
% 2.18/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_tops_1)).
% 2.18/0.67  fof(f151,plain,(
% 2.18/0.67    ~v3_pre_topc(u1_struct_0(sK0),sK0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(k1_xboole_0,sK0)),
% 2.18/0.67    inference(superposition,[],[f149,f132])).
% 2.18/0.67  fof(f613,plain,(
% 2.18/0.67    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK4(sK0,k1_xboole_0,X1),X1) | k2_pre_topc(sK0,k1_xboole_0) = X1) )),
% 2.18/0.67    inference(subsumption_resolution,[],[f608,f53])).
% 2.18/0.67  fof(f608,plain,(
% 2.18/0.67    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK4(sK0,k1_xboole_0,X1),X1) | k2_pre_topc(sK0,k1_xboole_0) = X1 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 2.18/0.67    inference(trivial_inequality_removal,[],[f607])).
% 2.18/0.67  fof(f607,plain,(
% 2.18/0.67    ( ! [X1] : (k1_xboole_0 != k1_xboole_0 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK4(sK0,k1_xboole_0,X1),X1) | k2_pre_topc(sK0,k1_xboole_0) = X1 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 2.18/0.67    inference(superposition,[],[f533,f141])).
% 2.18/0.67  fof(f141,plain,(
% 2.18/0.67    ( ! [X1] : (k1_xboole_0 = k1_setfam_1(k2_tarski(k1_xboole_0,X1))) )),
% 2.18/0.67    inference(trivial_inequality_removal,[],[f139])).
% 2.18/0.67  fof(f139,plain,(
% 2.18/0.67    ( ! [X1] : (k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k1_setfam_1(k2_tarski(k1_xboole_0,X1))) )),
% 2.18/0.67    inference(superposition,[],[f123,f96])).
% 2.18/0.67  fof(f96,plain,(
% 2.18/0.67    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_setfam_1(k2_tarski(k1_xboole_0,X0)))) )),
% 2.18/0.67    inference(definition_unfolding,[],[f55,f94])).
% 2.18/0.67  fof(f55,plain,(
% 2.18/0.67    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 2.18/0.67    inference(cnf_transformation,[],[f5])).
% 2.18/0.67  fof(f5,axiom,(
% 2.18/0.67    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 2.18/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).
% 2.18/0.67  fof(f123,plain,(
% 2.18/0.67    ( ! [X2,X3] : (k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X3))) != X2 | k1_xboole_0 = k1_setfam_1(k2_tarski(X2,X3))) )),
% 2.18/0.67    inference(resolution,[],[f102,f99])).
% 2.18/0.67  fof(f99,plain,(
% 2.18/0.67    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.18/0.67    inference(definition_unfolding,[],[f90,f84])).
% 2.18/0.67  fof(f90,plain,(
% 2.18/0.67    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 2.18/0.67    inference(cnf_transformation,[],[f1])).
% 2.18/0.67  fof(f1,axiom,(
% 2.18/0.67    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 2.18/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 2.18/0.67  fof(f533,plain,(
% 2.18/0.67    ( ! [X2,X3] : (k1_xboole_0 != k1_setfam_1(k2_tarski(X2,u1_struct_0(sK0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK4(sK0,X2,X3),X3) | k2_pre_topc(sK0,X2) = X3 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 2.18/0.67    inference(resolution,[],[f530,f100])).
% 2.18/0.67  fof(f100,plain,(
% 2.18/0.67    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.18/0.67    inference(definition_unfolding,[],[f89,f84])).
% 2.18/0.67  fof(f89,plain,(
% 2.18/0.67    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) )),
% 2.18/0.67    inference(cnf_transformation,[],[f1])).
% 2.18/0.67  fof(f530,plain,(
% 2.18/0.67    ( ! [X0,X1] : (~r1_xboole_0(X1,u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK4(sK0,X1,X0),X0) | k2_pre_topc(sK0,X1) = X0) )),
% 2.18/0.67    inference(subsumption_resolution,[],[f529,f114])).
% 2.18/0.67  fof(f529,plain,(
% 2.18/0.67    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(u1_struct_0(sK0),sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_xboole_0(X1,u1_struct_0(sK0)) | r2_hidden(sK4(sK0,X1,X0),X0) | k2_pre_topc(sK0,X1) = X0) )),
% 2.18/0.67    inference(subsumption_resolution,[],[f528,f109])).
% 2.18/0.67  fof(f528,plain,(
% 2.18/0.67    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(u1_struct_0(sK0),sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_xboole_0(X1,u1_struct_0(sK0)) | r2_hidden(sK4(sK0,X1,X0),X0) | k2_pre_topc(sK0,X1) = X0) )),
% 2.18/0.67    inference(duplicate_literal_removal,[],[f523])).
% 2.18/0.67  fof(f523,plain,(
% 2.18/0.67    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(u1_struct_0(sK0),sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_xboole_0(X1,u1_struct_0(sK0)) | r2_hidden(sK4(sK0,X1,X0),X0) | k2_pre_topc(sK0,X1) = X0 | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X1) = X0) )),
% 2.18/0.67    inference(resolution,[],[f468,f171])).
% 2.18/0.67  fof(f468,plain,(
% 2.18/0.67    ( ! [X2,X0,X1] : (~r2_hidden(sK4(sK0,X0,X1),X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X2,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_xboole_0(X0,X2) | r2_hidden(sK4(sK0,X0,X1),X1) | k2_pre_topc(sK0,X0) = X1) )),
% 2.18/0.67    inference(resolution,[],[f81,f51])).
% 2.18/0.67  fof(f81,plain,(
% 2.18/0.67    ( ! [X4,X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X4,X0) | ~r2_hidden(sK4(X0,X1,X2),X4) | ~r1_xboole_0(X1,X4) | r2_hidden(sK4(X0,X1,X2),X2) | k2_pre_topc(X0,X1) = X2) )),
% 2.18/0.67    inference(cnf_transformation,[],[f36])).
% 2.18/0.67  % SZS output end Proof for theBenchmark
% 2.18/0.67  % (1643)------------------------------
% 2.18/0.67  % (1643)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.18/0.67  % (1643)Termination reason: Refutation
% 2.18/0.67  
% 2.18/0.67  % (1643)Memory used [KB]: 6780
% 2.18/0.67  % (1643)Time elapsed: 0.194 s
% 2.18/0.67  % (1643)------------------------------
% 2.18/0.67  % (1643)------------------------------
% 2.18/0.67  % (1636)Success in time 0.302 s
%------------------------------------------------------------------------------
