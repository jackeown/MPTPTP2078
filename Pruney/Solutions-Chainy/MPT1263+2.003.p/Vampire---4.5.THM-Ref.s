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
% DateTime   : Thu Dec  3 13:12:16 EST 2020

% Result     : Theorem 2.61s
% Output     : Refutation 2.61s
% Verified   : 
% Statistics : Number of formulae       :  200 (2650 expanded)
%              Number of leaves         :   24 ( 592 expanded)
%              Depth                    :   39
%              Number of atoms          :  679 (11604 expanded)
%              Number of equality atoms :  158 (2095 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1917,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1916,f1277])).

fof(f1277,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f1276,f49])).

fof(f49,plain,
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

fof(f1276,plain,(
    v1_tops_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f1275,f56])).

fof(f56,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f1275,plain,
    ( ~ l1_pre_topc(sK0)
    | v1_tops_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f1274,f54])).

fof(f54,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f28])).

fof(f1274,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | v1_tops_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f1271,f117])).

fof(f117,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(resolution,[],[f113,f56])).

fof(f113,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | u1_struct_0(X0) = k2_struct_0(X0) ) ),
    inference(resolution,[],[f62,f63])).

fof(f63,plain,(
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

fof(f62,plain,(
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

fof(f1271,plain,
    ( u1_struct_0(sK0) != k2_struct_0(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | v1_tops_1(sK1,sK0) ),
    inference(superposition,[],[f67,f998])).

fof(f998,plain,(
    u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) ),
    inference(subsumption_resolution,[],[f997,f54])).

fof(f997,plain,
    ( u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f996,f112])).

fof(f112,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f61,f57])).

fof(f57,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f61,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f996,plain,
    ( u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(duplicate_literal_removal,[],[f995])).

fof(f995,plain,
    ( u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) ),
    inference(resolution,[],[f994,f195])).

fof(f195,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(sK0,X0,X1),u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_pre_topc(sK0,X0) = X1 ) ),
    inference(resolution,[],[f87,f56])).

fof(f87,plain,(
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

fof(f994,plain,
    ( ~ r2_hidden(sK4(sK0,sK1,u1_struct_0(sK0)),u1_struct_0(sK0))
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) ),
    inference(subsumption_resolution,[],[f993,f54])).

fof(f993,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK4(sK0,sK1,u1_struct_0(sK0)),u1_struct_0(sK0))
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) ),
    inference(subsumption_resolution,[],[f992,f112])).

fof(f992,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK4(sK0,sK1,u1_struct_0(sK0)),u1_struct_0(sK0))
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) ),
    inference(subsumption_resolution,[],[f991,f704])).

fof(f704,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f703,f192])).

fof(f192,plain,(
    v3_pre_topc(k1_xboole_0,sK0) ),
    inference(forward_demodulation,[],[f191,f136])).

fof(f136,plain,(
    ! [X0] : k1_xboole_0 = k3_subset_1(X0,X0) ),
    inference(backward_demodulation,[],[f128,f135])).

fof(f135,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f134,f111])).

fof(f111,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f101,f100])).

fof(f100,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f59,f89])).

fof(f89,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f59,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f101,plain,(
    ! [X0] : k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = X0 ),
    inference(definition_unfolding,[],[f60,f99])).

fof(f99,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f90,f89])).

fof(f90,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f60,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f134,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f132,f100])).

fof(f132,plain,(
    ! [X0] : k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = k3_subset_1(X0,k1_xboole_0) ),
    inference(resolution,[],[f103,f58])).

fof(f58,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f103,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ) ),
    inference(definition_unfolding,[],[f92,f99])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f128,plain,(
    ! [X0] : k1_xboole_0 = k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0)) ),
    inference(resolution,[],[f93,f58])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f191,plain,(
    v3_pre_topc(k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)),sK0) ),
    inference(subsumption_resolution,[],[f190,f56])).

fof(f190,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f188,f112])).

fof(f188,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f187,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ l1_pre_topc(X0) ) ),
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

fof(f187,plain,(
    v4_pre_topc(u1_struct_0(sK0),sK0) ),
    inference(subsumption_resolution,[],[f186,f122])).

fof(f122,plain,(
    u1_struct_0(sK0) = k2_pre_topc(sK0,u1_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f121,f117])).

fof(f121,plain,(
    k2_struct_0(sK0) = k2_pre_topc(sK0,k2_struct_0(sK0)) ),
    inference(resolution,[],[f64,f56])).

fof(f64,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | k2_struct_0(X0) = k2_pre_topc(X0,k2_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = k2_pre_topc(X0,k2_struct_0(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => k2_struct_0(X0) = k2_pre_topc(X0,k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_tops_1)).

fof(f186,plain,
    ( u1_struct_0(sK0) != k2_pre_topc(sK0,u1_struct_0(sK0))
    | v4_pre_topc(u1_struct_0(sK0),sK0) ),
    inference(resolution,[],[f183,f112])).

fof(f183,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_pre_topc(sK0,X0) != X0
      | v4_pre_topc(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f182,f56])).

fof(f182,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | k2_pre_topc(sK0,X0) != X0
      | v4_pre_topc(X0,sK0) ) ),
    inference(resolution,[],[f65,f55])).

fof(f55,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k2_pre_topc(X0,X1) != X1
      | v4_pre_topc(X1,X0) ) ),
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

fof(f703,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | ~ v3_pre_topc(k1_xboole_0,sK0) ) ),
    inference(subsumption_resolution,[],[f702,f58])).

fof(f702,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(k1_xboole_0,sK0) ) ),
    inference(trivial_inequality_removal,[],[f700])).

fof(f700,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_xboole_0
      | ~ r2_hidden(X0,k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(k1_xboole_0,sK0) ) ),
    inference(superposition,[],[f665,f100])).

fof(f665,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k1_setfam_1(k2_tarski(u1_struct_0(sK0),X0))
      | ~ r2_hidden(X1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X0,sK0) ) ),
    inference(resolution,[],[f663,f105])).

fof(f105,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k1_xboole_0 != k1_setfam_1(k2_tarski(X0,X1)) ) ),
    inference(definition_unfolding,[],[f95,f89])).

fof(f95,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f663,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(u1_struct_0(sK0),X1)
      | ~ v3_pre_topc(X1,sK0)
      | ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f662,f94])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
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

fof(f662,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X1,sK0)
      | ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(u1_struct_0(sK0),X1) ) ),
    inference(subsumption_resolution,[],[f655,f112])).

fof(f655,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X1,sK0)
      | ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(u1_struct_0(sK0),X1)
      | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(superposition,[],[f649,f122])).

fof(f649,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,k2_pre_topc(sK0,X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X2,sK0)
      | ~ r2_hidden(X1,X2)
      | ~ r1_xboole_0(X0,X2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f648,f98])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
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

fof(f648,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X2,sK0)
      | ~ r2_hidden(X1,X2)
      | ~ r1_xboole_0(X0,X2)
      | ~ r2_hidden(X1,k2_pre_topc(sK0,X0)) ) ),
    inference(resolution,[],[f75,f56])).

fof(f75,plain,(
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

fof(f991,plain,
    ( r2_hidden(sK4(sK0,sK1,u1_struct_0(sK0)),k1_xboole_0)
    | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK4(sK0,sK1,u1_struct_0(sK0)),u1_struct_0(sK0))
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) ),
    inference(duplicate_literal_removal,[],[f990])).

fof(f990,plain,
    ( r2_hidden(sK4(sK0,sK1,u1_struct_0(sK0)),k1_xboole_0)
    | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK4(sK0,sK1,u1_struct_0(sK0)),u1_struct_0(sK0))
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) ),
    inference(superposition,[],[f987,f798])).

fof(f798,plain,
    ( k1_xboole_0 = sK5(sK0,sK1,u1_struct_0(sK0))
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) ),
    inference(subsumption_resolution,[],[f797,f54])).

fof(f797,plain,
    ( u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | k1_xboole_0 = sK5(sK0,sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(duplicate_literal_removal,[],[f796])).

fof(f796,plain,
    ( u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | k1_xboole_0 = sK5(sK0,sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) ),
    inference(resolution,[],[f791,f158])).

fof(f158,plain,(
    ! [X0] :
      ( ~ v1_tops_1(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | u1_struct_0(sK0) = k2_pre_topc(sK0,X0) ) ),
    inference(forward_demodulation,[],[f157,f117])).

fof(f157,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_struct_0(sK0) = k2_pre_topc(sK0,X0)
      | ~ v1_tops_1(X0,sK0) ) ),
    inference(resolution,[],[f68,f56])).

fof(f68,plain,(
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

fof(f791,plain,
    ( v1_tops_1(sK1,sK0)
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | k1_xboole_0 = sK5(sK0,sK1,u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f790,f54])).

fof(f790,plain,
    ( k1_xboole_0 = sK5(sK0,sK1,u1_struct_0(sK0))
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | v1_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(duplicate_literal_removal,[],[f789])).

fof(f789,plain,
    ( k1_xboole_0 = sK5(sK0,sK1,u1_struct_0(sK0))
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | v1_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) ),
    inference(resolution,[],[f787,f280])).

fof(f280,plain,(
    ! [X0] :
      ( v3_pre_topc(sK5(sK0,X0,u1_struct_0(sK0)),sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | u1_struct_0(sK0) = k2_pre_topc(sK0,X0) ) ),
    inference(subsumption_resolution,[],[f279,f112])).

fof(f279,plain,(
    ! [X0] :
      ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | v3_pre_topc(sK5(sK0,X0,u1_struct_0(sK0)),sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | u1_struct_0(sK0) = k2_pre_topc(sK0,X0) ) ),
    inference(duplicate_literal_removal,[],[f278])).

fof(f278,plain,(
    ! [X0] :
      ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | v3_pre_topc(sK5(sK0,X0,u1_struct_0(sK0)),sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | u1_struct_0(sK0) = k2_pre_topc(sK0,X0)
      | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | u1_struct_0(sK0) = k2_pre_topc(sK0,X0) ) ),
    inference(resolution,[],[f277,f195])).

fof(f277,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(sK0,X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v3_pre_topc(sK5(sK0,X0,X1),sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_pre_topc(sK0,X0) = X1 ) ),
    inference(resolution,[],[f83,f56])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(sK5(X0,X1,X2),X0)
      | ~ r2_hidden(sK4(X0,X1,X2),X2)
      | k2_pre_topc(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f787,plain,
    ( ~ v3_pre_topc(sK5(sK0,sK1,u1_struct_0(sK0)),sK0)
    | k1_xboole_0 = sK5(sK0,sK1,u1_struct_0(sK0))
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | v1_tops_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f786,f54])).

fof(f786,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | k1_xboole_0 = sK5(sK0,sK1,u1_struct_0(sK0))
    | ~ v3_pre_topc(sK5(sK0,sK1,u1_struct_0(sK0)),sK0)
    | v1_tops_1(sK1,sK0) ),
    inference(duplicate_literal_removal,[],[f773])).

fof(f773,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | k1_xboole_0 = sK5(sK0,sK1,u1_struct_0(sK0))
    | ~ v3_pre_topc(sK5(sK0,sK1,u1_struct_0(sK0)),sK0)
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | v1_tops_1(sK1,sK0) ),
    inference(resolution,[],[f772,f343])).

fof(f343,plain,
    ( ~ m1_subset_1(sK5(sK0,sK1,u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = sK5(sK0,sK1,u1_struct_0(sK0))
    | ~ v3_pre_topc(sK5(sK0,sK1,u1_struct_0(sK0)),sK0)
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | v1_tops_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f342,f54])).

fof(f342,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | k1_xboole_0 = sK5(sK0,sK1,u1_struct_0(sK0))
    | ~ v3_pre_topc(sK5(sK0,sK1,u1_struct_0(sK0)),sK0)
    | ~ m1_subset_1(sK5(sK0,sK1,u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_tops_1(sK1,sK0) ),
    inference(resolution,[],[f340,f53])).

fof(f53,plain,(
    ! [X2] :
      ( ~ r1_xboole_0(sK1,X2)
      | k1_xboole_0 = X2
      | ~ v3_pre_topc(X2,sK0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_tops_1(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f340,plain,(
    ! [X0] :
      ( r1_xboole_0(X0,sK5(sK0,X0,u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | u1_struct_0(sK0) = k2_pre_topc(sK0,X0) ) ),
    inference(subsumption_resolution,[],[f339,f112])).

fof(f339,plain,(
    ! [X0] :
      ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | r1_xboole_0(X0,sK5(sK0,X0,u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | u1_struct_0(sK0) = k2_pre_topc(sK0,X0) ) ),
    inference(duplicate_literal_removal,[],[f338])).

fof(f338,plain,(
    ! [X0] :
      ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | r1_xboole_0(X0,sK5(sK0,X0,u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | u1_struct_0(sK0) = k2_pre_topc(sK0,X0)
      | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | u1_struct_0(sK0) = k2_pre_topc(sK0,X0) ) ),
    inference(resolution,[],[f337,f195])).

fof(f337,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(sK0,X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | r1_xboole_0(X0,sK5(sK0,X0,X1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_pre_topc(sK0,X0) = X1 ) ),
    inference(resolution,[],[f85,f56])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_xboole_0(X1,sK5(X0,X1,X2))
      | ~ r2_hidden(sK4(X0,X1,X2),X2)
      | k2_pre_topc(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f772,plain,(
    ! [X0] :
      ( m1_subset_1(sK5(sK0,X0,u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | u1_struct_0(sK0) = k2_pre_topc(sK0,X0) ) ),
    inference(subsumption_resolution,[],[f770,f112])).

fof(f770,plain,(
    ! [X0] :
      ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_subset_1(sK5(sK0,X0,u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | u1_struct_0(sK0) = k2_pre_topc(sK0,X0) ) ),
    inference(duplicate_literal_removal,[],[f769])).

fof(f769,plain,(
    ! [X0] :
      ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_subset_1(sK5(sK0,X0,u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | u1_struct_0(sK0) = k2_pre_topc(sK0,X0)
      | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | u1_struct_0(sK0) = k2_pre_topc(sK0,X0) ) ),
    inference(resolution,[],[f765,f195])).

fof(f765,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(sK0,X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_subset_1(sK5(sK0,X0,X1),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_pre_topc(sK0,X0) = X1 ) ),
    inference(resolution,[],[f82,f56])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(sK4(X0,X1,X2),X2)
      | k2_pre_topc(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f987,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(sK0,X0,X1),sK5(sK0,X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(sK4(sK0,X0,X1),X1)
      | k2_pre_topc(sK0,X0) = X1 ) ),
    inference(resolution,[],[f84,f56])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(sK4(X0,X1,X2),sK5(X0,X1,X2))
      | ~ r2_hidden(sK4(X0,X1,X2),X2)
      | k2_pre_topc(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) != k2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v1_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f1916,plain,(
    ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f1899,f1280])).

fof(f1280,plain,(
    k1_xboole_0 != sK2 ),
    inference(resolution,[],[f1276,f50])).

fof(f50,plain,
    ( ~ v1_tops_1(sK1,sK0)
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f28])).

fof(f1899,plain,
    ( k1_xboole_0 = sK2
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f1846,f1333])).

fof(f1333,plain,(
    ! [X0] : ~ r2_hidden(X0,sK2) ),
    inference(subsumption_resolution,[],[f1332,f1277])).

fof(f1332,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK2)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f1325,f1279])).

fof(f1279,plain,(
    v3_pre_topc(sK2,sK0) ),
    inference(resolution,[],[f1276,f51])).

fof(f51,plain,
    ( ~ v1_tops_1(sK1,sK0)
    | v3_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f1325,plain,(
    ! [X0] :
      ( ~ v3_pre_topc(sK2,sK0)
      | ~ r2_hidden(X0,sK2)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f1273,f1278])).

fof(f1278,plain,(
    r1_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f1276,f52])).

fof(f52,plain,
    ( ~ v1_tops_1(sK1,sK0)
    | r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f1273,plain,(
    ! [X4,X3] :
      ( ~ r1_xboole_0(sK1,X4)
      | ~ v3_pre_topc(X4,sK0)
      | ~ r2_hidden(X3,X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f1272,f94])).

fof(f1272,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(X3,u1_struct_0(sK0))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X4,sK0)
      | ~ r2_hidden(X3,X4)
      | ~ r1_xboole_0(sK1,X4) ) ),
    inference(subsumption_resolution,[],[f1269,f54])).

fof(f1269,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(X3,u1_struct_0(sK0))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X4,sK0)
      | ~ r2_hidden(X3,X4)
      | ~ r1_xboole_0(sK1,X4)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(superposition,[],[f649,f998])).

fof(f1846,plain,(
    ! [X2] :
      ( r2_hidden(sK4(sK0,k1_xboole_0,X2),X2)
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(duplicate_literal_removal,[],[f1845])).

fof(f1845,plain,(
    ! [X2] :
      ( k1_xboole_0 = X2
      | k1_xboole_0 = X2
      | r2_hidden(sK4(sK0,k1_xboole_0,X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(forward_demodulation,[],[f1844,f175])).

fof(f175,plain,(
    k1_xboole_0 = k2_pre_topc(sK0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f174,f56])).

fof(f174,plain,
    ( ~ l1_pre_topc(sK0)
    | k1_xboole_0 = k2_pre_topc(sK0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f170,f58])).

fof(f170,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k1_xboole_0 = k2_pre_topc(sK0,k1_xboole_0) ),
    inference(resolution,[],[f167,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k2_pre_topc(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f167,plain,(
    v4_pre_topc(k1_xboole_0,sK0) ),
    inference(subsumption_resolution,[],[f166,f58])).

fof(f166,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(k1_xboole_0,sK0) ),
    inference(subsumption_resolution,[],[f164,f120])).

fof(f120,plain,(
    v3_pre_topc(u1_struct_0(sK0),sK0) ),
    inference(subsumption_resolution,[],[f119,f55])).

fof(f119,plain,
    ( v3_pre_topc(u1_struct_0(sK0),sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f118,f56])).

fof(f118,plain,
    ( v3_pre_topc(u1_struct_0(sK0),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(superposition,[],[f88,f117])).

fof(f88,plain,(
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

fof(f164,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK0),sK0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(k1_xboole_0,sK0) ),
    inference(superposition,[],[f162,f135])).

fof(f162,plain,(
    ! [X0] :
      ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v4_pre_topc(X0,sK0) ) ),
    inference(resolution,[],[f69,f56])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | v4_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f1844,plain,(
    ! [X2] :
      ( k1_xboole_0 = X2
      | r2_hidden(sK4(sK0,k1_xboole_0,X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_pre_topc(sK0,k1_xboole_0) = X2 ) ),
    inference(subsumption_resolution,[],[f1843,f58])).

fof(f1843,plain,(
    ! [X2] :
      ( k1_xboole_0 = X2
      | r2_hidden(sK4(sK0,k1_xboole_0,X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_pre_topc(sK0,k1_xboole_0) = X2 ) ),
    inference(subsumption_resolution,[],[f1842,f120])).

fof(f1842,plain,(
    ! [X2] :
      ( ~ v3_pre_topc(u1_struct_0(sK0),sK0)
      | k1_xboole_0 = X2
      | r2_hidden(sK4(sK0,k1_xboole_0,X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_pre_topc(sK0,k1_xboole_0) = X2 ) ),
    inference(subsumption_resolution,[],[f1832,f112])).

fof(f1832,plain,(
    ! [X2] :
      ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(u1_struct_0(sK0),sK0)
      | k1_xboole_0 = X2
      | r2_hidden(sK4(sK0,k1_xboole_0,X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_pre_topc(sK0,k1_xboole_0) = X2 ) ),
    inference(duplicate_literal_removal,[],[f1824])).

fof(f1824,plain,(
    ! [X2] :
      ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(u1_struct_0(sK0),sK0)
      | k1_xboole_0 = X2
      | r2_hidden(sK4(sK0,k1_xboole_0,X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_pre_topc(sK0,k1_xboole_0) = X2 ) ),
    inference(resolution,[],[f1800,f195])).

fof(f1800,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(sK4(sK0,k1_xboole_0,X5),X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X4,sK0)
      | k1_xboole_0 = X5
      | r2_hidden(sK4(sK0,k1_xboole_0,X5),X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(forward_demodulation,[],[f1799,f175])).

fof(f1799,plain,(
    ! [X4,X5] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X4,sK0)
      | ~ r2_hidden(sK4(sK0,k1_xboole_0,X5),X4)
      | r2_hidden(sK4(sK0,k1_xboole_0,X5),X5)
      | k2_pre_topc(sK0,k1_xboole_0) = X5
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f1796,f58])).

fof(f1796,plain,(
    ! [X4,X5] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X4,sK0)
      | ~ r2_hidden(sK4(sK0,k1_xboole_0,X5),X4)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK4(sK0,k1_xboole_0,X5),X5)
      | k2_pre_topc(sK0,k1_xboole_0) = X5
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(trivial_inequality_removal,[],[f1787])).

fof(f1787,plain,(
    ! [X4,X5] :
      ( k1_xboole_0 != k1_xboole_0
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X4,sK0)
      | ~ r2_hidden(sK4(sK0,k1_xboole_0,X5),X4)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK4(sK0,k1_xboole_0,X5),X5)
      | k2_pre_topc(sK0,k1_xboole_0) = X5
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(superposition,[],[f1480,f123])).

fof(f123,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k2_tarski(k1_xboole_0,X0)) ),
    inference(resolution,[],[f102,f115])).

fof(f115,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(resolution,[],[f97,f58])).

fof(f97,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
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
    inference(definition_unfolding,[],[f91,f89])).

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

fof(f1480,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != k1_setfam_1(k2_tarski(X2,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X1,sK0)
      | ~ r2_hidden(sK4(sK0,X2,X0),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK4(sK0,X2,X0),X0)
      | k2_pre_topc(sK0,X2) = X0
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f1398,f105])).

fof(f1398,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X2,sK0)
      | ~ r2_hidden(sK4(sK0,X0,X1),X2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK4(sK0,X0,X1),X1)
      | k2_pre_topc(sK0,X0) = X1 ) ),
    inference(resolution,[],[f86,f56])).

fof(f86,plain,(
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
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n018.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:31:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.55  % (6214)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.56  % (6205)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.56  % (6206)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.57  % (6213)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.57  % (6222)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.57  % (6221)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.60  % (6221)Refutation not found, incomplete strategy% (6221)------------------------------
% 0.21/0.60  % (6221)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.60  % (6219)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.60  % (6218)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.61  % (6212)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.61  % (6201)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.61  % (6202)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.61  % (6199)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.71/0.61  % (6203)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.71/0.61  % (6228)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.71/0.61  % (6201)Refutation not found, incomplete strategy% (6201)------------------------------
% 1.71/0.61  % (6201)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.71/0.61  % (6201)Termination reason: Refutation not found, incomplete strategy
% 1.71/0.61  
% 1.71/0.61  % (6201)Memory used [KB]: 10874
% 1.71/0.61  % (6201)Time elapsed: 0.166 s
% 1.71/0.61  % (6201)------------------------------
% 1.71/0.61  % (6201)------------------------------
% 1.71/0.61  % (6209)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.71/0.61  % (6224)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.71/0.61  % (6221)Termination reason: Refutation not found, incomplete strategy
% 1.71/0.61  
% 1.71/0.61  % (6221)Memory used [KB]: 11001
% 1.71/0.61  % (6221)Time elapsed: 0.139 s
% 1.71/0.61  % (6221)------------------------------
% 1.71/0.61  % (6221)------------------------------
% 1.71/0.61  % (6216)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.71/0.61  % (6215)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.71/0.62  % (6216)Refutation not found, incomplete strategy% (6216)------------------------------
% 1.71/0.62  % (6216)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.71/0.62  % (6216)Termination reason: Refutation not found, incomplete strategy
% 1.71/0.62  
% 1.71/0.62  % (6216)Memory used [KB]: 10746
% 1.71/0.62  % (6216)Time elapsed: 0.124 s
% 1.71/0.62  % (6216)------------------------------
% 1.71/0.62  % (6216)------------------------------
% 1.71/0.62  % (6211)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.71/0.62  % (6226)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.71/0.62  % (6220)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.71/0.62  % (6207)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.71/0.62  % (6200)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.71/0.62  % (6208)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.71/0.62  % (6227)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.71/0.62  % (6210)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.71/0.62  % (6223)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.71/0.62  % (6204)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.97/0.63  % (6225)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.97/0.64  % (6217)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.97/0.64  % (6207)Refutation not found, incomplete strategy% (6207)------------------------------
% 1.97/0.64  % (6207)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.97/0.64  % (6207)Termination reason: Refutation not found, incomplete strategy
% 1.97/0.64  
% 1.97/0.64  % (6207)Memory used [KB]: 10874
% 1.97/0.64  % (6207)Time elapsed: 0.210 s
% 1.97/0.64  % (6207)------------------------------
% 1.97/0.64  % (6207)------------------------------
% 2.13/0.65  % (6225)Refutation not found, incomplete strategy% (6225)------------------------------
% 2.13/0.65  % (6225)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.13/0.65  % (6225)Termination reason: Refutation not found, incomplete strategy
% 2.13/0.65  
% 2.13/0.65  % (6225)Memory used [KB]: 11001
% 2.13/0.65  % (6225)Time elapsed: 0.224 s
% 2.13/0.65  % (6225)------------------------------
% 2.13/0.65  % (6225)------------------------------
% 2.13/0.66  % (6209)Refutation not found, incomplete strategy% (6209)------------------------------
% 2.13/0.66  % (6209)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.13/0.66  % (6209)Termination reason: Refutation not found, incomplete strategy
% 2.13/0.66  
% 2.13/0.66  % (6209)Memory used [KB]: 11001
% 2.13/0.66  % (6209)Time elapsed: 0.212 s
% 2.13/0.66  % (6209)------------------------------
% 2.13/0.66  % (6209)------------------------------
% 2.13/0.69  % (6237)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.61/0.73  % (6239)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.61/0.74  % (6248)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.61/0.75  % (6205)Refutation found. Thanks to Tanya!
% 2.61/0.75  % SZS status Theorem for theBenchmark
% 2.61/0.75  % SZS output start Proof for theBenchmark
% 2.61/0.75  fof(f1917,plain,(
% 2.61/0.75    $false),
% 2.61/0.75    inference(subsumption_resolution,[],[f1916,f1277])).
% 2.61/0.75  fof(f1277,plain,(
% 2.61/0.75    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.61/0.75    inference(resolution,[],[f1276,f49])).
% 2.61/0.75  fof(f49,plain,(
% 2.61/0.75    ~v1_tops_1(sK1,sK0) | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.61/0.75    inference(cnf_transformation,[],[f28])).
% 2.61/0.75  fof(f28,plain,(
% 2.61/0.75    ? [X0] : (? [X1] : ((v1_tops_1(X1,X0) <~> ! [X2] : (~r1_xboole_0(X1,X2) | ~v3_pre_topc(X2,X0) | k1_xboole_0 = X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.61/0.75    inference(flattening,[],[f27])).
% 2.61/0.75  fof(f27,plain,(
% 2.61/0.75    ? [X0] : (? [X1] : ((v1_tops_1(X1,X0) <~> ! [X2] : ((~r1_xboole_0(X1,X2) | ~v3_pre_topc(X2,X0) | k1_xboole_0 = X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 2.61/0.75    inference(ennf_transformation,[],[f25])).
% 2.61/0.75  fof(f25,negated_conjecture,(
% 2.61/0.75    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_xboole_0(X1,X2) & v3_pre_topc(X2,X0) & k1_xboole_0 != X2)))))),
% 2.61/0.75    inference(negated_conjecture,[],[f24])).
% 2.61/0.75  fof(f24,conjecture,(
% 2.61/0.75    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_xboole_0(X1,X2) & v3_pre_topc(X2,X0) & k1_xboole_0 != X2)))))),
% 2.61/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_tops_1)).
% 2.61/0.75  fof(f1276,plain,(
% 2.61/0.75    v1_tops_1(sK1,sK0)),
% 2.61/0.75    inference(subsumption_resolution,[],[f1275,f56])).
% 2.61/0.75  fof(f56,plain,(
% 2.61/0.75    l1_pre_topc(sK0)),
% 2.61/0.75    inference(cnf_transformation,[],[f28])).
% 2.61/0.75  fof(f1275,plain,(
% 2.61/0.75    ~l1_pre_topc(sK0) | v1_tops_1(sK1,sK0)),
% 2.61/0.75    inference(subsumption_resolution,[],[f1274,f54])).
% 2.61/0.75  fof(f54,plain,(
% 2.61/0.75    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.61/0.75    inference(cnf_transformation,[],[f28])).
% 2.61/0.75  fof(f1274,plain,(
% 2.61/0.75    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | v1_tops_1(sK1,sK0)),
% 2.61/0.75    inference(subsumption_resolution,[],[f1271,f117])).
% 2.61/0.75  fof(f117,plain,(
% 2.61/0.75    u1_struct_0(sK0) = k2_struct_0(sK0)),
% 2.61/0.75    inference(resolution,[],[f113,f56])).
% 2.61/0.75  fof(f113,plain,(
% 2.61/0.75    ( ! [X0] : (~l1_pre_topc(X0) | u1_struct_0(X0) = k2_struct_0(X0)) )),
% 2.61/0.75    inference(resolution,[],[f62,f63])).
% 2.61/0.75  fof(f63,plain,(
% 2.61/0.75    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 2.61/0.75    inference(cnf_transformation,[],[f30])).
% 2.61/0.75  fof(f30,plain,(
% 2.61/0.75    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.61/0.75    inference(ennf_transformation,[],[f17])).
% 2.61/0.75  fof(f17,axiom,(
% 2.61/0.75    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.61/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 2.61/0.75  fof(f62,plain,(
% 2.61/0.75    ( ! [X0] : (~l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0)) )),
% 2.61/0.75    inference(cnf_transformation,[],[f29])).
% 2.61/0.75  fof(f29,plain,(
% 2.61/0.75    ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0))),
% 2.61/0.75    inference(ennf_transformation,[],[f16])).
% 2.61/0.75  fof(f16,axiom,(
% 2.61/0.75    ! [X0] : (l1_struct_0(X0) => u1_struct_0(X0) = k2_struct_0(X0))),
% 2.61/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 2.61/0.75  fof(f1271,plain,(
% 2.61/0.75    u1_struct_0(sK0) != k2_struct_0(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | v1_tops_1(sK1,sK0)),
% 2.61/0.75    inference(superposition,[],[f67,f998])).
% 2.61/0.75  fof(f998,plain,(
% 2.61/0.75    u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)),
% 2.61/0.75    inference(subsumption_resolution,[],[f997,f54])).
% 2.61/0.75  fof(f997,plain,(
% 2.61/0.75    u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.61/0.75    inference(subsumption_resolution,[],[f996,f112])).
% 2.61/0.75  fof(f112,plain,(
% 2.61/0.75    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 2.61/0.75    inference(forward_demodulation,[],[f61,f57])).
% 2.61/0.75  fof(f57,plain,(
% 2.61/0.75    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 2.61/0.75    inference(cnf_transformation,[],[f6])).
% 2.61/0.75  fof(f6,axiom,(
% 2.61/0.75    ! [X0] : k2_subset_1(X0) = X0),
% 2.61/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 2.61/0.75  fof(f61,plain,(
% 2.61/0.75    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 2.61/0.75    inference(cnf_transformation,[],[f8])).
% 2.61/0.75  fof(f8,axiom,(
% 2.61/0.75    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 2.61/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 2.61/0.75  fof(f996,plain,(
% 2.61/0.75    u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.61/0.75    inference(duplicate_literal_removal,[],[f995])).
% 2.61/0.75  fof(f995,plain,(
% 2.61/0.75    u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)),
% 2.61/0.75    inference(resolution,[],[f994,f195])).
% 2.61/0.75  fof(f195,plain,(
% 2.61/0.75    ( ! [X0,X1] : (r2_hidden(sK4(sK0,X0,X1),u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = X1) )),
% 2.61/0.75    inference(resolution,[],[f87,f56])).
% 2.61/0.75  fof(f87,plain,(
% 2.61/0.75    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | r2_hidden(sK4(X0,X1,X2),u1_struct_0(X0)) | k2_pre_topc(X0,X1) = X2) )),
% 2.61/0.75    inference(cnf_transformation,[],[f39])).
% 2.61/0.75  fof(f39,plain,(
% 2.61/0.75    ! [X0] : (! [X1] : (! [X2] : ((k2_pre_topc(X0,X1) = X2 <=> ! [X3] : ((r2_hidden(X3,X2) <=> ! [X4] : (~r1_xboole_0(X1,X4) | ~r2_hidden(X3,X4) | ~v3_pre_topc(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.61/0.75    inference(flattening,[],[f38])).
% 2.61/0.75  fof(f38,plain,(
% 2.61/0.75    ! [X0] : (! [X1] : (! [X2] : ((k2_pre_topc(X0,X1) = X2 <=> ! [X3] : ((r2_hidden(X3,X2) <=> ! [X4] : ((~r1_xboole_0(X1,X4) | ~r2_hidden(X3,X4) | ~v3_pre_topc(X4,X0)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.61/0.75    inference(ennf_transformation,[],[f15])).
% 2.61/0.75  fof(f15,axiom,(
% 2.61/0.75    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (k2_pre_topc(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) <=> ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_xboole_0(X1,X4) & r2_hidden(X3,X4) & v3_pre_topc(X4,X0)))))))))),
% 2.61/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_pre_topc)).
% 2.61/0.75  fof(f994,plain,(
% 2.61/0.75    ~r2_hidden(sK4(sK0,sK1,u1_struct_0(sK0)),u1_struct_0(sK0)) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)),
% 2.61/0.75    inference(subsumption_resolution,[],[f993,f54])).
% 2.61/0.75  fof(f993,plain,(
% 2.61/0.75    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK4(sK0,sK1,u1_struct_0(sK0)),u1_struct_0(sK0)) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)),
% 2.61/0.75    inference(subsumption_resolution,[],[f992,f112])).
% 2.61/0.75  fof(f992,plain,(
% 2.61/0.75    ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK4(sK0,sK1,u1_struct_0(sK0)),u1_struct_0(sK0)) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)),
% 2.61/0.75    inference(subsumption_resolution,[],[f991,f704])).
% 2.61/0.75  fof(f704,plain,(
% 2.61/0.75    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 2.61/0.75    inference(subsumption_resolution,[],[f703,f192])).
% 2.61/0.75  fof(f192,plain,(
% 2.61/0.75    v3_pre_topc(k1_xboole_0,sK0)),
% 2.61/0.75    inference(forward_demodulation,[],[f191,f136])).
% 2.61/0.75  fof(f136,plain,(
% 2.61/0.75    ( ! [X0] : (k1_xboole_0 = k3_subset_1(X0,X0)) )),
% 2.61/0.75    inference(backward_demodulation,[],[f128,f135])).
% 2.61/0.75  fof(f135,plain,(
% 2.61/0.75    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 2.61/0.75    inference(forward_demodulation,[],[f134,f111])).
% 2.61/0.75  fof(f111,plain,(
% 2.61/0.75    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.61/0.75    inference(forward_demodulation,[],[f101,f100])).
% 2.61/0.75  fof(f100,plain,(
% 2.61/0.75    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0))) )),
% 2.61/0.75    inference(definition_unfolding,[],[f59,f89])).
% 2.61/0.75  fof(f89,plain,(
% 2.61/0.75    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.61/0.75    inference(cnf_transformation,[],[f12])).
% 2.61/0.75  fof(f12,axiom,(
% 2.61/0.75    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 2.61/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 2.61/0.75  fof(f59,plain,(
% 2.61/0.75    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 2.61/0.75    inference(cnf_transformation,[],[f4])).
% 2.61/0.75  fof(f4,axiom,(
% 2.61/0.75    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 2.61/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 2.61/0.75  fof(f101,plain,(
% 2.61/0.75    ( ! [X0] : (k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = X0) )),
% 2.61/0.75    inference(definition_unfolding,[],[f60,f99])).
% 2.61/0.75  fof(f99,plain,(
% 2.61/0.75    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 2.61/0.75    inference(definition_unfolding,[],[f90,f89])).
% 2.61/0.75  fof(f90,plain,(
% 2.61/0.75    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.61/0.75    inference(cnf_transformation,[],[f2])).
% 2.61/0.75  fof(f2,axiom,(
% 2.61/0.75    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.61/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.61/0.75  fof(f60,plain,(
% 2.61/0.75    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.61/0.75    inference(cnf_transformation,[],[f5])).
% 2.61/0.75  fof(f5,axiom,(
% 2.61/0.75    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 2.61/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 2.61/0.75  fof(f134,plain,(
% 2.61/0.75    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = k3_subset_1(X0,k1_xboole_0)) )),
% 2.61/0.75    inference(forward_demodulation,[],[f132,f100])).
% 2.61/0.75  fof(f132,plain,(
% 2.61/0.75    ( ! [X0] : (k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = k3_subset_1(X0,k1_xboole_0)) )),
% 2.61/0.75    inference(resolution,[],[f103,f58])).
% 2.61/0.75  fof(f58,plain,(
% 2.61/0.75    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.61/0.75    inference(cnf_transformation,[],[f11])).
% 2.61/0.75  fof(f11,axiom,(
% 2.61/0.75    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.61/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 2.61/0.75  fof(f103,plain,(
% 2.61/0.75    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 2.61/0.75    inference(definition_unfolding,[],[f92,f99])).
% 2.61/0.75  fof(f92,plain,(
% 2.61/0.75    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 2.61/0.75    inference(cnf_transformation,[],[f43])).
% 2.61/0.75  fof(f43,plain,(
% 2.61/0.75    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.61/0.75    inference(ennf_transformation,[],[f7])).
% 2.61/0.75  fof(f7,axiom,(
% 2.61/0.75    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 2.61/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 2.61/0.75  fof(f128,plain,(
% 2.61/0.75    ( ! [X0] : (k1_xboole_0 = k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0))) )),
% 2.61/0.75    inference(resolution,[],[f93,f58])).
% 2.61/0.75  fof(f93,plain,(
% 2.61/0.75    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 2.61/0.75    inference(cnf_transformation,[],[f44])).
% 2.61/0.75  fof(f44,plain,(
% 2.61/0.75    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.61/0.75    inference(ennf_transformation,[],[f9])).
% 2.61/0.75  fof(f9,axiom,(
% 2.61/0.75    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 2.61/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 2.61/0.75  fof(f191,plain,(
% 2.61/0.75    v3_pre_topc(k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)),sK0)),
% 2.61/0.75    inference(subsumption_resolution,[],[f190,f56])).
% 2.61/0.75  fof(f190,plain,(
% 2.61/0.75    v3_pre_topc(k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)),sK0) | ~l1_pre_topc(sK0)),
% 2.61/0.75    inference(subsumption_resolution,[],[f188,f112])).
% 2.61/0.75  fof(f188,plain,(
% 2.61/0.75    ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)),sK0) | ~l1_pre_topc(sK0)),
% 2.61/0.75    inference(resolution,[],[f187,f70])).
% 2.61/0.75  fof(f70,plain,(
% 2.61/0.75    ( ! [X0,X1] : (~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~l1_pre_topc(X0)) )),
% 2.61/0.75    inference(cnf_transformation,[],[f35])).
% 2.61/0.75  fof(f35,plain,(
% 2.61/0.75    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.61/0.75    inference(ennf_transformation,[],[f23])).
% 2.61/0.75  fof(f23,axiom,(
% 2.61/0.75    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 2.61/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tops_1)).
% 2.61/0.75  fof(f187,plain,(
% 2.61/0.75    v4_pre_topc(u1_struct_0(sK0),sK0)),
% 2.61/0.75    inference(subsumption_resolution,[],[f186,f122])).
% 2.61/0.75  fof(f122,plain,(
% 2.61/0.75    u1_struct_0(sK0) = k2_pre_topc(sK0,u1_struct_0(sK0))),
% 2.61/0.75    inference(forward_demodulation,[],[f121,f117])).
% 2.61/0.75  fof(f121,plain,(
% 2.61/0.75    k2_struct_0(sK0) = k2_pre_topc(sK0,k2_struct_0(sK0))),
% 2.61/0.75    inference(resolution,[],[f64,f56])).
% 2.61/0.75  fof(f64,plain,(
% 2.61/0.75    ( ! [X0] : (~l1_pre_topc(X0) | k2_struct_0(X0) = k2_pre_topc(X0,k2_struct_0(X0))) )),
% 2.61/0.75    inference(cnf_transformation,[],[f31])).
% 2.61/0.75  fof(f31,plain,(
% 2.61/0.75    ! [X0] : (k2_struct_0(X0) = k2_pre_topc(X0,k2_struct_0(X0)) | ~l1_pre_topc(X0))),
% 2.61/0.75    inference(ennf_transformation,[],[f22])).
% 2.61/0.75  fof(f22,axiom,(
% 2.61/0.75    ! [X0] : (l1_pre_topc(X0) => k2_struct_0(X0) = k2_pre_topc(X0,k2_struct_0(X0)))),
% 2.61/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_tops_1)).
% 2.61/0.75  fof(f186,plain,(
% 2.61/0.75    u1_struct_0(sK0) != k2_pre_topc(sK0,u1_struct_0(sK0)) | v4_pre_topc(u1_struct_0(sK0),sK0)),
% 2.61/0.75    inference(resolution,[],[f183,f112])).
% 2.61/0.75  fof(f183,plain,(
% 2.61/0.75    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) != X0 | v4_pre_topc(X0,sK0)) )),
% 2.61/0.75    inference(subsumption_resolution,[],[f182,f56])).
% 2.61/0.75  fof(f182,plain,(
% 2.61/0.75    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | k2_pre_topc(sK0,X0) != X0 | v4_pre_topc(X0,sK0)) )),
% 2.61/0.75    inference(resolution,[],[f65,f55])).
% 2.61/0.75  fof(f55,plain,(
% 2.61/0.75    v2_pre_topc(sK0)),
% 2.61/0.75    inference(cnf_transformation,[],[f28])).
% 2.61/0.75  fof(f65,plain,(
% 2.61/0.75    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | k2_pre_topc(X0,X1) != X1 | v4_pre_topc(X1,X0)) )),
% 2.61/0.75    inference(cnf_transformation,[],[f33])).
% 2.61/0.75  fof(f33,plain,(
% 2.61/0.75    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.61/0.75    inference(flattening,[],[f32])).
% 2.61/0.75  fof(f32,plain,(
% 2.61/0.75    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.61/0.75    inference(ennf_transformation,[],[f18])).
% 2.61/0.75  fof(f18,axiom,(
% 2.61/0.75    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 2.61/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).
% 2.61/0.75  fof(f703,plain,(
% 2.61/0.75    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0) | ~v3_pre_topc(k1_xboole_0,sK0)) )),
% 2.61/0.75    inference(subsumption_resolution,[],[f702,f58])).
% 2.61/0.75  fof(f702,plain,(
% 2.61/0.75    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(k1_xboole_0,sK0)) )),
% 2.61/0.75    inference(trivial_inequality_removal,[],[f700])).
% 2.61/0.75  fof(f700,plain,(
% 2.61/0.75    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | ~r2_hidden(X0,k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(k1_xboole_0,sK0)) )),
% 2.61/0.75    inference(superposition,[],[f665,f100])).
% 2.61/0.75  fof(f665,plain,(
% 2.61/0.75    ( ! [X0,X1] : (k1_xboole_0 != k1_setfam_1(k2_tarski(u1_struct_0(sK0),X0)) | ~r2_hidden(X1,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X0,sK0)) )),
% 2.61/0.75    inference(resolution,[],[f663,f105])).
% 2.61/0.75  fof(f105,plain,(
% 2.61/0.75    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.61/0.75    inference(definition_unfolding,[],[f95,f89])).
% 2.61/0.75  fof(f95,plain,(
% 2.61/0.75    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) )),
% 2.61/0.75    inference(cnf_transformation,[],[f1])).
% 2.61/0.75  fof(f1,axiom,(
% 2.61/0.75    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 2.61/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 2.61/0.75  fof(f663,plain,(
% 2.61/0.75    ( ! [X0,X1] : (~r1_xboole_0(u1_struct_0(sK0),X1) | ~v3_pre_topc(X1,sK0) | ~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 2.61/0.75    inference(subsumption_resolution,[],[f662,f94])).
% 2.61/0.75  fof(f94,plain,(
% 2.61/0.75    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | r2_hidden(X2,X0)) )),
% 2.61/0.75    inference(cnf_transformation,[],[f45])).
% 2.61/0.75  fof(f45,plain,(
% 2.61/0.75    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.61/0.75    inference(ennf_transformation,[],[f10])).
% 2.61/0.75  fof(f10,axiom,(
% 2.61/0.75    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 2.61/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 2.61/0.75  fof(f662,plain,(
% 2.61/0.75    ( ! [X0,X1] : (~r2_hidden(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X1,sK0) | ~r2_hidden(X0,X1) | ~r1_xboole_0(u1_struct_0(sK0),X1)) )),
% 2.61/0.75    inference(subsumption_resolution,[],[f655,f112])).
% 2.61/0.75  fof(f655,plain,(
% 2.61/0.75    ( ! [X0,X1] : (~r2_hidden(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X1,sK0) | ~r2_hidden(X0,X1) | ~r1_xboole_0(u1_struct_0(sK0),X1) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 2.61/0.75    inference(superposition,[],[f649,f122])).
% 2.61/0.75  fof(f649,plain,(
% 2.61/0.75    ( ! [X2,X0,X1] : (~r2_hidden(X1,k2_pre_topc(sK0,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X2,sK0) | ~r2_hidden(X1,X2) | ~r1_xboole_0(X0,X2) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 2.61/0.75    inference(subsumption_resolution,[],[f648,f98])).
% 2.61/0.75  fof(f98,plain,(
% 2.61/0.75    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2)) )),
% 2.61/0.75    inference(cnf_transformation,[],[f48])).
% 2.61/0.75  fof(f48,plain,(
% 2.61/0.75    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.61/0.75    inference(flattening,[],[f47])).
% 2.61/0.75  fof(f47,plain,(
% 2.61/0.75    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 2.61/0.75    inference(ennf_transformation,[],[f14])).
% 2.61/0.75  fof(f14,axiom,(
% 2.61/0.75    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 2.61/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 2.61/0.75  fof(f648,plain,(
% 2.61/0.75    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X2,sK0) | ~r2_hidden(X1,X2) | ~r1_xboole_0(X0,X2) | ~r2_hidden(X1,k2_pre_topc(sK0,X0))) )),
% 2.61/0.75    inference(resolution,[],[f75,f56])).
% 2.61/0.75  fof(f75,plain,(
% 2.61/0.75    ( ! [X2,X0,X3,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X3,X0) | ~r2_hidden(X2,X3) | ~r1_xboole_0(X1,X3) | ~r2_hidden(X2,k2_pre_topc(X0,X1))) )),
% 2.61/0.75    inference(cnf_transformation,[],[f37])).
% 2.61/0.75  fof(f37,plain,(
% 2.61/0.75    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k2_pre_topc(X0,X1)) <=> (! [X3] : (~r1_xboole_0(X1,X3) | ~r2_hidden(X2,X3) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & ~v2_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.61/0.75    inference(flattening,[],[f36])).
% 2.61/0.75  fof(f36,plain,(
% 2.61/0.75    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k2_pre_topc(X0,X1)) <=> (! [X3] : ((~r1_xboole_0(X1,X3) | ~r2_hidden(X2,X3) | ~v3_pre_topc(X3,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & ~v2_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.61/0.75    inference(ennf_transformation,[],[f19])).
% 2.61/0.75  fof(f19,axiom,(
% 2.61/0.75    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,k2_pre_topc(X0,X1)) <=> (! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_xboole_0(X1,X3) & r2_hidden(X2,X3) & v3_pre_topc(X3,X0))) & ~v2_struct_0(X0))))))),
% 2.61/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_pre_topc)).
% 2.61/0.75  fof(f991,plain,(
% 2.61/0.75    r2_hidden(sK4(sK0,sK1,u1_struct_0(sK0)),k1_xboole_0) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK4(sK0,sK1,u1_struct_0(sK0)),u1_struct_0(sK0)) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)),
% 2.61/0.75    inference(duplicate_literal_removal,[],[f990])).
% 2.61/0.75  fof(f990,plain,(
% 2.61/0.75    r2_hidden(sK4(sK0,sK1,u1_struct_0(sK0)),k1_xboole_0) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK4(sK0,sK1,u1_struct_0(sK0)),u1_struct_0(sK0)) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)),
% 2.61/0.75    inference(superposition,[],[f987,f798])).
% 2.61/0.75  fof(f798,plain,(
% 2.61/0.75    k1_xboole_0 = sK5(sK0,sK1,u1_struct_0(sK0)) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)),
% 2.61/0.75    inference(subsumption_resolution,[],[f797,f54])).
% 2.61/0.75  fof(f797,plain,(
% 2.61/0.75    u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) | k1_xboole_0 = sK5(sK0,sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.61/0.75    inference(duplicate_literal_removal,[],[f796])).
% 2.61/0.75  fof(f796,plain,(
% 2.61/0.75    u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) | k1_xboole_0 = sK5(sK0,sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)),
% 2.61/0.75    inference(resolution,[],[f791,f158])).
% 2.61/0.75  fof(f158,plain,(
% 2.61/0.75    ( ! [X0] : (~v1_tops_1(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_pre_topc(sK0,X0)) )),
% 2.61/0.75    inference(forward_demodulation,[],[f157,f117])).
% 2.61/0.75  fof(f157,plain,(
% 2.61/0.75    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_struct_0(sK0) = k2_pre_topc(sK0,X0) | ~v1_tops_1(X0,sK0)) )),
% 2.61/0.75    inference(resolution,[],[f68,f56])).
% 2.61/0.75  fof(f68,plain,(
% 2.61/0.75    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = k2_struct_0(X0) | ~v1_tops_1(X1,X0)) )),
% 2.61/0.75    inference(cnf_transformation,[],[f34])).
% 2.61/0.75  fof(f34,plain,(
% 2.61/0.75    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> k2_pre_topc(X0,X1) = k2_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.61/0.75    inference(ennf_transformation,[],[f20])).
% 2.61/0.75  fof(f20,axiom,(
% 2.61/0.75    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> k2_pre_topc(X0,X1) = k2_struct_0(X0))))),
% 2.61/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).
% 2.61/0.75  fof(f791,plain,(
% 2.61/0.75    v1_tops_1(sK1,sK0) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) | k1_xboole_0 = sK5(sK0,sK1,u1_struct_0(sK0))),
% 2.61/0.75    inference(subsumption_resolution,[],[f790,f54])).
% 2.61/0.75  fof(f790,plain,(
% 2.61/0.75    k1_xboole_0 = sK5(sK0,sK1,u1_struct_0(sK0)) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) | v1_tops_1(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.61/0.75    inference(duplicate_literal_removal,[],[f789])).
% 2.61/0.75  fof(f789,plain,(
% 2.61/0.75    k1_xboole_0 = sK5(sK0,sK1,u1_struct_0(sK0)) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) | v1_tops_1(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)),
% 2.61/0.75    inference(resolution,[],[f787,f280])).
% 2.61/0.75  fof(f280,plain,(
% 2.61/0.75    ( ! [X0] : (v3_pre_topc(sK5(sK0,X0,u1_struct_0(sK0)),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_pre_topc(sK0,X0)) )),
% 2.61/0.75    inference(subsumption_resolution,[],[f279,f112])).
% 2.61/0.75  fof(f279,plain,(
% 2.61/0.75    ( ! [X0] : (~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(sK5(sK0,X0,u1_struct_0(sK0)),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_pre_topc(sK0,X0)) )),
% 2.61/0.75    inference(duplicate_literal_removal,[],[f278])).
% 2.61/0.75  fof(f278,plain,(
% 2.61/0.75    ( ! [X0] : (~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(sK5(sK0,X0,u1_struct_0(sK0)),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_pre_topc(sK0,X0) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_pre_topc(sK0,X0)) )),
% 2.61/0.75    inference(resolution,[],[f277,f195])).
% 2.61/0.75  fof(f277,plain,(
% 2.61/0.75    ( ! [X0,X1] : (~r2_hidden(sK4(sK0,X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(sK5(sK0,X0,X1),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = X1) )),
% 2.61/0.75    inference(resolution,[],[f83,f56])).
% 2.61/0.75  fof(f83,plain,(
% 2.61/0.75    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(sK5(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2) | k2_pre_topc(X0,X1) = X2) )),
% 2.61/0.75    inference(cnf_transformation,[],[f39])).
% 2.61/0.75  fof(f787,plain,(
% 2.61/0.75    ~v3_pre_topc(sK5(sK0,sK1,u1_struct_0(sK0)),sK0) | k1_xboole_0 = sK5(sK0,sK1,u1_struct_0(sK0)) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) | v1_tops_1(sK1,sK0)),
% 2.61/0.75    inference(subsumption_resolution,[],[f786,f54])).
% 2.61/0.75  fof(f786,plain,(
% 2.61/0.75    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) | k1_xboole_0 = sK5(sK0,sK1,u1_struct_0(sK0)) | ~v3_pre_topc(sK5(sK0,sK1,u1_struct_0(sK0)),sK0) | v1_tops_1(sK1,sK0)),
% 2.61/0.75    inference(duplicate_literal_removal,[],[f773])).
% 2.61/0.75  fof(f773,plain,(
% 2.61/0.75    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) | k1_xboole_0 = sK5(sK0,sK1,u1_struct_0(sK0)) | ~v3_pre_topc(sK5(sK0,sK1,u1_struct_0(sK0)),sK0) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) | v1_tops_1(sK1,sK0)),
% 2.61/0.75    inference(resolution,[],[f772,f343])).
% 2.61/0.75  fof(f343,plain,(
% 2.61/0.75    ~m1_subset_1(sK5(sK0,sK1,u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = sK5(sK0,sK1,u1_struct_0(sK0)) | ~v3_pre_topc(sK5(sK0,sK1,u1_struct_0(sK0)),sK0) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) | v1_tops_1(sK1,sK0)),
% 2.61/0.75    inference(subsumption_resolution,[],[f342,f54])).
% 2.61/0.75  fof(f342,plain,(
% 2.61/0.75    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) | k1_xboole_0 = sK5(sK0,sK1,u1_struct_0(sK0)) | ~v3_pre_topc(sK5(sK0,sK1,u1_struct_0(sK0)),sK0) | ~m1_subset_1(sK5(sK0,sK1,u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) | v1_tops_1(sK1,sK0)),
% 2.61/0.75    inference(resolution,[],[f340,f53])).
% 2.61/0.75  fof(f53,plain,(
% 2.61/0.75    ( ! [X2] : (~r1_xboole_0(sK1,X2) | k1_xboole_0 = X2 | ~v3_pre_topc(X2,sK0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | v1_tops_1(sK1,sK0)) )),
% 2.61/0.75    inference(cnf_transformation,[],[f28])).
% 2.61/0.75  fof(f340,plain,(
% 2.61/0.75    ( ! [X0] : (r1_xboole_0(X0,sK5(sK0,X0,u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_pre_topc(sK0,X0)) )),
% 2.61/0.75    inference(subsumption_resolution,[],[f339,f112])).
% 2.61/0.75  fof(f339,plain,(
% 2.61/0.75    ( ! [X0] : (~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | r1_xboole_0(X0,sK5(sK0,X0,u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_pre_topc(sK0,X0)) )),
% 2.61/0.75    inference(duplicate_literal_removal,[],[f338])).
% 2.61/0.75  fof(f338,plain,(
% 2.61/0.75    ( ! [X0] : (~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | r1_xboole_0(X0,sK5(sK0,X0,u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_pre_topc(sK0,X0) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_pre_topc(sK0,X0)) )),
% 2.61/0.75    inference(resolution,[],[f337,f195])).
% 2.61/0.75  fof(f337,plain,(
% 2.61/0.75    ( ! [X0,X1] : (~r2_hidden(sK4(sK0,X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | r1_xboole_0(X0,sK5(sK0,X0,X1)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = X1) )),
% 2.61/0.75    inference(resolution,[],[f85,f56])).
% 2.61/0.75  fof(f85,plain,(
% 2.61/0.75    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | r1_xboole_0(X1,sK5(X0,X1,X2)) | ~r2_hidden(sK4(X0,X1,X2),X2) | k2_pre_topc(X0,X1) = X2) )),
% 2.61/0.75    inference(cnf_transformation,[],[f39])).
% 2.61/0.75  fof(f772,plain,(
% 2.61/0.75    ( ! [X0] : (m1_subset_1(sK5(sK0,X0,u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_pre_topc(sK0,X0)) )),
% 2.61/0.75    inference(subsumption_resolution,[],[f770,f112])).
% 2.61/0.75  fof(f770,plain,(
% 2.61/0.75    ( ! [X0] : (~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(sK5(sK0,X0,u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_pre_topc(sK0,X0)) )),
% 2.61/0.75    inference(duplicate_literal_removal,[],[f769])).
% 2.61/0.75  fof(f769,plain,(
% 2.61/0.75    ( ! [X0] : (~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(sK5(sK0,X0,u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_pre_topc(sK0,X0) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_pre_topc(sK0,X0)) )),
% 2.61/0.75    inference(resolution,[],[f765,f195])).
% 2.61/0.75  fof(f765,plain,(
% 2.61/0.75    ( ! [X0,X1] : (~r2_hidden(sK4(sK0,X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(sK5(sK0,X0,X1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = X1) )),
% 2.61/0.75    inference(resolution,[],[f82,f56])).
% 2.61/0.75  fof(f82,plain,(
% 2.61/0.75    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(sK4(X0,X1,X2),X2) | k2_pre_topc(X0,X1) = X2) )),
% 2.61/0.75    inference(cnf_transformation,[],[f39])).
% 2.61/0.75  fof(f987,plain,(
% 2.61/0.75    ( ! [X0,X1] : (r2_hidden(sK4(sK0,X0,X1),sK5(sK0,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK4(sK0,X0,X1),X1) | k2_pre_topc(sK0,X0) = X1) )),
% 2.61/0.75    inference(resolution,[],[f84,f56])).
% 2.61/0.75  fof(f84,plain,(
% 2.61/0.75    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | r2_hidden(sK4(X0,X1,X2),sK5(X0,X1,X2)) | ~r2_hidden(sK4(X0,X1,X2),X2) | k2_pre_topc(X0,X1) = X2) )),
% 2.61/0.75    inference(cnf_transformation,[],[f39])).
% 2.61/0.75  fof(f67,plain,(
% 2.61/0.75    ( ! [X0,X1] : (k2_pre_topc(X0,X1) != k2_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v1_tops_1(X1,X0)) )),
% 2.61/0.75    inference(cnf_transformation,[],[f34])).
% 2.61/0.75  fof(f1916,plain,(
% 2.61/0.75    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.61/0.75    inference(subsumption_resolution,[],[f1899,f1280])).
% 2.61/0.75  fof(f1280,plain,(
% 2.61/0.75    k1_xboole_0 != sK2),
% 2.61/0.75    inference(resolution,[],[f1276,f50])).
% 2.61/0.75  fof(f50,plain,(
% 2.61/0.75    ~v1_tops_1(sK1,sK0) | k1_xboole_0 != sK2),
% 2.61/0.75    inference(cnf_transformation,[],[f28])).
% 2.61/0.75  fof(f1899,plain,(
% 2.61/0.75    k1_xboole_0 = sK2 | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.61/0.75    inference(resolution,[],[f1846,f1333])).
% 2.61/0.75  fof(f1333,plain,(
% 2.61/0.75    ( ! [X0] : (~r2_hidden(X0,sK2)) )),
% 2.61/0.75    inference(subsumption_resolution,[],[f1332,f1277])).
% 2.61/0.75  fof(f1332,plain,(
% 2.61/0.75    ( ! [X0] : (~r2_hidden(X0,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 2.61/0.75    inference(subsumption_resolution,[],[f1325,f1279])).
% 2.61/0.75  fof(f1279,plain,(
% 2.61/0.75    v3_pre_topc(sK2,sK0)),
% 2.61/0.75    inference(resolution,[],[f1276,f51])).
% 2.61/0.75  fof(f51,plain,(
% 2.61/0.75    ~v1_tops_1(sK1,sK0) | v3_pre_topc(sK2,sK0)),
% 2.61/0.75    inference(cnf_transformation,[],[f28])).
% 2.61/0.75  fof(f1325,plain,(
% 2.61/0.75    ( ! [X0] : (~v3_pre_topc(sK2,sK0) | ~r2_hidden(X0,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 2.61/0.75    inference(resolution,[],[f1273,f1278])).
% 2.61/0.75  fof(f1278,plain,(
% 2.61/0.75    r1_xboole_0(sK1,sK2)),
% 2.61/0.75    inference(resolution,[],[f1276,f52])).
% 2.61/0.75  fof(f52,plain,(
% 2.61/0.75    ~v1_tops_1(sK1,sK0) | r1_xboole_0(sK1,sK2)),
% 2.61/0.75    inference(cnf_transformation,[],[f28])).
% 2.61/0.75  fof(f1273,plain,(
% 2.61/0.75    ( ! [X4,X3] : (~r1_xboole_0(sK1,X4) | ~v3_pre_topc(X4,sK0) | ~r2_hidden(X3,X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 2.61/0.75    inference(subsumption_resolution,[],[f1272,f94])).
% 2.61/0.75  fof(f1272,plain,(
% 2.61/0.75    ( ! [X4,X3] : (~r2_hidden(X3,u1_struct_0(sK0)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X4,sK0) | ~r2_hidden(X3,X4) | ~r1_xboole_0(sK1,X4)) )),
% 2.61/0.75    inference(subsumption_resolution,[],[f1269,f54])).
% 2.61/0.76  fof(f1269,plain,(
% 2.61/0.76    ( ! [X4,X3] : (~r2_hidden(X3,u1_struct_0(sK0)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X4,sK0) | ~r2_hidden(X3,X4) | ~r1_xboole_0(sK1,X4) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 2.61/0.76    inference(superposition,[],[f649,f998])).
% 2.61/0.76  fof(f1846,plain,(
% 2.61/0.76    ( ! [X2] : (r2_hidden(sK4(sK0,k1_xboole_0,X2),X2) | k1_xboole_0 = X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 2.61/0.76    inference(duplicate_literal_removal,[],[f1845])).
% 2.61/0.76  fof(f1845,plain,(
% 2.61/0.76    ( ! [X2] : (k1_xboole_0 = X2 | k1_xboole_0 = X2 | r2_hidden(sK4(sK0,k1_xboole_0,X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 2.61/0.76    inference(forward_demodulation,[],[f1844,f175])).
% 2.61/0.76  fof(f175,plain,(
% 2.61/0.76    k1_xboole_0 = k2_pre_topc(sK0,k1_xboole_0)),
% 2.61/0.76    inference(subsumption_resolution,[],[f174,f56])).
% 2.61/0.76  fof(f174,plain,(
% 2.61/0.76    ~l1_pre_topc(sK0) | k1_xboole_0 = k2_pre_topc(sK0,k1_xboole_0)),
% 2.61/0.76    inference(subsumption_resolution,[],[f170,f58])).
% 2.61/0.76  fof(f170,plain,(
% 2.61/0.76    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | k1_xboole_0 = k2_pre_topc(sK0,k1_xboole_0)),
% 2.61/0.76    inference(resolution,[],[f167,f66])).
% 2.61/0.76  fof(f66,plain,(
% 2.61/0.76    ( ! [X0,X1] : (~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | k2_pre_topc(X0,X1) = X1) )),
% 2.61/0.76    inference(cnf_transformation,[],[f33])).
% 2.61/0.76  fof(f167,plain,(
% 2.61/0.76    v4_pre_topc(k1_xboole_0,sK0)),
% 2.61/0.76    inference(subsumption_resolution,[],[f166,f58])).
% 2.61/0.76  fof(f166,plain,(
% 2.61/0.76    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(k1_xboole_0,sK0)),
% 2.61/0.76    inference(subsumption_resolution,[],[f164,f120])).
% 2.61/0.76  fof(f120,plain,(
% 2.61/0.76    v3_pre_topc(u1_struct_0(sK0),sK0)),
% 2.61/0.76    inference(subsumption_resolution,[],[f119,f55])).
% 2.61/0.76  fof(f119,plain,(
% 2.61/0.76    v3_pre_topc(u1_struct_0(sK0),sK0) | ~v2_pre_topc(sK0)),
% 2.61/0.76    inference(subsumption_resolution,[],[f118,f56])).
% 2.61/0.76  fof(f118,plain,(
% 2.61/0.76    v3_pre_topc(u1_struct_0(sK0),sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 2.61/0.76    inference(superposition,[],[f88,f117])).
% 2.61/0.76  fof(f88,plain,(
% 2.61/0.76    ( ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.61/0.76    inference(cnf_transformation,[],[f41])).
% 2.61/0.76  fof(f41,plain,(
% 2.61/0.76    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.61/0.76    inference(flattening,[],[f40])).
% 2.61/0.76  fof(f40,plain,(
% 2.61/0.76    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.61/0.76    inference(ennf_transformation,[],[f21])).
% 2.61/0.76  fof(f21,axiom,(
% 2.61/0.76    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k2_struct_0(X0),X0))),
% 2.61/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_tops_1)).
% 2.61/0.76  fof(f164,plain,(
% 2.61/0.76    ~v3_pre_topc(u1_struct_0(sK0),sK0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(k1_xboole_0,sK0)),
% 2.61/0.76    inference(superposition,[],[f162,f135])).
% 2.61/0.76  fof(f162,plain,(
% 2.61/0.76    ( ! [X0] : (~v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(X0,sK0)) )),
% 2.61/0.76    inference(resolution,[],[f69,f56])).
% 2.61/0.76  fof(f69,plain,(
% 2.61/0.76    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | v4_pre_topc(X1,X0)) )),
% 2.61/0.76    inference(cnf_transformation,[],[f35])).
% 2.61/0.76  fof(f1844,plain,(
% 2.61/0.76    ( ! [X2] : (k1_xboole_0 = X2 | r2_hidden(sK4(sK0,k1_xboole_0,X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,k1_xboole_0) = X2) )),
% 2.61/0.76    inference(subsumption_resolution,[],[f1843,f58])).
% 2.61/0.76  fof(f1843,plain,(
% 2.61/0.76    ( ! [X2] : (k1_xboole_0 = X2 | r2_hidden(sK4(sK0,k1_xboole_0,X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,k1_xboole_0) = X2) )),
% 2.61/0.76    inference(subsumption_resolution,[],[f1842,f120])).
% 2.61/0.76  fof(f1842,plain,(
% 2.61/0.76    ( ! [X2] : (~v3_pre_topc(u1_struct_0(sK0),sK0) | k1_xboole_0 = X2 | r2_hidden(sK4(sK0,k1_xboole_0,X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,k1_xboole_0) = X2) )),
% 2.61/0.76    inference(subsumption_resolution,[],[f1832,f112])).
% 2.61/0.76  fof(f1832,plain,(
% 2.61/0.76    ( ! [X2] : (~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(u1_struct_0(sK0),sK0) | k1_xboole_0 = X2 | r2_hidden(sK4(sK0,k1_xboole_0,X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,k1_xboole_0) = X2) )),
% 2.61/0.76    inference(duplicate_literal_removal,[],[f1824])).
% 2.61/0.76  fof(f1824,plain,(
% 2.61/0.76    ( ! [X2] : (~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(u1_struct_0(sK0),sK0) | k1_xboole_0 = X2 | r2_hidden(sK4(sK0,k1_xboole_0,X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,k1_xboole_0) = X2) )),
% 2.61/0.76    inference(resolution,[],[f1800,f195])).
% 2.61/0.76  fof(f1800,plain,(
% 2.61/0.76    ( ! [X4,X5] : (~r2_hidden(sK4(sK0,k1_xboole_0,X5),X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X4,sK0) | k1_xboole_0 = X5 | r2_hidden(sK4(sK0,k1_xboole_0,X5),X5) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 2.61/0.76    inference(forward_demodulation,[],[f1799,f175])).
% 2.61/0.76  fof(f1799,plain,(
% 2.61/0.76    ( ! [X4,X5] : (~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X4,sK0) | ~r2_hidden(sK4(sK0,k1_xboole_0,X5),X4) | r2_hidden(sK4(sK0,k1_xboole_0,X5),X5) | k2_pre_topc(sK0,k1_xboole_0) = X5 | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 2.61/0.76    inference(subsumption_resolution,[],[f1796,f58])).
% 2.61/0.76  fof(f1796,plain,(
% 2.61/0.76    ( ! [X4,X5] : (~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X4,sK0) | ~r2_hidden(sK4(sK0,k1_xboole_0,X5),X4) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK4(sK0,k1_xboole_0,X5),X5) | k2_pre_topc(sK0,k1_xboole_0) = X5 | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 2.61/0.76    inference(trivial_inequality_removal,[],[f1787])).
% 2.61/0.76  fof(f1787,plain,(
% 2.61/0.76    ( ! [X4,X5] : (k1_xboole_0 != k1_xboole_0 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X4,sK0) | ~r2_hidden(sK4(sK0,k1_xboole_0,X5),X4) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK4(sK0,k1_xboole_0,X5),X5) | k2_pre_topc(sK0,k1_xboole_0) = X5 | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 2.61/0.76    inference(superposition,[],[f1480,f123])).
% 2.61/0.76  fof(f123,plain,(
% 2.61/0.76    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k2_tarski(k1_xboole_0,X0))) )),
% 2.61/0.76    inference(resolution,[],[f102,f115])).
% 2.61/0.76  fof(f115,plain,(
% 2.61/0.76    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.61/0.76    inference(resolution,[],[f97,f58])).
% 2.61/0.76  fof(f97,plain,(
% 2.61/0.76    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 2.61/0.76    inference(cnf_transformation,[],[f46])).
% 2.61/0.76  fof(f46,plain,(
% 2.61/0.76    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 2.61/0.76    inference(ennf_transformation,[],[f26])).
% 2.61/0.76  fof(f26,plain,(
% 2.61/0.76    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 2.61/0.76    inference(unused_predicate_definition_removal,[],[f13])).
% 2.61/0.76  fof(f13,axiom,(
% 2.61/0.76    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.61/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 2.61/0.76  fof(f102,plain,(
% 2.61/0.76    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_setfam_1(k2_tarski(X0,X1)) = X0) )),
% 2.61/0.76    inference(definition_unfolding,[],[f91,f89])).
% 2.61/0.76  fof(f91,plain,(
% 2.61/0.76    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 2.61/0.76    inference(cnf_transformation,[],[f42])).
% 2.61/0.76  fof(f42,plain,(
% 2.61/0.76    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.61/0.76    inference(ennf_transformation,[],[f3])).
% 2.61/0.76  fof(f3,axiom,(
% 2.61/0.76    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.61/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 2.61/0.76  fof(f1480,plain,(
% 2.61/0.76    ( ! [X2,X0,X1] : (k1_xboole_0 != k1_setfam_1(k2_tarski(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X1,sK0) | ~r2_hidden(sK4(sK0,X2,X0),X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK4(sK0,X2,X0),X0) | k2_pre_topc(sK0,X2) = X0 | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 2.61/0.76    inference(resolution,[],[f1398,f105])).
% 2.61/0.76  fof(f1398,plain,(
% 2.61/0.76    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X2,sK0) | ~r2_hidden(sK4(sK0,X0,X1),X2) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK4(sK0,X0,X1),X1) | k2_pre_topc(sK0,X0) = X1) )),
% 2.61/0.76    inference(resolution,[],[f86,f56])).
% 2.61/0.76  fof(f86,plain,(
% 2.61/0.76    ( ! [X4,X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X4,X0) | ~r2_hidden(sK4(X0,X1,X2),X4) | ~r1_xboole_0(X1,X4) | r2_hidden(sK4(X0,X1,X2),X2) | k2_pre_topc(X0,X1) = X2) )),
% 2.61/0.76    inference(cnf_transformation,[],[f39])).
% 2.61/0.76  % SZS output end Proof for theBenchmark
% 2.61/0.76  % (6205)------------------------------
% 2.61/0.76  % (6205)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.61/0.76  % (6205)Termination reason: Refutation
% 2.61/0.76  
% 2.61/0.76  % (6205)Memory used [KB]: 8187
% 2.61/0.76  % (6205)Time elapsed: 0.272 s
% 2.61/0.76  % (6205)------------------------------
% 2.61/0.76  % (6205)------------------------------
% 2.61/0.76  % (6198)Success in time 0.389 s
%------------------------------------------------------------------------------
