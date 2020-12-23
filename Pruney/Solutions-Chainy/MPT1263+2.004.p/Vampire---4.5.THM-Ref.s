%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:12:16 EST 2020

% Result     : Theorem 1.45s
% Output     : Refutation 1.45s
% Verified   : 
% Statistics : Number of formulae       :  186 (4336 expanded)
%              Number of leaves         :   23 ( 912 expanded)
%              Depth                    :   47
%              Number of atoms          :  622 (21976 expanded)
%              Number of equality atoms :  163 (3917 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f690,plain,(
    $false ),
    inference(subsumption_resolution,[],[f689,f451])).

fof(f451,plain,(
    r1_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f449,f47])).

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

fof(f449,plain,(
    v1_tops_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f448,f51])).

fof(f51,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f448,plain,
    ( ~ l1_pre_topc(sK0)
    | v1_tops_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f447,f49])).

fof(f49,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f26])).

fof(f447,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | v1_tops_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f442,f109])).

fof(f109,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(resolution,[],[f108,f51])).

fof(f108,plain,(
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

fof(f442,plain,
    ( u1_struct_0(sK0) != k2_struct_0(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | v1_tops_1(sK1,sK0) ),
    inference(superposition,[],[f62,f431])).

fof(f431,plain,(
    u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) ),
    inference(subsumption_resolution,[],[f430,f94])).

fof(f94,plain,(
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

fof(f430,plain,
    ( u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | k1_xboole_0 != k1_setfam_1(k2_tarski(u1_struct_0(sK0),k1_xboole_0)) ),
    inference(resolution,[],[f427,f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k1_xboole_0 != k1_setfam_1(k2_tarski(X0,X1)) ) ),
    inference(definition_unfolding,[],[f90,f84])).

fof(f90,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f427,plain,
    ( ~ r1_xboole_0(u1_struct_0(sK0),k1_xboole_0)
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) ),
    inference(subsumption_resolution,[],[f426,f339])).

fof(f339,plain,
    ( v3_pre_topc(k1_xboole_0,sK0)
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) ),
    inference(subsumption_resolution,[],[f332,f49])).

fof(f332,plain,
    ( v3_pre_topc(k1_xboole_0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) ),
    inference(duplicate_literal_removal,[],[f331])).

fof(f331,plain,
    ( v3_pre_topc(k1_xboole_0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) ),
    inference(superposition,[],[f226,f324])).

fof(f324,plain,
    ( k1_xboole_0 = sK5(sK0,sK1,u1_struct_0(sK0))
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) ),
    inference(duplicate_literal_removal,[],[f323])).

fof(f323,plain,
    ( u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | k1_xboole_0 = sK5(sK0,sK1,u1_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f322,f109])).

fof(f322,plain,
    ( u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | k1_xboole_0 = sK5(sK0,sK1,u1_struct_0(sK0))
    | k2_struct_0(sK0) = k2_pre_topc(sK0,sK1) ),
    inference(subsumption_resolution,[],[f321,f51])).

fof(f321,plain,
    ( u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | k1_xboole_0 = sK5(sK0,sK1,u1_struct_0(sK0))
    | k2_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f320,f49])).

fof(f320,plain,
    ( u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | k1_xboole_0 = sK5(sK0,sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f315,f63])).

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

fof(f315,plain,
    ( v1_tops_1(sK1,sK0)
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | k1_xboole_0 = sK5(sK0,sK1,u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f314,f49])).

fof(f314,plain,
    ( k1_xboole_0 = sK5(sK0,sK1,u1_struct_0(sK0))
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | v1_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(duplicate_literal_removal,[],[f312])).

fof(f312,plain,
    ( k1_xboole_0 = sK5(sK0,sK1,u1_struct_0(sK0))
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | v1_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) ),
    inference(resolution,[],[f296,f231])).

fof(f231,plain,(
    ! [X0] :
      ( r1_xboole_0(X0,sK5(sK0,X0,u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | u1_struct_0(sK0) = k2_pre_topc(sK0,X0) ) ),
    inference(subsumption_resolution,[],[f230,f107])).

fof(f107,plain,(
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

fof(f230,plain,(
    ! [X0] :
      ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | r1_xboole_0(X0,sK5(sK0,X0,u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | u1_struct_0(sK0) = k2_pre_topc(sK0,X0) ) ),
    inference(duplicate_literal_removal,[],[f229])).

fof(f229,plain,(
    ! [X0] :
      ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | r1_xboole_0(X0,sK5(sK0,X0,u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | u1_struct_0(sK0) = k2_pre_topc(sK0,X0)
      | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | u1_struct_0(sK0) = k2_pre_topc(sK0,X0) ) ),
    inference(resolution,[],[f228,f206])).

fof(f206,plain,(
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

fof(f228,plain,(
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

fof(f296,plain,
    ( ~ r1_xboole_0(sK1,sK5(sK0,sK1,u1_struct_0(sK0)))
    | k1_xboole_0 = sK5(sK0,sK1,u1_struct_0(sK0))
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | v1_tops_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f295,f49])).

fof(f295,plain,
    ( u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | k1_xboole_0 = sK5(sK0,sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_xboole_0(sK1,sK5(sK0,sK1,u1_struct_0(sK0)))
    | v1_tops_1(sK1,sK0) ),
    inference(duplicate_literal_removal,[],[f290])).

fof(f290,plain,
    ( u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | k1_xboole_0 = sK5(sK0,sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_xboole_0(sK1,sK5(sK0,sK1,u1_struct_0(sK0)))
    | v1_tops_1(sK1,sK0) ),
    inference(resolution,[],[f278,f227])).

fof(f227,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK5(sK0,X0,u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
      | u1_struct_0(sK0) = k2_pre_topc(sK0,X0)
      | k1_xboole_0 = sK5(sK0,X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_xboole_0(sK1,sK5(sK0,X0,u1_struct_0(sK0)))
      | v1_tops_1(sK1,sK0) ) ),
    inference(resolution,[],[f226,f48])).

fof(f48,plain,(
    ! [X2] :
      ( ~ v3_pre_topc(X2,sK0)
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_xboole_0(sK1,X2)
      | v1_tops_1(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f278,plain,
    ( m1_subset_1(sK5(sK0,sK1,u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) ),
    inference(resolution,[],[f277,f49])).

fof(f277,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_subset_1(sK5(sK0,X0,u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
      | u1_struct_0(sK0) = k2_pre_topc(sK0,X0) ) ),
    inference(subsumption_resolution,[],[f276,f107])).

fof(f276,plain,(
    ! [X0] :
      ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_subset_1(sK5(sK0,X0,u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | u1_struct_0(sK0) = k2_pre_topc(sK0,X0) ) ),
    inference(duplicate_literal_removal,[],[f275])).

fof(f275,plain,(
    ! [X0] :
      ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_subset_1(sK5(sK0,X0,u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | u1_struct_0(sK0) = k2_pre_topc(sK0,X0)
      | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | u1_struct_0(sK0) = k2_pre_topc(sK0,X0) ) ),
    inference(resolution,[],[f274,f206])).

fof(f274,plain,(
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

fof(f226,plain,(
    ! [X0] :
      ( v3_pre_topc(sK5(sK0,X0,u1_struct_0(sK0)),sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | u1_struct_0(sK0) = k2_pre_topc(sK0,X0) ) ),
    inference(subsumption_resolution,[],[f225,f107])).

fof(f225,plain,(
    ! [X0] :
      ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | v3_pre_topc(sK5(sK0,X0,u1_struct_0(sK0)),sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | u1_struct_0(sK0) = k2_pre_topc(sK0,X0) ) ),
    inference(duplicate_literal_removal,[],[f224])).

fof(f224,plain,(
    ! [X0] :
      ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | v3_pre_topc(sK5(sK0,X0,u1_struct_0(sK0)),sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | u1_struct_0(sK0) = k2_pre_topc(sK0,X0)
      | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | u1_struct_0(sK0) = k2_pre_topc(sK0,X0) ) ),
    inference(resolution,[],[f223,f206])).

fof(f223,plain,(
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

fof(f426,plain,
    ( u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | ~ v3_pre_topc(k1_xboole_0,sK0)
    | ~ r1_xboole_0(u1_struct_0(sK0),k1_xboole_0) ),
    inference(subsumption_resolution,[],[f425,f53])).

fof(f53,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f425,plain,
    ( u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | ~ v3_pre_topc(k1_xboole_0,sK0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_xboole_0(u1_struct_0(sK0),k1_xboole_0) ),
    inference(duplicate_literal_removal,[],[f422])).

fof(f422,plain,
    ( u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | ~ v3_pre_topc(k1_xboole_0,sK0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_xboole_0(u1_struct_0(sK0),k1_xboole_0)
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) ),
    inference(resolution,[],[f420,f362])).

fof(f362,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v3_pre_topc(X1,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_xboole_0(u1_struct_0(sK0),X1)
      | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) ) ),
    inference(subsumption_resolution,[],[f361,f89])).

fof(f89,plain,(
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

fof(f361,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X1,sK0)
      | ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(u1_struct_0(sK0),X1)
      | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) ) ),
    inference(subsumption_resolution,[],[f349,f107])).

fof(f349,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X1,sK0)
      | ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(u1_struct_0(sK0),X1)
      | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) ) ),
    inference(superposition,[],[f268,f348])).

fof(f348,plain,
    ( u1_struct_0(sK0) = k2_pre_topc(sK0,u1_struct_0(sK0))
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) ),
    inference(subsumption_resolution,[],[f347,f51])).

fof(f347,plain,
    ( u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | u1_struct_0(sK0) = k2_pre_topc(sK0,u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f344,f107])).

fof(f344,plain,
    ( u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | u1_struct_0(sK0) = k2_pre_topc(sK0,u1_struct_0(sK0)) ),
    inference(resolution,[],[f341,f61])).

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

fof(f341,plain,
    ( v4_pre_topc(u1_struct_0(sK0),sK0)
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) ),
    inference(resolution,[],[f339,f136])).

fof(f136,plain,
    ( ~ v3_pre_topc(k1_xboole_0,sK0)
    | v4_pre_topc(u1_struct_0(sK0),sK0) ),
    inference(subsumption_resolution,[],[f133,f107])).

fof(f133,plain,
    ( ~ v3_pre_topc(k1_xboole_0,sK0)
    | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(u1_struct_0(sK0),sK0) ),
    inference(superposition,[],[f130,f126])).

fof(f126,plain,(
    ! [X0] : k1_xboole_0 = k3_subset_1(X0,X0) ),
    inference(backward_demodulation,[],[f116,f125])).

fof(f125,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f124,f106])).

fof(f106,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f96,f94])).

fof(f96,plain,(
    ! [X0] : k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = X0 ),
    inference(definition_unfolding,[],[f56,f93])).

fof(f93,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f86,f84])).

fof(f86,plain,(
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

fof(f124,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f122,f94])).

fof(f122,plain,(
    ! [X0] : k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = k3_subset_1(X0,k1_xboole_0) ),
    inference(resolution,[],[f98,f53])).

fof(f98,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ) ),
    inference(definition_unfolding,[],[f87,f93])).

fof(f87,plain,(
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

fof(f116,plain,(
    ! [X0] : k1_xboole_0 = k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0)) ),
    inference(resolution,[],[f88,f53])).

fof(f88,plain,(
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

fof(f130,plain,(
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

fof(f268,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,k2_pre_topc(sK0,X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X2,sK0)
      | ~ r2_hidden(X1,X2)
      | ~ r1_xboole_0(X0,X2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f267,f92])).

fof(f92,plain,(
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

fof(f267,plain,(
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

fof(f420,plain,
    ( r2_hidden(sK4(sK0,sK1,u1_struct_0(sK0)),k1_xboole_0)
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) ),
    inference(subsumption_resolution,[],[f417,f49])).

fof(f417,plain,
    ( r2_hidden(sK4(sK0,sK1,u1_struct_0(sK0)),k1_xboole_0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) ),
    inference(duplicate_literal_removal,[],[f416])).

fof(f416,plain,
    ( r2_hidden(sK4(sK0,sK1,u1_struct_0(sK0)),k1_xboole_0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) ),
    inference(superposition,[],[f412,f324])).

fof(f412,plain,(
    ! [X0] :
      ( r2_hidden(sK4(sK0,X0,u1_struct_0(sK0)),sK5(sK0,X0,u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | u1_struct_0(sK0) = k2_pre_topc(sK0,X0) ) ),
    inference(subsumption_resolution,[],[f411,f107])).

fof(f411,plain,(
    ! [X0] :
      ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK4(sK0,X0,u1_struct_0(sK0)),sK5(sK0,X0,u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | u1_struct_0(sK0) = k2_pre_topc(sK0,X0) ) ),
    inference(duplicate_literal_removal,[],[f410])).

fof(f410,plain,(
    ! [X0] :
      ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK4(sK0,X0,u1_struct_0(sK0)),sK5(sK0,X0,u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | u1_struct_0(sK0) = k2_pre_topc(sK0,X0)
      | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | u1_struct_0(sK0) = k2_pre_topc(sK0,X0) ) ),
    inference(resolution,[],[f372,f206])).

fof(f372,plain,(
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

fof(f689,plain,(
    ~ r1_xboole_0(sK1,sK2) ),
    inference(subsumption_resolution,[],[f688,f450])).

fof(f450,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f449,f44])).

fof(f44,plain,
    ( ~ v1_tops_1(sK1,sK0)
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f26])).

fof(f688,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_xboole_0(sK1,sK2) ),
    inference(subsumption_resolution,[],[f669,f452])).

fof(f452,plain,(
    v3_pre_topc(sK2,sK0) ),
    inference(resolution,[],[f449,f46])).

fof(f46,plain,
    ( ~ v1_tops_1(sK1,sK0)
    | v3_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f669,plain,
    ( ~ v3_pre_topc(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f664,f445])).

fof(f445,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v3_pre_topc(X1,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_xboole_0(sK1,X1) ) ),
    inference(subsumption_resolution,[],[f444,f89])).

fof(f444,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X1,sK0)
      | ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(sK1,X1) ) ),
    inference(subsumption_resolution,[],[f435,f49])).

fof(f435,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X1,sK0)
      | ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(sK1,X1)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(superposition,[],[f268,f431])).

fof(f664,plain,(
    r2_hidden(sK4(sK0,k1_xboole_0,sK2),sK2) ),
    inference(subsumption_resolution,[],[f657,f453])).

fof(f453,plain,(
    k1_xboole_0 != sK2 ),
    inference(resolution,[],[f449,f45])).

fof(f45,plain,
    ( ~ v1_tops_1(sK1,sK0)
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f26])).

fof(f657,plain,
    ( k1_xboole_0 = sK2
    | r2_hidden(sK4(sK0,k1_xboole_0,sK2),sK2) ),
    inference(resolution,[],[f653,f450])).

fof(f653,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | k1_xboole_0 = X1
      | r2_hidden(sK4(sK0,k1_xboole_0,X1),X1) ) ),
    inference(forward_demodulation,[],[f652,f139])).

fof(f139,plain,(
    k1_xboole_0 = k2_pre_topc(sK0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f138,f51])).

fof(f138,plain,
    ( ~ l1_pre_topc(sK0)
    | k1_xboole_0 = k2_pre_topc(sK0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f137,f53])).

fof(f137,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k1_xboole_0 = k2_pre_topc(sK0,k1_xboole_0) ),
    inference(resolution,[],[f135,f61])).

fof(f135,plain,(
    v4_pre_topc(k1_xboole_0,sK0) ),
    inference(subsumption_resolution,[],[f134,f53])).

fof(f134,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(k1_xboole_0,sK0) ),
    inference(subsumption_resolution,[],[f132,f112])).

fof(f112,plain,(
    v3_pre_topc(u1_struct_0(sK0),sK0) ),
    inference(forward_demodulation,[],[f111,f109])).

fof(f111,plain,(
    v3_pre_topc(k2_struct_0(sK0),sK0) ),
    inference(subsumption_resolution,[],[f110,f51])).

fof(f110,plain,
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

fof(f132,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK0),sK0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(k1_xboole_0,sK0) ),
    inference(superposition,[],[f130,f125])).

fof(f652,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK4(sK0,k1_xboole_0,X1),X1)
      | k2_pre_topc(sK0,k1_xboole_0) = X1 ) ),
    inference(subsumption_resolution,[],[f648,f53])).

fof(f648,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK4(sK0,k1_xboole_0,X1),X1)
      | k2_pre_topc(sK0,k1_xboole_0) = X1
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(trivial_inequality_removal,[],[f647])).

fof(f647,plain,(
    ! [X1] :
      ( k1_xboole_0 != k1_xboole_0
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK4(sK0,k1_xboole_0,X1),X1)
      | k2_pre_topc(sK0,k1_xboole_0) = X1
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(superposition,[],[f624,f160])).

fof(f160,plain,(
    ! [X3] : k1_xboole_0 = k1_setfam_1(k2_tarski(k1_xboole_0,X3)) ),
    inference(forward_demodulation,[],[f151,f95])).

fof(f95,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_setfam_1(k2_tarski(k1_xboole_0,X0))) ),
    inference(definition_unfolding,[],[f55,f93])).

fof(f55,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(f151,plain,(
    ! [X3] : k5_xboole_0(k1_xboole_0,k1_setfam_1(k2_tarski(k1_xboole_0,k1_xboole_0))) = k1_setfam_1(k2_tarski(k1_xboole_0,X3)) ),
    inference(superposition,[],[f97,f95])).

fof(f97,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))))) ),
    inference(definition_unfolding,[],[f85,f84,f93,f93])).

fof(f85,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f624,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k1_setfam_1(k2_tarski(X0,u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK4(sK0,X0,X1),X1)
      | k2_pre_topc(sK0,X0) = X1
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f586,f100])).

fof(f586,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK4(sK0,X1,X0),X0)
      | k2_pre_topc(sK0,X1) = X0 ) ),
    inference(subsumption_resolution,[],[f585,f206])).

fof(f585,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(sK4(sK0,X1,X0),u1_struct_0(sK0))
      | ~ r1_xboole_0(X1,u1_struct_0(sK0))
      | r2_hidden(sK4(sK0,X1,X0),X0)
      | k2_pre_topc(sK0,X1) = X0 ) ),
    inference(subsumption_resolution,[],[f580,f107])).

fof(f580,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(sK4(sK0,X1,X0),u1_struct_0(sK0))
      | ~ r1_xboole_0(X1,u1_struct_0(sK0))
      | r2_hidden(sK4(sK0,X1,X0),X0)
      | k2_pre_topc(sK0,X1) = X0 ) ),
    inference(resolution,[],[f497,f112])).

fof(f497,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_pre_topc(X2,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(sK4(sK0,X0,X1),X2)
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
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n014.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:54:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.51  % (17358)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.51  % (17349)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.52  % (17350)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.24/0.52  % (17351)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.24/0.53  % (17355)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.24/0.53  % (17359)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.24/0.53  % (17357)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.24/0.53  % (17366)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.24/0.53  % (17375)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.24/0.53  % (17363)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.24/0.53  % (17373)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.24/0.53  % (17371)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.24/0.53  % (17354)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.24/0.54  % (17368)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.24/0.54  % (17363)Refutation not found, incomplete strategy% (17363)------------------------------
% 1.24/0.54  % (17363)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.54  % (17363)Termination reason: Refutation not found, incomplete strategy
% 1.24/0.54  
% 1.24/0.54  % (17363)Memory used [KB]: 10746
% 1.24/0.54  % (17363)Time elapsed: 0.120 s
% 1.24/0.54  % (17363)------------------------------
% 1.24/0.54  % (17363)------------------------------
% 1.24/0.54  % (17369)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.24/0.54  % (17367)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.24/0.54  % (17365)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.24/0.54  % (17348)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.24/0.54  % (17364)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.24/0.54  % (17346)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.24/0.54  % (17374)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.24/0.54  % (17362)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.24/0.54  % (17352)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.24/0.55  % (17370)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.24/0.55  % (17347)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.45/0.55  % (17361)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.45/0.55  % (17360)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.45/0.55  % (17353)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.45/0.55  % (17356)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.45/0.55  % (17372)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.45/0.56  % (17368)Refutation not found, incomplete strategy% (17368)------------------------------
% 1.45/0.56  % (17368)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.57  % (17368)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.57  
% 1.45/0.57  % (17368)Memory used [KB]: 10874
% 1.45/0.57  % (17368)Time elapsed: 0.116 s
% 1.45/0.57  % (17368)------------------------------
% 1.45/0.57  % (17368)------------------------------
% 1.45/0.58  % (17356)Refutation not found, incomplete strategy% (17356)------------------------------
% 1.45/0.58  % (17356)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.58  % (17356)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.58  
% 1.45/0.58  % (17356)Memory used [KB]: 11001
% 1.45/0.58  % (17356)Time elapsed: 0.168 s
% 1.45/0.58  % (17356)------------------------------
% 1.45/0.58  % (17356)------------------------------
% 1.45/0.60  % (17352)Refutation found. Thanks to Tanya!
% 1.45/0.60  % SZS status Theorem for theBenchmark
% 1.45/0.60  % SZS output start Proof for theBenchmark
% 1.45/0.60  fof(f690,plain,(
% 1.45/0.60    $false),
% 1.45/0.60    inference(subsumption_resolution,[],[f689,f451])).
% 1.45/0.60  fof(f451,plain,(
% 1.45/0.60    r1_xboole_0(sK1,sK2)),
% 1.45/0.60    inference(resolution,[],[f449,f47])).
% 1.45/0.60  fof(f47,plain,(
% 1.45/0.60    ~v1_tops_1(sK1,sK0) | r1_xboole_0(sK1,sK2)),
% 1.45/0.60    inference(cnf_transformation,[],[f26])).
% 1.45/0.60  fof(f26,plain,(
% 1.45/0.60    ? [X0] : (? [X1] : ((v1_tops_1(X1,X0) <~> ! [X2] : (~r1_xboole_0(X1,X2) | ~v3_pre_topc(X2,X0) | k1_xboole_0 = X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.45/0.60    inference(flattening,[],[f25])).
% 1.45/0.60  fof(f25,plain,(
% 1.45/0.60    ? [X0] : (? [X1] : ((v1_tops_1(X1,X0) <~> ! [X2] : ((~r1_xboole_0(X1,X2) | ~v3_pre_topc(X2,X0) | k1_xboole_0 = X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 1.45/0.60    inference(ennf_transformation,[],[f24])).
% 1.45/0.60  fof(f24,negated_conjecture,(
% 1.45/0.60    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_xboole_0(X1,X2) & v3_pre_topc(X2,X0) & k1_xboole_0 != X2)))))),
% 1.45/0.60    inference(negated_conjecture,[],[f23])).
% 1.45/0.60  fof(f23,conjecture,(
% 1.45/0.60    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_xboole_0(X1,X2) & v3_pre_topc(X2,X0) & k1_xboole_0 != X2)))))),
% 1.45/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_tops_1)).
% 1.45/0.60  fof(f449,plain,(
% 1.45/0.60    v1_tops_1(sK1,sK0)),
% 1.45/0.60    inference(subsumption_resolution,[],[f448,f51])).
% 1.45/0.60  fof(f51,plain,(
% 1.45/0.60    l1_pre_topc(sK0)),
% 1.45/0.60    inference(cnf_transformation,[],[f26])).
% 1.45/0.60  fof(f448,plain,(
% 1.45/0.60    ~l1_pre_topc(sK0) | v1_tops_1(sK1,sK0)),
% 1.45/0.60    inference(subsumption_resolution,[],[f447,f49])).
% 1.45/0.60  fof(f49,plain,(
% 1.45/0.60    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.45/0.60    inference(cnf_transformation,[],[f26])).
% 1.45/0.60  fof(f447,plain,(
% 1.45/0.60    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | v1_tops_1(sK1,sK0)),
% 1.45/0.60    inference(subsumption_resolution,[],[f442,f109])).
% 1.45/0.60  fof(f109,plain,(
% 1.45/0.60    u1_struct_0(sK0) = k2_struct_0(sK0)),
% 1.45/0.60    inference(resolution,[],[f108,f51])).
% 1.45/0.60  fof(f108,plain,(
% 1.45/0.60    ( ! [X0] : (~l1_pre_topc(X0) | u1_struct_0(X0) = k2_struct_0(X0)) )),
% 1.45/0.60    inference(resolution,[],[f58,f59])).
% 1.45/0.60  fof(f59,plain,(
% 1.45/0.60    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.45/0.60    inference(cnf_transformation,[],[f28])).
% 1.45/0.60  fof(f28,plain,(
% 1.45/0.60    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.45/0.60    inference(ennf_transformation,[],[f17])).
% 1.45/0.60  fof(f17,axiom,(
% 1.45/0.60    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.45/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 1.45/0.60  fof(f58,plain,(
% 1.45/0.60    ( ! [X0] : (~l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0)) )),
% 1.45/0.60    inference(cnf_transformation,[],[f27])).
% 1.45/0.60  fof(f27,plain,(
% 1.45/0.60    ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0))),
% 1.45/0.60    inference(ennf_transformation,[],[f16])).
% 1.45/0.60  fof(f16,axiom,(
% 1.45/0.60    ! [X0] : (l1_struct_0(X0) => u1_struct_0(X0) = k2_struct_0(X0))),
% 1.45/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 1.45/0.60  fof(f442,plain,(
% 1.45/0.60    u1_struct_0(sK0) != k2_struct_0(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | v1_tops_1(sK1,sK0)),
% 1.45/0.60    inference(superposition,[],[f62,f431])).
% 1.45/0.60  fof(f431,plain,(
% 1.45/0.60    u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)),
% 1.45/0.60    inference(subsumption_resolution,[],[f430,f94])).
% 1.45/0.60  fof(f94,plain,(
% 1.45/0.60    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0))) )),
% 1.45/0.60    inference(definition_unfolding,[],[f54,f84])).
% 1.45/0.60  fof(f84,plain,(
% 1.45/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.45/0.60    inference(cnf_transformation,[],[f13])).
% 1.45/0.60  fof(f13,axiom,(
% 1.45/0.60    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.45/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.45/0.60  fof(f54,plain,(
% 1.45/0.60    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.45/0.60    inference(cnf_transformation,[],[f3])).
% 1.45/0.60  fof(f3,axiom,(
% 1.45/0.60    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.45/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 1.45/0.60  fof(f430,plain,(
% 1.45/0.60    u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) | k1_xboole_0 != k1_setfam_1(k2_tarski(u1_struct_0(sK0),k1_xboole_0))),
% 1.45/0.60    inference(resolution,[],[f427,f100])).
% 1.45/0.60  fof(f100,plain,(
% 1.45/0.60    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.45/0.60    inference(definition_unfolding,[],[f90,f84])).
% 1.45/0.60  fof(f90,plain,(
% 1.45/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) )),
% 1.45/0.60    inference(cnf_transformation,[],[f1])).
% 1.45/0.60  fof(f1,axiom,(
% 1.45/0.60    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.45/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.45/0.60  fof(f427,plain,(
% 1.45/0.60    ~r1_xboole_0(u1_struct_0(sK0),k1_xboole_0) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)),
% 1.45/0.60    inference(subsumption_resolution,[],[f426,f339])).
% 1.45/0.60  fof(f339,plain,(
% 1.45/0.60    v3_pre_topc(k1_xboole_0,sK0) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)),
% 1.45/0.60    inference(subsumption_resolution,[],[f332,f49])).
% 1.45/0.60  fof(f332,plain,(
% 1.45/0.60    v3_pre_topc(k1_xboole_0,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)),
% 1.45/0.60    inference(duplicate_literal_removal,[],[f331])).
% 1.45/0.60  fof(f331,plain,(
% 1.45/0.60    v3_pre_topc(k1_xboole_0,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)),
% 1.45/0.60    inference(superposition,[],[f226,f324])).
% 1.45/0.60  fof(f324,plain,(
% 1.45/0.60    k1_xboole_0 = sK5(sK0,sK1,u1_struct_0(sK0)) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)),
% 1.45/0.60    inference(duplicate_literal_removal,[],[f323])).
% 1.45/0.60  fof(f323,plain,(
% 1.45/0.60    u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) | k1_xboole_0 = sK5(sK0,sK1,u1_struct_0(sK0))),
% 1.45/0.60    inference(forward_demodulation,[],[f322,f109])).
% 1.45/0.60  fof(f322,plain,(
% 1.45/0.60    u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) | k1_xboole_0 = sK5(sK0,sK1,u1_struct_0(sK0)) | k2_struct_0(sK0) = k2_pre_topc(sK0,sK1)),
% 1.45/0.60    inference(subsumption_resolution,[],[f321,f51])).
% 1.45/0.60  fof(f321,plain,(
% 1.45/0.60    u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) | k1_xboole_0 = sK5(sK0,sK1,u1_struct_0(sK0)) | k2_struct_0(sK0) = k2_pre_topc(sK0,sK1) | ~l1_pre_topc(sK0)),
% 1.45/0.60    inference(subsumption_resolution,[],[f320,f49])).
% 1.45/0.60  fof(f320,plain,(
% 1.45/0.60    u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) | k1_xboole_0 = sK5(sK0,sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | k2_struct_0(sK0) = k2_pre_topc(sK0,sK1) | ~l1_pre_topc(sK0)),
% 1.45/0.60    inference(resolution,[],[f315,f63])).
% 1.45/0.60  fof(f63,plain,(
% 1.45/0.60    ( ! [X0,X1] : (~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = k2_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.45/0.60    inference(cnf_transformation,[],[f31])).
% 1.45/0.60  fof(f31,plain,(
% 1.45/0.60    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> k2_pre_topc(X0,X1) = k2_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.45/0.60    inference(ennf_transformation,[],[f20])).
% 1.45/0.60  fof(f20,axiom,(
% 1.45/0.60    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> k2_pre_topc(X0,X1) = k2_struct_0(X0))))),
% 1.45/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tops_1)).
% 1.45/0.60  fof(f315,plain,(
% 1.45/0.60    v1_tops_1(sK1,sK0) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) | k1_xboole_0 = sK5(sK0,sK1,u1_struct_0(sK0))),
% 1.45/0.60    inference(subsumption_resolution,[],[f314,f49])).
% 1.45/0.60  fof(f314,plain,(
% 1.45/0.60    k1_xboole_0 = sK5(sK0,sK1,u1_struct_0(sK0)) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) | v1_tops_1(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.45/0.60    inference(duplicate_literal_removal,[],[f312])).
% 1.45/0.60  fof(f312,plain,(
% 1.45/0.60    k1_xboole_0 = sK5(sK0,sK1,u1_struct_0(sK0)) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) | v1_tops_1(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)),
% 1.45/0.60    inference(resolution,[],[f296,f231])).
% 1.45/0.60  fof(f231,plain,(
% 1.45/0.60    ( ! [X0] : (r1_xboole_0(X0,sK5(sK0,X0,u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_pre_topc(sK0,X0)) )),
% 1.45/0.60    inference(subsumption_resolution,[],[f230,f107])).
% 1.45/0.60  fof(f107,plain,(
% 1.45/0.60    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 1.45/0.60    inference(forward_demodulation,[],[f57,f52])).
% 1.45/0.60  fof(f52,plain,(
% 1.45/0.60    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.45/0.60    inference(cnf_transformation,[],[f7])).
% 1.45/0.60  fof(f7,axiom,(
% 1.45/0.60    ! [X0] : k2_subset_1(X0) = X0),
% 1.45/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 1.45/0.60  fof(f57,plain,(
% 1.45/0.60    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 1.45/0.60    inference(cnf_transformation,[],[f9])).
% 1.45/0.60  fof(f9,axiom,(
% 1.45/0.60    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 1.45/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 1.45/0.60  fof(f230,plain,(
% 1.45/0.60    ( ! [X0] : (~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | r1_xboole_0(X0,sK5(sK0,X0,u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_pre_topc(sK0,X0)) )),
% 1.45/0.60    inference(duplicate_literal_removal,[],[f229])).
% 1.45/0.60  fof(f229,plain,(
% 1.45/0.60    ( ! [X0] : (~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | r1_xboole_0(X0,sK5(sK0,X0,u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_pre_topc(sK0,X0) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_pre_topc(sK0,X0)) )),
% 1.45/0.60    inference(resolution,[],[f228,f206])).
% 1.45/0.60  fof(f206,plain,(
% 1.45/0.60    ( ! [X0,X1] : (r2_hidden(sK4(sK0,X0,X1),u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = X1) )),
% 1.45/0.60    inference(resolution,[],[f82,f51])).
% 1.45/0.60  fof(f82,plain,(
% 1.45/0.60    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | r2_hidden(sK4(X0,X1,X2),u1_struct_0(X0)) | k2_pre_topc(X0,X1) = X2) )),
% 1.45/0.60    inference(cnf_transformation,[],[f36])).
% 1.45/0.60  fof(f36,plain,(
% 1.45/0.60    ! [X0] : (! [X1] : (! [X2] : ((k2_pre_topc(X0,X1) = X2 <=> ! [X3] : ((r2_hidden(X3,X2) <=> ! [X4] : (~r1_xboole_0(X1,X4) | ~r2_hidden(X3,X4) | ~v3_pre_topc(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.45/0.60    inference(flattening,[],[f35])).
% 1.45/0.60  fof(f35,plain,(
% 1.45/0.60    ! [X0] : (! [X1] : (! [X2] : ((k2_pre_topc(X0,X1) = X2 <=> ! [X3] : ((r2_hidden(X3,X2) <=> ! [X4] : ((~r1_xboole_0(X1,X4) | ~r2_hidden(X3,X4) | ~v3_pre_topc(X4,X0)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.45/0.60    inference(ennf_transformation,[],[f15])).
% 1.45/0.60  fof(f15,axiom,(
% 1.45/0.60    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (k2_pre_topc(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) <=> ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_xboole_0(X1,X4) & r2_hidden(X3,X4) & v3_pre_topc(X4,X0)))))))))),
% 1.45/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_pre_topc)).
% 1.45/0.60  fof(f228,plain,(
% 1.45/0.60    ( ! [X0,X1] : (~r2_hidden(sK4(sK0,X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | r1_xboole_0(X0,sK5(sK0,X0,X1)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = X1) )),
% 1.45/0.60    inference(resolution,[],[f80,f51])).
% 1.45/0.60  fof(f80,plain,(
% 1.45/0.60    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | r1_xboole_0(X1,sK5(X0,X1,X2)) | ~r2_hidden(sK4(X0,X1,X2),X2) | k2_pre_topc(X0,X1) = X2) )),
% 1.45/0.60    inference(cnf_transformation,[],[f36])).
% 1.45/0.60  fof(f296,plain,(
% 1.45/0.60    ~r1_xboole_0(sK1,sK5(sK0,sK1,u1_struct_0(sK0))) | k1_xboole_0 = sK5(sK0,sK1,u1_struct_0(sK0)) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) | v1_tops_1(sK1,sK0)),
% 1.45/0.60    inference(subsumption_resolution,[],[f295,f49])).
% 1.45/0.60  fof(f295,plain,(
% 1.45/0.60    u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) | k1_xboole_0 = sK5(sK0,sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_xboole_0(sK1,sK5(sK0,sK1,u1_struct_0(sK0))) | v1_tops_1(sK1,sK0)),
% 1.45/0.60    inference(duplicate_literal_removal,[],[f290])).
% 1.45/0.60  fof(f290,plain,(
% 1.45/0.60    u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) | k1_xboole_0 = sK5(sK0,sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_xboole_0(sK1,sK5(sK0,sK1,u1_struct_0(sK0))) | v1_tops_1(sK1,sK0)),
% 1.45/0.60    inference(resolution,[],[f278,f227])).
% 1.45/0.60  fof(f227,plain,(
% 1.45/0.60    ( ! [X0] : (~m1_subset_1(sK5(sK0,X0,u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_pre_topc(sK0,X0) | k1_xboole_0 = sK5(sK0,X0,u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_xboole_0(sK1,sK5(sK0,X0,u1_struct_0(sK0))) | v1_tops_1(sK1,sK0)) )),
% 1.45/0.60    inference(resolution,[],[f226,f48])).
% 1.45/0.60  fof(f48,plain,(
% 1.45/0.60    ( ! [X2] : (~v3_pre_topc(X2,sK0) | k1_xboole_0 = X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_xboole_0(sK1,X2) | v1_tops_1(sK1,sK0)) )),
% 1.45/0.60    inference(cnf_transformation,[],[f26])).
% 1.45/0.60  fof(f278,plain,(
% 1.45/0.60    m1_subset_1(sK5(sK0,sK1,u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)),
% 1.45/0.60    inference(resolution,[],[f277,f49])).
% 1.45/0.60  fof(f277,plain,(
% 1.45/0.60    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(sK5(sK0,X0,u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_pre_topc(sK0,X0)) )),
% 1.45/0.60    inference(subsumption_resolution,[],[f276,f107])).
% 1.45/0.60  fof(f276,plain,(
% 1.45/0.60    ( ! [X0] : (~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(sK5(sK0,X0,u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_pre_topc(sK0,X0)) )),
% 1.45/0.60    inference(duplicate_literal_removal,[],[f275])).
% 1.45/0.60  fof(f275,plain,(
% 1.45/0.60    ( ! [X0] : (~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(sK5(sK0,X0,u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_pre_topc(sK0,X0) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_pre_topc(sK0,X0)) )),
% 1.45/0.60    inference(resolution,[],[f274,f206])).
% 1.45/0.60  fof(f274,plain,(
% 1.45/0.60    ( ! [X0,X1] : (~r2_hidden(sK4(sK0,X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(sK5(sK0,X0,X1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = X1) )),
% 1.45/0.60    inference(resolution,[],[f77,f51])).
% 1.45/0.60  fof(f77,plain,(
% 1.45/0.60    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(sK4(X0,X1,X2),X2) | k2_pre_topc(X0,X1) = X2) )),
% 1.45/0.60    inference(cnf_transformation,[],[f36])).
% 1.45/0.60  fof(f226,plain,(
% 1.45/0.60    ( ! [X0] : (v3_pre_topc(sK5(sK0,X0,u1_struct_0(sK0)),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_pre_topc(sK0,X0)) )),
% 1.45/0.60    inference(subsumption_resolution,[],[f225,f107])).
% 1.45/0.60  fof(f225,plain,(
% 1.45/0.60    ( ! [X0] : (~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(sK5(sK0,X0,u1_struct_0(sK0)),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_pre_topc(sK0,X0)) )),
% 1.45/0.60    inference(duplicate_literal_removal,[],[f224])).
% 1.45/0.60  fof(f224,plain,(
% 1.45/0.60    ( ! [X0] : (~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(sK5(sK0,X0,u1_struct_0(sK0)),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_pre_topc(sK0,X0) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_pre_topc(sK0,X0)) )),
% 1.45/0.60    inference(resolution,[],[f223,f206])).
% 1.45/0.60  fof(f223,plain,(
% 1.45/0.60    ( ! [X0,X1] : (~r2_hidden(sK4(sK0,X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(sK5(sK0,X0,X1),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = X1) )),
% 1.45/0.60    inference(resolution,[],[f78,f51])).
% 1.45/0.60  fof(f78,plain,(
% 1.45/0.60    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(sK5(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2) | k2_pre_topc(X0,X1) = X2) )),
% 1.45/0.60    inference(cnf_transformation,[],[f36])).
% 1.45/0.60  fof(f426,plain,(
% 1.45/0.60    u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) | ~v3_pre_topc(k1_xboole_0,sK0) | ~r1_xboole_0(u1_struct_0(sK0),k1_xboole_0)),
% 1.45/0.60    inference(subsumption_resolution,[],[f425,f53])).
% 1.45/0.60  fof(f53,plain,(
% 1.45/0.60    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.45/0.60    inference(cnf_transformation,[],[f12])).
% 1.45/0.60  fof(f12,axiom,(
% 1.45/0.60    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.45/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 1.45/0.60  fof(f425,plain,(
% 1.45/0.60    u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) | ~v3_pre_topc(k1_xboole_0,sK0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_xboole_0(u1_struct_0(sK0),k1_xboole_0)),
% 1.45/0.60    inference(duplicate_literal_removal,[],[f422])).
% 1.45/0.60  fof(f422,plain,(
% 1.45/0.60    u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) | ~v3_pre_topc(k1_xboole_0,sK0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_xboole_0(u1_struct_0(sK0),k1_xboole_0) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)),
% 1.45/0.60    inference(resolution,[],[f420,f362])).
% 1.45/0.60  fof(f362,plain,(
% 1.45/0.60    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~v3_pre_topc(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_xboole_0(u1_struct_0(sK0),X1) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)) )),
% 1.45/0.60    inference(subsumption_resolution,[],[f361,f89])).
% 1.45/0.60  fof(f89,plain,(
% 1.45/0.60    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | r2_hidden(X2,X0)) )),
% 1.45/0.60    inference(cnf_transformation,[],[f41])).
% 1.45/0.60  fof(f41,plain,(
% 1.45/0.60    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.45/0.60    inference(ennf_transformation,[],[f11])).
% 1.45/0.60  fof(f11,axiom,(
% 1.45/0.60    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 1.45/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 1.45/0.60  fof(f361,plain,(
% 1.45/0.60    ( ! [X0,X1] : (~r2_hidden(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X1,sK0) | ~r2_hidden(X0,X1) | ~r1_xboole_0(u1_struct_0(sK0),X1) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)) )),
% 1.45/0.60    inference(subsumption_resolution,[],[f349,f107])).
% 1.45/0.60  fof(f349,plain,(
% 1.45/0.60    ( ! [X0,X1] : (~r2_hidden(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X1,sK0) | ~r2_hidden(X0,X1) | ~r1_xboole_0(u1_struct_0(sK0),X1) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)) )),
% 1.45/0.60    inference(superposition,[],[f268,f348])).
% 1.45/0.60  fof(f348,plain,(
% 1.45/0.60    u1_struct_0(sK0) = k2_pre_topc(sK0,u1_struct_0(sK0)) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)),
% 1.45/0.60    inference(subsumption_resolution,[],[f347,f51])).
% 1.45/0.60  fof(f347,plain,(
% 1.45/0.60    u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) | ~l1_pre_topc(sK0) | u1_struct_0(sK0) = k2_pre_topc(sK0,u1_struct_0(sK0))),
% 1.45/0.60    inference(subsumption_resolution,[],[f344,f107])).
% 1.45/0.60  fof(f344,plain,(
% 1.45/0.60    u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | u1_struct_0(sK0) = k2_pre_topc(sK0,u1_struct_0(sK0))),
% 1.45/0.60    inference(resolution,[],[f341,f61])).
% 1.45/0.60  fof(f61,plain,(
% 1.45/0.60    ( ! [X0,X1] : (~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | k2_pre_topc(X0,X1) = X1) )),
% 1.45/0.60    inference(cnf_transformation,[],[f30])).
% 1.45/0.60  fof(f30,plain,(
% 1.45/0.60    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.45/0.60    inference(flattening,[],[f29])).
% 1.45/0.60  fof(f29,plain,(
% 1.45/0.60    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.45/0.60    inference(ennf_transformation,[],[f18])).
% 1.45/0.60  fof(f18,axiom,(
% 1.45/0.60    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 1.45/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).
% 1.45/0.60  fof(f341,plain,(
% 1.45/0.60    v4_pre_topc(u1_struct_0(sK0),sK0) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)),
% 1.45/0.60    inference(resolution,[],[f339,f136])).
% 1.45/0.60  fof(f136,plain,(
% 1.45/0.60    ~v3_pre_topc(k1_xboole_0,sK0) | v4_pre_topc(u1_struct_0(sK0),sK0)),
% 1.45/0.60    inference(subsumption_resolution,[],[f133,f107])).
% 1.45/0.60  fof(f133,plain,(
% 1.45/0.60    ~v3_pre_topc(k1_xboole_0,sK0) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(u1_struct_0(sK0),sK0)),
% 1.45/0.60    inference(superposition,[],[f130,f126])).
% 1.45/0.60  fof(f126,plain,(
% 1.45/0.60    ( ! [X0] : (k1_xboole_0 = k3_subset_1(X0,X0)) )),
% 1.45/0.60    inference(backward_demodulation,[],[f116,f125])).
% 1.45/0.60  fof(f125,plain,(
% 1.45/0.60    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 1.45/0.60    inference(forward_demodulation,[],[f124,f106])).
% 1.45/0.60  fof(f106,plain,(
% 1.45/0.60    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.45/0.60    inference(forward_demodulation,[],[f96,f94])).
% 1.45/0.60  fof(f96,plain,(
% 1.45/0.60    ( ! [X0] : (k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = X0) )),
% 1.45/0.60    inference(definition_unfolding,[],[f56,f93])).
% 1.45/0.60  fof(f93,plain,(
% 1.45/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 1.45/0.60    inference(definition_unfolding,[],[f86,f84])).
% 1.45/0.60  fof(f86,plain,(
% 1.45/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.45/0.60    inference(cnf_transformation,[],[f2])).
% 1.45/0.60  fof(f2,axiom,(
% 1.45/0.60    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.45/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.45/0.60  fof(f56,plain,(
% 1.45/0.60    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.45/0.60    inference(cnf_transformation,[],[f4])).
% 1.45/0.60  fof(f4,axiom,(
% 1.45/0.60    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.45/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 1.45/0.60  fof(f124,plain,(
% 1.45/0.60    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = k3_subset_1(X0,k1_xboole_0)) )),
% 1.45/0.60    inference(forward_demodulation,[],[f122,f94])).
% 1.45/0.60  fof(f122,plain,(
% 1.45/0.60    ( ! [X0] : (k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = k3_subset_1(X0,k1_xboole_0)) )),
% 1.45/0.60    inference(resolution,[],[f98,f53])).
% 1.45/0.60  fof(f98,plain,(
% 1.45/0.60    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 1.45/0.60    inference(definition_unfolding,[],[f87,f93])).
% 1.45/0.60  fof(f87,plain,(
% 1.45/0.60    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 1.45/0.60    inference(cnf_transformation,[],[f39])).
% 1.45/0.60  fof(f39,plain,(
% 1.45/0.60    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.45/0.60    inference(ennf_transformation,[],[f8])).
% 1.45/0.60  fof(f8,axiom,(
% 1.45/0.60    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.45/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 1.45/0.60  fof(f116,plain,(
% 1.45/0.60    ( ! [X0] : (k1_xboole_0 = k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0))) )),
% 1.45/0.60    inference(resolution,[],[f88,f53])).
% 1.45/0.60  fof(f88,plain,(
% 1.45/0.60    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 1.45/0.60    inference(cnf_transformation,[],[f40])).
% 1.45/0.60  fof(f40,plain,(
% 1.45/0.60    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.45/0.60    inference(ennf_transformation,[],[f10])).
% 1.45/0.60  fof(f10,axiom,(
% 1.45/0.60    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 1.45/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 1.45/0.60  fof(f130,plain,(
% 1.45/0.60    ( ! [X0] : (~v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(X0,sK0)) )),
% 1.45/0.60    inference(resolution,[],[f64,f51])).
% 1.45/0.60  fof(f64,plain,(
% 1.45/0.60    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | v4_pre_topc(X1,X0)) )),
% 1.45/0.60    inference(cnf_transformation,[],[f32])).
% 1.45/0.60  fof(f32,plain,(
% 1.45/0.60    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.45/0.60    inference(ennf_transformation,[],[f22])).
% 1.45/0.60  fof(f22,axiom,(
% 1.45/0.60    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 1.45/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tops_1)).
% 1.45/0.60  fof(f268,plain,(
% 1.45/0.60    ( ! [X2,X0,X1] : (~r2_hidden(X1,k2_pre_topc(sK0,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X2,sK0) | ~r2_hidden(X1,X2) | ~r1_xboole_0(X0,X2) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 1.45/0.60    inference(subsumption_resolution,[],[f267,f92])).
% 1.45/0.60  fof(f92,plain,(
% 1.45/0.60    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2)) )),
% 1.45/0.60    inference(cnf_transformation,[],[f43])).
% 1.45/0.60  fof(f43,plain,(
% 1.45/0.60    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.45/0.60    inference(flattening,[],[f42])).
% 1.45/0.60  fof(f42,plain,(
% 1.45/0.60    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 1.45/0.60    inference(ennf_transformation,[],[f14])).
% 1.45/0.60  fof(f14,axiom,(
% 1.45/0.60    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 1.45/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 1.45/0.60  fof(f267,plain,(
% 1.45/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X2,sK0) | ~r2_hidden(X1,X2) | ~r1_xboole_0(X0,X2) | ~r2_hidden(X1,k2_pre_topc(sK0,X0))) )),
% 1.45/0.60    inference(resolution,[],[f70,f51])).
% 1.45/0.60  fof(f70,plain,(
% 1.45/0.60    ( ! [X2,X0,X3,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X3,X0) | ~r2_hidden(X2,X3) | ~r1_xboole_0(X1,X3) | ~r2_hidden(X2,k2_pre_topc(X0,X1))) )),
% 1.45/0.60    inference(cnf_transformation,[],[f34])).
% 1.45/0.60  fof(f34,plain,(
% 1.45/0.60    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k2_pre_topc(X0,X1)) <=> (! [X3] : (~r1_xboole_0(X1,X3) | ~r2_hidden(X2,X3) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & ~v2_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.45/0.60    inference(flattening,[],[f33])).
% 1.45/0.60  fof(f33,plain,(
% 1.45/0.60    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k2_pre_topc(X0,X1)) <=> (! [X3] : ((~r1_xboole_0(X1,X3) | ~r2_hidden(X2,X3) | ~v3_pre_topc(X3,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & ~v2_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.45/0.60    inference(ennf_transformation,[],[f19])).
% 1.45/0.60  fof(f19,axiom,(
% 1.45/0.60    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,k2_pre_topc(X0,X1)) <=> (! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_xboole_0(X1,X3) & r2_hidden(X2,X3) & v3_pre_topc(X3,X0))) & ~v2_struct_0(X0))))))),
% 1.45/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_pre_topc)).
% 1.45/0.60  fof(f420,plain,(
% 1.45/0.60    r2_hidden(sK4(sK0,sK1,u1_struct_0(sK0)),k1_xboole_0) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)),
% 1.45/0.60    inference(subsumption_resolution,[],[f417,f49])).
% 1.45/0.60  fof(f417,plain,(
% 1.45/0.60    r2_hidden(sK4(sK0,sK1,u1_struct_0(sK0)),k1_xboole_0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)),
% 1.45/0.60    inference(duplicate_literal_removal,[],[f416])).
% 1.45/0.60  fof(f416,plain,(
% 1.45/0.60    r2_hidden(sK4(sK0,sK1,u1_struct_0(sK0)),k1_xboole_0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)),
% 1.45/0.60    inference(superposition,[],[f412,f324])).
% 1.45/0.60  fof(f412,plain,(
% 1.45/0.60    ( ! [X0] : (r2_hidden(sK4(sK0,X0,u1_struct_0(sK0)),sK5(sK0,X0,u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_pre_topc(sK0,X0)) )),
% 1.45/0.60    inference(subsumption_resolution,[],[f411,f107])).
% 1.45/0.60  fof(f411,plain,(
% 1.45/0.60    ( ! [X0] : (~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK4(sK0,X0,u1_struct_0(sK0)),sK5(sK0,X0,u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_pre_topc(sK0,X0)) )),
% 1.45/0.60    inference(duplicate_literal_removal,[],[f410])).
% 1.45/0.60  fof(f410,plain,(
% 1.45/0.60    ( ! [X0] : (~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK4(sK0,X0,u1_struct_0(sK0)),sK5(sK0,X0,u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_pre_topc(sK0,X0) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_pre_topc(sK0,X0)) )),
% 1.45/0.60    inference(resolution,[],[f372,f206])).
% 1.45/0.60  fof(f372,plain,(
% 1.45/0.60    ( ! [X0,X1] : (~r2_hidden(sK4(sK0,X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK4(sK0,X0,X1),sK5(sK0,X0,X1)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = X1) )),
% 1.45/0.60    inference(resolution,[],[f79,f51])).
% 1.45/0.60  fof(f79,plain,(
% 1.45/0.60    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | r2_hidden(sK4(X0,X1,X2),sK5(X0,X1,X2)) | ~r2_hidden(sK4(X0,X1,X2),X2) | k2_pre_topc(X0,X1) = X2) )),
% 1.45/0.60    inference(cnf_transformation,[],[f36])).
% 1.45/0.60  fof(f62,plain,(
% 1.45/0.60    ( ! [X0,X1] : (k2_pre_topc(X0,X1) != k2_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v1_tops_1(X1,X0)) )),
% 1.45/0.60    inference(cnf_transformation,[],[f31])).
% 1.45/0.60  fof(f689,plain,(
% 1.45/0.60    ~r1_xboole_0(sK1,sK2)),
% 1.45/0.60    inference(subsumption_resolution,[],[f688,f450])).
% 1.45/0.60  fof(f450,plain,(
% 1.45/0.60    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.45/0.60    inference(resolution,[],[f449,f44])).
% 1.45/0.60  fof(f44,plain,(
% 1.45/0.60    ~v1_tops_1(sK1,sK0) | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.45/0.60    inference(cnf_transformation,[],[f26])).
% 1.45/0.60  fof(f688,plain,(
% 1.45/0.60    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_xboole_0(sK1,sK2)),
% 1.45/0.60    inference(subsumption_resolution,[],[f669,f452])).
% 1.45/0.60  fof(f452,plain,(
% 1.45/0.60    v3_pre_topc(sK2,sK0)),
% 1.45/0.60    inference(resolution,[],[f449,f46])).
% 1.45/0.60  fof(f46,plain,(
% 1.45/0.60    ~v1_tops_1(sK1,sK0) | v3_pre_topc(sK2,sK0)),
% 1.45/0.60    inference(cnf_transformation,[],[f26])).
% 1.45/0.60  fof(f669,plain,(
% 1.45/0.60    ~v3_pre_topc(sK2,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_xboole_0(sK1,sK2)),
% 1.45/0.60    inference(resolution,[],[f664,f445])).
% 1.45/0.60  fof(f445,plain,(
% 1.45/0.60    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~v3_pre_topc(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_xboole_0(sK1,X1)) )),
% 1.45/0.60    inference(subsumption_resolution,[],[f444,f89])).
% 1.45/0.60  fof(f444,plain,(
% 1.45/0.60    ( ! [X0,X1] : (~r2_hidden(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X1,sK0) | ~r2_hidden(X0,X1) | ~r1_xboole_0(sK1,X1)) )),
% 1.45/0.60    inference(subsumption_resolution,[],[f435,f49])).
% 1.45/0.60  fof(f435,plain,(
% 1.45/0.60    ( ! [X0,X1] : (~r2_hidden(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X1,sK0) | ~r2_hidden(X0,X1) | ~r1_xboole_0(sK1,X1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 1.45/0.60    inference(superposition,[],[f268,f431])).
% 1.45/0.60  fof(f664,plain,(
% 1.45/0.60    r2_hidden(sK4(sK0,k1_xboole_0,sK2),sK2)),
% 1.45/0.60    inference(subsumption_resolution,[],[f657,f453])).
% 1.45/0.60  fof(f453,plain,(
% 1.45/0.60    k1_xboole_0 != sK2),
% 1.45/0.60    inference(resolution,[],[f449,f45])).
% 1.45/0.60  fof(f45,plain,(
% 1.45/0.60    ~v1_tops_1(sK1,sK0) | k1_xboole_0 != sK2),
% 1.45/0.60    inference(cnf_transformation,[],[f26])).
% 1.45/0.60  fof(f657,plain,(
% 1.45/0.60    k1_xboole_0 = sK2 | r2_hidden(sK4(sK0,k1_xboole_0,sK2),sK2)),
% 1.45/0.60    inference(resolution,[],[f653,f450])).
% 1.45/0.60  fof(f653,plain,(
% 1.45/0.60    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = X1 | r2_hidden(sK4(sK0,k1_xboole_0,X1),X1)) )),
% 1.45/0.60    inference(forward_demodulation,[],[f652,f139])).
% 1.45/0.60  fof(f139,plain,(
% 1.45/0.60    k1_xboole_0 = k2_pre_topc(sK0,k1_xboole_0)),
% 1.45/0.60    inference(subsumption_resolution,[],[f138,f51])).
% 1.45/0.60  fof(f138,plain,(
% 1.45/0.60    ~l1_pre_topc(sK0) | k1_xboole_0 = k2_pre_topc(sK0,k1_xboole_0)),
% 1.45/0.60    inference(subsumption_resolution,[],[f137,f53])).
% 1.45/0.60  fof(f137,plain,(
% 1.45/0.60    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | k1_xboole_0 = k2_pre_topc(sK0,k1_xboole_0)),
% 1.45/0.60    inference(resolution,[],[f135,f61])).
% 1.45/0.60  fof(f135,plain,(
% 1.45/0.60    v4_pre_topc(k1_xboole_0,sK0)),
% 1.45/0.60    inference(subsumption_resolution,[],[f134,f53])).
% 1.45/0.60  fof(f134,plain,(
% 1.45/0.60    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(k1_xboole_0,sK0)),
% 1.45/0.60    inference(subsumption_resolution,[],[f132,f112])).
% 1.45/0.60  fof(f112,plain,(
% 1.45/0.60    v3_pre_topc(u1_struct_0(sK0),sK0)),
% 1.45/0.60    inference(forward_demodulation,[],[f111,f109])).
% 1.45/0.60  fof(f111,plain,(
% 1.45/0.60    v3_pre_topc(k2_struct_0(sK0),sK0)),
% 1.45/0.60    inference(subsumption_resolution,[],[f110,f51])).
% 1.45/0.60  fof(f110,plain,(
% 1.45/0.60    ~l1_pre_topc(sK0) | v3_pre_topc(k2_struct_0(sK0),sK0)),
% 1.45/0.60    inference(resolution,[],[f83,f50])).
% 1.45/0.60  fof(f50,plain,(
% 1.45/0.60    v2_pre_topc(sK0)),
% 1.45/0.60    inference(cnf_transformation,[],[f26])).
% 1.45/0.60  fof(f83,plain,(
% 1.45/0.60    ( ! [X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v3_pre_topc(k2_struct_0(X0),X0)) )),
% 1.45/0.60    inference(cnf_transformation,[],[f38])).
% 1.45/0.60  fof(f38,plain,(
% 1.45/0.60    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.45/0.60    inference(flattening,[],[f37])).
% 1.45/0.60  fof(f37,plain,(
% 1.45/0.60    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.45/0.60    inference(ennf_transformation,[],[f21])).
% 1.45/0.60  fof(f21,axiom,(
% 1.45/0.60    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k2_struct_0(X0),X0))),
% 1.45/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_tops_1)).
% 1.45/0.60  fof(f132,plain,(
% 1.45/0.60    ~v3_pre_topc(u1_struct_0(sK0),sK0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(k1_xboole_0,sK0)),
% 1.45/0.60    inference(superposition,[],[f130,f125])).
% 1.45/0.60  fof(f652,plain,(
% 1.45/0.60    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK4(sK0,k1_xboole_0,X1),X1) | k2_pre_topc(sK0,k1_xboole_0) = X1) )),
% 1.45/0.60    inference(subsumption_resolution,[],[f648,f53])).
% 1.45/0.60  fof(f648,plain,(
% 1.45/0.60    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK4(sK0,k1_xboole_0,X1),X1) | k2_pre_topc(sK0,k1_xboole_0) = X1 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 1.45/0.60    inference(trivial_inequality_removal,[],[f647])).
% 1.45/0.60  fof(f647,plain,(
% 1.45/0.60    ( ! [X1] : (k1_xboole_0 != k1_xboole_0 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK4(sK0,k1_xboole_0,X1),X1) | k2_pre_topc(sK0,k1_xboole_0) = X1 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 1.45/0.60    inference(superposition,[],[f624,f160])).
% 1.45/0.60  fof(f160,plain,(
% 1.45/0.60    ( ! [X3] : (k1_xboole_0 = k1_setfam_1(k2_tarski(k1_xboole_0,X3))) )),
% 1.45/0.60    inference(forward_demodulation,[],[f151,f95])).
% 1.45/0.60  fof(f95,plain,(
% 1.45/0.60    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_setfam_1(k2_tarski(k1_xboole_0,X0)))) )),
% 1.45/0.60    inference(definition_unfolding,[],[f55,f93])).
% 1.45/0.60  fof(f55,plain,(
% 1.45/0.60    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 1.45/0.60    inference(cnf_transformation,[],[f6])).
% 1.45/0.60  fof(f6,axiom,(
% 1.45/0.60    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 1.45/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).
% 1.45/0.60  fof(f151,plain,(
% 1.45/0.60    ( ! [X3] : (k5_xboole_0(k1_xboole_0,k1_setfam_1(k2_tarski(k1_xboole_0,k1_xboole_0))) = k1_setfam_1(k2_tarski(k1_xboole_0,X3))) )),
% 1.45/0.60    inference(superposition,[],[f97,f95])).
% 1.45/0.60  fof(f97,plain,(
% 1.45/0.60    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))))))) )),
% 1.45/0.60    inference(definition_unfolding,[],[f85,f84,f93,f93])).
% 1.45/0.60  fof(f85,plain,(
% 1.45/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.45/0.60    inference(cnf_transformation,[],[f5])).
% 1.45/0.60  fof(f5,axiom,(
% 1.45/0.60    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.45/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.45/0.60  fof(f624,plain,(
% 1.45/0.60    ( ! [X0,X1] : (k1_xboole_0 != k1_setfam_1(k2_tarski(X0,u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK4(sK0,X0,X1),X1) | k2_pre_topc(sK0,X0) = X1 | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 1.45/0.60    inference(resolution,[],[f586,f100])).
% 1.45/0.60  fof(f586,plain,(
% 1.45/0.60    ( ! [X0,X1] : (~r1_xboole_0(X1,u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK4(sK0,X1,X0),X0) | k2_pre_topc(sK0,X1) = X0) )),
% 1.45/0.60    inference(subsumption_resolution,[],[f585,f206])).
% 1.45/0.60  fof(f585,plain,(
% 1.45/0.60    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK4(sK0,X1,X0),u1_struct_0(sK0)) | ~r1_xboole_0(X1,u1_struct_0(sK0)) | r2_hidden(sK4(sK0,X1,X0),X0) | k2_pre_topc(sK0,X1) = X0) )),
% 1.45/0.60    inference(subsumption_resolution,[],[f580,f107])).
% 1.45/0.60  fof(f580,plain,(
% 1.45/0.60    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK4(sK0,X1,X0),u1_struct_0(sK0)) | ~r1_xboole_0(X1,u1_struct_0(sK0)) | r2_hidden(sK4(sK0,X1,X0),X0) | k2_pre_topc(sK0,X1) = X0) )),
% 1.45/0.60    inference(resolution,[],[f497,f112])).
% 1.45/0.60  fof(f497,plain,(
% 1.45/0.60    ( ! [X2,X0,X1] : (~v3_pre_topc(X2,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK4(sK0,X0,X1),X2) | ~r1_xboole_0(X0,X2) | r2_hidden(sK4(sK0,X0,X1),X1) | k2_pre_topc(sK0,X0) = X1) )),
% 1.45/0.60    inference(resolution,[],[f81,f51])).
% 1.45/0.60  fof(f81,plain,(
% 1.45/0.60    ( ! [X4,X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X4,X0) | ~r2_hidden(sK4(X0,X1,X2),X4) | ~r1_xboole_0(X1,X4) | r2_hidden(sK4(X0,X1,X2),X2) | k2_pre_topc(X0,X1) = X2) )),
% 1.45/0.60    inference(cnf_transformation,[],[f36])).
% 1.45/0.60  % SZS output end Proof for theBenchmark
% 1.45/0.60  % (17352)------------------------------
% 1.45/0.60  % (17352)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.60  % (17352)Termination reason: Refutation
% 1.45/0.60  
% 1.45/0.60  % (17352)Memory used [KB]: 6908
% 1.45/0.60  % (17352)Time elapsed: 0.151 s
% 1.45/0.60  % (17352)------------------------------
% 1.45/0.60  % (17352)------------------------------
% 1.45/0.61  % (17345)Success in time 0.241 s
%------------------------------------------------------------------------------
