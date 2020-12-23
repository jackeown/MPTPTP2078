%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:13:03 EST 2020

% Result     : Theorem 1.17s
% Output     : Refutation 1.17s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 194 expanded)
%              Number of leaves         :    8 (  36 expanded)
%              Depth                    :   23
%              Number of atoms          :  210 ( 810 expanded)
%              Number of equality atoms :   38 (  52 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f130,plain,(
    $false ),
    inference(subsumption_resolution,[],[f129,f102])).

fof(f102,plain,(
    ~ v6_tops_1(sK1,sK0) ),
    inference(global_subsumption,[],[f22,f84])).

fof(f84,plain,(
    v5_tops_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f83,f26])).

fof(f26,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v5_tops_1(X1,X0)
          <~> v6_tops_1(X1,X0) )
          & v4_pre_topc(X1,X0)
          & v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v5_tops_1(X1,X0)
          <~> v6_tops_1(X1,X0) )
          & v4_pre_topc(X1,X0)
          & v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( ( v4_pre_topc(X1,X0)
                & v3_pre_topc(X1,X0) )
             => ( v5_tops_1(X1,X0)
              <=> v6_tops_1(X1,X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v4_pre_topc(X1,X0)
              & v3_pre_topc(X1,X0) )
           => ( v5_tops_1(X1,X0)
            <=> v6_tops_1(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_tops_1)).

fof(f83,plain,
    ( ~ l1_pre_topc(sK0)
    | v5_tops_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f82,f23])).

fof(f23,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f11])).

fof(f82,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | v5_tops_1(sK1,sK0) ),
    inference(trivial_inequality_removal,[],[f80])).

fof(f80,plain,
    ( sK1 != sK1
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | v5_tops_1(sK1,sK0) ),
    inference(superposition,[],[f32,f79])).

fof(f79,plain,(
    sK1 = k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f78,f45])).

fof(f45,plain,(
    sK1 = k2_pre_topc(sK0,sK1) ),
    inference(subsumption_resolution,[],[f44,f25])).

fof(f25,plain,(
    v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f44,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | sK1 = k2_pre_topc(sK0,sK1) ),
    inference(subsumption_resolution,[],[f42,f26])).

fof(f42,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v4_pre_topc(sK1,sK0)
    | sK1 = k2_pre_topc(sK0,sK1) ),
    inference(resolution,[],[f28,f23])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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

fof(f78,plain,(
    k2_pre_topc(sK0,sK1) = k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f77,f24])).

fof(f24,plain,(
    v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f77,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | k2_pre_topc(sK0,sK1) = k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f75,f26])).

fof(f75,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v3_pre_topc(sK1,sK0)
    | k2_pre_topc(sK0,sK1) = k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) ),
    inference(resolution,[],[f29,f23])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v3_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) = k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,X1))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,X1)))
          | ~ v3_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,X1)))
          | ~ v3_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
           => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_tops_1)).

fof(f32,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,k1_tops_1(X0,X1)) != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v5_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_tops_1(X1,X0)
          <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v5_tops_1(X1,X0)
          <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tops_1)).

fof(f22,plain,
    ( ~ v6_tops_1(sK1,sK0)
    | ~ v5_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f129,plain,(
    v6_tops_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f128,f26])).

fof(f128,plain,
    ( ~ l1_pre_topc(sK0)
    | v6_tops_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f127,f23])).

fof(f127,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | v6_tops_1(sK1,sK0) ),
    inference(resolution,[],[f125,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v6_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v6_tops_1(X1,X0)
          <=> v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v6_tops_1(X1,X0)
          <=> v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t101_tops_1)).

fof(f125,plain,(
    v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    inference(subsumption_resolution,[],[f124,f23])).

fof(f124,plain,
    ( v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f121,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f121,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    inference(subsumption_resolution,[],[f120,f26])).

fof(f120,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    inference(trivial_inequality_removal,[],[f118])).

fof(f118,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK1) != k3_subset_1(u1_struct_0(sK0),sK1)
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    inference(superposition,[],[f32,f117])).

fof(f117,plain,(
    k3_subset_1(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) ),
    inference(forward_demodulation,[],[f116,f93])).

fof(f93,plain,(
    k3_subset_1(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) ),
    inference(subsumption_resolution,[],[f92,f23])).

fof(f92,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f90,f26])).

fof(f90,plain,
    ( ~ l1_pre_topc(sK0)
    | k3_subset_1(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f43,f58])).

fof(f58,plain,(
    v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    inference(subsumption_resolution,[],[f57,f23])).

fof(f57,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f56,f36])).

fof(f56,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    inference(subsumption_resolution,[],[f55,f26])).

fof(f55,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    inference(subsumption_resolution,[],[f54,f24])).

fof(f54,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    inference(superposition,[],[f34,f39])).

fof(f39,plain,(
    sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) ),
    inference(resolution,[],[f37,f23])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v4_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tops_1)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ l1_pre_topc(X0)
      | k3_subset_1(u1_struct_0(X0),X1) = k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(resolution,[],[f28,f36])).

fof(f116,plain,(
    k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))) ),
    inference(subsumption_resolution,[],[f115,f25])).

fof(f115,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f113,f26])).

fof(f113,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))))
    | ~ l1_pre_topc(sK0)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(resolution,[],[f109,f23])).

fof(f109,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)) = k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))))
      | ~ l1_pre_topc(X0)
      | ~ v4_pre_topc(X1,X0) ) ),
    inference(duplicate_literal_removal,[],[f107])).

fof(f107,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)) = k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v4_pre_topc(X1,X0) ) ),
    inference(resolution,[],[f76,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v4_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ l1_pre_topc(X0)
      | k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)) = k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(resolution,[],[f29,f36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n013.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 13:43:09 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.49  % (18982)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.22/0.50  % (18988)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.22/0.50  % (18977)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.22/0.51  % (18981)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.22/0.51  % (18996)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.22/0.51  % (18983)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 1.17/0.51  % (18993)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 1.17/0.51  % (19000)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 1.17/0.51  % (18979)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 1.17/0.51  % (18993)Refutation not found, incomplete strategy% (18993)------------------------------
% 1.17/0.51  % (18993)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.17/0.51  % (18993)Termination reason: Refutation not found, incomplete strategy
% 1.17/0.51  
% 1.17/0.51  % (18993)Memory used [KB]: 1663
% 1.17/0.51  % (18993)Time elapsed: 0.094 s
% 1.17/0.51  % (18993)------------------------------
% 1.17/0.51  % (18993)------------------------------
% 1.17/0.51  % (18998)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 1.17/0.51  % (18980)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 1.17/0.51  % (18990)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 1.17/0.51  % (18980)Refutation not found, incomplete strategy% (18980)------------------------------
% 1.17/0.51  % (18980)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.17/0.51  % (18980)Termination reason: Refutation not found, incomplete strategy
% 1.17/0.51  
% 1.17/0.51  % (18980)Memory used [KB]: 10618
% 1.17/0.51  % (18980)Time elapsed: 0.094 s
% 1.17/0.51  % (18980)------------------------------
% 1.17/0.51  % (18980)------------------------------
% 1.17/0.51  % (18978)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 1.17/0.52  % (19000)Refutation not found, incomplete strategy% (19000)------------------------------
% 1.17/0.52  % (19000)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.17/0.52  % (19000)Termination reason: Refutation not found, incomplete strategy
% 1.17/0.52  
% 1.17/0.52  % (19000)Memory used [KB]: 10618
% 1.17/0.52  % (19000)Time elapsed: 0.054 s
% 1.17/0.52  % (19000)------------------------------
% 1.17/0.52  % (19000)------------------------------
% 1.17/0.52  % (18990)Refutation found. Thanks to Tanya!
% 1.17/0.52  % SZS status Theorem for theBenchmark
% 1.17/0.52  % SZS output start Proof for theBenchmark
% 1.17/0.52  fof(f130,plain,(
% 1.17/0.52    $false),
% 1.17/0.52    inference(subsumption_resolution,[],[f129,f102])).
% 1.17/0.52  fof(f102,plain,(
% 1.17/0.52    ~v6_tops_1(sK1,sK0)),
% 1.17/0.52    inference(global_subsumption,[],[f22,f84])).
% 1.17/0.52  fof(f84,plain,(
% 1.17/0.52    v5_tops_1(sK1,sK0)),
% 1.17/0.52    inference(subsumption_resolution,[],[f83,f26])).
% 1.17/0.52  fof(f26,plain,(
% 1.17/0.52    l1_pre_topc(sK0)),
% 1.17/0.52    inference(cnf_transformation,[],[f11])).
% 1.17/0.52  fof(f11,plain,(
% 1.17/0.52    ? [X0] : (? [X1] : ((v5_tops_1(X1,X0) <~> v6_tops_1(X1,X0)) & v4_pre_topc(X1,X0) & v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.17/0.52    inference(flattening,[],[f10])).
% 1.17/0.52  fof(f10,plain,(
% 1.17/0.52    ? [X0] : (? [X1] : (((v5_tops_1(X1,X0) <~> v6_tops_1(X1,X0)) & (v4_pre_topc(X1,X0) & v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.17/0.52    inference(ennf_transformation,[],[f9])).
% 1.17/0.52  fof(f9,negated_conjecture,(
% 1.17/0.52    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v4_pre_topc(X1,X0) & v3_pre_topc(X1,X0)) => (v5_tops_1(X1,X0) <=> v6_tops_1(X1,X0)))))),
% 1.17/0.52    inference(negated_conjecture,[],[f8])).
% 1.17/0.52  fof(f8,conjecture,(
% 1.17/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v4_pre_topc(X1,X0) & v3_pre_topc(X1,X0)) => (v5_tops_1(X1,X0) <=> v6_tops_1(X1,X0)))))),
% 1.17/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_tops_1)).
% 1.17/0.52  fof(f83,plain,(
% 1.17/0.52    ~l1_pre_topc(sK0) | v5_tops_1(sK1,sK0)),
% 1.17/0.52    inference(subsumption_resolution,[],[f82,f23])).
% 1.17/0.52  fof(f23,plain,(
% 1.17/0.52    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.17/0.52    inference(cnf_transformation,[],[f11])).
% 1.17/0.52  fof(f82,plain,(
% 1.17/0.52    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | v5_tops_1(sK1,sK0)),
% 1.17/0.52    inference(trivial_inequality_removal,[],[f80])).
% 1.17/0.52  fof(f80,plain,(
% 1.17/0.52    sK1 != sK1 | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | v5_tops_1(sK1,sK0)),
% 1.17/0.52    inference(superposition,[],[f32,f79])).
% 1.17/0.52  fof(f79,plain,(
% 1.17/0.52    sK1 = k2_pre_topc(sK0,k1_tops_1(sK0,sK1))),
% 1.17/0.52    inference(forward_demodulation,[],[f78,f45])).
% 1.17/0.52  fof(f45,plain,(
% 1.17/0.52    sK1 = k2_pre_topc(sK0,sK1)),
% 1.17/0.52    inference(subsumption_resolution,[],[f44,f25])).
% 1.17/0.52  fof(f25,plain,(
% 1.17/0.52    v4_pre_topc(sK1,sK0)),
% 1.17/0.52    inference(cnf_transformation,[],[f11])).
% 1.17/0.52  fof(f44,plain,(
% 1.17/0.52    ~v4_pre_topc(sK1,sK0) | sK1 = k2_pre_topc(sK0,sK1)),
% 1.17/0.52    inference(subsumption_resolution,[],[f42,f26])).
% 1.17/0.52  fof(f42,plain,(
% 1.17/0.52    ~l1_pre_topc(sK0) | ~v4_pre_topc(sK1,sK0) | sK1 = k2_pre_topc(sK0,sK1)),
% 1.17/0.52    inference(resolution,[],[f28,f23])).
% 1.17/0.52  fof(f28,plain,(
% 1.17/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) = X1) )),
% 1.17/0.52    inference(cnf_transformation,[],[f13])).
% 1.17/0.52  fof(f13,plain,(
% 1.17/0.52    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.17/0.52    inference(flattening,[],[f12])).
% 1.17/0.52  fof(f12,plain,(
% 1.17/0.52    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.17/0.52    inference(ennf_transformation,[],[f3])).
% 1.17/0.52  fof(f3,axiom,(
% 1.17/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 1.17/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).
% 1.17/0.52  fof(f78,plain,(
% 1.17/0.52    k2_pre_topc(sK0,sK1) = k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))),
% 1.17/0.52    inference(subsumption_resolution,[],[f77,f24])).
% 1.17/0.52  fof(f24,plain,(
% 1.17/0.52    v3_pre_topc(sK1,sK0)),
% 1.17/0.52    inference(cnf_transformation,[],[f11])).
% 1.17/0.52  fof(f77,plain,(
% 1.17/0.52    ~v3_pre_topc(sK1,sK0) | k2_pre_topc(sK0,sK1) = k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))),
% 1.17/0.52    inference(subsumption_resolution,[],[f75,f26])).
% 1.17/0.52  fof(f75,plain,(
% 1.17/0.52    ~l1_pre_topc(sK0) | ~v3_pre_topc(sK1,sK0) | k2_pre_topc(sK0,sK1) = k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))),
% 1.17/0.52    inference(resolution,[],[f29,f23])).
% 1.17/0.52  fof(f29,plain,(
% 1.17/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v3_pre_topc(X1,X0) | k2_pre_topc(X0,X1) = k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,X1)))) )),
% 1.17/0.52    inference(cnf_transformation,[],[f15])).
% 1.17/0.52  fof(f15,plain,(
% 1.17/0.52    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,X1))) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.17/0.52    inference(flattening,[],[f14])).
% 1.17/0.52  fof(f14,plain,(
% 1.17/0.52    ! [X0] : (! [X1] : ((k2_pre_topc(X0,X1) = k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,X1))) | ~v3_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.17/0.52    inference(ennf_transformation,[],[f7])).
% 1.17/0.52  fof(f7,axiom,(
% 1.17/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,X1))))))),
% 1.17/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_tops_1)).
% 1.17/0.52  fof(f32,plain,(
% 1.17/0.52    ( ! [X0,X1] : (k2_pre_topc(X0,k1_tops_1(X0,X1)) != X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v5_tops_1(X1,X0)) )),
% 1.17/0.52    inference(cnf_transformation,[],[f17])).
% 1.17/0.52  fof(f17,plain,(
% 1.17/0.52    ! [X0] : (! [X1] : ((v5_tops_1(X1,X0) <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.17/0.52    inference(ennf_transformation,[],[f4])).
% 1.17/0.52  fof(f4,axiom,(
% 1.17/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v5_tops_1(X1,X0) <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1)))),
% 1.17/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tops_1)).
% 1.17/0.52  fof(f22,plain,(
% 1.17/0.52    ~v6_tops_1(sK1,sK0) | ~v5_tops_1(sK1,sK0)),
% 1.17/0.52    inference(cnf_transformation,[],[f11])).
% 1.17/0.52  fof(f129,plain,(
% 1.17/0.52    v6_tops_1(sK1,sK0)),
% 1.17/0.52    inference(subsumption_resolution,[],[f128,f26])).
% 1.17/0.52  fof(f128,plain,(
% 1.17/0.52    ~l1_pre_topc(sK0) | v6_tops_1(sK1,sK0)),
% 1.17/0.52    inference(subsumption_resolution,[],[f127,f23])).
% 1.17/0.52  fof(f127,plain,(
% 1.17/0.52    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | v6_tops_1(sK1,sK0)),
% 1.17/0.52    inference(resolution,[],[f125,f30])).
% 1.17/0.52  fof(f30,plain,(
% 1.17/0.52    ( ! [X0,X1] : (~v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v6_tops_1(X1,X0)) )),
% 1.17/0.52    inference(cnf_transformation,[],[f16])).
% 1.17/0.52  fof(f16,plain,(
% 1.17/0.52    ! [X0] : (! [X1] : ((v6_tops_1(X1,X0) <=> v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.17/0.52    inference(ennf_transformation,[],[f5])).
% 1.17/0.52  fof(f5,axiom,(
% 1.17/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v6_tops_1(X1,X0) <=> v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 1.17/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t101_tops_1)).
% 1.17/0.52  fof(f125,plain,(
% 1.17/0.52    v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)),
% 1.17/0.52    inference(subsumption_resolution,[],[f124,f23])).
% 1.17/0.52  fof(f124,plain,(
% 1.17/0.52    v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.17/0.52    inference(resolution,[],[f121,f36])).
% 1.17/0.52  fof(f36,plain,(
% 1.17/0.52    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.17/0.52    inference(cnf_transformation,[],[f19])).
% 1.17/0.52  fof(f19,plain,(
% 1.17/0.52    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.17/0.52    inference(ennf_transformation,[],[f1])).
% 1.17/0.52  fof(f1,axiom,(
% 1.17/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.17/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 1.17/0.52  fof(f121,plain,(
% 1.17/0.52    ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)),
% 1.17/0.52    inference(subsumption_resolution,[],[f120,f26])).
% 1.17/0.52  fof(f120,plain,(
% 1.17/0.52    ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)),
% 1.17/0.52    inference(trivial_inequality_removal,[],[f118])).
% 1.17/0.52  fof(f118,plain,(
% 1.17/0.52    k3_subset_1(u1_struct_0(sK0),sK1) != k3_subset_1(u1_struct_0(sK0),sK1) | ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)),
% 1.17/0.52    inference(superposition,[],[f32,f117])).
% 1.17/0.52  fof(f117,plain,(
% 1.17/0.52    k3_subset_1(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))),
% 1.17/0.52    inference(forward_demodulation,[],[f116,f93])).
% 1.17/0.52  fof(f93,plain,(
% 1.17/0.52    k3_subset_1(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),
% 1.17/0.52    inference(subsumption_resolution,[],[f92,f23])).
% 1.17/0.52  fof(f92,plain,(
% 1.17/0.52    k3_subset_1(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.17/0.52    inference(subsumption_resolution,[],[f90,f26])).
% 1.17/0.52  fof(f90,plain,(
% 1.17/0.52    ~l1_pre_topc(sK0) | k3_subset_1(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.17/0.52    inference(resolution,[],[f43,f58])).
% 1.17/0.52  fof(f58,plain,(
% 1.17/0.52    v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)),
% 1.17/0.52    inference(subsumption_resolution,[],[f57,f23])).
% 1.17/0.52  fof(f57,plain,(
% 1.17/0.52    v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.17/0.52    inference(resolution,[],[f56,f36])).
% 1.17/0.52  fof(f56,plain,(
% 1.17/0.52    ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)),
% 1.17/0.52    inference(subsumption_resolution,[],[f55,f26])).
% 1.17/0.52  fof(f55,plain,(
% 1.17/0.52    ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)),
% 1.17/0.52    inference(subsumption_resolution,[],[f54,f24])).
% 1.17/0.52  fof(f54,plain,(
% 1.17/0.52    ~v3_pre_topc(sK1,sK0) | ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)),
% 1.17/0.52    inference(superposition,[],[f34,f39])).
% 1.17/0.52  fof(f39,plain,(
% 1.17/0.52    sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))),
% 1.17/0.52    inference(resolution,[],[f37,f23])).
% 1.17/0.52  fof(f37,plain,(
% 1.17/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 1.17/0.52    inference(cnf_transformation,[],[f20])).
% 1.17/0.52  fof(f20,plain,(
% 1.17/0.52    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.17/0.52    inference(ennf_transformation,[],[f2])).
% 1.17/0.52  fof(f2,axiom,(
% 1.17/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 1.17/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 1.17/0.52  fof(f34,plain,(
% 1.17/0.52    ( ! [X0,X1] : (~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v4_pre_topc(X1,X0)) )),
% 1.17/0.52    inference(cnf_transformation,[],[f18])).
% 1.17/0.52  fof(f18,plain,(
% 1.17/0.52    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.17/0.52    inference(ennf_transformation,[],[f6])).
% 1.17/0.52  fof(f6,axiom,(
% 1.17/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 1.17/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tops_1)).
% 1.17/0.52  fof(f43,plain,(
% 1.17/0.52    ( ! [X0,X1] : (~v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~l1_pre_topc(X0) | k3_subset_1(u1_struct_0(X0),X1) = k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) )),
% 1.17/0.52    inference(resolution,[],[f28,f36])).
% 1.17/0.52  fof(f116,plain,(
% 1.17/0.52    k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))))),
% 1.17/0.52    inference(subsumption_resolution,[],[f115,f25])).
% 1.17/0.52  fof(f115,plain,(
% 1.17/0.52    k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))) | ~v4_pre_topc(sK1,sK0)),
% 1.17/0.52    inference(subsumption_resolution,[],[f113,f26])).
% 1.17/0.52  fof(f113,plain,(
% 1.17/0.52    k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))) | ~l1_pre_topc(sK0) | ~v4_pre_topc(sK1,sK0)),
% 1.17/0.52    inference(resolution,[],[f109,f23])).
% 1.17/0.52  fof(f109,plain,(
% 1.17/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)) = k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))) | ~l1_pre_topc(X0) | ~v4_pre_topc(X1,X0)) )),
% 1.17/0.52    inference(duplicate_literal_removal,[],[f107])).
% 1.17/0.52  fof(f107,plain,(
% 1.17/0.52    ( ! [X0,X1] : (~l1_pre_topc(X0) | k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)) = k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v4_pre_topc(X1,X0)) )),
% 1.17/0.52    inference(resolution,[],[f76,f35])).
% 1.17/0.52  fof(f35,plain,(
% 1.17/0.52    ( ! [X0,X1] : (v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v4_pre_topc(X1,X0)) )),
% 1.17/0.52    inference(cnf_transformation,[],[f18])).
% 1.17/0.52  fof(f76,plain,(
% 1.17/0.52    ( ! [X0,X1] : (~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~l1_pre_topc(X0) | k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)) = k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) )),
% 1.17/0.52    inference(resolution,[],[f29,f36])).
% 1.17/0.52  % SZS output end Proof for theBenchmark
% 1.17/0.52  % (18990)------------------------------
% 1.17/0.52  % (18990)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.17/0.52  % (18990)Termination reason: Refutation
% 1.17/0.52  
% 1.17/0.52  % (18990)Memory used [KB]: 6140
% 1.17/0.52  % (18990)Time elapsed: 0.101 s
% 1.17/0.52  % (18990)------------------------------
% 1.17/0.52  % (18990)------------------------------
% 1.17/0.52  % (18976)Success in time 0.152 s
%------------------------------------------------------------------------------
