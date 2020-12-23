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
% DateTime   : Thu Dec  3 13:13:07 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 186 expanded)
%              Number of leaves         :    8 (  36 expanded)
%              Depth                    :   18
%              Number of atoms          :  169 ( 810 expanded)
%              Number of equality atoms :   16 (  26 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f236,plain,(
    $false ),
    inference(subsumption_resolution,[],[f235,f202])).

fof(f202,plain,(
    ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f201,f23])).

fof(f23,plain,(
    ~ v6_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v6_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & v6_tops_1(X2,X0)
              & v6_tops_1(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v6_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & v6_tops_1(X2,X0)
              & v6_tops_1(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v6_tops_1(X2,X0)
                    & v6_tops_1(X1,X0) )
                 => v6_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v6_tops_1(X2,X0)
                  & v6_tops_1(X1,X0) )
               => v6_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t109_tops_1)).

fof(f201,plain,
    ( ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | v6_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(subsumption_resolution,[],[f197,f26])).

fof(f26,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f197,plain,
    ( ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | v6_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(resolution,[],[f185,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v6_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v6_tops_1(X1,X0)
          <=> v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v6_tops_1(X1,X0)
          <=> v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t101_tops_1)).

fof(f185,plain,(
    v5_tops_1(k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK1,sK2)),sK0) ),
    inference(backward_demodulation,[],[f124,f184])).

fof(f184,plain,(
    k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),sK2)) = k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK1,sK2)) ),
    inference(forward_demodulation,[],[f174,f75])).

fof(f75,plain,(
    k9_subset_1(u1_struct_0(sK0),sK1,sK2) = k7_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK2)) ),
    inference(forward_demodulation,[],[f74,f42])).

fof(f42,plain,(
    sK2 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2)) ),
    inference(resolution,[],[f20,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f20,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f11])).

fof(f74,plain,(
    k7_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK2)) = k9_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2))) ),
    inference(resolution,[],[f50,f44])).

fof(f44,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f20,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f50,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | k7_subset_1(u1_struct_0(sK0),sK1,X2) = k9_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),X2)) ) ),
    inference(resolution,[],[f24,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_subset_1)).

fof(f24,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f11])).

fof(f174,plain,(
    k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),sK2)) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK2))) ),
    inference(resolution,[],[f48,f44])).

fof(f48,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK1,X1)) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),X1) ) ),
    inference(resolution,[],[f24,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_subset_1)).

fof(f124,plain,(
    v5_tops_1(k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),sK2)),sK0) ),
    inference(subsumption_resolution,[],[f122,f44])).

fof(f122,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | v5_tops_1(k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),sK2)),sK0) ),
    inference(resolution,[],[f55,f40])).

fof(f40,plain,(
    v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK2),sK0) ),
    inference(subsumption_resolution,[],[f39,f26])).

fof(f39,plain,
    ( v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK2),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f38,f20])).

fof(f38,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK2),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f22,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ v6_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f22,plain,(
    v6_tops_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f55,plain,(
    ! [X0] :
      ( ~ v5_tops_1(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v5_tops_1(k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),X0),sK0) ) ),
    inference(subsumption_resolution,[],[f54,f25])).

fof(f25,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f54,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_pre_topc(sK0)
      | ~ v5_tops_1(X0,sK0)
      | v5_tops_1(k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),X0),sK0) ) ),
    inference(subsumption_resolution,[],[f53,f49])).

fof(f49,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f24,f30])).

fof(f53,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_pre_topc(sK0)
      | ~ v5_tops_1(X0,sK0)
      | v5_tops_1(k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),X0),sK0) ) ),
    inference(subsumption_resolution,[],[f52,f26])).

fof(f52,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_pre_topc(sK0)
      | ~ v5_tops_1(X0,sK0)
      | v5_tops_1(k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),X0),sK0) ) ),
    inference(resolution,[],[f37,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_tops_1(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ v5_tops_1(X2,X0)
      | v5_tops_1(k4_subset_1(u1_struct_0(X0),X1,X2),X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v5_tops_1(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
              | ~ v5_tops_1(X2,X0)
              | ~ v5_tops_1(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v5_tops_1(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
              | ~ v5_tops_1(X2,X0)
              | ~ v5_tops_1(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v5_tops_1(X2,X0)
                  & v5_tops_1(X1,X0) )
               => v5_tops_1(k4_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_tops_1)).

fof(f37,plain,(
    v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    inference(subsumption_resolution,[],[f36,f26])).

fof(f36,plain,
    ( v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f35,f24])).

fof(f35,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f21,f29])).

fof(f21,plain,(
    v6_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f235,plain,(
    m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f46,f75])).

fof(f46,plain,(
    ! [X0] : m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f24,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_subset_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n024.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 20:23:51 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.23/0.49  % (17871)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.23/0.49  % (17863)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.23/0.51  % (17873)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.23/0.51  % (17871)Refutation not found, incomplete strategy% (17871)------------------------------
% 0.23/0.51  % (17871)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.51  % (17871)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.51  
% 0.23/0.51  % (17871)Memory used [KB]: 10618
% 0.23/0.51  % (17871)Time elapsed: 0.076 s
% 0.23/0.51  % (17871)------------------------------
% 0.23/0.51  % (17871)------------------------------
% 0.23/0.51  % (17868)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.23/0.51  % (17885)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.23/0.51  % (17881)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.23/0.51  % (17869)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.23/0.52  % (17882)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.23/0.52  % (17865)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.23/0.52  % (17880)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.23/0.52  % (17884)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.23/0.52  % (17867)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.23/0.52  % (17870)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.23/0.52  % (17866)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.23/0.52  % (17872)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.23/0.52  % (17873)Refutation not found, incomplete strategy% (17873)------------------------------
% 0.23/0.52  % (17873)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.52  % (17873)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.52  
% 0.23/0.52  % (17873)Memory used [KB]: 10618
% 0.23/0.52  % (17873)Time elapsed: 0.100 s
% 0.23/0.52  % (17873)------------------------------
% 0.23/0.52  % (17873)------------------------------
% 0.23/0.53  % (17878)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.23/0.53  % (17864)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.23/0.53  % (17876)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.23/0.53  % (17874)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.23/0.53  % (17883)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.23/0.53  % (17883)Refutation found. Thanks to Tanya!
% 0.23/0.53  % SZS status Theorem for theBenchmark
% 0.23/0.53  % SZS output start Proof for theBenchmark
% 0.23/0.53  fof(f236,plain,(
% 0.23/0.53    $false),
% 0.23/0.53    inference(subsumption_resolution,[],[f235,f202])).
% 0.23/0.53  fof(f202,plain,(
% 0.23/0.53    ~m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.23/0.53    inference(subsumption_resolution,[],[f201,f23])).
% 0.23/0.53  fof(f23,plain,(
% 0.23/0.53    ~v6_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)),
% 0.23/0.53    inference(cnf_transformation,[],[f11])).
% 0.23/0.53  fof(f11,plain,(
% 0.23/0.53    ? [X0] : (? [X1] : (? [X2] : (~v6_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & v6_tops_1(X2,X0) & v6_tops_1(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.23/0.53    inference(flattening,[],[f10])).
% 0.23/0.53  fof(f10,plain,(
% 0.23/0.53    ? [X0] : (? [X1] : (? [X2] : ((~v6_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v6_tops_1(X2,X0) & v6_tops_1(X1,X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.23/0.53    inference(ennf_transformation,[],[f9])).
% 0.23/0.53  fof(f9,negated_conjecture,(
% 0.23/0.53    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v6_tops_1(X2,X0) & v6_tops_1(X1,X0)) => v6_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 0.23/0.53    inference(negated_conjecture,[],[f8])).
% 0.23/0.53  fof(f8,conjecture,(
% 0.23/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v6_tops_1(X2,X0) & v6_tops_1(X1,X0)) => v6_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 0.23/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t109_tops_1)).
% 0.23/0.53  fof(f201,plain,(
% 0.23/0.53    ~m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | v6_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)),
% 0.23/0.53    inference(subsumption_resolution,[],[f197,f26])).
% 0.23/0.53  fof(f26,plain,(
% 0.23/0.53    l1_pre_topc(sK0)),
% 0.23/0.53    inference(cnf_transformation,[],[f11])).
% 0.23/0.53  fof(f197,plain,(
% 0.23/0.53    ~m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | v6_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)),
% 0.23/0.53    inference(resolution,[],[f185,f28])).
% 0.23/0.53  fof(f28,plain,(
% 0.23/0.53    ( ! [X0,X1] : (~v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v6_tops_1(X1,X0)) )),
% 0.23/0.53    inference(cnf_transformation,[],[f13])).
% 0.23/0.53  fof(f13,plain,(
% 0.23/0.53    ! [X0] : (! [X1] : ((v6_tops_1(X1,X0) <=> v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.23/0.53    inference(ennf_transformation,[],[f6])).
% 0.23/0.53  fof(f6,axiom,(
% 0.23/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v6_tops_1(X1,X0) <=> v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 0.23/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t101_tops_1)).
% 0.23/0.53  fof(f185,plain,(
% 0.23/0.53    v5_tops_1(k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK1,sK2)),sK0)),
% 0.23/0.53    inference(backward_demodulation,[],[f124,f184])).
% 0.23/0.53  fof(f184,plain,(
% 0.23/0.53    k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),sK2)) = k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK1,sK2))),
% 0.23/0.53    inference(forward_demodulation,[],[f174,f75])).
% 0.23/0.53  fof(f75,plain,(
% 0.23/0.53    k9_subset_1(u1_struct_0(sK0),sK1,sK2) = k7_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK2))),
% 0.23/0.53    inference(forward_demodulation,[],[f74,f42])).
% 0.23/0.53  fof(f42,plain,(
% 0.23/0.53    sK2 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2))),
% 0.23/0.53    inference(resolution,[],[f20,f33])).
% 0.23/0.53  fof(f33,plain,(
% 0.23/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 0.23/0.53    inference(cnf_transformation,[],[f18])).
% 0.23/0.53  fof(f18,plain,(
% 0.23/0.53    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.23/0.53    inference(ennf_transformation,[],[f3])).
% 0.23/0.53  fof(f3,axiom,(
% 0.23/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 0.23/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 0.23/0.53  fof(f20,plain,(
% 0.23/0.53    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.23/0.53    inference(cnf_transformation,[],[f11])).
% 0.23/0.53  fof(f74,plain,(
% 0.23/0.53    k7_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK2)) = k9_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2)))),
% 0.23/0.53    inference(resolution,[],[f50,f44])).
% 0.23/0.53  fof(f44,plain,(
% 0.23/0.53    m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.23/0.53    inference(resolution,[],[f20,f30])).
% 0.23/0.53  fof(f30,plain,(
% 0.23/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 0.23/0.53    inference(cnf_transformation,[],[f14])).
% 0.23/0.53  fof(f14,plain,(
% 0.23/0.53    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.23/0.53    inference(ennf_transformation,[],[f1])).
% 0.23/0.53  fof(f1,axiom,(
% 0.23/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.23/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 0.23/0.53  fof(f50,plain,(
% 0.23/0.53    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | k7_subset_1(u1_struct_0(sK0),sK1,X2) = k9_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),X2))) )),
% 0.23/0.53    inference(resolution,[],[f24,f27])).
% 0.23/0.53  fof(f27,plain,(
% 0.23/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))) )),
% 0.23/0.53    inference(cnf_transformation,[],[f12])).
% 0.23/0.53  fof(f12,plain,(
% 0.23/0.53    ! [X0,X1] : (! [X2] : (k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.23/0.53    inference(ennf_transformation,[],[f4])).
% 0.23/0.53  fof(f4,axiom,(
% 0.23/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))))),
% 0.23/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_subset_1)).
% 0.23/0.53  fof(f24,plain,(
% 0.23/0.53    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.23/0.53    inference(cnf_transformation,[],[f11])).
% 0.23/0.53  fof(f174,plain,(
% 0.23/0.53    k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),sK2)) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK2)))),
% 0.23/0.53    inference(resolution,[],[f48,f44])).
% 0.23/0.53  fof(f48,plain,(
% 0.23/0.53    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK1,X1)) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),X1)) )),
% 0.23/0.53    inference(resolution,[],[f24,f32])).
% 0.23/0.53  fof(f32,plain,(
% 0.23/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2)) )),
% 0.23/0.53    inference(cnf_transformation,[],[f17])).
% 0.23/0.53  fof(f17,plain,(
% 0.23/0.53    ! [X0,X1] : (! [X2] : (k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.23/0.53    inference(ennf_transformation,[],[f5])).
% 0.23/0.53  fof(f5,axiom,(
% 0.23/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2)))),
% 0.23/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_subset_1)).
% 0.23/0.53  fof(f124,plain,(
% 0.23/0.53    v5_tops_1(k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),sK2)),sK0)),
% 0.23/0.53    inference(subsumption_resolution,[],[f122,f44])).
% 0.23/0.53  fof(f122,plain,(
% 0.23/0.53    ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0))) | v5_tops_1(k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),sK2)),sK0)),
% 0.23/0.53    inference(resolution,[],[f55,f40])).
% 0.23/0.53  fof(f40,plain,(
% 0.23/0.53    v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK2),sK0)),
% 0.23/0.53    inference(subsumption_resolution,[],[f39,f26])).
% 0.23/0.53  fof(f39,plain,(
% 0.23/0.53    v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK2),sK0) | ~l1_pre_topc(sK0)),
% 0.23/0.53    inference(subsumption_resolution,[],[f38,f20])).
% 0.23/0.53  fof(f38,plain,(
% 0.23/0.53    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK2),sK0) | ~l1_pre_topc(sK0)),
% 0.23/0.53    inference(resolution,[],[f22,f29])).
% 0.23/0.53  fof(f29,plain,(
% 0.23/0.53    ( ! [X0,X1] : (~v6_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~l1_pre_topc(X0)) )),
% 0.23/0.53    inference(cnf_transformation,[],[f13])).
% 0.23/0.53  fof(f22,plain,(
% 0.23/0.53    v6_tops_1(sK2,sK0)),
% 0.23/0.53    inference(cnf_transformation,[],[f11])).
% 0.23/0.53  fof(f55,plain,(
% 0.23/0.53    ( ! [X0] : (~v5_tops_1(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v5_tops_1(k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),X0),sK0)) )),
% 0.23/0.53    inference(subsumption_resolution,[],[f54,f25])).
% 0.23/0.53  fof(f25,plain,(
% 0.23/0.53    v2_pre_topc(sK0)),
% 0.23/0.53    inference(cnf_transformation,[],[f11])).
% 0.23/0.53  fof(f54,plain,(
% 0.23/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | ~v5_tops_1(X0,sK0) | v5_tops_1(k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),X0),sK0)) )),
% 0.23/0.53    inference(subsumption_resolution,[],[f53,f49])).
% 0.23/0.53  fof(f49,plain,(
% 0.23/0.53    m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.23/0.53    inference(resolution,[],[f24,f30])).
% 0.23/0.53  fof(f53,plain,(
% 0.23/0.53    ( ! [X0] : (~m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | ~v5_tops_1(X0,sK0) | v5_tops_1(k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),X0),sK0)) )),
% 0.23/0.53    inference(subsumption_resolution,[],[f52,f26])).
% 0.23/0.53  fof(f52,plain,(
% 0.23/0.53    ( ! [X0] : (~l1_pre_topc(sK0) | ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | ~v5_tops_1(X0,sK0) | v5_tops_1(k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),X0),sK0)) )),
% 0.23/0.53    inference(resolution,[],[f37,f31])).
% 0.23/0.53  fof(f31,plain,(
% 0.23/0.53    ( ! [X2,X0,X1] : (~v5_tops_1(X1,X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~v5_tops_1(X2,X0) | v5_tops_1(k4_subset_1(u1_struct_0(X0),X1,X2),X0)) )),
% 0.23/0.53    inference(cnf_transformation,[],[f16])).
% 0.23/0.53  fof(f16,plain,(
% 0.23/0.53    ! [X0] : (! [X1] : (! [X2] : (v5_tops_1(k4_subset_1(u1_struct_0(X0),X1,X2),X0) | ~v5_tops_1(X2,X0) | ~v5_tops_1(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.23/0.53    inference(flattening,[],[f15])).
% 0.23/0.53  fof(f15,plain,(
% 0.23/0.53    ! [X0] : (! [X1] : (! [X2] : ((v5_tops_1(k4_subset_1(u1_struct_0(X0),X1,X2),X0) | (~v5_tops_1(X2,X0) | ~v5_tops_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.23/0.53    inference(ennf_transformation,[],[f7])).
% 0.23/0.53  fof(f7,axiom,(
% 0.23/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v5_tops_1(X2,X0) & v5_tops_1(X1,X0)) => v5_tops_1(k4_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 0.23/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_tops_1)).
% 0.23/0.53  fof(f37,plain,(
% 0.23/0.53    v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)),
% 0.23/0.53    inference(subsumption_resolution,[],[f36,f26])).
% 0.23/0.53  fof(f36,plain,(
% 0.23/0.53    v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | ~l1_pre_topc(sK0)),
% 0.23/0.53    inference(subsumption_resolution,[],[f35,f24])).
% 0.23/0.53  fof(f35,plain,(
% 0.23/0.53    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | ~l1_pre_topc(sK0)),
% 0.23/0.53    inference(resolution,[],[f21,f29])).
% 0.23/0.53  fof(f21,plain,(
% 0.23/0.53    v6_tops_1(sK1,sK0)),
% 0.23/0.53    inference(cnf_transformation,[],[f11])).
% 0.23/0.53  fof(f235,plain,(
% 0.23/0.53    m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.23/0.53    inference(superposition,[],[f46,f75])).
% 0.23/0.53  fof(f46,plain,(
% 0.23/0.53    ( ! [X0] : (m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.23/0.53    inference(resolution,[],[f24,f34])).
% 0.23/0.53  fof(f34,plain,(
% 0.23/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))) )),
% 0.23/0.53    inference(cnf_transformation,[],[f19])).
% 0.23/0.53  fof(f19,plain,(
% 0.23/0.53    ! [X0,X1,X2] : (m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.23/0.53    inference(ennf_transformation,[],[f2])).
% 0.23/0.53  fof(f2,axiom,(
% 0.23/0.53    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.23/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_subset_1)).
% 0.23/0.53  % SZS output end Proof for theBenchmark
% 0.23/0.53  % (17883)------------------------------
% 0.23/0.53  % (17883)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.53  % (17883)Termination reason: Refutation
% 0.23/0.53  
% 0.23/0.53  % (17883)Memory used [KB]: 6396
% 0.23/0.53  % (17883)Time elapsed: 0.112 s
% 0.23/0.53  % (17883)------------------------------
% 0.23/0.53  % (17883)------------------------------
% 0.23/0.54  % (17859)Success in time 0.165 s
%------------------------------------------------------------------------------
