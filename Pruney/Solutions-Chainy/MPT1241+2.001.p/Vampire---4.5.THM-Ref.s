%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:18 EST 2020

% Result     : Theorem 1.43s
% Output     : Refutation 1.43s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 817 expanded)
%              Number of leaves         :   13 ( 170 expanded)
%              Depth                    :   24
%              Number of atoms          :  226 (3540 expanded)
%              Number of equality atoms :   61 ( 822 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f269,plain,(
    $false ),
    inference(global_subsumption,[],[f30,f257,f268])).

fof(f268,plain,(
    sK3 = k1_tops_1(sK1,sK3) ),
    inference(forward_demodulation,[],[f267,f66])).

fof(f66,plain,(
    sK3 = k3_subset_1(k2_struct_0(sK1),k3_subset_1(k2_struct_0(sK1),sK3)) ),
    inference(resolution,[],[f49,f57])).

fof(f57,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK1))) ),
    inference(backward_demodulation,[],[f33,f55])).

fof(f55,plain,(
    u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(resolution,[],[f40,f53])).

fof(f53,plain,(
    l1_struct_0(sK1) ),
    inference(resolution,[],[f41,f35])).

fof(f35,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ~ v3_pre_topc(X2,X0)
                      & k1_tops_1(X0,X2) = X2 )
                    | ( k1_tops_1(X1,X3) != X3
                      & v3_pre_topc(X3,X1) ) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ~ v3_pre_topc(X2,X0)
                      & k1_tops_1(X0,X2) = X2 )
                    | ( k1_tops_1(X1,X3) != X3
                      & v3_pre_topc(X3,X1) ) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( l1_pre_topc(X1)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( ( k1_tops_1(X0,X2) = X2
                       => v3_pre_topc(X2,X0) )
                      & ( v3_pre_topc(X3,X1)
                       => k1_tops_1(X1,X3) = X3 ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( k1_tops_1(X0,X2) = X2
                     => v3_pre_topc(X2,X0) )
                    & ( v3_pre_topc(X3,X1)
                     => k1_tops_1(X1,X3) = X3 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tops_1)).

fof(f41,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f40,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f33,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f16])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f267,plain,(
    k1_tops_1(sK1,sK3) = k3_subset_1(k2_struct_0(sK1),k3_subset_1(k2_struct_0(sK1),sK3)) ),
    inference(backward_demodulation,[],[f216,f263])).

fof(f263,plain,(
    k3_subset_1(k2_struct_0(sK1),sK3) = k2_pre_topc(sK1,k3_subset_1(k2_struct_0(sK1),sK3)) ),
    inference(resolution,[],[f262,f247])).

fof(f247,plain,
    ( ~ v3_pre_topc(sK3,sK1)
    | k3_subset_1(k2_struct_0(sK1),sK3) = k2_pre_topc(sK1,k3_subset_1(k2_struct_0(sK1),sK3)) ),
    inference(subsumption_resolution,[],[f241,f57])).

fof(f241,plain,
    ( k3_subset_1(k2_struct_0(sK1),sK3) = k2_pre_topc(sK1,k3_subset_1(k2_struct_0(sK1),sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK1)))
    | ~ v3_pre_topc(sK3,sK1) ),
    inference(resolution,[],[f105,f149])).

fof(f149,plain,
    ( v4_pre_topc(k3_subset_1(k2_struct_0(sK1),sK3),sK1)
    | ~ v3_pre_topc(sK3,sK1) ),
    inference(subsumption_resolution,[],[f148,f57])).

fof(f148,plain,
    ( ~ v3_pre_topc(sK3,sK1)
    | v4_pre_topc(k3_subset_1(k2_struct_0(sK1),sK3),sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK1))) ),
    inference(resolution,[],[f137,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f137,plain,
    ( ~ m1_subset_1(k3_subset_1(k2_struct_0(sK1),sK3),k1_zfmisc_1(k2_struct_0(sK1)))
    | ~ v3_pre_topc(sK3,sK1)
    | v4_pre_topc(k3_subset_1(k2_struct_0(sK1),sK3),sK1) ),
    inference(superposition,[],[f133,f116])).

fof(f116,plain,(
    sK3 = k4_xboole_0(k2_struct_0(sK1),k3_subset_1(k2_struct_0(sK1),sK3)) ),
    inference(forward_demodulation,[],[f113,f66])).

fof(f113,plain,(
    k3_subset_1(k2_struct_0(sK1),k3_subset_1(k2_struct_0(sK1),sK3)) = k4_xboole_0(k2_struct_0(sK1),k3_subset_1(k2_struct_0(sK1),sK3)) ),
    inference(resolution,[],[f60,f57])).

fof(f60,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X1))
      | k3_subset_1(X1,k3_subset_1(X1,X2)) = k4_xboole_0(X1,k3_subset_1(X1,X2)) ) ),
    inference(resolution,[],[f48,f47])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f133,plain,(
    ! [X0] :
      ( ~ v3_pre_topc(k4_xboole_0(k2_struct_0(sK1),X0),sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1)))
      | v4_pre_topc(X0,sK1) ) ),
    inference(forward_demodulation,[],[f132,f70])).

fof(f70,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k7_subset_1(X0,X0,X1) ),
    inference(resolution,[],[f51,f52])).

fof(f52,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f39,f38])).

fof(f38,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f39,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f132,plain,(
    ! [X0] :
      ( ~ v3_pre_topc(k7_subset_1(k2_struct_0(sK1),k2_struct_0(sK1),X0),sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1)))
      | v4_pre_topc(X0,sK1) ) ),
    inference(subsumption_resolution,[],[f130,f35])).

fof(f130,plain,(
    ! [X0] :
      ( ~ v3_pre_topc(k7_subset_1(k2_struct_0(sK1),k2_struct_0(sK1),X0),sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1)))
      | ~ l1_pre_topc(sK1)
      | v4_pre_topc(X0,sK1) ) ),
    inference(superposition,[],[f45,f55])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v4_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_pre_topc)).

fof(f105,plain,(
    ! [X0] :
      ( ~ v4_pre_topc(k3_subset_1(k2_struct_0(sK1),X0),sK1)
      | k3_subset_1(k2_struct_0(sK1),X0) = k2_pre_topc(sK1,k3_subset_1(k2_struct_0(sK1),X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) ) ),
    inference(resolution,[],[f98,f47])).

fof(f98,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1)))
      | ~ v4_pre_topc(X0,sK1)
      | k2_pre_topc(sK1,X0) = X0 ) ),
    inference(subsumption_resolution,[],[f96,f35])).

fof(f96,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1)))
      | ~ l1_pre_topc(sK1)
      | ~ v4_pre_topc(X0,sK1)
      | k2_pre_topc(sK1,X0) = X0 ) ),
    inference(superposition,[],[f44,f55])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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

fof(f262,plain,(
    v3_pre_topc(sK3,sK1) ),
    inference(resolution,[],[f257,f32])).

fof(f32,plain,
    ( ~ v3_pre_topc(sK2,sK0)
    | v3_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f216,plain,(
    k1_tops_1(sK1,sK3) = k3_subset_1(k2_struct_0(sK1),k2_pre_topc(sK1,k3_subset_1(k2_struct_0(sK1),sK3))) ),
    inference(resolution,[],[f204,f57])).

fof(f204,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1)))
      | k1_tops_1(sK1,X0) = k3_subset_1(k2_struct_0(sK1),k2_pre_topc(sK1,k3_subset_1(k2_struct_0(sK1),X0))) ) ),
    inference(subsumption_resolution,[],[f202,f35])).

fof(f202,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1)))
      | ~ l1_pre_topc(sK1)
      | k1_tops_1(sK1,X0) = k3_subset_1(k2_struct_0(sK1),k2_pre_topc(sK1,k3_subset_1(k2_struct_0(sK1),X0))) ) ),
    inference(superposition,[],[f42,f55])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).

fof(f257,plain,(
    v3_pre_topc(sK2,sK0) ),
    inference(backward_demodulation,[],[f88,f256])).

fof(f256,plain,(
    sK2 = k1_tops_1(sK0,sK2) ),
    inference(subsumption_resolution,[],[f255,f29])).

fof(f29,plain,
    ( sK3 != k1_tops_1(sK1,sK3)
    | sK2 = k1_tops_1(sK0,sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f255,plain,
    ( sK3 = k1_tops_1(sK1,sK3)
    | sK2 = k1_tops_1(sK0,sK2) ),
    inference(forward_demodulation,[],[f252,f66])).

fof(f252,plain,
    ( k1_tops_1(sK1,sK3) = k3_subset_1(k2_struct_0(sK1),k3_subset_1(k2_struct_0(sK1),sK3))
    | sK2 = k1_tops_1(sK0,sK2) ),
    inference(superposition,[],[f216,f249])).

fof(f249,plain,
    ( k3_subset_1(k2_struct_0(sK1),sK3) = k2_pre_topc(sK1,k3_subset_1(k2_struct_0(sK1),sK3))
    | sK2 = k1_tops_1(sK0,sK2) ),
    inference(resolution,[],[f247,f31])).

fof(f31,plain,
    ( v3_pre_topc(sK3,sK1)
    | sK2 = k1_tops_1(sK0,sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f88,plain,(
    v3_pre_topc(k1_tops_1(sK0,sK2),sK0) ),
    inference(resolution,[],[f80,f58])).

fof(f58,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f34,f56])).

fof(f56,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(resolution,[],[f40,f54])).

fof(f54,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f41,f37])).

fof(f37,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f34,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f16])).

fof(f80,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
      | v3_pre_topc(k1_tops_1(sK0,X1),sK0) ) ),
    inference(subsumption_resolution,[],[f79,f36])).

fof(f36,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f79,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v2_pre_topc(sK0)
      | v3_pre_topc(k1_tops_1(sK0,X1),sK0) ) ),
    inference(subsumption_resolution,[],[f77,f37])).

fof(f77,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v3_pre_topc(k1_tops_1(sK0,X1),sK0) ) ),
    inference(superposition,[],[f50,f56])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

fof(f30,plain,
    ( sK3 != k1_tops_1(sK1,sK3)
    | ~ v3_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:32:46 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (29798)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.21/0.50  % (29798)Refutation not found, incomplete strategy% (29798)------------------------------
% 0.21/0.50  % (29798)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (29798)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (29798)Memory used [KB]: 6268
% 0.21/0.50  % (29798)Time elapsed: 0.069 s
% 0.21/0.50  % (29798)------------------------------
% 0.21/0.50  % (29798)------------------------------
% 0.21/0.52  % (29785)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.53  % (29785)Refutation not found, incomplete strategy% (29785)------------------------------
% 0.21/0.53  % (29785)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (29785)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (29785)Memory used [KB]: 6140
% 0.21/0.53  % (29785)Time elapsed: 0.063 s
% 0.21/0.53  % (29785)------------------------------
% 0.21/0.53  % (29785)------------------------------
% 0.21/0.53  % (29791)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.21/0.53  % (29801)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.21/0.53  % (29801)Refutation not found, incomplete strategy% (29801)------------------------------
% 0.21/0.53  % (29801)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (29801)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (29801)Memory used [KB]: 10618
% 0.21/0.53  % (29801)Time elapsed: 0.068 s
% 0.21/0.53  % (29801)------------------------------
% 0.21/0.53  % (29801)------------------------------
% 0.21/0.54  % (29793)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 1.43/0.54  % (29794)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 1.43/0.54  % (29794)Refutation not found, incomplete strategy% (29794)------------------------------
% 1.43/0.54  % (29794)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.54  % (29794)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.54  
% 1.43/0.54  % (29794)Memory used [KB]: 1663
% 1.43/0.54  % (29794)Time elapsed: 0.119 s
% 1.43/0.54  % (29794)------------------------------
% 1.43/0.54  % (29794)------------------------------
% 1.43/0.55  % (29784)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 1.43/0.55  % (29783)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 1.43/0.55  % (29780)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 1.43/0.55  % (29778)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 1.43/0.55  % (29799)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 1.43/0.55  % (29791)Refutation found. Thanks to Tanya!
% 1.43/0.55  % SZS status Theorem for theBenchmark
% 1.43/0.55  % SZS output start Proof for theBenchmark
% 1.43/0.56  fof(f269,plain,(
% 1.43/0.56    $false),
% 1.43/0.56    inference(global_subsumption,[],[f30,f257,f268])).
% 1.43/0.56  fof(f268,plain,(
% 1.43/0.56    sK3 = k1_tops_1(sK1,sK3)),
% 1.43/0.56    inference(forward_demodulation,[],[f267,f66])).
% 1.43/0.56  fof(f66,plain,(
% 1.43/0.56    sK3 = k3_subset_1(k2_struct_0(sK1),k3_subset_1(k2_struct_0(sK1),sK3))),
% 1.43/0.56    inference(resolution,[],[f49,f57])).
% 1.43/0.56  fof(f57,plain,(
% 1.43/0.56    m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK1)))),
% 1.43/0.56    inference(backward_demodulation,[],[f33,f55])).
% 1.43/0.56  fof(f55,plain,(
% 1.43/0.56    u1_struct_0(sK1) = k2_struct_0(sK1)),
% 1.43/0.56    inference(resolution,[],[f40,f53])).
% 1.43/0.56  fof(f53,plain,(
% 1.43/0.56    l1_struct_0(sK1)),
% 1.43/0.56    inference(resolution,[],[f41,f35])).
% 1.43/0.56  fof(f35,plain,(
% 1.43/0.56    l1_pre_topc(sK1)),
% 1.43/0.56    inference(cnf_transformation,[],[f16])).
% 1.43/0.56  fof(f16,plain,(
% 1.43/0.56    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~v3_pre_topc(X2,X0) & k1_tops_1(X0,X2) = X2) | (k1_tops_1(X1,X3) != X3 & v3_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.43/0.56    inference(flattening,[],[f15])).
% 1.43/0.56  fof(f15,plain,(
% 1.43/0.56    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~v3_pre_topc(X2,X0) & k1_tops_1(X0,X2) = X2) | (k1_tops_1(X1,X3) != X3 & v3_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 1.43/0.56    inference(ennf_transformation,[],[f14])).
% 1.43/0.56  fof(f14,negated_conjecture,(
% 1.43/0.56    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((k1_tops_1(X0,X2) = X2 => v3_pre_topc(X2,X0)) & (v3_pre_topc(X3,X1) => k1_tops_1(X1,X3) = X3))))))),
% 1.43/0.56    inference(negated_conjecture,[],[f13])).
% 1.43/0.56  fof(f13,conjecture,(
% 1.43/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((k1_tops_1(X0,X2) = X2 => v3_pre_topc(X2,X0)) & (v3_pre_topc(X3,X1) => k1_tops_1(X1,X3) = X3))))))),
% 1.43/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tops_1)).
% 1.43/0.56  fof(f41,plain,(
% 1.43/0.56    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 1.43/0.56    inference(cnf_transformation,[],[f18])).
% 1.43/0.56  fof(f18,plain,(
% 1.43/0.56    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.43/0.56    inference(ennf_transformation,[],[f9])).
% 1.43/0.56  fof(f9,axiom,(
% 1.43/0.56    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.43/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 1.43/0.56  fof(f40,plain,(
% 1.43/0.56    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 1.43/0.56    inference(cnf_transformation,[],[f17])).
% 1.43/0.56  fof(f17,plain,(
% 1.43/0.56    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 1.43/0.56    inference(ennf_transformation,[],[f7])).
% 1.43/0.56  fof(f7,axiom,(
% 1.43/0.56    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 1.43/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 1.43/0.56  fof(f33,plain,(
% 1.43/0.56    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))),
% 1.43/0.56    inference(cnf_transformation,[],[f16])).
% 1.43/0.56  fof(f49,plain,(
% 1.43/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 1.43/0.56    inference(cnf_transformation,[],[f25])).
% 1.43/0.56  fof(f25,plain,(
% 1.43/0.56    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.43/0.56    inference(ennf_transformation,[],[f5])).
% 1.43/0.56  fof(f5,axiom,(
% 1.43/0.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 1.43/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 1.43/0.56  fof(f267,plain,(
% 1.43/0.56    k1_tops_1(sK1,sK3) = k3_subset_1(k2_struct_0(sK1),k3_subset_1(k2_struct_0(sK1),sK3))),
% 1.43/0.56    inference(backward_demodulation,[],[f216,f263])).
% 1.43/0.56  fof(f263,plain,(
% 1.43/0.56    k3_subset_1(k2_struct_0(sK1),sK3) = k2_pre_topc(sK1,k3_subset_1(k2_struct_0(sK1),sK3))),
% 1.43/0.56    inference(resolution,[],[f262,f247])).
% 1.43/0.56  fof(f247,plain,(
% 1.43/0.56    ~v3_pre_topc(sK3,sK1) | k3_subset_1(k2_struct_0(sK1),sK3) = k2_pre_topc(sK1,k3_subset_1(k2_struct_0(sK1),sK3))),
% 1.43/0.56    inference(subsumption_resolution,[],[f241,f57])).
% 1.43/0.56  fof(f241,plain,(
% 1.43/0.56    k3_subset_1(k2_struct_0(sK1),sK3) = k2_pre_topc(sK1,k3_subset_1(k2_struct_0(sK1),sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK1))) | ~v3_pre_topc(sK3,sK1)),
% 1.43/0.56    inference(resolution,[],[f105,f149])).
% 1.43/0.56  fof(f149,plain,(
% 1.43/0.56    v4_pre_topc(k3_subset_1(k2_struct_0(sK1),sK3),sK1) | ~v3_pre_topc(sK3,sK1)),
% 1.43/0.56    inference(subsumption_resolution,[],[f148,f57])).
% 1.43/0.56  fof(f148,plain,(
% 1.43/0.56    ~v3_pre_topc(sK3,sK1) | v4_pre_topc(k3_subset_1(k2_struct_0(sK1),sK3),sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK1)))),
% 1.43/0.56    inference(resolution,[],[f137,f47])).
% 1.43/0.56  fof(f47,plain,(
% 1.43/0.56    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.43/0.56    inference(cnf_transformation,[],[f23])).
% 1.43/0.56  fof(f23,plain,(
% 1.43/0.56    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.43/0.56    inference(ennf_transformation,[],[f4])).
% 1.43/0.56  fof(f4,axiom,(
% 1.43/0.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.43/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 1.43/0.56  fof(f137,plain,(
% 1.43/0.56    ~m1_subset_1(k3_subset_1(k2_struct_0(sK1),sK3),k1_zfmisc_1(k2_struct_0(sK1))) | ~v3_pre_topc(sK3,sK1) | v4_pre_topc(k3_subset_1(k2_struct_0(sK1),sK3),sK1)),
% 1.43/0.56    inference(superposition,[],[f133,f116])).
% 1.43/0.56  fof(f116,plain,(
% 1.43/0.56    sK3 = k4_xboole_0(k2_struct_0(sK1),k3_subset_1(k2_struct_0(sK1),sK3))),
% 1.43/0.56    inference(forward_demodulation,[],[f113,f66])).
% 1.43/0.56  fof(f113,plain,(
% 1.43/0.56    k3_subset_1(k2_struct_0(sK1),k3_subset_1(k2_struct_0(sK1),sK3)) = k4_xboole_0(k2_struct_0(sK1),k3_subset_1(k2_struct_0(sK1),sK3))),
% 1.43/0.56    inference(resolution,[],[f60,f57])).
% 1.43/0.56  fof(f60,plain,(
% 1.43/0.56    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X1)) | k3_subset_1(X1,k3_subset_1(X1,X2)) = k4_xboole_0(X1,k3_subset_1(X1,X2))) )),
% 1.43/0.56    inference(resolution,[],[f48,f47])).
% 1.43/0.56  fof(f48,plain,(
% 1.43/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)) )),
% 1.43/0.56    inference(cnf_transformation,[],[f24])).
% 1.43/0.56  fof(f24,plain,(
% 1.43/0.56    ! [X0,X1] : (k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.43/0.56    inference(ennf_transformation,[],[f2])).
% 1.43/0.56  fof(f2,axiom,(
% 1.43/0.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,X1) = k4_xboole_0(X0,X1))),
% 1.43/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 1.43/0.56  fof(f133,plain,(
% 1.43/0.56    ( ! [X0] : (~v3_pre_topc(k4_xboole_0(k2_struct_0(sK1),X0),sK1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) | v4_pre_topc(X0,sK1)) )),
% 1.43/0.56    inference(forward_demodulation,[],[f132,f70])).
% 1.43/0.56  fof(f70,plain,(
% 1.43/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k7_subset_1(X0,X0,X1)) )),
% 1.43/0.56    inference(resolution,[],[f51,f52])).
% 1.43/0.56  fof(f52,plain,(
% 1.43/0.56    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 1.43/0.56    inference(forward_demodulation,[],[f39,f38])).
% 1.43/0.56  fof(f38,plain,(
% 1.43/0.56    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.43/0.56    inference(cnf_transformation,[],[f1])).
% 1.43/0.56  fof(f1,axiom,(
% 1.43/0.56    ! [X0] : k2_subset_1(X0) = X0),
% 1.43/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 1.43/0.56  fof(f39,plain,(
% 1.43/0.56    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 1.43/0.56    inference(cnf_transformation,[],[f3])).
% 1.43/0.56  fof(f3,axiom,(
% 1.43/0.56    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 1.43/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 1.43/0.56  fof(f51,plain,(
% 1.43/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)) )),
% 1.43/0.56    inference(cnf_transformation,[],[f28])).
% 1.43/0.56  fof(f28,plain,(
% 1.43/0.56    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.43/0.56    inference(ennf_transformation,[],[f6])).
% 1.43/0.56  fof(f6,axiom,(
% 1.43/0.56    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 1.43/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 1.43/0.56  fof(f132,plain,(
% 1.43/0.56    ( ! [X0] : (~v3_pre_topc(k7_subset_1(k2_struct_0(sK1),k2_struct_0(sK1),X0),sK1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) | v4_pre_topc(X0,sK1)) )),
% 1.43/0.56    inference(subsumption_resolution,[],[f130,f35])).
% 1.43/0.56  fof(f130,plain,(
% 1.43/0.56    ( ! [X0] : (~v3_pre_topc(k7_subset_1(k2_struct_0(sK1),k2_struct_0(sK1),X0),sK1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) | ~l1_pre_topc(sK1) | v4_pre_topc(X0,sK1)) )),
% 1.43/0.56    inference(superposition,[],[f45,f55])).
% 1.43/0.56  fof(f45,plain,(
% 1.43/0.56    ( ! [X0,X1] : (~v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v4_pre_topc(X1,X0)) )),
% 1.43/0.56    inference(cnf_transformation,[],[f22])).
% 1.43/0.56  fof(f22,plain,(
% 1.43/0.56    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.43/0.56    inference(ennf_transformation,[],[f8])).
% 1.43/0.56  fof(f8,axiom,(
% 1.43/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0))))),
% 1.43/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_pre_topc)).
% 1.43/0.56  fof(f105,plain,(
% 1.43/0.56    ( ! [X0] : (~v4_pre_topc(k3_subset_1(k2_struct_0(sK1),X0),sK1) | k3_subset_1(k2_struct_0(sK1),X0) = k2_pre_topc(sK1,k3_subset_1(k2_struct_0(sK1),X0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1)))) )),
% 1.43/0.56    inference(resolution,[],[f98,f47])).
% 1.43/0.56  fof(f98,plain,(
% 1.43/0.56    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) | ~v4_pre_topc(X0,sK1) | k2_pre_topc(sK1,X0) = X0) )),
% 1.43/0.56    inference(subsumption_resolution,[],[f96,f35])).
% 1.43/0.56  fof(f96,plain,(
% 1.43/0.56    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) | ~l1_pre_topc(sK1) | ~v4_pre_topc(X0,sK1) | k2_pre_topc(sK1,X0) = X0) )),
% 1.43/0.56    inference(superposition,[],[f44,f55])).
% 1.43/0.56  fof(f44,plain,(
% 1.43/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) = X1) )),
% 1.43/0.56    inference(cnf_transformation,[],[f21])).
% 1.43/0.56  fof(f21,plain,(
% 1.43/0.56    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.43/0.56    inference(flattening,[],[f20])).
% 1.43/0.56  fof(f20,plain,(
% 1.43/0.56    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.43/0.56    inference(ennf_transformation,[],[f10])).
% 1.43/0.56  fof(f10,axiom,(
% 1.43/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 1.43/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).
% 1.43/0.56  fof(f262,plain,(
% 1.43/0.56    v3_pre_topc(sK3,sK1)),
% 1.43/0.56    inference(resolution,[],[f257,f32])).
% 1.43/0.56  fof(f32,plain,(
% 1.43/0.56    ~v3_pre_topc(sK2,sK0) | v3_pre_topc(sK3,sK1)),
% 1.43/0.56    inference(cnf_transformation,[],[f16])).
% 1.43/0.56  fof(f216,plain,(
% 1.43/0.56    k1_tops_1(sK1,sK3) = k3_subset_1(k2_struct_0(sK1),k2_pre_topc(sK1,k3_subset_1(k2_struct_0(sK1),sK3)))),
% 1.43/0.56    inference(resolution,[],[f204,f57])).
% 1.43/0.56  fof(f204,plain,(
% 1.43/0.56    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) | k1_tops_1(sK1,X0) = k3_subset_1(k2_struct_0(sK1),k2_pre_topc(sK1,k3_subset_1(k2_struct_0(sK1),X0)))) )),
% 1.43/0.56    inference(subsumption_resolution,[],[f202,f35])).
% 1.43/0.56  fof(f202,plain,(
% 1.43/0.56    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) | ~l1_pre_topc(sK1) | k1_tops_1(sK1,X0) = k3_subset_1(k2_struct_0(sK1),k2_pre_topc(sK1,k3_subset_1(k2_struct_0(sK1),X0)))) )),
% 1.43/0.56    inference(superposition,[],[f42,f55])).
% 1.43/0.56  fof(f42,plain,(
% 1.43/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))) )),
% 1.43/0.56    inference(cnf_transformation,[],[f19])).
% 1.43/0.56  fof(f19,plain,(
% 1.43/0.56    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.43/0.56    inference(ennf_transformation,[],[f11])).
% 1.43/0.56  fof(f11,axiom,(
% 1.43/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))))),
% 1.43/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).
% 1.43/0.56  fof(f257,plain,(
% 1.43/0.56    v3_pre_topc(sK2,sK0)),
% 1.43/0.56    inference(backward_demodulation,[],[f88,f256])).
% 1.43/0.56  fof(f256,plain,(
% 1.43/0.56    sK2 = k1_tops_1(sK0,sK2)),
% 1.43/0.56    inference(subsumption_resolution,[],[f255,f29])).
% 1.43/0.56  fof(f29,plain,(
% 1.43/0.56    sK3 != k1_tops_1(sK1,sK3) | sK2 = k1_tops_1(sK0,sK2)),
% 1.43/0.56    inference(cnf_transformation,[],[f16])).
% 1.43/0.56  fof(f255,plain,(
% 1.43/0.56    sK3 = k1_tops_1(sK1,sK3) | sK2 = k1_tops_1(sK0,sK2)),
% 1.43/0.56    inference(forward_demodulation,[],[f252,f66])).
% 1.43/0.56  fof(f252,plain,(
% 1.43/0.56    k1_tops_1(sK1,sK3) = k3_subset_1(k2_struct_0(sK1),k3_subset_1(k2_struct_0(sK1),sK3)) | sK2 = k1_tops_1(sK0,sK2)),
% 1.43/0.56    inference(superposition,[],[f216,f249])).
% 1.43/0.56  fof(f249,plain,(
% 1.43/0.56    k3_subset_1(k2_struct_0(sK1),sK3) = k2_pre_topc(sK1,k3_subset_1(k2_struct_0(sK1),sK3)) | sK2 = k1_tops_1(sK0,sK2)),
% 1.43/0.56    inference(resolution,[],[f247,f31])).
% 1.43/0.56  fof(f31,plain,(
% 1.43/0.56    v3_pre_topc(sK3,sK1) | sK2 = k1_tops_1(sK0,sK2)),
% 1.43/0.56    inference(cnf_transformation,[],[f16])).
% 1.43/0.56  fof(f88,plain,(
% 1.43/0.56    v3_pre_topc(k1_tops_1(sK0,sK2),sK0)),
% 1.43/0.56    inference(resolution,[],[f80,f58])).
% 1.43/0.56  fof(f58,plain,(
% 1.43/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0)))),
% 1.43/0.56    inference(backward_demodulation,[],[f34,f56])).
% 1.43/0.56  fof(f56,plain,(
% 1.43/0.56    u1_struct_0(sK0) = k2_struct_0(sK0)),
% 1.43/0.56    inference(resolution,[],[f40,f54])).
% 1.43/0.56  fof(f54,plain,(
% 1.43/0.56    l1_struct_0(sK0)),
% 1.43/0.56    inference(resolution,[],[f41,f37])).
% 1.43/0.56  fof(f37,plain,(
% 1.43/0.56    l1_pre_topc(sK0)),
% 1.43/0.56    inference(cnf_transformation,[],[f16])).
% 1.43/0.56  fof(f34,plain,(
% 1.43/0.56    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.43/0.56    inference(cnf_transformation,[],[f16])).
% 1.43/0.56  fof(f80,plain,(
% 1.43/0.56    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | v3_pre_topc(k1_tops_1(sK0,X1),sK0)) )),
% 1.43/0.56    inference(subsumption_resolution,[],[f79,f36])).
% 1.43/0.56  fof(f36,plain,(
% 1.43/0.56    v2_pre_topc(sK0)),
% 1.43/0.56    inference(cnf_transformation,[],[f16])).
% 1.43/0.56  fof(f79,plain,(
% 1.43/0.56    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~v2_pre_topc(sK0) | v3_pre_topc(k1_tops_1(sK0,X1),sK0)) )),
% 1.43/0.56    inference(subsumption_resolution,[],[f77,f37])).
% 1.43/0.56  fof(f77,plain,(
% 1.43/0.56    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v3_pre_topc(k1_tops_1(sK0,X1),sK0)) )),
% 1.43/0.56    inference(superposition,[],[f50,f56])).
% 1.43/0.56  fof(f50,plain,(
% 1.43/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v3_pre_topc(k1_tops_1(X0,X1),X0)) )),
% 1.43/0.56    inference(cnf_transformation,[],[f27])).
% 1.43/0.56  fof(f27,plain,(
% 1.43/0.56    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.43/0.56    inference(flattening,[],[f26])).
% 1.43/0.56  fof(f26,plain,(
% 1.43/0.56    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.43/0.56    inference(ennf_transformation,[],[f12])).
% 1.43/0.56  fof(f12,axiom,(
% 1.43/0.56    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 1.43/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).
% 1.43/0.56  fof(f30,plain,(
% 1.43/0.56    sK3 != k1_tops_1(sK1,sK3) | ~v3_pre_topc(sK2,sK0)),
% 1.43/0.56    inference(cnf_transformation,[],[f16])).
% 1.43/0.56  % SZS output end Proof for theBenchmark
% 1.43/0.56  % (29791)------------------------------
% 1.43/0.56  % (29791)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.56  % (29791)Termination reason: Refutation
% 1.43/0.56  
% 1.43/0.56  % (29791)Memory used [KB]: 6396
% 1.43/0.56  % (29791)Time elapsed: 0.121 s
% 1.43/0.56  % (29791)------------------------------
% 1.43/0.56  % (29791)------------------------------
% 1.43/0.56  % (29779)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 1.43/0.56  % (29777)Success in time 0.194 s
%------------------------------------------------------------------------------
