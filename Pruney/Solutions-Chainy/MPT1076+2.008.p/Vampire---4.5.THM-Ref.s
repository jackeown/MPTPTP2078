%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:12 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 361 expanded)
%              Number of leaves         :    7 (  67 expanded)
%              Depth                    :   13
%              Number of atoms          :  267 (2646 expanded)
%              Number of equality atoms :   35 ( 276 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f153,plain,(
    $false ),
    inference(global_subsumption,[],[f149,f152])).

fof(f152,plain,(
    k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(forward_demodulation,[],[f151,f111])).

fof(f111,plain,(
    k3_funct_2(sK1,sK0,sK3,sK5) = k1_funct_1(sK3,sK5) ),
    inference(resolution,[],[f54,f23])).

fof(f23,plain,(
    m1_subset_1(sK5,sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2,X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5))
                      & v1_partfun1(X4,X0)
                      & m1_subset_1(X5,X1) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                  & v1_funct_1(X4) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2,X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5))
                      & v1_partfun1(X4,X0)
                      & m1_subset_1(X5,X1) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                  & v1_funct_1(X4) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2,X3] :
                ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
                  & v1_funct_2(X3,X1,X0)
                  & v1_funct_1(X3) )
               => ! [X4] :
                    ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                      & v1_funct_1(X4) )
                   => ! [X5] :
                        ( m1_subset_1(X5,X1)
                       => ( v1_partfun1(X4,X0)
                         => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2,X3] :
              ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
                & v1_funct_2(X3,X1,X0)
                & v1_funct_1(X3) )
             => ! [X4] :
                  ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                    & v1_funct_1(X4) )
                 => ! [X5] :
                      ( m1_subset_1(X5,X1)
                     => ( v1_partfun1(X4,X0)
                       => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t193_funct_2)).

fof(f54,plain,(
    ! [X6] :
      ( ~ m1_subset_1(X6,sK1)
      | k3_funct_2(sK1,sK0,sK3,X6) = k1_funct_1(sK3,X6) ) ),
    inference(global_subsumption,[],[f28,f31,f29,f48])).

fof(f48,plain,(
    ! [X6] :
      ( ~ m1_subset_1(X6,sK1)
      | ~ v1_funct_2(sK3,sK1,sK0)
      | ~ v1_funct_1(sK3)
      | v1_xboole_0(sK1)
      | k3_funct_2(sK1,sK0,sK3,X6) = k1_funct_1(sK3,X6) ) ),
    inference(resolution,[],[f38,f30])).

fof(f30,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f10])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0)
      | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

fof(f29,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f31,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f28,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f10])).

fof(f151,plain,(
    k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) ),
    inference(resolution,[],[f147,f23])).

fof(f147,plain,(
    ! [X5] :
      ( ~ m1_subset_1(X5,sK1)
      | k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X5) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,X5)) ) ),
    inference(global_subsumption,[],[f26,f24,f144])).

fof(f144,plain,(
    ! [X5] :
      ( ~ m1_subset_1(X5,sK1)
      | ~ v1_funct_1(sK4)
      | ~ v1_partfun1(sK4,sK0)
      | k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X5) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,X5)) ) ),
    inference(resolution,[],[f107,f27])).

fof(f27,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f10])).

fof(f107,plain,(
    ! [X10,X8,X9] :
      ( ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(sK0,X9)))
      | ~ m1_subset_1(X10,sK1)
      | ~ v1_funct_1(X8)
      | ~ v1_partfun1(X8,sK0)
      | k3_funct_2(sK1,X9,k8_funct_2(sK1,sK0,X9,sK3,X8),X10) = k1_funct_1(X8,k3_funct_2(sK1,sK0,sK3,X10)) ) ),
    inference(global_subsumption,[],[f28,f31,f32,f29,f89])).

fof(f89,plain,(
    ! [X10,X8,X9] :
      ( ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(sK0,X9)))
      | ~ m1_subset_1(X10,sK1)
      | ~ v1_funct_2(sK3,sK1,sK0)
      | ~ v1_funct_1(sK3)
      | ~ v1_funct_1(X8)
      | v1_xboole_0(sK1)
      | v1_xboole_0(sK0)
      | ~ v1_partfun1(X8,sK0)
      | k3_funct_2(sK1,X9,k8_funct_2(sK1,sK0,X9,sK3,X8),X10) = k1_funct_1(X8,k3_funct_2(sK1,sK0,sK3,X10)) ) ),
    inference(resolution,[],[f34,f30])).

fof(f34,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(X5,X1)
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0)
      | ~ v1_partfun1(X4,X0)
      | k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2,X3] :
              ( ! [X4] :
                  ( ! [X5] :
                      ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5))
                      | ~ v1_partfun1(X4,X0)
                      | ~ m1_subset_1(X5,X1) )
                  | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                  | ~ v1_funct_1(X4) )
              | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              | ~ v1_funct_2(X3,X1,X0)
              | ~ v1_funct_1(X3) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2,X3] :
              ( ! [X4] :
                  ( ! [X5] :
                      ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5))
                      | ~ v1_partfun1(X4,X0)
                      | ~ m1_subset_1(X5,X1) )
                  | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                  | ~ v1_funct_1(X4) )
              | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              | ~ v1_funct_2(X3,X1,X0)
              | ~ v1_funct_1(X3) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2,X3] :
              ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
                & v1_funct_2(X3,X1,X0)
                & v1_funct_1(X3) )
             => ! [X4] :
                  ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                    & v1_funct_1(X4) )
                 => ! [X5] :
                      ( m1_subset_1(X5,X1)
                     => ( v1_partfun1(X4,X0)
                       => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t192_funct_2)).

fof(f32,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f24,plain,(
    v1_partfun1(sK4,sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f26,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f10])).

fof(f149,plain,(
    k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(backward_demodulation,[],[f112,f142])).

fof(f142,plain,(
    k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(forward_demodulation,[],[f127,f122])).

fof(f122,plain,(
    k3_funct_2(sK0,sK2,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(resolution,[],[f55,f114])).

fof(f114,plain,(
    m1_subset_1(k1_funct_1(sK3,sK5),sK0) ),
    inference(global_subsumption,[],[f28,f31,f23,f29,f30,f113])).

fof(f113,plain,
    ( m1_subset_1(k1_funct_1(sK3,sK5),sK0)
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK5,sK1)
    | v1_xboole_0(sK1) ),
    inference(superposition,[],[f37,f111])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_funct_2)).

fof(f55,plain,(
    ! [X7] :
      ( ~ m1_subset_1(X7,sK0)
      | k3_funct_2(sK0,sK2,sK4,X7) = k1_funct_1(sK4,X7) ) ),
    inference(global_subsumption,[],[f26,f32,f44,f49])).

fof(f49,plain,(
    ! [X7] :
      ( ~ m1_subset_1(X7,sK0)
      | ~ v1_funct_2(sK4,sK0,sK2)
      | ~ v1_funct_1(sK4)
      | v1_xboole_0(sK0)
      | k3_funct_2(sK0,sK2,sK4,X7) = k1_funct_1(sK4,X7) ) ),
    inference(resolution,[],[f38,f27])).

fof(f44,plain,(
    v1_funct_2(sK4,sK0,sK2) ),
    inference(global_subsumption,[],[f26,f24,f42])).

fof(f42,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_partfun1(sK4,sK0)
    | v1_funct_2(sK4,sK0,sK2) ),
    inference(resolution,[],[f36,f27])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_partfun1(X2,X0)
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v1_partfun1(X2,X0)
          & v1_funct_1(X2) )
       => ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_2)).

fof(f127,plain,(
    k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) = k3_funct_2(sK0,sK2,sK4,k1_funct_1(sK3,sK5)) ),
    inference(resolution,[],[f79,f114])).

fof(f79,plain,(
    ! [X7] :
      ( ~ m1_subset_1(X7,sK0)
      | k3_funct_2(sK0,sK2,sK4,X7) = k7_partfun1(sK2,sK4,X7) ) ),
    inference(global_subsumption,[],[f26,f32,f41,f44,f73])).

fof(f73,plain,(
    ! [X7] :
      ( ~ m1_subset_1(X7,sK0)
      | ~ v1_funct_1(sK4)
      | ~ v1_funct_2(sK4,sK0,sK2)
      | v1_xboole_0(sK2)
      | v1_xboole_0(sK0)
      | k3_funct_2(sK0,sK2,sK4,X7) = k7_partfun1(sK2,sK4,X7) ) ),
    inference(resolution,[],[f33,f27])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,X0)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0)
      | k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3)
                  | ~ m1_subset_1(X3,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_2(X2,X0,X1)
              | ~ v1_funct_1(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3)
                  | ~ m1_subset_1(X3,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_2(X2,X0,X1)
              | ~ v1_funct_1(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X2,X0,X1)
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_subset_1(X3,X0)
                 => k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t176_funct_2)).

fof(f41,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(global_subsumption,[],[f32,f24,f39])).

fof(f39,plain,
    ( ~ v1_xboole_0(sK2)
    | v1_xboole_0(sK0)
    | ~ v1_partfun1(sK4,sK0) ),
    inference(resolution,[],[f35,f27])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0)
      | ~ v1_partfun1(X2,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ~ v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ~ v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ~ v1_partfun1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_partfun1)).

fof(f112,plain,(
    k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) ),
    inference(backward_demodulation,[],[f25,f111])).

fof(f25,plain,(
    k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:24:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.44  % (21675)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.20/0.45  % (21683)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.20/0.46  % (21675)Refutation found. Thanks to Tanya!
% 0.20/0.46  % SZS status Theorem for theBenchmark
% 0.20/0.46  % SZS output start Proof for theBenchmark
% 0.20/0.46  fof(f153,plain,(
% 0.20/0.46    $false),
% 0.20/0.46    inference(global_subsumption,[],[f149,f152])).
% 0.20/0.46  fof(f152,plain,(
% 0.20/0.46    k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))),
% 0.20/0.46    inference(forward_demodulation,[],[f151,f111])).
% 0.20/0.46  fof(f111,plain,(
% 0.20/0.46    k3_funct_2(sK1,sK0,sK3,sK5) = k1_funct_1(sK3,sK5)),
% 0.20/0.46    inference(resolution,[],[f54,f23])).
% 0.20/0.46  fof(f23,plain,(
% 0.20/0.46    m1_subset_1(sK5,sK1)),
% 0.20/0.46    inference(cnf_transformation,[],[f10])).
% 0.20/0.46  fof(f10,plain,(
% 0.20/0.46    ? [X0] : (? [X1] : (? [X2,X3] : (? [X4] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.20/0.46    inference(flattening,[],[f9])).
% 0.20/0.46  fof(f9,plain,(
% 0.20/0.46    ? [X0] : (? [X1] : (? [X2,X3] : (? [X4] : (? [X5] : ((k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0)) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.20/0.46    inference(ennf_transformation,[],[f8])).
% 0.20/0.46  fof(f8,negated_conjecture,(
% 0.20/0.46    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (v1_partfun1(X4,X0) => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5))))))))),
% 0.20/0.46    inference(negated_conjecture,[],[f7])).
% 0.20/0.46  fof(f7,conjecture,(
% 0.20/0.46    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (v1_partfun1(X4,X0) => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5))))))))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t193_funct_2)).
% 0.20/0.46  fof(f54,plain,(
% 0.20/0.46    ( ! [X6] : (~m1_subset_1(X6,sK1) | k3_funct_2(sK1,sK0,sK3,X6) = k1_funct_1(sK3,X6)) )),
% 0.20/0.46    inference(global_subsumption,[],[f28,f31,f29,f48])).
% 0.20/0.46  fof(f48,plain,(
% 0.20/0.46    ( ! [X6] : (~m1_subset_1(X6,sK1) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | v1_xboole_0(sK1) | k3_funct_2(sK1,sK0,sK3,X6) = k1_funct_1(sK3,X6)) )),
% 0.20/0.46    inference(resolution,[],[f38,f30])).
% 0.20/0.46  fof(f30,plain,(
% 0.20/0.46    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.20/0.46    inference(cnf_transformation,[],[f10])).
% 0.20/0.47  fof(f38,plain,(
% 0.20/0.47    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0) | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f22])).
% 0.20/0.47  fof(f22,plain,(
% 0.20/0.47    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 0.20/0.47    inference(flattening,[],[f21])).
% 0.20/0.47  fof(f21,plain,(
% 0.20/0.47    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f4])).
% 0.20/0.47  fof(f4,axiom,(
% 0.20/0.47    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).
% 0.20/0.47  fof(f29,plain,(
% 0.20/0.47    v1_funct_2(sK3,sK1,sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f10])).
% 0.20/0.47  fof(f31,plain,(
% 0.20/0.47    ~v1_xboole_0(sK1)),
% 0.20/0.47    inference(cnf_transformation,[],[f10])).
% 0.20/0.47  fof(f28,plain,(
% 0.20/0.47    v1_funct_1(sK3)),
% 0.20/0.47    inference(cnf_transformation,[],[f10])).
% 0.20/0.47  fof(f151,plain,(
% 0.20/0.47    k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5))),
% 0.20/0.47    inference(resolution,[],[f147,f23])).
% 0.20/0.47  fof(f147,plain,(
% 0.20/0.47    ( ! [X5] : (~m1_subset_1(X5,sK1) | k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X5) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,X5))) )),
% 0.20/0.47    inference(global_subsumption,[],[f26,f24,f144])).
% 0.20/0.47  fof(f144,plain,(
% 0.20/0.47    ( ! [X5] : (~m1_subset_1(X5,sK1) | ~v1_funct_1(sK4) | ~v1_partfun1(sK4,sK0) | k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X5) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,X5))) )),
% 0.20/0.47    inference(resolution,[],[f107,f27])).
% 0.20/0.47  fof(f27,plain,(
% 0.20/0.47    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.20/0.47    inference(cnf_transformation,[],[f10])).
% 0.20/0.47  fof(f107,plain,(
% 0.20/0.47    ( ! [X10,X8,X9] : (~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(sK0,X9))) | ~m1_subset_1(X10,sK1) | ~v1_funct_1(X8) | ~v1_partfun1(X8,sK0) | k3_funct_2(sK1,X9,k8_funct_2(sK1,sK0,X9,sK3,X8),X10) = k1_funct_1(X8,k3_funct_2(sK1,sK0,sK3,X10))) )),
% 0.20/0.47    inference(global_subsumption,[],[f28,f31,f32,f29,f89])).
% 0.20/0.47  fof(f89,plain,(
% 0.20/0.47    ( ! [X10,X8,X9] : (~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(sK0,X9))) | ~m1_subset_1(X10,sK1) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~v1_funct_1(X8) | v1_xboole_0(sK1) | v1_xboole_0(sK0) | ~v1_partfun1(X8,sK0) | k3_funct_2(sK1,X9,k8_funct_2(sK1,sK0,X9,sK3,X8),X10) = k1_funct_1(X8,k3_funct_2(sK1,sK0,sK3,X10))) )),
% 0.20/0.47    inference(resolution,[],[f34,f30])).
% 0.20/0.47  fof(f34,plain,(
% 0.20/0.47    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~m1_subset_1(X5,X1) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~v1_funct_1(X4) | v1_xboole_0(X1) | v1_xboole_0(X0) | ~v1_partfun1(X4,X0) | k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f14])).
% 0.20/0.47  fof(f14,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (! [X2,X3] : (! [X4] : (! [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) | ~v1_partfun1(X4,X0) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.20/0.47    inference(flattening,[],[f13])).
% 0.20/0.47  fof(f13,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (! [X2,X3] : (! [X4] : (! [X5] : ((k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) | ~v1_partfun1(X4,X0)) | ~m1_subset_1(X5,X1)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f6])).
% 0.20/0.47  fof(f6,axiom,(
% 0.20/0.47    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (v1_partfun1(X4,X0) => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5))))))))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t192_funct_2)).
% 0.20/0.47  fof(f32,plain,(
% 0.20/0.47    ~v1_xboole_0(sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f10])).
% 0.20/0.47  fof(f24,plain,(
% 0.20/0.47    v1_partfun1(sK4,sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f10])).
% 0.20/0.47  fof(f26,plain,(
% 0.20/0.47    v1_funct_1(sK4)),
% 0.20/0.47    inference(cnf_transformation,[],[f10])).
% 0.20/0.47  fof(f149,plain,(
% 0.20/0.47    k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))),
% 0.20/0.47    inference(backward_demodulation,[],[f112,f142])).
% 0.20/0.47  fof(f142,plain,(
% 0.20/0.47    k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))),
% 0.20/0.47    inference(forward_demodulation,[],[f127,f122])).
% 0.20/0.47  fof(f122,plain,(
% 0.20/0.47    k3_funct_2(sK0,sK2,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))),
% 0.20/0.47    inference(resolution,[],[f55,f114])).
% 0.20/0.47  fof(f114,plain,(
% 0.20/0.47    m1_subset_1(k1_funct_1(sK3,sK5),sK0)),
% 0.20/0.47    inference(global_subsumption,[],[f28,f31,f23,f29,f30,f113])).
% 0.20/0.47  fof(f113,plain,(
% 0.20/0.47    m1_subset_1(k1_funct_1(sK3,sK5),sK0) | ~v1_funct_1(sK3) | ~v1_funct_2(sK3,sK1,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~m1_subset_1(sK5,sK1) | v1_xboole_0(sK1)),
% 0.20/0.47    inference(superposition,[],[f37,f111])).
% 0.20/0.47  fof(f37,plain,(
% 0.20/0.47    ( ! [X2,X0,X3,X1] : (m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,X0) | v1_xboole_0(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f20])).
% 0.20/0.47  fof(f20,plain,(
% 0.20/0.47    ! [X0,X1,X2,X3] : (m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 0.20/0.47    inference(flattening,[],[f19])).
% 0.20/0.47  fof(f19,plain,(
% 0.20/0.47    ! [X0,X1,X2,X3] : (m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f3])).
% 0.20/0.47  fof(f3,axiom,(
% 0.20/0.47    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_funct_2)).
% 0.20/0.47  fof(f55,plain,(
% 0.20/0.47    ( ! [X7] : (~m1_subset_1(X7,sK0) | k3_funct_2(sK0,sK2,sK4,X7) = k1_funct_1(sK4,X7)) )),
% 0.20/0.47    inference(global_subsumption,[],[f26,f32,f44,f49])).
% 0.20/0.47  fof(f49,plain,(
% 0.20/0.47    ( ! [X7] : (~m1_subset_1(X7,sK0) | ~v1_funct_2(sK4,sK0,sK2) | ~v1_funct_1(sK4) | v1_xboole_0(sK0) | k3_funct_2(sK0,sK2,sK4,X7) = k1_funct_1(sK4,X7)) )),
% 0.20/0.47    inference(resolution,[],[f38,f27])).
% 0.20/0.47  fof(f44,plain,(
% 0.20/0.47    v1_funct_2(sK4,sK0,sK2)),
% 0.20/0.47    inference(global_subsumption,[],[f26,f24,f42])).
% 0.20/0.47  fof(f42,plain,(
% 0.20/0.47    ~v1_funct_1(sK4) | ~v1_partfun1(sK4,sK0) | v1_funct_2(sK4,sK0,sK2)),
% 0.20/0.47    inference(resolution,[],[f36,f27])).
% 0.20/0.47  fof(f36,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v1_partfun1(X2,X0) | v1_funct_2(X2,X0,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f18])).
% 0.20/0.47  fof(f18,plain,(
% 0.20/0.47    ! [X0,X1,X2] : ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.47    inference(flattening,[],[f17])).
% 0.20/0.47  fof(f17,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~v1_partfun1(X2,X0) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.47    inference(ennf_transformation,[],[f1])).
% 0.20/0.47  fof(f1,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_partfun1(X2,X0) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_2)).
% 0.20/0.47  fof(f127,plain,(
% 0.20/0.47    k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) = k3_funct_2(sK0,sK2,sK4,k1_funct_1(sK3,sK5))),
% 0.20/0.47    inference(resolution,[],[f79,f114])).
% 0.20/0.47  fof(f79,plain,(
% 0.20/0.47    ( ! [X7] : (~m1_subset_1(X7,sK0) | k3_funct_2(sK0,sK2,sK4,X7) = k7_partfun1(sK2,sK4,X7)) )),
% 0.20/0.47    inference(global_subsumption,[],[f26,f32,f41,f44,f73])).
% 0.20/0.47  fof(f73,plain,(
% 0.20/0.47    ( ! [X7] : (~m1_subset_1(X7,sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK0,sK2) | v1_xboole_0(sK2) | v1_xboole_0(sK0) | k3_funct_2(sK0,sK2,sK4,X7) = k7_partfun1(sK2,sK4,X7)) )),
% 0.20/0.47    inference(resolution,[],[f33,f27])).
% 0.20/0.47  fof(f33,plain,(
% 0.20/0.47    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,X0) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | v1_xboole_0(X1) | v1_xboole_0(X0) | k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f12])).
% 0.20/0.47  fof(f12,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3) | ~m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.20/0.47    inference(flattening,[],[f11])).
% 0.20/0.47  fof(f11,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3) | ~m1_subset_1(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f5])).
% 0.20/0.47  fof(f5,axiom,(
% 0.20/0.47    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,X0) => k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3)))))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t176_funct_2)).
% 0.20/0.47  fof(f41,plain,(
% 0.20/0.47    ~v1_xboole_0(sK2)),
% 0.20/0.47    inference(global_subsumption,[],[f32,f24,f39])).
% 0.20/0.47  fof(f39,plain,(
% 0.20/0.47    ~v1_xboole_0(sK2) | v1_xboole_0(sK0) | ~v1_partfun1(sK4,sK0)),
% 0.20/0.47    inference(resolution,[],[f35,f27])).
% 0.20/0.47  fof(f35,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X1) | v1_xboole_0(X0) | ~v1_partfun1(X2,X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f16])).
% 0.20/0.47  fof(f16,plain,(
% 0.20/0.47    ! [X0,X1] : (! [X2] : (~v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X1) | v1_xboole_0(X0))),
% 0.20/0.47    inference(flattening,[],[f15])).
% 0.20/0.47  fof(f15,plain,(
% 0.20/0.47    ! [X0,X1] : (! [X2] : (~v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | (~v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f2])).
% 0.20/0.47  fof(f2,axiom,(
% 0.20/0.47    ! [X0,X1] : ((v1_xboole_0(X1) & ~v1_xboole_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ~v1_partfun1(X2,X0)))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_partfun1)).
% 0.20/0.47  fof(f112,plain,(
% 0.20/0.47    k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5))),
% 0.20/0.47    inference(backward_demodulation,[],[f25,f111])).
% 0.20/0.47  fof(f25,plain,(
% 0.20/0.47    k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5))),
% 0.20/0.47    inference(cnf_transformation,[],[f10])).
% 0.20/0.47  % SZS output end Proof for theBenchmark
% 0.20/0.47  % (21675)------------------------------
% 0.20/0.47  % (21675)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (21675)Termination reason: Refutation
% 0.20/0.47  
% 0.20/0.47  % (21675)Memory used [KB]: 10874
% 0.20/0.47  % (21675)Time elapsed: 0.065 s
% 0.20/0.47  % (21675)------------------------------
% 0.20/0.47  % (21675)------------------------------
% 0.20/0.47  % (21662)Success in time 0.115 s
%------------------------------------------------------------------------------
