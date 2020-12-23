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
% DateTime   : Thu Dec  3 13:08:14 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 389 expanded)
%              Number of leaves         :    7 (  67 expanded)
%              Depth                    :   23
%              Number of atoms          :  342 (2761 expanded)
%              Number of equality atoms :   49 ( 296 expanded)
%              Maximal formula depth    :   16 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f117,plain,(
    $false ),
    inference(subsumption_resolution,[],[f116,f83])).

fof(f83,plain,(
    k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(backward_demodulation,[],[f59,f82])).

fof(f82,plain,(
    k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(subsumption_resolution,[],[f81,f29])).

fof(f29,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
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
    inference(flattening,[],[f10])).

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
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
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
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t193_funct_2)).

fof(f81,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(subsumption_resolution,[],[f80,f34])).

fof(f34,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f80,plain,
    ( v1_xboole_0(sK0)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(resolution,[],[f79,f26])).

fof(f26,plain,(
    v1_partfun1(sK4,sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ v1_partfun1(X1,X0)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
      | k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ) ),
    inference(resolution,[],[f78,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X1)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_partfun1)).

fof(f78,plain,
    ( v1_xboole_0(sK2)
    | k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(forward_demodulation,[],[f77,f66])).

fof(f66,plain,(
    k1_funct_1(sK4,k1_funct_1(sK3,sK5)) = k3_funct_2(sK0,sK2,sK4,k1_funct_1(sK3,sK5)) ),
    inference(resolution,[],[f65,f50])).

fof(f50,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK0)
      | k1_funct_1(sK4,X0) = k3_funct_2(sK0,sK2,sK4,X0) ) ),
    inference(subsumption_resolution,[],[f49,f34])).

fof(f49,plain,(
    ! [X0] :
      ( v1_xboole_0(sK0)
      | ~ m1_subset_1(X0,sK0)
      | k1_funct_1(sK4,X0) = k3_funct_2(sK0,sK2,sK4,X0) ) ),
    inference(subsumption_resolution,[],[f48,f45])).

fof(f45,plain,(
    v1_funct_2(sK4,sK0,sK2) ),
    inference(resolution,[],[f44,f29])).

fof(f44,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
      | v1_funct_2(sK4,sK0,X0) ) ),
    inference(subsumption_resolution,[],[f43,f28])).

fof(f28,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f11])).

fof(f43,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
      | ~ v1_funct_1(sK4)
      | v1_funct_2(sK4,sK0,X0) ) ),
    inference(resolution,[],[f38,f26])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_partfun1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( v1_partfun1(X2,X0)
       => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t131_funct_2)).

fof(f48,plain,(
    ! [X0] :
      ( ~ v1_funct_2(sK4,sK0,sK2)
      | v1_xboole_0(sK0)
      | ~ m1_subset_1(X0,sK0)
      | k1_funct_1(sK4,X0) = k3_funct_2(sK0,sK2,sK4,X0) ) ),
    inference(resolution,[],[f46,f29])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(sK4,X0,X1)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X2,X0)
      | k3_funct_2(X0,X1,sK4,X2) = k1_funct_1(sK4,X2) ) ),
    inference(resolution,[],[f41,f28])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | v1_xboole_0(X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,X0)
      | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

fof(f65,plain,(
    m1_subset_1(k1_funct_1(sK3,sK5),sK0) ),
    inference(subsumption_resolution,[],[f64,f33])).

fof(f33,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f64,plain,
    ( m1_subset_1(k1_funct_1(sK3,sK5),sK0)
    | v1_xboole_0(sK1) ),
    inference(subsumption_resolution,[],[f63,f25])).

fof(f25,plain,(
    m1_subset_1(sK5,sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f63,plain,
    ( m1_subset_1(k1_funct_1(sK3,sK5),sK0)
    | ~ m1_subset_1(sK5,sK1)
    | v1_xboole_0(sK1) ),
    inference(subsumption_resolution,[],[f62,f32])).

fof(f32,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f11])).

fof(f62,plain,
    ( m1_subset_1(k1_funct_1(sK3,sK5),sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK5,sK1)
    | v1_xboole_0(sK1) ),
    inference(subsumption_resolution,[],[f61,f31])).

fof(f31,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f61,plain,
    ( m1_subset_1(k1_funct_1(sK3,sK5),sK0)
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK5,sK1)
    | v1_xboole_0(sK1) ),
    inference(subsumption_resolution,[],[f60,f30])).

fof(f30,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f11])).

fof(f60,plain,
    ( m1_subset_1(k1_funct_1(sK3,sK5),sK0)
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK5,sK1)
    | v1_xboole_0(sK1) ),
    inference(superposition,[],[f40,f58])).

fof(f58,plain,(
    k3_funct_2(sK1,sK0,sK3,sK5) = k1_funct_1(sK3,sK5) ),
    inference(resolution,[],[f56,f25])).

fof(f56,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK1)
      | k1_funct_1(sK3,X0) = k3_funct_2(sK1,sK0,sK3,X0) ) ),
    inference(subsumption_resolution,[],[f55,f33])).

fof(f55,plain,(
    ! [X0] :
      ( v1_xboole_0(sK1)
      | ~ m1_subset_1(X0,sK1)
      | k1_funct_1(sK3,X0) = k3_funct_2(sK1,sK0,sK3,X0) ) ),
    inference(subsumption_resolution,[],[f54,f31])).

fof(f54,plain,(
    ! [X0] :
      ( ~ v1_funct_2(sK3,sK1,sK0)
      | v1_xboole_0(sK1)
      | ~ m1_subset_1(X0,sK1)
      | k1_funct_1(sK3,X0) = k3_funct_2(sK1,sK0,sK3,X0) ) ),
    inference(resolution,[],[f47,f32])).

fof(f47,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_2(sK3,X3,X4)
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X5,X3)
      | k3_funct_2(X3,X4,sK3,X5) = k1_funct_1(sK3,X5) ) ),
    inference(resolution,[],[f41,f30])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_funct_2)).

fof(f77,plain,
    ( v1_xboole_0(sK2)
    | k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) = k3_funct_2(sK0,sK2,sK4,k1_funct_1(sK3,sK5)) ),
    inference(resolution,[],[f75,f65])).

fof(f75,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK0)
      | v1_xboole_0(sK2)
      | k3_funct_2(sK0,sK2,sK4,X0) = k7_partfun1(sK2,sK4,X0) ) ),
    inference(subsumption_resolution,[],[f74,f45])).

fof(f74,plain,(
    ! [X0] :
      ( ~ v1_funct_2(sK4,sK0,sK2)
      | v1_xboole_0(sK2)
      | ~ m1_subset_1(X0,sK0)
      | k3_funct_2(sK0,sK2,sK4,X0) = k7_partfun1(sK2,sK4,X0) ) ),
    inference(subsumption_resolution,[],[f73,f34])).

fof(f73,plain,(
    ! [X0] :
      ( v1_xboole_0(sK0)
      | ~ v1_funct_2(sK4,sK0,sK2)
      | v1_xboole_0(sK2)
      | ~ m1_subset_1(X0,sK0)
      | k3_funct_2(sK0,sK2,sK4,X0) = k7_partfun1(sK2,sK4,X0) ) ),
    inference(resolution,[],[f51,f29])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | v1_xboole_0(X1)
      | ~ v1_funct_2(sK4,X1,X0)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X2,X1)
      | k3_funct_2(X1,X0,sK4,X2) = k7_partfun1(X0,sK4,X2) ) ),
    inference(resolution,[],[f39,f28])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,X0)
      | k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',ie1_funct_2)).

fof(f59,plain,(
    k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) ),
    inference(backward_demodulation,[],[f27,f58])).

fof(f27,plain,(
    k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) ),
    inference(cnf_transformation,[],[f11])).

fof(f116,plain,(
    k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(forward_demodulation,[],[f115,f58])).

fof(f115,plain,(
    k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) ),
    inference(resolution,[],[f113,f25])).

fof(f113,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK1)
      | k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,X0)) = k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) ) ),
    inference(subsumption_resolution,[],[f112,f33])).

% (28707)Refutation not found, incomplete strategy% (28707)------------------------------
% (28707)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f112,plain,(
    ! [X0] :
      ( v1_xboole_0(sK1)
      | ~ m1_subset_1(X0,sK1)
      | k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,X0)) = k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) ) ),
    inference(subsumption_resolution,[],[f111,f32])).

fof(f111,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | v1_xboole_0(sK1)
      | ~ m1_subset_1(X0,sK1)
      | k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,X0)) = k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) ) ),
    inference(subsumption_resolution,[],[f110,f30])).

fof(f110,plain,(
    ! [X0] :
      ( ~ v1_funct_1(sK3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | v1_xboole_0(sK1)
      | ~ m1_subset_1(X0,sK1)
      | k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,X0)) = k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) ) ),
    inference(resolution,[],[f109,f31])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X0,X1,sK0)
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X2,X1)
      | k3_funct_2(X1,sK2,k8_funct_2(X1,sK0,sK2,X0,sK4),X2) = k1_funct_1(sK4,k3_funct_2(X1,sK0,X0,X2)) ) ),
    inference(resolution,[],[f93,f29])).

fof(f93,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X2)))
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,X0,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X3,X0)
      | k3_funct_2(X0,X2,k8_funct_2(X0,sK0,X2,X1,sK4),X3) = k1_funct_1(sK4,k3_funct_2(X0,sK0,X1,X3)) ) ),
    inference(subsumption_resolution,[],[f92,f34])).

fof(f92,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_xboole_0(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,X0,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X2)))
      | ~ m1_subset_1(X3,X0)
      | v1_xboole_0(sK0)
      | k3_funct_2(X0,X2,k8_funct_2(X0,sK0,X2,X1,sK4),X3) = k1_funct_1(sK4,k3_funct_2(X0,sK0,X1,X3)) ) ),
    inference(subsumption_resolution,[],[f91,f28])).

fof(f91,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_xboole_0(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,X0,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
      | ~ v1_funct_1(sK4)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X2)))
      | ~ m1_subset_1(X3,X0)
      | v1_xboole_0(sK0)
      | k3_funct_2(X0,X2,k8_funct_2(X0,sK0,X2,X1,sK4),X3) = k1_funct_1(sK4,k3_funct_2(X0,sK0,X1,X3)) ) ),
    inference(resolution,[],[f35,f26])).

fof(f35,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_partfun1(X4,X0)
      | v1_xboole_0(X1)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X1,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
      | ~ m1_subset_1(X5,X1)
      | v1_xboole_0(X0)
      | k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) ) ),
    inference(cnf_transformation,[],[f13])).

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
    inference(flattening,[],[f12])).

fof(f12,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t192_funct_2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:22:36 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.22/0.51  % (28691)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.52  % (28707)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.52  % (28700)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.53  % (28699)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.53  % (28708)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.53  % (28692)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.53  % (28691)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.53  fof(f117,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(subsumption_resolution,[],[f116,f83])).
% 0.22/0.53  fof(f83,plain,(
% 0.22/0.53    k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))),
% 0.22/0.53    inference(backward_demodulation,[],[f59,f82])).
% 0.22/0.53  fof(f82,plain,(
% 0.22/0.53    k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))),
% 0.22/0.53    inference(subsumption_resolution,[],[f81,f29])).
% 0.22/0.53  fof(f29,plain,(
% 0.22/0.53    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.22/0.53    inference(cnf_transformation,[],[f11])).
% 0.22/0.53  fof(f11,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : (? [X2,X3] : (? [X4] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.22/0.53    inference(flattening,[],[f10])).
% 0.22/0.53  fof(f10,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : (? [X2,X3] : (? [X4] : (? [X5] : ((k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0)) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f9])).
% 0.22/0.53  fof(f9,negated_conjecture,(
% 0.22/0.53    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (v1_partfun1(X4,X0) => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5))))))))),
% 0.22/0.53    inference(negated_conjecture,[],[f8])).
% 0.22/0.53  fof(f8,conjecture,(
% 0.22/0.53    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (v1_partfun1(X4,X0) => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5))))))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t193_funct_2)).
% 0.22/0.53  fof(f81,plain,(
% 0.22/0.53    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))),
% 0.22/0.53    inference(subsumption_resolution,[],[f80,f34])).
% 0.22/0.53  fof(f34,plain,(
% 0.22/0.53    ~v1_xboole_0(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f11])).
% 0.22/0.53  fof(f80,plain,(
% 0.22/0.53    v1_xboole_0(sK0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))),
% 0.22/0.53    inference(resolution,[],[f79,f26])).
% 0.22/0.53  fof(f26,plain,(
% 0.22/0.53    v1_partfun1(sK4,sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f11])).
% 0.22/0.53  fof(f79,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~v1_partfun1(X1,X0) | v1_xboole_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) | k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))) )),
% 0.22/0.53    inference(resolution,[],[f78,f37])).
% 0.22/0.53  fof(f37,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~v1_xboole_0(X1) | v1_xboole_0(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_partfun1(X2,X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f16])).
% 0.22/0.53  fof(f16,plain,(
% 0.22/0.53    ! [X0,X1] : (! [X2] : (~v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X1) | v1_xboole_0(X0))),
% 0.22/0.53    inference(flattening,[],[f15])).
% 0.22/0.53  fof(f15,plain,(
% 0.22/0.53    ! [X0,X1] : (! [X2] : (~v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | (~v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f2])).
% 0.22/0.53  fof(f2,axiom,(
% 0.22/0.53    ! [X0,X1] : ((v1_xboole_0(X1) & ~v1_xboole_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ~v1_partfun1(X2,X0)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_partfun1)).
% 0.22/0.53  fof(f78,plain,(
% 0.22/0.53    v1_xboole_0(sK2) | k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))),
% 0.22/0.53    inference(forward_demodulation,[],[f77,f66])).
% 0.22/0.53  fof(f66,plain,(
% 0.22/0.53    k1_funct_1(sK4,k1_funct_1(sK3,sK5)) = k3_funct_2(sK0,sK2,sK4,k1_funct_1(sK3,sK5))),
% 0.22/0.53    inference(resolution,[],[f65,f50])).
% 0.22/0.53  fof(f50,plain,(
% 0.22/0.53    ( ! [X0] : (~m1_subset_1(X0,sK0) | k1_funct_1(sK4,X0) = k3_funct_2(sK0,sK2,sK4,X0)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f49,f34])).
% 0.22/0.53  fof(f49,plain,(
% 0.22/0.53    ( ! [X0] : (v1_xboole_0(sK0) | ~m1_subset_1(X0,sK0) | k1_funct_1(sK4,X0) = k3_funct_2(sK0,sK2,sK4,X0)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f48,f45])).
% 0.22/0.53  fof(f45,plain,(
% 0.22/0.53    v1_funct_2(sK4,sK0,sK2)),
% 0.22/0.53    inference(resolution,[],[f44,f29])).
% 0.22/0.53  fof(f44,plain,(
% 0.22/0.53    ( ! [X0] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) | v1_funct_2(sK4,sK0,X0)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f43,f28])).
% 0.22/0.53  fof(f28,plain,(
% 0.22/0.53    v1_funct_1(sK4)),
% 0.22/0.53    inference(cnf_transformation,[],[f11])).
% 0.22/0.53  fof(f43,plain,(
% 0.22/0.53    ( ! [X0] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) | ~v1_funct_1(sK4) | v1_funct_2(sK4,sK0,X0)) )),
% 0.22/0.53    inference(resolution,[],[f38,f26])).
% 0.22/0.53  fof(f38,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | v1_funct_2(X2,X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f18])).
% 0.22/0.53  fof(f18,plain,(
% 0.22/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.22/0.53    inference(flattening,[],[f17])).
% 0.22/0.53  fof(f17,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~v1_partfun1(X2,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.22/0.53    inference(ennf_transformation,[],[f6])).
% 0.22/0.53  fof(f6,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t131_funct_2)).
% 0.22/0.53  fof(f48,plain,(
% 0.22/0.53    ( ! [X0] : (~v1_funct_2(sK4,sK0,sK2) | v1_xboole_0(sK0) | ~m1_subset_1(X0,sK0) | k1_funct_1(sK4,X0) = k3_funct_2(sK0,sK2,sK4,X0)) )),
% 0.22/0.53    inference(resolution,[],[f46,f29])).
% 0.22/0.53  fof(f46,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK4,X0,X1) | v1_xboole_0(X0) | ~m1_subset_1(X2,X0) | k3_funct_2(X0,X1,sK4,X2) = k1_funct_1(sK4,X2)) )),
% 0.22/0.53    inference(resolution,[],[f41,f28])).
% 0.22/0.53  fof(f41,plain,(
% 0.22/0.53    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | v1_xboole_0(X0) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,X0) | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f24])).
% 0.22/0.53  fof(f24,plain,(
% 0.22/0.53    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 0.22/0.53    inference(flattening,[],[f23])).
% 0.22/0.53  fof(f23,plain,(
% 0.22/0.53    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f5])).
% 0.22/0.53  fof(f5,axiom,(
% 0.22/0.53    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).
% 0.22/0.53  fof(f65,plain,(
% 0.22/0.53    m1_subset_1(k1_funct_1(sK3,sK5),sK0)),
% 0.22/0.53    inference(subsumption_resolution,[],[f64,f33])).
% 0.22/0.53  fof(f33,plain,(
% 0.22/0.53    ~v1_xboole_0(sK1)),
% 0.22/0.53    inference(cnf_transformation,[],[f11])).
% 0.22/0.53  fof(f64,plain,(
% 0.22/0.53    m1_subset_1(k1_funct_1(sK3,sK5),sK0) | v1_xboole_0(sK1)),
% 0.22/0.53    inference(subsumption_resolution,[],[f63,f25])).
% 0.22/0.53  fof(f25,plain,(
% 0.22/0.53    m1_subset_1(sK5,sK1)),
% 0.22/0.53    inference(cnf_transformation,[],[f11])).
% 0.22/0.53  fof(f63,plain,(
% 0.22/0.53    m1_subset_1(k1_funct_1(sK3,sK5),sK0) | ~m1_subset_1(sK5,sK1) | v1_xboole_0(sK1)),
% 0.22/0.53    inference(subsumption_resolution,[],[f62,f32])).
% 0.22/0.53  fof(f32,plain,(
% 0.22/0.53    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.22/0.53    inference(cnf_transformation,[],[f11])).
% 0.22/0.53  fof(f62,plain,(
% 0.22/0.53    m1_subset_1(k1_funct_1(sK3,sK5),sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~m1_subset_1(sK5,sK1) | v1_xboole_0(sK1)),
% 0.22/0.53    inference(subsumption_resolution,[],[f61,f31])).
% 0.22/0.53  fof(f31,plain,(
% 0.22/0.53    v1_funct_2(sK3,sK1,sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f11])).
% 0.22/0.53  fof(f61,plain,(
% 0.22/0.53    m1_subset_1(k1_funct_1(sK3,sK5),sK0) | ~v1_funct_2(sK3,sK1,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~m1_subset_1(sK5,sK1) | v1_xboole_0(sK1)),
% 0.22/0.53    inference(subsumption_resolution,[],[f60,f30])).
% 0.22/0.53  fof(f30,plain,(
% 0.22/0.53    v1_funct_1(sK3)),
% 0.22/0.53    inference(cnf_transformation,[],[f11])).
% 0.22/0.53  fof(f60,plain,(
% 0.22/0.53    m1_subset_1(k1_funct_1(sK3,sK5),sK0) | ~v1_funct_1(sK3) | ~v1_funct_2(sK3,sK1,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~m1_subset_1(sK5,sK1) | v1_xboole_0(sK1)),
% 0.22/0.53    inference(superposition,[],[f40,f58])).
% 0.22/0.53  fof(f58,plain,(
% 0.22/0.53    k3_funct_2(sK1,sK0,sK3,sK5) = k1_funct_1(sK3,sK5)),
% 0.22/0.53    inference(resolution,[],[f56,f25])).
% 0.22/0.53  fof(f56,plain,(
% 0.22/0.53    ( ! [X0] : (~m1_subset_1(X0,sK1) | k1_funct_1(sK3,X0) = k3_funct_2(sK1,sK0,sK3,X0)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f55,f33])).
% 0.22/0.53  fof(f55,plain,(
% 0.22/0.53    ( ! [X0] : (v1_xboole_0(sK1) | ~m1_subset_1(X0,sK1) | k1_funct_1(sK3,X0) = k3_funct_2(sK1,sK0,sK3,X0)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f54,f31])).
% 0.22/0.53  fof(f54,plain,(
% 0.22/0.53    ( ! [X0] : (~v1_funct_2(sK3,sK1,sK0) | v1_xboole_0(sK1) | ~m1_subset_1(X0,sK1) | k1_funct_1(sK3,X0) = k3_funct_2(sK1,sK0,sK3,X0)) )),
% 0.22/0.53    inference(resolution,[],[f47,f32])).
% 0.22/0.53  fof(f47,plain,(
% 0.22/0.53    ( ! [X4,X5,X3] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_2(sK3,X3,X4) | v1_xboole_0(X3) | ~m1_subset_1(X5,X3) | k3_funct_2(X3,X4,sK3,X5) = k1_funct_1(sK3,X5)) )),
% 0.22/0.53    inference(resolution,[],[f41,f30])).
% 0.22/0.53  fof(f40,plain,(
% 0.22/0.53    ( ! [X2,X0,X3,X1] : (m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,X0) | v1_xboole_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f22])).
% 0.22/0.53  fof(f22,plain,(
% 0.22/0.53    ! [X0,X1,X2,X3] : (m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 0.22/0.53    inference(flattening,[],[f21])).
% 0.22/0.53  fof(f21,plain,(
% 0.22/0.53    ! [X0,X1,X2,X3] : (m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f3])).
% 0.22/0.53  fof(f3,axiom,(
% 0.22/0.53    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_funct_2)).
% 0.22/0.53  fof(f77,plain,(
% 0.22/0.53    v1_xboole_0(sK2) | k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) = k3_funct_2(sK0,sK2,sK4,k1_funct_1(sK3,sK5))),
% 0.22/0.53    inference(resolution,[],[f75,f65])).
% 0.22/0.53  fof(f75,plain,(
% 0.22/0.53    ( ! [X0] : (~m1_subset_1(X0,sK0) | v1_xboole_0(sK2) | k3_funct_2(sK0,sK2,sK4,X0) = k7_partfun1(sK2,sK4,X0)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f74,f45])).
% 0.22/0.53  fof(f74,plain,(
% 0.22/0.53    ( ! [X0] : (~v1_funct_2(sK4,sK0,sK2) | v1_xboole_0(sK2) | ~m1_subset_1(X0,sK0) | k3_funct_2(sK0,sK2,sK4,X0) = k7_partfun1(sK2,sK4,X0)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f73,f34])).
% 0.22/0.53  fof(f73,plain,(
% 0.22/0.53    ( ! [X0] : (v1_xboole_0(sK0) | ~v1_funct_2(sK4,sK0,sK2) | v1_xboole_0(sK2) | ~m1_subset_1(X0,sK0) | k3_funct_2(sK0,sK2,sK4,X0) = k7_partfun1(sK2,sK4,X0)) )),
% 0.22/0.53    inference(resolution,[],[f51,f29])).
% 0.22/0.53  fof(f51,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | v1_xboole_0(X1) | ~v1_funct_2(sK4,X1,X0) | v1_xboole_0(X0) | ~m1_subset_1(X2,X1) | k3_funct_2(X1,X0,sK4,X2) = k7_partfun1(X0,sK4,X2)) )),
% 0.22/0.53    inference(resolution,[],[f39,f28])).
% 0.22/0.53  fof(f39,plain,(
% 0.22/0.53    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | v1_xboole_0(X1) | v1_xboole_0(X0) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,X0) | k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f20])).
% 0.22/0.53  fof(f20,plain,(
% 0.22/0.53    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 0.22/0.53    inference(flattening,[],[f19])).
% 0.22/0.53  fof(f19,plain,(
% 0.22/0.53    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f4])).
% 0.22/0.53  fof(f4,axiom,(
% 0.22/0.53    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',ie1_funct_2)).
% 0.22/0.53  fof(f59,plain,(
% 0.22/0.53    k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5))),
% 0.22/0.53    inference(backward_demodulation,[],[f27,f58])).
% 0.22/0.53  fof(f27,plain,(
% 0.22/0.53    k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5))),
% 0.22/0.53    inference(cnf_transformation,[],[f11])).
% 0.22/0.53  fof(f116,plain,(
% 0.22/0.53    k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))),
% 0.22/0.53    inference(forward_demodulation,[],[f115,f58])).
% 0.22/0.53  fof(f115,plain,(
% 0.22/0.53    k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5))),
% 0.22/0.53    inference(resolution,[],[f113,f25])).
% 0.22/0.53  fof(f113,plain,(
% 0.22/0.53    ( ! [X0] : (~m1_subset_1(X0,sK1) | k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,X0)) = k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f112,f33])).
% 0.22/0.54  % (28707)Refutation not found, incomplete strategy% (28707)------------------------------
% 0.22/0.54  % (28707)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  fof(f112,plain,(
% 0.22/0.54    ( ! [X0] : (v1_xboole_0(sK1) | ~m1_subset_1(X0,sK1) | k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,X0)) = k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0)) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f111,f32])).
% 0.22/0.54  fof(f111,plain,(
% 0.22/0.54    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | v1_xboole_0(sK1) | ~m1_subset_1(X0,sK1) | k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,X0)) = k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0)) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f110,f30])).
% 0.22/0.54  fof(f110,plain,(
% 0.22/0.54    ( ! [X0] : (~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | v1_xboole_0(sK1) | ~m1_subset_1(X0,sK1) | k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,X0)) = k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0)) )),
% 0.22/0.54    inference(resolution,[],[f109,f31])).
% 0.22/0.54  fof(f109,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~v1_funct_2(X0,X1,sK0) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0))) | v1_xboole_0(X1) | ~m1_subset_1(X2,X1) | k3_funct_2(X1,sK2,k8_funct_2(X1,sK0,sK2,X0,sK4),X2) = k1_funct_1(sK4,k3_funct_2(X1,sK0,X0,X2))) )),
% 0.22/0.54    inference(resolution,[],[f93,f29])).
% 0.22/0.54  fof(f93,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X2))) | ~v1_funct_1(X1) | ~v1_funct_2(X1,X0,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) | v1_xboole_0(X0) | ~m1_subset_1(X3,X0) | k3_funct_2(X0,X2,k8_funct_2(X0,sK0,X2,X1,sK4),X3) = k1_funct_1(sK4,k3_funct_2(X0,sK0,X1,X3))) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f92,f34])).
% 0.22/0.54  fof(f92,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (v1_xboole_0(X0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,X0,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X2))) | ~m1_subset_1(X3,X0) | v1_xboole_0(sK0) | k3_funct_2(X0,X2,k8_funct_2(X0,sK0,X2,X1,sK4),X3) = k1_funct_1(sK4,k3_funct_2(X0,sK0,X1,X3))) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f91,f28])).
% 0.22/0.54  fof(f91,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (v1_xboole_0(X0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,X0,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) | ~v1_funct_1(sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X2))) | ~m1_subset_1(X3,X0) | v1_xboole_0(sK0) | k3_funct_2(X0,X2,k8_funct_2(X0,sK0,X2,X1,sK4),X3) = k1_funct_1(sK4,k3_funct_2(X0,sK0,X1,X3))) )),
% 0.22/0.54    inference(resolution,[],[f35,f26])).
% 0.22/0.54  fof(f35,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_partfun1(X4,X0) | v1_xboole_0(X1) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~m1_subset_1(X5,X1) | v1_xboole_0(X0) | k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f13])).
% 0.22/0.54  fof(f13,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (! [X2,X3] : (! [X4] : (! [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) | ~v1_partfun1(X4,X0) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.22/0.54    inference(flattening,[],[f12])).
% 0.22/0.54  fof(f12,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (! [X2,X3] : (! [X4] : (! [X5] : ((k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) | ~v1_partfun1(X4,X0)) | ~m1_subset_1(X5,X1)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f7])).
% 0.22/0.54  fof(f7,axiom,(
% 0.22/0.54    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (v1_partfun1(X4,X0) => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5))))))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t192_funct_2)).
% 0.22/0.54  % SZS output end Proof for theBenchmark
% 0.22/0.54  % (28691)------------------------------
% 0.22/0.54  % (28691)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (28691)Termination reason: Refutation
% 0.22/0.54  
% 0.22/0.54  % (28691)Memory used [KB]: 6268
% 0.22/0.54  % (28691)Time elapsed: 0.108 s
% 0.22/0.54  % (28691)------------------------------
% 0.22/0.54  % (28691)------------------------------
% 0.22/0.54  % (28689)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.55  % (28684)Success in time 0.178 s
%------------------------------------------------------------------------------
