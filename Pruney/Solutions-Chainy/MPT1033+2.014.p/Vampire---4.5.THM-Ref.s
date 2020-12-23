%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:44 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.30s
% Verified   : 
% Statistics : Number of formulae       :   72 (3035 expanded)
%              Number of leaves         :    6 ( 524 expanded)
%              Depth                    :   25
%              Number of atoms          :  230 (20222 expanded)
%              Number of equality atoms :   44 (3722 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f149,plain,(
    $false ),
    inference(subsumption_resolution,[],[f146,f128])).

fof(f128,plain,(
    r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f91,f118])).

fof(f118,plain,(
    k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f114,f91])).

fof(f114,plain,
    ( ~ r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,sK2)
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f85,f107])).

fof(f107,plain,
    ( sK2 = sK3
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f104,f30])).

fof(f30,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f104,plain,
    ( v1_xboole_0(sK2)
    | sK2 = sK3 ),
    inference(resolution,[],[f77,f82])).

fof(f82,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0(sK2) ),
    inference(backward_demodulation,[],[f46,f80])).

fof(f80,plain,(
    k1_xboole_0 = sK0 ),
    inference(trivial_inequality_removal,[],[f79])).

fof(f79,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f18,f66])).

fof(f66,plain,(
    k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f61,f47])).

fof(f47,plain,(
    r2_relset_1(sK0,sK1,sK2,sK2) ),
    inference(resolution,[],[f26,f34])).

fof(f34,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f33])).

fof(f33,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 != X3
      | r2_relset_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f26,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & r1_partfun1(X2,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & r1_partfun1(X2,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X3,X0,X1)
              & v1_funct_1(X3) )
           => ( r1_partfun1(X2,X3)
             => ( r2_relset_1(X0,X1,X2,X3)
                | ( k1_xboole_0 != X0
                  & k1_xboole_0 = X1 ) ) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( r1_partfun1(X2,X3)
           => ( r2_relset_1(X0,X1,X2,X3)
              | ( k1_xboole_0 != X0
                & k1_xboole_0 = X1 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_funct_2)).

fof(f61,plain,
    ( ~ r2_relset_1(sK0,sK1,sK2,sK2)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f23,f56])).

fof(f56,plain,
    ( sK2 = sK3
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f55,f30])).

fof(f55,plain,
    ( v1_xboole_0(sK1)
    | sK2 = sK3 ),
    inference(subsumption_resolution,[],[f54,f26])).

fof(f54,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | sK2 = sK3
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f53,f21])).

fof(f21,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f9])).

fof(f53,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
      | sK2 = sK3
      | v1_xboole_0(sK1) ) ),
    inference(subsumption_resolution,[],[f52,f43])).

fof(f43,plain,
    ( v1_partfun1(sK2,sK0)
    | v1_xboole_0(sK1) ),
    inference(subsumption_resolution,[],[f42,f24])).

fof(f24,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f42,plain,
    ( ~ v1_funct_1(sK2)
    | v1_xboole_0(sK1)
    | v1_partfun1(sK2,sK0) ),
    inference(subsumption_resolution,[],[f41,f26])).

fof(f41,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | v1_xboole_0(sK1)
    | v1_partfun1(sK2,sK0) ),
    inference(resolution,[],[f25,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_partfun1(X2,X0) ) ),
    inference(cnf_transformation,[],[f17])).

% (19258)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f25,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f52,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
      | ~ v1_partfun1(sK2,sK0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
      | sK2 = sK3
      | v1_xboole_0(sK1) ) ),
    inference(resolution,[],[f37,f40])).

fof(f40,plain,
    ( v1_partfun1(sK3,sK0)
    | v1_xboole_0(sK1) ),
    inference(subsumption_resolution,[],[f39,f19])).

fof(f19,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f9])).

fof(f39,plain,
    ( ~ v1_funct_1(sK3)
    | v1_xboole_0(sK1)
    | v1_partfun1(sK3,sK0) ),
    inference(subsumption_resolution,[],[f38,f21])).

fof(f38,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(sK1)
    | v1_partfun1(sK3,sK0) ),
    inference(resolution,[],[f20,f32])).

fof(f20,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ v1_partfun1(sK3,X0)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_partfun1(sK2,X0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sK2 = sK3 ) ),
    inference(subsumption_resolution,[],[f36,f24])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_partfun1(sK2,X0)
      | ~ v1_partfun1(sK3,X0)
      | ~ v1_funct_1(sK2)
      | sK2 = sK3 ) ),
    inference(subsumption_resolution,[],[f35,f19])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(sK3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_partfun1(sK2,X0)
      | ~ v1_partfun1(sK3,X0)
      | ~ v1_funct_1(sK2)
      | sK2 = sK3 ) ),
    inference(resolution,[],[f22,f29])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_partfun1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_partfun1(X2,X0)
      | ~ v1_partfun1(X3,X0)
      | ~ v1_funct_1(X2)
      | X2 = X3 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( X2 = X3
          | ~ r1_partfun1(X2,X3)
          | ~ v1_partfun1(X3,X0)
          | ~ v1_partfun1(X2,X0)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( X2 = X3
          | ~ r1_partfun1(X2,X3)
          | ~ v1_partfun1(X3,X0)
          | ~ v1_partfun1(X2,X0)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_1(X3) )
         => ( ( r1_partfun1(X2,X3)
              & v1_partfun1(X3,X0)
              & v1_partfun1(X2,X0) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_partfun1)).

fof(f22,plain,(
    r1_partfun1(sK2,sK3) ),
    inference(cnf_transformation,[],[f9])).

fof(f23,plain,(
    ~ r2_relset_1(sK0,sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f9])).

fof(f18,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f9])).

fof(f46,plain,
    ( ~ v1_xboole_0(sK0)
    | v1_xboole_0(sK2) ),
    inference(resolution,[],[f26,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0)
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_relset_1)).

fof(f77,plain,
    ( v1_xboole_0(k1_xboole_0)
    | sK2 = sK3 ),
    inference(backward_demodulation,[],[f55,f66])).

fof(f85,plain,(
    ~ r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,sK3) ),
    inference(backward_demodulation,[],[f69,f80])).

fof(f69,plain,(
    ~ r2_relset_1(sK0,k1_xboole_0,sK2,sK3) ),
    inference(backward_demodulation,[],[f23,f66])).

fof(f91,plain,(
    r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,sK2) ),
    inference(backward_demodulation,[],[f75,f80])).

fof(f75,plain,(
    r2_relset_1(sK0,k1_xboole_0,sK2,sK2) ),
    inference(backward_demodulation,[],[f47,f66])).

fof(f146,plain,(
    ~ r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f124,f138])).

fof(f138,plain,(
    k1_xboole_0 = sK3 ),
    inference(subsumption_resolution,[],[f130,f30])).

fof(f130,plain,
    ( k1_xboole_0 = sK3
    | v1_xboole_0(sK3) ),
    inference(backward_demodulation,[],[f105,f118])).

fof(f105,plain,
    ( v1_xboole_0(sK3)
    | sK2 = sK3 ),
    inference(resolution,[],[f77,f81])).

fof(f81,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0(sK3) ),
    inference(backward_demodulation,[],[f44,f80])).

fof(f44,plain,
    ( ~ v1_xboole_0(sK0)
    | v1_xboole_0(sK3) ),
    inference(resolution,[],[f21,f31])).

fof(f124,plain,(
    ~ r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,sK3) ),
    inference(backward_demodulation,[],[f85,f118])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n001.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:49:59 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.49  % (19245)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.49  % (19245)Refutation not found, incomplete strategy% (19245)------------------------------
% 0.21/0.49  % (19245)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (19245)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (19245)Memory used [KB]: 1663
% 0.21/0.49  % (19245)Time elapsed: 0.005 s
% 0.21/0.49  % (19245)------------------------------
% 0.21/0.49  % (19245)------------------------------
% 0.21/0.51  % (19244)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.52  % (19253)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.52  % (19240)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.52  % (19243)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.53  % (19249)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.53  % (19251)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.53  % (19252)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.53  % (19243)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f149,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(subsumption_resolution,[],[f146,f128])).
% 0.21/0.53  fof(f128,plain,(
% 0.21/0.53    r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 0.21/0.53    inference(backward_demodulation,[],[f91,f118])).
% 0.21/0.53  fof(f118,plain,(
% 0.21/0.53    k1_xboole_0 = sK2),
% 0.21/0.53    inference(subsumption_resolution,[],[f114,f91])).
% 0.21/0.53  fof(f114,plain,(
% 0.21/0.53    ~r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,sK2) | k1_xboole_0 = sK2),
% 0.21/0.53    inference(superposition,[],[f85,f107])).
% 0.21/0.53  fof(f107,plain,(
% 0.21/0.53    sK2 = sK3 | k1_xboole_0 = sK2),
% 0.21/0.53    inference(resolution,[],[f104,f30])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f14])).
% 0.21/0.53  fof(f14,plain,(
% 0.21/0.53    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.21/0.53  fof(f104,plain,(
% 0.21/0.53    v1_xboole_0(sK2) | sK2 = sK3),
% 0.21/0.53    inference(resolution,[],[f77,f82])).
% 0.21/0.53  fof(f82,plain,(
% 0.21/0.53    ~v1_xboole_0(k1_xboole_0) | v1_xboole_0(sK2)),
% 0.21/0.53    inference(backward_demodulation,[],[f46,f80])).
% 0.21/0.53  fof(f80,plain,(
% 0.21/0.53    k1_xboole_0 = sK0),
% 0.21/0.53    inference(trivial_inequality_removal,[],[f79])).
% 0.21/0.53  fof(f79,plain,(
% 0.21/0.53    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0),
% 0.21/0.53    inference(superposition,[],[f18,f66])).
% 0.21/0.53  fof(f66,plain,(
% 0.21/0.53    k1_xboole_0 = sK1),
% 0.21/0.53    inference(subsumption_resolution,[],[f61,f47])).
% 0.21/0.53  fof(f47,plain,(
% 0.21/0.53    r2_relset_1(sK0,sK1,sK2,sK2)),
% 0.21/0.53    inference(resolution,[],[f26,f34])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f33])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 0.21/0.53    inference(equality_resolution,[],[f27])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X2 != X3 | r2_relset_1(X0,X1,X2,X3)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f11])).
% 0.21/0.53  fof(f11,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.53    inference(flattening,[],[f10])).
% 0.21/0.53  fof(f10,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.30/0.53    inference(ennf_transformation,[],[f3])).
% 1.30/0.53  fof(f3,axiom,(
% 1.30/0.53    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.30/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.30/0.53  fof(f26,plain,(
% 1.30/0.53    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.30/0.53    inference(cnf_transformation,[],[f9])).
% 1.30/0.53  fof(f9,plain,(
% 1.30/0.53    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_partfun1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.30/0.53    inference(flattening,[],[f8])).
% 1.30/0.53  fof(f8,plain,(
% 1.30/0.53    ? [X0,X1,X2] : (? [X3] : (((~r2_relset_1(X0,X1,X2,X3) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_partfun1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.30/0.53    inference(ennf_transformation,[],[f7])).
% 1.30/0.53  fof(f7,negated_conjecture,(
% 1.30/0.53    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_partfun1(X2,X3) => (r2_relset_1(X0,X1,X2,X3) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)))))),
% 1.30/0.53    inference(negated_conjecture,[],[f6])).
% 1.30/0.53  fof(f6,conjecture,(
% 1.30/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_partfun1(X2,X3) => (r2_relset_1(X0,X1,X2,X3) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)))))),
% 1.30/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_funct_2)).
% 1.30/0.53  fof(f61,plain,(
% 1.30/0.53    ~r2_relset_1(sK0,sK1,sK2,sK2) | k1_xboole_0 = sK1),
% 1.30/0.53    inference(superposition,[],[f23,f56])).
% 1.30/0.53  fof(f56,plain,(
% 1.30/0.53    sK2 = sK3 | k1_xboole_0 = sK1),
% 1.30/0.53    inference(resolution,[],[f55,f30])).
% 1.30/0.53  fof(f55,plain,(
% 1.30/0.53    v1_xboole_0(sK1) | sK2 = sK3),
% 1.30/0.53    inference(subsumption_resolution,[],[f54,f26])).
% 1.30/0.53  fof(f54,plain,(
% 1.30/0.53    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | sK2 = sK3 | v1_xboole_0(sK1)),
% 1.30/0.53    inference(resolution,[],[f53,f21])).
% 1.30/0.53  fof(f21,plain,(
% 1.30/0.53    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.30/0.53    inference(cnf_transformation,[],[f9])).
% 1.30/0.53  fof(f53,plain,(
% 1.30/0.53    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) | sK2 = sK3 | v1_xboole_0(sK1)) )),
% 1.30/0.53    inference(subsumption_resolution,[],[f52,f43])).
% 1.30/0.53  fof(f43,plain,(
% 1.30/0.53    v1_partfun1(sK2,sK0) | v1_xboole_0(sK1)),
% 1.30/0.53    inference(subsumption_resolution,[],[f42,f24])).
% 1.30/0.53  fof(f24,plain,(
% 1.30/0.53    v1_funct_1(sK2)),
% 1.30/0.53    inference(cnf_transformation,[],[f9])).
% 1.30/0.53  fof(f42,plain,(
% 1.30/0.53    ~v1_funct_1(sK2) | v1_xboole_0(sK1) | v1_partfun1(sK2,sK0)),
% 1.30/0.53    inference(subsumption_resolution,[],[f41,f26])).
% 1.30/0.53  fof(f41,plain,(
% 1.30/0.53    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | v1_xboole_0(sK1) | v1_partfun1(sK2,sK0)),
% 1.30/0.53    inference(resolution,[],[f25,f32])).
% 1.30/0.53  fof(f32,plain,(
% 1.30/0.53    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | v1_xboole_0(X1) | v1_partfun1(X2,X0)) )),
% 1.30/0.53    inference(cnf_transformation,[],[f17])).
% 1.30/0.53  % (19258)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.30/0.53  fof(f17,plain,(
% 1.30/0.53    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 1.30/0.53    inference(flattening,[],[f16])).
% 1.30/0.53  fof(f16,plain,(
% 1.30/0.53    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 1.30/0.53    inference(ennf_transformation,[],[f4])).
% 1.30/0.53  fof(f4,axiom,(
% 1.30/0.53    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 1.30/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).
% 1.30/0.53  fof(f25,plain,(
% 1.30/0.53    v1_funct_2(sK2,sK0,sK1)),
% 1.30/0.53    inference(cnf_transformation,[],[f9])).
% 1.30/0.53  fof(f52,plain,(
% 1.30/0.53    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) | ~v1_partfun1(sK2,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) | sK2 = sK3 | v1_xboole_0(sK1)) )),
% 1.30/0.53    inference(resolution,[],[f37,f40])).
% 1.30/0.53  fof(f40,plain,(
% 1.30/0.53    v1_partfun1(sK3,sK0) | v1_xboole_0(sK1)),
% 1.30/0.53    inference(subsumption_resolution,[],[f39,f19])).
% 1.30/0.53  fof(f19,plain,(
% 1.30/0.53    v1_funct_1(sK3)),
% 1.30/0.53    inference(cnf_transformation,[],[f9])).
% 1.30/0.53  fof(f39,plain,(
% 1.30/0.53    ~v1_funct_1(sK3) | v1_xboole_0(sK1) | v1_partfun1(sK3,sK0)),
% 1.30/0.53    inference(subsumption_resolution,[],[f38,f21])).
% 1.30/0.53  fof(f38,plain,(
% 1.30/0.53    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | v1_xboole_0(sK1) | v1_partfun1(sK3,sK0)),
% 1.30/0.53    inference(resolution,[],[f20,f32])).
% 1.30/0.53  fof(f20,plain,(
% 1.30/0.53    v1_funct_2(sK3,sK0,sK1)),
% 1.30/0.53    inference(cnf_transformation,[],[f9])).
% 1.30/0.53  fof(f37,plain,(
% 1.30/0.53    ( ! [X0,X1] : (~v1_partfun1(sK3,X0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_partfun1(sK2,X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sK2 = sK3) )),
% 1.30/0.53    inference(subsumption_resolution,[],[f36,f24])).
% 1.30/0.53  fof(f36,plain,(
% 1.30/0.53    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_partfun1(sK2,X0) | ~v1_partfun1(sK3,X0) | ~v1_funct_1(sK2) | sK2 = sK3) )),
% 1.30/0.53    inference(subsumption_resolution,[],[f35,f19])).
% 1.30/0.53  fof(f35,plain,(
% 1.30/0.53    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_partfun1(sK2,X0) | ~v1_partfun1(sK3,X0) | ~v1_funct_1(sK2) | sK2 = sK3) )),
% 1.30/0.53    inference(resolution,[],[f22,f29])).
% 1.30/0.53  fof(f29,plain,(
% 1.30/0.53    ( ! [X2,X0,X3,X1] : (~r1_partfun1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_partfun1(X2,X0) | ~v1_partfun1(X3,X0) | ~v1_funct_1(X2) | X2 = X3) )),
% 1.30/0.53    inference(cnf_transformation,[],[f13])).
% 1.30/0.53  fof(f13,plain,(
% 1.30/0.53    ! [X0,X1,X2] : (! [X3] : (X2 = X3 | ~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.30/0.53    inference(flattening,[],[f12])).
% 1.30/0.53  fof(f12,plain,(
% 1.30/0.53    ! [X0,X1,X2] : (! [X3] : ((X2 = X3 | (~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.30/0.53    inference(ennf_transformation,[],[f5])).
% 1.30/0.53  fof(f5,axiom,(
% 1.30/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ((r1_partfun1(X2,X3) & v1_partfun1(X3,X0) & v1_partfun1(X2,X0)) => X2 = X3)))),
% 1.30/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_partfun1)).
% 1.30/0.53  fof(f22,plain,(
% 1.30/0.53    r1_partfun1(sK2,sK3)),
% 1.30/0.53    inference(cnf_transformation,[],[f9])).
% 1.30/0.53  fof(f23,plain,(
% 1.30/0.53    ~r2_relset_1(sK0,sK1,sK2,sK3)),
% 1.30/0.53    inference(cnf_transformation,[],[f9])).
% 1.30/0.53  fof(f18,plain,(
% 1.30/0.53    k1_xboole_0 != sK1 | k1_xboole_0 = sK0),
% 1.30/0.53    inference(cnf_transformation,[],[f9])).
% 1.30/0.53  fof(f46,plain,(
% 1.30/0.53    ~v1_xboole_0(sK0) | v1_xboole_0(sK2)),
% 1.30/0.53    inference(resolution,[],[f26,f31])).
% 1.30/0.53  fof(f31,plain,(
% 1.30/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0) | v1_xboole_0(X2)) )),
% 1.30/0.53    inference(cnf_transformation,[],[f15])).
% 1.30/0.53  fof(f15,plain,(
% 1.30/0.53    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 1.30/0.53    inference(ennf_transformation,[],[f2])).
% 1.30/0.53  fof(f2,axiom,(
% 1.30/0.53    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_xboole_0(X2)))),
% 1.30/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_relset_1)).
% 1.30/0.53  fof(f77,plain,(
% 1.30/0.53    v1_xboole_0(k1_xboole_0) | sK2 = sK3),
% 1.30/0.53    inference(backward_demodulation,[],[f55,f66])).
% 1.30/0.53  fof(f85,plain,(
% 1.30/0.53    ~r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,sK3)),
% 1.30/0.53    inference(backward_demodulation,[],[f69,f80])).
% 1.30/0.53  fof(f69,plain,(
% 1.30/0.53    ~r2_relset_1(sK0,k1_xboole_0,sK2,sK3)),
% 1.30/0.53    inference(backward_demodulation,[],[f23,f66])).
% 1.30/0.53  fof(f91,plain,(
% 1.30/0.53    r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,sK2)),
% 1.30/0.53    inference(backward_demodulation,[],[f75,f80])).
% 1.30/0.53  fof(f75,plain,(
% 1.30/0.53    r2_relset_1(sK0,k1_xboole_0,sK2,sK2)),
% 1.30/0.53    inference(backward_demodulation,[],[f47,f66])).
% 1.30/0.53  fof(f146,plain,(
% 1.30/0.53    ~r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 1.30/0.53    inference(backward_demodulation,[],[f124,f138])).
% 1.30/0.53  fof(f138,plain,(
% 1.30/0.53    k1_xboole_0 = sK3),
% 1.30/0.53    inference(subsumption_resolution,[],[f130,f30])).
% 1.30/0.53  fof(f130,plain,(
% 1.30/0.53    k1_xboole_0 = sK3 | v1_xboole_0(sK3)),
% 1.30/0.53    inference(backward_demodulation,[],[f105,f118])).
% 1.30/0.53  fof(f105,plain,(
% 1.30/0.53    v1_xboole_0(sK3) | sK2 = sK3),
% 1.30/0.53    inference(resolution,[],[f77,f81])).
% 1.30/0.53  fof(f81,plain,(
% 1.30/0.53    ~v1_xboole_0(k1_xboole_0) | v1_xboole_0(sK3)),
% 1.30/0.53    inference(backward_demodulation,[],[f44,f80])).
% 1.30/0.53  fof(f44,plain,(
% 1.30/0.53    ~v1_xboole_0(sK0) | v1_xboole_0(sK3)),
% 1.30/0.53    inference(resolution,[],[f21,f31])).
% 1.30/0.53  fof(f124,plain,(
% 1.30/0.53    ~r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,sK3)),
% 1.30/0.53    inference(backward_demodulation,[],[f85,f118])).
% 1.30/0.53  % SZS output end Proof for theBenchmark
% 1.30/0.53  % (19243)------------------------------
% 1.30/0.53  % (19243)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.53  % (19243)Termination reason: Refutation
% 1.30/0.53  
% 1.30/0.53  % (19243)Memory used [KB]: 6140
% 1.30/0.53  % (19243)Time elapsed: 0.103 s
% 1.30/0.53  % (19243)------------------------------
% 1.30/0.53  % (19243)------------------------------
% 1.30/0.53  % (19239)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 1.30/0.54  % (19237)Success in time 0.173 s
%------------------------------------------------------------------------------
