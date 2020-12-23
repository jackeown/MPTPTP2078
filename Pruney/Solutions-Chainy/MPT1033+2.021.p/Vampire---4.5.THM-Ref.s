%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:45 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   72 (2270 expanded)
%              Number of leaves         :    6 ( 393 expanded)
%              Depth                    :   23
%              Number of atoms          :  227 (15116 expanded)
%              Number of equality atoms :   43 (2771 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f151,plain,(
    $false ),
    inference(subsumption_resolution,[],[f150,f146])).

fof(f146,plain,(
    r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f95,f140])).

fof(f140,plain,(
    k1_xboole_0 = sK3 ),
    inference(subsumption_resolution,[],[f126,f30])).

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

fof(f126,plain,
    ( k1_xboole_0 = sK3
    | v1_xboole_0(sK3) ),
    inference(backward_demodulation,[],[f57,f121])).

fof(f121,plain,(
    k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f118,f96])).

fof(f96,plain,(
    r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,sK2) ),
    inference(backward_demodulation,[],[f82,f87])).

fof(f87,plain,(
    k1_xboole_0 = sK0 ),
    inference(trivial_inequality_removal,[],[f86])).

fof(f86,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f18,f71])).

fof(f71,plain,(
    k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f65,f47])).

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

fof(f65,plain,
    ( ~ r2_relset_1(sK0,sK1,sK2,sK2)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f23,f58])).

fof(f58,plain,
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

fof(f82,plain,(
    r2_relset_1(sK0,k1_xboole_0,sK2,sK2) ),
    inference(backward_demodulation,[],[f47,f71])).

fof(f118,plain,
    ( ~ r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,sK2)
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f90,f59])).

fof(f59,plain,
    ( sK2 = sK3
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f56,f30])).

fof(f56,plain,
    ( v1_xboole_0(sK2)
    | sK2 = sK3 ),
    inference(resolution,[],[f55,f46])).

fof(f46,plain,
    ( ~ v1_xboole_0(sK1)
    | v1_xboole_0(sK2) ),
    inference(resolution,[],[f26,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0)
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

fof(f90,plain,(
    ~ r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,sK3) ),
    inference(backward_demodulation,[],[f74,f87])).

fof(f74,plain,(
    ~ r2_relset_1(sK0,k1_xboole_0,sK2,sK3) ),
    inference(backward_demodulation,[],[f23,f71])).

fof(f57,plain,
    ( v1_xboole_0(sK3)
    | sK2 = sK3 ),
    inference(resolution,[],[f55,f44])).

fof(f44,plain,
    ( ~ v1_xboole_0(sK1)
    | v1_xboole_0(sK3) ),
    inference(resolution,[],[f21,f31])).

fof(f95,plain,(
    r2_relset_1(k1_xboole_0,k1_xboole_0,sK3,sK3) ),
    inference(backward_demodulation,[],[f80,f87])).

fof(f80,plain,(
    r2_relset_1(sK0,k1_xboole_0,sK3,sK3) ),
    inference(backward_demodulation,[],[f45,f71])).

fof(f45,plain,(
    r2_relset_1(sK0,sK1,sK3,sK3) ),
    inference(resolution,[],[f21,f34])).

fof(f150,plain,(
    ~ r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f131,f140])).

fof(f131,plain,(
    ~ r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,sK3) ),
    inference(backward_demodulation,[],[f90,f121])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 10:41:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.21/0.47  % (32182)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.48  % (32172)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.48  % (32172)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f151,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(subsumption_resolution,[],[f150,f146])).
% 0.21/0.48  fof(f146,plain,(
% 0.21/0.48    r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 0.21/0.48    inference(backward_demodulation,[],[f95,f140])).
% 0.21/0.48  fof(f140,plain,(
% 0.21/0.48    k1_xboole_0 = sK3),
% 0.21/0.48    inference(subsumption_resolution,[],[f126,f30])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.21/0.48  fof(f126,plain,(
% 0.21/0.48    k1_xboole_0 = sK3 | v1_xboole_0(sK3)),
% 0.21/0.48    inference(backward_demodulation,[],[f57,f121])).
% 0.21/0.48  fof(f121,plain,(
% 0.21/0.48    k1_xboole_0 = sK2),
% 0.21/0.48    inference(subsumption_resolution,[],[f118,f96])).
% 0.21/0.48  fof(f96,plain,(
% 0.21/0.48    r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,sK2)),
% 0.21/0.48    inference(backward_demodulation,[],[f82,f87])).
% 0.21/0.48  fof(f87,plain,(
% 0.21/0.48    k1_xboole_0 = sK0),
% 0.21/0.48    inference(trivial_inequality_removal,[],[f86])).
% 0.21/0.48  fof(f86,plain,(
% 0.21/0.48    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0),
% 0.21/0.48    inference(superposition,[],[f18,f71])).
% 0.21/0.48  fof(f71,plain,(
% 0.21/0.48    k1_xboole_0 = sK1),
% 0.21/0.48    inference(subsumption_resolution,[],[f65,f47])).
% 0.21/0.48  fof(f47,plain,(
% 0.21/0.48    r2_relset_1(sK0,sK1,sK2,sK2)),
% 0.21/0.48    inference(resolution,[],[f26,f34])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f33])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 0.21/0.48    inference(equality_resolution,[],[f27])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X2 != X3 | r2_relset_1(X0,X1,X2,X3)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(flattening,[],[f10])).
% 0.21/0.48  fof(f10,plain,(
% 0.21/0.48    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.21/0.48    inference(ennf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.48    inference(cnf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,plain,(
% 0.21/0.48    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_partfun1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.21/0.48    inference(flattening,[],[f8])).
% 0.21/0.48  fof(f8,plain,(
% 0.21/0.48    ? [X0,X1,X2] : (? [X3] : (((~r2_relset_1(X0,X1,X2,X3) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_partfun1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.21/0.48    inference(ennf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_partfun1(X2,X3) => (r2_relset_1(X0,X1,X2,X3) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)))))),
% 0.21/0.48    inference(negated_conjecture,[],[f6])).
% 0.21/0.48  fof(f6,conjecture,(
% 0.21/0.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_partfun1(X2,X3) => (r2_relset_1(X0,X1,X2,X3) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_funct_2)).
% 0.21/0.48  fof(f65,plain,(
% 0.21/0.48    ~r2_relset_1(sK0,sK1,sK2,sK2) | k1_xboole_0 = sK1),
% 0.21/0.48    inference(superposition,[],[f23,f58])).
% 0.21/0.48  fof(f58,plain,(
% 0.21/0.48    sK2 = sK3 | k1_xboole_0 = sK1),
% 0.21/0.48    inference(resolution,[],[f55,f30])).
% 0.21/0.48  fof(f55,plain,(
% 0.21/0.48    v1_xboole_0(sK1) | sK2 = sK3),
% 0.21/0.48    inference(subsumption_resolution,[],[f54,f26])).
% 0.21/0.48  fof(f54,plain,(
% 0.21/0.48    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | sK2 = sK3 | v1_xboole_0(sK1)),
% 0.21/0.48    inference(resolution,[],[f53,f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.48    inference(cnf_transformation,[],[f9])).
% 0.21/0.48  fof(f53,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) | sK2 = sK3 | v1_xboole_0(sK1)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f52,f43])).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    v1_partfun1(sK2,sK0) | v1_xboole_0(sK1)),
% 0.21/0.48    inference(subsumption_resolution,[],[f42,f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    v1_funct_1(sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f9])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    ~v1_funct_1(sK2) | v1_xboole_0(sK1) | v1_partfun1(sK2,sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f41,f26])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | v1_xboole_0(sK1) | v1_partfun1(sK2,sK0)),
% 0.21/0.48    inference(resolution,[],[f25,f32])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | v1_xboole_0(X1) | v1_partfun1(X2,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.21/0.48    inference(flattening,[],[f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    v1_funct_2(sK2,sK0,sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f9])).
% 0.21/0.48  fof(f52,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) | ~v1_partfun1(sK2,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) | sK2 = sK3 | v1_xboole_0(sK1)) )),
% 0.21/0.48    inference(resolution,[],[f37,f40])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    v1_partfun1(sK3,sK0) | v1_xboole_0(sK1)),
% 0.21/0.48    inference(subsumption_resolution,[],[f39,f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    v1_funct_1(sK3)),
% 0.21/0.48    inference(cnf_transformation,[],[f9])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    ~v1_funct_1(sK3) | v1_xboole_0(sK1) | v1_partfun1(sK3,sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f38,f21])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | v1_xboole_0(sK1) | v1_partfun1(sK3,sK0)),
% 0.21/0.48    inference(resolution,[],[f20,f32])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    v1_funct_2(sK3,sK0,sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f9])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v1_partfun1(sK3,X0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_partfun1(sK2,X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sK2 = sK3) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f36,f24])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_partfun1(sK2,X0) | ~v1_partfun1(sK3,X0) | ~v1_funct_1(sK2) | sK2 = sK3) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f35,f19])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_partfun1(sK2,X0) | ~v1_partfun1(sK3,X0) | ~v1_funct_1(sK2) | sK2 = sK3) )),
% 0.21/0.48    inference(resolution,[],[f22,f29])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (~r1_partfun1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_partfun1(X2,X0) | ~v1_partfun1(X3,X0) | ~v1_funct_1(X2) | X2 = X3) )),
% 0.21/0.48    inference(cnf_transformation,[],[f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (! [X3] : (X2 = X3 | ~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.21/0.48    inference(flattening,[],[f12])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (! [X3] : ((X2 = X3 | (~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.21/0.48    inference(ennf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ((r1_partfun1(X2,X3) & v1_partfun1(X3,X0) & v1_partfun1(X2,X0)) => X2 = X3)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_partfun1)).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    r1_partfun1(sK2,sK3)),
% 0.21/0.48    inference(cnf_transformation,[],[f9])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ~r2_relset_1(sK0,sK1,sK2,sK3)),
% 0.21/0.48    inference(cnf_transformation,[],[f9])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    k1_xboole_0 != sK1 | k1_xboole_0 = sK0),
% 0.21/0.48    inference(cnf_transformation,[],[f9])).
% 0.21/0.48  fof(f82,plain,(
% 0.21/0.48    r2_relset_1(sK0,k1_xboole_0,sK2,sK2)),
% 0.21/0.48    inference(backward_demodulation,[],[f47,f71])).
% 0.21/0.48  fof(f118,plain,(
% 0.21/0.48    ~r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,sK2) | k1_xboole_0 = sK2),
% 0.21/0.48    inference(superposition,[],[f90,f59])).
% 0.21/0.48  fof(f59,plain,(
% 0.21/0.48    sK2 = sK3 | k1_xboole_0 = sK2),
% 0.21/0.48    inference(resolution,[],[f56,f30])).
% 0.21/0.48  fof(f56,plain,(
% 0.21/0.48    v1_xboole_0(sK2) | sK2 = sK3),
% 0.21/0.48    inference(resolution,[],[f55,f46])).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    ~v1_xboole_0(sK1) | v1_xboole_0(sK2)),
% 0.21/0.48    inference(resolution,[],[f26,f31])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0) | v1_xboole_0(X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).
% 0.21/0.48  fof(f90,plain,(
% 0.21/0.48    ~r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,sK3)),
% 0.21/0.48    inference(backward_demodulation,[],[f74,f87])).
% 0.21/0.48  fof(f74,plain,(
% 0.21/0.48    ~r2_relset_1(sK0,k1_xboole_0,sK2,sK3)),
% 0.21/0.48    inference(backward_demodulation,[],[f23,f71])).
% 0.21/0.48  fof(f57,plain,(
% 0.21/0.48    v1_xboole_0(sK3) | sK2 = sK3),
% 0.21/0.48    inference(resolution,[],[f55,f44])).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    ~v1_xboole_0(sK1) | v1_xboole_0(sK3)),
% 0.21/0.48    inference(resolution,[],[f21,f31])).
% 0.21/0.48  fof(f95,plain,(
% 0.21/0.48    r2_relset_1(k1_xboole_0,k1_xboole_0,sK3,sK3)),
% 0.21/0.48    inference(backward_demodulation,[],[f80,f87])).
% 0.21/0.48  fof(f80,plain,(
% 0.21/0.48    r2_relset_1(sK0,k1_xboole_0,sK3,sK3)),
% 0.21/0.48    inference(backward_demodulation,[],[f45,f71])).
% 0.21/0.48  fof(f45,plain,(
% 0.21/0.48    r2_relset_1(sK0,sK1,sK3,sK3)),
% 0.21/0.48    inference(resolution,[],[f21,f34])).
% 0.21/0.48  fof(f150,plain,(
% 0.21/0.48    ~r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 0.21/0.48    inference(forward_demodulation,[],[f131,f140])).
% 0.21/0.48  fof(f131,plain,(
% 0.21/0.48    ~r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,sK3)),
% 0.21/0.48    inference(backward_demodulation,[],[f90,f121])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (32172)------------------------------
% 0.21/0.48  % (32172)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (32172)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (32172)Memory used [KB]: 6140
% 0.21/0.48  % (32172)Time elapsed: 0.055 s
% 0.21/0.48  % (32172)------------------------------
% 0.21/0.48  % (32172)------------------------------
% 0.21/0.48  % (32166)Success in time 0.129 s
%------------------------------------------------------------------------------
