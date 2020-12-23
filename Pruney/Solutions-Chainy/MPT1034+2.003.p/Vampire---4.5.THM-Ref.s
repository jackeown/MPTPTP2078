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
% DateTime   : Thu Dec  3 13:06:50 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   71 (2068 expanded)
%              Number of leaves         :    8 ( 632 expanded)
%              Depth                    :   26
%              Number of atoms          :  253 (14850 expanded)
%              Number of equality atoms :   37 ( 349 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f179,plain,(
    $false ),
    inference(subsumption_resolution,[],[f178,f135])).

fof(f135,plain,(
    r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f77,f121])).

fof(f121,plain,(
    k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f107,f39])).

fof(f39,plain,(
    r2_relset_1(sK0,sK0,sK1,sK1) ),
    inference(resolution,[],[f38,f24])).

fof(f24,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ~ r2_relset_1(sK0,sK0,sK1,sK2)
    & r1_partfun1(sK1,sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v1_funct_2(sK2,sK0,sK0)
    & v1_funct_1(sK2)
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f19,f18])).

fof(f18,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r2_relset_1(X0,X0,X1,X2)
            & r1_partfun1(X1,X2)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v1_funct_2(X2,X0,X0)
            & v1_funct_1(X2) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
   => ( ? [X2] :
          ( ~ r2_relset_1(sK0,sK0,sK1,X2)
          & r1_partfun1(sK1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
          & v1_funct_2(X2,sK0,sK0)
          & v1_funct_1(X2) )
      & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v1_funct_2(sK1,sK0,sK0)
      & v1_funct_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X2] :
        ( ~ r2_relset_1(sK0,sK0,sK1,X2)
        & r1_partfun1(sK1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        & v1_funct_2(X2,sK0,sK0)
        & v1_funct_1(X2) )
   => ( ~ r2_relset_1(sK0,sK0,sK1,sK2)
      & r1_partfun1(sK1,sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v1_funct_2(sK2,sK0,sK0)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X1,X2)
          & r1_partfun1(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X1,X2)
          & r1_partfun1(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ! [X2] :
            ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v1_funct_2(X2,X0,X0)
              & v1_funct_1(X2) )
           => ( r1_partfun1(X1,X2)
             => r2_relset_1(X0,X0,X1,X2) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v1_funct_2(X2,X0,X0)
            & v1_funct_1(X2) )
         => ( r1_partfun1(X1,X2)
           => r2_relset_1(X0,X0,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_funct_2)).

fof(f38,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f37])).

fof(f37,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f107,plain,
    ( ~ r2_relset_1(sK0,sK0,sK1,sK1)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f29,f100])).

fof(f100,plain,
    ( sK1 = sK2
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f97,f30])).

fof(f30,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f97,plain,
    ( v1_xboole_0(sK1)
    | sK1 = sK2 ),
    inference(resolution,[],[f96,f73])).

fof(f73,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(superposition,[],[f24,f71])).

fof(f71,plain,(
    k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f64,f39])).

fof(f64,plain,
    ( ~ r2_relset_1(sK0,sK0,sK1,sK1)
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f29,f59])).

fof(f59,plain,
    ( sK1 = sK2
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f57,f30])).

fof(f57,plain,
    ( v1_xboole_0(sK0)
    | sK1 = sK2 ),
    inference(subsumption_resolution,[],[f56,f44])).

fof(f44,plain,
    ( v1_partfun1(sK1,sK0)
    | v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f43,f23])).

fof(f23,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f43,plain,
    ( v1_partfun1(sK1,sK0)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f41,f24])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_partfun1(sK1,X0)
      | ~ v1_funct_2(sK1,X0,X1)
      | v1_xboole_0(X1) ) ),
    inference(resolution,[],[f32,f22])).

fof(f22,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | v1_partfun1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f56,plain,
    ( ~ v1_partfun1(sK1,sK0)
    | sK1 = sK2
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f55,f46])).

fof(f46,plain,
    ( v1_partfun1(sK2,sK0)
    | v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f45,f26])).

fof(f26,plain,(
    v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f45,plain,
    ( v1_partfun1(sK2,sK0)
    | ~ v1_funct_2(sK2,sK0,sK0)
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f42,f27])).

fof(f27,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f20])).

fof(f42,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | v1_partfun1(sK2,X2)
      | ~ v1_funct_2(sK2,X2,X3)
      | v1_xboole_0(X3) ) ),
    inference(resolution,[],[f32,f25])).

fof(f25,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f55,plain,
    ( ~ v1_partfun1(sK2,sK0)
    | ~ v1_partfun1(sK1,sK0)
    | sK1 = sK2 ),
    inference(subsumption_resolution,[],[f54,f24])).

fof(f54,plain,
    ( ~ v1_partfun1(sK2,sK0)
    | ~ v1_partfun1(sK1,sK0)
    | sK1 = sK2
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f53,f27])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_partfun1(sK2,X0)
      | ~ v1_partfun1(sK1,X0)
      | sK1 = sK2
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(subsumption_resolution,[],[f52,f22])).

fof(f52,plain,(
    ! [X0,X1] :
      ( sK1 = sK2
      | ~ v1_partfun1(sK2,X0)
      | ~ v1_partfun1(sK1,X0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(sK1) ) ),
    inference(subsumption_resolution,[],[f51,f25])).

fof(f51,plain,(
    ! [X0,X1] :
      ( sK1 = sK2
      | ~ v1_partfun1(sK2,X0)
      | ~ v1_partfun1(sK1,X0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(sK2)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(sK1) ) ),
    inference(resolution,[],[f34,f28])).

fof(f28,plain,(
    r1_partfun1(sK1,sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_partfun1(X2,X3)
      | X2 = X3
      | ~ v1_partfun1(X3,X0)
      | ~ v1_partfun1(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f14,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_partfun1)).

fof(f96,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
      | sK1 = sK2
      | v1_xboole_0(X0) ) ),
    inference(forward_demodulation,[],[f58,f71])).

fof(f58,plain,(
    ! [X0,X1] :
      ( sK1 = sK2
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f57,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

fof(f29,plain,(
    ~ r2_relset_1(sK0,sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f77,plain,(
    r2_relset_1(k1_xboole_0,k1_xboole_0,sK1,sK1) ),
    inference(superposition,[],[f39,f71])).

fof(f178,plain,(
    ~ r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f177,f71])).

fof(f177,plain,(
    ~ r2_relset_1(sK0,sK0,k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f158,f121])).

fof(f158,plain,(
    ~ r2_relset_1(sK0,sK0,sK1,k1_xboole_0) ),
    inference(superposition,[],[f29,f153])).

fof(f153,plain,(
    k1_xboole_0 = sK2 ),
    inference(duplicate_literal_removal,[],[f152])).

fof(f152,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK2 ),
    inference(forward_demodulation,[],[f102,f121])).

fof(f102,plain,
    ( sK1 = sK2
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f98,f30])).

fof(f98,plain,
    ( v1_xboole_0(sK2)
    | sK1 = sK2 ),
    inference(resolution,[],[f96,f75])).

fof(f75,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(superposition,[],[f27,f71])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:40:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.46  % (27558)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.19/0.46  % (27558)Refutation not found, incomplete strategy% (27558)------------------------------
% 0.19/0.46  % (27558)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.46  % (27558)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.46  
% 0.19/0.46  % (27558)Memory used [KB]: 6140
% 0.19/0.46  % (27558)Time elapsed: 0.075 s
% 0.19/0.46  % (27558)------------------------------
% 0.19/0.46  % (27558)------------------------------
% 0.19/0.46  % (27562)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.19/0.47  % (27574)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.19/0.48  % (27570)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.19/0.48  % (27557)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.19/0.48  % (27566)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.19/0.48  % (27574)Refutation found. Thanks to Tanya!
% 0.19/0.48  % SZS status Theorem for theBenchmark
% 0.19/0.48  % SZS output start Proof for theBenchmark
% 0.19/0.48  fof(f179,plain,(
% 0.19/0.48    $false),
% 0.19/0.48    inference(subsumption_resolution,[],[f178,f135])).
% 0.19/0.48  fof(f135,plain,(
% 0.19/0.48    r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 0.19/0.48    inference(superposition,[],[f77,f121])).
% 0.19/0.48  fof(f121,plain,(
% 0.19/0.48    k1_xboole_0 = sK1),
% 0.19/0.48    inference(subsumption_resolution,[],[f107,f39])).
% 0.19/0.48  fof(f39,plain,(
% 0.19/0.48    r2_relset_1(sK0,sK0,sK1,sK1)),
% 0.19/0.48    inference(resolution,[],[f38,f24])).
% 0.19/0.48  fof(f24,plain,(
% 0.19/0.48    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.19/0.48    inference(cnf_transformation,[],[f20])).
% 0.19/0.48  fof(f20,plain,(
% 0.19/0.48    (~r2_relset_1(sK0,sK0,sK1,sK2) & r1_partfun1(sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 0.19/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f19,f18])).
% 0.19/0.48  fof(f18,plain,(
% 0.19/0.48    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X1,X2) & r1_partfun1(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (? [X2] : (~r2_relset_1(sK0,sK0,sK1,X2) & r1_partfun1(sK1,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(X2,sK0,sK0) & v1_funct_1(X2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 0.19/0.48    introduced(choice_axiom,[])).
% 0.19/0.48  fof(f19,plain,(
% 0.19/0.48    ? [X2] : (~r2_relset_1(sK0,sK0,sK1,X2) & r1_partfun1(sK1,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(X2,sK0,sK0) & v1_funct_1(X2)) => (~r2_relset_1(sK0,sK0,sK1,sK2) & r1_partfun1(sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2))),
% 0.19/0.48    introduced(choice_axiom,[])).
% 0.19/0.48  fof(f9,plain,(
% 0.19/0.48    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X1,X2) & r1_partfun1(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 0.19/0.48    inference(flattening,[],[f8])).
% 0.19/0.48  fof(f8,plain,(
% 0.19/0.48    ? [X0,X1] : (? [X2] : ((~r2_relset_1(X0,X0,X1,X2) & r1_partfun1(X1,X2)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 0.19/0.48    inference(ennf_transformation,[],[f7])).
% 0.19/0.48  fof(f7,negated_conjecture,(
% 0.19/0.48    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r1_partfun1(X1,X2) => r2_relset_1(X0,X0,X1,X2))))),
% 0.19/0.48    inference(negated_conjecture,[],[f6])).
% 0.19/0.48  fof(f6,conjecture,(
% 0.19/0.48    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r1_partfun1(X1,X2) => r2_relset_1(X0,X0,X1,X2))))),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_funct_2)).
% 0.19/0.48  fof(f38,plain,(
% 0.19/0.48    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 0.19/0.48    inference(duplicate_literal_removal,[],[f37])).
% 0.19/0.48  fof(f37,plain,(
% 0.19/0.48    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.19/0.48    inference(equality_resolution,[],[f36])).
% 0.19/0.48  fof(f36,plain,(
% 0.19/0.48    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.19/0.48    inference(cnf_transformation,[],[f21])).
% 0.19/0.48  fof(f21,plain,(
% 0.19/0.48    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.48    inference(nnf_transformation,[],[f17])).
% 0.19/0.48  fof(f17,plain,(
% 0.19/0.48    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.48    inference(flattening,[],[f16])).
% 0.19/0.48  fof(f16,plain,(
% 0.19/0.48    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.19/0.48    inference(ennf_transformation,[],[f3])).
% 0.19/0.48  fof(f3,axiom,(
% 0.19/0.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 0.19/0.48  fof(f107,plain,(
% 0.19/0.48    ~r2_relset_1(sK0,sK0,sK1,sK1) | k1_xboole_0 = sK1),
% 0.19/0.48    inference(superposition,[],[f29,f100])).
% 0.19/0.48  fof(f100,plain,(
% 0.19/0.48    sK1 = sK2 | k1_xboole_0 = sK1),
% 0.19/0.48    inference(resolution,[],[f97,f30])).
% 0.19/0.48  fof(f30,plain,(
% 0.19/0.48    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.19/0.48    inference(cnf_transformation,[],[f10])).
% 0.19/0.48  fof(f10,plain,(
% 0.19/0.48    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.19/0.48    inference(ennf_transformation,[],[f1])).
% 0.19/0.48  fof(f1,axiom,(
% 0.19/0.48    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.19/0.48  fof(f97,plain,(
% 0.19/0.48    v1_xboole_0(sK1) | sK1 = sK2),
% 0.19/0.48    inference(resolution,[],[f96,f73])).
% 0.19/0.48  fof(f73,plain,(
% 0.19/0.48    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 0.19/0.48    inference(superposition,[],[f24,f71])).
% 0.19/0.48  fof(f71,plain,(
% 0.19/0.48    k1_xboole_0 = sK0),
% 0.19/0.48    inference(subsumption_resolution,[],[f64,f39])).
% 0.19/0.48  fof(f64,plain,(
% 0.19/0.48    ~r2_relset_1(sK0,sK0,sK1,sK1) | k1_xboole_0 = sK0),
% 0.19/0.48    inference(superposition,[],[f29,f59])).
% 0.19/0.48  fof(f59,plain,(
% 0.19/0.48    sK1 = sK2 | k1_xboole_0 = sK0),
% 0.19/0.48    inference(resolution,[],[f57,f30])).
% 0.19/0.48  fof(f57,plain,(
% 0.19/0.48    v1_xboole_0(sK0) | sK1 = sK2),
% 0.19/0.48    inference(subsumption_resolution,[],[f56,f44])).
% 0.19/0.48  fof(f44,plain,(
% 0.19/0.48    v1_partfun1(sK1,sK0) | v1_xboole_0(sK0)),
% 0.19/0.48    inference(subsumption_resolution,[],[f43,f23])).
% 0.19/0.48  fof(f23,plain,(
% 0.19/0.48    v1_funct_2(sK1,sK0,sK0)),
% 0.19/0.48    inference(cnf_transformation,[],[f20])).
% 0.19/0.48  fof(f43,plain,(
% 0.19/0.48    v1_partfun1(sK1,sK0) | ~v1_funct_2(sK1,sK0,sK0) | v1_xboole_0(sK0)),
% 0.19/0.48    inference(resolution,[],[f41,f24])).
% 0.19/0.48  fof(f41,plain,(
% 0.19/0.48    ( ! [X0,X1] : (~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_partfun1(sK1,X0) | ~v1_funct_2(sK1,X0,X1) | v1_xboole_0(X1)) )),
% 0.19/0.48    inference(resolution,[],[f32,f22])).
% 0.19/0.48  fof(f22,plain,(
% 0.19/0.48    v1_funct_1(sK1)),
% 0.19/0.48    inference(cnf_transformation,[],[f20])).
% 0.19/0.48  fof(f32,plain,(
% 0.19/0.48    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f12])).
% 0.19/0.48  fof(f12,plain,(
% 0.19/0.48    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.19/0.48    inference(flattening,[],[f11])).
% 0.19/0.48  fof(f11,plain,(
% 0.19/0.48    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.19/0.48    inference(ennf_transformation,[],[f4])).
% 0.19/0.48  fof(f4,axiom,(
% 0.19/0.48    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).
% 0.19/0.48  fof(f56,plain,(
% 0.19/0.48    ~v1_partfun1(sK1,sK0) | sK1 = sK2 | v1_xboole_0(sK0)),
% 0.19/0.48    inference(resolution,[],[f55,f46])).
% 0.19/0.48  fof(f46,plain,(
% 0.19/0.48    v1_partfun1(sK2,sK0) | v1_xboole_0(sK0)),
% 0.19/0.48    inference(subsumption_resolution,[],[f45,f26])).
% 0.19/0.48  fof(f26,plain,(
% 0.19/0.48    v1_funct_2(sK2,sK0,sK0)),
% 0.19/0.48    inference(cnf_transformation,[],[f20])).
% 0.19/0.48  fof(f45,plain,(
% 0.19/0.48    v1_partfun1(sK2,sK0) | ~v1_funct_2(sK2,sK0,sK0) | v1_xboole_0(sK0)),
% 0.19/0.48    inference(resolution,[],[f42,f27])).
% 0.19/0.48  fof(f27,plain,(
% 0.19/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.19/0.48    inference(cnf_transformation,[],[f20])).
% 0.19/0.48  fof(f42,plain,(
% 0.19/0.48    ( ! [X2,X3] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | v1_partfun1(sK2,X2) | ~v1_funct_2(sK2,X2,X3) | v1_xboole_0(X3)) )),
% 0.19/0.48    inference(resolution,[],[f32,f25])).
% 0.19/0.48  fof(f25,plain,(
% 0.19/0.48    v1_funct_1(sK2)),
% 0.19/0.48    inference(cnf_transformation,[],[f20])).
% 0.19/0.48  fof(f55,plain,(
% 0.19/0.48    ~v1_partfun1(sK2,sK0) | ~v1_partfun1(sK1,sK0) | sK1 = sK2),
% 0.19/0.48    inference(subsumption_resolution,[],[f54,f24])).
% 0.19/0.48  fof(f54,plain,(
% 0.19/0.48    ~v1_partfun1(sK2,sK0) | ~v1_partfun1(sK1,sK0) | sK1 = sK2 | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.19/0.48    inference(resolution,[],[f53,f27])).
% 0.19/0.48  fof(f53,plain,(
% 0.19/0.48    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_partfun1(sK2,X0) | ~v1_partfun1(sK1,X0) | sK1 = sK2 | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.19/0.48    inference(subsumption_resolution,[],[f52,f22])).
% 0.19/0.48  fof(f52,plain,(
% 0.19/0.48    ( ! [X0,X1] : (sK1 = sK2 | ~v1_partfun1(sK2,X0) | ~v1_partfun1(sK1,X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(sK1)) )),
% 0.19/0.48    inference(subsumption_resolution,[],[f51,f25])).
% 0.19/0.48  fof(f51,plain,(
% 0.19/0.48    ( ! [X0,X1] : (sK1 = sK2 | ~v1_partfun1(sK2,X0) | ~v1_partfun1(sK1,X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(sK1)) )),
% 0.19/0.48    inference(resolution,[],[f34,f28])).
% 0.19/0.48  fof(f28,plain,(
% 0.19/0.48    r1_partfun1(sK1,sK2)),
% 0.19/0.48    inference(cnf_transformation,[],[f20])).
% 0.19/0.48  fof(f34,plain,(
% 0.19/0.48    ( ! [X2,X0,X3,X1] : (~r1_partfun1(X2,X3) | X2 = X3 | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f15])).
% 0.19/0.48  fof(f15,plain,(
% 0.19/0.48    ! [X0,X1,X2] : (! [X3] : (X2 = X3 | ~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.19/0.48    inference(flattening,[],[f14])).
% 0.19/0.48  fof(f14,plain,(
% 0.19/0.48    ! [X0,X1,X2] : (! [X3] : ((X2 = X3 | (~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.19/0.48    inference(ennf_transformation,[],[f5])).
% 0.19/0.48  fof(f5,axiom,(
% 0.19/0.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ((r1_partfun1(X2,X3) & v1_partfun1(X3,X0) & v1_partfun1(X2,X0)) => X2 = X3)))),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_partfun1)).
% 0.19/0.48  fof(f96,plain,(
% 0.19/0.48    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) | sK1 = sK2 | v1_xboole_0(X0)) )),
% 0.19/0.48    inference(forward_demodulation,[],[f58,f71])).
% 0.19/0.48  fof(f58,plain,(
% 0.19/0.48    ( ! [X0,X1] : (sK1 = sK2 | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0))) | v1_xboole_0(X0)) )),
% 0.19/0.48    inference(resolution,[],[f57,f33])).
% 0.19/0.48  fof(f33,plain,(
% 0.19/0.48    ( ! [X2,X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | v1_xboole_0(X2)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f13])).
% 0.19/0.48  fof(f13,plain,(
% 0.19/0.48    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 0.19/0.48    inference(ennf_transformation,[],[f2])).
% 0.19/0.48  fof(f2,axiom,(
% 0.19/0.48    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).
% 0.19/0.48  fof(f29,plain,(
% 0.19/0.48    ~r2_relset_1(sK0,sK0,sK1,sK2)),
% 0.19/0.48    inference(cnf_transformation,[],[f20])).
% 0.19/0.48  fof(f77,plain,(
% 0.19/0.48    r2_relset_1(k1_xboole_0,k1_xboole_0,sK1,sK1)),
% 0.19/0.48    inference(superposition,[],[f39,f71])).
% 0.19/0.48  fof(f178,plain,(
% 0.19/0.48    ~r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 0.19/0.48    inference(forward_demodulation,[],[f177,f71])).
% 0.19/0.48  fof(f177,plain,(
% 0.19/0.48    ~r2_relset_1(sK0,sK0,k1_xboole_0,k1_xboole_0)),
% 0.19/0.48    inference(forward_demodulation,[],[f158,f121])).
% 0.19/0.48  fof(f158,plain,(
% 0.19/0.48    ~r2_relset_1(sK0,sK0,sK1,k1_xboole_0)),
% 0.19/0.48    inference(superposition,[],[f29,f153])).
% 0.19/0.48  fof(f153,plain,(
% 0.19/0.48    k1_xboole_0 = sK2),
% 0.19/0.48    inference(duplicate_literal_removal,[],[f152])).
% 0.19/0.48  fof(f152,plain,(
% 0.19/0.48    k1_xboole_0 = sK2 | k1_xboole_0 = sK2),
% 0.19/0.48    inference(forward_demodulation,[],[f102,f121])).
% 0.19/0.48  fof(f102,plain,(
% 0.19/0.48    sK1 = sK2 | k1_xboole_0 = sK2),
% 0.19/0.48    inference(resolution,[],[f98,f30])).
% 0.19/0.48  fof(f98,plain,(
% 0.19/0.48    v1_xboole_0(sK2) | sK1 = sK2),
% 0.19/0.48    inference(resolution,[],[f96,f75])).
% 0.19/0.48  fof(f75,plain,(
% 0.19/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 0.19/0.48    inference(superposition,[],[f27,f71])).
% 0.19/0.48  % SZS output end Proof for theBenchmark
% 0.19/0.48  % (27574)------------------------------
% 0.19/0.48  % (27574)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.48  % (27574)Termination reason: Refutation
% 0.19/0.48  
% 0.19/0.48  % (27574)Memory used [KB]: 6140
% 0.19/0.48  % (27574)Time elapsed: 0.098 s
% 0.19/0.48  % (27574)------------------------------
% 0.19/0.48  % (27574)------------------------------
% 0.19/0.48  % (27578)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.19/0.48  % (27564)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.19/0.49  % (27552)Success in time 0.135 s
%------------------------------------------------------------------------------
