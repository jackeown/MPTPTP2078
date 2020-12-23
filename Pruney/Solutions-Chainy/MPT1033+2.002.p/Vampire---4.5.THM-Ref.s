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
% DateTime   : Thu Dec  3 13:06:42 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 562 expanded)
%              Number of leaves         :   13 ( 107 expanded)
%              Depth                    :   21
%              Number of atoms          :  291 (3386 expanded)
%              Number of equality atoms :   37 ( 591 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f462,plain,(
    $false ),
    inference(subsumption_resolution,[],[f446,f218])).

fof(f218,plain,(
    ! [X0,X1] : r2_relset_1(X0,X1,k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[],[f208,f44])).

fof(f44,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f208,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | r2_relset_1(X1,X2,X0,X0) ) ),
    inference(resolution,[],[f61,f44])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X2,X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => r2_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

fof(f446,plain,(
    ~ r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f390,f420])).

fof(f420,plain,(
    k1_xboole_0 = sK3 ),
    inference(resolution,[],[f359,f45])).

fof(f45,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f359,plain,(
    v1_xboole_0(sK3) ),
    inference(subsumption_resolution,[],[f155,f309])).

fof(f309,plain,(
    v5_relat_1(sK3,k1_xboole_0) ),
    inference(backward_demodulation,[],[f112,f301])).

fof(f301,plain,(
    k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f268,f219])).

fof(f219,plain,(
    r2_relset_1(sK0,sK1,sK2,sK2) ),
    inference(resolution,[],[f208,f42])).

fof(f42,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
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
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
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

fof(f268,plain,
    ( ~ r2_relset_1(sK0,sK1,sK2,sK2)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f39,f263])).

fof(f263,plain,
    ( sK2 = sK3
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f261,f45])).

fof(f261,plain,
    ( v1_xboole_0(sK1)
    | sK2 = sK3 ),
    inference(subsumption_resolution,[],[f260,f190])).

fof(f190,plain,
    ( v1_partfun1(sK2,sK0)
    | v1_xboole_0(sK1) ),
    inference(subsumption_resolution,[],[f186,f41])).

fof(f41,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f186,plain,
    ( v1_xboole_0(sK1)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | v1_partfun1(sK2,sK0) ),
    inference(resolution,[],[f172,f42])).

fof(f172,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | v1_xboole_0(X3)
      | ~ v1_funct_2(sK2,X2,X3)
      | v1_partfun1(sK2,X2) ) ),
    inference(resolution,[],[f48,f40])).

fof(f40,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1)
      | ~ v1_funct_2(X2,X0,X1)
      | v1_partfun1(X2,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f260,plain,
    ( ~ v1_partfun1(sK2,sK0)
    | sK2 = sK3
    | v1_xboole_0(sK1) ),
    inference(subsumption_resolution,[],[f259,f38])).

fof(f38,plain,(
    r1_partfun1(sK2,sK3) ),
    inference(cnf_transformation,[],[f18])).

fof(f259,plain,
    ( ~ v1_partfun1(sK2,sK0)
    | ~ r1_partfun1(sK2,sK3)
    | sK2 = sK3
    | v1_xboole_0(sK1) ),
    inference(subsumption_resolution,[],[f256,f40])).

fof(f256,plain,
    ( ~ v1_partfun1(sK2,sK0)
    | ~ v1_funct_1(sK2)
    | ~ r1_partfun1(sK2,sK3)
    | sK2 = sK3
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f254,f42])).

fof(f254,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_partfun1(X0,sK0)
      | ~ v1_funct_1(X0)
      | ~ r1_partfun1(X0,sK3)
      | sK3 = X0
      | v1_xboole_0(sK1) ) ),
    inference(resolution,[],[f250,f181])).

fof(f181,plain,
    ( v1_partfun1(sK3,sK0)
    | v1_xboole_0(sK1) ),
    inference(subsumption_resolution,[],[f177,f36])).

fof(f36,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f177,plain,
    ( v1_xboole_0(sK1)
    | ~ v1_funct_2(sK3,sK0,sK1)
    | v1_partfun1(sK3,sK0) ),
    inference(resolution,[],[f171,f37])).

fof(f37,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f18])).

fof(f171,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1)
      | ~ v1_funct_2(sK3,X0,X1)
      | v1_partfun1(sK3,X0) ) ),
    inference(resolution,[],[f48,f35])).

fof(f35,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f18])).

fof(f250,plain,(
    ! [X0] :
      ( ~ v1_partfun1(sK3,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_partfun1(X0,sK0)
      | ~ v1_funct_1(X0)
      | ~ r1_partfun1(X0,sK3)
      | sK3 = X0 ) ),
    inference(resolution,[],[f216,f37])).

fof(f216,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_partfun1(X0,X1)
      | ~ v1_partfun1(sK3,X1)
      | ~ r1_partfun1(X0,sK3)
      | sK3 = X0 ) ),
    inference(resolution,[],[f59,f35])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_partfun1(X2,X0)
      | ~ v1_partfun1(X3,X0)
      | ~ r1_partfun1(X2,X3)
      | X2 = X3 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
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

fof(f39,plain,(
    ~ r2_relset_1(sK0,sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f18])).

fof(f112,plain,(
    v5_relat_1(sK3,sK1) ),
    inference(resolution,[],[f58,f37])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f155,plain,
    ( ~ v5_relat_1(sK3,k1_xboole_0)
    | v1_xboole_0(sK3) ),
    inference(resolution,[],[f150,f65])).

fof(f65,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f46,f43])).

fof(f43,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f150,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ v5_relat_1(sK3,k1_xboole_0) ),
    inference(resolution,[],[f147,f92])).

fof(f92,plain,(
    ! [X2] :
      ( r1_tarski(k2_relat_1(sK3),X2)
      | ~ v5_relat_1(sK3,X2) ) ),
    inference(resolution,[],[f50,f75])).

fof(f75,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f56,f37])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f147,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),k1_xboole_0)
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[],[f141,f62])).

fof(f62,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f141,plain,(
    ! [X0] :
      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X0)))
      | ~ r1_tarski(k2_relat_1(sK3),X0) ) ),
    inference(subsumption_resolution,[],[f139,f75])).

fof(f139,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK3)
      | ~ r1_tarski(k2_relat_1(sK3),X0)
      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X0))) ) ),
    inference(resolution,[],[f52,f35])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

fof(f390,plain,(
    ~ r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,sK3) ),
    inference(backward_demodulation,[],[f332,f381])).

fof(f381,plain,(
    k1_xboole_0 = sK2 ),
    inference(resolution,[],[f339,f45])).

fof(f339,plain,(
    v1_xboole_0(sK2) ),
    inference(subsumption_resolution,[],[f169,f308])).

fof(f308,plain,(
    v5_relat_1(sK2,k1_xboole_0) ),
    inference(backward_demodulation,[],[f111,f301])).

fof(f111,plain,(
    v5_relat_1(sK2,sK1) ),
    inference(resolution,[],[f58,f42])).

fof(f169,plain,
    ( ~ v5_relat_1(sK2,k1_xboole_0)
    | v1_xboole_0(sK2) ),
    inference(resolution,[],[f164,f65])).

fof(f164,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ v5_relat_1(sK2,k1_xboole_0) ),
    inference(resolution,[],[f161,f91])).

fof(f91,plain,(
    ! [X1] :
      ( r1_tarski(k2_relat_1(sK2),X1)
      | ~ v5_relat_1(sK2,X1) ) ),
    inference(resolution,[],[f50,f74])).

fof(f74,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f56,f42])).

fof(f161,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),k1_xboole_0)
    | m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[],[f142,f62])).

fof(f142,plain,(
    ! [X1] :
      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X1)))
      | ~ r1_tarski(k2_relat_1(sK2),X1) ) ),
    inference(subsumption_resolution,[],[f140,f74])).

fof(f140,plain,(
    ! [X1] :
      ( ~ v1_relat_1(sK2)
      | ~ r1_tarski(k2_relat_1(sK2),X1)
      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X1))) ) ),
    inference(resolution,[],[f52,f40])).

fof(f332,plain,(
    ~ r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,sK3) ),
    inference(forward_demodulation,[],[f305,f302])).

fof(f302,plain,(
    k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f34,f301])).

fof(f34,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f18])).

fof(f305,plain,(
    ~ r2_relset_1(sK0,k1_xboole_0,sK2,sK3) ),
    inference(backward_demodulation,[],[f39,f301])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:07:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (11658)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.46  % (11650)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.48  % (11658)Refutation found. Thanks to Tanya!
% 0.20/0.48  % SZS status Theorem for theBenchmark
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.48  fof(f462,plain,(
% 0.20/0.48    $false),
% 0.20/0.48    inference(subsumption_resolution,[],[f446,f218])).
% 0.20/0.48  fof(f218,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r2_relset_1(X0,X1,k1_xboole_0,k1_xboole_0)) )),
% 0.20/0.48    inference(resolution,[],[f208,f44])).
% 0.20/0.48  fof(f44,plain,(
% 0.20/0.48    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f5])).
% 0.20/0.48  fof(f5,axiom,(
% 0.20/0.48    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.20/0.48  fof(f208,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | r2_relset_1(X1,X2,X0,X0)) )),
% 0.20/0.48    inference(resolution,[],[f61,f44])).
% 0.20/0.48  fof(f61,plain,(
% 0.20/0.48    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X2,X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f33])).
% 0.20/0.48  fof(f33,plain,(
% 0.20/0.48    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.48    inference(flattening,[],[f32])).
% 0.20/0.48  fof(f32,plain,(
% 0.20/0.48    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.20/0.48    inference(ennf_transformation,[],[f11])).
% 0.20/0.48  fof(f11,axiom,(
% 0.20/0.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => r2_relset_1(X0,X1,X2,X2))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).
% 0.20/0.48  fof(f446,plain,(
% 0.20/0.48    ~r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 0.20/0.48    inference(backward_demodulation,[],[f390,f420])).
% 0.20/0.48  fof(f420,plain,(
% 0.20/0.48    k1_xboole_0 = sK3),
% 0.20/0.48    inference(resolution,[],[f359,f45])).
% 0.20/0.48  fof(f45,plain,(
% 0.20/0.48    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.20/0.48    inference(cnf_transformation,[],[f19])).
% 0.20/0.48  fof(f19,plain,(
% 0.20/0.48    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f2])).
% 0.20/0.48  fof(f2,axiom,(
% 0.20/0.48    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.20/0.48  fof(f359,plain,(
% 0.20/0.48    v1_xboole_0(sK3)),
% 0.20/0.48    inference(subsumption_resolution,[],[f155,f309])).
% 0.20/0.48  fof(f309,plain,(
% 0.20/0.48    v5_relat_1(sK3,k1_xboole_0)),
% 0.20/0.48    inference(backward_demodulation,[],[f112,f301])).
% 0.20/0.48  fof(f301,plain,(
% 0.20/0.48    k1_xboole_0 = sK1),
% 0.20/0.48    inference(subsumption_resolution,[],[f268,f219])).
% 0.20/0.48  fof(f219,plain,(
% 0.20/0.48    r2_relset_1(sK0,sK1,sK2,sK2)),
% 0.20/0.48    inference(resolution,[],[f208,f42])).
% 0.20/0.48  fof(f42,plain,(
% 0.20/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.48    inference(cnf_transformation,[],[f18])).
% 0.20/0.48  fof(f18,plain,(
% 0.20/0.48    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_partfun1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.20/0.48    inference(flattening,[],[f17])).
% 0.20/0.48  fof(f17,plain,(
% 0.20/0.48    ? [X0,X1,X2] : (? [X3] : (((~r2_relset_1(X0,X1,X2,X3) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_partfun1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.20/0.48    inference(ennf_transformation,[],[f16])).
% 0.20/0.48  fof(f16,negated_conjecture,(
% 0.20/0.48    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_partfun1(X2,X3) => (r2_relset_1(X0,X1,X2,X3) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)))))),
% 0.20/0.48    inference(negated_conjecture,[],[f15])).
% 0.20/0.48  fof(f15,conjecture,(
% 0.20/0.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_partfun1(X2,X3) => (r2_relset_1(X0,X1,X2,X3) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)))))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_funct_2)).
% 0.20/0.48  fof(f268,plain,(
% 0.20/0.48    ~r2_relset_1(sK0,sK1,sK2,sK2) | k1_xboole_0 = sK1),
% 0.20/0.48    inference(superposition,[],[f39,f263])).
% 0.20/0.48  fof(f263,plain,(
% 0.20/0.48    sK2 = sK3 | k1_xboole_0 = sK1),
% 0.20/0.48    inference(resolution,[],[f261,f45])).
% 0.20/0.48  fof(f261,plain,(
% 0.20/0.48    v1_xboole_0(sK1) | sK2 = sK3),
% 0.20/0.48    inference(subsumption_resolution,[],[f260,f190])).
% 0.20/0.48  fof(f190,plain,(
% 0.20/0.48    v1_partfun1(sK2,sK0) | v1_xboole_0(sK1)),
% 0.20/0.48    inference(subsumption_resolution,[],[f186,f41])).
% 0.20/0.48  fof(f41,plain,(
% 0.20/0.48    v1_funct_2(sK2,sK0,sK1)),
% 0.20/0.48    inference(cnf_transformation,[],[f18])).
% 0.20/0.48  fof(f186,plain,(
% 0.20/0.48    v1_xboole_0(sK1) | ~v1_funct_2(sK2,sK0,sK1) | v1_partfun1(sK2,sK0)),
% 0.20/0.48    inference(resolution,[],[f172,f42])).
% 0.20/0.48  fof(f172,plain,(
% 0.20/0.48    ( ! [X2,X3] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | v1_xboole_0(X3) | ~v1_funct_2(sK2,X2,X3) | v1_partfun1(sK2,X2)) )),
% 0.20/0.48    inference(resolution,[],[f48,f40])).
% 0.20/0.48  fof(f40,plain,(
% 0.20/0.48    v1_funct_1(sK2)),
% 0.20/0.48    inference(cnf_transformation,[],[f18])).
% 0.20/0.48  fof(f48,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | ~v1_funct_2(X2,X0,X1) | v1_partfun1(X2,X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f22])).
% 0.20/0.48  fof(f22,plain,(
% 0.20/0.48    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.20/0.48    inference(flattening,[],[f21])).
% 0.20/0.48  fof(f21,plain,(
% 0.20/0.48    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.20/0.48    inference(ennf_transformation,[],[f12])).
% 0.20/0.48  fof(f12,axiom,(
% 0.20/0.48    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).
% 0.20/0.48  fof(f260,plain,(
% 0.20/0.48    ~v1_partfun1(sK2,sK0) | sK2 = sK3 | v1_xboole_0(sK1)),
% 0.20/0.48    inference(subsumption_resolution,[],[f259,f38])).
% 0.20/0.48  fof(f38,plain,(
% 0.20/0.48    r1_partfun1(sK2,sK3)),
% 0.20/0.48    inference(cnf_transformation,[],[f18])).
% 0.20/0.48  fof(f259,plain,(
% 0.20/0.48    ~v1_partfun1(sK2,sK0) | ~r1_partfun1(sK2,sK3) | sK2 = sK3 | v1_xboole_0(sK1)),
% 0.20/0.48    inference(subsumption_resolution,[],[f256,f40])).
% 0.20/0.48  fof(f256,plain,(
% 0.20/0.48    ~v1_partfun1(sK2,sK0) | ~v1_funct_1(sK2) | ~r1_partfun1(sK2,sK3) | sK2 = sK3 | v1_xboole_0(sK1)),
% 0.20/0.48    inference(resolution,[],[f254,f42])).
% 0.20/0.48  fof(f254,plain,(
% 0.20/0.48    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_partfun1(X0,sK0) | ~v1_funct_1(X0) | ~r1_partfun1(X0,sK3) | sK3 = X0 | v1_xboole_0(sK1)) )),
% 0.20/0.48    inference(resolution,[],[f250,f181])).
% 0.20/0.48  fof(f181,plain,(
% 0.20/0.48    v1_partfun1(sK3,sK0) | v1_xboole_0(sK1)),
% 0.20/0.48    inference(subsumption_resolution,[],[f177,f36])).
% 0.20/0.48  fof(f36,plain,(
% 0.20/0.48    v1_funct_2(sK3,sK0,sK1)),
% 0.20/0.48    inference(cnf_transformation,[],[f18])).
% 0.20/0.48  fof(f177,plain,(
% 0.20/0.48    v1_xboole_0(sK1) | ~v1_funct_2(sK3,sK0,sK1) | v1_partfun1(sK3,sK0)),
% 0.20/0.48    inference(resolution,[],[f171,f37])).
% 0.20/0.48  fof(f37,plain,(
% 0.20/0.48    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.48    inference(cnf_transformation,[],[f18])).
% 0.20/0.48  fof(f171,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | ~v1_funct_2(sK3,X0,X1) | v1_partfun1(sK3,X0)) )),
% 0.20/0.48    inference(resolution,[],[f48,f35])).
% 0.20/0.48  fof(f35,plain,(
% 0.20/0.48    v1_funct_1(sK3)),
% 0.20/0.48    inference(cnf_transformation,[],[f18])).
% 0.20/0.48  fof(f250,plain,(
% 0.20/0.48    ( ! [X0] : (~v1_partfun1(sK3,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_partfun1(X0,sK0) | ~v1_funct_1(X0) | ~r1_partfun1(X0,sK3) | sK3 = X0) )),
% 0.20/0.48    inference(resolution,[],[f216,f37])).
% 0.20/0.48  fof(f216,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_partfun1(X0,X1) | ~v1_partfun1(sK3,X1) | ~r1_partfun1(X0,sK3) | sK3 = X0) )),
% 0.20/0.48    inference(resolution,[],[f59,f35])).
% 0.20/0.48  fof(f59,plain,(
% 0.20/0.48    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_partfun1(X2,X0) | ~v1_partfun1(X3,X0) | ~r1_partfun1(X2,X3) | X2 = X3) )),
% 0.20/0.48    inference(cnf_transformation,[],[f29])).
% 0.20/0.48  fof(f29,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (! [X3] : (X2 = X3 | ~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.20/0.48    inference(flattening,[],[f28])).
% 0.20/0.48  fof(f28,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (! [X3] : ((X2 = X3 | (~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.20/0.48    inference(ennf_transformation,[],[f13])).
% 0.20/0.48  fof(f13,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ((r1_partfun1(X2,X3) & v1_partfun1(X3,X0) & v1_partfun1(X2,X0)) => X2 = X3)))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_partfun1)).
% 0.20/0.48  fof(f39,plain,(
% 0.20/0.48    ~r2_relset_1(sK0,sK1,sK2,sK3)),
% 0.20/0.48    inference(cnf_transformation,[],[f18])).
% 0.20/0.48  fof(f112,plain,(
% 0.20/0.48    v5_relat_1(sK3,sK1)),
% 0.20/0.48    inference(resolution,[],[f58,f37])).
% 0.20/0.48  fof(f58,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f27])).
% 0.20/0.48  fof(f27,plain,(
% 0.20/0.48    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.48    inference(ennf_transformation,[],[f10])).
% 0.20/0.48  fof(f10,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.20/0.48  fof(f155,plain,(
% 0.20/0.48    ~v5_relat_1(sK3,k1_xboole_0) | v1_xboole_0(sK3)),
% 0.20/0.48    inference(resolution,[],[f150,f65])).
% 0.20/0.48  fof(f65,plain,(
% 0.20/0.48    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | v1_xboole_0(X0)) )),
% 0.20/0.48    inference(resolution,[],[f46,f43])).
% 0.20/0.48  fof(f43,plain,(
% 0.20/0.48    v1_xboole_0(k1_xboole_0)),
% 0.20/0.48    inference(cnf_transformation,[],[f1])).
% 0.20/0.48  fof(f1,axiom,(
% 0.20/0.48    v1_xboole_0(k1_xboole_0)),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.48  fof(f46,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f20])).
% 0.20/0.48  fof(f20,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f6])).
% 0.20/0.48  fof(f6,axiom,(
% 0.20/0.48    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).
% 0.20/0.48  fof(f150,plain,(
% 0.20/0.48    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | ~v5_relat_1(sK3,k1_xboole_0)),
% 0.20/0.48    inference(resolution,[],[f147,f92])).
% 0.20/0.48  fof(f92,plain,(
% 0.20/0.48    ( ! [X2] : (r1_tarski(k2_relat_1(sK3),X2) | ~v5_relat_1(sK3,X2)) )),
% 0.20/0.48    inference(resolution,[],[f50,f75])).
% 0.20/0.48  fof(f75,plain,(
% 0.20/0.48    v1_relat_1(sK3)),
% 0.20/0.48    inference(resolution,[],[f56,f37])).
% 0.20/0.48  fof(f56,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f26])).
% 0.20/0.48  fof(f26,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.48    inference(ennf_transformation,[],[f9])).
% 0.20/0.48  fof(f9,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.20/0.48  fof(f50,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f23])).
% 0.20/0.48  fof(f23,plain,(
% 0.20/0.48    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.48    inference(ennf_transformation,[],[f8])).
% 0.20/0.48  fof(f8,axiom,(
% 0.20/0.48    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 0.20/0.48  fof(f147,plain,(
% 0.20/0.48    ~r1_tarski(k2_relat_1(sK3),k1_xboole_0) | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))),
% 0.20/0.48    inference(superposition,[],[f141,f62])).
% 0.20/0.48  fof(f62,plain,(
% 0.20/0.48    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.20/0.48    inference(equality_resolution,[],[f55])).
% 0.20/0.48  fof(f55,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f3])).
% 0.20/0.48  fof(f3,axiom,(
% 0.20/0.48    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.20/0.48  fof(f141,plain,(
% 0.20/0.48    ( ! [X0] : (m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X0))) | ~r1_tarski(k2_relat_1(sK3),X0)) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f139,f75])).
% 0.20/0.48  fof(f139,plain,(
% 0.20/0.48    ( ! [X0] : (~v1_relat_1(sK3) | ~r1_tarski(k2_relat_1(sK3),X0) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X0)))) )),
% 0.20/0.48    inference(resolution,[],[f52,f35])).
% 0.20/0.48  fof(f52,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~v1_funct_1(X1) | ~v1_relat_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f25])).
% 0.20/0.49  fof(f25,plain,(
% 0.20/0.49    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.49    inference(flattening,[],[f24])).
% 0.20/0.49  fof(f24,plain,(
% 0.20/0.49    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.20/0.49    inference(ennf_transformation,[],[f14])).
% 0.20/0.49  fof(f14,axiom,(
% 0.20/0.49    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).
% 0.20/0.49  fof(f390,plain,(
% 0.20/0.49    ~r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,sK3)),
% 0.20/0.49    inference(backward_demodulation,[],[f332,f381])).
% 0.20/0.49  fof(f381,plain,(
% 0.20/0.49    k1_xboole_0 = sK2),
% 0.20/0.49    inference(resolution,[],[f339,f45])).
% 0.20/0.49  fof(f339,plain,(
% 0.20/0.49    v1_xboole_0(sK2)),
% 0.20/0.49    inference(subsumption_resolution,[],[f169,f308])).
% 0.20/0.49  fof(f308,plain,(
% 0.20/0.49    v5_relat_1(sK2,k1_xboole_0)),
% 0.20/0.49    inference(backward_demodulation,[],[f111,f301])).
% 0.20/0.49  fof(f111,plain,(
% 0.20/0.49    v5_relat_1(sK2,sK1)),
% 0.20/0.49    inference(resolution,[],[f58,f42])).
% 0.20/0.49  fof(f169,plain,(
% 0.20/0.49    ~v5_relat_1(sK2,k1_xboole_0) | v1_xboole_0(sK2)),
% 0.20/0.49    inference(resolution,[],[f164,f65])).
% 0.20/0.49  fof(f164,plain,(
% 0.20/0.49    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~v5_relat_1(sK2,k1_xboole_0)),
% 0.20/0.49    inference(resolution,[],[f161,f91])).
% 0.20/0.49  fof(f91,plain,(
% 0.20/0.49    ( ! [X1] : (r1_tarski(k2_relat_1(sK2),X1) | ~v5_relat_1(sK2,X1)) )),
% 0.20/0.49    inference(resolution,[],[f50,f74])).
% 0.20/0.49  fof(f74,plain,(
% 0.20/0.49    v1_relat_1(sK2)),
% 0.20/0.49    inference(resolution,[],[f56,f42])).
% 0.20/0.49  fof(f161,plain,(
% 0.20/0.49    ~r1_tarski(k2_relat_1(sK2),k1_xboole_0) | m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 0.20/0.49    inference(superposition,[],[f142,f62])).
% 0.20/0.49  fof(f142,plain,(
% 0.20/0.49    ( ! [X1] : (m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X1))) | ~r1_tarski(k2_relat_1(sK2),X1)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f140,f74])).
% 0.20/0.49  fof(f140,plain,(
% 0.20/0.49    ( ! [X1] : (~v1_relat_1(sK2) | ~r1_tarski(k2_relat_1(sK2),X1) | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X1)))) )),
% 0.20/0.49    inference(resolution,[],[f52,f40])).
% 0.20/0.49  fof(f332,plain,(
% 0.20/0.49    ~r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,sK3)),
% 0.20/0.49    inference(forward_demodulation,[],[f305,f302])).
% 0.20/0.49  fof(f302,plain,(
% 0.20/0.49    k1_xboole_0 = sK0),
% 0.20/0.49    inference(subsumption_resolution,[],[f34,f301])).
% 0.20/0.49  fof(f34,plain,(
% 0.20/0.49    k1_xboole_0 != sK1 | k1_xboole_0 = sK0),
% 0.20/0.49    inference(cnf_transformation,[],[f18])).
% 0.20/0.49  fof(f305,plain,(
% 0.20/0.49    ~r2_relset_1(sK0,k1_xboole_0,sK2,sK3)),
% 0.20/0.49    inference(backward_demodulation,[],[f39,f301])).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (11658)------------------------------
% 0.20/0.49  % (11658)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (11658)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (11658)Memory used [KB]: 1791
% 0.20/0.49  % (11658)Time elapsed: 0.076 s
% 0.20/0.49  % (11658)------------------------------
% 0.20/0.49  % (11658)------------------------------
% 0.20/0.49  % (11638)Success in time 0.13 s
%------------------------------------------------------------------------------
