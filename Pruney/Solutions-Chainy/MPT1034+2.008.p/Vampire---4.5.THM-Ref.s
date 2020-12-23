%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:50 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   76 (1871 expanded)
%              Number of leaves         :    7 ( 590 expanded)
%              Depth                    :   25
%              Number of atoms          :  338 (14395 expanded)
%              Number of equality atoms :   55 ( 512 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f366,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f363])).

fof(f363,plain,(
    k1_funct_1(sK1,sK3(k1_xboole_0,sK1,sK1)) != k1_funct_1(sK1,sK3(k1_xboole_0,sK1,sK1)) ),
    inference(backward_demodulation,[],[f220,f353])).

fof(f353,plain,(
    sK1 = sK2 ),
    inference(subsumption_resolution,[],[f352,f22])).

fof(f22,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ~ r2_relset_1(sK0,sK0,sK1,sK2)
    & r1_partfun1(sK1,sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v1_funct_2(sK2,sK0,sK0)
    & v1_funct_1(sK2)
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f15,f14])).

fof(f14,plain,
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

fof(f15,plain,
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

fof(f7,plain,(
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
    inference(flattening,[],[f6])).

fof(f6,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
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
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
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

fof(f352,plain,
    ( sK1 = sK2
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f351,f25])).

fof(f25,plain,(
    r1_partfun1(sK1,sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f351,plain,
    ( ~ r1_partfun1(sK1,sK2)
    | sK1 = sK2
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f349,f317])).

fof(f317,plain,(
    v1_partfun1(sK2,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f316,f22])).

fof(f316,plain,
    ( v1_partfun1(sK2,k1_xboole_0)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f305,f206])).

fof(f206,plain,(
    v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f23,f202])).

fof(f202,plain,(
    k1_xboole_0 = sK0 ),
    inference(trivial_inequality_removal,[],[f201])).

fof(f201,plain,
    ( k1_funct_1(sK1,sK3(sK0,sK1,sK1)) != k1_funct_1(sK1,sK3(sK0,sK1,sK1))
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f200,f154])).

fof(f154,plain,
    ( sK1 = sK2
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f152,f102])).

fof(f102,plain,
    ( v1_partfun1(sK1,sK0)
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f101,f19])).

fof(f19,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f101,plain,
    ( v1_partfun1(sK1,sK0)
    | k1_xboole_0 = sK0
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f90,f20])).

fof(f20,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f90,plain,
    ( v1_partfun1(sK1,sK0)
    | k1_xboole_0 = sK0
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(resolution,[],[f21,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(duplicate_literal_removal,[],[f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v1_partfun1(X2,X0)
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_funct_2)).

fof(f21,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f16])).

fof(f152,plain,
    ( ~ v1_partfun1(sK1,sK0)
    | sK1 = sK2
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f141,f121])).

fof(f121,plain,
    ( v1_partfun1(sK2,sK0)
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f120,f22])).

fof(f120,plain,
    ( v1_partfun1(sK2,sK0)
    | k1_xboole_0 = sK0
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f109,f23])).

fof(f109,plain,
    ( v1_partfun1(sK2,sK0)
    | k1_xboole_0 = sK0
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f24,f34])).

fof(f24,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f16])).

fof(f141,plain,
    ( ~ v1_partfun1(sK2,sK0)
    | ~ v1_partfun1(sK1,sK0)
    | sK1 = sK2 ),
    inference(subsumption_resolution,[],[f140,f22])).

fof(f140,plain,
    ( ~ v1_partfun1(sK2,sK0)
    | ~ v1_partfun1(sK1,sK0)
    | sK1 = sK2
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f138,f25])).

fof(f138,plain,
    ( ~ r1_partfun1(sK1,sK2)
    | ~ v1_partfun1(sK2,sK0)
    | ~ v1_partfun1(sK1,sK0)
    | sK1 = sK2
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f99,f24])).

fof(f99,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | ~ r1_partfun1(sK1,X4)
      | ~ v1_partfun1(X4,sK0)
      | ~ v1_partfun1(sK1,sK0)
      | sK1 = X4
      | ~ v1_funct_1(X4) ) ),
    inference(subsumption_resolution,[],[f88,f19])).

fof(f88,plain,(
    ! [X4] :
      ( sK1 = X4
      | ~ r1_partfun1(sK1,X4)
      | ~ v1_partfun1(X4,sK0)
      | ~ v1_partfun1(sK1,sK0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_1(sK1) ) ),
    inference(resolution,[],[f21,f31])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r1_partfun1(X2,X3)
      | ~ v1_partfun1(X3,X0)
      | ~ v1_partfun1(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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

fof(f200,plain,(
    k1_funct_1(sK1,sK3(sK0,sK1,sK2)) != k1_funct_1(sK2,sK3(sK0,sK1,sK2)) ),
    inference(subsumption_resolution,[],[f199,f21])).

fof(f199,plain,
    ( k1_funct_1(sK1,sK3(sK0,sK1,sK2)) != k1_funct_1(sK2,sK3(sK0,sK1,sK2))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subsumption_resolution,[],[f83,f24])).

fof(f83,plain,
    ( k1_funct_1(sK1,sK3(sK0,sK1,sK2)) != k1_funct_1(sK2,sK3(sK0,sK1,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subsumption_resolution,[],[f82,f19])).

fof(f82,plain,
    ( k1_funct_1(sK1,sK3(sK0,sK1,sK2)) != k1_funct_1(sK2,sK3(sK0,sK1,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f81,f20])).

fof(f81,plain,
    ( k1_funct_1(sK1,sK3(sK0,sK1,sK2)) != k1_funct_1(sK2,sK3(sK0,sK1,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f80,f22])).

fof(f80,plain,
    ( k1_funct_1(sK1,sK3(sK0,sK1,sK2)) != k1_funct_1(sK2,sK3(sK0,sK1,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f75,f23])).

fof(f75,plain,
    ( k1_funct_1(sK1,sK3(sK0,sK1,sK2)) != k1_funct_1(sK2,sK3(sK0,sK1,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(resolution,[],[f26,f28])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | k1_funct_1(X2,sK3(X0,X2,X3)) != k1_funct_1(X3,sK3(X0,X2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r2_relset_1(X0,X1,X2,X3)
          | ( k1_funct_1(X2,sK3(X0,X2,X3)) != k1_funct_1(X3,sK3(X0,X2,X3))
            & m1_subset_1(sK3(X0,X2,X3),X0) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f9,f17])).

fof(f17,plain,(
    ! [X3,X2,X0] :
      ( ? [X4] :
          ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
          & m1_subset_1(X4,X0) )
     => ( k1_funct_1(X2,sK3(X0,X2,X3)) != k1_funct_1(X3,sK3(X0,X2,X3))
        & m1_subset_1(sK3(X0,X2,X3),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r2_relset_1(X0,X1,X2,X3)
          | ? [X4] :
              ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
              & m1_subset_1(X4,X0) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r2_relset_1(X0,X1,X2,X3)
          | ? [X4] :
              ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
              & m1_subset_1(X4,X0) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( ! [X4] :
                ( m1_subset_1(X4,X0)
               => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) )
           => r2_relset_1(X0,X1,X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_funct_2)).

fof(f26,plain,(
    ~ r2_relset_1(sK0,sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f23,plain,(
    v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f305,plain,
    ( v1_partfun1(sK2,k1_xboole_0)
    | ~ v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f207,f33])).

fof(f33,plain,(
    ! [X2,X1] :
      ( v1_partfun1(X2,k1_xboole_0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(duplicate_literal_removal,[],[f32])).

fof(f32,plain,(
    ! [X2,X1] :
      ( v1_partfun1(X2,k1_xboole_0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f207,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f24,f202])).

fof(f349,plain,
    ( ~ v1_partfun1(sK2,k1_xboole_0)
    | ~ r1_partfun1(sK1,sK2)
    | sK1 = sK2
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f346,f207])).

fof(f346,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
      | ~ v1_partfun1(X4,k1_xboole_0)
      | ~ r1_partfun1(sK1,X4)
      | sK1 = X4
      | ~ v1_funct_1(X4) ) ),
    inference(subsumption_resolution,[],[f228,f291])).

fof(f291,plain,(
    v1_partfun1(sK1,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f290,f19])).

fof(f290,plain,
    ( v1_partfun1(sK1,k1_xboole_0)
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f280,f204])).

fof(f204,plain,(
    v1_funct_2(sK1,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f20,f202])).

fof(f280,plain,
    ( v1_partfun1(sK1,k1_xboole_0)
    | ~ v1_funct_2(sK1,k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(sK1) ),
    inference(resolution,[],[f205,f33])).

fof(f205,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f21,f202])).

fof(f228,plain,(
    ! [X4] :
      ( ~ v1_partfun1(sK1,k1_xboole_0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
      | ~ v1_partfun1(X4,k1_xboole_0)
      | ~ r1_partfun1(sK1,X4)
      | sK1 = X4
      | ~ v1_funct_1(X4) ) ),
    inference(forward_demodulation,[],[f227,f202])).

fof(f227,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
      | ~ v1_partfun1(X4,k1_xboole_0)
      | ~ r1_partfun1(sK1,X4)
      | ~ v1_partfun1(sK1,sK0)
      | sK1 = X4
      | ~ v1_funct_1(X4) ) ),
    inference(forward_demodulation,[],[f211,f202])).

fof(f211,plain,(
    ! [X4] :
      ( ~ v1_partfun1(X4,k1_xboole_0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | ~ r1_partfun1(sK1,X4)
      | ~ v1_partfun1(sK1,sK0)
      | sK1 = X4
      | ~ v1_funct_1(X4) ) ),
    inference(backward_demodulation,[],[f99,f202])).

fof(f220,plain,(
    k1_funct_1(sK1,sK3(k1_xboole_0,sK1,sK2)) != k1_funct_1(sK2,sK3(k1_xboole_0,sK1,sK2)) ),
    inference(backward_demodulation,[],[f200,f202])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n018.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:28:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (27746)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.47  % (27746)Refutation not found, incomplete strategy% (27746)------------------------------
% 0.21/0.47  % (27746)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (27746)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (27746)Memory used [KB]: 10490
% 0.21/0.47  % (27746)Time elapsed: 0.003 s
% 0.21/0.47  % (27746)------------------------------
% 0.21/0.47  % (27746)------------------------------
% 0.21/0.48  % (27753)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.49  % (27753)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f366,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(trivial_inequality_removal,[],[f363])).
% 0.21/0.49  fof(f363,plain,(
% 0.21/0.49    k1_funct_1(sK1,sK3(k1_xboole_0,sK1,sK1)) != k1_funct_1(sK1,sK3(k1_xboole_0,sK1,sK1))),
% 0.21/0.49    inference(backward_demodulation,[],[f220,f353])).
% 0.21/0.49  fof(f353,plain,(
% 0.21/0.49    sK1 = sK2),
% 0.21/0.49    inference(subsumption_resolution,[],[f352,f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    v1_funct_1(sK2)),
% 0.21/0.49    inference(cnf_transformation,[],[f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    (~r2_relset_1(sK0,sK0,sK1,sK2) & r1_partfun1(sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f15,f14])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X1,X2) & r1_partfun1(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (? [X2] : (~r2_relset_1(sK0,sK0,sK1,X2) & r1_partfun1(sK1,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(X2,sK0,sK0) & v1_funct_1(X2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ? [X2] : (~r2_relset_1(sK0,sK0,sK1,X2) & r1_partfun1(sK1,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(X2,sK0,sK0) & v1_funct_1(X2)) => (~r2_relset_1(sK0,sK0,sK1,sK2) & r1_partfun1(sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f7,plain,(
% 0.21/0.49    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X1,X2) & r1_partfun1(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 0.21/0.49    inference(flattening,[],[f6])).
% 0.21/0.49  fof(f6,plain,(
% 0.21/0.49    ? [X0,X1] : (? [X2] : ((~r2_relset_1(X0,X0,X1,X2) & r1_partfun1(X1,X2)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,negated_conjecture,(
% 0.21/0.49    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r1_partfun1(X1,X2) => r2_relset_1(X0,X0,X1,X2))))),
% 0.21/0.49    inference(negated_conjecture,[],[f4])).
% 0.21/0.49  fof(f4,conjecture,(
% 0.21/0.49    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r1_partfun1(X1,X2) => r2_relset_1(X0,X0,X1,X2))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_funct_2)).
% 0.21/0.49  fof(f352,plain,(
% 0.21/0.49    sK1 = sK2 | ~v1_funct_1(sK2)),
% 0.21/0.49    inference(subsumption_resolution,[],[f351,f25])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    r1_partfun1(sK1,sK2)),
% 0.21/0.49    inference(cnf_transformation,[],[f16])).
% 0.21/0.49  fof(f351,plain,(
% 0.21/0.49    ~r1_partfun1(sK1,sK2) | sK1 = sK2 | ~v1_funct_1(sK2)),
% 0.21/0.49    inference(subsumption_resolution,[],[f349,f317])).
% 0.21/0.49  fof(f317,plain,(
% 0.21/0.49    v1_partfun1(sK2,k1_xboole_0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f316,f22])).
% 0.21/0.49  fof(f316,plain,(
% 0.21/0.49    v1_partfun1(sK2,k1_xboole_0) | ~v1_funct_1(sK2)),
% 0.21/0.49    inference(subsumption_resolution,[],[f305,f206])).
% 0.21/0.49  fof(f206,plain,(
% 0.21/0.49    v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)),
% 0.21/0.49    inference(backward_demodulation,[],[f23,f202])).
% 0.21/0.49  fof(f202,plain,(
% 0.21/0.49    k1_xboole_0 = sK0),
% 0.21/0.49    inference(trivial_inequality_removal,[],[f201])).
% 0.21/0.49  fof(f201,plain,(
% 0.21/0.49    k1_funct_1(sK1,sK3(sK0,sK1,sK1)) != k1_funct_1(sK1,sK3(sK0,sK1,sK1)) | k1_xboole_0 = sK0),
% 0.21/0.49    inference(superposition,[],[f200,f154])).
% 0.21/0.49  fof(f154,plain,(
% 0.21/0.49    sK1 = sK2 | k1_xboole_0 = sK0),
% 0.21/0.49    inference(subsumption_resolution,[],[f152,f102])).
% 0.21/0.49  fof(f102,plain,(
% 0.21/0.49    v1_partfun1(sK1,sK0) | k1_xboole_0 = sK0),
% 0.21/0.49    inference(subsumption_resolution,[],[f101,f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    v1_funct_1(sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f16])).
% 0.21/0.49  fof(f101,plain,(
% 0.21/0.49    v1_partfun1(sK1,sK0) | k1_xboole_0 = sK0 | ~v1_funct_1(sK1)),
% 0.21/0.49    inference(subsumption_resolution,[],[f90,f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    v1_funct_2(sK1,sK0,sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f16])).
% 0.21/0.49  fof(f90,plain,(
% 0.21/0.49    v1_partfun1(sK1,sK0) | k1_xboole_0 = sK0 | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 0.21/0.49    inference(resolution,[],[f21,f34])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f29])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.21/0.49    inference(flattening,[],[f10])).
% 0.21/0.49  fof(f10,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (((v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.21/0.49    inference(ennf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_funct_2)).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.21/0.49    inference(cnf_transformation,[],[f16])).
% 0.21/0.49  fof(f152,plain,(
% 0.21/0.49    ~v1_partfun1(sK1,sK0) | sK1 = sK2 | k1_xboole_0 = sK0),
% 0.21/0.49    inference(resolution,[],[f141,f121])).
% 0.21/0.49  fof(f121,plain,(
% 0.21/0.49    v1_partfun1(sK2,sK0) | k1_xboole_0 = sK0),
% 0.21/0.49    inference(subsumption_resolution,[],[f120,f22])).
% 0.21/0.49  fof(f120,plain,(
% 0.21/0.49    v1_partfun1(sK2,sK0) | k1_xboole_0 = sK0 | ~v1_funct_1(sK2)),
% 0.21/0.49    inference(subsumption_resolution,[],[f109,f23])).
% 0.21/0.49  fof(f109,plain,(
% 0.21/0.49    v1_partfun1(sK2,sK0) | k1_xboole_0 = sK0 | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2)),
% 0.21/0.49    inference(resolution,[],[f24,f34])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.21/0.49    inference(cnf_transformation,[],[f16])).
% 0.21/0.49  fof(f141,plain,(
% 0.21/0.49    ~v1_partfun1(sK2,sK0) | ~v1_partfun1(sK1,sK0) | sK1 = sK2),
% 0.21/0.49    inference(subsumption_resolution,[],[f140,f22])).
% 0.21/0.49  fof(f140,plain,(
% 0.21/0.49    ~v1_partfun1(sK2,sK0) | ~v1_partfun1(sK1,sK0) | sK1 = sK2 | ~v1_funct_1(sK2)),
% 0.21/0.49    inference(subsumption_resolution,[],[f138,f25])).
% 0.21/0.49  fof(f138,plain,(
% 0.21/0.49    ~r1_partfun1(sK1,sK2) | ~v1_partfun1(sK2,sK0) | ~v1_partfun1(sK1,sK0) | sK1 = sK2 | ~v1_funct_1(sK2)),
% 0.21/0.49    inference(resolution,[],[f99,f24])).
% 0.21/0.49  fof(f99,plain,(
% 0.21/0.49    ( ! [X4] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~r1_partfun1(sK1,X4) | ~v1_partfun1(X4,sK0) | ~v1_partfun1(sK1,sK0) | sK1 = X4 | ~v1_funct_1(X4)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f88,f19])).
% 0.21/0.49  fof(f88,plain,(
% 0.21/0.49    ( ! [X4] : (sK1 = X4 | ~r1_partfun1(sK1,X4) | ~v1_partfun1(X4,sK0) | ~v1_partfun1(sK1,sK0) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(X4) | ~v1_funct_1(sK1)) )),
% 0.21/0.49    inference(resolution,[],[f21,f31])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (! [X3] : (X2 = X3 | ~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.21/0.49    inference(flattening,[],[f12])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (! [X3] : ((X2 = X3 | (~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.21/0.49    inference(ennf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ((r1_partfun1(X2,X3) & v1_partfun1(X3,X0) & v1_partfun1(X2,X0)) => X2 = X3)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_partfun1)).
% 0.21/0.49  fof(f200,plain,(
% 0.21/0.49    k1_funct_1(sK1,sK3(sK0,sK1,sK2)) != k1_funct_1(sK2,sK3(sK0,sK1,sK2))),
% 0.21/0.49    inference(subsumption_resolution,[],[f199,f21])).
% 0.21/0.49  fof(f199,plain,(
% 0.21/0.49    k1_funct_1(sK1,sK3(sK0,sK1,sK2)) != k1_funct_1(sK2,sK3(sK0,sK1,sK2)) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.21/0.49    inference(subsumption_resolution,[],[f83,f24])).
% 0.21/0.49  fof(f83,plain,(
% 0.21/0.49    k1_funct_1(sK1,sK3(sK0,sK1,sK2)) != k1_funct_1(sK2,sK3(sK0,sK1,sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.21/0.49    inference(subsumption_resolution,[],[f82,f19])).
% 0.21/0.49  fof(f82,plain,(
% 0.21/0.49    k1_funct_1(sK1,sK3(sK0,sK1,sK2)) != k1_funct_1(sK2,sK3(sK0,sK1,sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1)),
% 0.21/0.49    inference(subsumption_resolution,[],[f81,f20])).
% 0.21/0.49  fof(f81,plain,(
% 0.21/0.49    k1_funct_1(sK1,sK3(sK0,sK1,sK2)) != k1_funct_1(sK2,sK3(sK0,sK1,sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 0.21/0.49    inference(subsumption_resolution,[],[f80,f22])).
% 0.21/0.49  fof(f80,plain,(
% 0.21/0.49    k1_funct_1(sK1,sK3(sK0,sK1,sK2)) != k1_funct_1(sK2,sK3(sK0,sK1,sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 0.21/0.49    inference(subsumption_resolution,[],[f75,f23])).
% 0.21/0.49  fof(f75,plain,(
% 0.21/0.49    k1_funct_1(sK1,sK3(sK0,sK1,sK2)) != k1_funct_1(sK2,sK3(sK0,sK1,sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 0.21/0.49    inference(resolution,[],[f26,f28])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | k1_funct_1(X2,sK3(X0,X2,X3)) != k1_funct_1(X3,sK3(X0,X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (! [X3] : (r2_relset_1(X0,X1,X2,X3) | (k1_funct_1(X2,sK3(X0,X2,X3)) != k1_funct_1(X3,sK3(X0,X2,X3)) & m1_subset_1(sK3(X0,X2,X3),X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f9,f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ! [X3,X2,X0] : (? [X4] : (k1_funct_1(X2,X4) != k1_funct_1(X3,X4) & m1_subset_1(X4,X0)) => (k1_funct_1(X2,sK3(X0,X2,X3)) != k1_funct_1(X3,sK3(X0,X2,X3)) & m1_subset_1(sK3(X0,X2,X3),X0)))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f9,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (! [X3] : (r2_relset_1(X0,X1,X2,X3) | ? [X4] : (k1_funct_1(X2,X4) != k1_funct_1(X3,X4) & m1_subset_1(X4,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.21/0.49    inference(flattening,[],[f8])).
% 0.21/0.49  fof(f8,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (! [X3] : ((r2_relset_1(X0,X1,X2,X3) | ? [X4] : (k1_funct_1(X2,X4) != k1_funct_1(X3,X4) & m1_subset_1(X4,X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.21/0.49    inference(ennf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (m1_subset_1(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_funct_2)).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ~r2_relset_1(sK0,sK0,sK1,sK2)),
% 0.21/0.49    inference(cnf_transformation,[],[f16])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    v1_funct_2(sK2,sK0,sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f16])).
% 0.21/0.49  fof(f305,plain,(
% 0.21/0.49    v1_partfun1(sK2,k1_xboole_0) | ~v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) | ~v1_funct_1(sK2)),
% 0.21/0.49    inference(resolution,[],[f207,f33])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    ( ! [X2,X1] : (v1_partfun1(X2,k1_xboole_0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~v1_funct_1(X2)) )),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f32])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    ( ! [X2,X1] : (v1_partfun1(X2,k1_xboole_0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_1(X2)) )),
% 0.21/0.49    inference(equality_resolution,[],[f30])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f11])).
% 0.21/0.49  fof(f207,plain,(
% 0.21/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 0.21/0.49    inference(backward_demodulation,[],[f24,f202])).
% 0.21/0.49  fof(f349,plain,(
% 0.21/0.49    ~v1_partfun1(sK2,k1_xboole_0) | ~r1_partfun1(sK1,sK2) | sK1 = sK2 | ~v1_funct_1(sK2)),
% 0.21/0.49    inference(resolution,[],[f346,f207])).
% 0.21/0.49  fof(f346,plain,(
% 0.21/0.49    ( ! [X4] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~v1_partfun1(X4,k1_xboole_0) | ~r1_partfun1(sK1,X4) | sK1 = X4 | ~v1_funct_1(X4)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f228,f291])).
% 0.21/0.49  fof(f291,plain,(
% 0.21/0.49    v1_partfun1(sK1,k1_xboole_0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f290,f19])).
% 0.21/0.49  fof(f290,plain,(
% 0.21/0.49    v1_partfun1(sK1,k1_xboole_0) | ~v1_funct_1(sK1)),
% 0.21/0.49    inference(subsumption_resolution,[],[f280,f204])).
% 0.21/0.49  fof(f204,plain,(
% 0.21/0.49    v1_funct_2(sK1,k1_xboole_0,k1_xboole_0)),
% 0.21/0.49    inference(backward_demodulation,[],[f20,f202])).
% 0.21/0.49  fof(f280,plain,(
% 0.21/0.49    v1_partfun1(sK1,k1_xboole_0) | ~v1_funct_2(sK1,k1_xboole_0,k1_xboole_0) | ~v1_funct_1(sK1)),
% 0.21/0.49    inference(resolution,[],[f205,f33])).
% 0.21/0.49  fof(f205,plain,(
% 0.21/0.49    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 0.21/0.49    inference(backward_demodulation,[],[f21,f202])).
% 0.21/0.49  fof(f228,plain,(
% 0.21/0.49    ( ! [X4] : (~v1_partfun1(sK1,k1_xboole_0) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~v1_partfun1(X4,k1_xboole_0) | ~r1_partfun1(sK1,X4) | sK1 = X4 | ~v1_funct_1(X4)) )),
% 0.21/0.49    inference(forward_demodulation,[],[f227,f202])).
% 0.21/0.49  fof(f227,plain,(
% 0.21/0.49    ( ! [X4] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~v1_partfun1(X4,k1_xboole_0) | ~r1_partfun1(sK1,X4) | ~v1_partfun1(sK1,sK0) | sK1 = X4 | ~v1_funct_1(X4)) )),
% 0.21/0.49    inference(forward_demodulation,[],[f211,f202])).
% 0.21/0.49  fof(f211,plain,(
% 0.21/0.49    ( ! [X4] : (~v1_partfun1(X4,k1_xboole_0) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~r1_partfun1(sK1,X4) | ~v1_partfun1(sK1,sK0) | sK1 = X4 | ~v1_funct_1(X4)) )),
% 0.21/0.49    inference(backward_demodulation,[],[f99,f202])).
% 0.21/0.49  fof(f220,plain,(
% 0.21/0.49    k1_funct_1(sK1,sK3(k1_xboole_0,sK1,sK2)) != k1_funct_1(sK2,sK3(k1_xboole_0,sK1,sK2))),
% 0.21/0.49    inference(backward_demodulation,[],[f200,f202])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (27753)------------------------------
% 0.21/0.49  % (27753)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (27753)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (27753)Memory used [KB]: 1791
% 0.21/0.49  % (27753)Time elapsed: 0.070 s
% 0.21/0.49  % (27753)------------------------------
% 0.21/0.49  % (27753)------------------------------
% 0.21/0.49  % (27734)Success in time 0.129 s
%------------------------------------------------------------------------------
