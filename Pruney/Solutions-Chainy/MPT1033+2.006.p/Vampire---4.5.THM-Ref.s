%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:43 EST 2020

% Result     : Theorem 1.44s
% Output     : Refutation 1.44s
% Verified   : 
% Statistics : Number of formulae       :  165 (7263 expanded)
%              Number of leaves         :   23 (2287 expanded)
%              Depth                    :   34
%              Number of atoms          :  580 (61318 expanded)
%              Number of equality atoms :  132 (12225 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2048,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1988,f906])).

fof(f906,plain,(
    r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,sK2) ),
    inference(subsumption_resolution,[],[f897,f879])).

fof(f879,plain,(
    ~ sP10(k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f777,f813])).

fof(f813,plain,(
    k1_xboole_0 = sK0 ),
    inference(trivial_inequality_removal,[],[f812])).

fof(f812,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f66,f768])).

fof(f768,plain,(
    k1_xboole_0 = sK1 ),
    inference(resolution,[],[f767,f73])).

fof(f73,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f767,plain,(
    v1_xboole_0(sK1) ),
    inference(subsumption_resolution,[],[f733,f257])).

fof(f257,plain,(
    r2_relset_1(sK0,sK1,sK2,sK2) ),
    inference(subsumption_resolution,[],[f143,f144])).

fof(f144,plain,(
    ~ sP10(sK1,sK0) ),
    inference(resolution,[],[f61,f104])).

fof(f104,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ sP10(X1,X0) ) ),
    inference(general_splitting,[],[f96,f103_D])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP10(X1,X0) ) ),
    inference(cnf_transformation,[],[f103_D])).

fof(f103_D,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_relset_1(X0,X1,X2,X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    <=> ~ sP10(X1,X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP10])])).

fof(f96,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => r2_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

fof(f61,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,
    ( ~ r2_relset_1(sK0,sK1,sK2,sK3)
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_partfun1(sK2,sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f23,f45,f44])).

fof(f44,plain,
    ( ? [X0,X1,X2] :
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
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ~ r2_relset_1(sK0,sK1,sK2,X3)
          & ( k1_xboole_0 = sK0
            | k1_xboole_0 != sK1 )
          & r1_partfun1(sK2,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
          & v1_funct_2(X3,sK0,sK1)
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ? [X3] :
        ( ~ r2_relset_1(sK0,sK1,sK2,X3)
        & ( k1_xboole_0 = sK0
          | k1_xboole_0 != sK1 )
        & r1_partfun1(sK2,X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        & v1_funct_2(X3,sK0,sK1)
        & v1_funct_1(X3) )
   => ( ~ r2_relset_1(sK0,sK1,sK2,sK3)
      & ( k1_xboole_0 = sK0
        | k1_xboole_0 != sK1 )
      & r1_partfun1(sK2,sK3)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
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
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_2)).

fof(f143,plain,
    ( r2_relset_1(sK0,sK1,sK2,sK2)
    | sP10(sK1,sK0) ),
    inference(resolution,[],[f61,f103])).

fof(f733,plain,
    ( ~ r2_relset_1(sK0,sK1,sK2,sK2)
    | v1_xboole_0(sK1) ),
    inference(superposition,[],[f67,f727])).

fof(f727,plain,
    ( sK2 = sK3
    | v1_xboole_0(sK1) ),
    inference(subsumption_resolution,[],[f725,f150])).

fof(f150,plain,
    ( v1_partfun1(sK2,sK0)
    | v1_xboole_0(sK1) ),
    inference(subsumption_resolution,[],[f149,f59])).

fof(f59,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f149,plain,
    ( v1_partfun1(sK2,sK0)
    | ~ v1_funct_1(sK2)
    | v1_xboole_0(sK1) ),
    inference(subsumption_resolution,[],[f138,f60])).

fof(f60,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f138,plain,
    ( v1_partfun1(sK2,sK0)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f61,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f725,plain,
    ( ~ v1_partfun1(sK2,sK0)
    | sK2 = sK3
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f549,f165])).

fof(f165,plain,
    ( v1_partfun1(sK3,sK0)
    | v1_xboole_0(sK1) ),
    inference(subsumption_resolution,[],[f164,f62])).

fof(f62,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f46])).

fof(f164,plain,
    ( v1_partfun1(sK3,sK0)
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(sK1) ),
    inference(subsumption_resolution,[],[f153,f63])).

fof(f63,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f153,plain,
    ( v1_partfun1(sK3,sK0)
    | ~ v1_funct_2(sK3,sK0,sK1)
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f64,f84])).

fof(f64,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f46])).

fof(f549,plain,
    ( ~ v1_partfun1(sK3,sK0)
    | ~ v1_partfun1(sK2,sK0)
    | sK2 = sK3 ),
    inference(subsumption_resolution,[],[f548,f62])).

fof(f548,plain,
    ( ~ v1_partfun1(sK3,sK0)
    | ~ v1_partfun1(sK2,sK0)
    | sK2 = sK3
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f545,f65])).

fof(f65,plain,(
    r1_partfun1(sK2,sK3) ),
    inference(cnf_transformation,[],[f46])).

fof(f545,plain,
    ( ~ r1_partfun1(sK2,sK3)
    | ~ v1_partfun1(sK3,sK0)
    | ~ v1_partfun1(sK2,sK0)
    | sK2 = sK3
    | ~ v1_funct_1(sK3) ),
    inference(resolution,[],[f151,f64])).

fof(f151,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ r1_partfun1(sK2,X0)
      | ~ v1_partfun1(X0,sK0)
      | ~ v1_partfun1(sK2,sK0)
      | sK2 = X0
      | ~ v1_funct_1(X0) ) ),
    inference(subsumption_resolution,[],[f141,f59])).

fof(f141,plain,(
    ! [X0] :
      ( sK2 = X0
      | ~ r1_partfun1(sK2,X0)
      | ~ v1_partfun1(X0,sK0)
      | ~ v1_partfun1(sK2,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_1(X0)
      | ~ v1_funct_1(sK2) ) ),
    inference(resolution,[],[f61,f93])).

fof(f93,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r1_partfun1(X2,X3)
      | ~ v1_partfun1(X3,X0)
      | ~ v1_partfun1(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f37,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
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

fof(f67,plain,(
    ~ r2_relset_1(sK0,sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f46])).

fof(f66,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f46])).

fof(f777,plain,(
    ~ sP10(k1_xboole_0,sK0) ),
    inference(backward_demodulation,[],[f144,f768])).

fof(f897,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,sK2)
    | sP10(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[],[f875,f103])).

fof(f875,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f772,f813])).

fof(f772,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f61,f768])).

fof(f1988,plain,(
    ~ r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,sK2) ),
    inference(backward_demodulation,[],[f878,f1949])).

fof(f1949,plain,(
    sK2 = sK3 ),
    inference(subsumption_resolution,[],[f1948,f154])).

fof(f154,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f64,f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f1948,plain,
    ( sK2 = sK3
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f1928,f62])).

fof(f1928,plain,
    ( sK2 = sK3
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(trivial_inequality_removal,[],[f1927])).

fof(f1927,plain,
    ( k1_xboole_0 != k1_xboole_0
    | sK2 = sK3
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(superposition,[],[f1778,f1826])).

fof(f1826,plain,(
    k1_xboole_0 = k1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f1820,f1293])).

fof(f1293,plain,(
    sP9(k2_relat_1(sK3)) ),
    inference(subsumption_resolution,[],[f1287,f811])).

fof(f811,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(backward_demodulation,[],[f767,f768])).

fof(f1287,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | sP9(k2_relat_1(sK3)) ),
    inference(resolution,[],[f800,f101])).

fof(f101,plain,(
    ! [X2,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | sP9(X1) ) ),
    inference(cnf_transformation,[],[f101_D])).

fof(f101_D,plain,(
    ! [X1] :
      ( ! [X2] :
          ( ~ v1_xboole_0(X2)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) )
    <=> ~ sP9(X1) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP9])])).

fof(f800,plain,(
    m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(k1_xboole_0)) ),
    inference(backward_demodulation,[],[f245,f768])).

fof(f245,plain,(
    m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK1)) ),
    inference(resolution,[],[f216,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f216,plain,(
    r1_tarski(k2_relat_1(sK3),sK1) ),
    inference(subsumption_resolution,[],[f215,f154])).

fof(f215,plain,
    ( r1_tarski(k2_relat_1(sK3),sK1)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f155,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f155,plain,(
    v5_relat_1(sK3,sK1) ),
    inference(resolution,[],[f64,f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f1820,plain,
    ( k1_xboole_0 = k1_relat_1(sK3)
    | ~ sP9(k2_relat_1(sK3)) ),
    inference(resolution,[],[f1777,f340])).

fof(f340,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,k1_relat_1(sK3))
      | ~ sP9(k2_relat_1(sK3)) ) ),
    inference(resolution,[],[f335,f102])).

fof(f102,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ sP9(X1) ) ),
    inference(general_splitting,[],[f95,f101_D])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f335,plain,(
    ! [X16] :
      ( r2_hidden(k1_funct_1(sK3,X16),k2_relat_1(sK3))
      | ~ r2_hidden(X16,k1_relat_1(sK3)) ) ),
    inference(subsumption_resolution,[],[f128,f154])).

fof(f128,plain,(
    ! [X16] :
      ( r2_hidden(k1_funct_1(sK3,X16),k2_relat_1(sK3))
      | ~ r2_hidden(X16,k1_relat_1(sK3))
      | ~ v1_relat_1(sK3) ) ),
    inference(resolution,[],[f62,f98])).

fof(f98,plain,(
    ! [X6,X0] :
      ( r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0))
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f97])).

fof(f97,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X6),X1)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | k1_funct_1(X0,X6) != X5
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) != sK5(X0,X1)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                | ~ r2_hidden(sK5(X0,X1),X1) )
              & ( ( sK5(X0,X1) = k1_funct_1(X0,sK6(X0,X1))
                  & r2_hidden(sK6(X0,X1),k1_relat_1(X0)) )
                | r2_hidden(sK5(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK7(X0,X5)) = X5
                    & r2_hidden(sK7(X0,X5),k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f50,f53,f52,f51])).

fof(f51,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( k1_funct_1(X0,X3) != X2
                | ~ r2_hidden(X3,k1_relat_1(X0)) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( k1_funct_1(X0,X4) = X2
                & r2_hidden(X4,k1_relat_1(X0)) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( k1_funct_1(X0,X3) != sK5(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK5(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = sK5(X0,X1)
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( sK5(X0,X1) = k1_funct_1(X0,sK6(X0,X1))
        & r2_hidden(sK6(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK7(X0,X5)) = X5
        & r2_hidden(sK7(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X2
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ? [X7] :
                      ( k1_funct_1(X0,X7) = X5
                      & r2_hidden(X7,k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X2] :
                ( ( r2_hidden(X2,X1)
                  | ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) ) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

fof(f1777,plain,(
    ! [X4] :
      ( r2_hidden(sK5(sK2,X4),X4)
      | k1_xboole_0 = X4 ) ),
    inference(backward_demodulation,[],[f1722,f1746])).

fof(f1746,plain,(
    k1_xboole_0 = k2_relat_1(sK2) ),
    inference(resolution,[],[f1722,f1506])).

fof(f1506,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[],[f1493,f102])).

fof(f1493,plain,(
    sP9(k1_xboole_0) ),
    inference(resolution,[],[f825,f68])).

fof(f68,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f825,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
      | sP9(X0) ) ),
    inference(resolution,[],[f811,f101])).

fof(f1722,plain,(
    ! [X4] :
      ( r2_hidden(sK5(sK2,X4),X4)
      | k2_relat_1(sK2) = X4 ) ),
    inference(subsumption_resolution,[],[f1703,f1164])).

fof(f1164,plain,(
    ! [X0] : ~ r2_hidden(X0,k2_relat_1(sK2)) ),
    inference(resolution,[],[f1148,f102])).

fof(f1148,plain,(
    sP9(k2_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f1142,f811])).

fof(f1142,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | sP9(k2_relat_1(sK2)) ),
    inference(resolution,[],[f797,f101])).

fof(f797,plain,(
    m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(k1_xboole_0)) ),
    inference(backward_demodulation,[],[f225,f768])).

fof(f225,plain,(
    m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) ),
    inference(resolution,[],[f213,f89])).

fof(f213,plain,(
    r1_tarski(k2_relat_1(sK2),sK1) ),
    inference(subsumption_resolution,[],[f212,f139])).

fof(f139,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f61,f91])).

fof(f212,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f140,f85])).

fof(f140,plain,(
    v5_relat_1(sK2,sK1) ),
    inference(resolution,[],[f61,f92])).

fof(f1703,plain,(
    ! [X4] :
      ( r2_hidden(sK6(sK2,X4),k2_relat_1(sK2))
      | k2_relat_1(sK2) = X4
      | r2_hidden(sK5(sK2,X4),X4) ) ),
    inference(backward_demodulation,[],[f423,f1684])).

fof(f1684,plain,(
    k1_relat_1(sK2) = k2_relat_1(sK2) ),
    inference(superposition,[],[f72,f1679])).

fof(f1679,plain,(
    sK2 = k6_relat_1(k1_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f1678,f1237])).

fof(f1237,plain,(
    ! [X2] : ~ r2_hidden(X2,k1_relat_1(sK2)) ),
    inference(resolution,[],[f1164,f288])).

fof(f288,plain,(
    ! [X16] :
      ( r2_hidden(k1_funct_1(sK2,X16),k2_relat_1(sK2))
      | ~ r2_hidden(X16,k1_relat_1(sK2)) ) ),
    inference(subsumption_resolution,[],[f115,f139])).

fof(f115,plain,(
    ! [X16] :
      ( r2_hidden(k1_funct_1(sK2,X16),k2_relat_1(sK2))
      | ~ r2_hidden(X16,k1_relat_1(sK2))
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f59,f98])).

fof(f1678,plain,
    ( r2_hidden(sK4(k6_relat_1(k1_relat_1(sK2)),sK2),k1_relat_1(sK2))
    | sK2 = k6_relat_1(k1_relat_1(sK2)) ),
    inference(equality_resolution,[],[f484])).

fof(f484,plain,(
    ! [X0] :
      ( k1_relat_1(sK2) != X0
      | r2_hidden(sK4(k6_relat_1(X0),sK2),X0)
      | k6_relat_1(X0) = sK2 ) ),
    inference(subsumption_resolution,[],[f483,f69])).

fof(f69,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f483,plain,(
    ! [X0] :
      ( k1_relat_1(sK2) != X0
      | r2_hidden(sK4(k6_relat_1(X0),sK2),X0)
      | k6_relat_1(X0) = sK2
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(subsumption_resolution,[],[f481,f70])).

fof(f70,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f481,plain,(
    ! [X0] :
      ( k1_relat_1(sK2) != X0
      | r2_hidden(sK4(k6_relat_1(X0),sK2),X0)
      | k6_relat_1(X0) = sK2
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f480,f71])).

fof(f71,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f480,plain,(
    ! [X1] :
      ( k1_relat_1(X1) != k1_relat_1(sK2)
      | r2_hidden(sK4(X1,sK2),k1_relat_1(X1))
      | sK2 = X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f106,f139])).

fof(f106,plain,(
    ! [X1] :
      ( sK2 = X1
      | r2_hidden(sK4(X1,sK2),k1_relat_1(X1))
      | k1_relat_1(X1) != k1_relat_1(sK2)
      | ~ v1_relat_1(sK2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f59,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK4(X0,X1),k1_relat_1(X0))
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ( k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1))
            & r2_hidden(sK4(X0,X1),k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f26,f47])).

fof(f47,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
          & r2_hidden(X2,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1))
        & r2_hidden(sK4(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ? [X2] :
              ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ? [X2] :
              ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( ! [X2] :
                  ( r2_hidden(X2,k1_relat_1(X0))
                 => k1_funct_1(X0,X2) = k1_funct_1(X1,X2) )
              & k1_relat_1(X0) = k1_relat_1(X1) )
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_1)).

fof(f72,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f423,plain,(
    ! [X4] :
      ( r2_hidden(sK6(sK2,X4),k1_relat_1(sK2))
      | k2_relat_1(sK2) = X4
      | r2_hidden(sK5(sK2,X4),X4) ) ),
    inference(subsumption_resolution,[],[f109,f139])).

fof(f109,plain,(
    ! [X4] :
      ( k2_relat_1(sK2) = X4
      | r2_hidden(sK6(sK2,X4),k1_relat_1(sK2))
      | r2_hidden(sK5(sK2,X4),X4)
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f59,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
      | r2_hidden(sK6(X0,X1),k1_relat_1(X0))
      | r2_hidden(sK5(X0,X1),X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f1778,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relat_1(X0)
      | sK2 = X0
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(backward_demodulation,[],[f1725,f1746])).

fof(f1725,plain,(
    ! [X0] :
      ( k1_relat_1(X0) != k2_relat_1(sK2)
      | sK2 = X0
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(forward_demodulation,[],[f1724,f1684])).

fof(f1724,plain,(
    ! [X0] :
      ( k1_relat_1(X0) != k1_relat_1(sK2)
      | sK2 = X0
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f1705,f1164])).

fof(f1705,plain,(
    ! [X0] :
      ( r2_hidden(sK4(sK2,X0),k2_relat_1(sK2))
      | k1_relat_1(X0) != k1_relat_1(sK2)
      | sK2 = X0
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(backward_demodulation,[],[f459,f1684])).

fof(f459,plain,(
    ! [X0] :
      ( k1_relat_1(X0) != k1_relat_1(sK2)
      | r2_hidden(sK4(sK2,X0),k1_relat_1(sK2))
      | sK2 = X0
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f105,f139])).

fof(f105,plain,(
    ! [X0] :
      ( sK2 = X0
      | r2_hidden(sK4(sK2,X0),k1_relat_1(sK2))
      | k1_relat_1(X0) != k1_relat_1(sK2)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f59,f74])).

fof(f878,plain,(
    ~ r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,sK3) ),
    inference(backward_demodulation,[],[f775,f813])).

fof(f775,plain,(
    ~ r2_relset_1(sK0,k1_xboole_0,sK2,sK3) ),
    inference(backward_demodulation,[],[f67,f768])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:37:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (3800)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.48  % (3816)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.50  % (3796)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.51  % (3803)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.52  % (3809)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.32/0.53  % (3819)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.32/0.53  % (3810)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.32/0.53  % (3794)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 1.32/0.54  % (3795)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.32/0.54  % (3811)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.32/0.54  % (3818)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.32/0.54  % (3797)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 1.32/0.54  % (3805)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 1.32/0.54  % (3799)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 1.44/0.54  % (3801)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.44/0.55  % (3799)Refutation not found, incomplete strategy% (3799)------------------------------
% 1.44/0.55  % (3799)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.55  % (3799)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.55  
% 1.44/0.55  % (3799)Memory used [KB]: 10618
% 1.44/0.55  % (3799)Time elapsed: 0.126 s
% 1.44/0.55  % (3799)------------------------------
% 1.44/0.55  % (3799)------------------------------
% 1.44/0.55  % (3798)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 1.44/0.55  % (3806)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.44/0.55  % (3808)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.44/0.55  % (3813)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.44/0.56  % (3817)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.44/0.56  % (3812)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.44/0.56  % (3815)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.44/0.56  % (3814)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.44/0.57  % (3802)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.44/0.57  % (3798)Refutation not found, incomplete strategy% (3798)------------------------------
% 1.44/0.57  % (3798)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.57  % (3798)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.57  
% 1.44/0.57  % (3798)Memory used [KB]: 6140
% 1.44/0.57  % (3798)Time elapsed: 0.132 s
% 1.44/0.57  % (3798)------------------------------
% 1.44/0.57  % (3798)------------------------------
% 1.44/0.57  % (3804)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.44/0.57  % (3793)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 1.44/0.58  % (3793)Refutation not found, incomplete strategy% (3793)------------------------------
% 1.44/0.58  % (3793)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.58  % (3793)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.58  
% 1.44/0.58  % (3793)Memory used [KB]: 10618
% 1.44/0.58  % (3793)Time elapsed: 0.142 s
% 1.44/0.58  % (3793)------------------------------
% 1.44/0.58  % (3793)------------------------------
% 1.44/0.62  % (3812)Refutation found. Thanks to Tanya!
% 1.44/0.62  % SZS status Theorem for theBenchmark
% 1.44/0.62  % SZS output start Proof for theBenchmark
% 1.44/0.62  fof(f2048,plain,(
% 1.44/0.62    $false),
% 1.44/0.62    inference(subsumption_resolution,[],[f1988,f906])).
% 1.44/0.62  fof(f906,plain,(
% 1.44/0.62    r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,sK2)),
% 1.44/0.62    inference(subsumption_resolution,[],[f897,f879])).
% 1.44/0.62  fof(f879,plain,(
% 1.44/0.62    ~sP10(k1_xboole_0,k1_xboole_0)),
% 1.44/0.62    inference(backward_demodulation,[],[f777,f813])).
% 1.44/0.62  fof(f813,plain,(
% 1.44/0.62    k1_xboole_0 = sK0),
% 1.44/0.62    inference(trivial_inequality_removal,[],[f812])).
% 1.44/0.62  fof(f812,plain,(
% 1.44/0.62    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0),
% 1.44/0.62    inference(superposition,[],[f66,f768])).
% 1.44/0.62  fof(f768,plain,(
% 1.44/0.62    k1_xboole_0 = sK1),
% 1.44/0.62    inference(resolution,[],[f767,f73])).
% 1.44/0.63  fof(f73,plain,(
% 1.44/0.63    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 1.44/0.63    inference(cnf_transformation,[],[f24])).
% 1.44/0.63  fof(f24,plain,(
% 1.44/0.63    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.44/0.63    inference(ennf_transformation,[],[f1])).
% 1.44/0.63  fof(f1,axiom,(
% 1.44/0.63    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.44/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 1.44/0.63  fof(f767,plain,(
% 1.44/0.63    v1_xboole_0(sK1)),
% 1.44/0.63    inference(subsumption_resolution,[],[f733,f257])).
% 1.44/0.63  fof(f257,plain,(
% 1.44/0.63    r2_relset_1(sK0,sK1,sK2,sK2)),
% 1.44/0.63    inference(subsumption_resolution,[],[f143,f144])).
% 1.44/0.63  fof(f144,plain,(
% 1.44/0.63    ~sP10(sK1,sK0)),
% 1.44/0.63    inference(resolution,[],[f61,f104])).
% 1.44/0.63  fof(f104,plain,(
% 1.44/0.63    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~sP10(X1,X0)) )),
% 1.44/0.63    inference(general_splitting,[],[f96,f103_D])).
% 1.44/0.63  fof(f103,plain,(
% 1.44/0.63    ( ! [X2,X0,X1] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP10(X1,X0)) )),
% 1.44/0.63    inference(cnf_transformation,[],[f103_D])).
% 1.44/0.63  fof(f103_D,plain,(
% 1.44/0.63    ( ! [X0,X1] : (( ! [X2] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) <=> ~sP10(X1,X0)) )),
% 1.44/0.63    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP10])])).
% 1.44/0.63  fof(f96,plain,(
% 1.44/0.63    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.44/0.63    inference(cnf_transformation,[],[f43])).
% 1.44/0.63  fof(f43,plain,(
% 1.44/0.63    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.44/0.63    inference(flattening,[],[f42])).
% 1.44/0.63  fof(f42,plain,(
% 1.44/0.63    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.44/0.63    inference(ennf_transformation,[],[f16])).
% 1.44/0.63  fof(f16,axiom,(
% 1.44/0.63    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => r2_relset_1(X0,X1,X2,X2))),
% 1.44/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).
% 1.44/0.63  fof(f61,plain,(
% 1.44/0.63    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.44/0.63    inference(cnf_transformation,[],[f46])).
% 1.44/0.63  fof(f46,plain,(
% 1.44/0.63    (~r2_relset_1(sK0,sK1,sK2,sK3) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_partfun1(sK2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 1.44/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f23,f45,f44])).
% 1.44/0.63  fof(f44,plain,(
% 1.44/0.63    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_partfun1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (~r2_relset_1(sK0,sK1,sK2,X3) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_partfun1(sK2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(X3,sK0,sK1) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 1.44/0.63    introduced(choice_axiom,[])).
% 1.44/0.63  fof(f45,plain,(
% 1.44/0.63    ? [X3] : (~r2_relset_1(sK0,sK1,sK2,X3) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_partfun1(sK2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(X3,sK0,sK1) & v1_funct_1(X3)) => (~r2_relset_1(sK0,sK1,sK2,sK3) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_partfun1(sK2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 1.44/0.63    introduced(choice_axiom,[])).
% 1.44/0.63  fof(f23,plain,(
% 1.44/0.63    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_partfun1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.44/0.63    inference(flattening,[],[f22])).
% 1.44/0.63  fof(f22,plain,(
% 1.44/0.63    ? [X0,X1,X2] : (? [X3] : (((~r2_relset_1(X0,X1,X2,X3) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_partfun1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.44/0.63    inference(ennf_transformation,[],[f20])).
% 1.44/0.63  fof(f20,negated_conjecture,(
% 1.44/0.63    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_partfun1(X2,X3) => (r2_relset_1(X0,X1,X2,X3) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)))))),
% 1.44/0.63    inference(negated_conjecture,[],[f19])).
% 1.44/0.63  fof(f19,conjecture,(
% 1.44/0.63    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_partfun1(X2,X3) => (r2_relset_1(X0,X1,X2,X3) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)))))),
% 1.44/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_2)).
% 1.44/0.63  fof(f143,plain,(
% 1.44/0.63    r2_relset_1(sK0,sK1,sK2,sK2) | sP10(sK1,sK0)),
% 1.44/0.63    inference(resolution,[],[f61,f103])).
% 1.44/0.63  fof(f733,plain,(
% 1.44/0.63    ~r2_relset_1(sK0,sK1,sK2,sK2) | v1_xboole_0(sK1)),
% 1.44/0.63    inference(superposition,[],[f67,f727])).
% 1.44/0.63  fof(f727,plain,(
% 1.44/0.63    sK2 = sK3 | v1_xboole_0(sK1)),
% 1.44/0.63    inference(subsumption_resolution,[],[f725,f150])).
% 1.44/0.63  fof(f150,plain,(
% 1.44/0.63    v1_partfun1(sK2,sK0) | v1_xboole_0(sK1)),
% 1.44/0.63    inference(subsumption_resolution,[],[f149,f59])).
% 1.44/0.63  fof(f59,plain,(
% 1.44/0.63    v1_funct_1(sK2)),
% 1.44/0.63    inference(cnf_transformation,[],[f46])).
% 1.44/0.63  fof(f149,plain,(
% 1.44/0.63    v1_partfun1(sK2,sK0) | ~v1_funct_1(sK2) | v1_xboole_0(sK1)),
% 1.44/0.63    inference(subsumption_resolution,[],[f138,f60])).
% 1.44/0.63  fof(f60,plain,(
% 1.44/0.63    v1_funct_2(sK2,sK0,sK1)),
% 1.44/0.63    inference(cnf_transformation,[],[f46])).
% 1.44/0.63  fof(f138,plain,(
% 1.44/0.63    v1_partfun1(sK2,sK0) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | v1_xboole_0(sK1)),
% 1.44/0.63    inference(resolution,[],[f61,f84])).
% 1.44/0.63  fof(f84,plain,(
% 1.44/0.63    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 1.44/0.63    inference(cnf_transformation,[],[f30])).
% 1.44/0.63  fof(f30,plain,(
% 1.44/0.63    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 1.44/0.63    inference(flattening,[],[f29])).
% 1.44/0.63  fof(f29,plain,(
% 1.44/0.63    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 1.44/0.63    inference(ennf_transformation,[],[f17])).
% 1.44/0.63  fof(f17,axiom,(
% 1.44/0.63    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 1.44/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).
% 1.44/0.63  fof(f725,plain,(
% 1.44/0.63    ~v1_partfun1(sK2,sK0) | sK2 = sK3 | v1_xboole_0(sK1)),
% 1.44/0.63    inference(resolution,[],[f549,f165])).
% 1.44/0.63  fof(f165,plain,(
% 1.44/0.63    v1_partfun1(sK3,sK0) | v1_xboole_0(sK1)),
% 1.44/0.63    inference(subsumption_resolution,[],[f164,f62])).
% 1.44/0.63  fof(f62,plain,(
% 1.44/0.63    v1_funct_1(sK3)),
% 1.44/0.63    inference(cnf_transformation,[],[f46])).
% 1.44/0.63  fof(f164,plain,(
% 1.44/0.63    v1_partfun1(sK3,sK0) | ~v1_funct_1(sK3) | v1_xboole_0(sK1)),
% 1.44/0.63    inference(subsumption_resolution,[],[f153,f63])).
% 1.44/0.63  fof(f63,plain,(
% 1.44/0.63    v1_funct_2(sK3,sK0,sK1)),
% 1.44/0.63    inference(cnf_transformation,[],[f46])).
% 1.44/0.63  fof(f153,plain,(
% 1.44/0.63    v1_partfun1(sK3,sK0) | ~v1_funct_2(sK3,sK0,sK1) | ~v1_funct_1(sK3) | v1_xboole_0(sK1)),
% 1.44/0.63    inference(resolution,[],[f64,f84])).
% 1.44/0.63  fof(f64,plain,(
% 1.44/0.63    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.44/0.63    inference(cnf_transformation,[],[f46])).
% 1.44/0.63  fof(f549,plain,(
% 1.44/0.63    ~v1_partfun1(sK3,sK0) | ~v1_partfun1(sK2,sK0) | sK2 = sK3),
% 1.44/0.63    inference(subsumption_resolution,[],[f548,f62])).
% 1.44/0.63  fof(f548,plain,(
% 1.44/0.63    ~v1_partfun1(sK3,sK0) | ~v1_partfun1(sK2,sK0) | sK2 = sK3 | ~v1_funct_1(sK3)),
% 1.44/0.63    inference(subsumption_resolution,[],[f545,f65])).
% 1.44/0.63  fof(f65,plain,(
% 1.44/0.63    r1_partfun1(sK2,sK3)),
% 1.44/0.63    inference(cnf_transformation,[],[f46])).
% 1.44/0.63  fof(f545,plain,(
% 1.44/0.63    ~r1_partfun1(sK2,sK3) | ~v1_partfun1(sK3,sK0) | ~v1_partfun1(sK2,sK0) | sK2 = sK3 | ~v1_funct_1(sK3)),
% 1.44/0.63    inference(resolution,[],[f151,f64])).
% 1.44/0.63  fof(f151,plain,(
% 1.44/0.63    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~r1_partfun1(sK2,X0) | ~v1_partfun1(X0,sK0) | ~v1_partfun1(sK2,sK0) | sK2 = X0 | ~v1_funct_1(X0)) )),
% 1.44/0.63    inference(subsumption_resolution,[],[f141,f59])).
% 1.44/0.63  fof(f141,plain,(
% 1.44/0.63    ( ! [X0] : (sK2 = X0 | ~r1_partfun1(sK2,X0) | ~v1_partfun1(X0,sK0) | ~v1_partfun1(sK2,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(X0) | ~v1_funct_1(sK2)) )),
% 1.44/0.63    inference(resolution,[],[f61,f93])).
% 1.44/0.63  fof(f93,plain,(
% 1.44/0.63    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 1.44/0.63    inference(cnf_transformation,[],[f38])).
% 1.44/0.63  fof(f38,plain,(
% 1.44/0.63    ! [X0,X1,X2] : (! [X3] : (X2 = X3 | ~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.44/0.63    inference(flattening,[],[f37])).
% 1.44/0.63  fof(f37,plain,(
% 1.44/0.63    ! [X0,X1,X2] : (! [X3] : ((X2 = X3 | (~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.44/0.63    inference(ennf_transformation,[],[f18])).
% 1.44/0.63  fof(f18,axiom,(
% 1.44/0.63    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ((r1_partfun1(X2,X3) & v1_partfun1(X3,X0) & v1_partfun1(X2,X0)) => X2 = X3)))),
% 1.44/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_partfun1)).
% 1.44/0.63  fof(f67,plain,(
% 1.44/0.63    ~r2_relset_1(sK0,sK1,sK2,sK3)),
% 1.44/0.63    inference(cnf_transformation,[],[f46])).
% 1.44/0.63  fof(f66,plain,(
% 1.44/0.63    k1_xboole_0 != sK1 | k1_xboole_0 = sK0),
% 1.44/0.63    inference(cnf_transformation,[],[f46])).
% 1.44/0.63  fof(f777,plain,(
% 1.44/0.63    ~sP10(k1_xboole_0,sK0)),
% 1.44/0.63    inference(backward_demodulation,[],[f144,f768])).
% 1.44/0.63  fof(f897,plain,(
% 1.44/0.63    r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,sK2) | sP10(k1_xboole_0,k1_xboole_0)),
% 1.44/0.63    inference(resolution,[],[f875,f103])).
% 1.44/0.63  fof(f875,plain,(
% 1.44/0.63    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 1.44/0.63    inference(backward_demodulation,[],[f772,f813])).
% 1.44/0.63  fof(f772,plain,(
% 1.44/0.63    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))),
% 1.44/0.63    inference(backward_demodulation,[],[f61,f768])).
% 1.44/0.63  fof(f1988,plain,(
% 1.44/0.63    ~r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,sK2)),
% 1.44/0.63    inference(backward_demodulation,[],[f878,f1949])).
% 1.44/0.63  fof(f1949,plain,(
% 1.44/0.63    sK2 = sK3),
% 1.44/0.63    inference(subsumption_resolution,[],[f1948,f154])).
% 1.44/0.63  fof(f154,plain,(
% 1.44/0.63    v1_relat_1(sK3)),
% 1.44/0.63    inference(resolution,[],[f64,f91])).
% 1.44/0.63  fof(f91,plain,(
% 1.44/0.63    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.44/0.63    inference(cnf_transformation,[],[f35])).
% 1.44/0.63  fof(f35,plain,(
% 1.44/0.63    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.44/0.63    inference(ennf_transformation,[],[f14])).
% 1.44/0.63  fof(f14,axiom,(
% 1.44/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.44/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.44/0.63  fof(f1948,plain,(
% 1.44/0.63    sK2 = sK3 | ~v1_relat_1(sK3)),
% 1.44/0.63    inference(subsumption_resolution,[],[f1928,f62])).
% 1.44/0.63  fof(f1928,plain,(
% 1.44/0.63    sK2 = sK3 | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)),
% 1.44/0.63    inference(trivial_inequality_removal,[],[f1927])).
% 1.44/0.63  fof(f1927,plain,(
% 1.44/0.63    k1_xboole_0 != k1_xboole_0 | sK2 = sK3 | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)),
% 1.44/0.63    inference(superposition,[],[f1778,f1826])).
% 1.44/0.63  fof(f1826,plain,(
% 1.44/0.63    k1_xboole_0 = k1_relat_1(sK3)),
% 1.44/0.63    inference(subsumption_resolution,[],[f1820,f1293])).
% 1.44/0.63  fof(f1293,plain,(
% 1.44/0.63    sP9(k2_relat_1(sK3))),
% 1.44/0.63    inference(subsumption_resolution,[],[f1287,f811])).
% 1.44/0.63  fof(f811,plain,(
% 1.44/0.63    v1_xboole_0(k1_xboole_0)),
% 1.44/0.63    inference(backward_demodulation,[],[f767,f768])).
% 1.44/0.63  fof(f1287,plain,(
% 1.44/0.63    ~v1_xboole_0(k1_xboole_0) | sP9(k2_relat_1(sK3))),
% 1.44/0.63    inference(resolution,[],[f800,f101])).
% 1.44/0.63  fof(f101,plain,(
% 1.44/0.63    ( ! [X2,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | sP9(X1)) )),
% 1.44/0.63    inference(cnf_transformation,[],[f101_D])).
% 1.44/0.63  fof(f101_D,plain,(
% 1.44/0.63    ( ! [X1] : (( ! [X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2))) ) <=> ~sP9(X1)) )),
% 1.44/0.63    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP9])])).
% 1.44/0.63  fof(f800,plain,(
% 1.44/0.63    m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(k1_xboole_0))),
% 1.44/0.63    inference(backward_demodulation,[],[f245,f768])).
% 1.44/0.63  fof(f245,plain,(
% 1.44/0.63    m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK1))),
% 1.44/0.63    inference(resolution,[],[f216,f89])).
% 1.44/0.63  fof(f89,plain,(
% 1.44/0.63    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.44/0.63    inference(cnf_transformation,[],[f58])).
% 1.44/0.63  fof(f58,plain,(
% 1.44/0.63    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.44/0.63    inference(nnf_transformation,[],[f5])).
% 1.44/0.63  fof(f5,axiom,(
% 1.44/0.63    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.44/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.44/0.63  fof(f216,plain,(
% 1.44/0.63    r1_tarski(k2_relat_1(sK3),sK1)),
% 1.44/0.63    inference(subsumption_resolution,[],[f215,f154])).
% 1.44/0.63  fof(f215,plain,(
% 1.44/0.63    r1_tarski(k2_relat_1(sK3),sK1) | ~v1_relat_1(sK3)),
% 1.44/0.63    inference(resolution,[],[f155,f85])).
% 1.44/0.63  fof(f85,plain,(
% 1.44/0.63    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.44/0.63    inference(cnf_transformation,[],[f57])).
% 1.44/0.63  fof(f57,plain,(
% 1.44/0.63    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.44/0.63    inference(nnf_transformation,[],[f31])).
% 1.44/0.63  fof(f31,plain,(
% 1.44/0.63    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.44/0.63    inference(ennf_transformation,[],[f8])).
% 1.44/0.63  fof(f8,axiom,(
% 1.44/0.63    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.44/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 1.44/0.63  fof(f155,plain,(
% 1.44/0.63    v5_relat_1(sK3,sK1)),
% 1.44/0.63    inference(resolution,[],[f64,f92])).
% 1.44/0.63  fof(f92,plain,(
% 1.44/0.63    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.44/0.63    inference(cnf_transformation,[],[f36])).
% 1.44/0.63  fof(f36,plain,(
% 1.44/0.63    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.44/0.63    inference(ennf_transformation,[],[f21])).
% 1.44/0.63  fof(f21,plain,(
% 1.44/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 1.44/0.63    inference(pure_predicate_removal,[],[f15])).
% 1.44/0.63  fof(f15,axiom,(
% 1.44/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.44/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.44/0.63  fof(f1820,plain,(
% 1.44/0.63    k1_xboole_0 = k1_relat_1(sK3) | ~sP9(k2_relat_1(sK3))),
% 1.44/0.63    inference(resolution,[],[f1777,f340])).
% 1.44/0.63  fof(f340,plain,(
% 1.44/0.63    ( ! [X5] : (~r2_hidden(X5,k1_relat_1(sK3)) | ~sP9(k2_relat_1(sK3))) )),
% 1.44/0.63    inference(resolution,[],[f335,f102])).
% 1.44/0.63  fof(f102,plain,(
% 1.44/0.63    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~sP9(X1)) )),
% 1.44/0.63    inference(general_splitting,[],[f95,f101_D])).
% 1.44/0.63  fof(f95,plain,(
% 1.44/0.63    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 1.44/0.63    inference(cnf_transformation,[],[f41])).
% 1.44/0.63  fof(f41,plain,(
% 1.44/0.63    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.44/0.63    inference(ennf_transformation,[],[f7])).
% 1.44/0.63  fof(f7,axiom,(
% 1.44/0.63    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 1.44/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 1.44/0.63  fof(f335,plain,(
% 1.44/0.63    ( ! [X16] : (r2_hidden(k1_funct_1(sK3,X16),k2_relat_1(sK3)) | ~r2_hidden(X16,k1_relat_1(sK3))) )),
% 1.44/0.63    inference(subsumption_resolution,[],[f128,f154])).
% 1.44/0.63  fof(f128,plain,(
% 1.44/0.63    ( ! [X16] : (r2_hidden(k1_funct_1(sK3,X16),k2_relat_1(sK3)) | ~r2_hidden(X16,k1_relat_1(sK3)) | ~v1_relat_1(sK3)) )),
% 1.44/0.63    inference(resolution,[],[f62,f98])).
% 1.44/0.63  fof(f98,plain,(
% 1.44/0.63    ( ! [X6,X0] : (r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0)) | ~r2_hidden(X6,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.44/0.63    inference(equality_resolution,[],[f97])).
% 1.44/0.63  fof(f97,plain,(
% 1.44/0.63    ( ! [X6,X0,X1] : (r2_hidden(k1_funct_1(X0,X6),X1) | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.44/0.63    inference(equality_resolution,[],[f78])).
% 1.44/0.63  fof(f78,plain,(
% 1.44/0.63    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.44/0.63    inference(cnf_transformation,[],[f54])).
% 1.44/0.63  fof(f54,plain,(
% 1.44/0.63    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK5(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK5(X0,X1),X1)) & ((sK5(X0,X1) = k1_funct_1(X0,sK6(X0,X1)) & r2_hidden(sK6(X0,X1),k1_relat_1(X0))) | r2_hidden(sK5(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK7(X0,X5)) = X5 & r2_hidden(sK7(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.44/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f50,f53,f52,f51])).
% 1.44/0.63  fof(f51,plain,(
% 1.44/0.63    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK5(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK5(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK5(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK5(X0,X1),X1))))),
% 1.44/0.63    introduced(choice_axiom,[])).
% 1.44/0.63  fof(f52,plain,(
% 1.44/0.63    ! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = sK5(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) => (sK5(X0,X1) = k1_funct_1(X0,sK6(X0,X1)) & r2_hidden(sK6(X0,X1),k1_relat_1(X0))))),
% 1.44/0.63    introduced(choice_axiom,[])).
% 1.44/0.63  fof(f53,plain,(
% 1.44/0.63    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK7(X0,X5)) = X5 & r2_hidden(sK7(X0,X5),k1_relat_1(X0))))),
% 1.44/0.63    introduced(choice_axiom,[])).
% 1.44/0.63  fof(f50,plain,(
% 1.44/0.63    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.44/0.63    inference(rectify,[],[f49])).
% 1.44/0.63  fof(f49,plain,(
% 1.44/0.63    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.44/0.63    inference(nnf_transformation,[],[f28])).
% 1.44/0.63  fof(f28,plain,(
% 1.44/0.63    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.44/0.63    inference(flattening,[],[f27])).
% 1.44/0.63  fof(f27,plain,(
% 1.44/0.63    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.44/0.63    inference(ennf_transformation,[],[f10])).
% 1.44/0.63  fof(f10,axiom,(
% 1.44/0.63    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 1.44/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).
% 1.44/0.63  fof(f1777,plain,(
% 1.44/0.63    ( ! [X4] : (r2_hidden(sK5(sK2,X4),X4) | k1_xboole_0 = X4) )),
% 1.44/0.63    inference(backward_demodulation,[],[f1722,f1746])).
% 1.44/0.63  fof(f1746,plain,(
% 1.44/0.63    k1_xboole_0 = k2_relat_1(sK2)),
% 1.44/0.63    inference(resolution,[],[f1722,f1506])).
% 1.44/0.63  fof(f1506,plain,(
% 1.44/0.63    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.44/0.63    inference(resolution,[],[f1493,f102])).
% 1.44/0.63  fof(f1493,plain,(
% 1.44/0.63    sP9(k1_xboole_0)),
% 1.44/0.63    inference(resolution,[],[f825,f68])).
% 1.44/0.63  fof(f68,plain,(
% 1.44/0.63    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.44/0.63    inference(cnf_transformation,[],[f3])).
% 1.44/0.63  fof(f3,axiom,(
% 1.44/0.63    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.44/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 1.44/0.63  fof(f825,plain,(
% 1.44/0.63    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | sP9(X0)) )),
% 1.44/0.63    inference(resolution,[],[f811,f101])).
% 1.44/0.63  fof(f1722,plain,(
% 1.44/0.63    ( ! [X4] : (r2_hidden(sK5(sK2,X4),X4) | k2_relat_1(sK2) = X4) )),
% 1.44/0.63    inference(subsumption_resolution,[],[f1703,f1164])).
% 1.44/0.63  fof(f1164,plain,(
% 1.44/0.63    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK2))) )),
% 1.44/0.63    inference(resolution,[],[f1148,f102])).
% 1.44/0.63  fof(f1148,plain,(
% 1.44/0.63    sP9(k2_relat_1(sK2))),
% 1.44/0.63    inference(subsumption_resolution,[],[f1142,f811])).
% 1.44/0.63  fof(f1142,plain,(
% 1.44/0.63    ~v1_xboole_0(k1_xboole_0) | sP9(k2_relat_1(sK2))),
% 1.44/0.63    inference(resolution,[],[f797,f101])).
% 1.44/0.63  fof(f797,plain,(
% 1.44/0.63    m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(k1_xboole_0))),
% 1.44/0.63    inference(backward_demodulation,[],[f225,f768])).
% 1.44/0.63  fof(f225,plain,(
% 1.44/0.63    m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1))),
% 1.44/0.63    inference(resolution,[],[f213,f89])).
% 1.44/0.63  fof(f213,plain,(
% 1.44/0.63    r1_tarski(k2_relat_1(sK2),sK1)),
% 1.44/0.63    inference(subsumption_resolution,[],[f212,f139])).
% 1.44/0.63  fof(f139,plain,(
% 1.44/0.63    v1_relat_1(sK2)),
% 1.44/0.63    inference(resolution,[],[f61,f91])).
% 1.44/0.63  fof(f212,plain,(
% 1.44/0.63    r1_tarski(k2_relat_1(sK2),sK1) | ~v1_relat_1(sK2)),
% 1.44/0.63    inference(resolution,[],[f140,f85])).
% 1.44/0.63  fof(f140,plain,(
% 1.44/0.63    v5_relat_1(sK2,sK1)),
% 1.44/0.63    inference(resolution,[],[f61,f92])).
% 1.44/0.63  fof(f1703,plain,(
% 1.44/0.63    ( ! [X4] : (r2_hidden(sK6(sK2,X4),k2_relat_1(sK2)) | k2_relat_1(sK2) = X4 | r2_hidden(sK5(sK2,X4),X4)) )),
% 1.44/0.63    inference(backward_demodulation,[],[f423,f1684])).
% 1.44/0.63  fof(f1684,plain,(
% 1.44/0.63    k1_relat_1(sK2) = k2_relat_1(sK2)),
% 1.44/0.63    inference(superposition,[],[f72,f1679])).
% 1.44/0.63  fof(f1679,plain,(
% 1.44/0.63    sK2 = k6_relat_1(k1_relat_1(sK2))),
% 1.44/0.63    inference(subsumption_resolution,[],[f1678,f1237])).
% 1.44/0.63  fof(f1237,plain,(
% 1.44/0.63    ( ! [X2] : (~r2_hidden(X2,k1_relat_1(sK2))) )),
% 1.44/0.63    inference(resolution,[],[f1164,f288])).
% 1.44/0.63  fof(f288,plain,(
% 1.44/0.63    ( ! [X16] : (r2_hidden(k1_funct_1(sK2,X16),k2_relat_1(sK2)) | ~r2_hidden(X16,k1_relat_1(sK2))) )),
% 1.44/0.63    inference(subsumption_resolution,[],[f115,f139])).
% 1.44/0.63  fof(f115,plain,(
% 1.44/0.63    ( ! [X16] : (r2_hidden(k1_funct_1(sK2,X16),k2_relat_1(sK2)) | ~r2_hidden(X16,k1_relat_1(sK2)) | ~v1_relat_1(sK2)) )),
% 1.44/0.63    inference(resolution,[],[f59,f98])).
% 1.44/0.63  fof(f1678,plain,(
% 1.44/0.63    r2_hidden(sK4(k6_relat_1(k1_relat_1(sK2)),sK2),k1_relat_1(sK2)) | sK2 = k6_relat_1(k1_relat_1(sK2))),
% 1.44/0.63    inference(equality_resolution,[],[f484])).
% 1.44/0.63  fof(f484,plain,(
% 1.44/0.63    ( ! [X0] : (k1_relat_1(sK2) != X0 | r2_hidden(sK4(k6_relat_1(X0),sK2),X0) | k6_relat_1(X0) = sK2) )),
% 1.44/0.63    inference(subsumption_resolution,[],[f483,f69])).
% 1.44/0.63  fof(f69,plain,(
% 1.44/0.63    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.44/0.63    inference(cnf_transformation,[],[f11])).
% 1.44/0.63  fof(f11,axiom,(
% 1.44/0.63    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.44/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).
% 1.44/0.63  fof(f483,plain,(
% 1.44/0.63    ( ! [X0] : (k1_relat_1(sK2) != X0 | r2_hidden(sK4(k6_relat_1(X0),sK2),X0) | k6_relat_1(X0) = sK2 | ~v1_relat_1(k6_relat_1(X0))) )),
% 1.44/0.63    inference(subsumption_resolution,[],[f481,f70])).
% 1.44/0.63  fof(f70,plain,(
% 1.44/0.63    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 1.44/0.63    inference(cnf_transformation,[],[f11])).
% 1.44/0.63  fof(f481,plain,(
% 1.44/0.63    ( ! [X0] : (k1_relat_1(sK2) != X0 | r2_hidden(sK4(k6_relat_1(X0),sK2),X0) | k6_relat_1(X0) = sK2 | ~v1_funct_1(k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0))) )),
% 1.44/0.63    inference(superposition,[],[f480,f71])).
% 1.44/0.63  fof(f71,plain,(
% 1.44/0.63    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.44/0.63    inference(cnf_transformation,[],[f9])).
% 1.44/0.63  fof(f9,axiom,(
% 1.44/0.63    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.44/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 1.44/0.63  fof(f480,plain,(
% 1.44/0.63    ( ! [X1] : (k1_relat_1(X1) != k1_relat_1(sK2) | r2_hidden(sK4(X1,sK2),k1_relat_1(X1)) | sK2 = X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.44/0.63    inference(subsumption_resolution,[],[f106,f139])).
% 1.44/0.63  fof(f106,plain,(
% 1.44/0.63    ( ! [X1] : (sK2 = X1 | r2_hidden(sK4(X1,sK2),k1_relat_1(X1)) | k1_relat_1(X1) != k1_relat_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.44/0.63    inference(resolution,[],[f59,f74])).
% 1.44/0.63  fof(f74,plain,(
% 1.44/0.63    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK4(X0,X1),k1_relat_1(X0)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.44/0.63    inference(cnf_transformation,[],[f48])).
% 1.44/0.63  fof(f48,plain,(
% 1.44/0.63    ! [X0] : (! [X1] : (X0 = X1 | (k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1)) & r2_hidden(sK4(X0,X1),k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.44/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f26,f47])).
% 1.44/0.63  fof(f47,plain,(
% 1.44/0.63    ! [X1,X0] : (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1)) & r2_hidden(sK4(X0,X1),k1_relat_1(X0))))),
% 1.44/0.63    introduced(choice_axiom,[])).
% 1.44/0.63  fof(f26,plain,(
% 1.44/0.63    ! [X0] : (! [X1] : (X0 = X1 | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.44/0.63    inference(flattening,[],[f25])).
% 1.44/0.63  fof(f25,plain,(
% 1.44/0.63    ! [X0] : (! [X1] : ((X0 = X1 | (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.44/0.63    inference(ennf_transformation,[],[f12])).
% 1.44/0.63  fof(f12,axiom,(
% 1.44/0.63    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) => X0 = X1)))),
% 1.44/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_1)).
% 1.44/0.63  fof(f72,plain,(
% 1.44/0.63    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 1.44/0.63    inference(cnf_transformation,[],[f9])).
% 1.44/0.63  fof(f423,plain,(
% 1.44/0.63    ( ! [X4] : (r2_hidden(sK6(sK2,X4),k1_relat_1(sK2)) | k2_relat_1(sK2) = X4 | r2_hidden(sK5(sK2,X4),X4)) )),
% 1.44/0.63    inference(subsumption_resolution,[],[f109,f139])).
% 1.44/0.63  fof(f109,plain,(
% 1.44/0.63    ( ! [X4] : (k2_relat_1(sK2) = X4 | r2_hidden(sK6(sK2,X4),k1_relat_1(sK2)) | r2_hidden(sK5(sK2,X4),X4) | ~v1_relat_1(sK2)) )),
% 1.44/0.63    inference(resolution,[],[f59,f79])).
% 1.44/0.63  fof(f79,plain,(
% 1.44/0.63    ( ! [X0,X1] : (k2_relat_1(X0) = X1 | r2_hidden(sK6(X0,X1),k1_relat_1(X0)) | r2_hidden(sK5(X0,X1),X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.44/0.63    inference(cnf_transformation,[],[f54])).
% 1.44/0.63  fof(f1778,plain,(
% 1.44/0.63    ( ! [X0] : (k1_xboole_0 != k1_relat_1(X0) | sK2 = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.44/0.63    inference(backward_demodulation,[],[f1725,f1746])).
% 1.44/0.63  fof(f1725,plain,(
% 1.44/0.63    ( ! [X0] : (k1_relat_1(X0) != k2_relat_1(sK2) | sK2 = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.44/0.63    inference(forward_demodulation,[],[f1724,f1684])).
% 1.44/0.63  fof(f1724,plain,(
% 1.44/0.63    ( ! [X0] : (k1_relat_1(X0) != k1_relat_1(sK2) | sK2 = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.44/0.63    inference(subsumption_resolution,[],[f1705,f1164])).
% 1.44/0.63  fof(f1705,plain,(
% 1.44/0.63    ( ! [X0] : (r2_hidden(sK4(sK2,X0),k2_relat_1(sK2)) | k1_relat_1(X0) != k1_relat_1(sK2) | sK2 = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.44/0.63    inference(backward_demodulation,[],[f459,f1684])).
% 1.44/0.63  fof(f459,plain,(
% 1.44/0.63    ( ! [X0] : (k1_relat_1(X0) != k1_relat_1(sK2) | r2_hidden(sK4(sK2,X0),k1_relat_1(sK2)) | sK2 = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.44/0.63    inference(subsumption_resolution,[],[f105,f139])).
% 1.44/0.63  fof(f105,plain,(
% 1.44/0.63    ( ! [X0] : (sK2 = X0 | r2_hidden(sK4(sK2,X0),k1_relat_1(sK2)) | k1_relat_1(X0) != k1_relat_1(sK2) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_relat_1(sK2)) )),
% 1.44/0.63    inference(resolution,[],[f59,f74])).
% 1.44/0.63  fof(f878,plain,(
% 1.44/0.63    ~r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,sK3)),
% 1.44/0.63    inference(backward_demodulation,[],[f775,f813])).
% 1.44/0.63  fof(f775,plain,(
% 1.44/0.63    ~r2_relset_1(sK0,k1_xboole_0,sK2,sK3)),
% 1.44/0.63    inference(backward_demodulation,[],[f67,f768])).
% 1.44/0.63  % SZS output end Proof for theBenchmark
% 1.44/0.63  % (3812)------------------------------
% 1.44/0.63  % (3812)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.63  % (3812)Termination reason: Refutation
% 1.44/0.63  
% 1.44/0.63  % (3812)Memory used [KB]: 2174
% 1.44/0.63  % (3812)Time elapsed: 0.207 s
% 1.44/0.63  % (3812)------------------------------
% 1.44/0.63  % (3812)------------------------------
% 2.07/0.63  % (3785)Success in time 0.27 s
%------------------------------------------------------------------------------
