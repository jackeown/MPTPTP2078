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
% DateTime   : Thu Dec  3 13:01:28 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 684 expanded)
%              Number of leaves         :   18 ( 209 expanded)
%              Depth                    :   19
%              Number of atoms          :  427 (5393 expanded)
%              Number of equality atoms :  138 (1702 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f413,plain,(
    $false ),
    inference(subsumption_resolution,[],[f412,f376])).

fof(f376,plain,(
    sK3 != k2_relat_1(sK5) ),
    inference(backward_demodulation,[],[f259,f374])).

fof(f374,plain,(
    sK3 = k9_relat_1(sK5,k2_relat_1(sK4)) ),
    inference(backward_demodulation,[],[f146,f373])).

fof(f373,plain,(
    sK3 = k2_relat_1(k5_relat_1(sK4,sK5)) ),
    inference(forward_demodulation,[],[f363,f293])).

fof(f293,plain,(
    sK3 = k2_relset_1(sK1,sK3,k5_relat_1(sK4,sK5)) ),
    inference(backward_demodulation,[],[f60,f292])).

fof(f292,plain,(
    k1_partfun1(sK1,sK2,sK2,sK3,sK4,sK5) = k5_relat_1(sK4,sK5) ),
    inference(subsumption_resolution,[],[f290,f57])).

fof(f57,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,
    ( sK2 != k2_relset_1(sK1,sK2,sK4)
    & k1_xboole_0 != sK3
    & v2_funct_1(sK5)
    & sK3 = k2_relset_1(sK1,sK3,k1_partfun1(sK1,sK2,sK2,sK3,sK4,sK5))
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    & v1_funct_2(sK5,sK2,sK3)
    & v1_funct_1(sK5)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK4,sK1,sK2)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f20,f46,f45])).

fof(f45,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( k2_relset_1(X0,X1,X3) != X1
            & k1_xboole_0 != X2
            & v2_funct_1(X4)
            & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( sK2 != k2_relset_1(sK1,sK2,sK4)
          & k1_xboole_0 != sK3
          & v2_funct_1(X4)
          & sK3 = k2_relset_1(sK1,sK3,k1_partfun1(sK1,sK2,sK2,sK3,sK4,X4))
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
          & v1_funct_2(X4,sK2,sK3)
          & v1_funct_1(X4) )
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_2(sK4,sK1,sK2)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( ? [X4] :
        ( sK2 != k2_relset_1(sK1,sK2,sK4)
        & k1_xboole_0 != sK3
        & v2_funct_1(X4)
        & sK3 = k2_relset_1(sK1,sK3,k1_partfun1(sK1,sK2,sK2,sK3,sK4,X4))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
        & v1_funct_2(X4,sK2,sK3)
        & v1_funct_1(X4) )
   => ( sK2 != k2_relset_1(sK1,sK2,sK4)
      & k1_xboole_0 != sK3
      & v2_funct_1(sK5)
      & sK3 = k2_relset_1(sK1,sK3,k1_partfun1(sK1,sK2,sK2,sK3,sK4,sK5))
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
      & v1_funct_2(sK5,sK2,sK3)
      & v1_funct_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( k2_relset_1(X0,X1,X3) != X1
          & k1_xboole_0 != X2
          & v2_funct_1(X4)
          & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X4,X1,X2)
          & v1_funct_1(X4) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( k2_relset_1(X0,X1,X3) != X1
          & k1_xboole_0 != X2
          & v2_funct_1(X4)
          & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X4,X1,X2)
          & v1_funct_1(X4) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ! [X4] :
            ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(X4,X1,X2)
              & v1_funct_1(X4) )
           => ( ( v2_funct_1(X4)
                & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 )
             => ( k2_relset_1(X0,X1,X3) = X1
                | k1_xboole_0 = X2 ) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
         => ( ( v2_funct_1(X4)
              & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 )
           => ( k2_relset_1(X0,X1,X3) = X1
              | k1_xboole_0 = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_funct_2)).

fof(f290,plain,
    ( ~ v1_funct_1(sK5)
    | k1_partfun1(sK1,sK2,sK2,sK3,sK4,sK5) = k5_relat_1(sK4,sK5) ),
    inference(resolution,[],[f287,f59])).

fof(f59,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f47])).

fof(f287,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X0)
      | k5_relat_1(sK4,X0) = k1_partfun1(sK1,sK2,X1,X2,sK4,X0) ) ),
    inference(subsumption_resolution,[],[f285,f54])).

fof(f54,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f47])).

fof(f285,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X0)
      | k5_relat_1(sK4,X0) = k1_partfun1(sK1,sK2,X1,X2,sK4,X0)
      | ~ v1_funct_1(sK4) ) ),
    inference(resolution,[],[f88,f56])).

fof(f56,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f47])).

fof(f88,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f60,plain,(
    sK3 = k2_relset_1(sK1,sK3,k1_partfun1(sK1,sK2,sK2,sK3,sK4,sK5)) ),
    inference(cnf_transformation,[],[f47])).

fof(f363,plain,(
    k2_relat_1(k5_relat_1(sK4,sK5)) = k2_relset_1(sK1,sK3,k5_relat_1(sK4,sK5)) ),
    inference(resolution,[],[f325,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f325,plain,(
    m1_subset_1(k5_relat_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) ),
    inference(forward_demodulation,[],[f324,f292])).

fof(f324,plain,(
    m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) ),
    inference(subsumption_resolution,[],[f321,f57])).

fof(f321,plain,
    ( ~ v1_funct_1(sK5)
    | m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) ),
    inference(resolution,[],[f318,f59])).

fof(f318,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X0)
      | m1_subset_1(k1_partfun1(sK1,sK2,X1,X2,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(sK1,X2))) ) ),
    inference(subsumption_resolution,[],[f316,f54])).

fof(f316,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X0)
      | m1_subset_1(k1_partfun1(sK1,sK2,X1,X2,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(sK1,X2)))
      | ~ v1_funct_1(sK4) ) ),
    inference(resolution,[],[f90,f56])).

fof(f90,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f146,plain,(
    k2_relat_1(k5_relat_1(sK4,sK5)) = k9_relat_1(sK5,k2_relat_1(sK4)) ),
    inference(resolution,[],[f143,f99])).

fof(f99,plain,(
    v1_relat_1(sK5) ),
    inference(resolution,[],[f76,f59])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f143,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k2_relat_1(k5_relat_1(sK4,X0)) = k9_relat_1(X0,k2_relat_1(sK4)) ) ),
    inference(resolution,[],[f64,f98])).

fof(f98,plain,(
    v1_relat_1(sK4) ),
    inference(resolution,[],[f76,f56])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).

fof(f259,plain,(
    k2_relat_1(sK5) != k9_relat_1(sK5,k2_relat_1(sK4)) ),
    inference(subsumption_resolution,[],[f258,f98])).

fof(f258,plain,
    ( k2_relat_1(sK5) != k9_relat_1(sK5,k2_relat_1(sK4))
    | ~ v1_relat_1(sK4) ),
    inference(subsumption_resolution,[],[f257,f54])).

fof(f257,plain,
    ( k2_relat_1(sK5) != k9_relat_1(sK5,k2_relat_1(sK4))
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4) ),
    inference(subsumption_resolution,[],[f255,f161])).

fof(f161,plain,(
    ~ r1_tarski(sK2,k2_relat_1(sK4)) ),
    inference(subsumption_resolution,[],[f160,f157])).

fof(f157,plain,(
    sK2 != k2_relat_1(sK4) ),
    inference(superposition,[],[f63,f155])).

fof(f155,plain,(
    k2_relset_1(sK1,sK2,sK4) = k2_relat_1(sK4) ),
    inference(resolution,[],[f78,f56])).

fof(f63,plain,(
    sK2 != k2_relset_1(sK1,sK2,sK4) ),
    inference(cnf_transformation,[],[f47])).

fof(f160,plain,
    ( sK2 = k2_relat_1(sK4)
    | ~ r1_tarski(sK2,k2_relat_1(sK4)) ),
    inference(resolution,[],[f158,f104])).

fof(f104,plain,(
    v5_relat_1(sK4,sK2) ),
    inference(resolution,[],[f80,f56])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f158,plain,(
    ! [X0] :
      ( ~ v5_relat_1(sK4,X0)
      | k2_relat_1(sK4) = X0
      | ~ r1_tarski(X0,k2_relat_1(sK4)) ) ),
    inference(resolution,[],[f101,f98])).

fof(f101,plain,(
    ! [X2,X1] :
      ( ~ v1_relat_1(X2)
      | k2_relat_1(X2) = X1
      | ~ v5_relat_1(X2,X1)
      | ~ r1_tarski(X1,k2_relat_1(X2)) ) ),
    inference(resolution,[],[f75,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f255,plain,
    ( k2_relat_1(sK5) != k9_relat_1(sK5,k2_relat_1(sK4))
    | r1_tarski(sK2,k2_relat_1(sK4))
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4) ),
    inference(superposition,[],[f254,f146])).

fof(f254,plain,(
    ! [X0] :
      ( k2_relat_1(sK5) != k2_relat_1(k5_relat_1(X0,sK5))
      | r1_tarski(sK2,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(forward_demodulation,[],[f253,f180])).

fof(f180,plain,(
    sK2 = k1_relat_1(sK5) ),
    inference(backward_demodulation,[],[f154,f179])).

fof(f179,plain,(
    sK2 = k1_relset_1(sK2,sK3,sK5) ),
    inference(subsumption_resolution,[],[f178,f62])).

fof(f62,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f47])).

fof(f178,plain,
    ( k1_xboole_0 = sK3
    | sK2 = k1_relset_1(sK2,sK3,sK5) ),
    inference(subsumption_resolution,[],[f176,f58])).

fof(f58,plain,(
    v1_funct_2(sK5,sK2,sK3) ),
    inference(cnf_transformation,[],[f47])).

fof(f176,plain,
    ( ~ v1_funct_2(sK5,sK2,sK3)
    | k1_xboole_0 = sK3
    | sK2 = k1_relset_1(sK2,sK3,sK5) ),
    inference(resolution,[],[f81,f124])).

fof(f124,plain,(
    sP0(sK2,sK5,sK3) ),
    inference(resolution,[],[f85,f59])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP0(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & sP0(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & sP0(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f38,f43])).

fof(f43,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ v1_funct_2(X1,X0,X2)
      | k1_xboole_0 = X2
      | k1_relset_1(X0,X2,X1) = X0 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X2 )
      | ~ sP0(X0,X1,X2) ) ),
    inference(rectify,[],[f51])).

fof(f51,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f154,plain,(
    k1_relat_1(sK5) = k1_relset_1(sK2,sK3,sK5) ),
    inference(resolution,[],[f77,f59])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f253,plain,(
    ! [X0] :
      ( r1_tarski(k1_relat_1(sK5),k2_relat_1(X0))
      | k2_relat_1(sK5) != k2_relat_1(k5_relat_1(X0,sK5))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f252,f99])).

fof(f252,plain,(
    ! [X0] :
      ( r1_tarski(k1_relat_1(sK5),k2_relat_1(X0))
      | k2_relat_1(sK5) != k2_relat_1(k5_relat_1(X0,sK5))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(sK5) ) ),
    inference(subsumption_resolution,[],[f251,f57])).

fof(f251,plain,(
    ! [X0] :
      ( r1_tarski(k1_relat_1(sK5),k2_relat_1(X0))
      | k2_relat_1(sK5) != k2_relat_1(k5_relat_1(X0,sK5))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(sK5)
      | ~ v1_relat_1(sK5) ) ),
    inference(resolution,[],[f65,f61])).

fof(f61,plain,(
    v2_funct_1(sK5) ),
    inference(cnf_transformation,[],[f47])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X0)
      | r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
      | k2_relat_1(X0) != k2_relat_1(k5_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v2_funct_1(X0)
          | k2_relat_1(X0) != k2_relat_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v2_funct_1(X0)
          | k2_relat_1(X0) != k2_relat_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( v2_funct_1(X0)
              & k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) )
           => r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_funct_1)).

fof(f412,plain,(
    sK3 = k2_relat_1(sK5) ),
    inference(subsumption_resolution,[],[f404,f105])).

fof(f105,plain,(
    v5_relat_1(sK5,sK3) ),
    inference(resolution,[],[f80,f59])).

fof(f404,plain,
    ( ~ v5_relat_1(sK5,sK3)
    | sK3 = k2_relat_1(sK5) ),
    inference(superposition,[],[f219,f374])).

fof(f219,plain,(
    ! [X0] :
      ( ~ v5_relat_1(sK5,k9_relat_1(sK5,X0))
      | k2_relat_1(sK5) = k9_relat_1(sK5,X0) ) ),
    inference(subsumption_resolution,[],[f217,f99])).

fof(f217,plain,(
    ! [X0] :
      ( k2_relat_1(sK5) = k9_relat_1(sK5,X0)
      | ~ v5_relat_1(sK5,k9_relat_1(sK5,X0))
      | ~ v1_relat_1(sK5) ) ),
    inference(resolution,[],[f190,f70])).

fof(f190,plain,(
    ! [X1] :
      ( ~ r1_tarski(k2_relat_1(sK5),k9_relat_1(sK5,X1))
      | k2_relat_1(sK5) = k9_relat_1(sK5,X1) ) ),
    inference(resolution,[],[f188,f75])).

fof(f188,plain,(
    ! [X0] : r1_tarski(k9_relat_1(sK5,X0),k2_relat_1(sK5)) ),
    inference(forward_demodulation,[],[f187,f119])).

fof(f119,plain,(
    k2_relat_1(sK5) = k9_relat_1(sK5,sK2) ),
    inference(superposition,[],[f107,f118])).

fof(f118,plain,(
    sK5 = k7_relat_1(sK5,sK2) ),
    inference(resolution,[],[f112,f103])).

fof(f103,plain,(
    v4_relat_1(sK5,sK2) ),
    inference(resolution,[],[f79,f59])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f112,plain,(
    ! [X1] :
      ( ~ v4_relat_1(sK5,X1)
      | sK5 = k7_relat_1(sK5,X1) ) ),
    inference(resolution,[],[f72,f99])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0)
      | k7_relat_1(X1,X0) = X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

fof(f107,plain,(
    ! [X1] : k9_relat_1(sK5,X1) = k2_relat_1(k7_relat_1(sK5,X1)) ),
    inference(resolution,[],[f66,f99])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f187,plain,(
    ! [X0] : r1_tarski(k9_relat_1(sK5,X0),k9_relat_1(sK5,sK2)) ),
    inference(subsumption_resolution,[],[f186,f99])).

fof(f186,plain,(
    ! [X0] :
      ( r1_tarski(k9_relat_1(sK5,X0),k9_relat_1(sK5,sK2))
      | ~ v1_relat_1(sK5) ) ),
    inference(superposition,[],[f67,f180])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X1,k1_relat_1(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:49:46 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (28114)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.51  % (28115)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.51  % (28127)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.51  % (28113)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.51  % (28112)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.51  % (28111)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.52  % (28122)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.52  % (28123)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.52  % (28130)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.52  % (28119)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.52  % (28112)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % (28131)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.53  % (28121)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.53  % (28120)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.53  % (28129)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.53  % (28128)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.53  % (28132)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.54  % (28117)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.54  % (28124)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  fof(f413,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(subsumption_resolution,[],[f412,f376])).
% 0.21/0.54  fof(f376,plain,(
% 0.21/0.54    sK3 != k2_relat_1(sK5)),
% 0.21/0.54    inference(backward_demodulation,[],[f259,f374])).
% 0.21/0.54  fof(f374,plain,(
% 0.21/0.54    sK3 = k9_relat_1(sK5,k2_relat_1(sK4))),
% 0.21/0.54    inference(backward_demodulation,[],[f146,f373])).
% 0.21/0.54  fof(f373,plain,(
% 0.21/0.54    sK3 = k2_relat_1(k5_relat_1(sK4,sK5))),
% 0.21/0.54    inference(forward_demodulation,[],[f363,f293])).
% 0.21/0.54  fof(f293,plain,(
% 0.21/0.54    sK3 = k2_relset_1(sK1,sK3,k5_relat_1(sK4,sK5))),
% 0.21/0.54    inference(backward_demodulation,[],[f60,f292])).
% 0.21/0.54  fof(f292,plain,(
% 0.21/0.54    k1_partfun1(sK1,sK2,sK2,sK3,sK4,sK5) = k5_relat_1(sK4,sK5)),
% 0.21/0.54    inference(subsumption_resolution,[],[f290,f57])).
% 0.21/0.54  fof(f57,plain,(
% 0.21/0.54    v1_funct_1(sK5)),
% 0.21/0.54    inference(cnf_transformation,[],[f47])).
% 0.21/0.54  fof(f47,plain,(
% 0.21/0.54    (sK2 != k2_relset_1(sK1,sK2,sK4) & k1_xboole_0 != sK3 & v2_funct_1(sK5) & sK3 = k2_relset_1(sK1,sK3,k1_partfun1(sK1,sK2,sK2,sK3,sK4,sK5)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK5,sK2,sK3) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4)),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f20,f46,f45])).
% 0.21/0.54  fof(f45,plain,(
% 0.21/0.54    ? [X0,X1,X2,X3] : (? [X4] : (k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2 & v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (? [X4] : (sK2 != k2_relset_1(sK1,sK2,sK4) & k1_xboole_0 != sK3 & v2_funct_1(X4) & sK3 = k2_relset_1(sK1,sK3,k1_partfun1(sK1,sK2,sK2,sK3,sK4,X4)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(X4,sK2,sK3) & v1_funct_1(X4)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f46,plain,(
% 0.21/0.54    ? [X4] : (sK2 != k2_relset_1(sK1,sK2,sK4) & k1_xboole_0 != sK3 & v2_funct_1(X4) & sK3 = k2_relset_1(sK1,sK3,k1_partfun1(sK1,sK2,sK2,sK3,sK4,X4)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(X4,sK2,sK3) & v1_funct_1(X4)) => (sK2 != k2_relset_1(sK1,sK2,sK4) & k1_xboole_0 != sK3 & v2_funct_1(sK5) & sK3 = k2_relset_1(sK1,sK3,k1_partfun1(sK1,sK2,sK2,sK3,sK4,sK5)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK5,sK2,sK3) & v1_funct_1(sK5))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f20,plain,(
% 0.21/0.54    ? [X0,X1,X2,X3] : (? [X4] : (k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2 & v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.21/0.54    inference(flattening,[],[f19])).
% 0.21/0.54  fof(f19,plain,(
% 0.21/0.54    ? [X0,X1,X2,X3] : (? [X4] : (((k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2) & (v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.21/0.54    inference(ennf_transformation,[],[f18])).
% 0.21/0.54  fof(f18,negated_conjecture,(
% 0.21/0.54    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2) => (k2_relset_1(X0,X1,X3) = X1 | k1_xboole_0 = X2))))),
% 0.21/0.54    inference(negated_conjecture,[],[f17])).
% 0.21/0.54  fof(f17,conjecture,(
% 0.21/0.54    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2) => (k2_relset_1(X0,X1,X3) = X1 | k1_xboole_0 = X2))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_funct_2)).
% 0.21/0.54  fof(f290,plain,(
% 0.21/0.54    ~v1_funct_1(sK5) | k1_partfun1(sK1,sK2,sK2,sK3,sK4,sK5) = k5_relat_1(sK4,sK5)),
% 0.21/0.54    inference(resolution,[],[f287,f59])).
% 0.21/0.54  fof(f59,plain,(
% 0.21/0.54    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 0.21/0.54    inference(cnf_transformation,[],[f47])).
% 0.21/0.54  fof(f287,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X0) | k5_relat_1(sK4,X0) = k1_partfun1(sK1,sK2,X1,X2,sK4,X0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f285,f54])).
% 0.21/0.54  fof(f54,plain,(
% 0.21/0.54    v1_funct_1(sK4)),
% 0.21/0.54    inference(cnf_transformation,[],[f47])).
% 0.21/0.54  fof(f285,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X0) | k5_relat_1(sK4,X0) = k1_partfun1(sK1,sK2,X1,X2,sK4,X0) | ~v1_funct_1(sK4)) )),
% 0.21/0.54    inference(resolution,[],[f88,f56])).
% 0.21/0.54  fof(f56,plain,(
% 0.21/0.54    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.21/0.54    inference(cnf_transformation,[],[f47])).
% 0.21/0.54  fof(f88,plain,(
% 0.21/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~v1_funct_1(X4)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f40])).
% 0.21/0.54  fof(f40,plain,(
% 0.21/0.54    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 0.21/0.54    inference(flattening,[],[f39])).
% 0.21/0.54  fof(f39,plain,(
% 0.21/0.54    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 0.21/0.54    inference(ennf_transformation,[],[f16])).
% 0.21/0.54  fof(f16,axiom,(
% 0.21/0.54    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 0.21/0.54  fof(f60,plain,(
% 0.21/0.54    sK3 = k2_relset_1(sK1,sK3,k1_partfun1(sK1,sK2,sK2,sK3,sK4,sK5))),
% 0.21/0.54    inference(cnf_transformation,[],[f47])).
% 0.21/0.54  fof(f363,plain,(
% 0.21/0.54    k2_relat_1(k5_relat_1(sK4,sK5)) = k2_relset_1(sK1,sK3,k5_relat_1(sK4,sK5))),
% 0.21/0.54    inference(resolution,[],[f325,f78])).
% 0.21/0.54  fof(f78,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f35])).
% 0.21/0.54  fof(f35,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.54    inference(ennf_transformation,[],[f13])).
% 0.21/0.54  fof(f13,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.54  fof(f325,plain,(
% 0.21/0.54    m1_subset_1(k5_relat_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))),
% 0.21/0.54    inference(forward_demodulation,[],[f324,f292])).
% 0.21/0.54  fof(f324,plain,(
% 0.21/0.54    m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))),
% 0.21/0.54    inference(subsumption_resolution,[],[f321,f57])).
% 0.21/0.54  fof(f321,plain,(
% 0.21/0.54    ~v1_funct_1(sK5) | m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))),
% 0.21/0.54    inference(resolution,[],[f318,f59])).
% 0.21/0.54  fof(f318,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X0) | m1_subset_1(k1_partfun1(sK1,sK2,X1,X2,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(sK1,X2)))) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f316,f54])).
% 0.21/0.54  fof(f316,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X0) | m1_subset_1(k1_partfun1(sK1,sK2,X1,X2,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(sK1,X2))) | ~v1_funct_1(sK4)) )),
% 0.21/0.54    inference(resolution,[],[f90,f56])).
% 0.21/0.54  fof(f90,plain,(
% 0.21/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~v1_funct_1(X4)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f42])).
% 0.21/0.54  fof(f42,plain,(
% 0.21/0.54    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 0.21/0.54    inference(flattening,[],[f41])).
% 0.21/0.54  fof(f41,plain,(
% 0.21/0.54    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 0.21/0.54    inference(ennf_transformation,[],[f15])).
% 0.21/0.54  fof(f15,axiom,(
% 0.21/0.54    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 0.21/0.54  fof(f146,plain,(
% 0.21/0.54    k2_relat_1(k5_relat_1(sK4,sK5)) = k9_relat_1(sK5,k2_relat_1(sK4))),
% 0.21/0.54    inference(resolution,[],[f143,f99])).
% 0.21/0.54  fof(f99,plain,(
% 0.21/0.54    v1_relat_1(sK5)),
% 0.21/0.54    inference(resolution,[],[f76,f59])).
% 0.21/0.54  fof(f76,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f33])).
% 0.21/0.54  fof(f33,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.54    inference(ennf_transformation,[],[f10])).
% 0.21/0.54  fof(f10,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.54  fof(f143,plain,(
% 0.21/0.54    ( ! [X0] : (~v1_relat_1(X0) | k2_relat_1(k5_relat_1(sK4,X0)) = k9_relat_1(X0,k2_relat_1(sK4))) )),
% 0.21/0.54    inference(resolution,[],[f64,f98])).
% 0.21/0.54  fof(f98,plain,(
% 0.21/0.54    v1_relat_1(sK4)),
% 0.21/0.54    inference(resolution,[],[f76,f56])).
% 0.21/0.54  fof(f64,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f21])).
% 0.21/0.54  fof(f21,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f7])).
% 0.21/0.54  fof(f7,axiom,(
% 0.21/0.54    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).
% 0.21/0.54  fof(f259,plain,(
% 0.21/0.54    k2_relat_1(sK5) != k9_relat_1(sK5,k2_relat_1(sK4))),
% 0.21/0.54    inference(subsumption_resolution,[],[f258,f98])).
% 0.21/0.54  fof(f258,plain,(
% 0.21/0.54    k2_relat_1(sK5) != k9_relat_1(sK5,k2_relat_1(sK4)) | ~v1_relat_1(sK4)),
% 0.21/0.54    inference(subsumption_resolution,[],[f257,f54])).
% 0.21/0.54  fof(f257,plain,(
% 0.21/0.54    k2_relat_1(sK5) != k9_relat_1(sK5,k2_relat_1(sK4)) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4)),
% 0.21/0.54    inference(subsumption_resolution,[],[f255,f161])).
% 0.21/0.54  fof(f161,plain,(
% 0.21/0.54    ~r1_tarski(sK2,k2_relat_1(sK4))),
% 0.21/0.54    inference(subsumption_resolution,[],[f160,f157])).
% 0.21/0.54  fof(f157,plain,(
% 0.21/0.54    sK2 != k2_relat_1(sK4)),
% 0.21/0.54    inference(superposition,[],[f63,f155])).
% 0.21/0.54  fof(f155,plain,(
% 0.21/0.54    k2_relset_1(sK1,sK2,sK4) = k2_relat_1(sK4)),
% 0.21/0.54    inference(resolution,[],[f78,f56])).
% 0.21/0.54  fof(f63,plain,(
% 0.21/0.54    sK2 != k2_relset_1(sK1,sK2,sK4)),
% 0.21/0.54    inference(cnf_transformation,[],[f47])).
% 0.21/0.54  fof(f160,plain,(
% 0.21/0.54    sK2 = k2_relat_1(sK4) | ~r1_tarski(sK2,k2_relat_1(sK4))),
% 0.21/0.54    inference(resolution,[],[f158,f104])).
% 0.21/0.54  fof(f104,plain,(
% 0.21/0.54    v5_relat_1(sK4,sK2)),
% 0.21/0.54    inference(resolution,[],[f80,f56])).
% 0.21/0.54  fof(f80,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f36])).
% 0.21/0.54  fof(f36,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.54    inference(ennf_transformation,[],[f11])).
% 0.21/0.54  fof(f11,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.54  fof(f158,plain,(
% 0.21/0.54    ( ! [X0] : (~v5_relat_1(sK4,X0) | k2_relat_1(sK4) = X0 | ~r1_tarski(X0,k2_relat_1(sK4))) )),
% 0.21/0.54    inference(resolution,[],[f101,f98])).
% 0.21/0.54  fof(f101,plain,(
% 0.21/0.54    ( ! [X2,X1] : (~v1_relat_1(X2) | k2_relat_1(X2) = X1 | ~v5_relat_1(X2,X1) | ~r1_tarski(X1,k2_relat_1(X2))) )),
% 0.21/0.54    inference(resolution,[],[f75,f70])).
% 0.21/0.54  fof(f70,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f48])).
% 0.21/0.54  fof(f48,plain,(
% 0.21/0.54    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.21/0.54    inference(nnf_transformation,[],[f30])).
% 0.21/0.54  fof(f30,plain,(
% 0.21/0.54    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f2])).
% 0.21/0.54  fof(f2,axiom,(
% 0.21/0.54    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 0.21/0.54  fof(f75,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.21/0.54    inference(cnf_transformation,[],[f50])).
% 0.21/0.54  fof(f50,plain,(
% 0.21/0.54    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.54    inference(flattening,[],[f49])).
% 0.21/0.54  fof(f49,plain,(
% 0.21/0.54    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.54    inference(nnf_transformation,[],[f1])).
% 0.21/0.54  fof(f1,axiom,(
% 0.21/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.54  fof(f255,plain,(
% 0.21/0.54    k2_relat_1(sK5) != k9_relat_1(sK5,k2_relat_1(sK4)) | r1_tarski(sK2,k2_relat_1(sK4)) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4)),
% 0.21/0.54    inference(superposition,[],[f254,f146])).
% 0.21/0.54  fof(f254,plain,(
% 0.21/0.54    ( ! [X0] : (k2_relat_1(sK5) != k2_relat_1(k5_relat_1(X0,sK5)) | r1_tarski(sK2,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(forward_demodulation,[],[f253,f180])).
% 0.21/0.54  fof(f180,plain,(
% 0.21/0.54    sK2 = k1_relat_1(sK5)),
% 0.21/0.54    inference(backward_demodulation,[],[f154,f179])).
% 0.21/0.54  fof(f179,plain,(
% 0.21/0.54    sK2 = k1_relset_1(sK2,sK3,sK5)),
% 0.21/0.54    inference(subsumption_resolution,[],[f178,f62])).
% 0.21/0.54  fof(f62,plain,(
% 0.21/0.54    k1_xboole_0 != sK3),
% 0.21/0.54    inference(cnf_transformation,[],[f47])).
% 0.21/0.54  fof(f178,plain,(
% 0.21/0.54    k1_xboole_0 = sK3 | sK2 = k1_relset_1(sK2,sK3,sK5)),
% 0.21/0.54    inference(subsumption_resolution,[],[f176,f58])).
% 0.21/0.54  fof(f58,plain,(
% 0.21/0.54    v1_funct_2(sK5,sK2,sK3)),
% 0.21/0.54    inference(cnf_transformation,[],[f47])).
% 0.21/0.54  fof(f176,plain,(
% 0.21/0.54    ~v1_funct_2(sK5,sK2,sK3) | k1_xboole_0 = sK3 | sK2 = k1_relset_1(sK2,sK3,sK5)),
% 0.21/0.54    inference(resolution,[],[f81,f124])).
% 0.21/0.54  fof(f124,plain,(
% 0.21/0.54    sP0(sK2,sK5,sK3)),
% 0.21/0.54    inference(resolution,[],[f85,f59])).
% 0.21/0.54  fof(f85,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP0(X0,X2,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f53])).
% 0.21/0.54  fof(f53,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & sP0(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.54    inference(nnf_transformation,[],[f44])).
% 0.21/0.54  fof(f44,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & sP0(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.54    inference(definition_folding,[],[f38,f43])).
% 0.21/0.54  fof(f43,plain,(
% 0.21/0.54    ! [X0,X2,X1] : ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X2,X1))),
% 0.21/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.54  fof(f38,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.54    inference(flattening,[],[f37])).
% 0.21/0.54  fof(f37,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.54    inference(ennf_transformation,[],[f14])).
% 0.21/0.54  fof(f14,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.54  fof(f81,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | ~v1_funct_2(X1,X0,X2) | k1_xboole_0 = X2 | k1_relset_1(X0,X2,X1) = X0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f52])).
% 0.21/0.54  fof(f52,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (((v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0) & (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X2) | ~sP0(X0,X1,X2))),
% 0.21/0.54    inference(rectify,[],[f51])).
% 0.21/0.54  fof(f51,plain,(
% 0.21/0.54    ! [X0,X2,X1] : (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X2,X1))),
% 0.21/0.54    inference(nnf_transformation,[],[f43])).
% 0.21/0.54  fof(f154,plain,(
% 0.21/0.54    k1_relat_1(sK5) = k1_relset_1(sK2,sK3,sK5)),
% 0.21/0.54    inference(resolution,[],[f77,f59])).
% 0.21/0.54  fof(f77,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f34])).
% 0.21/0.54  fof(f34,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.54    inference(ennf_transformation,[],[f12])).
% 0.21/0.54  fof(f12,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.54  fof(f253,plain,(
% 0.21/0.54    ( ! [X0] : (r1_tarski(k1_relat_1(sK5),k2_relat_1(X0)) | k2_relat_1(sK5) != k2_relat_1(k5_relat_1(X0,sK5)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f252,f99])).
% 0.21/0.54  fof(f252,plain,(
% 0.21/0.54    ( ! [X0] : (r1_tarski(k1_relat_1(sK5),k2_relat_1(X0)) | k2_relat_1(sK5) != k2_relat_1(k5_relat_1(X0,sK5)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_relat_1(sK5)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f251,f57])).
% 0.21/0.54  fof(f251,plain,(
% 0.21/0.54    ( ! [X0] : (r1_tarski(k1_relat_1(sK5),k2_relat_1(X0)) | k2_relat_1(sK5) != k2_relat_1(k5_relat_1(X0,sK5)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_funct_1(sK5) | ~v1_relat_1(sK5)) )),
% 0.21/0.54    inference(resolution,[],[f65,f61])).
% 0.21/0.54  fof(f61,plain,(
% 0.21/0.54    v2_funct_1(sK5)),
% 0.21/0.54    inference(cnf_transformation,[],[f47])).
% 0.21/0.54  fof(f65,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~v2_funct_1(X0) | r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | k2_relat_1(X0) != k2_relat_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f23])).
% 0.21/0.54  fof(f23,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v2_funct_1(X0) | k2_relat_1(X0) != k2_relat_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.54    inference(flattening,[],[f22])).
% 0.21/0.54  fof(f22,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : ((r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | (~v2_funct_1(X0) | k2_relat_1(X0) != k2_relat_1(k5_relat_1(X1,X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f9])).
% 0.21/0.54  fof(f9,axiom,(
% 0.21/0.54    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X0) & k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))) => r1_tarski(k1_relat_1(X0),k2_relat_1(X1)))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_funct_1)).
% 0.21/0.54  fof(f412,plain,(
% 0.21/0.54    sK3 = k2_relat_1(sK5)),
% 0.21/0.54    inference(subsumption_resolution,[],[f404,f105])).
% 0.21/0.54  fof(f105,plain,(
% 0.21/0.54    v5_relat_1(sK5,sK3)),
% 0.21/0.54    inference(resolution,[],[f80,f59])).
% 0.21/0.54  fof(f404,plain,(
% 0.21/0.54    ~v5_relat_1(sK5,sK3) | sK3 = k2_relat_1(sK5)),
% 0.21/0.54    inference(superposition,[],[f219,f374])).
% 0.21/0.54  fof(f219,plain,(
% 0.21/0.54    ( ! [X0] : (~v5_relat_1(sK5,k9_relat_1(sK5,X0)) | k2_relat_1(sK5) = k9_relat_1(sK5,X0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f217,f99])).
% 0.21/0.54  fof(f217,plain,(
% 0.21/0.54    ( ! [X0] : (k2_relat_1(sK5) = k9_relat_1(sK5,X0) | ~v5_relat_1(sK5,k9_relat_1(sK5,X0)) | ~v1_relat_1(sK5)) )),
% 0.21/0.54    inference(resolution,[],[f190,f70])).
% 0.21/0.54  fof(f190,plain,(
% 0.21/0.54    ( ! [X1] : (~r1_tarski(k2_relat_1(sK5),k9_relat_1(sK5,X1)) | k2_relat_1(sK5) = k9_relat_1(sK5,X1)) )),
% 0.21/0.54    inference(resolution,[],[f188,f75])).
% 0.21/0.54  fof(f188,plain,(
% 0.21/0.54    ( ! [X0] : (r1_tarski(k9_relat_1(sK5,X0),k2_relat_1(sK5))) )),
% 0.21/0.54    inference(forward_demodulation,[],[f187,f119])).
% 0.21/0.54  fof(f119,plain,(
% 0.21/0.54    k2_relat_1(sK5) = k9_relat_1(sK5,sK2)),
% 0.21/0.54    inference(superposition,[],[f107,f118])).
% 0.21/0.54  fof(f118,plain,(
% 0.21/0.54    sK5 = k7_relat_1(sK5,sK2)),
% 0.21/0.54    inference(resolution,[],[f112,f103])).
% 0.21/0.54  fof(f103,plain,(
% 0.21/0.54    v4_relat_1(sK5,sK2)),
% 0.21/0.54    inference(resolution,[],[f79,f59])).
% 0.21/0.54  fof(f79,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f36])).
% 0.21/0.54  fof(f112,plain,(
% 0.21/0.54    ( ! [X1] : (~v4_relat_1(sK5,X1) | sK5 = k7_relat_1(sK5,X1)) )),
% 0.21/0.54    inference(resolution,[],[f72,f99])).
% 0.21/0.54  fof(f72,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1) )),
% 0.21/0.54    inference(cnf_transformation,[],[f32])).
% 0.21/0.54  fof(f32,plain,(
% 0.21/0.54    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.54    inference(flattening,[],[f31])).
% 0.21/0.54  fof(f31,plain,(
% 0.21/0.54    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.21/0.54    inference(ennf_transformation,[],[f8])).
% 0.21/0.54  fof(f8,axiom,(
% 0.21/0.54    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).
% 0.21/0.54  fof(f107,plain,(
% 0.21/0.54    ( ! [X1] : (k9_relat_1(sK5,X1) = k2_relat_1(k7_relat_1(sK5,X1))) )),
% 0.21/0.54    inference(resolution,[],[f66,f99])).
% 0.21/0.54  fof(f66,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~v1_relat_1(X1) | k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f24])).
% 0.21/0.54  fof(f24,plain,(
% 0.21/0.54    ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f6])).
% 0.21/0.54  fof(f6,axiom,(
% 0.21/0.54    ! [X0,X1] : (v1_relat_1(X1) => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 0.21/0.54  fof(f187,plain,(
% 0.21/0.54    ( ! [X0] : (r1_tarski(k9_relat_1(sK5,X0),k9_relat_1(sK5,sK2))) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f186,f99])).
% 0.21/0.54  fof(f186,plain,(
% 0.21/0.54    ( ! [X0] : (r1_tarski(k9_relat_1(sK5,X0),k9_relat_1(sK5,sK2)) | ~v1_relat_1(sK5)) )),
% 0.21/0.54    inference(superposition,[],[f67,f180])).
% 0.21/0.54  fof(f67,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X1,k1_relat_1(X1))) | ~v1_relat_1(X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f25])).
% 0.21/0.54  fof(f25,plain,(
% 0.21/0.54    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X1,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f5])).
% 0.21/0.54  fof(f5,axiom,(
% 0.21/0.54    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X1,k1_relat_1(X1))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_relat_1)).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (28112)------------------------------
% 0.21/0.54  % (28112)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (28112)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (28112)Memory used [KB]: 6524
% 0.21/0.54  % (28112)Time elapsed: 0.101 s
% 0.21/0.54  % (28112)------------------------------
% 0.21/0.54  % (28112)------------------------------
% 0.21/0.54  % (28108)Success in time 0.178 s
%------------------------------------------------------------------------------
