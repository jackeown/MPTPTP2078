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
% DateTime   : Thu Dec  3 13:01:28 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  145 ( 824 expanded)
%              Number of leaves         :   20 ( 250 expanded)
%              Depth                    :   19
%              Number of atoms          :  445 (6269 expanded)
%              Number of equality atoms :  151 (1974 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f350,plain,(
    $false ),
    inference(subsumption_resolution,[],[f349,f142])).

fof(f142,plain,(
    sK2 != k2_relat_1(sK4) ),
    inference(superposition,[],[f62,f140])).

fof(f140,plain,(
    k2_relset_1(sK1,sK2,sK4) = k2_relat_1(sK4) ),
    inference(resolution,[],[f77,f55])).

fof(f55,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f20,f45,f44])).

fof(f44,plain,
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

fof(f45,plain,
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

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f62,plain,(
    sK2 != k2_relset_1(sK1,sK2,sK4) ),
    inference(cnf_transformation,[],[f46])).

fof(f349,plain,(
    sK2 = k2_relat_1(sK4) ),
    inference(backward_demodulation,[],[f298,f344])).

fof(f344,plain,(
    sK2 = k10_relat_1(sK5,sK3) ),
    inference(backward_demodulation,[],[f188,f328])).

fof(f328,plain,(
    sK3 = k2_relat_1(sK5) ),
    inference(subsumption_resolution,[],[f324,f107])).

fof(f107,plain,(
    v5_relat_1(sK5,sK3) ),
    inference(resolution,[],[f79,f58])).

fof(f58,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f46])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
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

fof(f324,plain,
    ( ~ v5_relat_1(sK5,sK3)
    | sK3 = k2_relat_1(sK5) ),
    inference(superposition,[],[f168,f295])).

fof(f295,plain,(
    sK3 = k9_relat_1(sK5,k2_relat_1(sK4)) ),
    inference(backward_demodulation,[],[f127,f294])).

fof(f294,plain,(
    sK3 = k2_relat_1(k5_relat_1(sK4,sK5)) ),
    inference(forward_demodulation,[],[f283,f209])).

fof(f209,plain,(
    sK3 = k2_relset_1(sK1,sK3,k5_relat_1(sK4,sK5)) ),
    inference(backward_demodulation,[],[f59,f208])).

fof(f208,plain,(
    k1_partfun1(sK1,sK2,sK2,sK3,sK4,sK5) = k5_relat_1(sK4,sK5) ),
    inference(subsumption_resolution,[],[f206,f56])).

fof(f56,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f46])).

fof(f206,plain,
    ( ~ v1_funct_1(sK5)
    | k1_partfun1(sK1,sK2,sK2,sK3,sK4,sK5) = k5_relat_1(sK4,sK5) ),
    inference(resolution,[],[f203,f58])).

fof(f203,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X0)
      | k5_relat_1(sK4,X0) = k1_partfun1(sK1,sK2,X1,X2,sK4,X0) ) ),
    inference(subsumption_resolution,[],[f201,f53])).

fof(f53,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f46])).

fof(f201,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X0)
      | k5_relat_1(sK4,X0) = k1_partfun1(sK1,sK2,X1,X2,sK4,X0)
      | ~ v1_funct_1(sK4) ) ),
    inference(resolution,[],[f87,f55])).

fof(f87,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
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

fof(f59,plain,(
    sK3 = k2_relset_1(sK1,sK3,k1_partfun1(sK1,sK2,sK2,sK3,sK4,sK5)) ),
    inference(cnf_transformation,[],[f46])).

fof(f283,plain,(
    k2_relat_1(k5_relat_1(sK4,sK5)) = k2_relset_1(sK1,sK3,k5_relat_1(sK4,sK5)) ),
    inference(resolution,[],[f241,f77])).

fof(f241,plain,(
    m1_subset_1(k5_relat_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) ),
    inference(forward_demodulation,[],[f240,f208])).

fof(f240,plain,(
    m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) ),
    inference(subsumption_resolution,[],[f237,f56])).

fof(f237,plain,
    ( ~ v1_funct_1(sK5)
    | m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) ),
    inference(resolution,[],[f221,f58])).

fof(f221,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X0)
      | m1_subset_1(k1_partfun1(sK1,sK2,X1,X2,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(sK1,X2))) ) ),
    inference(subsumption_resolution,[],[f219,f53])).

fof(f219,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X0)
      | m1_subset_1(k1_partfun1(sK1,sK2,X1,X2,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(sK1,X2)))
      | ~ v1_funct_1(sK4) ) ),
    inference(resolution,[],[f89,f55])).

fof(f89,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
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

fof(f127,plain,(
    k2_relat_1(k5_relat_1(sK4,sK5)) = k9_relat_1(sK5,k2_relat_1(sK4)) ),
    inference(resolution,[],[f124,f98])).

fof(f98,plain,(
    v1_relat_1(sK5) ),
    inference(resolution,[],[f75,f58])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f124,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k2_relat_1(k5_relat_1(sK4,X0)) = k9_relat_1(X0,k2_relat_1(sK4)) ) ),
    inference(resolution,[],[f64,f97])).

fof(f97,plain,(
    v1_relat_1(sK4) ),
    inference(resolution,[],[f75,f55])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).

fof(f168,plain,(
    ! [X0] :
      ( ~ v5_relat_1(sK5,k9_relat_1(sK5,X0))
      | k9_relat_1(sK5,X0) = k2_relat_1(sK5) ) ),
    inference(subsumption_resolution,[],[f166,f98])).

fof(f166,plain,(
    ! [X0] :
      ( k9_relat_1(sK5,X0) = k2_relat_1(sK5)
      | ~ v5_relat_1(sK5,k9_relat_1(sK5,X0))
      | ~ v1_relat_1(sK5) ) ),
    inference(resolution,[],[f163,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
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

fof(f163,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(sK5),k9_relat_1(sK5,X0))
      | k9_relat_1(sK5,X0) = k2_relat_1(sK5) ) ),
    inference(resolution,[],[f159,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
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

fof(f159,plain,(
    ! [X0] : r1_tarski(k9_relat_1(sK5,X0),k2_relat_1(sK5)) ),
    inference(forward_demodulation,[],[f158,f120])).

fof(f120,plain,(
    k2_relat_1(sK5) = k9_relat_1(sK5,sK2) ),
    inference(superposition,[],[f109,f119])).

fof(f119,plain,(
    sK5 = k7_relat_1(sK5,sK2) ),
    inference(resolution,[],[f115,f105])).

fof(f105,plain,(
    v4_relat_1(sK5,sK2) ),
    inference(resolution,[],[f78,f58])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f115,plain,(
    ! [X1] :
      ( ~ v4_relat_1(sK5,X1)
      | sK5 = k7_relat_1(sK5,X1) ) ),
    inference(resolution,[],[f71,f98])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0)
      | k7_relat_1(X1,X0) = X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

fof(f109,plain,(
    ! [X1] : k9_relat_1(sK5,X1) = k2_relat_1(k7_relat_1(sK5,X1)) ),
    inference(resolution,[],[f67,f98])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f158,plain,(
    ! [X0] : r1_tarski(k9_relat_1(sK5,X0),k9_relat_1(sK5,sK2)) ),
    inference(subsumption_resolution,[],[f157,f98])).

fof(f157,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK5)
      | r1_tarski(k9_relat_1(sK5,X0),k9_relat_1(sK5,sK2)) ) ),
    inference(superposition,[],[f113,f119])).

fof(f113,plain,(
    ! [X2,X3] :
      ( ~ v1_relat_1(k7_relat_1(sK5,X2))
      | r1_tarski(k9_relat_1(k7_relat_1(sK5,X2),X3),k9_relat_1(sK5,X2)) ) ),
    inference(superposition,[],[f66,f109])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).

fof(f188,plain,(
    sK2 = k10_relat_1(sK5,k2_relat_1(sK5)) ),
    inference(backward_demodulation,[],[f100,f187])).

fof(f187,plain,(
    sK2 = k1_relat_1(sK5) ),
    inference(backward_demodulation,[],[f133,f186])).

fof(f186,plain,(
    sK2 = k1_relset_1(sK2,sK3,sK5) ),
    inference(subsumption_resolution,[],[f185,f61])).

fof(f61,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f46])).

fof(f185,plain,
    ( k1_xboole_0 = sK3
    | sK2 = k1_relset_1(sK2,sK3,sK5) ),
    inference(subsumption_resolution,[],[f183,f57])).

fof(f57,plain,(
    v1_funct_2(sK5,sK2,sK3) ),
    inference(cnf_transformation,[],[f46])).

fof(f183,plain,
    ( ~ v1_funct_2(sK5,sK2,sK3)
    | k1_xboole_0 = sK3
    | sK2 = k1_relset_1(sK2,sK3,sK5) ),
    inference(resolution,[],[f80,f123])).

fof(f123,plain,(
    sP0(sK2,sK5,sK3) ),
    inference(resolution,[],[f84,f58])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP0(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & sP0(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & sP0(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f37,f42])).

fof(f42,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

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
    inference(flattening,[],[f36])).

fof(f36,plain,(
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

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ v1_funct_2(X1,X0,X2)
      | k1_xboole_0 = X2
      | k1_relset_1(X0,X2,X1) = X0 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X2 )
      | ~ sP0(X0,X1,X2) ) ),
    inference(rectify,[],[f50])).

fof(f50,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f133,plain,(
    k1_relat_1(sK5) = k1_relset_1(sK2,sK3,sK5) ),
    inference(resolution,[],[f76,f58])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f100,plain,(
    k1_relat_1(sK5) = k10_relat_1(sK5,k2_relat_1(sK5)) ),
    inference(resolution,[],[f63,f98])).

fof(f63,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

fof(f298,plain,(
    k2_relat_1(sK4) = k10_relat_1(sK5,sK3) ),
    inference(backward_demodulation,[],[f197,f295])).

fof(f197,plain,(
    k2_relat_1(sK4) = k10_relat_1(sK5,k9_relat_1(sK5,k2_relat_1(sK4))) ),
    inference(resolution,[],[f195,f175])).

fof(f175,plain,(
    r1_tarski(k2_relat_1(sK4),sK2) ),
    inference(resolution,[],[f174,f106])).

fof(f106,plain,(
    v5_relat_1(sK4,sK2) ),
    inference(resolution,[],[f79,f55])).

fof(f174,plain,(
    ! [X0] :
      ( ~ v5_relat_1(sK4,X0)
      | r1_tarski(k2_relat_1(sK4),X0) ) ),
    inference(forward_demodulation,[],[f173,f117])).

fof(f117,plain,(
    k2_relat_1(sK4) = k9_relat_1(sK4,sK1) ),
    inference(superposition,[],[f108,f116])).

fof(f116,plain,(
    sK4 = k7_relat_1(sK4,sK1) ),
    inference(resolution,[],[f114,f104])).

fof(f104,plain,(
    v4_relat_1(sK4,sK1) ),
    inference(resolution,[],[f78,f55])).

fof(f114,plain,(
    ! [X0] :
      ( ~ v4_relat_1(sK4,X0)
      | sK4 = k7_relat_1(sK4,X0) ) ),
    inference(resolution,[],[f71,f97])).

fof(f108,plain,(
    ! [X0] : k9_relat_1(sK4,X0) = k2_relat_1(k7_relat_1(sK4,X0)) ),
    inference(resolution,[],[f67,f97])).

fof(f173,plain,(
    ! [X0] :
      ( ~ v5_relat_1(sK4,X0)
      | r1_tarski(k9_relat_1(sK4,sK1),X0) ) ),
    inference(subsumption_resolution,[],[f172,f97])).

fof(f172,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK4)
      | ~ v5_relat_1(sK4,X0)
      | r1_tarski(k9_relat_1(sK4,sK1),X0) ) ),
    inference(superposition,[],[f110,f116])).

fof(f110,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(k7_relat_1(sK4,X0))
      | ~ v5_relat_1(k7_relat_1(sK4,X0),X1)
      | r1_tarski(k9_relat_1(sK4,X0),X1) ) ),
    inference(superposition,[],[f68,f108])).

fof(f195,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK2)
      | k10_relat_1(sK5,k9_relat_1(sK5,X0)) = X0 ) ),
    inference(forward_demodulation,[],[f194,f162])).

fof(f162,plain,(
    ! [X0] : k10_relat_1(sK5,X0) = k9_relat_1(k2_funct_1(sK5),X0) ),
    inference(subsumption_resolution,[],[f161,f98])).

fof(f161,plain,(
    ! [X0] :
      ( k10_relat_1(sK5,X0) = k9_relat_1(k2_funct_1(sK5),X0)
      | ~ v1_relat_1(sK5) ) ),
    inference(subsumption_resolution,[],[f160,f56])).

fof(f160,plain,(
    ! [X0] :
      ( k10_relat_1(sK5,X0) = k9_relat_1(k2_funct_1(sK5),X0)
      | ~ v1_funct_1(sK5)
      | ~ v1_relat_1(sK5) ) ),
    inference(resolution,[],[f70,f60])).

fof(f60,plain,(
    v2_funct_1(sK5) ),
    inference(cnf_transformation,[],[f46])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X1)
      | k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_1)).

fof(f194,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK2)
      | k9_relat_1(k2_funct_1(sK5),k9_relat_1(sK5,X0)) = X0 ) ),
    inference(forward_demodulation,[],[f193,f187])).

fof(f193,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_relat_1(sK5))
      | k9_relat_1(k2_funct_1(sK5),k9_relat_1(sK5,X0)) = X0 ) ),
    inference(subsumption_resolution,[],[f192,f98])).

fof(f192,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_relat_1(sK5))
      | k9_relat_1(k2_funct_1(sK5),k9_relat_1(sK5,X0)) = X0
      | ~ v1_relat_1(sK5) ) ),
    inference(subsumption_resolution,[],[f191,f56])).

fof(f191,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_relat_1(sK5))
      | k9_relat_1(k2_funct_1(sK5),k9_relat_1(sK5,X0)) = X0
      | ~ v1_funct_1(sK5)
      | ~ v1_relat_1(sK5) ) ),
    inference(resolution,[],[f65,f60])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X0)
      | ~ r1_tarski(X1,k1_relat_1(X0))
      | k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1
          | ~ r1_tarski(X1,k1_relat_1(X0))
          | ~ v2_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1
          | ~ r1_tarski(X1,k1_relat_1(X0))
          | ~ v2_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( r1_tarski(X1,k1_relat_1(X0))
            & v2_funct_1(X0) )
         => k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t177_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n020.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 18:21:07 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.19/0.43  % (4208)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.19/0.44  % (4224)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.19/0.47  % (4208)Refutation found. Thanks to Tanya!
% 0.19/0.47  % SZS status Theorem for theBenchmark
% 0.19/0.47  % SZS output start Proof for theBenchmark
% 0.19/0.47  fof(f350,plain,(
% 0.19/0.47    $false),
% 0.19/0.47    inference(subsumption_resolution,[],[f349,f142])).
% 0.19/0.47  fof(f142,plain,(
% 0.19/0.47    sK2 != k2_relat_1(sK4)),
% 0.19/0.47    inference(superposition,[],[f62,f140])).
% 0.19/0.47  fof(f140,plain,(
% 0.19/0.47    k2_relset_1(sK1,sK2,sK4) = k2_relat_1(sK4)),
% 0.19/0.47    inference(resolution,[],[f77,f55])).
% 0.19/0.47  fof(f55,plain,(
% 0.19/0.47    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.19/0.47    inference(cnf_transformation,[],[f46])).
% 0.19/0.47  fof(f46,plain,(
% 0.19/0.47    (sK2 != k2_relset_1(sK1,sK2,sK4) & k1_xboole_0 != sK3 & v2_funct_1(sK5) & sK3 = k2_relset_1(sK1,sK3,k1_partfun1(sK1,sK2,sK2,sK3,sK4,sK5)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK5,sK2,sK3) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4)),
% 0.19/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f20,f45,f44])).
% 0.19/0.47  fof(f44,plain,(
% 0.19/0.47    ? [X0,X1,X2,X3] : (? [X4] : (k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2 & v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (? [X4] : (sK2 != k2_relset_1(sK1,sK2,sK4) & k1_xboole_0 != sK3 & v2_funct_1(X4) & sK3 = k2_relset_1(sK1,sK3,k1_partfun1(sK1,sK2,sK2,sK3,sK4,X4)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(X4,sK2,sK3) & v1_funct_1(X4)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4))),
% 0.19/0.47    introduced(choice_axiom,[])).
% 0.19/0.47  fof(f45,plain,(
% 0.19/0.47    ? [X4] : (sK2 != k2_relset_1(sK1,sK2,sK4) & k1_xboole_0 != sK3 & v2_funct_1(X4) & sK3 = k2_relset_1(sK1,sK3,k1_partfun1(sK1,sK2,sK2,sK3,sK4,X4)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(X4,sK2,sK3) & v1_funct_1(X4)) => (sK2 != k2_relset_1(sK1,sK2,sK4) & k1_xboole_0 != sK3 & v2_funct_1(sK5) & sK3 = k2_relset_1(sK1,sK3,k1_partfun1(sK1,sK2,sK2,sK3,sK4,sK5)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK5,sK2,sK3) & v1_funct_1(sK5))),
% 0.19/0.47    introduced(choice_axiom,[])).
% 0.19/0.47  fof(f20,plain,(
% 0.19/0.47    ? [X0,X1,X2,X3] : (? [X4] : (k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2 & v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.19/0.47    inference(flattening,[],[f19])).
% 0.19/0.47  fof(f19,plain,(
% 0.19/0.47    ? [X0,X1,X2,X3] : (? [X4] : (((k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2) & (v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.19/0.47    inference(ennf_transformation,[],[f18])).
% 0.19/0.47  fof(f18,negated_conjecture,(
% 0.19/0.47    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2) => (k2_relset_1(X0,X1,X3) = X1 | k1_xboole_0 = X2))))),
% 0.19/0.47    inference(negated_conjecture,[],[f17])).
% 0.19/0.47  fof(f17,conjecture,(
% 0.19/0.47    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2) => (k2_relset_1(X0,X1,X3) = X1 | k1_xboole_0 = X2))))),
% 0.19/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_funct_2)).
% 0.19/0.47  fof(f77,plain,(
% 0.19/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f34])).
% 0.19/0.47  fof(f34,plain,(
% 0.19/0.47    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.47    inference(ennf_transformation,[],[f13])).
% 0.19/0.47  fof(f13,axiom,(
% 0.19/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.19/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.19/0.47  fof(f62,plain,(
% 0.19/0.47    sK2 != k2_relset_1(sK1,sK2,sK4)),
% 0.19/0.47    inference(cnf_transformation,[],[f46])).
% 0.19/0.47  fof(f349,plain,(
% 0.19/0.47    sK2 = k2_relat_1(sK4)),
% 0.19/0.47    inference(backward_demodulation,[],[f298,f344])).
% 0.19/0.47  fof(f344,plain,(
% 0.19/0.47    sK2 = k10_relat_1(sK5,sK3)),
% 0.19/0.47    inference(backward_demodulation,[],[f188,f328])).
% 0.19/0.47  fof(f328,plain,(
% 0.19/0.47    sK3 = k2_relat_1(sK5)),
% 0.19/0.47    inference(subsumption_resolution,[],[f324,f107])).
% 0.19/0.47  fof(f107,plain,(
% 0.19/0.47    v5_relat_1(sK5,sK3)),
% 0.19/0.47    inference(resolution,[],[f79,f58])).
% 0.19/0.47  fof(f58,plain,(
% 0.19/0.47    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 0.19/0.47    inference(cnf_transformation,[],[f46])).
% 0.19/0.47  fof(f79,plain,(
% 0.19/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f35])).
% 0.19/0.47  fof(f35,plain,(
% 0.19/0.47    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.47    inference(ennf_transformation,[],[f11])).
% 0.19/0.47  fof(f11,axiom,(
% 0.19/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.19/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.19/0.47  fof(f324,plain,(
% 0.19/0.47    ~v5_relat_1(sK5,sK3) | sK3 = k2_relat_1(sK5)),
% 0.19/0.47    inference(superposition,[],[f168,f295])).
% 0.19/0.47  fof(f295,plain,(
% 0.19/0.47    sK3 = k9_relat_1(sK5,k2_relat_1(sK4))),
% 0.19/0.47    inference(backward_demodulation,[],[f127,f294])).
% 0.19/0.47  fof(f294,plain,(
% 0.19/0.47    sK3 = k2_relat_1(k5_relat_1(sK4,sK5))),
% 0.19/0.47    inference(forward_demodulation,[],[f283,f209])).
% 0.19/0.47  fof(f209,plain,(
% 0.19/0.47    sK3 = k2_relset_1(sK1,sK3,k5_relat_1(sK4,sK5))),
% 0.19/0.47    inference(backward_demodulation,[],[f59,f208])).
% 0.19/0.47  fof(f208,plain,(
% 0.19/0.47    k1_partfun1(sK1,sK2,sK2,sK3,sK4,sK5) = k5_relat_1(sK4,sK5)),
% 0.19/0.47    inference(subsumption_resolution,[],[f206,f56])).
% 0.19/0.47  fof(f56,plain,(
% 0.19/0.47    v1_funct_1(sK5)),
% 0.19/0.47    inference(cnf_transformation,[],[f46])).
% 0.19/0.47  fof(f206,plain,(
% 0.19/0.47    ~v1_funct_1(sK5) | k1_partfun1(sK1,sK2,sK2,sK3,sK4,sK5) = k5_relat_1(sK4,sK5)),
% 0.19/0.47    inference(resolution,[],[f203,f58])).
% 0.19/0.47  fof(f203,plain,(
% 0.19/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X0) | k5_relat_1(sK4,X0) = k1_partfun1(sK1,sK2,X1,X2,sK4,X0)) )),
% 0.19/0.47    inference(subsumption_resolution,[],[f201,f53])).
% 0.19/0.47  fof(f53,plain,(
% 0.19/0.47    v1_funct_1(sK4)),
% 0.19/0.47    inference(cnf_transformation,[],[f46])).
% 0.19/0.47  fof(f201,plain,(
% 0.19/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X0) | k5_relat_1(sK4,X0) = k1_partfun1(sK1,sK2,X1,X2,sK4,X0) | ~v1_funct_1(sK4)) )),
% 0.19/0.47    inference(resolution,[],[f87,f55])).
% 0.19/0.47  fof(f87,plain,(
% 0.19/0.47    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~v1_funct_1(X4)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f39])).
% 0.19/0.47  fof(f39,plain,(
% 0.19/0.47    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 0.19/0.47    inference(flattening,[],[f38])).
% 0.19/0.47  fof(f38,plain,(
% 0.19/0.47    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 0.19/0.47    inference(ennf_transformation,[],[f16])).
% 0.19/0.47  fof(f16,axiom,(
% 0.19/0.47    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 0.19/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 0.19/0.47  fof(f59,plain,(
% 0.19/0.47    sK3 = k2_relset_1(sK1,sK3,k1_partfun1(sK1,sK2,sK2,sK3,sK4,sK5))),
% 0.19/0.47    inference(cnf_transformation,[],[f46])).
% 0.19/0.47  fof(f283,plain,(
% 0.19/0.47    k2_relat_1(k5_relat_1(sK4,sK5)) = k2_relset_1(sK1,sK3,k5_relat_1(sK4,sK5))),
% 0.19/0.47    inference(resolution,[],[f241,f77])).
% 0.19/0.47  fof(f241,plain,(
% 0.19/0.47    m1_subset_1(k5_relat_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))),
% 0.19/0.47    inference(forward_demodulation,[],[f240,f208])).
% 0.19/0.47  fof(f240,plain,(
% 0.19/0.47    m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))),
% 0.19/0.47    inference(subsumption_resolution,[],[f237,f56])).
% 0.19/0.47  fof(f237,plain,(
% 0.19/0.47    ~v1_funct_1(sK5) | m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))),
% 0.19/0.47    inference(resolution,[],[f221,f58])).
% 0.19/0.47  fof(f221,plain,(
% 0.19/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X0) | m1_subset_1(k1_partfun1(sK1,sK2,X1,X2,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(sK1,X2)))) )),
% 0.19/0.47    inference(subsumption_resolution,[],[f219,f53])).
% 0.19/0.47  fof(f219,plain,(
% 0.19/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X0) | m1_subset_1(k1_partfun1(sK1,sK2,X1,X2,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(sK1,X2))) | ~v1_funct_1(sK4)) )),
% 0.19/0.47    inference(resolution,[],[f89,f55])).
% 0.19/0.47  fof(f89,plain,(
% 0.19/0.47    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~v1_funct_1(X4)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f41])).
% 0.19/0.47  fof(f41,plain,(
% 0.19/0.47    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 0.19/0.47    inference(flattening,[],[f40])).
% 0.19/0.47  fof(f40,plain,(
% 0.19/0.47    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 0.19/0.47    inference(ennf_transformation,[],[f15])).
% 0.19/0.47  fof(f15,axiom,(
% 0.19/0.47    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 0.19/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 0.19/0.47  fof(f127,plain,(
% 0.19/0.47    k2_relat_1(k5_relat_1(sK4,sK5)) = k9_relat_1(sK5,k2_relat_1(sK4))),
% 0.19/0.47    inference(resolution,[],[f124,f98])).
% 0.19/0.47  fof(f98,plain,(
% 0.19/0.47    v1_relat_1(sK5)),
% 0.19/0.47    inference(resolution,[],[f75,f58])).
% 0.19/0.47  fof(f75,plain,(
% 0.19/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f32])).
% 0.19/0.47  fof(f32,plain,(
% 0.19/0.47    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.47    inference(ennf_transformation,[],[f10])).
% 0.19/0.47  fof(f10,axiom,(
% 0.19/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.19/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.19/0.47  fof(f124,plain,(
% 0.19/0.47    ( ! [X0] : (~v1_relat_1(X0) | k2_relat_1(k5_relat_1(sK4,X0)) = k9_relat_1(X0,k2_relat_1(sK4))) )),
% 0.19/0.47    inference(resolution,[],[f64,f97])).
% 0.19/0.47  fof(f97,plain,(
% 0.19/0.47    v1_relat_1(sK4)),
% 0.19/0.47    inference(resolution,[],[f75,f55])).
% 0.19/0.47  fof(f64,plain,(
% 0.19/0.47    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))) )),
% 0.19/0.47    inference(cnf_transformation,[],[f22])).
% 0.19/0.47  fof(f22,plain,(
% 0.19/0.47    ! [X0] : (! [X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.19/0.47    inference(ennf_transformation,[],[f5])).
% 0.19/0.47  fof(f5,axiom,(
% 0.19/0.47    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))))),
% 0.19/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).
% 0.19/0.47  fof(f168,plain,(
% 0.19/0.47    ( ! [X0] : (~v5_relat_1(sK5,k9_relat_1(sK5,X0)) | k9_relat_1(sK5,X0) = k2_relat_1(sK5)) )),
% 0.19/0.47    inference(subsumption_resolution,[],[f166,f98])).
% 0.19/0.47  fof(f166,plain,(
% 0.19/0.47    ( ! [X0] : (k9_relat_1(sK5,X0) = k2_relat_1(sK5) | ~v5_relat_1(sK5,k9_relat_1(sK5,X0)) | ~v1_relat_1(sK5)) )),
% 0.19/0.47    inference(resolution,[],[f163,f68])).
% 0.19/0.47  fof(f68,plain,(
% 0.19/0.47    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f47])).
% 0.19/0.47  fof(f47,plain,(
% 0.19/0.47    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.19/0.47    inference(nnf_transformation,[],[f27])).
% 0.19/0.47  fof(f27,plain,(
% 0.19/0.47    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.19/0.47    inference(ennf_transformation,[],[f2])).
% 0.19/0.47  fof(f2,axiom,(
% 0.19/0.47    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.19/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 0.19/0.47  fof(f163,plain,(
% 0.19/0.47    ( ! [X0] : (~r1_tarski(k2_relat_1(sK5),k9_relat_1(sK5,X0)) | k9_relat_1(sK5,X0) = k2_relat_1(sK5)) )),
% 0.19/0.47    inference(resolution,[],[f159,f74])).
% 0.19/0.47  fof(f74,plain,(
% 0.19/0.47    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.19/0.47    inference(cnf_transformation,[],[f49])).
% 0.19/0.47  fof(f49,plain,(
% 0.19/0.47    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.19/0.47    inference(flattening,[],[f48])).
% 0.19/0.47  fof(f48,plain,(
% 0.19/0.47    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.19/0.47    inference(nnf_transformation,[],[f1])).
% 0.19/0.47  fof(f1,axiom,(
% 0.19/0.47    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.19/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.19/0.47  fof(f159,plain,(
% 0.19/0.47    ( ! [X0] : (r1_tarski(k9_relat_1(sK5,X0),k2_relat_1(sK5))) )),
% 0.19/0.47    inference(forward_demodulation,[],[f158,f120])).
% 0.19/0.47  fof(f120,plain,(
% 0.19/0.47    k2_relat_1(sK5) = k9_relat_1(sK5,sK2)),
% 0.19/0.47    inference(superposition,[],[f109,f119])).
% 0.19/0.47  fof(f119,plain,(
% 0.19/0.47    sK5 = k7_relat_1(sK5,sK2)),
% 0.19/0.47    inference(resolution,[],[f115,f105])).
% 0.19/0.47  fof(f105,plain,(
% 0.19/0.47    v4_relat_1(sK5,sK2)),
% 0.19/0.47    inference(resolution,[],[f78,f58])).
% 0.19/0.47  fof(f78,plain,(
% 0.19/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f35])).
% 0.19/0.47  fof(f115,plain,(
% 0.19/0.47    ( ! [X1] : (~v4_relat_1(sK5,X1) | sK5 = k7_relat_1(sK5,X1)) )),
% 0.19/0.47    inference(resolution,[],[f71,f98])).
% 0.19/0.47  fof(f71,plain,(
% 0.19/0.47    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1) )),
% 0.19/0.47    inference(cnf_transformation,[],[f31])).
% 0.19/0.47  fof(f31,plain,(
% 0.19/0.47    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.19/0.47    inference(flattening,[],[f30])).
% 0.19/0.47  fof(f30,plain,(
% 0.19/0.47    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.19/0.47    inference(ennf_transformation,[],[f7])).
% 0.19/0.47  fof(f7,axiom,(
% 0.19/0.47    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.19/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).
% 0.19/0.47  fof(f109,plain,(
% 0.19/0.47    ( ! [X1] : (k9_relat_1(sK5,X1) = k2_relat_1(k7_relat_1(sK5,X1))) )),
% 0.19/0.47    inference(resolution,[],[f67,f98])).
% 0.19/0.47  fof(f67,plain,(
% 0.19/0.47    ( ! [X0,X1] : (~v1_relat_1(X1) | k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))) )),
% 0.19/0.47    inference(cnf_transformation,[],[f26])).
% 0.19/0.47  fof(f26,plain,(
% 0.19/0.47    ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 0.19/0.47    inference(ennf_transformation,[],[f4])).
% 0.19/0.47  fof(f4,axiom,(
% 0.19/0.47    ! [X0,X1] : (v1_relat_1(X1) => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)))),
% 0.19/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 0.19/0.47  fof(f158,plain,(
% 0.19/0.47    ( ! [X0] : (r1_tarski(k9_relat_1(sK5,X0),k9_relat_1(sK5,sK2))) )),
% 0.19/0.47    inference(subsumption_resolution,[],[f157,f98])).
% 0.19/0.47  fof(f157,plain,(
% 0.19/0.47    ( ! [X0] : (~v1_relat_1(sK5) | r1_tarski(k9_relat_1(sK5,X0),k9_relat_1(sK5,sK2))) )),
% 0.19/0.47    inference(superposition,[],[f113,f119])).
% 0.19/0.47  fof(f113,plain,(
% 0.19/0.47    ( ! [X2,X3] : (~v1_relat_1(k7_relat_1(sK5,X2)) | r1_tarski(k9_relat_1(k7_relat_1(sK5,X2),X3),k9_relat_1(sK5,X2))) )),
% 0.19/0.47    inference(superposition,[],[f66,f109])).
% 0.19/0.47  fof(f66,plain,(
% 0.19/0.47    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f25])).
% 0.19/0.47  fof(f25,plain,(
% 0.19/0.47    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.19/0.47    inference(ennf_transformation,[],[f3])).
% 0.19/0.47  fof(f3,axiom,(
% 0.19/0.47    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)))),
% 0.19/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).
% 0.19/0.47  fof(f188,plain,(
% 0.19/0.47    sK2 = k10_relat_1(sK5,k2_relat_1(sK5))),
% 0.19/0.47    inference(backward_demodulation,[],[f100,f187])).
% 0.19/0.47  fof(f187,plain,(
% 0.19/0.47    sK2 = k1_relat_1(sK5)),
% 0.19/0.47    inference(backward_demodulation,[],[f133,f186])).
% 0.19/0.47  fof(f186,plain,(
% 0.19/0.47    sK2 = k1_relset_1(sK2,sK3,sK5)),
% 0.19/0.47    inference(subsumption_resolution,[],[f185,f61])).
% 0.19/0.47  fof(f61,plain,(
% 0.19/0.47    k1_xboole_0 != sK3),
% 0.19/0.47    inference(cnf_transformation,[],[f46])).
% 0.19/0.47  fof(f185,plain,(
% 0.19/0.47    k1_xboole_0 = sK3 | sK2 = k1_relset_1(sK2,sK3,sK5)),
% 0.19/0.47    inference(subsumption_resolution,[],[f183,f57])).
% 0.19/0.47  fof(f57,plain,(
% 0.19/0.47    v1_funct_2(sK5,sK2,sK3)),
% 0.19/0.47    inference(cnf_transformation,[],[f46])).
% 0.19/0.47  fof(f183,plain,(
% 0.19/0.47    ~v1_funct_2(sK5,sK2,sK3) | k1_xboole_0 = sK3 | sK2 = k1_relset_1(sK2,sK3,sK5)),
% 0.19/0.47    inference(resolution,[],[f80,f123])).
% 0.19/0.47  fof(f123,plain,(
% 0.19/0.47    sP0(sK2,sK5,sK3)),
% 0.19/0.47    inference(resolution,[],[f84,f58])).
% 0.19/0.47  fof(f84,plain,(
% 0.19/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP0(X0,X2,X1)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f52])).
% 0.19/0.47  fof(f52,plain,(
% 0.19/0.47    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & sP0(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.47    inference(nnf_transformation,[],[f43])).
% 0.19/0.47  fof(f43,plain,(
% 0.19/0.47    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & sP0(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.47    inference(definition_folding,[],[f37,f42])).
% 0.19/0.47  fof(f42,plain,(
% 0.19/0.47    ! [X0,X2,X1] : ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X2,X1))),
% 0.19/0.47    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.19/0.47  fof(f37,plain,(
% 0.19/0.47    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.47    inference(flattening,[],[f36])).
% 0.19/0.47  fof(f36,plain,(
% 0.19/0.47    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.47    inference(ennf_transformation,[],[f14])).
% 0.19/0.47  fof(f14,axiom,(
% 0.19/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.19/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.19/0.47  fof(f80,plain,(
% 0.19/0.47    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | ~v1_funct_2(X1,X0,X2) | k1_xboole_0 = X2 | k1_relset_1(X0,X2,X1) = X0) )),
% 0.19/0.47    inference(cnf_transformation,[],[f51])).
% 0.19/0.47  fof(f51,plain,(
% 0.19/0.47    ! [X0,X1,X2] : (((v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0) & (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X2) | ~sP0(X0,X1,X2))),
% 0.19/0.47    inference(rectify,[],[f50])).
% 0.19/0.47  fof(f50,plain,(
% 0.19/0.47    ! [X0,X2,X1] : (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X2,X1))),
% 0.19/0.47    inference(nnf_transformation,[],[f42])).
% 0.19/0.47  fof(f133,plain,(
% 0.19/0.47    k1_relat_1(sK5) = k1_relset_1(sK2,sK3,sK5)),
% 0.19/0.47    inference(resolution,[],[f76,f58])).
% 0.19/0.47  fof(f76,plain,(
% 0.19/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f33])).
% 0.19/0.47  fof(f33,plain,(
% 0.19/0.47    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.47    inference(ennf_transformation,[],[f12])).
% 0.19/0.47  fof(f12,axiom,(
% 0.19/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.19/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.19/0.47  fof(f100,plain,(
% 0.19/0.47    k1_relat_1(sK5) = k10_relat_1(sK5,k2_relat_1(sK5))),
% 0.19/0.47    inference(resolution,[],[f63,f98])).
% 0.19/0.47  fof(f63,plain,(
% 0.19/0.47    ( ! [X0] : (~v1_relat_1(X0) | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f21])).
% 0.19/0.47  fof(f21,plain,(
% 0.19/0.47    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 0.19/0.47    inference(ennf_transformation,[],[f6])).
% 0.19/0.47  fof(f6,axiom,(
% 0.19/0.47    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 0.19/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).
% 0.19/0.47  fof(f298,plain,(
% 0.19/0.47    k2_relat_1(sK4) = k10_relat_1(sK5,sK3)),
% 0.19/0.47    inference(backward_demodulation,[],[f197,f295])).
% 0.19/0.47  fof(f197,plain,(
% 0.19/0.47    k2_relat_1(sK4) = k10_relat_1(sK5,k9_relat_1(sK5,k2_relat_1(sK4)))),
% 0.19/0.47    inference(resolution,[],[f195,f175])).
% 0.19/0.47  fof(f175,plain,(
% 0.19/0.47    r1_tarski(k2_relat_1(sK4),sK2)),
% 0.19/0.47    inference(resolution,[],[f174,f106])).
% 0.19/0.47  fof(f106,plain,(
% 0.19/0.47    v5_relat_1(sK4,sK2)),
% 0.19/0.47    inference(resolution,[],[f79,f55])).
% 0.19/0.47  fof(f174,plain,(
% 0.19/0.47    ( ! [X0] : (~v5_relat_1(sK4,X0) | r1_tarski(k2_relat_1(sK4),X0)) )),
% 0.19/0.47    inference(forward_demodulation,[],[f173,f117])).
% 0.19/0.47  fof(f117,plain,(
% 0.19/0.47    k2_relat_1(sK4) = k9_relat_1(sK4,sK1)),
% 0.19/0.47    inference(superposition,[],[f108,f116])).
% 0.19/0.47  fof(f116,plain,(
% 0.19/0.47    sK4 = k7_relat_1(sK4,sK1)),
% 0.19/0.47    inference(resolution,[],[f114,f104])).
% 0.19/0.47  fof(f104,plain,(
% 0.19/0.47    v4_relat_1(sK4,sK1)),
% 0.19/0.47    inference(resolution,[],[f78,f55])).
% 0.19/0.47  fof(f114,plain,(
% 0.19/0.47    ( ! [X0] : (~v4_relat_1(sK4,X0) | sK4 = k7_relat_1(sK4,X0)) )),
% 0.19/0.47    inference(resolution,[],[f71,f97])).
% 0.19/0.47  fof(f108,plain,(
% 0.19/0.47    ( ! [X0] : (k9_relat_1(sK4,X0) = k2_relat_1(k7_relat_1(sK4,X0))) )),
% 0.19/0.47    inference(resolution,[],[f67,f97])).
% 0.19/0.47  fof(f173,plain,(
% 0.19/0.47    ( ! [X0] : (~v5_relat_1(sK4,X0) | r1_tarski(k9_relat_1(sK4,sK1),X0)) )),
% 0.19/0.47    inference(subsumption_resolution,[],[f172,f97])).
% 0.19/0.47  fof(f172,plain,(
% 0.19/0.47    ( ! [X0] : (~v1_relat_1(sK4) | ~v5_relat_1(sK4,X0) | r1_tarski(k9_relat_1(sK4,sK1),X0)) )),
% 0.19/0.47    inference(superposition,[],[f110,f116])).
% 0.19/0.47  fof(f110,plain,(
% 0.19/0.47    ( ! [X0,X1] : (~v1_relat_1(k7_relat_1(sK4,X0)) | ~v5_relat_1(k7_relat_1(sK4,X0),X1) | r1_tarski(k9_relat_1(sK4,X0),X1)) )),
% 0.19/0.47    inference(superposition,[],[f68,f108])).
% 0.19/0.47  fof(f195,plain,(
% 0.19/0.47    ( ! [X0] : (~r1_tarski(X0,sK2) | k10_relat_1(sK5,k9_relat_1(sK5,X0)) = X0) )),
% 0.19/0.47    inference(forward_demodulation,[],[f194,f162])).
% 0.19/0.47  fof(f162,plain,(
% 0.19/0.47    ( ! [X0] : (k10_relat_1(sK5,X0) = k9_relat_1(k2_funct_1(sK5),X0)) )),
% 0.19/0.47    inference(subsumption_resolution,[],[f161,f98])).
% 0.19/0.47  fof(f161,plain,(
% 0.19/0.47    ( ! [X0] : (k10_relat_1(sK5,X0) = k9_relat_1(k2_funct_1(sK5),X0) | ~v1_relat_1(sK5)) )),
% 0.19/0.47    inference(subsumption_resolution,[],[f160,f56])).
% 0.19/0.47  fof(f160,plain,(
% 0.19/0.47    ( ! [X0] : (k10_relat_1(sK5,X0) = k9_relat_1(k2_funct_1(sK5),X0) | ~v1_funct_1(sK5) | ~v1_relat_1(sK5)) )),
% 0.19/0.47    inference(resolution,[],[f70,f60])).
% 0.19/0.47  fof(f60,plain,(
% 0.19/0.47    v2_funct_1(sK5)),
% 0.19/0.47    inference(cnf_transformation,[],[f46])).
% 0.19/0.47  fof(f70,plain,(
% 0.19/0.47    ( ! [X0,X1] : (~v2_funct_1(X1) | k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f29])).
% 0.19/0.47  fof(f29,plain,(
% 0.19/0.47    ! [X0,X1] : (k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.19/0.47    inference(flattening,[],[f28])).
% 0.19/0.47  fof(f28,plain,(
% 0.19/0.47    ! [X0,X1] : ((k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.19/0.47    inference(ennf_transformation,[],[f8])).
% 0.19/0.47  fof(f8,axiom,(
% 0.19/0.47    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)))),
% 0.19/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_1)).
% 0.19/0.47  fof(f194,plain,(
% 0.19/0.47    ( ! [X0] : (~r1_tarski(X0,sK2) | k9_relat_1(k2_funct_1(sK5),k9_relat_1(sK5,X0)) = X0) )),
% 0.19/0.47    inference(forward_demodulation,[],[f193,f187])).
% 0.19/0.47  fof(f193,plain,(
% 0.19/0.47    ( ! [X0] : (~r1_tarski(X0,k1_relat_1(sK5)) | k9_relat_1(k2_funct_1(sK5),k9_relat_1(sK5,X0)) = X0) )),
% 0.19/0.47    inference(subsumption_resolution,[],[f192,f98])).
% 0.19/0.47  fof(f192,plain,(
% 0.19/0.47    ( ! [X0] : (~r1_tarski(X0,k1_relat_1(sK5)) | k9_relat_1(k2_funct_1(sK5),k9_relat_1(sK5,X0)) = X0 | ~v1_relat_1(sK5)) )),
% 0.19/0.47    inference(subsumption_resolution,[],[f191,f56])).
% 0.19/0.47  fof(f191,plain,(
% 0.19/0.47    ( ! [X0] : (~r1_tarski(X0,k1_relat_1(sK5)) | k9_relat_1(k2_funct_1(sK5),k9_relat_1(sK5,X0)) = X0 | ~v1_funct_1(sK5) | ~v1_relat_1(sK5)) )),
% 0.19/0.47    inference(resolution,[],[f65,f60])).
% 0.19/0.47  fof(f65,plain,(
% 0.19/0.47    ( ! [X0,X1] : (~v2_funct_1(X0) | ~r1_tarski(X1,k1_relat_1(X0)) | k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f24])).
% 0.19/0.47  fof(f24,plain,(
% 0.19/0.47    ! [X0] : (! [X1] : (k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1 | ~r1_tarski(X1,k1_relat_1(X0)) | ~v2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.19/0.47    inference(flattening,[],[f23])).
% 0.19/0.47  fof(f23,plain,(
% 0.19/0.47    ! [X0] : (! [X1] : (k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1 | (~r1_tarski(X1,k1_relat_1(X0)) | ~v2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.19/0.47    inference(ennf_transformation,[],[f9])).
% 0.19/0.47  fof(f9,axiom,(
% 0.19/0.47    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((r1_tarski(X1,k1_relat_1(X0)) & v2_funct_1(X0)) => k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1))),
% 0.19/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t177_funct_1)).
% 0.19/0.47  % SZS output end Proof for theBenchmark
% 0.19/0.47  % (4208)------------------------------
% 0.19/0.47  % (4208)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.47  % (4208)Termination reason: Refutation
% 0.19/0.47  
% 0.19/0.47  % (4208)Memory used [KB]: 6524
% 0.19/0.47  % (4208)Time elapsed: 0.074 s
% 0.19/0.47  % (4208)------------------------------
% 0.19/0.47  % (4208)------------------------------
% 0.19/0.47  % (4204)Success in time 0.125 s
%------------------------------------------------------------------------------
