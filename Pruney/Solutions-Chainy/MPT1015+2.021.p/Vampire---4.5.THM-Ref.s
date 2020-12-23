%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:05:28 EST 2020

% Result     : Theorem 3.79s
% Output     : Refutation 3.79s
% Verified   : 
% Statistics : Number of formulae       :  201 (3286 expanded)
%              Number of leaves         :   26 ( 974 expanded)
%              Depth                    :   50
%              Number of atoms          : 1011 (24068 expanded)
%              Number of equality atoms :  183 (1144 expanded)
%              Maximal formula depth    :   23 (   8 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1271,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f125,f1247,f120])).

fof(f120,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(duplicate_literal_removal,[],[f119])).

fof(f119,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f108])).

fof(f108,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f1247,plain,(
    ~ r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f1090,f1232])).

fof(f1232,plain,(
    k1_xboole_0 = sK4 ),
    inference(subsumption_resolution,[],[f1230,f86])).

fof(f86,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f1230,plain,
    ( k1_xboole_0 = sK4
    | ~ v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) ),
    inference(resolution,[],[f1183,f1044])).

fof(f1044,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f67,f1040])).

fof(f1040,plain,(
    k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f1037,f67])).

fof(f1037,plain,
    ( k1_xboole_0 = sK2
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(resolution,[],[f953,f120])).

fof(f953,plain,
    ( ~ r2_relset_1(sK2,sK2,sK4,sK4)
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f70,f950])).

fof(f950,plain,
    ( k6_partfun1(sK2) = sK4
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f947,f64])).

fof(f64,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,
    ( ~ r2_relset_1(sK2,sK2,sK4,k6_partfun1(sK2))
    & v2_funct_1(sK3)
    & r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3),sK3)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    & v1_funct_2(sK4,sK2,sK2)
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    & v1_funct_2(sK3,sK2,sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f23,f52,f51])).

fof(f51,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r2_relset_1(X0,X0,X2,k6_partfun1(X0))
            & v2_funct_1(X1)
            & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v1_funct_2(X2,X0,X0)
            & v1_funct_1(X2) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
   => ( ? [X2] :
          ( ~ r2_relset_1(sK2,sK2,X2,k6_partfun1(sK2))
          & v2_funct_1(sK3)
          & r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,X2,sK3),sK3)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
          & v1_funct_2(X2,sK2,sK2)
          & v1_funct_1(X2) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
      & v1_funct_2(sK3,sK2,sK2)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,
    ( ? [X2] :
        ( ~ r2_relset_1(sK2,sK2,X2,k6_partfun1(sK2))
        & v2_funct_1(sK3)
        & r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,X2,sK3),sK3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
        & v1_funct_2(X2,sK2,sK2)
        & v1_funct_1(X2) )
   => ( ~ r2_relset_1(sK2,sK2,sK4,k6_partfun1(sK2))
      & v2_funct_1(sK3)
      & r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3),sK3)
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
      & v1_funct_2(sK4,sK2,sK2)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X2,k6_partfun1(X0))
          & v2_funct_1(X1)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X2,k6_partfun1(X0))
          & v2_funct_1(X1)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ! [X2] :
            ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v1_funct_2(X2,X0,X0)
              & v1_funct_1(X2) )
           => ( ( v2_funct_1(X1)
                & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1) )
             => r2_relset_1(X0,X0,X2,k6_partfun1(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v1_funct_2(X2,X0,X0)
            & v1_funct_1(X2) )
         => ( ( v2_funct_1(X1)
              & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1) )
           => r2_relset_1(X0,X0,X2,k6_partfun1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_funct_2)).

fof(f947,plain,
    ( k1_xboole_0 = sK2
    | k6_partfun1(sK2) = sK4
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(resolution,[],[f936,f189])).

fof(f189,plain,(
    ! [X2,X0,X1] :
      ( r2_relset_1(X0,X1,k5_relat_1(k6_partfun1(X0),X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(subsumption_resolution,[],[f188,f75])).

fof(f75,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f188,plain,(
    ! [X2,X0,X1] :
      ( r2_relset_1(X0,X1,k5_relat_1(k6_partfun1(X0),X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(duplicate_literal_removal,[],[f185])).

fof(f185,plain,(
    ! [X2,X0,X1] :
      ( r2_relset_1(X0,X1,k5_relat_1(k6_partfun1(X0),X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(superposition,[],[f90,f112])).

fof(f112,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2)
        & r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2)
        & r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_2)).

fof(f936,plain,
    ( ~ r2_relset_1(sK2,sK2,k5_relat_1(k6_partfun1(sK2),sK3),sK3)
    | k1_xboole_0 = sK2
    | k6_partfun1(sK2) = sK4 ),
    inference(subsumption_resolution,[],[f935,f902])).

fof(f902,plain,(
    v1_funct_1(k6_partfun1(sK2)) ),
    inference(resolution,[],[f900,f64])).

fof(f900,plain,(
    ! [X6,X7] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
      | v1_funct_1(k6_partfun1(sK2)) ) ),
    inference(subsumption_resolution,[],[f897,f86])).

fof(f897,plain,(
    ! [X6,X7] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
      | v1_funct_1(k6_partfun1(sK2))
      | ~ v1_relat_1(k2_zfmisc_1(sK2,sK2)) ) ),
    inference(resolution,[],[f886,f64])).

fof(f886,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(X2))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_funct_1(k6_partfun1(sK2))
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f885,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f885,plain,(
    ! [X8,X9] :
      ( ~ v1_relat_1(sK3)
      | v1_funct_1(k6_partfun1(sK2))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X8,X9))) ) ),
    inference(subsumption_resolution,[],[f883,f166])).

fof(f166,plain,
    ( v1_funct_2(sK3,sK2,k2_relat_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f164,f62])).

fof(f62,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f53])).

fof(f164,plain,
    ( v1_funct_2(sK3,sK2,k2_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(superposition,[],[f82,f161])).

fof(f161,plain,(
    sK2 = k1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f159,f64])).

fof(f159,plain,
    ( sK2 = k1_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(superposition,[],[f156,f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f156,plain,(
    sK2 = k1_relset_1(sK2,sK2,sK3) ),
    inference(subsumption_resolution,[],[f155,f62])).

fof(f155,plain,
    ( sK2 = k1_relset_1(sK2,sK2,sK3)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f151,f64])).

fof(f151,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | sK2 = k1_relset_1(sK2,sK2,sK3)
    | ~ v1_funct_1(sK3) ),
    inference(resolution,[],[f87,f63])).

fof(f63,plain,(
    v1_funct_2(sK3,sK2,sK2) ),
    inference(cnf_transformation,[],[f53])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(X1,X0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | k1_relset_1(X0,X0,X1) = X0
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k1_relset_1(X0,X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_2)).

fof(f82,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

fof(f883,plain,(
    ! [X8,X9] :
      ( ~ v1_funct_2(sK3,sK2,k2_relat_1(sK3))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))
      | v1_funct_1(k6_partfun1(sK2))
      | ~ v1_relat_1(sK3) ) ),
    inference(trivial_inequality_removal,[],[f882])).

fof(f882,plain,(
    ! [X8,X9] :
      ( ~ v1_funct_2(sK3,sK2,k2_relat_1(sK3))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))
      | v1_funct_1(k6_partfun1(sK2))
      | k2_relat_1(sK3) != k2_relat_1(sK3)
      | ~ v1_relat_1(sK3) ) ),
    inference(resolution,[],[f871,f162])).

fof(f162,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_relat_1(sK3))))
    | ~ v1_relat_1(sK3) ),
    inference(backward_demodulation,[],[f146,f161])).

fof(f146,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))))
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f83,f62])).

fof(f83,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f871,plain,(
    ! [X10,X8,X11,X9] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))
      | ~ v1_funct_2(sK3,X8,X9)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))
      | v1_funct_1(k6_partfun1(sK2))
      | k2_relat_1(sK3) != X9 ) ),
    inference(subsumption_resolution,[],[f868,f86])).

fof(f868,plain,(
    ! [X10,X8,X11,X9] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))
      | ~ v1_funct_2(sK3,X8,X9)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))
      | v1_funct_1(k6_partfun1(sK2))
      | k2_relat_1(sK3) != X9
      | ~ v1_relat_1(k2_zfmisc_1(sK2,sK2)) ) ),
    inference(resolution,[],[f851,f64])).

fof(f851,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(X4))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(sK3,X1,X0)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | v1_funct_1(k6_partfun1(sK2))
      | k2_relat_1(sK3) != X0
      | ~ v1_relat_1(X4) ) ),
    inference(resolution,[],[f848,f80])).

fof(f848,plain,(
    ! [X14,X12,X15,X13] :
      ( ~ v1_relat_1(sK3)
      | k2_relat_1(sK3) != X12
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X13,X12)))
      | ~ v1_funct_2(sK3,X13,X12)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X14,X15)))
      | v1_funct_1(k6_partfun1(sK2)) ) ),
    inference(subsumption_resolution,[],[f846,f166])).

fof(f846,plain,(
    ! [X14,X12,X15,X13] :
      ( v1_funct_1(k6_partfun1(sK2))
      | k2_relat_1(sK3) != X12
      | ~ v1_funct_2(sK3,sK2,k2_relat_1(sK3))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X13,X12)))
      | ~ v1_funct_2(sK3,X13,X12)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X14,X15)))
      | ~ v1_relat_1(sK3) ) ),
    inference(trivial_inequality_removal,[],[f845])).

fof(f845,plain,(
    ! [X14,X12,X15,X13] :
      ( v1_funct_1(k6_partfun1(sK2))
      | k2_relat_1(sK3) != X12
      | ~ v1_funct_2(sK3,sK2,k2_relat_1(sK3))
      | k2_relat_1(sK3) != k2_relat_1(sK3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X13,X12)))
      | ~ v1_funct_2(sK3,X13,X12)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X14,X15)))
      | ~ v1_relat_1(sK3) ) ),
    inference(resolution,[],[f838,f162])).

fof(f838,plain,(
    ! [X14,X12,X10,X15,X13,X11] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))
      | v1_funct_1(k6_partfun1(sK2))
      | k2_relat_1(sK3) != X10
      | ~ v1_funct_2(sK3,X11,X12)
      | k2_relat_1(sK3) != X12
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X13,X10)))
      | ~ v1_funct_2(sK3,X13,X10)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X14,X15))) ) ),
    inference(subsumption_resolution,[],[f835,f86])).

fof(f835,plain,(
    ! [X14,X12,X10,X15,X13,X11] :
      ( k2_relat_1(sK3) != X10
      | v1_funct_1(k6_partfun1(sK2))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))
      | ~ v1_funct_2(sK3,X11,X12)
      | k2_relat_1(sK3) != X12
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X13,X10)))
      | ~ v1_funct_2(sK3,X13,X10)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X14,X15)))
      | ~ v1_relat_1(k2_zfmisc_1(sK2,sK2)) ) ),
    inference(resolution,[],[f822,f64])).

fof(f822,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(X6))
      | k2_relat_1(sK3) != X2
      | v1_funct_1(k6_partfun1(sK2))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_2(sK3,X3,X4)
      | k2_relat_1(sK3) != X4
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X5,X2)))
      | ~ v1_funct_2(sK3,X5,X2)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_relat_1(X6) ) ),
    inference(resolution,[],[f821,f80])).

fof(f821,plain,(
    ! [X26,X24,X23,X27,X25,X22] :
      ( ~ v1_relat_1(sK3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X22,X23)))
      | k2_relat_1(sK3) != X24
      | v1_funct_1(k6_partfun1(sK2))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))
      | ~ v1_funct_2(sK3,X25,X26)
      | k2_relat_1(sK3) != X26
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X27,X24)))
      | ~ v1_funct_2(sK3,X27,X24) ) ),
    inference(forward_demodulation,[],[f820,f161])).

fof(f820,plain,(
    ! [X26,X24,X23,X27,X25,X22] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X22,X23)))
      | k2_relat_1(sK3) != X24
      | ~ v1_relat_1(sK3)
      | v1_funct_1(k6_partfun1(k1_relat_1(sK3)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))
      | ~ v1_funct_2(sK3,X25,X26)
      | k2_relat_1(sK3) != X26
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X27,X24)))
      | ~ v1_funct_2(sK3,X27,X24) ) ),
    inference(subsumption_resolution,[],[f812,f62])).

fof(f812,plain,(
    ! [X26,X24,X23,X27,X25,X22] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X22,X23)))
      | ~ v1_funct_1(sK3)
      | k2_relat_1(sK3) != X24
      | ~ v1_relat_1(sK3)
      | v1_funct_1(k6_partfun1(k1_relat_1(sK3)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))
      | ~ v1_funct_2(sK3,X25,X26)
      | k2_relat_1(sK3) != X26
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X27,X24)))
      | ~ v1_funct_2(sK3,X27,X24) ) ),
    inference(resolution,[],[f618,f69])).

fof(f69,plain,(
    v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f53])).

fof(f618,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_1(X2)
      | k2_relat_1(X2) != X1
      | ~ v1_relat_1(X2)
      | v1_funct_1(k6_partfun1(k1_relat_1(X2)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
      | ~ v1_funct_2(X2,X5,X6)
      | k2_relat_1(X2) != X6
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f617])).

fof(f617,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( k2_relat_1(X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_1(X2)
      | ~ v2_funct_1(X2)
      | ~ v1_relat_1(X2)
      | v1_funct_1(k6_partfun1(k1_relat_1(X2)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
      | ~ v1_funct_2(X2,X5,X6)
      | k2_relat_1(X2) != X6
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(superposition,[],[f515,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f515,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( k2_relset_1(X5,X6,X2) != X6
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_1(X2)
      | ~ v2_funct_1(X2)
      | ~ v1_relat_1(X2)
      | v1_funct_1(k6_partfun1(k1_relat_1(X2)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k2_relat_1(X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
      | ~ v1_funct_2(X2,X5,X6) ) ),
    inference(duplicate_literal_removal,[],[f514])).

fof(f514,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( k2_relat_1(X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_1(X2)
      | ~ v2_funct_1(X2)
      | ~ v1_relat_1(X2)
      | v1_funct_1(k6_partfun1(k1_relat_1(X2)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k2_relset_1(X5,X6,X2) != X6
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
      | ~ v1_funct_2(X2,X5,X6)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(superposition,[],[f407,f89])).

fof(f407,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( k2_relset_1(X3,X4,X0) != X4
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v1_funct_1(k6_partfun1(k1_relat_1(X0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_2(X0,X3,X4)
      | k2_relset_1(X5,X6,X0) != X6
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
      | ~ v1_funct_2(X0,X5,X6) ) ),
    inference(duplicate_literal_removal,[],[f404])).

fof(f404,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( v1_funct_1(k6_partfun1(k1_relat_1(X0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k2_relset_1(X3,X4,X0) != X4
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_2(X0,X3,X4)
      | k2_relset_1(X5,X6,X0) != X6
      | ~ v2_funct_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
      | ~ v1_funct_2(X0,X5,X6)
      | ~ v1_funct_1(X0) ) ),
    inference(resolution,[],[f335,f94])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

fof(f335,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | v1_funct_1(k6_partfun1(k1_relat_1(X0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k2_relset_1(X5,X6,X0) != X6
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
      | ~ v1_funct_2(X0,X5,X6) ) ),
    inference(duplicate_literal_removal,[],[f334])).

fof(f334,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | v1_funct_1(k6_partfun1(k1_relat_1(X0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k2_relset_1(X5,X6,X0) != X6
      | ~ v2_funct_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
      | ~ v1_funct_2(X0,X5,X6)
      | ~ v1_funct_1(X0) ) ),
    inference(resolution,[],[f254,f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(k2_funct_1(X2))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f254,plain,(
    ! [X6,X8,X7,X5,X9] :
      ( ~ v1_funct_1(k2_funct_1(X5))
      | ~ m1_subset_1(k2_funct_1(X5),k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
      | v1_funct_1(k6_partfun1(k1_relat_1(X5)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))
      | ~ v1_funct_1(X5)
      | ~ v2_funct_1(X5)
      | ~ v1_relat_1(X5) ) ),
    inference(duplicate_literal_removal,[],[f252])).

fof(f252,plain,(
    ! [X6,X8,X7,X5,X9] :
      ( v1_funct_1(k6_partfun1(k1_relat_1(X5)))
      | ~ m1_subset_1(k2_funct_1(X5),k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
      | ~ v1_funct_1(k2_funct_1(X5))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))
      | ~ v1_funct_1(X5)
      | ~ v2_funct_1(X5)
      | ~ v1_funct_1(X5)
      | ~ v1_relat_1(X5) ) ),
    inference(superposition,[],[f211,f118])).

fof(f118,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f84,f71])).

fof(f71,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f84,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

fof(f211,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_1(k5_relat_1(X4,X5))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(duplicate_literal_removal,[],[f210])).

fof(f210,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_1(k5_relat_1(X4,X5))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(superposition,[],[f110,f109])).

fof(f109,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

% (6499)Time limit reached!
% (6499)------------------------------
% (6499)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f110,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f935,plain,
    ( k1_xboole_0 = sK2
    | ~ r2_relset_1(sK2,sK2,k5_relat_1(k6_partfun1(sK2),sK3),sK3)
    | ~ v1_funct_1(k6_partfun1(sK2))
    | k6_partfun1(sK2) = sK4 ),
    inference(subsumption_resolution,[],[f925,f75])).

fof(f925,plain,
    ( k1_xboole_0 = sK2
    | ~ m1_subset_1(k6_partfun1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ r2_relset_1(sK2,sK2,k5_relat_1(k6_partfun1(sK2),sK3),sK3)
    | ~ v1_funct_1(k6_partfun1(sK2))
    | k6_partfun1(sK2) = sK4 ),
    inference(resolution,[],[f906,f480])).

fof(f480,plain,(
    ! [X0] :
      ( ~ v1_funct_2(X0,sK2,sK2)
      | k1_xboole_0 = sK2
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
      | ~ r2_relset_1(sK2,sK2,k5_relat_1(X0,sK3),sK3)
      | ~ v1_funct_1(X0)
      | sK4 = X0 ) ),
    inference(subsumption_resolution,[],[f479,f62])).

fof(f479,plain,(
    ! [X0] :
      ( ~ r2_relset_1(sK2,sK2,k5_relat_1(X0,sK3),sK3)
      | k1_xboole_0 = sK2
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
      | ~ v1_funct_2(X0,sK2,sK2)
      | ~ v1_funct_1(X0)
      | sK4 = X0
      | ~ v1_funct_1(sK3) ) ),
    inference(subsumption_resolution,[],[f474,f64])).

fof(f474,plain,(
    ! [X0] :
      ( ~ r2_relset_1(sK2,sK2,k5_relat_1(X0,sK3),sK3)
      | k1_xboole_0 = sK2
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
      | ~ v1_funct_2(X0,sK2,sK2)
      | ~ v1_funct_1(X0)
      | sK4 = X0
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
      | ~ v1_funct_1(sK3) ) ),
    inference(duplicate_literal_removal,[],[f473])).

fof(f473,plain,(
    ! [X0] :
      ( ~ r2_relset_1(sK2,sK2,k5_relat_1(X0,sK3),sK3)
      | k1_xboole_0 = sK2
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
      | ~ v1_funct_2(X0,sK2,sK2)
      | ~ v1_funct_1(X0)
      | sK4 = X0
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
      | ~ v1_funct_1(sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
      | ~ v1_funct_1(X0) ) ),
    inference(superposition,[],[f466,f109])).

fof(f466,plain,(
    ! [X4] :
      ( ~ r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,X4,sK3),sK3)
      | k1_xboole_0 = sK2
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
      | ~ v1_funct_2(X4,sK2,sK2)
      | ~ v1_funct_1(X4)
      | sK4 = X4 ) ),
    inference(forward_demodulation,[],[f465,f228])).

fof(f228,plain,(
    sK3 = k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3) ),
    inference(subsumption_resolution,[],[f227,f65])).

fof(f65,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f53])).

fof(f227,plain,
    ( ~ v1_funct_1(sK4)
    | sK3 = k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3) ),
    inference(subsumption_resolution,[],[f226,f67])).

fof(f226,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v1_funct_1(sK4)
    | sK3 = k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3) ),
    inference(subsumption_resolution,[],[f225,f62])).

fof(f225,plain,
    ( ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v1_funct_1(sK4)
    | sK3 = k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3) ),
    inference(subsumption_resolution,[],[f221,f64])).

fof(f221,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v1_funct_1(sK4)
    | sK3 = k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3) ),
    inference(resolution,[],[f111,f182])).

fof(f182,plain,
    ( ~ m1_subset_1(k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | sK3 = k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3) ),
    inference(subsumption_resolution,[],[f175,f64])).

fof(f175,plain,
    ( sK3 = k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ m1_subset_1(k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(resolution,[],[f107,f68])).

fof(f68,plain,(
    r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3),sK3) ),
    inference(cnf_transformation,[],[f53])).

fof(f107,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f111,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f465,plain,(
    ! [X4] :
      ( ~ r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,X4,sK3),k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3))
      | k1_xboole_0 = sK2
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
      | ~ v1_funct_2(X4,sK2,sK2)
      | ~ v1_funct_1(X4)
      | sK4 = X4 ) ),
    inference(subsumption_resolution,[],[f464,f65])).

fof(f464,plain,(
    ! [X4] :
      ( ~ r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,X4,sK3),k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3))
      | k1_xboole_0 = sK2
      | ~ v1_funct_1(sK4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
      | ~ v1_funct_2(X4,sK2,sK2)
      | ~ v1_funct_1(X4)
      | sK4 = X4 ) ),
    inference(subsumption_resolution,[],[f457,f67])).

fof(f457,plain,(
    ! [X4] :
      ( ~ r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,X4,sK3),k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
      | k1_xboole_0 = sK2
      | ~ v1_funct_1(sK4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
      | ~ v1_funct_2(X4,sK2,sK2)
      | ~ v1_funct_1(X4)
      | sK4 = X4 ) ),
    inference(resolution,[],[f451,f66])).

fof(f66,plain,(
    v1_funct_2(sK4,sK2,sK2) ),
    inference(cnf_transformation,[],[f53])).

fof(f451,plain,(
    ! [X8,X7,X9] :
      ( ~ v1_funct_2(X9,X7,sK2)
      | ~ r2_relset_1(X7,sK2,k1_partfun1(X7,sK2,sK2,sK2,X8,sK3),k1_partfun1(X7,sK2,sK2,sK2,X9,sK3))
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,sK2)))
      | k1_xboole_0 = sK2
      | ~ v1_funct_1(X9)
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X7,sK2)))
      | ~ v1_funct_2(X8,X7,sK2)
      | ~ v1_funct_1(X8)
      | X8 = X9 ) ),
    inference(subsumption_resolution,[],[f450,f63])).

fof(f450,plain,(
    ! [X8,X7,X9] :
      ( ~ v1_funct_2(sK3,sK2,sK2)
      | k1_xboole_0 = sK2
      | ~ r2_relset_1(X7,sK2,k1_partfun1(X7,sK2,sK2,sK2,X8,sK3),k1_partfun1(X7,sK2,sK2,sK2,X9,sK3))
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,sK2)))
      | ~ v1_funct_2(X9,X7,sK2)
      | ~ v1_funct_1(X9)
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X7,sK2)))
      | ~ v1_funct_2(X8,X7,sK2)
      | ~ v1_funct_1(X8)
      | X8 = X9 ) ),
    inference(duplicate_literal_removal,[],[f448])).

fof(f448,plain,(
    ! [X8,X7,X9] :
      ( ~ v1_funct_2(sK3,sK2,sK2)
      | k1_xboole_0 = sK2
      | ~ r2_relset_1(X7,sK2,k1_partfun1(X7,sK2,sK2,sK2,X8,sK3),k1_partfun1(X7,sK2,sK2,sK2,X9,sK3))
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,sK2)))
      | ~ v1_funct_2(X9,X7,sK2)
      | ~ v1_funct_1(X9)
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X7,sK2)))
      | ~ v1_funct_2(X8,X7,sK2)
      | ~ v1_funct_1(X8)
      | k1_xboole_0 = sK2
      | X8 = X9 ) ),
    inference(resolution,[],[f439,f64])).

fof(f439,plain,(
    ! [X23,X21,X19,X22,X20] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))
      | ~ v1_funct_2(sK3,X19,X20)
      | k1_xboole_0 = X20
      | ~ r2_relset_1(X21,X20,k1_partfun1(X21,X19,X19,X20,X22,sK3),k1_partfun1(X21,X19,X19,X20,X23,sK3))
      | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X19)))
      | ~ v1_funct_2(X23,X21,X19)
      | ~ v1_funct_1(X23)
      | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X21,X19)))
      | ~ v1_funct_2(X22,X21,X19)
      | ~ v1_funct_1(X22)
      | k1_xboole_0 = X19
      | X22 = X23 ) ),
    inference(subsumption_resolution,[],[f438,f62])).

fof(f438,plain,(
    ! [X23,X21,X19,X22,X20] :
      ( ~ v1_funct_2(sK3,X19,X20)
      | ~ v1_funct_1(sK3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))
      | k1_xboole_0 = X20
      | ~ r2_relset_1(X21,X20,k1_partfun1(X21,X19,X19,X20,X22,sK3),k1_partfun1(X21,X19,X19,X20,X23,sK3))
      | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X19)))
      | ~ v1_funct_2(X23,X21,X19)
      | ~ v1_funct_1(X23)
      | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X21,X19)))
      | ~ v1_funct_2(X22,X21,X19)
      | ~ v1_funct_1(X22)
      | k1_xboole_0 = X19
      | X22 = X23 ) ),
    inference(resolution,[],[f366,f69])).

fof(f366,plain,(
    ! [X12,X10,X8,X7,X11,X9] :
      ( ~ v2_funct_1(X7)
      | ~ v1_funct_2(X7,X8,X9)
      | ~ v1_funct_1(X7)
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))
      | k1_xboole_0 = X9
      | ~ r2_relset_1(X10,X9,k1_partfun1(X10,X8,X8,X9,X11,X7),k1_partfun1(X10,X8,X8,X9,X12,X7))
      | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X8)))
      | ~ v1_funct_2(X12,X10,X8)
      | ~ v1_funct_1(X12)
      | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X10,X8)))
      | ~ v1_funct_2(X11,X10,X8)
      | ~ v1_funct_1(X11)
      | k1_xboole_0 = X8
      | X11 = X12 ) ),
    inference(duplicate_literal_removal,[],[f365])).

fof(f365,plain,(
    ! [X12,X10,X8,X7,X11,X9] :
      ( ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))
      | ~ v1_funct_2(X7,X8,X9)
      | ~ v1_funct_1(X7)
      | ~ v2_funct_1(X7)
      | k1_xboole_0 = X9
      | ~ r2_relset_1(X10,X9,k1_partfun1(X10,X8,X8,X9,X11,X7),k1_partfun1(X10,X8,X8,X9,X12,X7))
      | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X8)))
      | ~ v1_funct_2(X12,X10,X8)
      | ~ v1_funct_1(X12)
      | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X10,X8)))
      | ~ v1_funct_2(X11,X10,X8)
      | ~ v1_funct_1(X11)
      | k1_xboole_0 = X8
      | X11 = X12
      | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X8)))
      | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X10,X8))) ) ),
    inference(resolution,[],[f263,f107])).

fof(f263,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r2_relset_1(X3,X0,X4,X5)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
      | ~ v1_funct_2(X1,X0,X2)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(X1)
      | k1_xboole_0 = X2
      | ~ r2_relset_1(X3,X2,k1_partfun1(X3,X0,X0,X2,X4,X1),k1_partfun1(X3,X0,X0,X2,X5,X1))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0)))
      | ~ v1_funct_2(X5,X3,X0)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X0)))
      | ~ v1_funct_2(X4,X3,X0)
      | ~ v1_funct_1(X4)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f183,f97])).

fof(f97,plain,(
    ! [X6,X2,X0,X8,X7,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_relset_1(X6,X2,k1_partfun1(X6,X0,X0,X2,X7,X1),k1_partfun1(X6,X0,X0,X2,X8,X1))
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X0)))
      | ~ v1_funct_2(X8,X6,X0)
      | ~ v1_funct_1(X8)
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X6,X0)))
      | ~ v1_funct_2(X7,X6,X0)
      | ~ v1_funct_1(X7)
      | r2_relset_1(X6,X0,X7,X8) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ~ r2_relset_1(sK5(X0,X1,X2),X0,sK6(X0,X1,X2),sK7(X0,X1,X2))
          & r2_relset_1(sK5(X0,X1,X2),X2,k1_partfun1(sK5(X0,X1,X2),X0,X0,X2,sK6(X0,X1,X2),X1),k1_partfun1(sK5(X0,X1,X2),X0,X0,X2,sK7(X0,X1,X2),X1))
          & m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(sK5(X0,X1,X2),X0)))
          & v1_funct_2(sK7(X0,X1,X2),sK5(X0,X1,X2),X0)
          & v1_funct_1(sK7(X0,X1,X2))
          & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(sK5(X0,X1,X2),X0)))
          & v1_funct_2(sK6(X0,X1,X2),sK5(X0,X1,X2),X0)
          & v1_funct_1(sK6(X0,X1,X2)) ) )
      & ( ! [X6,X7] :
            ( ! [X8] :
                ( r2_relset_1(X6,X0,X7,X8)
                | ~ r2_relset_1(X6,X2,k1_partfun1(X6,X0,X0,X2,X7,X1),k1_partfun1(X6,X0,X0,X2,X8,X1))
                | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X0)))
                | ~ v1_funct_2(X8,X6,X0)
                | ~ v1_funct_1(X8) )
            | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X6,X0)))
            | ~ v1_funct_2(X7,X6,X0)
            | ~ v1_funct_1(X7) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f57,f59,f58])).

fof(f58,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( ? [X5] :
              ( ~ r2_relset_1(X3,X0,X4,X5)
              & r2_relset_1(X3,X2,k1_partfun1(X3,X0,X0,X2,X4,X1),k1_partfun1(X3,X0,X0,X2,X5,X1))
              & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0)))
              & v1_funct_2(X5,X3,X0)
              & v1_funct_1(X5) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X0)))
          & v1_funct_2(X4,X3,X0)
          & v1_funct_1(X4) )
     => ( ? [X5] :
            ( ~ r2_relset_1(sK5(X0,X1,X2),X0,sK6(X0,X1,X2),X5)
            & r2_relset_1(sK5(X0,X1,X2),X2,k1_partfun1(sK5(X0,X1,X2),X0,X0,X2,sK6(X0,X1,X2),X1),k1_partfun1(sK5(X0,X1,X2),X0,X0,X2,X5,X1))
            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK5(X0,X1,X2),X0)))
            & v1_funct_2(X5,sK5(X0,X1,X2),X0)
            & v1_funct_1(X5) )
        & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(sK5(X0,X1,X2),X0)))
        & v1_funct_2(sK6(X0,X1,X2),sK5(X0,X1,X2),X0)
        & v1_funct_1(sK6(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( ~ r2_relset_1(sK5(X0,X1,X2),X0,sK6(X0,X1,X2),X5)
          & r2_relset_1(sK5(X0,X1,X2),X2,k1_partfun1(sK5(X0,X1,X2),X0,X0,X2,sK6(X0,X1,X2),X1),k1_partfun1(sK5(X0,X1,X2),X0,X0,X2,X5,X1))
          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK5(X0,X1,X2),X0)))
          & v1_funct_2(X5,sK5(X0,X1,X2),X0)
          & v1_funct_1(X5) )
     => ( ~ r2_relset_1(sK5(X0,X1,X2),X0,sK6(X0,X1,X2),sK7(X0,X1,X2))
        & r2_relset_1(sK5(X0,X1,X2),X2,k1_partfun1(sK5(X0,X1,X2),X0,X0,X2,sK6(X0,X1,X2),X1),k1_partfun1(sK5(X0,X1,X2),X0,X0,X2,sK7(X0,X1,X2),X1))
        & m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(sK5(X0,X1,X2),X0)))
        & v1_funct_2(sK7(X0,X1,X2),sK5(X0,X1,X2),X0)
        & v1_funct_1(sK7(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3,X4] :
            ( ? [X5] :
                ( ~ r2_relset_1(X3,X0,X4,X5)
                & r2_relset_1(X3,X2,k1_partfun1(X3,X0,X0,X2,X4,X1),k1_partfun1(X3,X0,X0,X2,X5,X1))
                & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0)))
                & v1_funct_2(X5,X3,X0)
                & v1_funct_1(X5) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X0)))
            & v1_funct_2(X4,X3,X0)
            & v1_funct_1(X4) ) )
      & ( ! [X6,X7] :
            ( ! [X8] :
                ( r2_relset_1(X6,X0,X7,X8)
                | ~ r2_relset_1(X6,X2,k1_partfun1(X6,X0,X0,X2,X7,X1),k1_partfun1(X6,X0,X0,X2,X8,X1))
                | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X0)))
                | ~ v1_funct_2(X8,X6,X0)
                | ~ v1_funct_1(X8) )
            | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X6,X0)))
            | ~ v1_funct_2(X7,X6,X0)
            | ~ v1_funct_1(X7) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f56])).

fof(f56,plain,(
    ! [X0,X2,X1] :
      ( ( sP0(X0,X2,X1)
        | ? [X3,X4] :
            ( ? [X5] :
                ( ~ r2_relset_1(X3,X0,X4,X5)
                & r2_relset_1(X3,X1,k1_partfun1(X3,X0,X0,X1,X4,X2),k1_partfun1(X3,X0,X0,X1,X5,X2))
                & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0)))
                & v1_funct_2(X5,X3,X0)
                & v1_funct_1(X5) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X0)))
            & v1_funct_2(X4,X3,X0)
            & v1_funct_1(X4) ) )
      & ( ! [X3,X4] :
            ( ! [X5] :
                ( r2_relset_1(X3,X0,X4,X5)
                | ~ r2_relset_1(X3,X1,k1_partfun1(X3,X0,X0,X1,X4,X2),k1_partfun1(X3,X0,X0,X1,X5,X2))
                | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0)))
                | ~ v1_funct_2(X5,X3,X0)
                | ~ v1_funct_1(X5) )
            | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X0)))
            | ~ v1_funct_2(X4,X3,X0)
            | ~ v1_funct_1(X4) )
        | ~ sP0(X0,X2,X1) ) ) ),
    inference(nnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X2,X1] :
      ( sP0(X0,X2,X1)
    <=> ! [X3,X4] :
          ( ! [X5] :
              ( r2_relset_1(X3,X0,X4,X5)
              | ~ r2_relset_1(X3,X1,k1_partfun1(X3,X0,X0,X1,X4,X2),k1_partfun1(X3,X0,X0,X1,X5,X2))
              | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0)))
              | ~ v1_funct_2(X5,X3,X0)
              | ~ v1_funct_1(X5) )
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X0)))
          | ~ v1_funct_2(X4,X3,X0)
          | ~ v1_funct_1(X4) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f183,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X2,X0)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X2,X1,X0)
      | ~ v1_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f106,f95])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ v2_funct_1(X1)
      | sP0(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( ( ( v2_funct_1(X1)
          | ~ sP0(X2,X1,X0) )
        & ( sP0(X2,X1,X0)
          | ~ v2_funct_1(X1) ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f54])).

fof(f54,plain,(
    ! [X1,X2,X0] :
      ( ( ( v2_funct_1(X2)
          | ~ sP0(X0,X2,X1) )
        & ( sP0(X0,X2,X1)
          | ~ v2_funct_1(X2) ) )
      | ~ sP1(X1,X2,X0) ) ),
    inference(nnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X1,X2,X0] :
      ( ( v2_funct_1(X2)
      <=> sP0(X0,X2,X1) )
      | ~ sP1(X1,X2,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( sP1(X1,X2,X0)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( sP1(X1,X2,X0)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(definition_folding,[],[f39,f49,f48])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_1(X2)
      <=> ! [X3,X4] :
            ( ! [X5] :
                ( r2_relset_1(X3,X0,X4,X5)
                | ~ r2_relset_1(X3,X1,k1_partfun1(X3,X0,X0,X1,X4,X2),k1_partfun1(X3,X0,X0,X1,X5,X2))
                | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0)))
                | ~ v1_funct_2(X5,X3,X0)
                | ~ v1_funct_1(X5) )
            | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X0)))
            | ~ v1_funct_2(X4,X3,X0)
            | ~ v1_funct_1(X4) ) )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_1(X2)
      <=> ! [X3,X4] :
            ( ! [X5] :
                ( r2_relset_1(X3,X0,X4,X5)
                | ~ r2_relset_1(X3,X1,k1_partfun1(X3,X0,X0,X1,X4,X2),k1_partfun1(X3,X0,X0,X1,X5,X2))
                | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0)))
                | ~ v1_funct_2(X5,X3,X0)
                | ~ v1_funct_1(X5) )
            | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X0)))
            | ~ v1_funct_2(X4,X3,X0)
            | ~ v1_funct_1(X4) ) )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ~ ( ~ ( v2_funct_1(X2)
            <=> ! [X3,X4] :
                  ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X0)))
                    & v1_funct_2(X4,X3,X0)
                    & v1_funct_1(X4) )
                 => ! [X5] :
                      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0)))
                        & v1_funct_2(X5,X3,X0)
                        & v1_funct_1(X5) )
                     => ( r2_relset_1(X3,X1,k1_partfun1(X3,X0,X0,X1,X4,X2),k1_partfun1(X3,X0,X0,X1,X5,X2))
                       => r2_relset_1(X3,X0,X4,X5) ) ) ) )
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_funct_2)).

fof(f906,plain,(
    v1_funct_2(k6_partfun1(sK2),sK2,sK2) ),
    inference(resolution,[],[f902,f134])).

fof(f134,plain,(
    ! [X0] :
      ( ~ v1_funct_1(k6_partfun1(X0))
      | v1_funct_2(k6_partfun1(X0),X0,X0) ) ),
    inference(forward_demodulation,[],[f133,f115])).

fof(f115,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f77,f71])).

fof(f77,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f133,plain,(
    ! [X0] :
      ( v1_funct_2(k6_partfun1(X0),X0,k2_relat_1(k6_partfun1(X0)))
      | ~ v1_funct_1(k6_partfun1(X0)) ) ),
    inference(subsumption_resolution,[],[f131,f114])).

fof(f114,plain,(
    ! [X0] : v1_relat_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f72,f71])).

fof(f72,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f131,plain,(
    ! [X0] :
      ( v1_funct_2(k6_partfun1(X0),X0,k2_relat_1(k6_partfun1(X0)))
      | ~ v1_funct_1(k6_partfun1(X0))
      | ~ v1_relat_1(k6_partfun1(X0)) ) ),
    inference(superposition,[],[f82,f116])).

fof(f116,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f76,f71])).

fof(f76,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f70,plain,(
    ~ r2_relset_1(sK2,sK2,sK4,k6_partfun1(sK2)) ),
    inference(cnf_transformation,[],[f53])).

fof(f67,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(cnf_transformation,[],[f53])).

fof(f1183,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(X0))
      | k1_xboole_0 = sK4
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f1088,f80])).

fof(f1088,plain,
    ( ~ v1_relat_1(sK4)
    | k1_xboole_0 = sK4 ),
    inference(trivial_inequality_removal,[],[f1054])).

fof(f1054,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK4
    | ~ v1_relat_1(sK4) ),
    inference(backward_demodulation,[],[f173,f1040])).

fof(f173,plain,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 = sK4
    | ~ v1_relat_1(sK4) ),
    inference(superposition,[],[f78,f169])).

fof(f169,plain,(
    sK2 = k1_relat_1(sK4) ),
    inference(subsumption_resolution,[],[f167,f67])).

fof(f167,plain,
    ( sK2 = k1_relat_1(sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(superposition,[],[f158,f88])).

fof(f158,plain,(
    sK2 = k1_relset_1(sK2,sK2,sK4) ),
    inference(subsumption_resolution,[],[f157,f65])).

fof(f157,plain,
    ( sK2 = k1_relset_1(sK2,sK2,sK4)
    | ~ v1_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f152,f67])).

fof(f152,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | sK2 = k1_relset_1(sK2,sK2,sK4)
    | ~ v1_funct_1(sK4) ),
    inference(resolution,[],[f87,f66])).

fof(f78,plain,(
    ! [X0] :
      ( k1_relat_1(X0) != k1_xboole_0
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_relat_1(X0) != k1_xboole_0 )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_relat_1(X0) != k1_xboole_0 )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

% (6522)Time limit reached!
% (6522)------------------------------
% (6522)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_relat_1(X0) = k1_xboole_0 )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(f1090,plain,(
    ~ r2_relset_1(k1_xboole_0,k1_xboole_0,sK4,k1_xboole_0) ),
    inference(forward_demodulation,[],[f1045,f124])).

fof(f124,plain,(
    k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    inference(equality_resolution,[],[f122])).

fof(f122,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k6_partfun1(X0) ) ),
    inference(subsumption_resolution,[],[f121,f114])).

fof(f121,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k6_partfun1(X0)
      | ~ v1_relat_1(k6_partfun1(X0)) ) ),
    inference(superposition,[],[f78,f116])).

fof(f1045,plain,(
    ~ r2_relset_1(k1_xboole_0,k1_xboole_0,sK4,k6_partfun1(k1_xboole_0)) ),
    inference(backward_demodulation,[],[f70,f1040])).

fof(f125,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(superposition,[],[f75,f124])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:13:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.48  % (6497)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.49  % (6506)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.50  % (6514)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.51  % (6501)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.51  % (6515)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.51  % (6522)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.51  % (6496)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.51  % (6498)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.51  % (6500)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.51  % (6507)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.52  % (6495)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.52  % (6510)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.52  % (6499)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.53  % (6494)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.53  % (6520)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.53  % (6493)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.53  % (6518)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.53  % (6521)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.54  % (6513)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.54  % (6503)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.54  % (6504)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.54  % (6511)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.54  % (6512)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.54  % (6516)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.54  % (6509)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.54  % (6505)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.54  % (6502)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.55  % (6509)Refutation not found, incomplete strategy% (6509)------------------------------
% 0.20/0.55  % (6509)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (6509)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (6509)Memory used [KB]: 10746
% 0.20/0.55  % (6509)Time elapsed: 0.129 s
% 0.20/0.55  % (6509)------------------------------
% 0.20/0.55  % (6509)------------------------------
% 0.20/0.55  % (6508)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.55  % (6519)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.62/0.58  % (6517)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.90/0.62  % (6503)Refutation not found, incomplete strategy% (6503)------------------------------
% 1.90/0.62  % (6503)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.90/0.62  % (6503)Termination reason: Refutation not found, incomplete strategy
% 1.90/0.62  
% 1.90/0.62  % (6503)Memory used [KB]: 11385
% 1.90/0.62  % (6503)Time elapsed: 0.212 s
% 1.90/0.62  % (6503)------------------------------
% 1.90/0.62  % (6503)------------------------------
% 2.14/0.68  % (6521)Refutation not found, incomplete strategy% (6521)------------------------------
% 2.14/0.68  % (6521)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.14/0.68  % (6521)Termination reason: Refutation not found, incomplete strategy
% 2.14/0.68  
% 2.14/0.68  % (6521)Memory used [KB]: 11641
% 2.14/0.68  % (6521)Time elapsed: 0.269 s
% 2.14/0.68  % (6521)------------------------------
% 2.14/0.68  % (6521)------------------------------
% 2.14/0.70  % (6493)Refutation not found, incomplete strategy% (6493)------------------------------
% 2.14/0.70  % (6493)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.14/0.70  % (6493)Termination reason: Refutation not found, incomplete strategy
% 2.14/0.70  
% 2.14/0.70  % (6493)Memory used [KB]: 1791
% 2.14/0.70  % (6493)Time elapsed: 0.300 s
% 2.14/0.70  % (6493)------------------------------
% 2.14/0.70  % (6493)------------------------------
% 2.14/0.71  % (6526)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.85/0.73  % (6548)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.85/0.79  % (6572)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 3.29/0.80  % (6572)Refutation not found, incomplete strategy% (6572)------------------------------
% 3.29/0.80  % (6572)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.29/0.80  % (6572)Termination reason: Refutation not found, incomplete strategy
% 3.29/0.80  
% 3.29/0.80  % (6572)Memory used [KB]: 6268
% 3.29/0.80  % (6572)Time elapsed: 0.064 s
% 3.29/0.80  % (6572)------------------------------
% 3.29/0.80  % (6572)------------------------------
% 3.29/0.80  % (6495)Time limit reached!
% 3.29/0.80  % (6495)------------------------------
% 3.29/0.80  % (6495)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.29/0.80  % (6495)Termination reason: Time limit
% 3.29/0.80  % (6495)Termination phase: Saturation
% 3.29/0.80  
% 3.29/0.80  % (6495)Memory used [KB]: 6780
% 3.29/0.80  % (6495)Time elapsed: 0.400 s
% 3.29/0.80  % (6495)------------------------------
% 3.29/0.80  % (6495)------------------------------
% 3.29/0.82  % (6517)Time limit reached!
% 3.29/0.82  % (6517)------------------------------
% 3.29/0.82  % (6517)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.29/0.82  % (6517)Termination reason: Time limit
% 3.29/0.82  % (6517)Termination phase: Saturation
% 3.29/0.82  
% 3.29/0.82  % (6517)Memory used [KB]: 13304
% 3.29/0.82  % (6517)Time elapsed: 0.400 s
% 3.29/0.82  % (6517)------------------------------
% 3.29/0.82  % (6517)------------------------------
% 3.29/0.84  % (6581)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 3.79/0.90  % (6645)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 3.79/0.92  % (6654)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 3.79/0.93  % (6648)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 3.79/0.93  % (6515)Refutation found. Thanks to Tanya!
% 3.79/0.93  % SZS status Theorem for theBenchmark
% 3.79/0.93  % SZS output start Proof for theBenchmark
% 3.79/0.93  fof(f1271,plain,(
% 3.79/0.93    $false),
% 3.79/0.93    inference(unit_resulting_resolution,[],[f125,f1247,f120])).
% 3.79/0.93  fof(f120,plain,(
% 3.79/0.93    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.79/0.93    inference(duplicate_literal_removal,[],[f119])).
% 3.79/0.93  fof(f119,plain,(
% 3.79/0.93    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.79/0.93    inference(equality_resolution,[],[f108])).
% 3.79/0.93  fof(f108,plain,(
% 3.79/0.93    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.79/0.93    inference(cnf_transformation,[],[f61])).
% 3.79/0.93  fof(f61,plain,(
% 3.79/0.93    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.79/0.93    inference(nnf_transformation,[],[f41])).
% 3.79/0.93  fof(f41,plain,(
% 3.79/0.93    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.79/0.93    inference(flattening,[],[f40])).
% 3.79/0.93  fof(f40,plain,(
% 3.79/0.93    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.79/0.93    inference(ennf_transformation,[],[f10])).
% 3.79/0.93  fof(f10,axiom,(
% 3.79/0.93    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 3.79/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 3.79/0.93  fof(f1247,plain,(
% 3.79/0.93    ~r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 3.79/0.93    inference(backward_demodulation,[],[f1090,f1232])).
% 3.79/0.93  fof(f1232,plain,(
% 3.79/0.93    k1_xboole_0 = sK4),
% 3.79/0.93    inference(subsumption_resolution,[],[f1230,f86])).
% 3.79/0.93  fof(f86,plain,(
% 3.79/0.93    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.79/0.93    inference(cnf_transformation,[],[f2])).
% 3.79/0.93  fof(f2,axiom,(
% 3.79/0.93    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.79/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 3.79/0.93  fof(f1230,plain,(
% 3.79/0.93    k1_xboole_0 = sK4 | ~v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))),
% 3.79/0.93    inference(resolution,[],[f1183,f1044])).
% 3.79/0.93  fof(f1044,plain,(
% 3.79/0.93    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 3.79/0.93    inference(backward_demodulation,[],[f67,f1040])).
% 3.79/0.93  fof(f1040,plain,(
% 3.79/0.93    k1_xboole_0 = sK2),
% 3.79/0.93    inference(subsumption_resolution,[],[f1037,f67])).
% 3.79/0.93  fof(f1037,plain,(
% 3.79/0.93    k1_xboole_0 = sK2 | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))),
% 3.79/0.93    inference(resolution,[],[f953,f120])).
% 3.79/0.93  fof(f953,plain,(
% 3.79/0.93    ~r2_relset_1(sK2,sK2,sK4,sK4) | k1_xboole_0 = sK2),
% 3.79/0.93    inference(superposition,[],[f70,f950])).
% 3.79/0.93  fof(f950,plain,(
% 3.79/0.93    k6_partfun1(sK2) = sK4 | k1_xboole_0 = sK2),
% 3.79/0.93    inference(subsumption_resolution,[],[f947,f64])).
% 3.79/0.93  fof(f64,plain,(
% 3.79/0.93    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))),
% 3.79/0.93    inference(cnf_transformation,[],[f53])).
% 3.79/0.93  fof(f53,plain,(
% 3.79/0.93    (~r2_relset_1(sK2,sK2,sK4,k6_partfun1(sK2)) & v2_funct_1(sK3) & r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3),sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v1_funct_2(sK4,sK2,sK2) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v1_funct_2(sK3,sK2,sK2) & v1_funct_1(sK3)),
% 3.79/0.93    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f23,f52,f51])).
% 3.79/0.93  fof(f51,plain,(
% 3.79/0.93    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k6_partfun1(X0)) & v2_funct_1(X1) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (? [X2] : (~r2_relset_1(sK2,sK2,X2,k6_partfun1(sK2)) & v2_funct_1(sK3) & r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,X2,sK3),sK3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v1_funct_2(X2,sK2,sK2) & v1_funct_1(X2)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v1_funct_2(sK3,sK2,sK2) & v1_funct_1(sK3))),
% 3.79/0.93    introduced(choice_axiom,[])).
% 3.79/0.93  fof(f52,plain,(
% 3.79/0.93    ? [X2] : (~r2_relset_1(sK2,sK2,X2,k6_partfun1(sK2)) & v2_funct_1(sK3) & r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,X2,sK3),sK3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v1_funct_2(X2,sK2,sK2) & v1_funct_1(X2)) => (~r2_relset_1(sK2,sK2,sK4,k6_partfun1(sK2)) & v2_funct_1(sK3) & r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3),sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v1_funct_2(sK4,sK2,sK2) & v1_funct_1(sK4))),
% 3.79/0.93    introduced(choice_axiom,[])).
% 3.79/0.93  fof(f23,plain,(
% 3.79/0.93    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k6_partfun1(X0)) & v2_funct_1(X1) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 3.79/0.93    inference(flattening,[],[f22])).
% 3.79/0.93  fof(f22,plain,(
% 3.79/0.93    ? [X0,X1] : (? [X2] : ((~r2_relset_1(X0,X0,X2,k6_partfun1(X0)) & (v2_funct_1(X1) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 3.79/0.93    inference(ennf_transformation,[],[f21])).
% 3.79/0.93  fof(f21,negated_conjecture,(
% 3.79/0.93    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => ((v2_funct_1(X1) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1)) => r2_relset_1(X0,X0,X2,k6_partfun1(X0)))))),
% 3.79/0.93    inference(negated_conjecture,[],[f20])).
% 3.79/0.93  fof(f20,conjecture,(
% 3.79/0.93    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => ((v2_funct_1(X1) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1)) => r2_relset_1(X0,X0,X2,k6_partfun1(X0)))))),
% 3.79/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_funct_2)).
% 3.79/0.93  fof(f947,plain,(
% 3.79/0.93    k1_xboole_0 = sK2 | k6_partfun1(sK2) = sK4 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))),
% 3.79/0.93    inference(resolution,[],[f936,f189])).
% 3.79/0.93  fof(f189,plain,(
% 3.79/0.93    ( ! [X2,X0,X1] : (r2_relset_1(X0,X1,k5_relat_1(k6_partfun1(X0),X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.79/0.93    inference(subsumption_resolution,[],[f188,f75])).
% 3.79/0.93  fof(f75,plain,(
% 3.79/0.93    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.79/0.93    inference(cnf_transformation,[],[f12])).
% 3.79/0.93  fof(f12,axiom,(
% 3.79/0.93    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 3.79/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 3.79/0.93  fof(f188,plain,(
% 3.79/0.93    ( ! [X2,X0,X1] : (r2_relset_1(X0,X1,k5_relat_1(k6_partfun1(X0),X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.79/0.93    inference(duplicate_literal_removal,[],[f185])).
% 3.79/0.93  fof(f185,plain,(
% 3.79/0.93    ( ! [X2,X0,X1] : (r2_relset_1(X0,X1,k5_relat_1(k6_partfun1(X0),X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.79/0.93    inference(superposition,[],[f90,f112])).
% 3.79/0.93  fof(f112,plain,(
% 3.79/0.93    ( ! [X4,X2,X0,X5,X3,X1] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.79/0.93    inference(cnf_transformation,[],[f47])).
% 3.79/0.93  fof(f47,plain,(
% 3.79/0.93    ! [X0,X1,X2,X3,X4,X5] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.79/0.93    inference(flattening,[],[f46])).
% 3.79/0.93  fof(f46,plain,(
% 3.79/0.93    ! [X0,X1,X2,X3,X4,X5] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.79/0.93    inference(ennf_transformation,[],[f9])).
% 3.79/0.93  fof(f9,axiom,(
% 3.79/0.93    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 3.79/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_relset_1)).
% 3.79/0.93  fof(f90,plain,(
% 3.79/0.93    ( ! [X2,X0,X1] : (r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.79/0.93    inference(cnf_transformation,[],[f35])).
% 3.79/0.93  fof(f35,plain,(
% 3.79/0.93    ! [X0,X1,X2] : ((r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2) & r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.79/0.93    inference(ennf_transformation,[],[f15])).
% 3.79/0.93  fof(f15,axiom,(
% 3.79/0.93    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2) & r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2)))),
% 3.79/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_2)).
% 3.79/0.93  fof(f936,plain,(
% 3.79/0.93    ~r2_relset_1(sK2,sK2,k5_relat_1(k6_partfun1(sK2),sK3),sK3) | k1_xboole_0 = sK2 | k6_partfun1(sK2) = sK4),
% 3.79/0.93    inference(subsumption_resolution,[],[f935,f902])).
% 3.79/0.93  fof(f902,plain,(
% 3.79/0.93    v1_funct_1(k6_partfun1(sK2))),
% 3.79/0.93    inference(resolution,[],[f900,f64])).
% 3.79/0.93  fof(f900,plain,(
% 3.79/0.93    ( ! [X6,X7] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) | v1_funct_1(k6_partfun1(sK2))) )),
% 3.79/0.93    inference(subsumption_resolution,[],[f897,f86])).
% 3.79/0.93  fof(f897,plain,(
% 3.79/0.93    ( ! [X6,X7] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) | v1_funct_1(k6_partfun1(sK2)) | ~v1_relat_1(k2_zfmisc_1(sK2,sK2))) )),
% 3.79/0.93    inference(resolution,[],[f886,f64])).
% 3.79/0.93  fof(f886,plain,(
% 3.79/0.93    ( ! [X2,X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(X2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_funct_1(k6_partfun1(sK2)) | ~v1_relat_1(X2)) )),
% 3.79/0.93    inference(resolution,[],[f885,f80])).
% 3.79/0.93  fof(f80,plain,(
% 3.79/0.93    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.79/0.93    inference(cnf_transformation,[],[f26])).
% 3.79/0.93  fof(f26,plain,(
% 3.79/0.93    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.79/0.93    inference(ennf_transformation,[],[f1])).
% 3.79/0.93  fof(f1,axiom,(
% 3.79/0.93    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.79/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 3.79/0.93  fof(f885,plain,(
% 3.79/0.93    ( ! [X8,X9] : (~v1_relat_1(sK3) | v1_funct_1(k6_partfun1(sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))) )),
% 3.79/0.93    inference(subsumption_resolution,[],[f883,f166])).
% 3.79/0.93  fof(f166,plain,(
% 3.79/0.93    v1_funct_2(sK3,sK2,k2_relat_1(sK3)) | ~v1_relat_1(sK3)),
% 3.79/0.93    inference(subsumption_resolution,[],[f164,f62])).
% 3.79/0.93  fof(f62,plain,(
% 3.79/0.93    v1_funct_1(sK3)),
% 3.79/0.93    inference(cnf_transformation,[],[f53])).
% 3.79/0.93  fof(f164,plain,(
% 3.79/0.93    v1_funct_2(sK3,sK2,k2_relat_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)),
% 3.79/0.93    inference(superposition,[],[f82,f161])).
% 3.79/0.93  fof(f161,plain,(
% 3.79/0.93    sK2 = k1_relat_1(sK3)),
% 3.79/0.93    inference(subsumption_resolution,[],[f159,f64])).
% 3.79/0.93  fof(f159,plain,(
% 3.79/0.93    sK2 = k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))),
% 3.79/0.93    inference(superposition,[],[f156,f88])).
% 3.79/0.93  fof(f88,plain,(
% 3.79/0.93    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.79/0.93    inference(cnf_transformation,[],[f33])).
% 3.79/0.93  fof(f33,plain,(
% 3.79/0.93    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.79/0.93    inference(ennf_transformation,[],[f7])).
% 3.79/0.93  fof(f7,axiom,(
% 3.79/0.93    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 3.79/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 3.79/0.93  fof(f156,plain,(
% 3.79/0.93    sK2 = k1_relset_1(sK2,sK2,sK3)),
% 3.79/0.93    inference(subsumption_resolution,[],[f155,f62])).
% 3.79/0.93  fof(f155,plain,(
% 3.79/0.93    sK2 = k1_relset_1(sK2,sK2,sK3) | ~v1_funct_1(sK3)),
% 3.79/0.93    inference(subsumption_resolution,[],[f151,f64])).
% 3.79/0.93  fof(f151,plain,(
% 3.79/0.93    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | sK2 = k1_relset_1(sK2,sK2,sK3) | ~v1_funct_1(sK3)),
% 3.79/0.93    inference(resolution,[],[f87,f63])).
% 3.79/0.93  fof(f63,plain,(
% 3.79/0.93    v1_funct_2(sK3,sK2,sK2)),
% 3.79/0.93    inference(cnf_transformation,[],[f53])).
% 3.79/0.93  fof(f87,plain,(
% 3.79/0.93    ( ! [X0,X1] : (~v1_funct_2(X1,X0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | k1_relset_1(X0,X0,X1) = X0 | ~v1_funct_1(X1)) )),
% 3.79/0.93    inference(cnf_transformation,[],[f32])).
% 3.79/0.93  fof(f32,plain,(
% 3.79/0.93    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 3.79/0.93    inference(flattening,[],[f31])).
% 3.79/0.93  fof(f31,plain,(
% 3.79/0.93    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 3.79/0.93    inference(ennf_transformation,[],[f19])).
% 3.79/0.93  fof(f19,axiom,(
% 3.79/0.93    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k1_relset_1(X0,X0,X1) = X0)),
% 3.79/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_2)).
% 3.79/0.93  fof(f82,plain,(
% 3.79/0.93    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.79/0.93    inference(cnf_transformation,[],[f28])).
% 3.79/0.93  fof(f28,plain,(
% 3.79/0.93    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.79/0.93    inference(flattening,[],[f27])).
% 3.79/0.93  fof(f27,plain,(
% 3.79/0.93    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.79/0.93    inference(ennf_transformation,[],[f18])).
% 3.79/0.93  fof(f18,axiom,(
% 3.79/0.93    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 3.79/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).
% 3.79/0.93  fof(f883,plain,(
% 3.79/0.93    ( ! [X8,X9] : (~v1_funct_2(sK3,sK2,k2_relat_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X8,X9))) | v1_funct_1(k6_partfun1(sK2)) | ~v1_relat_1(sK3)) )),
% 3.79/0.93    inference(trivial_inequality_removal,[],[f882])).
% 3.79/0.93  fof(f882,plain,(
% 3.79/0.93    ( ! [X8,X9] : (~v1_funct_2(sK3,sK2,k2_relat_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X8,X9))) | v1_funct_1(k6_partfun1(sK2)) | k2_relat_1(sK3) != k2_relat_1(sK3) | ~v1_relat_1(sK3)) )),
% 3.79/0.93    inference(resolution,[],[f871,f162])).
% 3.79/0.93  fof(f162,plain,(
% 3.79/0.93    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_relat_1(sK3)))) | ~v1_relat_1(sK3)),
% 3.79/0.93    inference(backward_demodulation,[],[f146,f161])).
% 3.79/0.93  fof(f146,plain,(
% 3.79/0.93    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))) | ~v1_relat_1(sK3)),
% 3.79/0.93    inference(resolution,[],[f83,f62])).
% 3.79/0.93  fof(f83,plain,(
% 3.79/0.93    ( ! [X0] : (~v1_funct_1(X0) | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_relat_1(X0)) )),
% 3.79/0.93    inference(cnf_transformation,[],[f28])).
% 3.79/0.93  fof(f871,plain,(
% 3.79/0.93    ( ! [X10,X8,X11,X9] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X8,X9))) | ~v1_funct_2(sK3,X8,X9) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X10,X11))) | v1_funct_1(k6_partfun1(sK2)) | k2_relat_1(sK3) != X9) )),
% 3.79/0.93    inference(subsumption_resolution,[],[f868,f86])).
% 3.79/0.93  fof(f868,plain,(
% 3.79/0.93    ( ! [X10,X8,X11,X9] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X8,X9))) | ~v1_funct_2(sK3,X8,X9) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X10,X11))) | v1_funct_1(k6_partfun1(sK2)) | k2_relat_1(sK3) != X9 | ~v1_relat_1(k2_zfmisc_1(sK2,sK2))) )),
% 3.79/0.93    inference(resolution,[],[f851,f64])).
% 3.79/0.93  fof(f851,plain,(
% 3.79/0.93    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(X4)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(sK3,X1,X0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | v1_funct_1(k6_partfun1(sK2)) | k2_relat_1(sK3) != X0 | ~v1_relat_1(X4)) )),
% 3.79/0.93    inference(resolution,[],[f848,f80])).
% 3.79/0.93  fof(f848,plain,(
% 3.79/0.93    ( ! [X14,X12,X15,X13] : (~v1_relat_1(sK3) | k2_relat_1(sK3) != X12 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X13,X12))) | ~v1_funct_2(sK3,X13,X12) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X14,X15))) | v1_funct_1(k6_partfun1(sK2))) )),
% 3.79/0.93    inference(subsumption_resolution,[],[f846,f166])).
% 3.79/0.93  fof(f846,plain,(
% 3.79/0.93    ( ! [X14,X12,X15,X13] : (v1_funct_1(k6_partfun1(sK2)) | k2_relat_1(sK3) != X12 | ~v1_funct_2(sK3,sK2,k2_relat_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X13,X12))) | ~v1_funct_2(sK3,X13,X12) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X14,X15))) | ~v1_relat_1(sK3)) )),
% 3.79/0.93    inference(trivial_inequality_removal,[],[f845])).
% 3.79/0.93  fof(f845,plain,(
% 3.79/0.93    ( ! [X14,X12,X15,X13] : (v1_funct_1(k6_partfun1(sK2)) | k2_relat_1(sK3) != X12 | ~v1_funct_2(sK3,sK2,k2_relat_1(sK3)) | k2_relat_1(sK3) != k2_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X13,X12))) | ~v1_funct_2(sK3,X13,X12) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X14,X15))) | ~v1_relat_1(sK3)) )),
% 3.79/0.93    inference(resolution,[],[f838,f162])).
% 3.79/0.93  fof(f838,plain,(
% 3.79/0.93    ( ! [X14,X12,X10,X15,X13,X11] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X11,X12))) | v1_funct_1(k6_partfun1(sK2)) | k2_relat_1(sK3) != X10 | ~v1_funct_2(sK3,X11,X12) | k2_relat_1(sK3) != X12 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X13,X10))) | ~v1_funct_2(sK3,X13,X10) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X14,X15)))) )),
% 3.79/0.93    inference(subsumption_resolution,[],[f835,f86])).
% 3.79/0.93  fof(f835,plain,(
% 3.79/0.93    ( ! [X14,X12,X10,X15,X13,X11] : (k2_relat_1(sK3) != X10 | v1_funct_1(k6_partfun1(sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X11,X12))) | ~v1_funct_2(sK3,X11,X12) | k2_relat_1(sK3) != X12 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X13,X10))) | ~v1_funct_2(sK3,X13,X10) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X14,X15))) | ~v1_relat_1(k2_zfmisc_1(sK2,sK2))) )),
% 3.79/0.93    inference(resolution,[],[f822,f64])).
% 3.79/0.93  fof(f822,plain,(
% 3.79/0.93    ( ! [X6,X4,X2,X0,X5,X3,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(X6)) | k2_relat_1(sK3) != X2 | v1_funct_1(k6_partfun1(sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_2(sK3,X3,X4) | k2_relat_1(sK3) != X4 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X5,X2))) | ~v1_funct_2(sK3,X5,X2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_relat_1(X6)) )),
% 3.79/0.93    inference(resolution,[],[f821,f80])).
% 3.79/0.93  fof(f821,plain,(
% 3.79/0.93    ( ! [X26,X24,X23,X27,X25,X22] : (~v1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X22,X23))) | k2_relat_1(sK3) != X24 | v1_funct_1(k6_partfun1(sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X25,X26))) | ~v1_funct_2(sK3,X25,X26) | k2_relat_1(sK3) != X26 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X27,X24))) | ~v1_funct_2(sK3,X27,X24)) )),
% 3.79/0.93    inference(forward_demodulation,[],[f820,f161])).
% 3.79/0.93  fof(f820,plain,(
% 3.79/0.93    ( ! [X26,X24,X23,X27,X25,X22] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X22,X23))) | k2_relat_1(sK3) != X24 | ~v1_relat_1(sK3) | v1_funct_1(k6_partfun1(k1_relat_1(sK3))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X25,X26))) | ~v1_funct_2(sK3,X25,X26) | k2_relat_1(sK3) != X26 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X27,X24))) | ~v1_funct_2(sK3,X27,X24)) )),
% 3.79/0.93    inference(subsumption_resolution,[],[f812,f62])).
% 3.79/0.93  fof(f812,plain,(
% 3.79/0.93    ( ! [X26,X24,X23,X27,X25,X22] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X22,X23))) | ~v1_funct_1(sK3) | k2_relat_1(sK3) != X24 | ~v1_relat_1(sK3) | v1_funct_1(k6_partfun1(k1_relat_1(sK3))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X25,X26))) | ~v1_funct_2(sK3,X25,X26) | k2_relat_1(sK3) != X26 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X27,X24))) | ~v1_funct_2(sK3,X27,X24)) )),
% 3.79/0.93    inference(resolution,[],[f618,f69])).
% 3.79/0.93  fof(f69,plain,(
% 3.79/0.93    v2_funct_1(sK3)),
% 3.79/0.93    inference(cnf_transformation,[],[f53])).
% 3.79/0.93  fof(f618,plain,(
% 3.79/0.93    ( ! [X6,X4,X2,X0,X5,X3,X1] : (~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_1(X2) | k2_relat_1(X2) != X1 | ~v1_relat_1(X2) | v1_funct_1(k6_partfun1(k1_relat_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) | ~v1_funct_2(X2,X5,X6) | k2_relat_1(X2) != X6 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1)) )),
% 3.79/0.93    inference(duplicate_literal_removal,[],[f617])).
% 3.79/0.93  fof(f617,plain,(
% 3.79/0.93    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_relat_1(X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_1(X2) | ~v2_funct_1(X2) | ~v1_relat_1(X2) | v1_funct_1(k6_partfun1(k1_relat_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) | ~v1_funct_2(X2,X5,X6) | k2_relat_1(X2) != X6 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.79/0.93    inference(superposition,[],[f515,f89])).
% 3.79/0.93  fof(f89,plain,(
% 3.79/0.93    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.79/0.93    inference(cnf_transformation,[],[f34])).
% 3.79/0.93  fof(f34,plain,(
% 3.79/0.93    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.79/0.93    inference(ennf_transformation,[],[f8])).
% 3.79/0.93  fof(f8,axiom,(
% 3.79/0.93    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 3.79/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 3.79/0.93  fof(f515,plain,(
% 3.79/0.93    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_relset_1(X5,X6,X2) != X6 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_1(X2) | ~v2_funct_1(X2) | ~v1_relat_1(X2) | v1_funct_1(k6_partfun1(k1_relat_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k2_relat_1(X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) | ~v1_funct_2(X2,X5,X6)) )),
% 3.79/0.93    inference(duplicate_literal_removal,[],[f514])).
% 3.79/0.93  fof(f514,plain,(
% 3.79/0.93    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_relat_1(X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_1(X2) | ~v2_funct_1(X2) | ~v1_relat_1(X2) | v1_funct_1(k6_partfun1(k1_relat_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k2_relset_1(X5,X6,X2) != X6 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) | ~v1_funct_2(X2,X5,X6) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.79/0.93    inference(superposition,[],[f407,f89])).
% 3.79/0.93  fof(f407,plain,(
% 3.79/0.93    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_relset_1(X3,X4,X0) != X4 | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0) | v1_funct_1(k6_partfun1(k1_relat_1(X0))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_2(X0,X3,X4) | k2_relset_1(X5,X6,X0) != X6 | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) | ~v1_funct_2(X0,X5,X6)) )),
% 3.79/0.93    inference(duplicate_literal_removal,[],[f404])).
% 3.79/0.93  fof(f404,plain,(
% 3.79/0.93    ( ! [X6,X4,X2,X0,X5,X3,X1] : (v1_funct_1(k6_partfun1(k1_relat_1(X0))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0) | k2_relset_1(X3,X4,X0) != X4 | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_2(X0,X3,X4) | k2_relset_1(X5,X6,X0) != X6 | ~v2_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) | ~v1_funct_2(X0,X5,X6) | ~v1_funct_1(X0)) )),
% 3.79/0.93    inference(resolution,[],[f335,f94])).
% 3.79/0.93  fof(f94,plain,(
% 3.79/0.93    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.79/0.93    inference(cnf_transformation,[],[f37])).
% 3.79/0.93  fof(f37,plain,(
% 3.79/0.93    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.79/0.93    inference(flattening,[],[f36])).
% 3.79/0.93  fof(f36,plain,(
% 3.79/0.93    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.79/0.93    inference(ennf_transformation,[],[f17])).
% 3.79/0.93  fof(f17,axiom,(
% 3.79/0.93    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 3.79/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).
% 3.79/0.93  fof(f335,plain,(
% 3.79/0.93    ( ! [X6,X4,X2,X0,X5,X3,X1] : (~m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_funct_1(k6_partfun1(k1_relat_1(X0))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0) | k2_relset_1(X5,X6,X0) != X6 | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) | ~v1_funct_2(X0,X5,X6)) )),
% 3.79/0.93    inference(duplicate_literal_removal,[],[f334])).
% 3.79/0.93  fof(f334,plain,(
% 3.79/0.93    ( ! [X6,X4,X2,X0,X5,X3,X1] : (~m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_funct_1(k6_partfun1(k1_relat_1(X0))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0) | k2_relset_1(X5,X6,X0) != X6 | ~v2_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) | ~v1_funct_2(X0,X5,X6) | ~v1_funct_1(X0)) )),
% 3.79/0.93    inference(resolution,[],[f254,f92])).
% 3.79/0.93  fof(f92,plain,(
% 3.79/0.93    ( ! [X2,X0,X1] : (v1_funct_1(k2_funct_1(X2)) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.79/0.93    inference(cnf_transformation,[],[f37])).
% 3.79/0.93  fof(f254,plain,(
% 3.79/0.93    ( ! [X6,X8,X7,X5,X9] : (~v1_funct_1(k2_funct_1(X5)) | ~m1_subset_1(k2_funct_1(X5),k1_zfmisc_1(k2_zfmisc_1(X6,X7))) | v1_funct_1(k6_partfun1(k1_relat_1(X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X8,X9))) | ~v1_funct_1(X5) | ~v2_funct_1(X5) | ~v1_relat_1(X5)) )),
% 3.79/0.93    inference(duplicate_literal_removal,[],[f252])).
% 3.79/0.93  fof(f252,plain,(
% 3.79/0.93    ( ! [X6,X8,X7,X5,X9] : (v1_funct_1(k6_partfun1(k1_relat_1(X5))) | ~m1_subset_1(k2_funct_1(X5),k1_zfmisc_1(k2_zfmisc_1(X6,X7))) | ~v1_funct_1(k2_funct_1(X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X8,X9))) | ~v1_funct_1(X5) | ~v2_funct_1(X5) | ~v1_funct_1(X5) | ~v1_relat_1(X5)) )),
% 3.79/0.93    inference(superposition,[],[f211,f118])).
% 3.79/0.93  fof(f118,plain,(
% 3.79/0.93    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.79/0.93    inference(definition_unfolding,[],[f84,f71])).
% 3.79/0.93  fof(f71,plain,(
% 3.79/0.93    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 3.79/0.93    inference(cnf_transformation,[],[f14])).
% 3.79/0.93  fof(f14,axiom,(
% 3.79/0.93    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 3.79/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 3.79/0.93  fof(f84,plain,(
% 3.79/0.93    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.79/0.93    inference(cnf_transformation,[],[f30])).
% 3.79/0.93  fof(f30,plain,(
% 3.79/0.93    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.79/0.93    inference(flattening,[],[f29])).
% 3.79/0.93  fof(f29,plain,(
% 3.79/0.93    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.79/0.93    inference(ennf_transformation,[],[f6])).
% 3.79/0.93  fof(f6,axiom,(
% 3.79/0.93    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 3.79/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).
% 3.79/0.93  fof(f211,plain,(
% 3.79/0.93    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k5_relat_1(X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.79/0.93    inference(duplicate_literal_removal,[],[f210])).
% 3.79/0.93  fof(f210,plain,(
% 3.79/0.93    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k5_relat_1(X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.79/0.93    inference(superposition,[],[f110,f109])).
% 3.79/0.93  fof(f109,plain,(
% 3.79/0.93    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.79/0.93    inference(cnf_transformation,[],[f43])).
% 3.79/0.93  fof(f43,plain,(
% 3.79/0.93    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.79/0.93    inference(flattening,[],[f42])).
% 3.79/0.93  fof(f42,plain,(
% 3.79/0.93    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.79/0.93    inference(ennf_transformation,[],[f13])).
% 3.79/0.93  fof(f13,axiom,(
% 3.79/0.93    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 3.79/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 3.79/0.93  % (6499)Time limit reached!
% 3.79/0.93  % (6499)------------------------------
% 3.79/0.93  % (6499)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.79/0.93  fof(f110,plain,(
% 3.79/0.93    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.79/0.93    inference(cnf_transformation,[],[f45])).
% 3.79/0.93  fof(f45,plain,(
% 3.79/0.93    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.79/0.93    inference(flattening,[],[f44])).
% 3.79/0.93  fof(f44,plain,(
% 3.79/0.93    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.79/0.93    inference(ennf_transformation,[],[f11])).
% 3.79/0.93  fof(f11,axiom,(
% 3.79/0.93    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 3.79/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 3.79/0.93  fof(f935,plain,(
% 3.79/0.93    k1_xboole_0 = sK2 | ~r2_relset_1(sK2,sK2,k5_relat_1(k6_partfun1(sK2),sK3),sK3) | ~v1_funct_1(k6_partfun1(sK2)) | k6_partfun1(sK2) = sK4),
% 3.79/0.93    inference(subsumption_resolution,[],[f925,f75])).
% 3.79/0.93  fof(f925,plain,(
% 3.79/0.93    k1_xboole_0 = sK2 | ~m1_subset_1(k6_partfun1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~r2_relset_1(sK2,sK2,k5_relat_1(k6_partfun1(sK2),sK3),sK3) | ~v1_funct_1(k6_partfun1(sK2)) | k6_partfun1(sK2) = sK4),
% 3.79/0.93    inference(resolution,[],[f906,f480])).
% 3.79/0.93  fof(f480,plain,(
% 3.79/0.93    ( ! [X0] : (~v1_funct_2(X0,sK2,sK2) | k1_xboole_0 = sK2 | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~r2_relset_1(sK2,sK2,k5_relat_1(X0,sK3),sK3) | ~v1_funct_1(X0) | sK4 = X0) )),
% 3.79/0.93    inference(subsumption_resolution,[],[f479,f62])).
% 3.79/0.93  fof(f479,plain,(
% 3.79/0.93    ( ! [X0] : (~r2_relset_1(sK2,sK2,k5_relat_1(X0,sK3),sK3) | k1_xboole_0 = sK2 | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_2(X0,sK2,sK2) | ~v1_funct_1(X0) | sK4 = X0 | ~v1_funct_1(sK3)) )),
% 3.79/0.93    inference(subsumption_resolution,[],[f474,f64])).
% 3.79/0.93  fof(f474,plain,(
% 3.79/0.93    ( ! [X0] : (~r2_relset_1(sK2,sK2,k5_relat_1(X0,sK3),sK3) | k1_xboole_0 = sK2 | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_2(X0,sK2,sK2) | ~v1_funct_1(X0) | sK4 = X0 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_1(sK3)) )),
% 3.79/0.93    inference(duplicate_literal_removal,[],[f473])).
% 3.79/0.93  fof(f473,plain,(
% 3.79/0.93    ( ! [X0] : (~r2_relset_1(sK2,sK2,k5_relat_1(X0,sK3),sK3) | k1_xboole_0 = sK2 | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_2(X0,sK2,sK2) | ~v1_funct_1(X0) | sK4 = X0 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_1(sK3) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_1(X0)) )),
% 3.79/0.93    inference(superposition,[],[f466,f109])).
% 3.79/0.93  fof(f466,plain,(
% 3.79/0.93    ( ! [X4] : (~r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,X4,sK3),sK3) | k1_xboole_0 = sK2 | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_2(X4,sK2,sK2) | ~v1_funct_1(X4) | sK4 = X4) )),
% 3.79/0.93    inference(forward_demodulation,[],[f465,f228])).
% 3.79/0.93  fof(f228,plain,(
% 3.79/0.93    sK3 = k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3)),
% 3.79/0.93    inference(subsumption_resolution,[],[f227,f65])).
% 3.79/0.93  fof(f65,plain,(
% 3.79/0.93    v1_funct_1(sK4)),
% 3.79/0.93    inference(cnf_transformation,[],[f53])).
% 3.79/0.93  fof(f227,plain,(
% 3.79/0.93    ~v1_funct_1(sK4) | sK3 = k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3)),
% 3.79/0.93    inference(subsumption_resolution,[],[f226,f67])).
% 3.79/0.93  fof(f226,plain,(
% 3.79/0.93    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_1(sK4) | sK3 = k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3)),
% 3.79/0.93    inference(subsumption_resolution,[],[f225,f62])).
% 3.79/0.93  fof(f225,plain,(
% 3.79/0.93    ~v1_funct_1(sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_1(sK4) | sK3 = k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3)),
% 3.79/0.93    inference(subsumption_resolution,[],[f221,f64])).
% 3.79/0.93  fof(f221,plain,(
% 3.79/0.93    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_1(sK4) | sK3 = k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3)),
% 3.79/0.93    inference(resolution,[],[f111,f182])).
% 3.79/0.93  fof(f182,plain,(
% 3.79/0.93    ~m1_subset_1(k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | sK3 = k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3)),
% 3.79/0.93    inference(subsumption_resolution,[],[f175,f64])).
% 3.79/0.93  fof(f175,plain,(
% 3.79/0.93    sK3 = k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~m1_subset_1(k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))),
% 3.79/0.93    inference(resolution,[],[f107,f68])).
% 3.79/0.93  fof(f68,plain,(
% 3.79/0.93    r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3),sK3)),
% 3.79/0.93    inference(cnf_transformation,[],[f53])).
% 3.79/0.93  fof(f107,plain,(
% 3.79/0.93    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.79/0.93    inference(cnf_transformation,[],[f61])).
% 3.79/0.93  fof(f111,plain,(
% 3.79/0.93    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.79/0.93    inference(cnf_transformation,[],[f45])).
% 3.79/0.93  fof(f465,plain,(
% 3.79/0.93    ( ! [X4] : (~r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,X4,sK3),k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3)) | k1_xboole_0 = sK2 | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_2(X4,sK2,sK2) | ~v1_funct_1(X4) | sK4 = X4) )),
% 3.79/0.93    inference(subsumption_resolution,[],[f464,f65])).
% 3.79/0.93  fof(f464,plain,(
% 3.79/0.93    ( ! [X4] : (~r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,X4,sK3),k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3)) | k1_xboole_0 = sK2 | ~v1_funct_1(sK4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_2(X4,sK2,sK2) | ~v1_funct_1(X4) | sK4 = X4) )),
% 3.79/0.93    inference(subsumption_resolution,[],[f457,f67])).
% 3.79/0.93  fof(f457,plain,(
% 3.79/0.93    ( ! [X4] : (~r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,X4,sK3),k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | k1_xboole_0 = sK2 | ~v1_funct_1(sK4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_2(X4,sK2,sK2) | ~v1_funct_1(X4) | sK4 = X4) )),
% 3.79/0.93    inference(resolution,[],[f451,f66])).
% 3.79/0.93  fof(f66,plain,(
% 3.79/0.93    v1_funct_2(sK4,sK2,sK2)),
% 3.79/0.93    inference(cnf_transformation,[],[f53])).
% 3.79/0.93  fof(f451,plain,(
% 3.79/0.93    ( ! [X8,X7,X9] : (~v1_funct_2(X9,X7,sK2) | ~r2_relset_1(X7,sK2,k1_partfun1(X7,sK2,sK2,sK2,X8,sK3),k1_partfun1(X7,sK2,sK2,sK2,X9,sK3)) | ~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,sK2))) | k1_xboole_0 = sK2 | ~v1_funct_1(X9) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X7,sK2))) | ~v1_funct_2(X8,X7,sK2) | ~v1_funct_1(X8) | X8 = X9) )),
% 3.79/0.93    inference(subsumption_resolution,[],[f450,f63])).
% 3.79/0.93  fof(f450,plain,(
% 3.79/0.93    ( ! [X8,X7,X9] : (~v1_funct_2(sK3,sK2,sK2) | k1_xboole_0 = sK2 | ~r2_relset_1(X7,sK2,k1_partfun1(X7,sK2,sK2,sK2,X8,sK3),k1_partfun1(X7,sK2,sK2,sK2,X9,sK3)) | ~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,sK2))) | ~v1_funct_2(X9,X7,sK2) | ~v1_funct_1(X9) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X7,sK2))) | ~v1_funct_2(X8,X7,sK2) | ~v1_funct_1(X8) | X8 = X9) )),
% 3.79/0.93    inference(duplicate_literal_removal,[],[f448])).
% 3.79/0.93  fof(f448,plain,(
% 3.79/0.93    ( ! [X8,X7,X9] : (~v1_funct_2(sK3,sK2,sK2) | k1_xboole_0 = sK2 | ~r2_relset_1(X7,sK2,k1_partfun1(X7,sK2,sK2,sK2,X8,sK3),k1_partfun1(X7,sK2,sK2,sK2,X9,sK3)) | ~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,sK2))) | ~v1_funct_2(X9,X7,sK2) | ~v1_funct_1(X9) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X7,sK2))) | ~v1_funct_2(X8,X7,sK2) | ~v1_funct_1(X8) | k1_xboole_0 = sK2 | X8 = X9) )),
% 3.79/0.93    inference(resolution,[],[f439,f64])).
% 3.79/0.93  fof(f439,plain,(
% 3.79/0.93    ( ! [X23,X21,X19,X22,X20] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X19,X20))) | ~v1_funct_2(sK3,X19,X20) | k1_xboole_0 = X20 | ~r2_relset_1(X21,X20,k1_partfun1(X21,X19,X19,X20,X22,sK3),k1_partfun1(X21,X19,X19,X20,X23,sK3)) | ~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X19))) | ~v1_funct_2(X23,X21,X19) | ~v1_funct_1(X23) | ~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X21,X19))) | ~v1_funct_2(X22,X21,X19) | ~v1_funct_1(X22) | k1_xboole_0 = X19 | X22 = X23) )),
% 3.79/0.93    inference(subsumption_resolution,[],[f438,f62])).
% 3.79/0.93  fof(f438,plain,(
% 3.79/0.93    ( ! [X23,X21,X19,X22,X20] : (~v1_funct_2(sK3,X19,X20) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X19,X20))) | k1_xboole_0 = X20 | ~r2_relset_1(X21,X20,k1_partfun1(X21,X19,X19,X20,X22,sK3),k1_partfun1(X21,X19,X19,X20,X23,sK3)) | ~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X19))) | ~v1_funct_2(X23,X21,X19) | ~v1_funct_1(X23) | ~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X21,X19))) | ~v1_funct_2(X22,X21,X19) | ~v1_funct_1(X22) | k1_xboole_0 = X19 | X22 = X23) )),
% 3.79/0.93    inference(resolution,[],[f366,f69])).
% 3.79/0.93  fof(f366,plain,(
% 3.79/0.93    ( ! [X12,X10,X8,X7,X11,X9] : (~v2_funct_1(X7) | ~v1_funct_2(X7,X8,X9) | ~v1_funct_1(X7) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X8,X9))) | k1_xboole_0 = X9 | ~r2_relset_1(X10,X9,k1_partfun1(X10,X8,X8,X9,X11,X7),k1_partfun1(X10,X8,X8,X9,X12,X7)) | ~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X8))) | ~v1_funct_2(X12,X10,X8) | ~v1_funct_1(X12) | ~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X10,X8))) | ~v1_funct_2(X11,X10,X8) | ~v1_funct_1(X11) | k1_xboole_0 = X8 | X11 = X12) )),
% 3.79/0.93    inference(duplicate_literal_removal,[],[f365])).
% 3.79/0.93  fof(f365,plain,(
% 3.79/0.93    ( ! [X12,X10,X8,X7,X11,X9] : (~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X8,X9))) | ~v1_funct_2(X7,X8,X9) | ~v1_funct_1(X7) | ~v2_funct_1(X7) | k1_xboole_0 = X9 | ~r2_relset_1(X10,X9,k1_partfun1(X10,X8,X8,X9,X11,X7),k1_partfun1(X10,X8,X8,X9,X12,X7)) | ~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X8))) | ~v1_funct_2(X12,X10,X8) | ~v1_funct_1(X12) | ~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X10,X8))) | ~v1_funct_2(X11,X10,X8) | ~v1_funct_1(X11) | k1_xboole_0 = X8 | X11 = X12 | ~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X8))) | ~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X10,X8)))) )),
% 3.79/0.93    inference(resolution,[],[f263,f107])).
% 3.79/0.93  fof(f263,plain,(
% 3.79/0.93    ( ! [X4,X2,X0,X5,X3,X1] : (r2_relset_1(X3,X0,X4,X5) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X1,X0,X2) | ~v1_funct_1(X1) | ~v2_funct_1(X1) | k1_xboole_0 = X2 | ~r2_relset_1(X3,X2,k1_partfun1(X3,X0,X0,X2,X4,X1),k1_partfun1(X3,X0,X0,X2,X5,X1)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) | ~v1_funct_2(X5,X3,X0) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) | ~v1_funct_2(X4,X3,X0) | ~v1_funct_1(X4) | k1_xboole_0 = X0) )),
% 3.79/0.93    inference(resolution,[],[f183,f97])).
% 3.79/0.93  fof(f97,plain,(
% 3.79/0.93    ( ! [X6,X2,X0,X8,X7,X1] : (~sP0(X0,X1,X2) | ~r2_relset_1(X6,X2,k1_partfun1(X6,X0,X0,X2,X7,X1),k1_partfun1(X6,X0,X0,X2,X8,X1)) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X0))) | ~v1_funct_2(X8,X6,X0) | ~v1_funct_1(X8) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X6,X0))) | ~v1_funct_2(X7,X6,X0) | ~v1_funct_1(X7) | r2_relset_1(X6,X0,X7,X8)) )),
% 3.79/0.93    inference(cnf_transformation,[],[f60])).
% 3.79/0.93  fof(f60,plain,(
% 3.79/0.93    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((~r2_relset_1(sK5(X0,X1,X2),X0,sK6(X0,X1,X2),sK7(X0,X1,X2)) & r2_relset_1(sK5(X0,X1,X2),X2,k1_partfun1(sK5(X0,X1,X2),X0,X0,X2,sK6(X0,X1,X2),X1),k1_partfun1(sK5(X0,X1,X2),X0,X0,X2,sK7(X0,X1,X2),X1)) & m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(sK5(X0,X1,X2),X0))) & v1_funct_2(sK7(X0,X1,X2),sK5(X0,X1,X2),X0) & v1_funct_1(sK7(X0,X1,X2))) & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(sK5(X0,X1,X2),X0))) & v1_funct_2(sK6(X0,X1,X2),sK5(X0,X1,X2),X0) & v1_funct_1(sK6(X0,X1,X2)))) & (! [X6,X7] : (! [X8] : (r2_relset_1(X6,X0,X7,X8) | ~r2_relset_1(X6,X2,k1_partfun1(X6,X0,X0,X2,X7,X1),k1_partfun1(X6,X0,X0,X2,X8,X1)) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X0))) | ~v1_funct_2(X8,X6,X0) | ~v1_funct_1(X8)) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X6,X0))) | ~v1_funct_2(X7,X6,X0) | ~v1_funct_1(X7)) | ~sP0(X0,X1,X2)))),
% 3.79/0.93    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f57,f59,f58])).
% 3.79/0.93  fof(f58,plain,(
% 3.79/0.93    ! [X2,X1,X0] : (? [X3,X4] : (? [X5] : (~r2_relset_1(X3,X0,X4,X5) & r2_relset_1(X3,X2,k1_partfun1(X3,X0,X0,X2,X4,X1),k1_partfun1(X3,X0,X0,X2,X5,X1)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) & v1_funct_2(X5,X3,X0) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) & v1_funct_2(X4,X3,X0) & v1_funct_1(X4)) => (? [X5] : (~r2_relset_1(sK5(X0,X1,X2),X0,sK6(X0,X1,X2),X5) & r2_relset_1(sK5(X0,X1,X2),X2,k1_partfun1(sK5(X0,X1,X2),X0,X0,X2,sK6(X0,X1,X2),X1),k1_partfun1(sK5(X0,X1,X2),X0,X0,X2,X5,X1)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK5(X0,X1,X2),X0))) & v1_funct_2(X5,sK5(X0,X1,X2),X0) & v1_funct_1(X5)) & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(sK5(X0,X1,X2),X0))) & v1_funct_2(sK6(X0,X1,X2),sK5(X0,X1,X2),X0) & v1_funct_1(sK6(X0,X1,X2))))),
% 3.79/0.93    introduced(choice_axiom,[])).
% 3.79/0.93  fof(f59,plain,(
% 3.79/0.93    ! [X2,X1,X0] : (? [X5] : (~r2_relset_1(sK5(X0,X1,X2),X0,sK6(X0,X1,X2),X5) & r2_relset_1(sK5(X0,X1,X2),X2,k1_partfun1(sK5(X0,X1,X2),X0,X0,X2,sK6(X0,X1,X2),X1),k1_partfun1(sK5(X0,X1,X2),X0,X0,X2,X5,X1)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK5(X0,X1,X2),X0))) & v1_funct_2(X5,sK5(X0,X1,X2),X0) & v1_funct_1(X5)) => (~r2_relset_1(sK5(X0,X1,X2),X0,sK6(X0,X1,X2),sK7(X0,X1,X2)) & r2_relset_1(sK5(X0,X1,X2),X2,k1_partfun1(sK5(X0,X1,X2),X0,X0,X2,sK6(X0,X1,X2),X1),k1_partfun1(sK5(X0,X1,X2),X0,X0,X2,sK7(X0,X1,X2),X1)) & m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(sK5(X0,X1,X2),X0))) & v1_funct_2(sK7(X0,X1,X2),sK5(X0,X1,X2),X0) & v1_funct_1(sK7(X0,X1,X2))))),
% 3.79/0.93    introduced(choice_axiom,[])).
% 3.79/0.93  fof(f57,plain,(
% 3.79/0.93    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3,X4] : (? [X5] : (~r2_relset_1(X3,X0,X4,X5) & r2_relset_1(X3,X2,k1_partfun1(X3,X0,X0,X2,X4,X1),k1_partfun1(X3,X0,X0,X2,X5,X1)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) & v1_funct_2(X5,X3,X0) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) & v1_funct_2(X4,X3,X0) & v1_funct_1(X4))) & (! [X6,X7] : (! [X8] : (r2_relset_1(X6,X0,X7,X8) | ~r2_relset_1(X6,X2,k1_partfun1(X6,X0,X0,X2,X7,X1),k1_partfun1(X6,X0,X0,X2,X8,X1)) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X0))) | ~v1_funct_2(X8,X6,X0) | ~v1_funct_1(X8)) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X6,X0))) | ~v1_funct_2(X7,X6,X0) | ~v1_funct_1(X7)) | ~sP0(X0,X1,X2)))),
% 3.79/0.93    inference(rectify,[],[f56])).
% 3.79/0.93  fof(f56,plain,(
% 3.79/0.93    ! [X0,X2,X1] : ((sP0(X0,X2,X1) | ? [X3,X4] : (? [X5] : (~r2_relset_1(X3,X0,X4,X5) & r2_relset_1(X3,X1,k1_partfun1(X3,X0,X0,X1,X4,X2),k1_partfun1(X3,X0,X0,X1,X5,X2)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) & v1_funct_2(X5,X3,X0) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) & v1_funct_2(X4,X3,X0) & v1_funct_1(X4))) & (! [X3,X4] : (! [X5] : (r2_relset_1(X3,X0,X4,X5) | ~r2_relset_1(X3,X1,k1_partfun1(X3,X0,X0,X1,X4,X2),k1_partfun1(X3,X0,X0,X1,X5,X2)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) | ~v1_funct_2(X5,X3,X0) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) | ~v1_funct_2(X4,X3,X0) | ~v1_funct_1(X4)) | ~sP0(X0,X2,X1)))),
% 3.79/0.93    inference(nnf_transformation,[],[f48])).
% 3.79/0.93  fof(f48,plain,(
% 3.79/0.93    ! [X0,X2,X1] : (sP0(X0,X2,X1) <=> ! [X3,X4] : (! [X5] : (r2_relset_1(X3,X0,X4,X5) | ~r2_relset_1(X3,X1,k1_partfun1(X3,X0,X0,X1,X4,X2),k1_partfun1(X3,X0,X0,X1,X5,X2)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) | ~v1_funct_2(X5,X3,X0) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) | ~v1_funct_2(X4,X3,X0) | ~v1_funct_1(X4)))),
% 3.79/0.93    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 3.79/0.93  fof(f183,plain,(
% 3.79/0.93    ( ! [X2,X0,X1] : (sP0(X1,X2,X0) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X2,X1,X0) | ~v1_funct_1(X2) | ~v2_funct_1(X2) | k1_xboole_0 = X0) )),
% 3.79/0.93    inference(resolution,[],[f106,f95])).
% 3.79/0.93  fof(f95,plain,(
% 3.79/0.93    ( ! [X2,X0,X1] : (~sP1(X0,X1,X2) | ~v2_funct_1(X1) | sP0(X2,X1,X0)) )),
% 3.79/0.93    inference(cnf_transformation,[],[f55])).
% 3.79/0.93  fof(f55,plain,(
% 3.79/0.93    ! [X0,X1,X2] : (((v2_funct_1(X1) | ~sP0(X2,X1,X0)) & (sP0(X2,X1,X0) | ~v2_funct_1(X1))) | ~sP1(X0,X1,X2))),
% 3.79/0.93    inference(rectify,[],[f54])).
% 3.79/0.93  fof(f54,plain,(
% 3.79/0.93    ! [X1,X2,X0] : (((v2_funct_1(X2) | ~sP0(X0,X2,X1)) & (sP0(X0,X2,X1) | ~v2_funct_1(X2))) | ~sP1(X1,X2,X0))),
% 3.79/0.93    inference(nnf_transformation,[],[f49])).
% 3.79/0.93  fof(f49,plain,(
% 3.79/0.93    ! [X1,X2,X0] : ((v2_funct_1(X2) <=> sP0(X0,X2,X1)) | ~sP1(X1,X2,X0))),
% 3.79/0.93    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 3.79/0.93  fof(f106,plain,(
% 3.79/0.93    ( ! [X2,X0,X1] : (sP1(X1,X2,X0) | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.79/0.93    inference(cnf_transformation,[],[f50])).
% 3.79/0.93  fof(f50,plain,(
% 3.79/0.93    ! [X0,X1,X2] : (sP1(X1,X2,X0) | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.79/0.93    inference(definition_folding,[],[f39,f49,f48])).
% 3.79/0.93  fof(f39,plain,(
% 3.79/0.93    ! [X0,X1,X2] : ((v2_funct_1(X2) <=> ! [X3,X4] : (! [X5] : (r2_relset_1(X3,X0,X4,X5) | ~r2_relset_1(X3,X1,k1_partfun1(X3,X0,X0,X1,X4,X2),k1_partfun1(X3,X0,X0,X1,X5,X2)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) | ~v1_funct_2(X5,X3,X0) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) | ~v1_funct_2(X4,X3,X0) | ~v1_funct_1(X4))) | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.79/0.93    inference(flattening,[],[f38])).
% 3.79/0.93  fof(f38,plain,(
% 3.79/0.93    ! [X0,X1,X2] : (((v2_funct_1(X2) <=> ! [X3,X4] : (! [X5] : ((r2_relset_1(X3,X0,X4,X5) | ~r2_relset_1(X3,X1,k1_partfun1(X3,X0,X0,X1,X4,X2),k1_partfun1(X3,X0,X0,X1,X5,X2))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) | ~v1_funct_2(X5,X3,X0) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) | ~v1_funct_2(X4,X3,X0) | ~v1_funct_1(X4)))) | k1_xboole_0 = X1 | k1_xboole_0 = X0) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.79/0.93    inference(ennf_transformation,[],[f16])).
% 3.79/0.93  fof(f16,axiom,(
% 3.79/0.93    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ~(~(v2_funct_1(X2) <=> ! [X3,X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) & v1_funct_2(X4,X3,X0) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) & v1_funct_2(X5,X3,X0) & v1_funct_1(X5)) => (r2_relset_1(X3,X1,k1_partfun1(X3,X0,X0,X1,X4,X2),k1_partfun1(X3,X0,X0,X1,X5,X2)) => r2_relset_1(X3,X0,X4,X5))))) & k1_xboole_0 != X1 & k1_xboole_0 != X0))),
% 3.79/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_funct_2)).
% 3.79/0.93  fof(f906,plain,(
% 3.79/0.93    v1_funct_2(k6_partfun1(sK2),sK2,sK2)),
% 3.79/0.93    inference(resolution,[],[f902,f134])).
% 3.79/0.93  fof(f134,plain,(
% 3.79/0.93    ( ! [X0] : (~v1_funct_1(k6_partfun1(X0)) | v1_funct_2(k6_partfun1(X0),X0,X0)) )),
% 3.79/0.93    inference(forward_demodulation,[],[f133,f115])).
% 3.79/0.93  fof(f115,plain,(
% 3.79/0.93    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 3.79/0.93    inference(definition_unfolding,[],[f77,f71])).
% 3.79/0.93  fof(f77,plain,(
% 3.79/0.93    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 3.79/0.93    inference(cnf_transformation,[],[f4])).
% 3.79/0.93  fof(f4,axiom,(
% 3.79/0.93    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 3.79/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 3.79/0.93  fof(f133,plain,(
% 3.79/0.93    ( ! [X0] : (v1_funct_2(k6_partfun1(X0),X0,k2_relat_1(k6_partfun1(X0))) | ~v1_funct_1(k6_partfun1(X0))) )),
% 3.79/0.93    inference(subsumption_resolution,[],[f131,f114])).
% 3.79/0.93  fof(f114,plain,(
% 3.79/0.93    ( ! [X0] : (v1_relat_1(k6_partfun1(X0))) )),
% 3.79/0.93    inference(definition_unfolding,[],[f72,f71])).
% 3.79/0.93  fof(f72,plain,(
% 3.79/0.93    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 3.79/0.93    inference(cnf_transformation,[],[f5])).
% 3.79/0.93  fof(f5,axiom,(
% 3.79/0.93    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 3.79/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).
% 3.79/0.93  fof(f131,plain,(
% 3.79/0.93    ( ! [X0] : (v1_funct_2(k6_partfun1(X0),X0,k2_relat_1(k6_partfun1(X0))) | ~v1_funct_1(k6_partfun1(X0)) | ~v1_relat_1(k6_partfun1(X0))) )),
% 3.79/0.93    inference(superposition,[],[f82,f116])).
% 3.79/0.93  fof(f116,plain,(
% 3.79/0.93    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 3.79/0.93    inference(definition_unfolding,[],[f76,f71])).
% 3.79/0.93  fof(f76,plain,(
% 3.79/0.93    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 3.79/0.93    inference(cnf_transformation,[],[f4])).
% 3.79/0.93  fof(f70,plain,(
% 3.79/0.93    ~r2_relset_1(sK2,sK2,sK4,k6_partfun1(sK2))),
% 3.79/0.93    inference(cnf_transformation,[],[f53])).
% 3.79/0.93  fof(f67,plain,(
% 3.79/0.93    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))),
% 3.79/0.93    inference(cnf_transformation,[],[f53])).
% 3.79/0.93  fof(f1183,plain,(
% 3.79/0.93    ( ! [X0] : (~m1_subset_1(sK4,k1_zfmisc_1(X0)) | k1_xboole_0 = sK4 | ~v1_relat_1(X0)) )),
% 3.79/0.93    inference(resolution,[],[f1088,f80])).
% 3.79/0.93  fof(f1088,plain,(
% 3.79/0.93    ~v1_relat_1(sK4) | k1_xboole_0 = sK4),
% 3.79/0.93    inference(trivial_inequality_removal,[],[f1054])).
% 3.79/0.93  fof(f1054,plain,(
% 3.79/0.93    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK4 | ~v1_relat_1(sK4)),
% 3.79/0.93    inference(backward_demodulation,[],[f173,f1040])).
% 3.79/0.93  fof(f173,plain,(
% 3.79/0.93    k1_xboole_0 != sK2 | k1_xboole_0 = sK4 | ~v1_relat_1(sK4)),
% 3.79/0.93    inference(superposition,[],[f78,f169])).
% 3.79/0.93  fof(f169,plain,(
% 3.79/0.93    sK2 = k1_relat_1(sK4)),
% 3.79/0.93    inference(subsumption_resolution,[],[f167,f67])).
% 3.79/0.93  fof(f167,plain,(
% 3.79/0.93    sK2 = k1_relat_1(sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))),
% 3.79/0.93    inference(superposition,[],[f158,f88])).
% 3.79/0.93  fof(f158,plain,(
% 3.79/0.93    sK2 = k1_relset_1(sK2,sK2,sK4)),
% 3.79/0.93    inference(subsumption_resolution,[],[f157,f65])).
% 3.79/0.93  fof(f157,plain,(
% 3.79/0.93    sK2 = k1_relset_1(sK2,sK2,sK4) | ~v1_funct_1(sK4)),
% 3.79/0.93    inference(subsumption_resolution,[],[f152,f67])).
% 3.79/0.93  fof(f152,plain,(
% 3.79/0.93    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | sK2 = k1_relset_1(sK2,sK2,sK4) | ~v1_funct_1(sK4)),
% 3.79/0.93    inference(resolution,[],[f87,f66])).
% 3.79/0.93  fof(f78,plain,(
% 3.79/0.93    ( ! [X0] : (k1_relat_1(X0) != k1_xboole_0 | k1_xboole_0 = X0 | ~v1_relat_1(X0)) )),
% 3.79/0.93    inference(cnf_transformation,[],[f25])).
% 3.79/0.93  fof(f25,plain,(
% 3.79/0.93    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_relat_1(X0) != k1_xboole_0) | ~v1_relat_1(X0))),
% 3.79/0.93    inference(flattening,[],[f24])).
% 3.79/0.93  fof(f24,plain,(
% 3.79/0.93    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_relat_1(X0) != k1_xboole_0)) | ~v1_relat_1(X0))),
% 3.79/0.93    inference(ennf_transformation,[],[f3])).
% 3.79/0.94  % (6522)Time limit reached!
% 3.79/0.94  % (6522)------------------------------
% 3.79/0.94  % (6522)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.79/0.94  fof(f3,axiom,(
% 3.79/0.94    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_relat_1(X0) = k1_xboole_0) => k1_xboole_0 = X0))),
% 3.79/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).
% 3.79/0.94  fof(f1090,plain,(
% 3.79/0.94    ~r2_relset_1(k1_xboole_0,k1_xboole_0,sK4,k1_xboole_0)),
% 3.79/0.94    inference(forward_demodulation,[],[f1045,f124])).
% 3.79/0.94  fof(f124,plain,(
% 3.79/0.94    k1_xboole_0 = k6_partfun1(k1_xboole_0)),
% 3.79/0.94    inference(equality_resolution,[],[f122])).
% 3.79/0.94  fof(f122,plain,(
% 3.79/0.94    ( ! [X0] : (k1_xboole_0 != X0 | k1_xboole_0 = k6_partfun1(X0)) )),
% 3.79/0.94    inference(subsumption_resolution,[],[f121,f114])).
% 3.79/0.94  fof(f121,plain,(
% 3.79/0.94    ( ! [X0] : (k1_xboole_0 != X0 | k1_xboole_0 = k6_partfun1(X0) | ~v1_relat_1(k6_partfun1(X0))) )),
% 3.79/0.94    inference(superposition,[],[f78,f116])).
% 3.79/0.94  fof(f1045,plain,(
% 3.79/0.94    ~r2_relset_1(k1_xboole_0,k1_xboole_0,sK4,k6_partfun1(k1_xboole_0))),
% 3.79/0.94    inference(backward_demodulation,[],[f70,f1040])).
% 3.79/0.94  fof(f125,plain,(
% 3.79/0.94    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 3.79/0.94    inference(superposition,[],[f75,f124])).
% 3.79/0.94  % SZS output end Proof for theBenchmark
% 3.79/0.94  % (6515)------------------------------
% 3.79/0.94  % (6515)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.79/0.94  % (6515)Termination reason: Refutation
% 3.79/0.94  
% 3.79/0.94  % (6515)Memory used [KB]: 10362
% 3.79/0.94  % (6515)Time elapsed: 0.508 s
% 3.79/0.94  % (6515)------------------------------
% 3.79/0.94  % (6515)------------------------------
% 3.79/0.94  % (6492)Success in time 0.58 s
%------------------------------------------------------------------------------
