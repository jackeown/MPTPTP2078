%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:05:27 EST 2020

% Result     : Theorem 4.77s
% Output     : Refutation 5.60s
% Verified   : 
% Statistics : Number of formulae       :  196 (3199 expanded)
%              Number of leaves         :   26 ( 943 expanded)
%              Depth                    :   46
%              Number of atoms          :  974 (23378 expanded)
%              Number of equality atoms :  172 (1052 expanded)
%              Maximal formula depth    :   23 (   8 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1570,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f133,f1542,f127])).

fof(f127,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(duplicate_literal_removal,[],[f126])).

fof(f126,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f114])).

fof(f114,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f1542,plain,(
    ~ r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f1369,f1526])).

fof(f1526,plain,(
    k1_xboole_0 = sK4 ),
    inference(resolution,[],[f1367,f1327])).

fof(f1327,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f70,f1323])).

fof(f1323,plain,(
    k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f1320,f70])).

fof(f1320,plain,
    ( k1_xboole_0 = sK2
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(resolution,[],[f1218,f127])).

fof(f1218,plain,
    ( ~ r2_relset_1(sK2,sK2,sK4,sK4)
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f73,f1215])).

fof(f1215,plain,
    ( k6_partfun1(sK2) = sK4
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f1212,f67])).

fof(f67,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,
    ( ~ r2_relset_1(sK2,sK2,sK4,k6_partfun1(sK2))
    & v2_funct_1(sK3)
    & r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3),sK3)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    & v1_funct_2(sK4,sK2,sK2)
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    & v1_funct_2(sK3,sK2,sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f25,f54,f53])).

fof(f53,plain,
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

fof(f54,plain,
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

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
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
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_funct_2)).

fof(f1212,plain,
    ( k1_xboole_0 = sK2
    | k6_partfun1(sK2) = sK4
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(resolution,[],[f1198,f209])).

fof(f209,plain,(
    ! [X2,X0,X1] :
      ( r2_relset_1(X0,X1,k5_relat_1(k6_partfun1(X0),X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(subsumption_resolution,[],[f208,f80])).

fof(f80,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f208,plain,(
    ! [X2,X0,X1] :
      ( r2_relset_1(X0,X1,k5_relat_1(k6_partfun1(X0),X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(duplicate_literal_removal,[],[f205])).

fof(f205,plain,(
    ! [X2,X0,X1] :
      ( r2_relset_1(X0,X1,k5_relat_1(k6_partfun1(X0),X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(superposition,[],[f96,f118])).

fof(f118,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2)
        & r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2)
        & r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_2)).

fof(f1198,plain,
    ( ~ r2_relset_1(sK2,sK2,k5_relat_1(k6_partfun1(sK2),sK3),sK3)
    | k1_xboole_0 = sK2
    | k6_partfun1(sK2) = sK4 ),
    inference(subsumption_resolution,[],[f1197,f1150])).

fof(f1150,plain,(
    v1_funct_1(k6_partfun1(sK2)) ),
    inference(resolution,[],[f1146,f67])).

fof(f1146,plain,(
    ! [X6,X7] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
      | v1_funct_1(k6_partfun1(sK2)) ) ),
    inference(resolution,[],[f1142,f67])).

fof(f1142,plain,(
    ! [X10,X8,X11,X9] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))
      | v1_funct_1(k6_partfun1(sK2)) ) ),
    inference(resolution,[],[f1137,f67])).

fof(f1137,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | v1_funct_1(k6_partfun1(sK2)) ) ),
    inference(subsumption_resolution,[],[f1136,f290])).

fof(f290,plain,(
    ! [X14,X13] :
      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_relat_1(sK3))))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X13,X14))) ) ),
    inference(forward_demodulation,[],[f286,f183])).

fof(f183,plain,(
    sK2 = k1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f181,f67])).

fof(f181,plain,
    ( sK2 = k1_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(superposition,[],[f178,f94])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f178,plain,(
    sK2 = k1_relset_1(sK2,sK2,sK3) ),
    inference(subsumption_resolution,[],[f177,f65])).

fof(f65,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f55])).

fof(f177,plain,
    ( sK2 = k1_relset_1(sK2,sK2,sK3)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f173,f67])).

fof(f173,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | sK2 = k1_relset_1(sK2,sK2,sK3)
    | ~ v1_funct_1(sK3) ),
    inference(resolution,[],[f90,f66])).

fof(f66,plain,(
    v1_funct_2(sK3,sK2,sK2) ),
    inference(cnf_transformation,[],[f55])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(X1,X0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | k1_relset_1(X0,X0,X1) = X0
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k1_relset_1(X0,X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_2)).

fof(f286,plain,(
    ! [X14,X13] :
      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X13,X14))) ) ),
    inference(resolution,[],[f155,f65])).

fof(f155,plain,(
    ! [X2,X3,X1] :
      ( ~ v1_funct_1(X1)
      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ) ),
    inference(resolution,[],[f87,f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f87,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

fof(f1136,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_relat_1(sK3))))
      | v1_funct_1(k6_partfun1(sK2))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) ) ),
    inference(forward_demodulation,[],[f1135,f183])).

fof(f1135,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_1(k6_partfun1(sK2))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) ) ),
    inference(subsumption_resolution,[],[f1134,f65])).

fof(f1134,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_1(k6_partfun1(sK2))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(sK3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) ) ),
    inference(trivial_inequality_removal,[],[f1130])).

fof(f1130,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k2_relat_1(sK3) != k2_relat_1(sK3)
      | v1_funct_1(k6_partfun1(sK2))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(sK3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) ) ),
    inference(resolution,[],[f1107,f144])).

fof(f144,plain,(
    ! [X2,X3,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ) ),
    inference(resolution,[],[f86,f93])).

fof(f86,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f1107,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_2(sK3,X3,X2)
      | k2_relat_1(sK3) != X2
      | v1_funct_1(k6_partfun1(sK2))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) ) ),
    inference(subsumption_resolution,[],[f1106,f290])).

fof(f1106,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_relat_1(sK3))))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relat_1(sK3) != X2
      | v1_funct_1(k6_partfun1(sK2))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
      | ~ v1_funct_2(sK3,X3,X2)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) ) ),
    inference(forward_demodulation,[],[f1105,f183])).

fof(f1105,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relat_1(sK3) != X2
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))))
      | v1_funct_1(k6_partfun1(sK2))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
      | ~ v1_funct_2(sK3,X3,X2)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) ) ),
    inference(subsumption_resolution,[],[f1104,f65])).

fof(f1104,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relat_1(sK3) != X2
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))))
      | v1_funct_1(k6_partfun1(sK2))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
      | ~ v1_funct_2(sK3,X3,X2)
      | ~ v1_funct_1(sK3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) ) ),
    inference(trivial_inequality_removal,[],[f1100])).

fof(f1100,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relat_1(sK3) != X2
      | k2_relat_1(sK3) != k2_relat_1(sK3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))))
      | v1_funct_1(k6_partfun1(sK2))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
      | ~ v1_funct_2(sK3,X3,X2)
      | ~ v1_funct_1(sK3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) ) ),
    inference(resolution,[],[f930,f144])).

fof(f930,plain,(
    ! [X26,X24,X23,X27,X25,X22] :
      ( ~ v1_funct_2(sK3,X26,X25)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X22,X23)))
      | k2_relat_1(sK3) != X24
      | k2_relat_1(sK3) != X25
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X26,X25)))
      | v1_funct_1(k6_partfun1(sK2))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X27,X24)))
      | ~ v1_funct_2(sK3,X27,X24) ) ),
    inference(forward_demodulation,[],[f929,f183])).

fof(f929,plain,(
    ! [X26,X24,X23,X27,X25,X22] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X22,X23)))
      | k2_relat_1(sK3) != X24
      | k2_relat_1(sK3) != X25
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X26,X25)))
      | ~ v1_funct_2(sK3,X26,X25)
      | v1_funct_1(k6_partfun1(k1_relat_1(sK3)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X27,X24)))
      | ~ v1_funct_2(sK3,X27,X24) ) ),
    inference(subsumption_resolution,[],[f921,f65])).

fof(f921,plain,(
    ! [X26,X24,X23,X27,X25,X22] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X22,X23)))
      | ~ v1_funct_1(sK3)
      | k2_relat_1(sK3) != X24
      | k2_relat_1(sK3) != X25
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X26,X25)))
      | ~ v1_funct_2(sK3,X26,X25)
      | v1_funct_1(k6_partfun1(k1_relat_1(sK3)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X27,X24)))
      | ~ v1_funct_2(sK3,X27,X24) ) ),
    inference(resolution,[],[f719,f72])).

fof(f72,plain,(
    v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f55])).

fof(f719,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_1(X2)
      | k2_relat_1(X2) != X1
      | k2_relat_1(X2) != X5
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X6,X5)))
      | ~ v1_funct_2(X2,X6,X5)
      | v1_funct_1(k6_partfun1(k1_relat_1(X2)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f718])).

fof(f718,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( k2_relat_1(X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k2_relat_1(X2) != X5
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X6,X5)))
      | ~ v1_funct_2(X2,X6,X5)
      | v1_funct_1(k6_partfun1(k1_relat_1(X2)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(superposition,[],[f513,f95])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f513,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( k2_relset_1(X5,X6,X0) != X6
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k2_relat_1(X0) != X3
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X4,X3)))
      | ~ v1_funct_2(X0,X4,X3)
      | v1_funct_1(k6_partfun1(k1_relat_1(X0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
      | ~ v1_funct_2(X0,X5,X6) ) ),
    inference(duplicate_literal_removal,[],[f509])).

fof(f509,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( v1_funct_1(k6_partfun1(k1_relat_1(X0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k2_relat_1(X0) != X3
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X4,X3)))
      | ~ v1_funct_2(X0,X4,X3)
      | k2_relset_1(X5,X6,X0) != X6
      | ~ v2_funct_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
      | ~ v1_funct_2(X0,X5,X6)
      | ~ v1_funct_1(X0) ) ),
    inference(resolution,[],[f502,f100])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

fof(f502,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
      | v1_funct_1(k6_partfun1(k1_relat_1(X2)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k2_relat_1(X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f501])).

fof(f501,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( k2_relat_1(X2) != X1
      | v1_funct_1(k6_partfun1(k1_relat_1(X2)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_1(X2)
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(superposition,[],[f405,f95])).

fof(f405,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( k2_relset_1(X5,X6,X0) != X6
      | v1_funct_1(k6_partfun1(k1_relat_1(X0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
      | ~ v1_funct_2(X0,X5,X6) ) ),
    inference(duplicate_literal_removal,[],[f404])).

fof(f404,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | v1_funct_1(k6_partfun1(k1_relat_1(X0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k2_relset_1(X5,X6,X0) != X6
      | ~ v2_funct_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
      | ~ v1_funct_2(X0,X5,X6)
      | ~ v1_funct_1(X0) ) ),
    inference(resolution,[],[f307,f98])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(k2_funct_1(X2))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f307,plain,(
    ! [X6,X8,X7,X5,X9] :
      ( ~ v1_funct_1(k2_funct_1(X5))
      | ~ m1_subset_1(k2_funct_1(X5),k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
      | v1_funct_1(k6_partfun1(k1_relat_1(X5)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))
      | ~ v1_funct_1(X5)
      | ~ v2_funct_1(X5) ) ),
    inference(subsumption_resolution,[],[f304,f93])).

fof(f304,plain,(
    ! [X6,X8,X7,X5,X9] :
      ( v1_funct_1(k6_partfun1(k1_relat_1(X5)))
      | ~ m1_subset_1(k2_funct_1(X5),k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
      | ~ v1_funct_1(k2_funct_1(X5))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))
      | ~ v1_funct_1(X5)
      | ~ v2_funct_1(X5)
      | ~ v1_relat_1(X5) ) ),
    inference(duplicate_literal_removal,[],[f302])).

fof(f302,plain,(
    ! [X6,X8,X7,X5,X9] :
      ( v1_funct_1(k6_partfun1(k1_relat_1(X5)))
      | ~ m1_subset_1(k2_funct_1(X5),k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
      | ~ v1_funct_1(k2_funct_1(X5))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))
      | ~ v1_funct_1(X5)
      | ~ v2_funct_1(X5)
      | ~ v1_funct_1(X5)
      | ~ v1_relat_1(X5) ) ),
    inference(superposition,[],[f247,f125])).

fof(f125,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f88,f76])).

fof(f76,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f88,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

fof(f247,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_1(k5_relat_1(X4,X5))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(duplicate_literal_removal,[],[f246])).

fof(f246,plain,(
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
    inference(superposition,[],[f116,f115])).

fof(f115,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
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
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f116,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
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
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f1197,plain,
    ( k1_xboole_0 = sK2
    | ~ r2_relset_1(sK2,sK2,k5_relat_1(k6_partfun1(sK2),sK3),sK3)
    | ~ v1_funct_1(k6_partfun1(sK2))
    | k6_partfun1(sK2) = sK4 ),
    inference(subsumption_resolution,[],[f1188,f80])).

fof(f1188,plain,
    ( k1_xboole_0 = sK2
    | ~ m1_subset_1(k6_partfun1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ r2_relset_1(sK2,sK2,k5_relat_1(k6_partfun1(sK2),sK3),sK3)
    | ~ v1_funct_1(k6_partfun1(sK2))
    | k6_partfun1(sK2) = sK4 ),
    inference(resolution,[],[f1166,f571])).

fof(f571,plain,(
    ! [X0] :
      ( ~ v1_funct_2(X0,sK2,sK2)
      | k1_xboole_0 = sK2
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
      | ~ r2_relset_1(sK2,sK2,k5_relat_1(X0,sK3),sK3)
      | ~ v1_funct_1(X0)
      | sK4 = X0 ) ),
    inference(subsumption_resolution,[],[f570,f65])).

fof(f570,plain,(
    ! [X0] :
      ( ~ r2_relset_1(sK2,sK2,k5_relat_1(X0,sK3),sK3)
      | k1_xboole_0 = sK2
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
      | ~ v1_funct_2(X0,sK2,sK2)
      | ~ v1_funct_1(X0)
      | sK4 = X0
      | ~ v1_funct_1(sK3) ) ),
    inference(subsumption_resolution,[],[f565,f67])).

fof(f565,plain,(
    ! [X0] :
      ( ~ r2_relset_1(sK2,sK2,k5_relat_1(X0,sK3),sK3)
      | k1_xboole_0 = sK2
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
      | ~ v1_funct_2(X0,sK2,sK2)
      | ~ v1_funct_1(X0)
      | sK4 = X0
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
      | ~ v1_funct_1(sK3) ) ),
    inference(duplicate_literal_removal,[],[f564])).

fof(f564,plain,(
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
    inference(superposition,[],[f557,f115])).

fof(f557,plain,(
    ! [X4] :
      ( ~ r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,X4,sK3),sK3)
      | k1_xboole_0 = sK2
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
      | ~ v1_funct_2(X4,sK2,sK2)
      | ~ v1_funct_1(X4)
      | sK4 = X4 ) ),
    inference(forward_demodulation,[],[f556,f268])).

fof(f268,plain,(
    sK3 = k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3) ),
    inference(subsumption_resolution,[],[f267,f68])).

fof(f68,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f55])).

fof(f267,plain,
    ( ~ v1_funct_1(sK4)
    | sK3 = k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3) ),
    inference(subsumption_resolution,[],[f266,f70])).

fof(f266,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v1_funct_1(sK4)
    | sK3 = k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3) ),
    inference(subsumption_resolution,[],[f265,f65])).

fof(f265,plain,
    ( ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v1_funct_1(sK4)
    | sK3 = k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3) ),
    inference(subsumption_resolution,[],[f262,f67])).

fof(f262,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v1_funct_1(sK4)
    | sK3 = k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3) ),
    inference(resolution,[],[f117,f202])).

fof(f202,plain,
    ( ~ m1_subset_1(k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | sK3 = k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3) ),
    inference(subsumption_resolution,[],[f195,f67])).

fof(f195,plain,
    ( sK3 = k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ m1_subset_1(k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(resolution,[],[f113,f71])).

fof(f71,plain,(
    r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3),sK3) ),
    inference(cnf_transformation,[],[f55])).

fof(f113,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f117,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f556,plain,(
    ! [X4] :
      ( ~ r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,X4,sK3),k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3))
      | k1_xboole_0 = sK2
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
      | ~ v1_funct_2(X4,sK2,sK2)
      | ~ v1_funct_1(X4)
      | sK4 = X4 ) ),
    inference(subsumption_resolution,[],[f555,f68])).

fof(f555,plain,(
    ! [X4] :
      ( ~ r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,X4,sK3),k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3))
      | k1_xboole_0 = sK2
      | ~ v1_funct_1(sK4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
      | ~ v1_funct_2(X4,sK2,sK2)
      | ~ v1_funct_1(X4)
      | sK4 = X4 ) ),
    inference(subsumption_resolution,[],[f548,f70])).

fof(f548,plain,(
    ! [X4] :
      ( ~ r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,X4,sK3),k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
      | k1_xboole_0 = sK2
      | ~ v1_funct_1(sK4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
      | ~ v1_funct_2(X4,sK2,sK2)
      | ~ v1_funct_1(X4)
      | sK4 = X4 ) ),
    inference(resolution,[],[f542,f69])).

fof(f69,plain,(
    v1_funct_2(sK4,sK2,sK2) ),
    inference(cnf_transformation,[],[f55])).

fof(f542,plain,(
    ! [X6,X7,X5] :
      ( ~ v1_funct_2(X7,X5,sK2)
      | ~ r2_relset_1(X5,sK2,k1_partfun1(X5,sK2,sK2,sK2,X6,sK3),k1_partfun1(X5,sK2,sK2,sK2,X7,sK3))
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X5,sK2)))
      | k1_xboole_0 = sK2
      | ~ v1_funct_1(X7)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X5,sK2)))
      | ~ v1_funct_2(X6,X5,sK2)
      | ~ v1_funct_1(X6)
      | X6 = X7 ) ),
    inference(subsumption_resolution,[],[f532,f67])).

fof(f532,plain,(
    ! [X6,X7,X5] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
      | k1_xboole_0 = sK2
      | ~ r2_relset_1(X5,sK2,k1_partfun1(X5,sK2,sK2,sK2,X6,sK3),k1_partfun1(X5,sK2,sK2,sK2,X7,sK3))
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X5,sK2)))
      | ~ v1_funct_2(X7,X5,sK2)
      | ~ v1_funct_1(X7)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X5,sK2)))
      | ~ v1_funct_2(X6,X5,sK2)
      | ~ v1_funct_1(X6)
      | X6 = X7 ) ),
    inference(duplicate_literal_removal,[],[f530])).

fof(f530,plain,(
    ! [X6,X7,X5] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
      | k1_xboole_0 = sK2
      | ~ r2_relset_1(X5,sK2,k1_partfun1(X5,sK2,sK2,sK2,X6,sK3),k1_partfun1(X5,sK2,sK2,sK2,X7,sK3))
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X5,sK2)))
      | ~ v1_funct_2(X7,X5,sK2)
      | ~ v1_funct_1(X7)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X5,sK2)))
      | ~ v1_funct_2(X6,X5,sK2)
      | ~ v1_funct_1(X6)
      | k1_xboole_0 = sK2
      | X6 = X7 ) ),
    inference(resolution,[],[f528,f66])).

fof(f528,plain,(
    ! [X23,X21,X19,X22,X20] :
      ( ~ v1_funct_2(sK3,X19,X20)
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
    inference(subsumption_resolution,[],[f527,f65])).

fof(f527,plain,(
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
    inference(resolution,[],[f466,f72])).

fof(f466,plain,(
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
    inference(duplicate_literal_removal,[],[f465])).

fof(f465,plain,(
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
    inference(resolution,[],[f310,f113])).

fof(f310,plain,(
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
    inference(resolution,[],[f203,f103])).

fof(f103,plain,(
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
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f60,f62,f61])).

fof(f61,plain,(
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

fof(f62,plain,(
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

fof(f60,plain,(
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
    inference(rectify,[],[f59])).

fof(f59,plain,(
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
    inference(nnf_transformation,[],[f50])).

fof(f50,plain,(
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

fof(f203,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X2,X0)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X2,X1,X0)
      | ~ v1_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f112,f101])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ v2_funct_1(X1)
      | sP0(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( ( ( v2_funct_1(X1)
          | ~ sP0(X2,X1,X0) )
        & ( sP0(X2,X1,X0)
          | ~ v2_funct_1(X1) ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f57])).

fof(f57,plain,(
    ! [X1,X2,X0] :
      ( ( ( v2_funct_1(X2)
          | ~ sP0(X0,X2,X1) )
        & ( sP0(X0,X2,X1)
          | ~ v2_funct_1(X2) ) )
      | ~ sP1(X1,X2,X0) ) ),
    inference(nnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X1,X2,X0] :
      ( ( v2_funct_1(X2)
      <=> sP0(X0,X2,X1) )
      | ~ sP1(X1,X2,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( sP1(X1,X2,X0)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( sP1(X1,X2,X0)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(definition_folding,[],[f41,f51,f50])).

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

fof(f40,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_funct_2)).

fof(f1166,plain,(
    v1_funct_2(k6_partfun1(sK2),sK2,sK2) ),
    inference(resolution,[],[f1150,f146])).

fof(f146,plain,(
    ! [X0] :
      ( ~ v1_funct_1(k6_partfun1(X0))
      | v1_funct_2(k6_partfun1(X0),X0,X0) ) ),
    inference(forward_demodulation,[],[f145,f123])).

fof(f123,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f81,f76])).

fof(f81,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f145,plain,(
    ! [X0] :
      ( v1_funct_2(k6_partfun1(X0),k1_relat_1(k6_partfun1(X0)),X0)
      | ~ v1_funct_1(k6_partfun1(X0)) ) ),
    inference(forward_demodulation,[],[f142,f122])).

fof(f122,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f82,f76])).

fof(f82,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f142,plain,(
    ! [X0] :
      ( ~ v1_funct_1(k6_partfun1(X0))
      | v1_funct_2(k6_partfun1(X0),k1_relat_1(k6_partfun1(X0)),k2_relat_1(k6_partfun1(X0))) ) ),
    inference(resolution,[],[f86,f121])).

fof(f121,plain,(
    ! [X0] : v1_relat_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f77,f76])).

fof(f77,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f73,plain,(
    ~ r2_relset_1(sK2,sK2,sK4,k6_partfun1(sK2)) ),
    inference(cnf_transformation,[],[f55])).

fof(f70,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(cnf_transformation,[],[f55])).

fof(f1367,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_xboole_0 = sK4 ) ),
    inference(trivial_inequality_removal,[],[f1335])).

fof(f1335,plain,(
    ! [X2,X3] :
      ( k1_xboole_0 != k1_xboole_0
      | k1_xboole_0 = sK4
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ) ),
    inference(backward_demodulation,[],[f193,f1323])).

fof(f193,plain,(
    ! [X2,X3] :
      ( k1_xboole_0 != sK2
      | k1_xboole_0 = sK4
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ) ),
    inference(superposition,[],[f136,f190])).

fof(f190,plain,(
    sK2 = k1_relat_1(sK4) ),
    inference(subsumption_resolution,[],[f188,f70])).

fof(f188,plain,
    ( sK2 = k1_relat_1(sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(superposition,[],[f180,f94])).

fof(f180,plain,(
    sK2 = k1_relset_1(sK2,sK2,sK4) ),
    inference(subsumption_resolution,[],[f179,f68])).

fof(f179,plain,
    ( sK2 = k1_relset_1(sK2,sK2,sK4)
    | ~ v1_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f174,f70])).

fof(f174,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | sK2 = k1_relset_1(sK2,sK2,sK4)
    | ~ v1_funct_1(sK4) ),
    inference(resolution,[],[f90,f69])).

fof(f136,plain,(
    ! [X2,X3,X1] :
      ( k1_xboole_0 != k1_relat_1(X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ) ),
    inference(resolution,[],[f83,f93])).

fof(f83,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

fof(f1369,plain,(
    ~ r2_relset_1(k1_xboole_0,k1_xboole_0,sK4,k1_xboole_0) ),
    inference(forward_demodulation,[],[f1328,f119])).

fof(f119,plain,(
    k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    inference(definition_unfolding,[],[f74,f76])).

fof(f74,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

fof(f1328,plain,(
    ~ r2_relset_1(k1_xboole_0,k1_xboole_0,sK4,k6_partfun1(k1_xboole_0)) ),
    inference(backward_demodulation,[],[f73,f1323])).

fof(f133,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(superposition,[],[f80,f119])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_vampire %s %d
% 0.11/0.33  % Computer   : n006.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 15:37:52 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.19/0.47  % (22044)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.19/0.47  % (22052)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.19/0.49  % (22057)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.19/0.49  % (22034)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.19/0.50  % (22049)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.19/0.50  % (22058)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.19/0.51  % (22041)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.19/0.51  % (22040)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.19/0.51  % (22030)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.19/0.51  % (22050)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.19/0.51  % (22045)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.19/0.51  % (22029)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.19/0.51  % (22056)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.19/0.51  % (22033)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.19/0.51  % (22042)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.19/0.52  % (22053)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.19/0.52  % (22032)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.19/0.52  % (22043)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.19/0.52  % (22054)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.19/0.52  % (22035)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.52  % (22031)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.19/0.52  % (22036)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.19/0.53  % (22038)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.19/0.53  % (22037)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.19/0.53  % (22039)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.19/0.53  % (22046)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.19/0.53  % (22051)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.19/0.53  % (22047)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.19/0.53  % (22045)Refutation not found, incomplete strategy% (22045)------------------------------
% 0.19/0.53  % (22045)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.53  % (22045)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.54  
% 0.19/0.54  % (22045)Memory used [KB]: 10746
% 0.19/0.54  % (22045)Time elapsed: 0.123 s
% 0.19/0.54  % (22045)------------------------------
% 0.19/0.54  % (22045)------------------------------
% 0.19/0.54  % (22048)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.19/0.55  % (22055)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 2.24/0.64  % (22070)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.31/0.68  % (22039)Refutation not found, incomplete strategy% (22039)------------------------------
% 2.31/0.68  % (22039)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.31/0.68  % (22039)Termination reason: Refutation not found, incomplete strategy
% 2.31/0.68  
% 2.31/0.68  % (22039)Memory used [KB]: 12025
% 2.31/0.68  % (22039)Time elapsed: 0.292 s
% 2.31/0.68  % (22039)------------------------------
% 2.31/0.68  % (22039)------------------------------
% 2.31/0.70  % (22057)Refutation not found, incomplete strategy% (22057)------------------------------
% 2.31/0.70  % (22057)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.31/0.70  % (22057)Termination reason: Refutation not found, incomplete strategy
% 2.31/0.70  
% 2.31/0.70  % (22057)Memory used [KB]: 12409
% 2.31/0.70  % (22057)Time elapsed: 0.305 s
% 2.31/0.70  % (22057)------------------------------
% 2.31/0.70  % (22057)------------------------------
% 3.12/0.79  % (22029)Refutation not found, incomplete strategy% (22029)------------------------------
% 3.12/0.79  % (22029)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.12/0.79  % (22029)Termination reason: Refutation not found, incomplete strategy
% 3.12/0.79  
% 3.12/0.79  % (22029)Memory used [KB]: 2430
% 3.12/0.79  % (22029)Time elapsed: 0.386 s
% 3.12/0.79  % (22029)------------------------------
% 3.12/0.79  % (22029)------------------------------
% 3.12/0.79  % (22053)Time limit reached!
% 3.12/0.79  % (22053)------------------------------
% 3.12/0.79  % (22053)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.12/0.79  % (22053)Termination reason: Time limit
% 3.12/0.79  
% 3.12/0.79  % (22053)Memory used [KB]: 13432
% 3.12/0.79  % (22053)Time elapsed: 0.401 s
% 3.12/0.79  % (22053)------------------------------
% 3.12/0.79  % (22053)------------------------------
% 3.12/0.81  % (22031)Time limit reached!
% 3.12/0.81  % (22031)------------------------------
% 3.12/0.81  % (22031)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.12/0.82  % (22031)Termination reason: Time limit
% 3.12/0.82  % (22031)Termination phase: Saturation
% 3.12/0.82  
% 3.12/0.82  % (22031)Memory used [KB]: 6652
% 3.12/0.82  % (22031)Time elapsed: 0.400 s
% 3.12/0.82  % (22031)------------------------------
% 3.12/0.82  % (22031)------------------------------
% 3.82/0.87  % (22071)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 3.82/0.88  % (22072)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 3.82/0.89  % (22035)Time limit reached!
% 3.82/0.89  % (22035)------------------------------
% 3.82/0.89  % (22035)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.82/0.89  % (22035)Termination reason: Time limit
% 3.82/0.89  % (22035)Termination phase: Saturation
% 3.82/0.89  
% 3.82/0.89  % (22035)Memory used [KB]: 14072
% 3.82/0.89  % (22035)Time elapsed: 0.500 s
% 3.82/0.89  % (22035)------------------------------
% 3.82/0.89  % (22035)------------------------------
% 4.10/0.90  % (22043)Time limit reached!
% 4.10/0.90  % (22043)------------------------------
% 4.10/0.90  % (22043)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.10/0.90  % (22043)Termination reason: Time limit
% 4.10/0.90  % (22043)Termination phase: Saturation
% 4.10/0.90  
% 4.10/0.90  % (22043)Memory used [KB]: 5245
% 4.10/0.90  % (22043)Time elapsed: 0.500 s
% 4.10/0.90  % (22043)------------------------------
% 4.10/0.90  % (22043)------------------------------
% 4.10/0.90  % (22058)Time limit reached!
% 4.10/0.90  % (22058)------------------------------
% 4.10/0.90  % (22058)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.10/0.90  % (22058)Termination reason: Time limit
% 4.10/0.90  % (22058)Termination phase: Saturation
% 4.10/0.90  
% 4.10/0.90  % (22058)Memory used [KB]: 6268
% 4.10/0.90  % (22058)Time elapsed: 0.500 s
% 4.10/0.90  % (22058)------------------------------
% 4.10/0.90  % (22058)------------------------------
% 4.10/0.93  % (22073)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 4.10/0.93  % (22074)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 4.46/0.98  % (22075)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 4.77/1.02  % (22076)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 4.77/1.02  % (22036)Time limit reached!
% 4.77/1.02  % (22036)------------------------------
% 4.77/1.02  % (22036)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.77/1.03  % (22036)Termination reason: Time limit
% 4.77/1.03  
% 4.77/1.03  % (22036)Memory used [KB]: 5628
% 4.77/1.03  % (22036)Time elapsed: 0.610 s
% 4.77/1.03  % (22036)------------------------------
% 4.77/1.03  % (22036)------------------------------
% 4.77/1.03  % (22077)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 4.77/1.03  % (22078)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 4.77/1.06  % (22051)Refutation found. Thanks to Tanya!
% 4.77/1.06  % SZS status Theorem for theBenchmark
% 4.77/1.06  % SZS output start Proof for theBenchmark
% 4.77/1.06  fof(f1570,plain,(
% 4.77/1.06    $false),
% 4.77/1.06    inference(unit_resulting_resolution,[],[f133,f1542,f127])).
% 4.77/1.06  fof(f127,plain,(
% 4.77/1.06    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.77/1.06    inference(duplicate_literal_removal,[],[f126])).
% 4.77/1.06  fof(f126,plain,(
% 4.77/1.06    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.77/1.06    inference(equality_resolution,[],[f114])).
% 4.77/1.06  fof(f114,plain,(
% 4.77/1.06    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.77/1.06    inference(cnf_transformation,[],[f64])).
% 4.77/1.06  fof(f64,plain,(
% 4.77/1.06    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.77/1.06    inference(nnf_transformation,[],[f43])).
% 4.77/1.06  fof(f43,plain,(
% 4.77/1.06    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.77/1.06    inference(flattening,[],[f42])).
% 4.77/1.06  fof(f42,plain,(
% 4.77/1.06    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 4.77/1.06    inference(ennf_transformation,[],[f12])).
% 4.77/1.06  fof(f12,axiom,(
% 4.77/1.06    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 4.77/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 4.77/1.06  fof(f1542,plain,(
% 4.77/1.06    ~r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 4.77/1.06    inference(backward_demodulation,[],[f1369,f1526])).
% 4.77/1.06  fof(f1526,plain,(
% 4.77/1.06    k1_xboole_0 = sK4),
% 4.77/1.06    inference(resolution,[],[f1367,f1327])).
% 4.77/1.06  fof(f1327,plain,(
% 4.77/1.06    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 4.77/1.06    inference(backward_demodulation,[],[f70,f1323])).
% 4.77/1.06  fof(f1323,plain,(
% 4.77/1.06    k1_xboole_0 = sK2),
% 4.77/1.06    inference(subsumption_resolution,[],[f1320,f70])).
% 4.77/1.06  fof(f1320,plain,(
% 4.77/1.06    k1_xboole_0 = sK2 | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))),
% 4.77/1.06    inference(resolution,[],[f1218,f127])).
% 4.77/1.06  fof(f1218,plain,(
% 4.77/1.06    ~r2_relset_1(sK2,sK2,sK4,sK4) | k1_xboole_0 = sK2),
% 4.77/1.06    inference(superposition,[],[f73,f1215])).
% 4.77/1.06  fof(f1215,plain,(
% 4.77/1.06    k6_partfun1(sK2) = sK4 | k1_xboole_0 = sK2),
% 4.77/1.06    inference(subsumption_resolution,[],[f1212,f67])).
% 4.77/1.06  fof(f67,plain,(
% 4.77/1.06    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))),
% 4.77/1.06    inference(cnf_transformation,[],[f55])).
% 4.77/1.06  fof(f55,plain,(
% 4.77/1.06    (~r2_relset_1(sK2,sK2,sK4,k6_partfun1(sK2)) & v2_funct_1(sK3) & r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3),sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v1_funct_2(sK4,sK2,sK2) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v1_funct_2(sK3,sK2,sK2) & v1_funct_1(sK3)),
% 4.77/1.06    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f25,f54,f53])).
% 4.77/1.06  fof(f53,plain,(
% 4.77/1.06    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k6_partfun1(X0)) & v2_funct_1(X1) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (? [X2] : (~r2_relset_1(sK2,sK2,X2,k6_partfun1(sK2)) & v2_funct_1(sK3) & r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,X2,sK3),sK3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v1_funct_2(X2,sK2,sK2) & v1_funct_1(X2)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v1_funct_2(sK3,sK2,sK2) & v1_funct_1(sK3))),
% 4.77/1.06    introduced(choice_axiom,[])).
% 4.77/1.06  fof(f54,plain,(
% 4.77/1.06    ? [X2] : (~r2_relset_1(sK2,sK2,X2,k6_partfun1(sK2)) & v2_funct_1(sK3) & r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,X2,sK3),sK3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v1_funct_2(X2,sK2,sK2) & v1_funct_1(X2)) => (~r2_relset_1(sK2,sK2,sK4,k6_partfun1(sK2)) & v2_funct_1(sK3) & r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3),sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v1_funct_2(sK4,sK2,sK2) & v1_funct_1(sK4))),
% 4.77/1.06    introduced(choice_axiom,[])).
% 4.77/1.06  fof(f25,plain,(
% 4.77/1.06    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k6_partfun1(X0)) & v2_funct_1(X1) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 4.77/1.06    inference(flattening,[],[f24])).
% 4.77/1.06  fof(f24,plain,(
% 4.77/1.06    ? [X0,X1] : (? [X2] : ((~r2_relset_1(X0,X0,X2,k6_partfun1(X0)) & (v2_funct_1(X1) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 4.77/1.06    inference(ennf_transformation,[],[f23])).
% 4.77/1.06  fof(f23,negated_conjecture,(
% 4.77/1.06    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => ((v2_funct_1(X1) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1)) => r2_relset_1(X0,X0,X2,k6_partfun1(X0)))))),
% 4.77/1.06    inference(negated_conjecture,[],[f22])).
% 4.77/1.06  fof(f22,conjecture,(
% 4.77/1.06    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => ((v2_funct_1(X1) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1)) => r2_relset_1(X0,X0,X2,k6_partfun1(X0)))))),
% 4.77/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_funct_2)).
% 4.77/1.06  fof(f1212,plain,(
% 4.77/1.06    k1_xboole_0 = sK2 | k6_partfun1(sK2) = sK4 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))),
% 4.77/1.06    inference(resolution,[],[f1198,f209])).
% 4.77/1.06  fof(f209,plain,(
% 4.77/1.06    ( ! [X2,X0,X1] : (r2_relset_1(X0,X1,k5_relat_1(k6_partfun1(X0),X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.77/1.06    inference(subsumption_resolution,[],[f208,f80])).
% 4.77/1.06  fof(f80,plain,(
% 4.77/1.06    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 4.77/1.06    inference(cnf_transformation,[],[f14])).
% 4.77/1.06  fof(f14,axiom,(
% 4.77/1.06    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 4.77/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 4.77/1.06  fof(f208,plain,(
% 4.77/1.06    ( ! [X2,X0,X1] : (r2_relset_1(X0,X1,k5_relat_1(k6_partfun1(X0),X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 4.77/1.06    inference(duplicate_literal_removal,[],[f205])).
% 4.77/1.06  fof(f205,plain,(
% 4.77/1.06    ( ! [X2,X0,X1] : (r2_relset_1(X0,X1,k5_relat_1(k6_partfun1(X0),X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 4.77/1.06    inference(superposition,[],[f96,f118])).
% 4.77/1.06  fof(f118,plain,(
% 4.77/1.06    ( ! [X4,X2,X0,X5,X3,X1] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.77/1.06    inference(cnf_transformation,[],[f49])).
% 4.77/1.06  fof(f49,plain,(
% 4.77/1.06    ! [X0,X1,X2,X3,X4,X5] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.77/1.06    inference(flattening,[],[f48])).
% 4.77/1.06  fof(f48,plain,(
% 4.77/1.06    ! [X0,X1,X2,X3,X4,X5] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 4.77/1.06    inference(ennf_transformation,[],[f11])).
% 4.77/1.06  fof(f11,axiom,(
% 4.77/1.06    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 4.77/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_relset_1)).
% 4.77/1.06  fof(f96,plain,(
% 4.77/1.06    ( ! [X2,X0,X1] : (r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.77/1.06    inference(cnf_transformation,[],[f37])).
% 4.77/1.06  fof(f37,plain,(
% 4.77/1.06    ! [X0,X1,X2] : ((r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2) & r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.77/1.06    inference(ennf_transformation,[],[f17])).
% 4.77/1.06  fof(f17,axiom,(
% 4.77/1.06    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2) & r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2)))),
% 4.77/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_2)).
% 4.77/1.06  fof(f1198,plain,(
% 4.77/1.06    ~r2_relset_1(sK2,sK2,k5_relat_1(k6_partfun1(sK2),sK3),sK3) | k1_xboole_0 = sK2 | k6_partfun1(sK2) = sK4),
% 4.77/1.06    inference(subsumption_resolution,[],[f1197,f1150])).
% 4.77/1.06  fof(f1150,plain,(
% 4.77/1.06    v1_funct_1(k6_partfun1(sK2))),
% 4.77/1.06    inference(resolution,[],[f1146,f67])).
% 4.77/1.06  fof(f1146,plain,(
% 4.77/1.06    ( ! [X6,X7] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) | v1_funct_1(k6_partfun1(sK2))) )),
% 4.77/1.06    inference(resolution,[],[f1142,f67])).
% 4.77/1.06  fof(f1142,plain,(
% 4.77/1.06    ( ! [X10,X8,X11,X9] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X8,X9))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X10,X11))) | v1_funct_1(k6_partfun1(sK2))) )),
% 4.77/1.06    inference(resolution,[],[f1137,f67])).
% 4.77/1.06  fof(f1137,plain,(
% 4.77/1.06    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | v1_funct_1(k6_partfun1(sK2))) )),
% 4.77/1.06    inference(subsumption_resolution,[],[f1136,f290])).
% 4.77/1.06  fof(f290,plain,(
% 4.77/1.06    ( ! [X14,X13] : (m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_relat_1(sK3)))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))) )),
% 4.77/1.06    inference(forward_demodulation,[],[f286,f183])).
% 4.77/1.06  fof(f183,plain,(
% 4.77/1.06    sK2 = k1_relat_1(sK3)),
% 4.77/1.06    inference(subsumption_resolution,[],[f181,f67])).
% 4.77/1.06  fof(f181,plain,(
% 4.77/1.06    sK2 = k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))),
% 4.77/1.06    inference(superposition,[],[f178,f94])).
% 4.77/1.06  fof(f94,plain,(
% 4.77/1.06    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.77/1.06    inference(cnf_transformation,[],[f35])).
% 4.77/1.06  fof(f35,plain,(
% 4.77/1.06    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.77/1.06    inference(ennf_transformation,[],[f9])).
% 4.77/1.06  fof(f9,axiom,(
% 4.77/1.06    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 4.77/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 4.77/1.06  fof(f178,plain,(
% 4.77/1.06    sK2 = k1_relset_1(sK2,sK2,sK3)),
% 4.77/1.06    inference(subsumption_resolution,[],[f177,f65])).
% 4.77/1.06  fof(f65,plain,(
% 4.77/1.06    v1_funct_1(sK3)),
% 4.77/1.06    inference(cnf_transformation,[],[f55])).
% 4.77/1.06  fof(f177,plain,(
% 4.77/1.06    sK2 = k1_relset_1(sK2,sK2,sK3) | ~v1_funct_1(sK3)),
% 4.77/1.06    inference(subsumption_resolution,[],[f173,f67])).
% 4.77/1.06  fof(f173,plain,(
% 4.77/1.06    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | sK2 = k1_relset_1(sK2,sK2,sK3) | ~v1_funct_1(sK3)),
% 4.77/1.06    inference(resolution,[],[f90,f66])).
% 4.77/1.06  fof(f66,plain,(
% 4.77/1.06    v1_funct_2(sK3,sK2,sK2)),
% 4.77/1.06    inference(cnf_transformation,[],[f55])).
% 4.77/1.06  fof(f90,plain,(
% 4.77/1.06    ( ! [X0,X1] : (~v1_funct_2(X1,X0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | k1_relset_1(X0,X0,X1) = X0 | ~v1_funct_1(X1)) )),
% 4.77/1.06    inference(cnf_transformation,[],[f33])).
% 4.77/1.06  fof(f33,plain,(
% 4.77/1.06    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 4.77/1.06    inference(flattening,[],[f32])).
% 4.77/1.06  fof(f32,plain,(
% 4.77/1.06    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 4.77/1.06    inference(ennf_transformation,[],[f21])).
% 4.77/1.06  fof(f21,axiom,(
% 4.77/1.06    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k1_relset_1(X0,X0,X1) = X0)),
% 4.77/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_2)).
% 4.77/1.06  fof(f286,plain,(
% 4.77/1.06    ( ! [X14,X13] : (m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))) )),
% 4.77/1.06    inference(resolution,[],[f155,f65])).
% 4.77/1.06  fof(f155,plain,(
% 4.77/1.06    ( ! [X2,X3,X1] : (~v1_funct_1(X1) | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) )),
% 4.77/1.06    inference(resolution,[],[f87,f93])).
% 4.77/1.06  fof(f93,plain,(
% 4.77/1.06    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.77/1.06    inference(cnf_transformation,[],[f34])).
% 4.77/1.06  fof(f34,plain,(
% 4.77/1.06    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.77/1.06    inference(ennf_transformation,[],[f8])).
% 4.77/1.06  fof(f8,axiom,(
% 4.77/1.06    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 4.77/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 4.77/1.06  fof(f87,plain,(
% 4.77/1.06    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))) )),
% 4.77/1.06    inference(cnf_transformation,[],[f29])).
% 4.77/1.06  fof(f29,plain,(
% 4.77/1.06    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 4.77/1.06    inference(flattening,[],[f28])).
% 4.77/1.06  fof(f28,plain,(
% 4.77/1.06    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 4.77/1.06    inference(ennf_transformation,[],[f20])).
% 4.77/1.06  fof(f20,axiom,(
% 4.77/1.06    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 4.77/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).
% 4.77/1.06  fof(f1136,plain,(
% 4.77/1.06    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_relat_1(sK3)))) | v1_funct_1(k6_partfun1(sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))) )),
% 4.77/1.06    inference(forward_demodulation,[],[f1135,f183])).
% 4.77/1.06  fof(f1135,plain,(
% 4.77/1.06    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k6_partfun1(sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))) )),
% 4.77/1.06    inference(subsumption_resolution,[],[f1134,f65])).
% 4.77/1.06  fof(f1134,plain,(
% 4.77/1.06    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k6_partfun1(sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))) )),
% 4.77/1.06    inference(trivial_inequality_removal,[],[f1130])).
% 4.77/1.06  fof(f1130,plain,(
% 4.77/1.06    ( ! [X4,X2,X0,X5,X3,X1] : (k2_relat_1(sK3) != k2_relat_1(sK3) | v1_funct_1(k6_partfun1(sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))) )),
% 4.77/1.06    inference(resolution,[],[f1107,f144])).
% 4.77/1.06  fof(f144,plain,(
% 4.77/1.06    ( ! [X2,X3,X1] : (v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1)) | ~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) )),
% 4.77/1.06    inference(resolution,[],[f86,f93])).
% 4.77/1.06  fof(f86,plain,(
% 4.77/1.06    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))) )),
% 4.77/1.06    inference(cnf_transformation,[],[f29])).
% 4.77/1.06  fof(f1107,plain,(
% 4.77/1.06    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_funct_2(sK3,X3,X2) | k2_relat_1(sK3) != X2 | v1_funct_1(k6_partfun1(sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))) )),
% 4.77/1.06    inference(subsumption_resolution,[],[f1106,f290])).
% 4.77/1.06  fof(f1106,plain,(
% 4.77/1.06    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_relat_1(sK3)))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relat_1(sK3) != X2 | v1_funct_1(k6_partfun1(sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) | ~v1_funct_2(sK3,X3,X2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))) )),
% 4.77/1.06    inference(forward_demodulation,[],[f1105,f183])).
% 4.77/1.06  fof(f1105,plain,(
% 4.77/1.06    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relat_1(sK3) != X2 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))) | v1_funct_1(k6_partfun1(sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) | ~v1_funct_2(sK3,X3,X2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))) )),
% 4.77/1.06    inference(subsumption_resolution,[],[f1104,f65])).
% 4.77/1.06  fof(f1104,plain,(
% 4.77/1.06    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relat_1(sK3) != X2 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))) | v1_funct_1(k6_partfun1(sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) | ~v1_funct_2(sK3,X3,X2) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))) )),
% 4.77/1.06    inference(trivial_inequality_removal,[],[f1100])).
% 4.77/1.06  fof(f1100,plain,(
% 4.77/1.06    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relat_1(sK3) != X2 | k2_relat_1(sK3) != k2_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))) | v1_funct_1(k6_partfun1(sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) | ~v1_funct_2(sK3,X3,X2) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))) )),
% 4.77/1.06    inference(resolution,[],[f930,f144])).
% 4.77/1.06  fof(f930,plain,(
% 4.77/1.06    ( ! [X26,X24,X23,X27,X25,X22] : (~v1_funct_2(sK3,X26,X25) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X22,X23))) | k2_relat_1(sK3) != X24 | k2_relat_1(sK3) != X25 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X26,X25))) | v1_funct_1(k6_partfun1(sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X27,X24))) | ~v1_funct_2(sK3,X27,X24)) )),
% 4.77/1.06    inference(forward_demodulation,[],[f929,f183])).
% 4.77/1.06  fof(f929,plain,(
% 4.77/1.06    ( ! [X26,X24,X23,X27,X25,X22] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X22,X23))) | k2_relat_1(sK3) != X24 | k2_relat_1(sK3) != X25 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X26,X25))) | ~v1_funct_2(sK3,X26,X25) | v1_funct_1(k6_partfun1(k1_relat_1(sK3))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X27,X24))) | ~v1_funct_2(sK3,X27,X24)) )),
% 4.77/1.06    inference(subsumption_resolution,[],[f921,f65])).
% 4.77/1.06  fof(f921,plain,(
% 4.77/1.06    ( ! [X26,X24,X23,X27,X25,X22] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X22,X23))) | ~v1_funct_1(sK3) | k2_relat_1(sK3) != X24 | k2_relat_1(sK3) != X25 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X26,X25))) | ~v1_funct_2(sK3,X26,X25) | v1_funct_1(k6_partfun1(k1_relat_1(sK3))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X27,X24))) | ~v1_funct_2(sK3,X27,X24)) )),
% 4.77/1.06    inference(resolution,[],[f719,f72])).
% 4.77/1.06  fof(f72,plain,(
% 4.77/1.06    v2_funct_1(sK3)),
% 4.77/1.06    inference(cnf_transformation,[],[f55])).
% 4.77/1.06  fof(f719,plain,(
% 4.77/1.06    ( ! [X6,X4,X2,X0,X5,X3,X1] : (~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_1(X2) | k2_relat_1(X2) != X1 | k2_relat_1(X2) != X5 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X6,X5))) | ~v1_funct_2(X2,X6,X5) | v1_funct_1(k6_partfun1(k1_relat_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1)) )),
% 4.77/1.06    inference(duplicate_literal_removal,[],[f718])).
% 4.77/1.06  fof(f718,plain,(
% 4.77/1.06    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_relat_1(X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_1(X2) | ~v2_funct_1(X2) | k2_relat_1(X2) != X5 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X6,X5))) | ~v1_funct_2(X2,X6,X5) | v1_funct_1(k6_partfun1(k1_relat_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.77/1.06    inference(superposition,[],[f513,f95])).
% 4.77/1.06  fof(f95,plain,(
% 4.77/1.06    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.77/1.06    inference(cnf_transformation,[],[f36])).
% 4.77/1.06  fof(f36,plain,(
% 4.77/1.06    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.77/1.06    inference(ennf_transformation,[],[f10])).
% 4.77/1.07  fof(f10,axiom,(
% 4.77/1.07    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 4.77/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 4.77/1.07  fof(f513,plain,(
% 4.77/1.07    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_relset_1(X5,X6,X0) != X6 | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k2_relat_1(X0) != X3 | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X4,X3))) | ~v1_funct_2(X0,X4,X3) | v1_funct_1(k6_partfun1(k1_relat_1(X0))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) | ~v1_funct_2(X0,X5,X6)) )),
% 4.77/1.07    inference(duplicate_literal_removal,[],[f509])).
% 4.77/1.07  fof(f509,plain,(
% 4.77/1.07    ( ! [X6,X4,X2,X0,X5,X3,X1] : (v1_funct_1(k6_partfun1(k1_relat_1(X0))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k2_relat_1(X0) != X3 | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X4,X3))) | ~v1_funct_2(X0,X4,X3) | k2_relset_1(X5,X6,X0) != X6 | ~v2_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) | ~v1_funct_2(X0,X5,X6) | ~v1_funct_1(X0)) )),
% 4.77/1.07    inference(resolution,[],[f502,f100])).
% 4.77/1.07  fof(f100,plain,(
% 4.77/1.07    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 4.77/1.07    inference(cnf_transformation,[],[f39])).
% 4.77/1.07  fof(f39,plain,(
% 4.77/1.07    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 4.77/1.07    inference(flattening,[],[f38])).
% 4.77/1.07  fof(f38,plain,(
% 4.77/1.07    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 4.77/1.07    inference(ennf_transformation,[],[f19])).
% 4.77/1.07  fof(f19,axiom,(
% 4.77/1.07    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 4.77/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).
% 4.77/1.07  fof(f502,plain,(
% 4.77/1.07    ( ! [X6,X4,X2,X0,X5,X3,X1] : (~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X5,X6))) | v1_funct_1(k6_partfun1(k1_relat_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_1(X2) | ~v2_funct_1(X2) | k2_relat_1(X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1)) )),
% 4.77/1.07    inference(duplicate_literal_removal,[],[f501])).
% 5.60/1.08  fof(f501,plain,(
% 5.60/1.08    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_relat_1(X2) != X1 | v1_funct_1(k6_partfun1(k1_relat_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_1(X2) | ~v2_funct_1(X2) | ~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X5,X6))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 5.60/1.08    inference(superposition,[],[f405,f95])).
% 5.60/1.08  fof(f405,plain,(
% 5.60/1.08    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_relset_1(X5,X6,X0) != X6 | v1_funct_1(k6_partfun1(k1_relat_1(X0))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) | ~v1_funct_2(X0,X5,X6)) )),
% 5.60/1.08    inference(duplicate_literal_removal,[],[f404])).
% 5.60/1.08  fof(f404,plain,(
% 5.60/1.08    ( ! [X6,X4,X2,X0,X5,X3,X1] : (~m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_funct_1(k6_partfun1(k1_relat_1(X0))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k2_relset_1(X5,X6,X0) != X6 | ~v2_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) | ~v1_funct_2(X0,X5,X6) | ~v1_funct_1(X0)) )),
% 5.60/1.08    inference(resolution,[],[f307,f98])).
% 5.60/1.08  fof(f98,plain,(
% 5.60/1.08    ( ! [X2,X0,X1] : (v1_funct_1(k2_funct_1(X2)) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 5.60/1.08    inference(cnf_transformation,[],[f39])).
% 5.60/1.08  fof(f307,plain,(
% 5.60/1.08    ( ! [X6,X8,X7,X5,X9] : (~v1_funct_1(k2_funct_1(X5)) | ~m1_subset_1(k2_funct_1(X5),k1_zfmisc_1(k2_zfmisc_1(X6,X7))) | v1_funct_1(k6_partfun1(k1_relat_1(X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X8,X9))) | ~v1_funct_1(X5) | ~v2_funct_1(X5)) )),
% 5.60/1.08    inference(subsumption_resolution,[],[f304,f93])).
% 5.60/1.08  fof(f304,plain,(
% 5.60/1.08    ( ! [X6,X8,X7,X5,X9] : (v1_funct_1(k6_partfun1(k1_relat_1(X5))) | ~m1_subset_1(k2_funct_1(X5),k1_zfmisc_1(k2_zfmisc_1(X6,X7))) | ~v1_funct_1(k2_funct_1(X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X8,X9))) | ~v1_funct_1(X5) | ~v2_funct_1(X5) | ~v1_relat_1(X5)) )),
% 5.60/1.08    inference(duplicate_literal_removal,[],[f302])).
% 5.60/1.08  fof(f302,plain,(
% 5.60/1.08    ( ! [X6,X8,X7,X5,X9] : (v1_funct_1(k6_partfun1(k1_relat_1(X5))) | ~m1_subset_1(k2_funct_1(X5),k1_zfmisc_1(k2_zfmisc_1(X6,X7))) | ~v1_funct_1(k2_funct_1(X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X8,X9))) | ~v1_funct_1(X5) | ~v2_funct_1(X5) | ~v1_funct_1(X5) | ~v1_relat_1(X5)) )),
% 5.60/1.08    inference(superposition,[],[f247,f125])).
% 5.60/1.08  fof(f125,plain,(
% 5.60/1.08    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 5.60/1.08    inference(definition_unfolding,[],[f88,f76])).
% 5.60/1.08  fof(f76,plain,(
% 5.60/1.08    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 5.60/1.08    inference(cnf_transformation,[],[f16])).
% 5.60/1.08  fof(f16,axiom,(
% 5.60/1.08    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 5.60/1.08    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 5.60/1.08  fof(f88,plain,(
% 5.60/1.08    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 5.60/1.08    inference(cnf_transformation,[],[f31])).
% 5.60/1.08  fof(f31,plain,(
% 5.60/1.08    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 5.60/1.08    inference(flattening,[],[f30])).
% 5.60/1.08  fof(f30,plain,(
% 5.60/1.08    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 5.60/1.08    inference(ennf_transformation,[],[f7])).
% 5.60/1.08  fof(f7,axiom,(
% 5.60/1.08    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 5.60/1.08    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).
% 5.60/1.08  fof(f247,plain,(
% 5.60/1.08    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k5_relat_1(X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 5.60/1.08    inference(duplicate_literal_removal,[],[f246])).
% 5.60/1.08  fof(f246,plain,(
% 5.60/1.08    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k5_relat_1(X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 5.60/1.08    inference(superposition,[],[f116,f115])).
% 5.60/1.08  fof(f115,plain,(
% 5.60/1.08    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 5.60/1.08    inference(cnf_transformation,[],[f45])).
% 5.60/1.08  fof(f45,plain,(
% 5.60/1.08    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 5.60/1.08    inference(flattening,[],[f44])).
% 5.60/1.08  fof(f44,plain,(
% 5.60/1.08    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 5.60/1.08    inference(ennf_transformation,[],[f15])).
% 5.60/1.08  fof(f15,axiom,(
% 5.60/1.08    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 5.60/1.08    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 5.60/1.08  fof(f116,plain,(
% 5.60/1.08    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 5.60/1.08    inference(cnf_transformation,[],[f47])).
% 5.60/1.08  fof(f47,plain,(
% 5.60/1.08    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 5.60/1.08    inference(flattening,[],[f46])).
% 5.60/1.08  fof(f46,plain,(
% 5.60/1.08    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 5.60/1.08    inference(ennf_transformation,[],[f13])).
% 5.60/1.08  fof(f13,axiom,(
% 5.60/1.08    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 5.60/1.08    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 5.60/1.08  fof(f1197,plain,(
% 5.60/1.08    k1_xboole_0 = sK2 | ~r2_relset_1(sK2,sK2,k5_relat_1(k6_partfun1(sK2),sK3),sK3) | ~v1_funct_1(k6_partfun1(sK2)) | k6_partfun1(sK2) = sK4),
% 5.60/1.08    inference(subsumption_resolution,[],[f1188,f80])).
% 5.60/1.08  fof(f1188,plain,(
% 5.60/1.08    k1_xboole_0 = sK2 | ~m1_subset_1(k6_partfun1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~r2_relset_1(sK2,sK2,k5_relat_1(k6_partfun1(sK2),sK3),sK3) | ~v1_funct_1(k6_partfun1(sK2)) | k6_partfun1(sK2) = sK4),
% 5.60/1.08    inference(resolution,[],[f1166,f571])).
% 5.60/1.08  fof(f571,plain,(
% 5.60/1.08    ( ! [X0] : (~v1_funct_2(X0,sK2,sK2) | k1_xboole_0 = sK2 | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~r2_relset_1(sK2,sK2,k5_relat_1(X0,sK3),sK3) | ~v1_funct_1(X0) | sK4 = X0) )),
% 5.60/1.08    inference(subsumption_resolution,[],[f570,f65])).
% 5.60/1.08  fof(f570,plain,(
% 5.60/1.08    ( ! [X0] : (~r2_relset_1(sK2,sK2,k5_relat_1(X0,sK3),sK3) | k1_xboole_0 = sK2 | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_2(X0,sK2,sK2) | ~v1_funct_1(X0) | sK4 = X0 | ~v1_funct_1(sK3)) )),
% 5.60/1.08    inference(subsumption_resolution,[],[f565,f67])).
% 5.60/1.08  fof(f565,plain,(
% 5.60/1.08    ( ! [X0] : (~r2_relset_1(sK2,sK2,k5_relat_1(X0,sK3),sK3) | k1_xboole_0 = sK2 | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_2(X0,sK2,sK2) | ~v1_funct_1(X0) | sK4 = X0 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_1(sK3)) )),
% 5.60/1.08    inference(duplicate_literal_removal,[],[f564])).
% 5.60/1.08  fof(f564,plain,(
% 5.60/1.08    ( ! [X0] : (~r2_relset_1(sK2,sK2,k5_relat_1(X0,sK3),sK3) | k1_xboole_0 = sK2 | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_2(X0,sK2,sK2) | ~v1_funct_1(X0) | sK4 = X0 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_1(sK3) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_1(X0)) )),
% 5.60/1.08    inference(superposition,[],[f557,f115])).
% 5.60/1.08  fof(f557,plain,(
% 5.60/1.08    ( ! [X4] : (~r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,X4,sK3),sK3) | k1_xboole_0 = sK2 | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_2(X4,sK2,sK2) | ~v1_funct_1(X4) | sK4 = X4) )),
% 5.60/1.08    inference(forward_demodulation,[],[f556,f268])).
% 5.60/1.08  fof(f268,plain,(
% 5.60/1.08    sK3 = k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3)),
% 5.60/1.08    inference(subsumption_resolution,[],[f267,f68])).
% 5.60/1.08  fof(f68,plain,(
% 5.60/1.08    v1_funct_1(sK4)),
% 5.60/1.08    inference(cnf_transformation,[],[f55])).
% 5.60/1.08  fof(f267,plain,(
% 5.60/1.08    ~v1_funct_1(sK4) | sK3 = k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3)),
% 5.60/1.08    inference(subsumption_resolution,[],[f266,f70])).
% 5.60/1.08  fof(f266,plain,(
% 5.60/1.08    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_1(sK4) | sK3 = k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3)),
% 5.60/1.08    inference(subsumption_resolution,[],[f265,f65])).
% 5.60/1.08  fof(f265,plain,(
% 5.60/1.08    ~v1_funct_1(sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_1(sK4) | sK3 = k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3)),
% 5.60/1.08    inference(subsumption_resolution,[],[f262,f67])).
% 5.60/1.08  fof(f262,plain,(
% 5.60/1.08    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_1(sK4) | sK3 = k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3)),
% 5.60/1.08    inference(resolution,[],[f117,f202])).
% 5.60/1.08  fof(f202,plain,(
% 5.60/1.08    ~m1_subset_1(k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | sK3 = k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3)),
% 5.60/1.08    inference(subsumption_resolution,[],[f195,f67])).
% 5.60/1.08  fof(f195,plain,(
% 5.60/1.08    sK3 = k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~m1_subset_1(k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))),
% 5.60/1.08    inference(resolution,[],[f113,f71])).
% 5.60/1.08  fof(f71,plain,(
% 5.60/1.08    r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3),sK3)),
% 5.60/1.08    inference(cnf_transformation,[],[f55])).
% 5.60/1.08  fof(f113,plain,(
% 5.60/1.08    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 5.60/1.08    inference(cnf_transformation,[],[f64])).
% 5.60/1.08  fof(f117,plain,(
% 5.60/1.08    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 5.60/1.08    inference(cnf_transformation,[],[f47])).
% 5.60/1.08  fof(f556,plain,(
% 5.60/1.08    ( ! [X4] : (~r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,X4,sK3),k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3)) | k1_xboole_0 = sK2 | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_2(X4,sK2,sK2) | ~v1_funct_1(X4) | sK4 = X4) )),
% 5.60/1.08    inference(subsumption_resolution,[],[f555,f68])).
% 5.60/1.08  fof(f555,plain,(
% 5.60/1.08    ( ! [X4] : (~r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,X4,sK3),k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3)) | k1_xboole_0 = sK2 | ~v1_funct_1(sK4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_2(X4,sK2,sK2) | ~v1_funct_1(X4) | sK4 = X4) )),
% 5.60/1.08    inference(subsumption_resolution,[],[f548,f70])).
% 5.60/1.08  fof(f548,plain,(
% 5.60/1.08    ( ! [X4] : (~r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,X4,sK3),k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | k1_xboole_0 = sK2 | ~v1_funct_1(sK4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_2(X4,sK2,sK2) | ~v1_funct_1(X4) | sK4 = X4) )),
% 5.60/1.08    inference(resolution,[],[f542,f69])).
% 5.60/1.08  fof(f69,plain,(
% 5.60/1.08    v1_funct_2(sK4,sK2,sK2)),
% 5.60/1.08    inference(cnf_transformation,[],[f55])).
% 5.60/1.08  fof(f542,plain,(
% 5.60/1.08    ( ! [X6,X7,X5] : (~v1_funct_2(X7,X5,sK2) | ~r2_relset_1(X5,sK2,k1_partfun1(X5,sK2,sK2,sK2,X6,sK3),k1_partfun1(X5,sK2,sK2,sK2,X7,sK3)) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X5,sK2))) | k1_xboole_0 = sK2 | ~v1_funct_1(X7) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X5,sK2))) | ~v1_funct_2(X6,X5,sK2) | ~v1_funct_1(X6) | X6 = X7) )),
% 5.60/1.08    inference(subsumption_resolution,[],[f532,f67])).
% 5.60/1.08  fof(f532,plain,(
% 5.60/1.08    ( ! [X6,X7,X5] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | k1_xboole_0 = sK2 | ~r2_relset_1(X5,sK2,k1_partfun1(X5,sK2,sK2,sK2,X6,sK3),k1_partfun1(X5,sK2,sK2,sK2,X7,sK3)) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X5,sK2))) | ~v1_funct_2(X7,X5,sK2) | ~v1_funct_1(X7) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X5,sK2))) | ~v1_funct_2(X6,X5,sK2) | ~v1_funct_1(X6) | X6 = X7) )),
% 5.60/1.08    inference(duplicate_literal_removal,[],[f530])).
% 5.60/1.08  fof(f530,plain,(
% 5.60/1.08    ( ! [X6,X7,X5] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | k1_xboole_0 = sK2 | ~r2_relset_1(X5,sK2,k1_partfun1(X5,sK2,sK2,sK2,X6,sK3),k1_partfun1(X5,sK2,sK2,sK2,X7,sK3)) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X5,sK2))) | ~v1_funct_2(X7,X5,sK2) | ~v1_funct_1(X7) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X5,sK2))) | ~v1_funct_2(X6,X5,sK2) | ~v1_funct_1(X6) | k1_xboole_0 = sK2 | X6 = X7) )),
% 5.60/1.08    inference(resolution,[],[f528,f66])).
% 5.60/1.08  fof(f528,plain,(
% 5.60/1.08    ( ! [X23,X21,X19,X22,X20] : (~v1_funct_2(sK3,X19,X20) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X19,X20))) | k1_xboole_0 = X20 | ~r2_relset_1(X21,X20,k1_partfun1(X21,X19,X19,X20,X22,sK3),k1_partfun1(X21,X19,X19,X20,X23,sK3)) | ~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X19))) | ~v1_funct_2(X23,X21,X19) | ~v1_funct_1(X23) | ~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X21,X19))) | ~v1_funct_2(X22,X21,X19) | ~v1_funct_1(X22) | k1_xboole_0 = X19 | X22 = X23) )),
% 5.60/1.08    inference(subsumption_resolution,[],[f527,f65])).
% 5.60/1.09  fof(f527,plain,(
% 5.60/1.09    ( ! [X23,X21,X19,X22,X20] : (~v1_funct_2(sK3,X19,X20) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X19,X20))) | k1_xboole_0 = X20 | ~r2_relset_1(X21,X20,k1_partfun1(X21,X19,X19,X20,X22,sK3),k1_partfun1(X21,X19,X19,X20,X23,sK3)) | ~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X19))) | ~v1_funct_2(X23,X21,X19) | ~v1_funct_1(X23) | ~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X21,X19))) | ~v1_funct_2(X22,X21,X19) | ~v1_funct_1(X22) | k1_xboole_0 = X19 | X22 = X23) )),
% 5.60/1.09    inference(resolution,[],[f466,f72])).
% 5.60/1.09  fof(f466,plain,(
% 5.60/1.09    ( ! [X12,X10,X8,X7,X11,X9] : (~v2_funct_1(X7) | ~v1_funct_2(X7,X8,X9) | ~v1_funct_1(X7) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X8,X9))) | k1_xboole_0 = X9 | ~r2_relset_1(X10,X9,k1_partfun1(X10,X8,X8,X9,X11,X7),k1_partfun1(X10,X8,X8,X9,X12,X7)) | ~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X8))) | ~v1_funct_2(X12,X10,X8) | ~v1_funct_1(X12) | ~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X10,X8))) | ~v1_funct_2(X11,X10,X8) | ~v1_funct_1(X11) | k1_xboole_0 = X8 | X11 = X12) )),
% 5.60/1.09    inference(duplicate_literal_removal,[],[f465])).
% 5.60/1.09  fof(f465,plain,(
% 5.60/1.09    ( ! [X12,X10,X8,X7,X11,X9] : (~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X8,X9))) | ~v1_funct_2(X7,X8,X9) | ~v1_funct_1(X7) | ~v2_funct_1(X7) | k1_xboole_0 = X9 | ~r2_relset_1(X10,X9,k1_partfun1(X10,X8,X8,X9,X11,X7),k1_partfun1(X10,X8,X8,X9,X12,X7)) | ~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X8))) | ~v1_funct_2(X12,X10,X8) | ~v1_funct_1(X12) | ~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X10,X8))) | ~v1_funct_2(X11,X10,X8) | ~v1_funct_1(X11) | k1_xboole_0 = X8 | X11 = X12 | ~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X8))) | ~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X10,X8)))) )),
% 5.60/1.09    inference(resolution,[],[f310,f113])).
% 5.60/1.09  fof(f310,plain,(
% 5.60/1.09    ( ! [X4,X2,X0,X5,X3,X1] : (r2_relset_1(X3,X0,X4,X5) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X1,X0,X2) | ~v1_funct_1(X1) | ~v2_funct_1(X1) | k1_xboole_0 = X2 | ~r2_relset_1(X3,X2,k1_partfun1(X3,X0,X0,X2,X4,X1),k1_partfun1(X3,X0,X0,X2,X5,X1)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) | ~v1_funct_2(X5,X3,X0) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) | ~v1_funct_2(X4,X3,X0) | ~v1_funct_1(X4) | k1_xboole_0 = X0) )),
% 5.60/1.09    inference(resolution,[],[f203,f103])).
% 5.60/1.09  fof(f103,plain,(
% 5.60/1.09    ( ! [X6,X2,X0,X8,X7,X1] : (~sP0(X0,X1,X2) | ~r2_relset_1(X6,X2,k1_partfun1(X6,X0,X0,X2,X7,X1),k1_partfun1(X6,X0,X0,X2,X8,X1)) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X0))) | ~v1_funct_2(X8,X6,X0) | ~v1_funct_1(X8) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X6,X0))) | ~v1_funct_2(X7,X6,X0) | ~v1_funct_1(X7) | r2_relset_1(X6,X0,X7,X8)) )),
% 5.60/1.09    inference(cnf_transformation,[],[f63])).
% 5.60/1.09  fof(f63,plain,(
% 5.60/1.09    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((~r2_relset_1(sK5(X0,X1,X2),X0,sK6(X0,X1,X2),sK7(X0,X1,X2)) & r2_relset_1(sK5(X0,X1,X2),X2,k1_partfun1(sK5(X0,X1,X2),X0,X0,X2,sK6(X0,X1,X2),X1),k1_partfun1(sK5(X0,X1,X2),X0,X0,X2,sK7(X0,X1,X2),X1)) & m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(sK5(X0,X1,X2),X0))) & v1_funct_2(sK7(X0,X1,X2),sK5(X0,X1,X2),X0) & v1_funct_1(sK7(X0,X1,X2))) & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(sK5(X0,X1,X2),X0))) & v1_funct_2(sK6(X0,X1,X2),sK5(X0,X1,X2),X0) & v1_funct_1(sK6(X0,X1,X2)))) & (! [X6,X7] : (! [X8] : (r2_relset_1(X6,X0,X7,X8) | ~r2_relset_1(X6,X2,k1_partfun1(X6,X0,X0,X2,X7,X1),k1_partfun1(X6,X0,X0,X2,X8,X1)) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X0))) | ~v1_funct_2(X8,X6,X0) | ~v1_funct_1(X8)) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X6,X0))) | ~v1_funct_2(X7,X6,X0) | ~v1_funct_1(X7)) | ~sP0(X0,X1,X2)))),
% 5.60/1.09    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f60,f62,f61])).
% 5.60/1.09  fof(f61,plain,(
% 5.60/1.09    ! [X2,X1,X0] : (? [X3,X4] : (? [X5] : (~r2_relset_1(X3,X0,X4,X5) & r2_relset_1(X3,X2,k1_partfun1(X3,X0,X0,X2,X4,X1),k1_partfun1(X3,X0,X0,X2,X5,X1)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) & v1_funct_2(X5,X3,X0) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) & v1_funct_2(X4,X3,X0) & v1_funct_1(X4)) => (? [X5] : (~r2_relset_1(sK5(X0,X1,X2),X0,sK6(X0,X1,X2),X5) & r2_relset_1(sK5(X0,X1,X2),X2,k1_partfun1(sK5(X0,X1,X2),X0,X0,X2,sK6(X0,X1,X2),X1),k1_partfun1(sK5(X0,X1,X2),X0,X0,X2,X5,X1)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK5(X0,X1,X2),X0))) & v1_funct_2(X5,sK5(X0,X1,X2),X0) & v1_funct_1(X5)) & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(sK5(X0,X1,X2),X0))) & v1_funct_2(sK6(X0,X1,X2),sK5(X0,X1,X2),X0) & v1_funct_1(sK6(X0,X1,X2))))),
% 5.60/1.09    introduced(choice_axiom,[])).
% 5.60/1.09  fof(f62,plain,(
% 5.60/1.09    ! [X2,X1,X0] : (? [X5] : (~r2_relset_1(sK5(X0,X1,X2),X0,sK6(X0,X1,X2),X5) & r2_relset_1(sK5(X0,X1,X2),X2,k1_partfun1(sK5(X0,X1,X2),X0,X0,X2,sK6(X0,X1,X2),X1),k1_partfun1(sK5(X0,X1,X2),X0,X0,X2,X5,X1)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK5(X0,X1,X2),X0))) & v1_funct_2(X5,sK5(X0,X1,X2),X0) & v1_funct_1(X5)) => (~r2_relset_1(sK5(X0,X1,X2),X0,sK6(X0,X1,X2),sK7(X0,X1,X2)) & r2_relset_1(sK5(X0,X1,X2),X2,k1_partfun1(sK5(X0,X1,X2),X0,X0,X2,sK6(X0,X1,X2),X1),k1_partfun1(sK5(X0,X1,X2),X0,X0,X2,sK7(X0,X1,X2),X1)) & m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(sK5(X0,X1,X2),X0))) & v1_funct_2(sK7(X0,X1,X2),sK5(X0,X1,X2),X0) & v1_funct_1(sK7(X0,X1,X2))))),
% 5.60/1.09    introduced(choice_axiom,[])).
% 5.60/1.09  fof(f60,plain,(
% 5.60/1.09    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3,X4] : (? [X5] : (~r2_relset_1(X3,X0,X4,X5) & r2_relset_1(X3,X2,k1_partfun1(X3,X0,X0,X2,X4,X1),k1_partfun1(X3,X0,X0,X2,X5,X1)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) & v1_funct_2(X5,X3,X0) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) & v1_funct_2(X4,X3,X0) & v1_funct_1(X4))) & (! [X6,X7] : (! [X8] : (r2_relset_1(X6,X0,X7,X8) | ~r2_relset_1(X6,X2,k1_partfun1(X6,X0,X0,X2,X7,X1),k1_partfun1(X6,X0,X0,X2,X8,X1)) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X0))) | ~v1_funct_2(X8,X6,X0) | ~v1_funct_1(X8)) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X6,X0))) | ~v1_funct_2(X7,X6,X0) | ~v1_funct_1(X7)) | ~sP0(X0,X1,X2)))),
% 5.60/1.09    inference(rectify,[],[f59])).
% 5.60/1.09  fof(f59,plain,(
% 5.60/1.09    ! [X0,X2,X1] : ((sP0(X0,X2,X1) | ? [X3,X4] : (? [X5] : (~r2_relset_1(X3,X0,X4,X5) & r2_relset_1(X3,X1,k1_partfun1(X3,X0,X0,X1,X4,X2),k1_partfun1(X3,X0,X0,X1,X5,X2)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) & v1_funct_2(X5,X3,X0) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) & v1_funct_2(X4,X3,X0) & v1_funct_1(X4))) & (! [X3,X4] : (! [X5] : (r2_relset_1(X3,X0,X4,X5) | ~r2_relset_1(X3,X1,k1_partfun1(X3,X0,X0,X1,X4,X2),k1_partfun1(X3,X0,X0,X1,X5,X2)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) | ~v1_funct_2(X5,X3,X0) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) | ~v1_funct_2(X4,X3,X0) | ~v1_funct_1(X4)) | ~sP0(X0,X2,X1)))),
% 5.60/1.09    inference(nnf_transformation,[],[f50])).
% 5.60/1.09  fof(f50,plain,(
% 5.60/1.09    ! [X0,X2,X1] : (sP0(X0,X2,X1) <=> ! [X3,X4] : (! [X5] : (r2_relset_1(X3,X0,X4,X5) | ~r2_relset_1(X3,X1,k1_partfun1(X3,X0,X0,X1,X4,X2),k1_partfun1(X3,X0,X0,X1,X5,X2)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) | ~v1_funct_2(X5,X3,X0) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) | ~v1_funct_2(X4,X3,X0) | ~v1_funct_1(X4)))),
% 5.60/1.09    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 5.60/1.09  fof(f203,plain,(
% 5.60/1.09    ( ! [X2,X0,X1] : (sP0(X1,X2,X0) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X2,X1,X0) | ~v1_funct_1(X2) | ~v2_funct_1(X2) | k1_xboole_0 = X0) )),
% 5.60/1.09    inference(resolution,[],[f112,f101])).
% 5.60/1.09  fof(f101,plain,(
% 5.60/1.09    ( ! [X2,X0,X1] : (~sP1(X0,X1,X2) | ~v2_funct_1(X1) | sP0(X2,X1,X0)) )),
% 5.60/1.09    inference(cnf_transformation,[],[f58])).
% 5.60/1.09  fof(f58,plain,(
% 5.60/1.09    ! [X0,X1,X2] : (((v2_funct_1(X1) | ~sP0(X2,X1,X0)) & (sP0(X2,X1,X0) | ~v2_funct_1(X1))) | ~sP1(X0,X1,X2))),
% 5.60/1.09    inference(rectify,[],[f57])).
% 5.60/1.09  fof(f57,plain,(
% 5.60/1.09    ! [X1,X2,X0] : (((v2_funct_1(X2) | ~sP0(X0,X2,X1)) & (sP0(X0,X2,X1) | ~v2_funct_1(X2))) | ~sP1(X1,X2,X0))),
% 5.60/1.09    inference(nnf_transformation,[],[f51])).
% 5.60/1.09  fof(f51,plain,(
% 5.60/1.09    ! [X1,X2,X0] : ((v2_funct_1(X2) <=> sP0(X0,X2,X1)) | ~sP1(X1,X2,X0))),
% 5.60/1.09    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 5.60/1.09  fof(f112,plain,(
% 5.60/1.09    ( ! [X2,X0,X1] : (sP1(X1,X2,X0) | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 5.60/1.09    inference(cnf_transformation,[],[f52])).
% 5.60/1.09  fof(f52,plain,(
% 5.60/1.09    ! [X0,X1,X2] : (sP1(X1,X2,X0) | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 5.60/1.09    inference(definition_folding,[],[f41,f51,f50])).
% 5.60/1.09  fof(f41,plain,(
% 5.60/1.09    ! [X0,X1,X2] : ((v2_funct_1(X2) <=> ! [X3,X4] : (! [X5] : (r2_relset_1(X3,X0,X4,X5) | ~r2_relset_1(X3,X1,k1_partfun1(X3,X0,X0,X1,X4,X2),k1_partfun1(X3,X0,X0,X1,X5,X2)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) | ~v1_funct_2(X5,X3,X0) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) | ~v1_funct_2(X4,X3,X0) | ~v1_funct_1(X4))) | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 5.60/1.09    inference(flattening,[],[f40])).
% 5.60/1.09  fof(f40,plain,(
% 5.60/1.09    ! [X0,X1,X2] : (((v2_funct_1(X2) <=> ! [X3,X4] : (! [X5] : ((r2_relset_1(X3,X0,X4,X5) | ~r2_relset_1(X3,X1,k1_partfun1(X3,X0,X0,X1,X4,X2),k1_partfun1(X3,X0,X0,X1,X5,X2))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) | ~v1_funct_2(X5,X3,X0) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) | ~v1_funct_2(X4,X3,X0) | ~v1_funct_1(X4)))) | k1_xboole_0 = X1 | k1_xboole_0 = X0) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 5.60/1.09    inference(ennf_transformation,[],[f18])).
% 5.60/1.09  fof(f18,axiom,(
% 5.60/1.09    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ~(~(v2_funct_1(X2) <=> ! [X3,X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) & v1_funct_2(X4,X3,X0) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) & v1_funct_2(X5,X3,X0) & v1_funct_1(X5)) => (r2_relset_1(X3,X1,k1_partfun1(X3,X0,X0,X1,X4,X2),k1_partfun1(X3,X0,X0,X1,X5,X2)) => r2_relset_1(X3,X0,X4,X5))))) & k1_xboole_0 != X1 & k1_xboole_0 != X0))),
% 5.60/1.09    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_funct_2)).
% 5.60/1.09  fof(f1166,plain,(
% 5.60/1.09    v1_funct_2(k6_partfun1(sK2),sK2,sK2)),
% 5.60/1.09    inference(resolution,[],[f1150,f146])).
% 5.60/1.09  fof(f146,plain,(
% 5.60/1.09    ( ! [X0] : (~v1_funct_1(k6_partfun1(X0)) | v1_funct_2(k6_partfun1(X0),X0,X0)) )),
% 5.60/1.09    inference(forward_demodulation,[],[f145,f123])).
% 5.60/1.09  fof(f123,plain,(
% 5.60/1.09    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 5.60/1.09    inference(definition_unfolding,[],[f81,f76])).
% 5.60/1.09  fof(f81,plain,(
% 5.60/1.09    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 5.60/1.09    inference(cnf_transformation,[],[f4])).
% 5.60/1.09  fof(f4,axiom,(
% 5.60/1.09    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 5.60/1.09    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 5.60/1.09  fof(f145,plain,(
% 5.60/1.09    ( ! [X0] : (v1_funct_2(k6_partfun1(X0),k1_relat_1(k6_partfun1(X0)),X0) | ~v1_funct_1(k6_partfun1(X0))) )),
% 5.60/1.09    inference(forward_demodulation,[],[f142,f122])).
% 5.60/1.09  fof(f122,plain,(
% 5.60/1.09    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 5.60/1.09    inference(definition_unfolding,[],[f82,f76])).
% 5.60/1.09  fof(f82,plain,(
% 5.60/1.09    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 5.60/1.09    inference(cnf_transformation,[],[f4])).
% 5.60/1.09  fof(f142,plain,(
% 5.60/1.09    ( ! [X0] : (~v1_funct_1(k6_partfun1(X0)) | v1_funct_2(k6_partfun1(X0),k1_relat_1(k6_partfun1(X0)),k2_relat_1(k6_partfun1(X0)))) )),
% 5.60/1.09    inference(resolution,[],[f86,f121])).
% 5.60/1.09  fof(f121,plain,(
% 5.60/1.09    ( ! [X0] : (v1_relat_1(k6_partfun1(X0))) )),
% 5.60/1.09    inference(definition_unfolding,[],[f77,f76])).
% 5.60/1.09  fof(f77,plain,(
% 5.60/1.09    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 5.60/1.09    inference(cnf_transformation,[],[f6])).
% 5.60/1.09  fof(f6,axiom,(
% 5.60/1.09    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 5.60/1.09    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).
% 5.60/1.09  fof(f73,plain,(
% 5.60/1.09    ~r2_relset_1(sK2,sK2,sK4,k6_partfun1(sK2))),
% 5.60/1.09    inference(cnf_transformation,[],[f55])).
% 5.60/1.09  fof(f70,plain,(
% 5.60/1.09    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))),
% 5.60/1.09    inference(cnf_transformation,[],[f55])).
% 5.60/1.09  fof(f1367,plain,(
% 5.60/1.09    ( ! [X2,X3] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_xboole_0 = sK4) )),
% 5.60/1.09    inference(trivial_inequality_removal,[],[f1335])).
% 5.60/1.09  fof(f1335,plain,(
% 5.60/1.09    ( ! [X2,X3] : (k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK4 | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) )),
% 5.60/1.09    inference(backward_demodulation,[],[f193,f1323])).
% 5.60/1.09  fof(f193,plain,(
% 5.60/1.09    ( ! [X2,X3] : (k1_xboole_0 != sK2 | k1_xboole_0 = sK4 | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) )),
% 5.60/1.09    inference(superposition,[],[f136,f190])).
% 5.60/1.09  fof(f190,plain,(
% 5.60/1.09    sK2 = k1_relat_1(sK4)),
% 5.60/1.09    inference(subsumption_resolution,[],[f188,f70])).
% 5.60/1.09  fof(f188,plain,(
% 5.60/1.09    sK2 = k1_relat_1(sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))),
% 5.60/1.09    inference(superposition,[],[f180,f94])).
% 5.60/1.09  fof(f180,plain,(
% 5.60/1.09    sK2 = k1_relset_1(sK2,sK2,sK4)),
% 5.60/1.09    inference(subsumption_resolution,[],[f179,f68])).
% 5.60/1.09  fof(f179,plain,(
% 5.60/1.09    sK2 = k1_relset_1(sK2,sK2,sK4) | ~v1_funct_1(sK4)),
% 5.60/1.09    inference(subsumption_resolution,[],[f174,f70])).
% 5.60/1.09  fof(f174,plain,(
% 5.60/1.09    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | sK2 = k1_relset_1(sK2,sK2,sK4) | ~v1_funct_1(sK4)),
% 5.60/1.09    inference(resolution,[],[f90,f69])).
% 5.60/1.09  fof(f136,plain,(
% 5.60/1.09    ( ! [X2,X3,X1] : (k1_xboole_0 != k1_relat_1(X1) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) )),
% 5.60/1.09    inference(resolution,[],[f83,f93])).
% 5.60/1.09  fof(f83,plain,(
% 5.60/1.09    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0) | k1_xboole_0 = X0) )),
% 5.60/1.09    inference(cnf_transformation,[],[f27])).
% 5.60/1.09  fof(f27,plain,(
% 5.60/1.09    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 5.60/1.09    inference(flattening,[],[f26])).
% 5.60/1.09  fof(f26,plain,(
% 5.60/1.09    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 5.60/1.09    inference(ennf_transformation,[],[f3])).
% 5.60/1.09  fof(f3,axiom,(
% 5.60/1.09    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 5.60/1.09    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).
% 5.60/1.09  fof(f1369,plain,(
% 5.60/1.09    ~r2_relset_1(k1_xboole_0,k1_xboole_0,sK4,k1_xboole_0)),
% 5.60/1.09    inference(forward_demodulation,[],[f1328,f119])).
% 5.60/1.09  fof(f119,plain,(
% 5.60/1.09    k1_xboole_0 = k6_partfun1(k1_xboole_0)),
% 5.60/1.09    inference(definition_unfolding,[],[f74,f76])).
% 5.60/1.09  fof(f74,plain,(
% 5.60/1.09    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 5.60/1.09    inference(cnf_transformation,[],[f5])).
% 5.60/1.09  fof(f5,axiom,(
% 5.60/1.09    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 5.60/1.09    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).
% 5.60/1.09  fof(f1328,plain,(
% 5.60/1.09    ~r2_relset_1(k1_xboole_0,k1_xboole_0,sK4,k6_partfun1(k1_xboole_0))),
% 5.60/1.09    inference(backward_demodulation,[],[f73,f1323])).
% 5.60/1.09  fof(f133,plain,(
% 5.60/1.09    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 5.60/1.09    inference(superposition,[],[f80,f119])).
% 5.60/1.09  % SZS output end Proof for theBenchmark
% 5.60/1.09  % (22051)------------------------------
% 5.60/1.09  % (22051)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.60/1.09  % (22051)Termination reason: Refutation
% 5.60/1.09  
% 5.60/1.09  % (22051)Memory used [KB]: 11385
% 5.60/1.09  % (22051)Time elapsed: 0.679 s
% 5.60/1.09  % (22051)------------------------------
% 5.60/1.09  % (22051)------------------------------
% 5.60/1.09  % (22028)Success in time 0.737 s
%------------------------------------------------------------------------------
