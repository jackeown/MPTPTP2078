%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1017+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:02 EST 2020

% Result     : Theorem 2.10s
% Output     : Refutation 2.10s
% Verified   : 
% Statistics : Number of formulae       :   44 ( 109 expanded)
%              Number of leaves         :    7 (  27 expanded)
%              Depth                    :   12
%              Number of atoms          :  163 ( 798 expanded)
%              Number of equality atoms :   19 (  89 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5370,plain,(
    $false ),
    inference(subsumption_resolution,[],[f5369,f5173])).

fof(f5173,plain,(
    v1_relat_1(sK158) ),
    inference(resolution,[],[f3373,f3502])).

fof(f3502,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f1644])).

fof(f1644,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1210])).

fof(f1210,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f3373,plain,(
    m1_subset_1(sK158,k1_zfmisc_1(k2_zfmisc_1(sK157,sK157))) ),
    inference(cnf_transformation,[],[f2670])).

fof(f2670,plain,
    ( ( ~ m1_subset_1(sK158,k1_zfmisc_1(k2_zfmisc_1(sK157,sK157)))
      | ~ v3_funct_2(sK158,sK157,sK157)
      | ~ v1_funct_2(sK158,sK157,sK157)
      | ~ v1_funct_1(sK158) )
    & sK157 = k2_relset_1(sK157,sK157,sK158)
    & v2_funct_1(sK158)
    & m1_subset_1(sK158,k1_zfmisc_1(k2_zfmisc_1(sK157,sK157)))
    & v1_funct_2(sK158,sK157,sK157)
    & v1_funct_1(sK158) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK157,sK158])],[f1571,f2669])).

fof(f2669,plain,
    ( ? [X0,X1] :
        ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          | ~ v3_funct_2(X1,X0,X0)
          | ~ v1_funct_2(X1,X0,X0)
          | ~ v1_funct_1(X1) )
        & k2_relset_1(X0,X0,X1) = X0
        & v2_funct_1(X1)
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
   => ( ( ~ m1_subset_1(sK158,k1_zfmisc_1(k2_zfmisc_1(sK157,sK157)))
        | ~ v3_funct_2(sK158,sK157,sK157)
        | ~ v1_funct_2(sK158,sK157,sK157)
        | ~ v1_funct_1(sK158) )
      & sK157 = k2_relset_1(sK157,sK157,sK158)
      & v2_funct_1(sK158)
      & m1_subset_1(sK158,k1_zfmisc_1(k2_zfmisc_1(sK157,sK157)))
      & v1_funct_2(sK158,sK157,sK157)
      & v1_funct_1(sK158) ) ),
    introduced(choice_axiom,[])).

fof(f1571,plain,(
    ? [X0,X1] :
      ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        | ~ v3_funct_2(X1,X0,X0)
        | ~ v1_funct_2(X1,X0,X0)
        | ~ v1_funct_1(X1) )
      & k2_relset_1(X0,X0,X1) = X0
      & v2_funct_1(X1)
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f1570])).

fof(f1570,plain,(
    ? [X0,X1] :
      ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        | ~ v3_funct_2(X1,X0,X0)
        | ~ v1_funct_2(X1,X0,X0)
        | ~ v1_funct_1(X1) )
      & k2_relset_1(X0,X0,X1) = X0
      & v2_funct_1(X1)
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f1556])).

fof(f1556,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ( ( k2_relset_1(X0,X0,X1) = X0
            & v2_funct_1(X1) )
         => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v3_funct_2(X1,X0,X0)
            & v1_funct_2(X1,X0,X0)
            & v1_funct_1(X1) ) ) ) ),
    inference(negated_conjecture,[],[f1555])).

fof(f1555,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( ( k2_relset_1(X0,X0,X1) = X0
          & v2_funct_1(X1) )
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X1,X0,X0)
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_funct_2)).

fof(f5369,plain,(
    ~ v1_relat_1(sK158) ),
    inference(subsumption_resolution,[],[f5368,f5178])).

fof(f5178,plain,(
    v5_relat_1(sK158,sK157) ),
    inference(resolution,[],[f3373,f3616])).

fof(f3616,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f1720])).

fof(f1720,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1211])).

fof(f1211,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f5368,plain,
    ( ~ v5_relat_1(sK158,sK157)
    | ~ v1_relat_1(sK158) ),
    inference(subsumption_resolution,[],[f5321,f5215])).

fof(f5215,plain,(
    ~ v2_funct_2(sK158,sK157) ),
    inference(global_subsumption,[],[f5212,f5214])).

fof(f5214,plain,
    ( ~ v2_funct_2(sK158,sK157)
    | v3_funct_2(sK158,sK157,sK157) ),
    inference(subsumption_resolution,[],[f5213,f3371])).

fof(f3371,plain,(
    v1_funct_1(sK158) ),
    inference(cnf_transformation,[],[f2670])).

fof(f5213,plain,
    ( ~ v2_funct_2(sK158,sK157)
    | ~ v1_funct_1(sK158)
    | v3_funct_2(sK158,sK157,sK157) ),
    inference(subsumption_resolution,[],[f5165,f3374])).

fof(f3374,plain,(
    v2_funct_1(sK158) ),
    inference(cnf_transformation,[],[f2670])).

fof(f5165,plain,
    ( ~ v2_funct_2(sK158,sK157)
    | ~ v2_funct_1(sK158)
    | ~ v1_funct_1(sK158)
    | v3_funct_2(sK158,sK157,sK157) ),
    inference(resolution,[],[f3373,f3382])).

fof(f3382,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v2_funct_2(X2,X1)
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | v3_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f1575])).

fof(f1575,plain,(
    ! [X0,X1,X2] :
      ( ( v3_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v2_funct_2(X2,X1)
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f1574])).

fof(f1574,plain,(
    ! [X0,X1,X2] :
      ( ( v3_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v2_funct_2(X2,X1)
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1472])).

fof(f1472,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) )
       => ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_funct_2)).

fof(f5212,plain,(
    ~ v3_funct_2(sK158,sK157,sK157) ),
    inference(global_subsumption,[],[f3376,f3371,f3372,f3373])).

fof(f3372,plain,(
    v1_funct_2(sK158,sK157,sK157) ),
    inference(cnf_transformation,[],[f2670])).

fof(f3376,plain,
    ( ~ m1_subset_1(sK158,k1_zfmisc_1(k2_zfmisc_1(sK157,sK157)))
    | ~ v3_funct_2(sK158,sK157,sK157)
    | ~ v1_funct_2(sK158,sK157,sK157)
    | ~ v1_funct_1(sK158) ),
    inference(cnf_transformation,[],[f2670])).

fof(f5321,plain,
    ( v2_funct_2(sK158,sK157)
    | ~ v5_relat_1(sK158,sK157)
    | ~ v1_relat_1(sK158) ),
    inference(superposition,[],[f5075,f5257])).

fof(f5257,plain,(
    sK157 = k2_relat_1(sK158) ),
    inference(subsumption_resolution,[],[f5247,f3373])).

fof(f5247,plain,
    ( sK157 = k2_relat_1(sK158)
    | ~ m1_subset_1(sK158,k1_zfmisc_1(k2_zfmisc_1(sK157,sK157))) ),
    inference(superposition,[],[f3375,f3419])).

fof(f3419,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f1592])).

fof(f1592,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1228])).

fof(f1228,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f3375,plain,(
    sK157 = k2_relset_1(sK157,sK157,sK158) ),
    inference(cnf_transformation,[],[f2670])).

fof(f5075,plain,(
    ! [X1] :
      ( v2_funct_2(X1,k2_relat_1(X1))
      | ~ v5_relat_1(X1,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f3606])).

fof(f3606,plain,(
    ! [X0,X1] :
      ( v2_funct_2(X1,X0)
      | k2_relat_1(X1) != X0
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f2786])).

fof(f2786,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f1707])).

fof(f1707,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f1706])).

fof(f1706,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1476])).

fof(f1476,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).
%------------------------------------------------------------------------------
