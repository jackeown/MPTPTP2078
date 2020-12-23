%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:05:49 EST 2020

% Result     : Theorem 2.34s
% Output     : Refutation 2.34s
% Verified   : 
% Statistics : Number of formulae       :  180 (1298 expanded)
%              Number of leaves         :   30 ( 346 expanded)
%              Depth                    :   18
%              Number of atoms          :  558 (6807 expanded)
%              Number of equality atoms :  127 ( 256 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1128,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f222,f377,f411,f427,f435,f1084,f1127])).

fof(f1127,plain,
    ( ~ spl6_1
    | spl6_2
    | ~ spl6_4 ),
    inference(avatar_contradiction_clause,[],[f1126])).

fof(f1126,plain,
    ( $false
    | ~ spl6_1
    | spl6_2
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f1125,f1124])).

fof(f1124,plain,
    ( r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0))
    | ~ spl6_1
    | ~ spl6_4 ),
    inference(forward_demodulation,[],[f1122,f1121])).

fof(f1121,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1))
    | ~ spl6_4 ),
    inference(backward_demodulation,[],[f295,f1120])).

fof(f1120,plain,
    ( k6_partfun1(sK0) = k6_partfun1(k1_relat_1(sK1))
    | ~ spl6_4 ),
    inference(forward_demodulation,[],[f259,f319])).

fof(f319,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK1,k2_funct_1(sK1))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f317])).

fof(f317,plain,
    ( spl6_4
  <=> k6_partfun1(sK0) = k5_relat_1(sK1,k2_funct_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f259,plain,(
    k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f228,f118,f235,f203])).

fof(f203,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f141,f125])).

fof(f125,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f141,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f61])).

fof(f61,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

fof(f235,plain,(
    v2_funct_1(sK1) ),
    inference(unit_resulting_resolution,[],[f118,f120,f121,f187])).

fof(f187,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_1(X2)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f91])).

fof(f91,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f90])).

fof(f90,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).

fof(f121,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f101])).

fof(f101,plain,
    ( ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) )
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v3_funct_2(sK1,sK0,sK0)
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f50,f100])).

fof(f100,plain,
    ( ? [X0,X1] :
        ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
          | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
   => ( ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
        | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v3_funct_2(sK1,sK0,sK0)
      & v1_funct_2(sK1,sK0,sK0)
      & v1_funct_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ? [X0,X1] :
      ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ? [X0,X1] :
      ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f46])).

fof(f46,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X1,X0,X0)
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) ) ) ),
    inference(negated_conjecture,[],[f45])).

fof(f45,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_funct_2)).

fof(f120,plain,(
    v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f101])).

fof(f118,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f101])).

fof(f228,plain,(
    v1_relat_1(sK1) ),
    inference(unit_resulting_resolution,[],[f121,f173])).

fof(f173,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f84])).

fof(f84,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f295,plain,(
    k6_partfun1(k1_relat_1(sK1)) = k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) ),
    inference(forward_demodulation,[],[f291,f259])).

fof(f291,plain,(
    k5_relat_1(sK1,k2_funct_1(sK1)) = k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f118,f121,f252,f249,f195])).

fof(f195,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f99])).

fof(f99,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f98])).

fof(f98,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f41])).

fof(f41,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f249,plain,(
    m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(forward_demodulation,[],[f226,f227])).

fof(f227,plain,(
    k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    inference(unit_resulting_resolution,[],[f118,f119,f120,f121,f158])).

fof(f158,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f42])).

fof(f42,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_2(X0,X1) = k2_funct_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

fof(f119,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f101])).

fof(f226,plain,(
    m1_subset_1(k2_funct_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(unit_resulting_resolution,[],[f118,f119,f120,f121,f162])).

fof(f162,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f39])).

fof(f39,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_2)).

fof(f252,plain,(
    v1_funct_1(k2_funct_1(sK1)) ),
    inference(forward_demodulation,[],[f223,f227])).

fof(f223,plain,(
    v1_funct_1(k2_funct_2(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f118,f119,f120,f121,f159])).

fof(f159,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k2_funct_2(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f77])).

fof(f1122,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0))
    | ~ spl6_1 ),
    inference(backward_demodulation,[],[f216,f227])).

fof(f216,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f215])).

fof(f215,plain,
    ( spl6_1
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f1125,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0))
    | spl6_2 ),
    inference(forward_demodulation,[],[f1123,f297])).

fof(f297,plain,(
    k6_partfun1(sK0) = k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) ),
    inference(forward_demodulation,[],[f288,f265])).

fof(f265,plain,(
    k6_partfun1(sK0) = k5_relat_1(k2_funct_1(sK1),sK1) ),
    inference(backward_demodulation,[],[f260,f264])).

fof(f264,plain,(
    sK0 = k2_relat_1(sK1) ),
    inference(unit_resulting_resolution,[],[f228,f230,f236,f155])).

fof(f155,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = X0
      | ~ v2_funct_2(X1,X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f108])).

fof(f108,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f38])).

fof(f38,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

fof(f236,plain,(
    v2_funct_2(sK1,sK0) ),
    inference(unit_resulting_resolution,[],[f118,f120,f121,f188])).

fof(f188,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_2(X2,X1)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f91])).

fof(f230,plain,(
    v5_relat_1(sK1,sK0) ),
    inference(unit_resulting_resolution,[],[f121,f175])).

fof(f175,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f85])).

fof(f85,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f260,plain,(
    k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(k2_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f228,f118,f235,f202])).

fof(f202,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f142,f125])).

fof(f142,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f288,plain,(
    k5_relat_1(k2_funct_1(sK1),sK1) = k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) ),
    inference(unit_resulting_resolution,[],[f118,f252,f121,f249,f195])).

fof(f1123,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0))
    | spl6_2 ),
    inference(backward_demodulation,[],[f221,f227])).

fof(f221,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
    | spl6_2 ),
    inference(avatar_component_clause,[],[f219])).

fof(f219,plain,
    ( spl6_2
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f1084,plain,
    ( ~ spl6_3
    | spl6_4
    | ~ spl6_8 ),
    inference(avatar_contradiction_clause,[],[f1083])).

fof(f1083,plain,
    ( $false
    | ~ spl6_3
    | spl6_4
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f1072,f567])).

fof(f567,plain,
    ( k5_relat_1(k1_xboole_0,k2_funct_1(k1_xboole_0)) != k6_partfun1(k1_xboole_0)
    | ~ spl6_3
    | spl6_4
    | ~ spl6_8 ),
    inference(forward_demodulation,[],[f512,f315])).

fof(f315,plain,
    ( k1_xboole_0 = sK0
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f313])).

fof(f313,plain,
    ( spl6_3
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f512,plain,
    ( k6_partfun1(sK0) != k5_relat_1(k1_xboole_0,k2_funct_1(k1_xboole_0))
    | spl6_4
    | ~ spl6_8 ),
    inference(forward_demodulation,[],[f318,f376])).

fof(f376,plain,
    ( k1_xboole_0 = sK1
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f374])).

fof(f374,plain,
    ( spl6_8
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f318,plain,
    ( k6_partfun1(sK0) != k5_relat_1(sK1,k2_funct_1(sK1))
    | spl6_4 ),
    inference(avatar_component_clause,[],[f317])).

fof(f1072,plain,
    ( k5_relat_1(k1_xboole_0,k2_funct_1(k1_xboole_0)) = k6_partfun1(k1_xboole_0)
    | ~ spl6_3
    | ~ spl6_8 ),
    inference(backward_demodulation,[],[f457,f1055])).

fof(f1055,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl6_3
    | ~ spl6_8 ),
    inference(unit_resulting_resolution,[],[f123,f1031,f169])).

fof(f169,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

fof(f1031,plain,
    ( v1_xboole_0(k1_relat_1(k1_xboole_0))
    | ~ spl6_3
    | ~ spl6_8 ),
    inference(unit_resulting_resolution,[],[f124,f534,f149])).

fof(f149,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

fof(f534,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ spl6_3
    | ~ spl6_8 ),
    inference(backward_demodulation,[],[f460,f315])).

fof(f460,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),sK0)
    | ~ spl6_8 ),
    inference(backward_demodulation,[],[f263,f376])).

fof(f263,plain,(
    r1_tarski(k1_relat_1(sK1),sK0) ),
    inference(unit_resulting_resolution,[],[f228,f229,f151])).

fof(f151,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f107])).

fof(f107,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f229,plain,(
    v4_relat_1(sK1,sK0) ),
    inference(unit_resulting_resolution,[],[f121,f174])).

fof(f174,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f85])).

fof(f124,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f123,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f457,plain,
    ( k5_relat_1(k1_xboole_0,k2_funct_1(k1_xboole_0)) = k6_partfun1(k1_relat_1(k1_xboole_0))
    | ~ spl6_8 ),
    inference(backward_demodulation,[],[f259,f376])).

fof(f435,plain,
    ( spl6_3
    | spl6_4
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f434,f321,f317,f313])).

fof(f321,plain,
    ( spl6_5
  <=> sK0 = k9_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f434,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK1,k2_funct_1(sK1))
    | k1_xboole_0 = sK0
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f433,f118])).

fof(f433,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK1,k2_funct_1(sK1))
    | k1_xboole_0 = sK0
    | ~ v1_funct_1(sK1)
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f432,f119])).

fof(f432,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK1,k2_funct_1(sK1))
    | k1_xboole_0 = sK0
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f431,f121])).

fof(f431,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK1,k2_funct_1(sK1))
    | k1_xboole_0 = sK0
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f422,f235])).

fof(f422,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK1,k2_funct_1(sK1))
    | k1_xboole_0 = sK0
    | ~ v2_funct_1(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ spl6_5 ),
    inference(trivial_inequality_removal,[],[f419])).

fof(f419,plain,
    ( sK0 != sK0
    | k6_partfun1(sK0) = k5_relat_1(sK1,k2_funct_1(sK1))
    | k1_xboole_0 = sK0
    | ~ v2_funct_1(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ spl6_5 ),
    inference(superposition,[],[f189,f413])).

fof(f413,plain,
    ( sK0 = k2_relset_1(sK0,sK0,sK1)
    | ~ spl6_5 ),
    inference(backward_demodulation,[],[f246,f322])).

fof(f322,plain,
    ( sK0 = k9_relat_1(sK1,sK0)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f321])).

fof(f246,plain,(
    k2_relset_1(sK0,sK0,sK1) = k9_relat_1(sK1,sK0) ),
    inference(forward_demodulation,[],[f231,f237])).

fof(f237,plain,(
    ! [X0] : k7_relset_1(sK0,sK0,sK1,X0) = k9_relat_1(sK1,X0) ),
    inference(unit_resulting_resolution,[],[f121,f192])).

fof(f192,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f95])).

fof(f95,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f231,plain,(
    k2_relset_1(sK0,sK0,sK1) = k7_relset_1(sK0,sK0,sK1,sK0) ),
    inference(unit_resulting_resolution,[],[f121,f176])).

fof(f176,plain,(
    ! [X2,X0,X1] :
      ( k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f86])).

fof(f86,plain,(
    ! [X0,X1,X2] :
      ( ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

fof(f189,plain,(
    ! [X2,X0,X1] :
      ( k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f93])).

fof(f93,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f92])).

fof(f92,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f44])).

fof(f44,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
            & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).

fof(f427,plain,
    ( spl6_1
    | ~ spl6_4 ),
    inference(avatar_contradiction_clause,[],[f426])).

fof(f426,plain,
    ( $false
    | spl6_1
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f423,f130])).

fof(f130,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f40])).

fof(f40,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f423,plain,
    ( ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl6_1
    | ~ spl6_4 ),
    inference(unit_resulting_resolution,[],[f416,f213])).

fof(f213,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(duplicate_literal_removal,[],[f210])).

fof(f210,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f194])).

fof(f194,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f117])).

fof(f117,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f97])).

fof(f97,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f96])).

fof(f96,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f416,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0))
    | spl6_1
    | ~ spl6_4 ),
    inference(backward_demodulation,[],[f261,f414])).

fof(f414,plain,
    ( k6_partfun1(sK0) = k6_partfun1(k1_relat_1(sK1))
    | ~ spl6_4 ),
    inference(backward_demodulation,[],[f259,f319])).

fof(f261,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_partfun1(k1_relat_1(sK1)),k6_partfun1(sK0))
    | spl6_1 ),
    inference(backward_demodulation,[],[f257,f259])).

fof(f257,plain,
    ( ~ r2_relset_1(sK0,sK0,k5_relat_1(sK1,k2_funct_1(sK1)),k6_partfun1(sK0))
    | spl6_1 ),
    inference(subsumption_resolution,[],[f256,f118])).

fof(f256,plain,
    ( ~ r2_relset_1(sK0,sK0,k5_relat_1(sK1,k2_funct_1(sK1)),k6_partfun1(sK0))
    | ~ v1_funct_1(sK1)
    | spl6_1 ),
    inference(subsumption_resolution,[],[f255,f121])).

fof(f255,plain,
    ( ~ r2_relset_1(sK0,sK0,k5_relat_1(sK1,k2_funct_1(sK1)),k6_partfun1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | spl6_1 ),
    inference(subsumption_resolution,[],[f254,f252])).

fof(f254,plain,
    ( ~ r2_relset_1(sK0,sK0,k5_relat_1(sK1,k2_funct_1(sK1)),k6_partfun1(sK0))
    | ~ v1_funct_1(k2_funct_1(sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | spl6_1 ),
    inference(subsumption_resolution,[],[f253,f249])).

fof(f253,plain,
    ( ~ r2_relset_1(sK0,sK0,k5_relat_1(sK1,k2_funct_1(sK1)),k6_partfun1(sK0))
    | ~ m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | spl6_1 ),
    inference(superposition,[],[f248,f195])).

fof(f248,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0))
    | spl6_1 ),
    inference(backward_demodulation,[],[f217,f227])).

fof(f217,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f215])).

fof(f411,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f408,f321])).

fof(f408,plain,(
    sK0 = k9_relat_1(sK1,sK0) ),
    inference(forward_demodulation,[],[f407,f264])).

fof(f407,plain,(
    k2_relat_1(sK1) = k9_relat_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f406,f228])).

fof(f406,plain,
    ( k2_relat_1(sK1) = k9_relat_1(sK1,sK0)
    | ~ v1_relat_1(sK1) ),
    inference(superposition,[],[f150,f262])).

fof(f262,plain,(
    sK1 = k7_relat_1(sK1,sK0) ),
    inference(unit_resulting_resolution,[],[f228,f229,f157])).

fof(f157,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(f150,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f377,plain,
    ( spl6_8
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f372,f313,f374])).

fof(f372,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f359,f228])).

fof(f359,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 = sK1
    | ~ v1_relat_1(sK1) ),
    inference(superposition,[],[f134,f264])).

fof(f134,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

fof(f222,plain,
    ( ~ spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f122,f219,f215])).

fof(f122,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f101])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.11  % Command    : run_vampire %s %d
% 0.10/0.31  % Computer   : n024.cluster.edu
% 0.10/0.31  % Model      : x86_64 x86_64
% 0.10/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.31  % Memory     : 8042.1875MB
% 0.10/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.31  % CPULimit   : 60
% 0.10/0.31  % WCLimit    : 600
% 0.10/0.31  % DateTime   : Tue Dec  1 18:21:36 EST 2020
% 0.10/0.31  % CPUTime    : 
% 0.16/0.43  % (2717)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.16/0.44  % (2727)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.16/0.44  % (2708)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.16/0.45  % (2719)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.16/0.45  % (2715)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.16/0.46  % (2731)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.16/0.46  % (2710)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.16/0.47  % (2707)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.16/0.47  % (2716)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.16/0.47  % (2706)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.16/0.48  % (2709)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.16/0.48  % (2713)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.16/0.48  % (2718)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.16/0.48  % (2721)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.16/0.48  % (2733)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.16/0.48  % (2705)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.16/0.48  % (2712)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.16/0.49  % (2704)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.16/0.49  % (2711)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.16/0.49  % (2728)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.16/0.49  % (2703)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.16/0.50  % (2729)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.16/0.50  % (2725)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.16/0.50  % (2724)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.16/0.50  % (2730)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.16/0.51  % (2722)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.16/0.51  % (2732)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.16/0.51  % (2723)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.16/0.52  % (2726)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.16/0.52  % (2720)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 2.34/0.64  % (2730)Refutation found. Thanks to Tanya!
% 2.34/0.64  % SZS status Theorem for theBenchmark
% 2.34/0.65  % SZS output start Proof for theBenchmark
% 2.34/0.65  fof(f1128,plain,(
% 2.34/0.65    $false),
% 2.34/0.65    inference(avatar_sat_refutation,[],[f222,f377,f411,f427,f435,f1084,f1127])).
% 2.34/0.65  fof(f1127,plain,(
% 2.34/0.65    ~spl6_1 | spl6_2 | ~spl6_4),
% 2.34/0.65    inference(avatar_contradiction_clause,[],[f1126])).
% 2.34/0.65  fof(f1126,plain,(
% 2.34/0.65    $false | (~spl6_1 | spl6_2 | ~spl6_4)),
% 2.34/0.65    inference(subsumption_resolution,[],[f1125,f1124])).
% 2.34/0.65  fof(f1124,plain,(
% 2.34/0.65    r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) | (~spl6_1 | ~spl6_4)),
% 2.34/0.65    inference(forward_demodulation,[],[f1122,f1121])).
% 2.34/0.65  fof(f1121,plain,(
% 2.34/0.65    k6_partfun1(sK0) = k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) | ~spl6_4),
% 2.34/0.65    inference(backward_demodulation,[],[f295,f1120])).
% 2.34/0.65  fof(f1120,plain,(
% 2.34/0.65    k6_partfun1(sK0) = k6_partfun1(k1_relat_1(sK1)) | ~spl6_4),
% 2.34/0.65    inference(forward_demodulation,[],[f259,f319])).
% 2.34/0.65  fof(f319,plain,(
% 2.34/0.65    k6_partfun1(sK0) = k5_relat_1(sK1,k2_funct_1(sK1)) | ~spl6_4),
% 2.34/0.65    inference(avatar_component_clause,[],[f317])).
% 2.34/0.65  fof(f317,plain,(
% 2.34/0.65    spl6_4 <=> k6_partfun1(sK0) = k5_relat_1(sK1,k2_funct_1(sK1))),
% 2.34/0.65    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 2.34/0.65  fof(f259,plain,(
% 2.34/0.65    k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1))),
% 2.34/0.65    inference(unit_resulting_resolution,[],[f228,f118,f235,f203])).
% 2.34/0.65  fof(f203,plain,(
% 2.34/0.65    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.34/0.65    inference(definition_unfolding,[],[f141,f125])).
% 2.34/0.65  fof(f125,plain,(
% 2.34/0.65    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 2.34/0.65    inference(cnf_transformation,[],[f43])).
% 2.34/0.65  fof(f43,axiom,(
% 2.34/0.65    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 2.34/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 2.34/0.65  fof(f141,plain,(
% 2.34/0.65    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.34/0.65    inference(cnf_transformation,[],[f62])).
% 2.34/0.65  fof(f62,plain,(
% 2.34/0.65    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.34/0.65    inference(flattening,[],[f61])).
% 2.34/0.65  fof(f61,plain,(
% 2.34/0.65    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.34/0.65    inference(ennf_transformation,[],[f27])).
% 2.34/0.65  fof(f27,axiom,(
% 2.34/0.65    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 2.34/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).
% 2.34/0.65  fof(f235,plain,(
% 2.34/0.65    v2_funct_1(sK1)),
% 2.34/0.65    inference(unit_resulting_resolution,[],[f118,f120,f121,f187])).
% 2.34/0.65  fof(f187,plain,(
% 2.34/0.65    ( ! [X2,X0,X1] : (v2_funct_1(X2) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.34/0.65    inference(cnf_transformation,[],[f91])).
% 2.34/0.65  fof(f91,plain,(
% 2.34/0.65    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.34/0.65    inference(flattening,[],[f90])).
% 2.34/0.65  fof(f90,plain,(
% 2.34/0.65    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.34/0.65    inference(ennf_transformation,[],[f36])).
% 2.34/0.65  fof(f36,axiom,(
% 2.34/0.65    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 2.34/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).
% 2.34/0.65  fof(f121,plain,(
% 2.34/0.65    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.34/0.65    inference(cnf_transformation,[],[f101])).
% 2.34/0.65  fof(f101,plain,(
% 2.34/0.65    (~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 2.34/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f50,f100])).
% 2.34/0.65  fof(f100,plain,(
% 2.34/0.65    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ((~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 2.34/0.65    introduced(choice_axiom,[])).
% 2.34/0.65  fof(f50,plain,(
% 2.34/0.65    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 2.34/0.65    inference(flattening,[],[f49])).
% 2.34/0.65  fof(f49,plain,(
% 2.34/0.65    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 2.34/0.65    inference(ennf_transformation,[],[f46])).
% 2.34/0.65  fof(f46,negated_conjecture,(
% 2.34/0.65    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 2.34/0.65    inference(negated_conjecture,[],[f45])).
% 2.34/0.65  fof(f45,conjecture,(
% 2.34/0.65    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 2.34/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_funct_2)).
% 2.34/0.65  fof(f120,plain,(
% 2.34/0.65    v3_funct_2(sK1,sK0,sK0)),
% 2.34/0.65    inference(cnf_transformation,[],[f101])).
% 2.34/0.65  fof(f118,plain,(
% 2.34/0.65    v1_funct_1(sK1)),
% 2.34/0.65    inference(cnf_transformation,[],[f101])).
% 2.34/0.65  fof(f228,plain,(
% 2.34/0.65    v1_relat_1(sK1)),
% 2.34/0.65    inference(unit_resulting_resolution,[],[f121,f173])).
% 2.34/0.65  fof(f173,plain,(
% 2.34/0.65    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.34/0.65    inference(cnf_transformation,[],[f84])).
% 2.34/0.65  fof(f84,plain,(
% 2.34/0.65    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.34/0.65    inference(ennf_transformation,[],[f29])).
% 2.34/0.65  fof(f29,axiom,(
% 2.34/0.65    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.34/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 2.34/0.65  fof(f295,plain,(
% 2.34/0.65    k6_partfun1(k1_relat_1(sK1)) = k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1))),
% 2.34/0.65    inference(forward_demodulation,[],[f291,f259])).
% 2.34/0.65  fof(f291,plain,(
% 2.34/0.65    k5_relat_1(sK1,k2_funct_1(sK1)) = k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1))),
% 2.34/0.65    inference(unit_resulting_resolution,[],[f118,f121,f252,f249,f195])).
% 2.34/0.65  fof(f195,plain,(
% 2.34/0.65    ( ! [X4,X2,X0,X5,X3,X1] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 2.34/0.65    inference(cnf_transformation,[],[f99])).
% 2.34/0.65  fof(f99,plain,(
% 2.34/0.65    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.34/0.65    inference(flattening,[],[f98])).
% 2.34/0.65  fof(f98,plain,(
% 2.34/0.65    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.34/0.65    inference(ennf_transformation,[],[f41])).
% 2.34/0.65  fof(f41,axiom,(
% 2.34/0.65    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 2.34/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 2.34/0.65  fof(f249,plain,(
% 2.34/0.65    m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.34/0.65    inference(forward_demodulation,[],[f226,f227])).
% 2.34/0.65  fof(f227,plain,(
% 2.34/0.65    k2_funct_2(sK0,sK1) = k2_funct_1(sK1)),
% 2.34/0.65    inference(unit_resulting_resolution,[],[f118,f119,f120,f121,f158])).
% 2.34/0.65  fof(f158,plain,(
% 2.34/0.65    ( ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 2.34/0.65    inference(cnf_transformation,[],[f75])).
% 2.34/0.65  fof(f75,plain,(
% 2.34/0.65    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 2.34/0.65    inference(flattening,[],[f74])).
% 2.34/0.65  fof(f74,plain,(
% 2.34/0.65    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 2.34/0.65    inference(ennf_transformation,[],[f42])).
% 2.34/0.65  fof(f42,axiom,(
% 2.34/0.65    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_2(X0,X1) = k2_funct_1(X1))),
% 2.34/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).
% 2.34/0.65  fof(f119,plain,(
% 2.34/0.65    v1_funct_2(sK1,sK0,sK0)),
% 2.34/0.65    inference(cnf_transformation,[],[f101])).
% 2.34/0.65  fof(f226,plain,(
% 2.34/0.65    m1_subset_1(k2_funct_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.34/0.65    inference(unit_resulting_resolution,[],[f118,f119,f120,f121,f162])).
% 2.34/0.65  fof(f162,plain,(
% 2.34/0.65    ( ! [X0,X1] : (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 2.34/0.65    inference(cnf_transformation,[],[f77])).
% 2.34/0.65  fof(f77,plain,(
% 2.34/0.65    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 2.34/0.65    inference(flattening,[],[f76])).
% 2.34/0.65  fof(f76,plain,(
% 2.34/0.65    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 2.34/0.65    inference(ennf_transformation,[],[f39])).
% 2.34/0.65  fof(f39,axiom,(
% 2.34/0.65    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))))),
% 2.34/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_2)).
% 2.34/0.65  fof(f252,plain,(
% 2.34/0.65    v1_funct_1(k2_funct_1(sK1))),
% 2.34/0.65    inference(forward_demodulation,[],[f223,f227])).
% 2.34/0.65  fof(f223,plain,(
% 2.34/0.65    v1_funct_1(k2_funct_2(sK0,sK1))),
% 2.34/0.65    inference(unit_resulting_resolution,[],[f118,f119,f120,f121,f159])).
% 2.34/0.65  fof(f159,plain,(
% 2.34/0.65    ( ! [X0,X1] : (v1_funct_1(k2_funct_2(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 2.34/0.65    inference(cnf_transformation,[],[f77])).
% 2.34/0.65  fof(f1122,plain,(
% 2.34/0.65    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) | ~spl6_1),
% 2.34/0.65    inference(backward_demodulation,[],[f216,f227])).
% 2.34/0.65  fof(f216,plain,(
% 2.34/0.65    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) | ~spl6_1),
% 2.34/0.65    inference(avatar_component_clause,[],[f215])).
% 2.34/0.65  fof(f215,plain,(
% 2.34/0.65    spl6_1 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))),
% 2.34/0.65    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 2.34/0.65  fof(f1125,plain,(
% 2.34/0.65    ~r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) | spl6_2),
% 2.34/0.65    inference(forward_demodulation,[],[f1123,f297])).
% 2.34/0.65  fof(f297,plain,(
% 2.34/0.65    k6_partfun1(sK0) = k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1)),
% 2.34/0.65    inference(forward_demodulation,[],[f288,f265])).
% 2.34/0.65  fof(f265,plain,(
% 2.34/0.65    k6_partfun1(sK0) = k5_relat_1(k2_funct_1(sK1),sK1)),
% 2.34/0.65    inference(backward_demodulation,[],[f260,f264])).
% 2.34/0.65  fof(f264,plain,(
% 2.34/0.65    sK0 = k2_relat_1(sK1)),
% 2.34/0.65    inference(unit_resulting_resolution,[],[f228,f230,f236,f155])).
% 2.34/0.65  fof(f155,plain,(
% 2.34/0.65    ( ! [X0,X1] : (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.34/0.65    inference(cnf_transformation,[],[f108])).
% 2.34/0.65  fof(f108,plain,(
% 2.34/0.65    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.34/0.65    inference(nnf_transformation,[],[f71])).
% 2.34/0.65  fof(f71,plain,(
% 2.34/0.65    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.34/0.65    inference(flattening,[],[f70])).
% 2.34/0.65  fof(f70,plain,(
% 2.34/0.65    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.34/0.65    inference(ennf_transformation,[],[f38])).
% 2.34/0.65  fof(f38,axiom,(
% 2.34/0.65    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 2.34/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).
% 2.34/0.65  fof(f236,plain,(
% 2.34/0.65    v2_funct_2(sK1,sK0)),
% 2.34/0.65    inference(unit_resulting_resolution,[],[f118,f120,f121,f188])).
% 2.34/0.65  fof(f188,plain,(
% 2.34/0.65    ( ! [X2,X0,X1] : (v2_funct_2(X2,X1) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.34/0.65    inference(cnf_transformation,[],[f91])).
% 2.34/0.65  fof(f230,plain,(
% 2.34/0.65    v5_relat_1(sK1,sK0)),
% 2.34/0.65    inference(unit_resulting_resolution,[],[f121,f175])).
% 2.34/0.65  fof(f175,plain,(
% 2.34/0.65    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.34/0.65    inference(cnf_transformation,[],[f85])).
% 2.34/0.65  fof(f85,plain,(
% 2.34/0.65    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.34/0.65    inference(ennf_transformation,[],[f30])).
% 2.34/0.65  fof(f30,axiom,(
% 2.34/0.65    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.34/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 2.34/0.65  fof(f260,plain,(
% 2.34/0.65    k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(k2_relat_1(sK1))),
% 2.34/0.65    inference(unit_resulting_resolution,[],[f228,f118,f235,f202])).
% 2.34/0.65  fof(f202,plain,(
% 2.34/0.65    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.34/0.65    inference(definition_unfolding,[],[f142,f125])).
% 2.34/0.65  fof(f142,plain,(
% 2.34/0.65    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.34/0.65    inference(cnf_transformation,[],[f62])).
% 2.34/0.65  fof(f288,plain,(
% 2.34/0.65    k5_relat_1(k2_funct_1(sK1),sK1) = k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1)),
% 2.34/0.65    inference(unit_resulting_resolution,[],[f118,f252,f121,f249,f195])).
% 2.34/0.65  fof(f1123,plain,(
% 2.34/0.65    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0)) | spl6_2),
% 2.34/0.65    inference(backward_demodulation,[],[f221,f227])).
% 2.34/0.65  fof(f221,plain,(
% 2.34/0.65    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | spl6_2),
% 2.34/0.65    inference(avatar_component_clause,[],[f219])).
% 2.34/0.65  fof(f219,plain,(
% 2.34/0.65    spl6_2 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))),
% 2.34/0.65    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 2.34/0.65  fof(f1084,plain,(
% 2.34/0.65    ~spl6_3 | spl6_4 | ~spl6_8),
% 2.34/0.65    inference(avatar_contradiction_clause,[],[f1083])).
% 2.34/0.65  fof(f1083,plain,(
% 2.34/0.65    $false | (~spl6_3 | spl6_4 | ~spl6_8)),
% 2.34/0.65    inference(subsumption_resolution,[],[f1072,f567])).
% 2.34/0.65  fof(f567,plain,(
% 2.34/0.65    k5_relat_1(k1_xboole_0,k2_funct_1(k1_xboole_0)) != k6_partfun1(k1_xboole_0) | (~spl6_3 | spl6_4 | ~spl6_8)),
% 2.34/0.65    inference(forward_demodulation,[],[f512,f315])).
% 2.34/0.65  fof(f315,plain,(
% 2.34/0.65    k1_xboole_0 = sK0 | ~spl6_3),
% 2.34/0.65    inference(avatar_component_clause,[],[f313])).
% 2.34/0.65  fof(f313,plain,(
% 2.34/0.65    spl6_3 <=> k1_xboole_0 = sK0),
% 2.34/0.65    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 2.34/0.65  fof(f512,plain,(
% 2.34/0.65    k6_partfun1(sK0) != k5_relat_1(k1_xboole_0,k2_funct_1(k1_xboole_0)) | (spl6_4 | ~spl6_8)),
% 2.34/0.65    inference(forward_demodulation,[],[f318,f376])).
% 2.34/0.65  fof(f376,plain,(
% 2.34/0.65    k1_xboole_0 = sK1 | ~spl6_8),
% 2.34/0.65    inference(avatar_component_clause,[],[f374])).
% 2.34/0.65  fof(f374,plain,(
% 2.34/0.65    spl6_8 <=> k1_xboole_0 = sK1),
% 2.34/0.65    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 2.34/0.65  fof(f318,plain,(
% 2.34/0.65    k6_partfun1(sK0) != k5_relat_1(sK1,k2_funct_1(sK1)) | spl6_4),
% 2.34/0.65    inference(avatar_component_clause,[],[f317])).
% 2.34/0.65  fof(f1072,plain,(
% 2.34/0.65    k5_relat_1(k1_xboole_0,k2_funct_1(k1_xboole_0)) = k6_partfun1(k1_xboole_0) | (~spl6_3 | ~spl6_8)),
% 2.34/0.65    inference(backward_demodulation,[],[f457,f1055])).
% 2.34/0.65  fof(f1055,plain,(
% 2.34/0.65    k1_xboole_0 = k1_relat_1(k1_xboole_0) | (~spl6_3 | ~spl6_8)),
% 2.34/0.65    inference(unit_resulting_resolution,[],[f123,f1031,f169])).
% 2.34/0.65  fof(f169,plain,(
% 2.34/0.65    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 2.34/0.65    inference(cnf_transformation,[],[f81])).
% 2.34/0.65  fof(f81,plain,(
% 2.34/0.65    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 2.34/0.65    inference(ennf_transformation,[],[f10])).
% 2.34/0.65  fof(f10,axiom,(
% 2.34/0.65    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 2.34/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).
% 2.34/0.65  fof(f1031,plain,(
% 2.34/0.65    v1_xboole_0(k1_relat_1(k1_xboole_0)) | (~spl6_3 | ~spl6_8)),
% 2.34/0.65    inference(unit_resulting_resolution,[],[f124,f534,f149])).
% 2.34/0.65  fof(f149,plain,(
% 2.34/0.65    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)) )),
% 2.34/0.65    inference(cnf_transformation,[],[f65])).
% 2.34/0.65  fof(f65,plain,(
% 2.34/0.65    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 2.34/0.65    inference(flattening,[],[f64])).
% 2.34/0.65  fof(f64,plain,(
% 2.34/0.65    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 2.34/0.65    inference(ennf_transformation,[],[f8])).
% 2.34/0.65  fof(f8,axiom,(
% 2.34/0.65    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 2.34/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).
% 2.34/0.65  fof(f534,plain,(
% 2.34/0.65    r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0) | (~spl6_3 | ~spl6_8)),
% 2.34/0.65    inference(backward_demodulation,[],[f460,f315])).
% 2.34/0.65  fof(f460,plain,(
% 2.34/0.65    r1_tarski(k1_relat_1(k1_xboole_0),sK0) | ~spl6_8),
% 2.34/0.65    inference(backward_demodulation,[],[f263,f376])).
% 2.34/0.65  fof(f263,plain,(
% 2.34/0.65    r1_tarski(k1_relat_1(sK1),sK0)),
% 2.34/0.65    inference(unit_resulting_resolution,[],[f228,f229,f151])).
% 2.34/0.65  fof(f151,plain,(
% 2.34/0.65    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.34/0.65    inference(cnf_transformation,[],[f107])).
% 2.34/0.65  fof(f107,plain,(
% 2.34/0.65    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.34/0.65    inference(nnf_transformation,[],[f67])).
% 2.34/0.65  fof(f67,plain,(
% 2.34/0.65    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.34/0.65    inference(ennf_transformation,[],[f17])).
% 2.34/0.65  fof(f17,axiom,(
% 2.34/0.65    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 2.34/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 2.34/0.65  fof(f229,plain,(
% 2.34/0.65    v4_relat_1(sK1,sK0)),
% 2.34/0.65    inference(unit_resulting_resolution,[],[f121,f174])).
% 2.34/0.65  fof(f174,plain,(
% 2.34/0.65    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.34/0.65    inference(cnf_transformation,[],[f85])).
% 2.34/0.65  fof(f124,plain,(
% 2.34/0.65    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 2.34/0.65    inference(cnf_transformation,[],[f7])).
% 2.34/0.65  fof(f7,axiom,(
% 2.34/0.65    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 2.34/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 2.34/0.65  fof(f123,plain,(
% 2.34/0.65    v1_xboole_0(k1_xboole_0)),
% 2.34/0.65    inference(cnf_transformation,[],[f4])).
% 2.34/0.65  fof(f4,axiom,(
% 2.34/0.65    v1_xboole_0(k1_xboole_0)),
% 2.34/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 2.34/0.65  fof(f457,plain,(
% 2.34/0.65    k5_relat_1(k1_xboole_0,k2_funct_1(k1_xboole_0)) = k6_partfun1(k1_relat_1(k1_xboole_0)) | ~spl6_8),
% 2.34/0.65    inference(backward_demodulation,[],[f259,f376])).
% 2.34/0.65  fof(f435,plain,(
% 2.34/0.65    spl6_3 | spl6_4 | ~spl6_5),
% 2.34/0.65    inference(avatar_split_clause,[],[f434,f321,f317,f313])).
% 2.34/0.65  fof(f321,plain,(
% 2.34/0.65    spl6_5 <=> sK0 = k9_relat_1(sK1,sK0)),
% 2.34/0.65    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 2.34/0.65  fof(f434,plain,(
% 2.34/0.65    k6_partfun1(sK0) = k5_relat_1(sK1,k2_funct_1(sK1)) | k1_xboole_0 = sK0 | ~spl6_5),
% 2.34/0.65    inference(subsumption_resolution,[],[f433,f118])).
% 2.34/0.65  fof(f433,plain,(
% 2.34/0.65    k6_partfun1(sK0) = k5_relat_1(sK1,k2_funct_1(sK1)) | k1_xboole_0 = sK0 | ~v1_funct_1(sK1) | ~spl6_5),
% 2.34/0.65    inference(subsumption_resolution,[],[f432,f119])).
% 2.34/0.65  fof(f432,plain,(
% 2.34/0.65    k6_partfun1(sK0) = k5_relat_1(sK1,k2_funct_1(sK1)) | k1_xboole_0 = sK0 | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | ~spl6_5),
% 2.34/0.65    inference(subsumption_resolution,[],[f431,f121])).
% 2.34/0.65  fof(f431,plain,(
% 2.34/0.65    k6_partfun1(sK0) = k5_relat_1(sK1,k2_funct_1(sK1)) | k1_xboole_0 = sK0 | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | ~spl6_5),
% 2.34/0.65    inference(subsumption_resolution,[],[f422,f235])).
% 2.34/0.65  fof(f422,plain,(
% 2.34/0.65    k6_partfun1(sK0) = k5_relat_1(sK1,k2_funct_1(sK1)) | k1_xboole_0 = sK0 | ~v2_funct_1(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | ~spl6_5),
% 2.34/0.65    inference(trivial_inequality_removal,[],[f419])).
% 2.34/0.65  fof(f419,plain,(
% 2.34/0.65    sK0 != sK0 | k6_partfun1(sK0) = k5_relat_1(sK1,k2_funct_1(sK1)) | k1_xboole_0 = sK0 | ~v2_funct_1(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | ~spl6_5),
% 2.34/0.65    inference(superposition,[],[f189,f413])).
% 2.34/0.65  fof(f413,plain,(
% 2.34/0.65    sK0 = k2_relset_1(sK0,sK0,sK1) | ~spl6_5),
% 2.34/0.65    inference(backward_demodulation,[],[f246,f322])).
% 2.34/0.65  fof(f322,plain,(
% 2.34/0.65    sK0 = k9_relat_1(sK1,sK0) | ~spl6_5),
% 2.34/0.65    inference(avatar_component_clause,[],[f321])).
% 2.34/0.65  fof(f246,plain,(
% 2.34/0.65    k2_relset_1(sK0,sK0,sK1) = k9_relat_1(sK1,sK0)),
% 2.34/0.65    inference(forward_demodulation,[],[f231,f237])).
% 2.34/0.65  fof(f237,plain,(
% 2.34/0.65    ( ! [X0] : (k7_relset_1(sK0,sK0,sK1,X0) = k9_relat_1(sK1,X0)) )),
% 2.34/0.65    inference(unit_resulting_resolution,[],[f121,f192])).
% 2.34/0.65  fof(f192,plain,(
% 2.34/0.65    ( ! [X2,X0,X3,X1] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.34/0.65    inference(cnf_transformation,[],[f95])).
% 2.34/0.65  fof(f95,plain,(
% 2.34/0.65    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.34/0.65    inference(ennf_transformation,[],[f31])).
% 2.34/0.65  fof(f31,axiom,(
% 2.34/0.65    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 2.34/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 2.34/0.65  fof(f231,plain,(
% 2.34/0.65    k2_relset_1(sK0,sK0,sK1) = k7_relset_1(sK0,sK0,sK1,sK0)),
% 2.34/0.65    inference(unit_resulting_resolution,[],[f121,f176])).
% 2.34/0.65  fof(f176,plain,(
% 2.34/0.65    ( ! [X2,X0,X1] : (k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.34/0.65    inference(cnf_transformation,[],[f86])).
% 2.34/0.65  fof(f86,plain,(
% 2.34/0.65    ! [X0,X1,X2] : ((k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.34/0.65    inference(ennf_transformation,[],[f34])).
% 2.34/0.65  fof(f34,axiom,(
% 2.34/0.65    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)))),
% 2.34/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).
% 2.34/0.65  fof(f189,plain,(
% 2.34/0.65    ( ! [X2,X0,X1] : (k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.34/0.65    inference(cnf_transformation,[],[f93])).
% 2.34/0.65  fof(f93,plain,(
% 2.34/0.65    ! [X0,X1,X2] : ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.34/0.65    inference(flattening,[],[f92])).
% 2.34/0.65  fof(f92,plain,(
% 2.34/0.65    ! [X0,X1,X2] : ((((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.34/0.65    inference(ennf_transformation,[],[f44])).
% 2.34/0.65  fof(f44,axiom,(
% 2.34/0.65    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1)))),
% 2.34/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).
% 2.34/0.65  fof(f427,plain,(
% 2.34/0.65    spl6_1 | ~spl6_4),
% 2.34/0.65    inference(avatar_contradiction_clause,[],[f426])).
% 2.34/0.65  fof(f426,plain,(
% 2.34/0.65    $false | (spl6_1 | ~spl6_4)),
% 2.34/0.65    inference(subsumption_resolution,[],[f423,f130])).
% 2.34/0.65  fof(f130,plain,(
% 2.34/0.65    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.34/0.65    inference(cnf_transformation,[],[f48])).
% 2.34/0.65  fof(f48,plain,(
% 2.34/0.65    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 2.34/0.65    inference(pure_predicate_removal,[],[f40])).
% 2.34/0.65  fof(f40,axiom,(
% 2.34/0.65    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 2.34/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 2.34/0.65  fof(f423,plain,(
% 2.34/0.65    ~m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | (spl6_1 | ~spl6_4)),
% 2.34/0.65    inference(unit_resulting_resolution,[],[f416,f213])).
% 2.34/0.65  fof(f213,plain,(
% 2.34/0.65    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.34/0.65    inference(duplicate_literal_removal,[],[f210])).
% 2.34/0.65  fof(f210,plain,(
% 2.34/0.65    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.34/0.65    inference(equality_resolution,[],[f194])).
% 2.34/0.65  fof(f194,plain,(
% 2.34/0.65    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.34/0.65    inference(cnf_transformation,[],[f117])).
% 2.34/0.65  fof(f117,plain,(
% 2.34/0.65    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.34/0.65    inference(nnf_transformation,[],[f97])).
% 2.34/0.65  fof(f97,plain,(
% 2.34/0.65    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.34/0.65    inference(flattening,[],[f96])).
% 2.34/0.65  fof(f96,plain,(
% 2.34/0.65    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.34/0.65    inference(ennf_transformation,[],[f32])).
% 2.34/0.65  fof(f32,axiom,(
% 2.34/0.65    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 2.34/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 2.34/0.65  fof(f416,plain,(
% 2.34/0.65    ~r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) | (spl6_1 | ~spl6_4)),
% 2.34/0.65    inference(backward_demodulation,[],[f261,f414])).
% 2.34/0.65  fof(f414,plain,(
% 2.34/0.65    k6_partfun1(sK0) = k6_partfun1(k1_relat_1(sK1)) | ~spl6_4),
% 2.34/0.65    inference(backward_demodulation,[],[f259,f319])).
% 2.34/0.65  fof(f261,plain,(
% 2.34/0.65    ~r2_relset_1(sK0,sK0,k6_partfun1(k1_relat_1(sK1)),k6_partfun1(sK0)) | spl6_1),
% 2.34/0.65    inference(backward_demodulation,[],[f257,f259])).
% 2.34/0.65  fof(f257,plain,(
% 2.34/0.65    ~r2_relset_1(sK0,sK0,k5_relat_1(sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) | spl6_1),
% 2.34/0.65    inference(subsumption_resolution,[],[f256,f118])).
% 2.34/0.65  fof(f256,plain,(
% 2.34/0.65    ~r2_relset_1(sK0,sK0,k5_relat_1(sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) | ~v1_funct_1(sK1) | spl6_1),
% 2.34/0.65    inference(subsumption_resolution,[],[f255,f121])).
% 2.34/0.65  fof(f255,plain,(
% 2.34/0.65    ~r2_relset_1(sK0,sK0,k5_relat_1(sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1) | spl6_1),
% 2.34/0.65    inference(subsumption_resolution,[],[f254,f252])).
% 2.34/0.65  fof(f254,plain,(
% 2.34/0.65    ~r2_relset_1(sK0,sK0,k5_relat_1(sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) | ~v1_funct_1(k2_funct_1(sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1) | spl6_1),
% 2.34/0.65    inference(subsumption_resolution,[],[f253,f249])).
% 2.34/0.65  fof(f253,plain,(
% 2.34/0.65    ~r2_relset_1(sK0,sK0,k5_relat_1(sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) | ~m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(k2_funct_1(sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1) | spl6_1),
% 2.34/0.65    inference(superposition,[],[f248,f195])).
% 2.34/0.65  fof(f248,plain,(
% 2.34/0.65    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) | spl6_1),
% 2.34/0.65    inference(backward_demodulation,[],[f217,f227])).
% 2.34/0.65  fof(f217,plain,(
% 2.34/0.65    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) | spl6_1),
% 2.34/0.65    inference(avatar_component_clause,[],[f215])).
% 2.34/0.65  fof(f411,plain,(
% 2.34/0.65    spl6_5),
% 2.34/0.65    inference(avatar_split_clause,[],[f408,f321])).
% 2.34/0.65  fof(f408,plain,(
% 2.34/0.65    sK0 = k9_relat_1(sK1,sK0)),
% 2.34/0.65    inference(forward_demodulation,[],[f407,f264])).
% 2.34/0.65  fof(f407,plain,(
% 2.34/0.65    k2_relat_1(sK1) = k9_relat_1(sK1,sK0)),
% 2.34/0.65    inference(subsumption_resolution,[],[f406,f228])).
% 2.34/0.65  fof(f406,plain,(
% 2.34/0.65    k2_relat_1(sK1) = k9_relat_1(sK1,sK0) | ~v1_relat_1(sK1)),
% 2.34/0.65    inference(superposition,[],[f150,f262])).
% 2.34/0.65  fof(f262,plain,(
% 2.34/0.65    sK1 = k7_relat_1(sK1,sK0)),
% 2.34/0.65    inference(unit_resulting_resolution,[],[f228,f229,f157])).
% 2.34/0.65  fof(f157,plain,(
% 2.34/0.65    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.34/0.65    inference(cnf_transformation,[],[f73])).
% 2.34/0.65  fof(f73,plain,(
% 2.34/0.65    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.34/0.65    inference(flattening,[],[f72])).
% 2.34/0.65  fof(f72,plain,(
% 2.34/0.65    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.34/0.65    inference(ennf_transformation,[],[f23])).
% 2.34/0.65  fof(f23,axiom,(
% 2.34/0.65    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 2.34/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).
% 2.34/0.65  fof(f150,plain,(
% 2.34/0.65    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.34/0.65    inference(cnf_transformation,[],[f66])).
% 2.34/0.65  fof(f66,plain,(
% 2.34/0.65    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.34/0.65    inference(ennf_transformation,[],[f22])).
% 2.34/0.65  fof(f22,axiom,(
% 2.34/0.65    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 2.34/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 2.34/0.65  fof(f377,plain,(
% 2.34/0.65    spl6_8 | ~spl6_3),
% 2.34/0.65    inference(avatar_split_clause,[],[f372,f313,f374])).
% 2.34/0.65  fof(f372,plain,(
% 2.34/0.65    k1_xboole_0 != sK0 | k1_xboole_0 = sK1),
% 2.34/0.65    inference(subsumption_resolution,[],[f359,f228])).
% 2.34/0.65  fof(f359,plain,(
% 2.34/0.65    k1_xboole_0 != sK0 | k1_xboole_0 = sK1 | ~v1_relat_1(sK1)),
% 2.34/0.65    inference(superposition,[],[f134,f264])).
% 2.34/0.65  fof(f134,plain,(
% 2.34/0.65    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 2.34/0.65    inference(cnf_transformation,[],[f52])).
% 2.34/0.65  fof(f52,plain,(
% 2.34/0.65    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 2.34/0.65    inference(flattening,[],[f51])).
% 2.34/0.65  fof(f51,plain,(
% 2.34/0.65    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 2.34/0.65    inference(ennf_transformation,[],[f24])).
% 2.34/0.65  fof(f24,axiom,(
% 2.34/0.65    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 2.34/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).
% 2.34/0.65  fof(f222,plain,(
% 2.34/0.65    ~spl6_1 | ~spl6_2),
% 2.34/0.65    inference(avatar_split_clause,[],[f122,f219,f215])).
% 2.34/0.65  fof(f122,plain,(
% 2.34/0.65    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))),
% 2.34/0.65    inference(cnf_transformation,[],[f101])).
% 2.34/0.65  % SZS output end Proof for theBenchmark
% 2.34/0.65  % (2730)------------------------------
% 2.34/0.65  % (2730)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.34/0.65  % (2730)Termination reason: Refutation
% 2.34/0.65  
% 2.34/0.65  % (2730)Memory used [KB]: 11385
% 2.34/0.65  % (2730)Time elapsed: 0.257 s
% 2.34/0.65  % (2730)------------------------------
% 2.34/0.65  % (2730)------------------------------
% 2.34/0.66  % (2701)Success in time 0.337 s
%------------------------------------------------------------------------------
