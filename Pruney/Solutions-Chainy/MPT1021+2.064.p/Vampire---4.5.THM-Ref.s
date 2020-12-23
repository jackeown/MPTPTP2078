%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:00 EST 2020

% Result     : Theorem 2.18s
% Output     : Refutation 2.22s
% Verified   : 
% Statistics : Number of formulae       :  164 (2127 expanded)
%              Number of leaves         :   20 ( 514 expanded)
%              Depth                    :   27
%              Number of atoms          :  485 (10838 expanded)
%              Number of equality atoms :  135 ( 588 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1219,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1218,f117])).

fof(f117,plain,(
    ! [X0,X1] : r2_relset_1(X0,X1,k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[],[f99,f58])).

fof(f58,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f99,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f98])).

fof(f98,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f90])).

fof(f90,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f1218,plain,(
    ~ r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f1217,f344])).

fof(f344,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(equality_resolution,[],[f272])).

fof(f272,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k6_relat_1(X0) ) ),
    inference(superposition,[],[f106,f63])).

fof(f63,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f106,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relat_1(k6_relat_1(X0))
      | k1_xboole_0 = k6_relat_1(X0) ) ),
    inference(resolution,[],[f65,f60])).

fof(f60,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f65,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

fof(f1217,plain,(
    ~ r2_relset_1(k1_xboole_0,k1_xboole_0,k6_relat_1(k1_xboole_0),k1_xboole_0) ),
    inference(forward_demodulation,[],[f1216,f371])).

fof(f371,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f370,f120])).

fof(f120,plain,(
    ! [X0,X1] : k1_relset_1(X0,X1,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f78,f58])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f370,plain,(
    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f361,f58])).

fof(f361,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(resolution,[],[f345,f97])).

fof(f97,plain,(
    ! [X2,X1] :
      ( ~ v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

fof(f40,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(f345,plain,(
    v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f136,f344])).

fof(f136,plain,(
    v1_funct_2(k6_relat_1(k1_xboole_0),k1_xboole_0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f134,f122])).

fof(f122,plain,(
    ! [X2] : k1_relset_1(X2,X2,k6_relat_1(X2)) = X2 ),
    inference(forward_demodulation,[],[f121,f63])).

fof(f121,plain,(
    ! [X2] : k1_relset_1(X2,X2,k6_relat_1(X2)) = k1_relat_1(k6_relat_1(X2)) ),
    inference(resolution,[],[f78,f102])).

fof(f102,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(forward_demodulation,[],[f62,f59])).

fof(f59,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f62,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f134,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,k6_relat_1(k1_xboole_0))
    | v1_funct_2(k6_relat_1(k1_xboole_0),k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[],[f96,f102])).

fof(f96,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f1216,plain,(
    ~ r2_relset_1(k1_xboole_0,k1_xboole_0,k6_relat_1(k1_relat_1(k1_xboole_0)),k1_xboole_0) ),
    inference(forward_demodulation,[],[f1215,f639])).

fof(f639,plain,(
    k1_xboole_0 = sK1 ),
    inference(trivial_inequality_removal,[],[f604])).

fof(f604,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK1 ),
    inference(backward_demodulation,[],[f414,f568])).

fof(f568,plain,(
    k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f567,f118])).

fof(f118,plain,(
    ! [X2] : r2_relset_1(X2,X2,k6_relat_1(X2),k6_relat_1(X2)) ),
    inference(resolution,[],[f99,f102])).

fof(f567,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0))
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f566,f221])).

fof(f221,plain,
    ( sK0 = k1_relat_1(sK1)
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f140,f119])).

fof(f119,plain,(
    k1_relset_1(sK0,sK0,sK1) = k1_relat_1(sK1) ),
    inference(resolution,[],[f78,f56])).

fof(f56,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,
    ( ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) )
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v3_funct_2(sK1,sK0,sK0)
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f26,f48])).

fof(f48,plain,
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

fof(f26,plain,(
    ? [X0,X1] :
      ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ? [X0,X1] :
      ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X1,X0,X0)
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_funct_2)).

fof(f140,plain,
    ( sK0 = k1_relset_1(sK0,sK0,sK1)
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f138,f56])).

fof(f138,plain,
    ( sK0 = k1_relset_1(sK0,sK0,sK1)
    | k1_xboole_0 = sK0
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f80,f54])).

fof(f54,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) = X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f566,plain,(
    ~ r2_relset_1(sK0,sK0,k6_relat_1(k1_relat_1(sK1)),k6_relat_1(sK0)) ),
    inference(backward_demodulation,[],[f467,f565])).

fof(f565,plain,(
    k6_relat_1(k1_relat_1(sK1)) = k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) ),
    inference(resolution,[],[f470,f178])).

fof(f178,plain,(
    m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(forward_demodulation,[],[f177,f155])).

fof(f155,plain,(
    k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f154,f53])).

fof(f53,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f49])).

fof(f154,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f153,f55])).

fof(f55,plain,(
    v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f153,plain,
    ( ~ v3_funct_2(sK1,sK0,sK0)
    | k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f151,f56])).

fof(f151,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v3_funct_2(sK1,sK0,sK0)
    | k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ v1_funct_1(sK1) ),
    inference(resolution,[],[f73,f54])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(X1,X0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_2(X0,X1) = k2_funct_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

fof(f177,plain,(
    m1_subset_1(k2_funct_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subsumption_resolution,[],[f176,f53])).

fof(f176,plain,
    ( m1_subset_1(k2_funct_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f175,f55])).

fof(f175,plain,
    ( ~ v3_funct_2(sK1,sK0,sK0)
    | m1_subset_1(k2_funct_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f173,f56])).

fof(f173,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v3_funct_2(sK1,sK0,sK0)
    | m1_subset_1(k2_funct_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1) ),
    inference(resolution,[],[f77,f54])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(X1,X0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
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

fof(f470,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k6_relat_1(k1_relat_1(sK1)) = k1_partfun1(sK0,sK0,X0,X1,sK1,k2_funct_1(sK1)) ) ),
    inference(resolution,[],[f341,f56])).

fof(f341,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k6_relat_1(k1_relat_1(sK1)) = k1_partfun1(X0,X1,X2,X3,sK1,k2_funct_1(sK1))
      | ~ m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ) ),
    inference(forward_demodulation,[],[f338,f328])).

fof(f328,plain,(
    k5_relat_1(sK1,k2_funct_1(sK1)) = k6_relat_1(k1_relat_1(sK1)) ),
    inference(resolution,[],[f223,f256])).

fof(f256,plain,(
    v1_relat_1(sK1) ),
    inference(resolution,[],[f105,f56])).

fof(f105,plain,(
    ! [X4,X2,X3] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | v1_relat_1(X2) ) ),
    inference(resolution,[],[f67,f70])).

fof(f70,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f223,plain,
    ( ~ v1_relat_1(sK1)
    | k5_relat_1(sK1,k2_funct_1(sK1)) = k6_relat_1(k1_relat_1(sK1)) ),
    inference(resolution,[],[f123,f127])).

fof(f127,plain,(
    v2_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f126,f56])).

fof(f126,plain,
    ( v2_funct_1(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subsumption_resolution,[],[f125,f53])).

fof(f125,plain,
    ( v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f87,f55])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_funct_2(X2,X0,X1)
      | v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).

fof(f123,plain,
    ( ~ v2_funct_1(sK1)
    | k5_relat_1(sK1,k2_funct_1(sK1)) = k6_relat_1(k1_relat_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f68,f53])).

fof(f68,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

fof(f338,plain,(
    ! [X2,X0,X3,X1] :
      ( k5_relat_1(sK1,k2_funct_1(sK1)) = k1_partfun1(X0,X1,X2,X3,sK1,k2_funct_1(sK1))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ) ),
    inference(resolution,[],[f180,f53])).

fof(f180,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_1(X4)
      | k1_partfun1(X2,X3,X0,X1,X4,k2_funct_1(sK1)) = k5_relat_1(X4,k2_funct_1(sK1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(resolution,[],[f156,f91])).

fof(f91,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f156,plain,(
    v1_funct_1(k2_funct_1(sK1)) ),
    inference(backward_demodulation,[],[f150,f155])).

fof(f150,plain,(
    v1_funct_1(k2_funct_2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f149,f53])).

fof(f149,plain,
    ( v1_funct_1(k2_funct_2(sK0,sK1))
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f148,f55])).

fof(f148,plain,
    ( ~ v3_funct_2(sK1,sK0,sK0)
    | v1_funct_1(k2_funct_2(sK0,sK1))
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f146,f56])).

fof(f146,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v3_funct_2(sK1,sK0,sK0)
    | v1_funct_1(k2_funct_2(sK0,sK1))
    | ~ v1_funct_1(sK1) ),
    inference(resolution,[],[f74,f54])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(X1,X0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | v1_funct_1(k2_funct_2(X0,X1))
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

% (26656)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
fof(f467,plain,(
    ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f466,f118])).

fof(f466,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_relat_1(sK0)) ),
    inference(backward_demodulation,[],[f158,f465])).

fof(f465,plain,(
    k6_relat_1(sK0) = k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) ),
    inference(resolution,[],[f337,f56])).

fof(f337,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k6_relat_1(sK0) = k1_partfun1(sK0,sK0,X0,X1,k2_funct_1(sK1),sK1) ) ),
    inference(resolution,[],[f285,f178])).

fof(f285,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | k6_relat_1(sK0) = k1_partfun1(X4,X5,X6,X7,k2_funct_1(sK1),sK1)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) ) ),
    inference(backward_demodulation,[],[f226,f284])).

fof(f284,plain,(
    k6_relat_1(sK0) = k5_relat_1(k2_funct_1(sK1),sK1) ),
    inference(subsumption_resolution,[],[f282,f256])).

fof(f282,plain,
    ( k6_relat_1(sK0) = k5_relat_1(k2_funct_1(sK1),sK1)
    | ~ v1_relat_1(sK1) ),
    inference(backward_demodulation,[],[f224,f281])).

fof(f281,plain,(
    sK0 = k2_relat_1(sK1) ),
    inference(resolution,[],[f160,f256])).

fof(f160,plain,
    ( ~ v1_relat_1(sK1)
    | sK0 = k2_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f159,f110])).

fof(f110,plain,(
    v5_relat_1(sK1,sK0) ),
    inference(resolution,[],[f79,f56])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f159,plain,
    ( sK0 = k2_relat_1(sK1)
    | ~ v5_relat_1(sK1,sK0)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f130,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_2(X1,X0)
      | k2_relat_1(X1) = X0
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

fof(f130,plain,(
    v2_funct_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f129,f56])).

fof(f129,plain,
    ( v2_funct_2(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subsumption_resolution,[],[f128,f53])).

fof(f128,plain,
    ( v2_funct_2(sK1,sK0)
    | ~ v1_funct_1(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f88,f55])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_funct_2(X2,X0,X1)
      | v2_funct_2(X2,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f224,plain,
    ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_relat_1(k2_relat_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f124,f127])).

fof(f124,plain,
    ( ~ v2_funct_1(sK1)
    | k5_relat_1(k2_funct_1(sK1),sK1) = k6_relat_1(k2_relat_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f69,f53])).

fof(f69,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f226,plain,(
    ! [X6,X4,X7,X5] :
      ( k5_relat_1(k2_funct_1(sK1),sK1) = k1_partfun1(X4,X5,X6,X7,k2_funct_1(sK1),sK1)
      | ~ m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) ) ),
    inference(resolution,[],[f179,f156])).

fof(f179,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_1(X4)
      | k1_partfun1(X2,X3,X0,X1,X4,sK1) = k5_relat_1(X4,sK1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(resolution,[],[f91,f53])).

fof(f158,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_relat_1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f157,f155])).

fof(f157,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_relat_1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_relat_1(sK0)) ),
    inference(backward_demodulation,[],[f101,f155])).

fof(f101,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_relat_1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f100,f59])).

fof(f100,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_relat_1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) ),
    inference(forward_demodulation,[],[f57,f59])).

fof(f57,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f49])).

fof(f414,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f275,f281])).

fof(f275,plain,
    ( k1_xboole_0 != k2_relat_1(sK1)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f256,f66])).

fof(f66,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 != k2_relat_1(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f1215,plain,(
    ~ r2_relset_1(k1_xboole_0,k1_xboole_0,k6_relat_1(k1_relat_1(sK1)),k1_xboole_0) ),
    inference(forward_demodulation,[],[f636,f344])).

fof(f636,plain,(
    ~ r2_relset_1(k1_xboole_0,k1_xboole_0,k6_relat_1(k1_relat_1(sK1)),k6_relat_1(k1_xboole_0)) ),
    inference(backward_demodulation,[],[f566,f568])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n011.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 19:17:42 EST 2020
% 0.15/0.35  % CPUTime    : 
% 1.51/0.58  % (26646)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.51/0.58  % (26662)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.51/0.59  % (26655)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.51/0.59  % (26661)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.51/0.59  % (26647)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.51/0.59  % (26645)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.69/0.59  % (26654)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.69/0.60  % (26655)Refutation not found, incomplete strategy% (26655)------------------------------
% 1.69/0.60  % (26655)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.69/0.60  % (26663)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.69/0.61  % (26653)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.69/0.61  % (26655)Termination reason: Refutation not found, incomplete strategy
% 1.69/0.61  
% 1.69/0.61  % (26655)Memory used [KB]: 10746
% 1.69/0.61  % (26655)Time elapsed: 0.162 s
% 1.69/0.61  % (26655)------------------------------
% 1.69/0.61  % (26655)------------------------------
% 1.69/0.63  % (26642)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.69/0.63  % (26652)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.69/0.64  % (26644)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.69/0.64  % (26641)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.69/0.64  % (26658)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.69/0.64  % (26650)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.69/0.65  % (26660)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.69/0.65  % (26665)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.69/0.65  % (26666)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 2.18/0.65  % (26668)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 2.18/0.65  % (26649)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 2.18/0.66  % (26646)Refutation found. Thanks to Tanya!
% 2.18/0.66  % SZS status Theorem for theBenchmark
% 2.18/0.66  % (26657)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 2.18/0.66  % SZS output start Proof for theBenchmark
% 2.18/0.66  fof(f1219,plain,(
% 2.18/0.66    $false),
% 2.18/0.66    inference(subsumption_resolution,[],[f1218,f117])).
% 2.18/0.66  fof(f117,plain,(
% 2.18/0.66    ( ! [X0,X1] : (r2_relset_1(X0,X1,k1_xboole_0,k1_xboole_0)) )),
% 2.18/0.66    inference(resolution,[],[f99,f58])).
% 2.18/0.66  fof(f58,plain,(
% 2.18/0.66    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.18/0.66    inference(cnf_transformation,[],[f1])).
% 2.18/0.66  fof(f1,axiom,(
% 2.18/0.66    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.18/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 2.18/0.66  fof(f99,plain,(
% 2.18/0.66    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 2.18/0.66    inference(duplicate_literal_removal,[],[f98])).
% 2.18/0.66  fof(f98,plain,(
% 2.18/0.66    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.18/0.66    inference(equality_resolution,[],[f90])).
% 2.18/0.66  fof(f90,plain,(
% 2.18/0.66    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.18/0.66    inference(cnf_transformation,[],[f52])).
% 2.18/0.66  fof(f52,plain,(
% 2.18/0.66    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.18/0.66    inference(nnf_transformation,[],[f45])).
% 2.18/0.66  fof(f45,plain,(
% 2.18/0.66    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.18/0.66    inference(flattening,[],[f44])).
% 2.18/0.66  fof(f44,plain,(
% 2.18/0.66    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.18/0.66    inference(ennf_transformation,[],[f11])).
% 2.18/0.66  fof(f11,axiom,(
% 2.18/0.66    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 2.18/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 2.18/0.66  fof(f1218,plain,(
% 2.18/0.66    ~r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 2.18/0.66    inference(forward_demodulation,[],[f1217,f344])).
% 2.18/0.66  fof(f344,plain,(
% 2.18/0.66    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 2.18/0.66    inference(equality_resolution,[],[f272])).
% 2.18/0.66  fof(f272,plain,(
% 2.18/0.66    ( ! [X0] : (k1_xboole_0 != X0 | k1_xboole_0 = k6_relat_1(X0)) )),
% 2.18/0.66    inference(superposition,[],[f106,f63])).
% 2.18/0.66  fof(f63,plain,(
% 2.18/0.66    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 2.18/0.66    inference(cnf_transformation,[],[f6])).
% 2.18/0.66  fof(f6,axiom,(
% 2.18/0.66    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 2.18/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 2.18/0.66  fof(f106,plain,(
% 2.18/0.66    ( ! [X0] : (k1_xboole_0 != k1_relat_1(k6_relat_1(X0)) | k1_xboole_0 = k6_relat_1(X0)) )),
% 2.18/0.66    inference(resolution,[],[f65,f60])).
% 2.18/0.66  fof(f60,plain,(
% 2.18/0.66    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 2.18/0.66    inference(cnf_transformation,[],[f7])).
% 2.18/0.66  fof(f7,axiom,(
% 2.18/0.66    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 2.18/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).
% 2.18/0.66  fof(f65,plain,(
% 2.18/0.66    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0) | k1_xboole_0 = X0) )),
% 2.18/0.66    inference(cnf_transformation,[],[f28])).
% 2.22/0.66  fof(f28,plain,(
% 2.22/0.66    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 2.22/0.66    inference(flattening,[],[f27])).
% 2.22/0.66  fof(f27,plain,(
% 2.22/0.66    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 2.22/0.66    inference(ennf_transformation,[],[f5])).
% 2.22/0.66  fof(f5,axiom,(
% 2.22/0.66    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 2.22/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).
% 2.22/0.66  fof(f1217,plain,(
% 2.22/0.66    ~r2_relset_1(k1_xboole_0,k1_xboole_0,k6_relat_1(k1_xboole_0),k1_xboole_0)),
% 2.22/0.66    inference(forward_demodulation,[],[f1216,f371])).
% 2.22/0.66  fof(f371,plain,(
% 2.22/0.66    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.22/0.66    inference(superposition,[],[f370,f120])).
% 2.22/0.66  fof(f120,plain,(
% 2.22/0.66    ( ! [X0,X1] : (k1_relset_1(X0,X1,k1_xboole_0) = k1_relat_1(k1_xboole_0)) )),
% 2.22/0.66    inference(resolution,[],[f78,f58])).
% 2.22/0.66  fof(f78,plain,(
% 2.22/0.66    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 2.22/0.66    inference(cnf_transformation,[],[f38])).
% 2.22/0.66  fof(f38,plain,(
% 2.22/0.66    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.22/0.66    inference(ennf_transformation,[],[f10])).
% 2.22/0.66  fof(f10,axiom,(
% 2.22/0.66    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 2.22/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 2.22/0.66  fof(f370,plain,(
% 2.22/0.66    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 2.22/0.66    inference(subsumption_resolution,[],[f361,f58])).
% 2.22/0.66  fof(f361,plain,(
% 2.22/0.66    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 2.22/0.66    inference(resolution,[],[f345,f97])).
% 2.22/0.66  fof(f97,plain,(
% 2.22/0.66    ( ! [X2,X1] : (~v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 2.22/0.66    inference(equality_resolution,[],[f81])).
% 2.22/0.66  fof(f81,plain,(
% 2.22/0.66    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.22/0.66    inference(cnf_transformation,[],[f51])).
% 2.22/0.66  fof(f51,plain,(
% 2.22/0.66    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.22/0.66    inference(nnf_transformation,[],[f41])).
% 2.22/0.66  fof(f41,plain,(
% 2.22/0.66    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.22/0.66    inference(flattening,[],[f40])).
% 2.22/0.66  fof(f40,plain,(
% 2.22/0.66    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.22/0.66    inference(ennf_transformation,[],[f13])).
% 2.22/0.66  fof(f13,axiom,(
% 2.22/0.66    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.22/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 2.22/0.66  fof(f345,plain,(
% 2.22/0.66    v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 2.22/0.66    inference(backward_demodulation,[],[f136,f344])).
% 2.22/0.66  fof(f136,plain,(
% 2.22/0.66    v1_funct_2(k6_relat_1(k1_xboole_0),k1_xboole_0,k1_xboole_0)),
% 2.22/0.66    inference(subsumption_resolution,[],[f134,f122])).
% 2.22/0.66  fof(f122,plain,(
% 2.22/0.66    ( ! [X2] : (k1_relset_1(X2,X2,k6_relat_1(X2)) = X2) )),
% 2.22/0.66    inference(forward_demodulation,[],[f121,f63])).
% 2.22/0.66  fof(f121,plain,(
% 2.22/0.66    ( ! [X2] : (k1_relset_1(X2,X2,k6_relat_1(X2)) = k1_relat_1(k6_relat_1(X2))) )),
% 2.22/0.66    inference(resolution,[],[f78,f102])).
% 2.22/0.66  fof(f102,plain,(
% 2.22/0.66    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.22/0.66    inference(forward_demodulation,[],[f62,f59])).
% 2.22/0.66  fof(f59,plain,(
% 2.22/0.66    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 2.22/0.66    inference(cnf_transformation,[],[f19])).
% 2.22/0.66  fof(f19,axiom,(
% 2.22/0.66    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 2.22/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 2.22/0.66  fof(f62,plain,(
% 2.22/0.66    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.22/0.66    inference(cnf_transformation,[],[f22])).
% 2.22/0.66  fof(f22,plain,(
% 2.22/0.66    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 2.22/0.66    inference(pure_predicate_removal,[],[f16])).
% 2.22/0.66  fof(f16,axiom,(
% 2.22/0.66    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 2.22/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 2.22/0.66  fof(f134,plain,(
% 2.22/0.66    k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,k6_relat_1(k1_xboole_0)) | v1_funct_2(k6_relat_1(k1_xboole_0),k1_xboole_0,k1_xboole_0)),
% 2.22/0.66    inference(resolution,[],[f96,f102])).
% 2.22/0.66  fof(f96,plain,(
% 2.22/0.66    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | v1_funct_2(X2,k1_xboole_0,X1)) )),
% 2.22/0.66    inference(equality_resolution,[],[f83])).
% 2.22/0.66  fof(f83,plain,(
% 2.22/0.66    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.22/0.66    inference(cnf_transformation,[],[f51])).
% 2.22/0.66  fof(f1216,plain,(
% 2.22/0.66    ~r2_relset_1(k1_xboole_0,k1_xboole_0,k6_relat_1(k1_relat_1(k1_xboole_0)),k1_xboole_0)),
% 2.22/0.66    inference(forward_demodulation,[],[f1215,f639])).
% 2.22/0.66  fof(f639,plain,(
% 2.22/0.66    k1_xboole_0 = sK1),
% 2.22/0.66    inference(trivial_inequality_removal,[],[f604])).
% 2.22/0.66  fof(f604,plain,(
% 2.22/0.66    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK1),
% 2.22/0.66    inference(backward_demodulation,[],[f414,f568])).
% 2.22/0.66  fof(f568,plain,(
% 2.22/0.66    k1_xboole_0 = sK0),
% 2.22/0.66    inference(subsumption_resolution,[],[f567,f118])).
% 2.22/0.66  fof(f118,plain,(
% 2.22/0.66    ( ! [X2] : (r2_relset_1(X2,X2,k6_relat_1(X2),k6_relat_1(X2))) )),
% 2.22/0.66    inference(resolution,[],[f99,f102])).
% 2.22/0.66  fof(f567,plain,(
% 2.22/0.66    ~r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0)) | k1_xboole_0 = sK0),
% 2.22/0.66    inference(superposition,[],[f566,f221])).
% 2.22/0.66  fof(f221,plain,(
% 2.22/0.66    sK0 = k1_relat_1(sK1) | k1_xboole_0 = sK0),
% 2.22/0.66    inference(superposition,[],[f140,f119])).
% 2.22/0.66  fof(f119,plain,(
% 2.22/0.66    k1_relset_1(sK0,sK0,sK1) = k1_relat_1(sK1)),
% 2.22/0.66    inference(resolution,[],[f78,f56])).
% 2.22/0.66  fof(f56,plain,(
% 2.22/0.66    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.22/0.66    inference(cnf_transformation,[],[f49])).
% 2.22/0.66  fof(f49,plain,(
% 2.22/0.66    (~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 2.22/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f26,f48])).
% 2.22/0.66  fof(f48,plain,(
% 2.22/0.66    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ((~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 2.22/0.66    introduced(choice_axiom,[])).
% 2.22/0.66  fof(f26,plain,(
% 2.22/0.66    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 2.22/0.66    inference(flattening,[],[f25])).
% 2.22/0.66  fof(f25,plain,(
% 2.22/0.66    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 2.22/0.66    inference(ennf_transformation,[],[f21])).
% 2.22/0.66  fof(f21,negated_conjecture,(
% 2.22/0.66    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 2.22/0.66    inference(negated_conjecture,[],[f20])).
% 2.22/0.66  fof(f20,conjecture,(
% 2.22/0.66    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 2.22/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_funct_2)).
% 2.22/0.66  fof(f140,plain,(
% 2.22/0.66    sK0 = k1_relset_1(sK0,sK0,sK1) | k1_xboole_0 = sK0),
% 2.22/0.66    inference(subsumption_resolution,[],[f138,f56])).
% 2.22/0.66  fof(f138,plain,(
% 2.22/0.66    sK0 = k1_relset_1(sK0,sK0,sK1) | k1_xboole_0 = sK0 | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.22/0.66    inference(resolution,[],[f80,f54])).
% 2.22/0.66  fof(f54,plain,(
% 2.22/0.66    v1_funct_2(sK1,sK0,sK0)),
% 2.22/0.66    inference(cnf_transformation,[],[f49])).
% 2.22/0.66  fof(f80,plain,(
% 2.22/0.66    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) = X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.22/0.66    inference(cnf_transformation,[],[f51])).
% 2.22/0.66  fof(f566,plain,(
% 2.22/0.66    ~r2_relset_1(sK0,sK0,k6_relat_1(k1_relat_1(sK1)),k6_relat_1(sK0))),
% 2.22/0.66    inference(backward_demodulation,[],[f467,f565])).
% 2.22/0.66  fof(f565,plain,(
% 2.22/0.66    k6_relat_1(k1_relat_1(sK1)) = k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1))),
% 2.22/0.66    inference(resolution,[],[f470,f178])).
% 2.22/0.66  fof(f178,plain,(
% 2.22/0.66    m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.22/0.66    inference(forward_demodulation,[],[f177,f155])).
% 2.22/0.66  fof(f155,plain,(
% 2.22/0.66    k2_funct_2(sK0,sK1) = k2_funct_1(sK1)),
% 2.22/0.66    inference(subsumption_resolution,[],[f154,f53])).
% 2.22/0.66  fof(f53,plain,(
% 2.22/0.66    v1_funct_1(sK1)),
% 2.22/0.66    inference(cnf_transformation,[],[f49])).
% 2.22/0.66  fof(f154,plain,(
% 2.22/0.66    k2_funct_2(sK0,sK1) = k2_funct_1(sK1) | ~v1_funct_1(sK1)),
% 2.22/0.66    inference(subsumption_resolution,[],[f153,f55])).
% 2.22/0.66  fof(f55,plain,(
% 2.22/0.66    v3_funct_2(sK1,sK0,sK0)),
% 2.22/0.66    inference(cnf_transformation,[],[f49])).
% 2.22/0.66  fof(f153,plain,(
% 2.22/0.66    ~v3_funct_2(sK1,sK0,sK0) | k2_funct_2(sK0,sK1) = k2_funct_1(sK1) | ~v1_funct_1(sK1)),
% 2.22/0.66    inference(subsumption_resolution,[],[f151,f56])).
% 2.22/0.66  fof(f151,plain,(
% 2.22/0.66    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v3_funct_2(sK1,sK0,sK0) | k2_funct_2(sK0,sK1) = k2_funct_1(sK1) | ~v1_funct_1(sK1)),
% 2.22/0.66    inference(resolution,[],[f73,f54])).
% 2.22/0.66  fof(f73,plain,(
% 2.22/0.66    ( ! [X0,X1] : (~v1_funct_2(X1,X0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | k2_funct_2(X0,X1) = k2_funct_1(X1) | ~v1_funct_1(X1)) )),
% 2.22/0.66    inference(cnf_transformation,[],[f35])).
% 2.22/0.66  fof(f35,plain,(
% 2.22/0.66    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 2.22/0.66    inference(flattening,[],[f34])).
% 2.22/0.66  fof(f34,plain,(
% 2.22/0.66    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 2.22/0.66    inference(ennf_transformation,[],[f18])).
% 2.22/0.66  fof(f18,axiom,(
% 2.22/0.66    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_2(X0,X1) = k2_funct_1(X1))),
% 2.22/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).
% 2.22/0.66  fof(f177,plain,(
% 2.22/0.66    m1_subset_1(k2_funct_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.22/0.66    inference(subsumption_resolution,[],[f176,f53])).
% 2.22/0.66  fof(f176,plain,(
% 2.22/0.66    m1_subset_1(k2_funct_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1)),
% 2.22/0.66    inference(subsumption_resolution,[],[f175,f55])).
% 2.22/0.66  fof(f175,plain,(
% 2.22/0.66    ~v3_funct_2(sK1,sK0,sK0) | m1_subset_1(k2_funct_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1)),
% 2.22/0.66    inference(subsumption_resolution,[],[f173,f56])).
% 2.22/0.66  fof(f173,plain,(
% 2.22/0.66    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v3_funct_2(sK1,sK0,sK0) | m1_subset_1(k2_funct_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1)),
% 2.22/0.66    inference(resolution,[],[f77,f54])).
% 2.22/0.66  fof(f77,plain,(
% 2.22/0.66    ( ! [X0,X1] : (~v1_funct_2(X1,X0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_1(X1)) )),
% 2.22/0.66    inference(cnf_transformation,[],[f37])).
% 2.22/0.66  fof(f37,plain,(
% 2.22/0.66    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 2.22/0.66    inference(flattening,[],[f36])).
% 2.22/0.66  fof(f36,plain,(
% 2.22/0.66    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 2.22/0.66    inference(ennf_transformation,[],[f15])).
% 2.22/0.66  fof(f15,axiom,(
% 2.22/0.66    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))))),
% 2.22/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_2)).
% 2.22/0.66  fof(f470,plain,(
% 2.22/0.66    ( ! [X0,X1] : (~m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k6_relat_1(k1_relat_1(sK1)) = k1_partfun1(sK0,sK0,X0,X1,sK1,k2_funct_1(sK1))) )),
% 2.22/0.66    inference(resolution,[],[f341,f56])).
% 2.22/0.66  fof(f341,plain,(
% 2.22/0.66    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k6_relat_1(k1_relat_1(sK1)) = k1_partfun1(X0,X1,X2,X3,sK1,k2_funct_1(sK1)) | ~m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) )),
% 2.22/0.66    inference(forward_demodulation,[],[f338,f328])).
% 2.22/0.66  fof(f328,plain,(
% 2.22/0.66    k5_relat_1(sK1,k2_funct_1(sK1)) = k6_relat_1(k1_relat_1(sK1))),
% 2.22/0.66    inference(resolution,[],[f223,f256])).
% 2.22/0.67  fof(f256,plain,(
% 2.22/0.67    v1_relat_1(sK1)),
% 2.22/0.67    inference(resolution,[],[f105,f56])).
% 2.22/0.67  fof(f105,plain,(
% 2.22/0.67    ( ! [X4,X2,X3] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | v1_relat_1(X2)) )),
% 2.22/0.67    inference(resolution,[],[f67,f70])).
% 2.22/0.67  fof(f70,plain,(
% 2.22/0.67    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.22/0.67    inference(cnf_transformation,[],[f4])).
% 2.22/0.67  fof(f4,axiom,(
% 2.22/0.67    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.22/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 2.22/0.67  fof(f67,plain,(
% 2.22/0.67    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 2.22/0.67    inference(cnf_transformation,[],[f29])).
% 2.22/0.67  fof(f29,plain,(
% 2.22/0.67    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.22/0.67    inference(ennf_transformation,[],[f3])).
% 2.22/0.67  fof(f3,axiom,(
% 2.22/0.67    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.22/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 2.22/0.67  fof(f223,plain,(
% 2.22/0.67    ~v1_relat_1(sK1) | k5_relat_1(sK1,k2_funct_1(sK1)) = k6_relat_1(k1_relat_1(sK1))),
% 2.22/0.67    inference(resolution,[],[f123,f127])).
% 2.22/0.67  fof(f127,plain,(
% 2.22/0.67    v2_funct_1(sK1)),
% 2.22/0.67    inference(subsumption_resolution,[],[f126,f56])).
% 2.22/0.67  fof(f126,plain,(
% 2.22/0.67    v2_funct_1(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.22/0.67    inference(subsumption_resolution,[],[f125,f53])).
% 2.22/0.67  fof(f125,plain,(
% 2.22/0.67    v2_funct_1(sK1) | ~v1_funct_1(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.22/0.67    inference(resolution,[],[f87,f55])).
% 2.22/0.67  fof(f87,plain,(
% 2.22/0.67    ( ! [X2,X0,X1] : (~v3_funct_2(X2,X0,X1) | v2_funct_1(X2) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.22/0.67    inference(cnf_transformation,[],[f43])).
% 2.22/0.67  fof(f43,plain,(
% 2.22/0.67    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.22/0.67    inference(flattening,[],[f42])).
% 2.22/0.67  fof(f42,plain,(
% 2.22/0.67    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.22/0.67    inference(ennf_transformation,[],[f12])).
% 2.22/0.67  fof(f12,axiom,(
% 2.22/0.67    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 2.22/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).
% 2.22/0.67  fof(f123,plain,(
% 2.22/0.67    ~v2_funct_1(sK1) | k5_relat_1(sK1,k2_funct_1(sK1)) = k6_relat_1(k1_relat_1(sK1)) | ~v1_relat_1(sK1)),
% 2.22/0.67    inference(resolution,[],[f68,f53])).
% 2.22/0.67  fof(f68,plain,(
% 2.22/0.67    ( ! [X0] : (~v1_funct_1(X0) | ~v2_funct_1(X0) | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 2.22/0.67    inference(cnf_transformation,[],[f31])).
% 2.22/0.67  fof(f31,plain,(
% 2.22/0.67    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.22/0.67    inference(flattening,[],[f30])).
% 2.22/0.67  fof(f30,plain,(
% 2.22/0.67    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.22/0.67    inference(ennf_transformation,[],[f8])).
% 2.22/0.67  fof(f8,axiom,(
% 2.22/0.67    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 2.22/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).
% 2.22/0.67  fof(f338,plain,(
% 2.22/0.67    ( ! [X2,X0,X3,X1] : (k5_relat_1(sK1,k2_funct_1(sK1)) = k1_partfun1(X0,X1,X2,X3,sK1,k2_funct_1(sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) )),
% 2.22/0.67    inference(resolution,[],[f180,f53])).
% 2.22/0.67  fof(f180,plain,(
% 2.22/0.67    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_1(X4) | k1_partfun1(X2,X3,X0,X1,X4,k2_funct_1(sK1)) = k5_relat_1(X4,k2_funct_1(sK1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.22/0.67    inference(resolution,[],[f156,f91])).
% 2.22/0.67  fof(f91,plain,(
% 2.22/0.67    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 2.22/0.67    inference(cnf_transformation,[],[f47])).
% 2.22/0.67  fof(f47,plain,(
% 2.22/0.67    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.22/0.67    inference(flattening,[],[f46])).
% 2.22/0.67  fof(f46,plain,(
% 2.22/0.67    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.22/0.67    inference(ennf_transformation,[],[f17])).
% 2.22/0.67  fof(f17,axiom,(
% 2.22/0.67    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 2.22/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 2.22/0.67  fof(f156,plain,(
% 2.22/0.67    v1_funct_1(k2_funct_1(sK1))),
% 2.22/0.67    inference(backward_demodulation,[],[f150,f155])).
% 2.22/0.67  fof(f150,plain,(
% 2.22/0.67    v1_funct_1(k2_funct_2(sK0,sK1))),
% 2.22/0.67    inference(subsumption_resolution,[],[f149,f53])).
% 2.22/0.67  fof(f149,plain,(
% 2.22/0.67    v1_funct_1(k2_funct_2(sK0,sK1)) | ~v1_funct_1(sK1)),
% 2.22/0.67    inference(subsumption_resolution,[],[f148,f55])).
% 2.22/0.67  fof(f148,plain,(
% 2.22/0.67    ~v3_funct_2(sK1,sK0,sK0) | v1_funct_1(k2_funct_2(sK0,sK1)) | ~v1_funct_1(sK1)),
% 2.22/0.67    inference(subsumption_resolution,[],[f146,f56])).
% 2.22/0.67  fof(f146,plain,(
% 2.22/0.67    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v3_funct_2(sK1,sK0,sK0) | v1_funct_1(k2_funct_2(sK0,sK1)) | ~v1_funct_1(sK1)),
% 2.22/0.67    inference(resolution,[],[f74,f54])).
% 2.22/0.67  fof(f74,plain,(
% 2.22/0.67    ( ! [X0,X1] : (~v1_funct_2(X1,X0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | v1_funct_1(k2_funct_2(X0,X1)) | ~v1_funct_1(X1)) )),
% 2.22/0.67    inference(cnf_transformation,[],[f37])).
% 2.22/0.67  % (26656)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 2.22/0.67  fof(f467,plain,(
% 2.22/0.67    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_relat_1(sK0))),
% 2.22/0.67    inference(subsumption_resolution,[],[f466,f118])).
% 2.22/0.67  fof(f466,plain,(
% 2.22/0.67    ~r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_relat_1(sK0))),
% 2.22/0.67    inference(backward_demodulation,[],[f158,f465])).
% 2.22/0.67  fof(f465,plain,(
% 2.22/0.67    k6_relat_1(sK0) = k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1)),
% 2.22/0.67    inference(resolution,[],[f337,f56])).
% 2.22/0.67  fof(f337,plain,(
% 2.22/0.67    ( ! [X0,X1] : (~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k6_relat_1(sK0) = k1_partfun1(sK0,sK0,X0,X1,k2_funct_1(sK1),sK1)) )),
% 2.22/0.67    inference(resolution,[],[f285,f178])).
% 2.22/0.67  fof(f285,plain,(
% 2.22/0.67    ( ! [X6,X4,X7,X5] : (~m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | k6_relat_1(sK0) = k1_partfun1(X4,X5,X6,X7,k2_funct_1(sK1),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))) )),
% 2.22/0.67    inference(backward_demodulation,[],[f226,f284])).
% 2.22/0.67  fof(f284,plain,(
% 2.22/0.67    k6_relat_1(sK0) = k5_relat_1(k2_funct_1(sK1),sK1)),
% 2.22/0.67    inference(subsumption_resolution,[],[f282,f256])).
% 2.22/0.67  fof(f282,plain,(
% 2.22/0.67    k6_relat_1(sK0) = k5_relat_1(k2_funct_1(sK1),sK1) | ~v1_relat_1(sK1)),
% 2.22/0.67    inference(backward_demodulation,[],[f224,f281])).
% 2.22/0.67  fof(f281,plain,(
% 2.22/0.67    sK0 = k2_relat_1(sK1)),
% 2.22/0.67    inference(resolution,[],[f160,f256])).
% 2.22/0.67  fof(f160,plain,(
% 2.22/0.67    ~v1_relat_1(sK1) | sK0 = k2_relat_1(sK1)),
% 2.22/0.67    inference(subsumption_resolution,[],[f159,f110])).
% 2.22/0.67  fof(f110,plain,(
% 2.22/0.67    v5_relat_1(sK1,sK0)),
% 2.22/0.67    inference(resolution,[],[f79,f56])).
% 2.22/0.67  fof(f79,plain,(
% 2.22/0.67    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 2.22/0.67    inference(cnf_transformation,[],[f39])).
% 2.22/0.67  fof(f39,plain,(
% 2.22/0.67    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.22/0.67    inference(ennf_transformation,[],[f23])).
% 2.22/0.67  fof(f23,plain,(
% 2.22/0.67    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 2.22/0.67    inference(pure_predicate_removal,[],[f9])).
% 2.22/0.67  fof(f9,axiom,(
% 2.22/0.67    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.22/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 2.22/0.67  fof(f159,plain,(
% 2.22/0.67    sK0 = k2_relat_1(sK1) | ~v5_relat_1(sK1,sK0) | ~v1_relat_1(sK1)),
% 2.22/0.67    inference(resolution,[],[f130,f71])).
% 2.22/0.67  fof(f71,plain,(
% 2.22/0.67    ( ! [X0,X1] : (~v2_funct_2(X1,X0) | k2_relat_1(X1) = X0 | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.22/0.67    inference(cnf_transformation,[],[f50])).
% 2.22/0.67  fof(f50,plain,(
% 2.22/0.67    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.22/0.67    inference(nnf_transformation,[],[f33])).
% 2.22/0.67  fof(f33,plain,(
% 2.22/0.67    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.22/0.67    inference(flattening,[],[f32])).
% 2.22/0.67  fof(f32,plain,(
% 2.22/0.67    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.22/0.67    inference(ennf_transformation,[],[f14])).
% 2.22/0.67  fof(f14,axiom,(
% 2.22/0.67    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 2.22/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).
% 2.22/0.67  fof(f130,plain,(
% 2.22/0.67    v2_funct_2(sK1,sK0)),
% 2.22/0.67    inference(subsumption_resolution,[],[f129,f56])).
% 2.22/0.67  fof(f129,plain,(
% 2.22/0.67    v2_funct_2(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.22/0.67    inference(subsumption_resolution,[],[f128,f53])).
% 2.22/0.67  fof(f128,plain,(
% 2.22/0.67    v2_funct_2(sK1,sK0) | ~v1_funct_1(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.22/0.67    inference(resolution,[],[f88,f55])).
% 2.22/0.67  fof(f88,plain,(
% 2.22/0.67    ( ! [X2,X0,X1] : (~v3_funct_2(X2,X0,X1) | v2_funct_2(X2,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.22/0.67    inference(cnf_transformation,[],[f43])).
% 2.22/0.67  fof(f224,plain,(
% 2.22/0.67    k5_relat_1(k2_funct_1(sK1),sK1) = k6_relat_1(k2_relat_1(sK1)) | ~v1_relat_1(sK1)),
% 2.22/0.67    inference(resolution,[],[f124,f127])).
% 2.22/0.67  fof(f124,plain,(
% 2.22/0.67    ~v2_funct_1(sK1) | k5_relat_1(k2_funct_1(sK1),sK1) = k6_relat_1(k2_relat_1(sK1)) | ~v1_relat_1(sK1)),
% 2.22/0.67    inference(resolution,[],[f69,f53])).
% 2.22/0.67  fof(f69,plain,(
% 2.22/0.67    ( ! [X0] : (~v1_funct_1(X0) | ~v2_funct_1(X0) | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 2.22/0.67    inference(cnf_transformation,[],[f31])).
% 2.22/0.67  fof(f226,plain,(
% 2.22/0.67    ( ! [X6,X4,X7,X5] : (k5_relat_1(k2_funct_1(sK1),sK1) = k1_partfun1(X4,X5,X6,X7,k2_funct_1(sK1),sK1) | ~m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))) )),
% 2.22/0.67    inference(resolution,[],[f179,f156])).
% 2.22/0.67  fof(f179,plain,(
% 2.22/0.67    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_1(X4) | k1_partfun1(X2,X3,X0,X1,X4,sK1) = k5_relat_1(X4,sK1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.22/0.67    inference(resolution,[],[f91,f53])).
% 2.22/0.67  fof(f158,plain,(
% 2.22/0.67    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_relat_1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_relat_1(sK0))),
% 2.22/0.67    inference(forward_demodulation,[],[f157,f155])).
% 2.22/0.67  fof(f157,plain,(
% 2.22/0.67    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_relat_1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_relat_1(sK0))),
% 2.22/0.67    inference(backward_demodulation,[],[f101,f155])).
% 2.22/0.67  fof(f101,plain,(
% 2.22/0.67    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_relat_1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_relat_1(sK0))),
% 2.22/0.67    inference(forward_demodulation,[],[f100,f59])).
% 2.22/0.67  fof(f100,plain,(
% 2.22/0.67    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_relat_1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))),
% 2.22/0.67    inference(forward_demodulation,[],[f57,f59])).
% 2.22/0.67  fof(f57,plain,(
% 2.22/0.67    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))),
% 2.22/0.67    inference(cnf_transformation,[],[f49])).
% 2.22/0.67  fof(f414,plain,(
% 2.22/0.67    k1_xboole_0 != sK0 | k1_xboole_0 = sK1),
% 2.22/0.67    inference(superposition,[],[f275,f281])).
% 2.22/0.67  fof(f275,plain,(
% 2.22/0.67    k1_xboole_0 != k2_relat_1(sK1) | k1_xboole_0 = sK1),
% 2.22/0.67    inference(resolution,[],[f256,f66])).
% 2.22/0.67  fof(f66,plain,(
% 2.22/0.67    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0) | k1_xboole_0 = X0) )),
% 2.22/0.67    inference(cnf_transformation,[],[f28])).
% 2.22/0.67  fof(f1215,plain,(
% 2.22/0.67    ~r2_relset_1(k1_xboole_0,k1_xboole_0,k6_relat_1(k1_relat_1(sK1)),k1_xboole_0)),
% 2.22/0.67    inference(forward_demodulation,[],[f636,f344])).
% 2.22/0.67  fof(f636,plain,(
% 2.22/0.67    ~r2_relset_1(k1_xboole_0,k1_xboole_0,k6_relat_1(k1_relat_1(sK1)),k6_relat_1(k1_xboole_0))),
% 2.22/0.67    inference(backward_demodulation,[],[f566,f568])).
% 2.22/0.67  % SZS output end Proof for theBenchmark
% 2.22/0.67  % (26646)------------------------------
% 2.22/0.67  % (26646)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.22/0.67  % (26646)Termination reason: Refutation
% 2.22/0.67  
% 2.22/0.67  % (26646)Memory used [KB]: 2174
% 2.22/0.67  % (26646)Time elapsed: 0.201 s
% 2.22/0.67  % (26646)------------------------------
% 2.22/0.67  % (26646)------------------------------
% 2.22/0.67  % (26638)Success in time 0.295 s
%------------------------------------------------------------------------------
