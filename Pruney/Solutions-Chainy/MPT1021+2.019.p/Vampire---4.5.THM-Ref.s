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
% DateTime   : Thu Dec  3 13:05:52 EST 2020

% Result     : Theorem 1.58s
% Output     : Refutation 1.58s
% Verified   : 
% Statistics : Number of formulae       :  159 (3582 expanded)
%              Number of leaves         :   17 ( 846 expanded)
%              Depth                    :   43
%              Number of atoms          :  594 (18700 expanded)
%              Number of equality atoms :  149 (1201 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f562,plain,(
    $false ),
    inference(resolution,[],[f561,f98])).

fof(f98,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f64,f65])).

fof(f65,plain,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f64,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f561,plain,(
    ~ m1_subset_1(k6_relat_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(resolution,[],[f553,f106])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( r2_relset_1(X1,X2,X0,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(condensation,[],[f62])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => r2_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

fof(f553,plain,(
    ~ r2_relset_1(k1_xboole_0,k1_xboole_0,k6_relat_1(k1_xboole_0),k6_relat_1(k1_xboole_0)) ),
    inference(duplicate_literal_removal,[],[f550])).

fof(f550,plain,
    ( ~ r2_relset_1(k1_xboole_0,k1_xboole_0,k6_relat_1(k1_xboole_0),k6_relat_1(k1_xboole_0))
    | ~ r2_relset_1(k1_xboole_0,k1_xboole_0,k6_relat_1(k1_xboole_0),k6_relat_1(k1_xboole_0)) ),
    inference(backward_demodulation,[],[f493,f541])).

fof(f541,plain,(
    k1_xboole_0 = k1_relat_1(sK1) ),
    inference(resolution,[],[f540,f442])).

fof(f442,plain,(
    v1_funct_2(sK1,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f58,f440])).

fof(f440,plain,(
    k1_xboole_0 = sK0 ),
    inference(resolution,[],[f439,f98])).

fof(f439,plain,
    ( ~ m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f438,f106])).

fof(f438,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0))
    | k1_xboole_0 = sK0 ),
    inference(duplicate_literal_removal,[],[f437])).

fof(f437,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0))
    | ~ r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0))
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f436,f139])).

fof(f139,plain,
    ( sK0 = k1_relat_1(sK1)
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f136,f58])).

fof(f136,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | sK0 = k1_relat_1(sK1)
    | k1_xboole_0 = sK0 ),
    inference(forward_demodulation,[],[f133,f112])).

fof(f112,plain,(
    k1_relset_1(sK0,sK0,sK1) = k1_relat_1(sK1) ),
    inference(resolution,[],[f93,f60])).

fof(f60,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,
    ( ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) )
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v3_funct_2(sK1,sK0,sK0)
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f52])).

fof(f52,plain,
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

fof(f24,plain,(
    ? [X0,X1] :
      ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0,X1] :
      ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X1,X0,X0)
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_funct_2)).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f133,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | k1_xboole_0 = sK0
    | sK0 = k1_relset_1(sK0,sK0,sK1) ),
    inference(resolution,[],[f75,f60])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
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
    inference(nnf_transformation,[],[f37])).

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

fof(f436,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_relat_1(k1_relat_1(sK1)),k6_relat_1(sK0))
    | ~ r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0)) ),
    inference(backward_demodulation,[],[f412,f435])).

fof(f435,plain,(
    k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k6_relat_1(k1_relat_1(sK1)) ),
    inference(resolution,[],[f434,f60])).

fof(f434,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k6_relat_1(k1_relat_1(sK1)) ) ),
    inference(resolution,[],[f433,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f433,plain,
    ( ~ v1_relat_1(sK1)
    | k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k6_relat_1(k1_relat_1(sK1)) ),
    inference(resolution,[],[f432,f57])).

fof(f57,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f53])).

fof(f432,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k6_relat_1(k1_relat_1(sK1)) ),
    inference(resolution,[],[f431,f59])).

fof(f59,plain,(
    v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f53])).

fof(f431,plain,
    ( ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k6_relat_1(k1_relat_1(sK1)) ),
    inference(resolution,[],[f430,f60])).

fof(f430,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1)
      | ~ v3_funct_2(sK1,X0,X1)
      | k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k6_relat_1(k1_relat_1(sK1)) ) ),
    inference(duplicate_literal_removal,[],[f429])).

fof(f429,plain,(
    ! [X0,X1] :
      ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k6_relat_1(k1_relat_1(sK1))
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1)
      | ~ v3_funct_2(sK1,X0,X1)
      | ~ v1_funct_1(sK1)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(resolution,[],[f427,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_1(X2)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).

fof(f427,plain,
    ( ~ v2_funct_1(sK1)
    | k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k6_relat_1(k1_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(duplicate_literal_removal,[],[f426])).

fof(f426,plain,
    ( ~ v2_funct_1(sK1)
    | k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k6_relat_1(k1_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f421,f84])).

fof(f84,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f421,plain,
    ( ~ v1_funct_1(k2_funct_1(sK1))
    | ~ v2_funct_1(sK1)
    | k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k6_relat_1(k1_relat_1(sK1))
    | ~ v1_funct_1(sK1) ),
    inference(resolution,[],[f420,f58])).

fof(f420,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(k2_funct_1(sK1))
    | ~ v2_funct_1(sK1)
    | k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k6_relat_1(k1_relat_1(sK1))
    | ~ v1_funct_1(sK1) ),
    inference(resolution,[],[f367,f60])).

fof(f367,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | ~ v1_funct_1(k2_funct_1(sK1))
    | ~ v2_funct_1(sK1)
    | k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k6_relat_1(k1_relat_1(sK1))
    | ~ v1_funct_2(sK1,sK0,sK0) ),
    inference(forward_demodulation,[],[f366,f332])).

fof(f332,plain,(
    k5_relat_1(sK1,k2_funct_1(sK1)) = k6_relat_1(k1_relat_1(sK1)) ),
    inference(resolution,[],[f331,f60])).

fof(f331,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k5_relat_1(sK1,k2_funct_1(sK1)) = k6_relat_1(k1_relat_1(sK1)) ) ),
    inference(resolution,[],[f329,f68])).

fof(f329,plain,
    ( ~ v1_relat_1(sK1)
    | k5_relat_1(sK1,k2_funct_1(sK1)) = k6_relat_1(k1_relat_1(sK1)) ),
    inference(resolution,[],[f328,f57])).

fof(f328,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | k5_relat_1(sK1,k2_funct_1(sK1)) = k6_relat_1(k1_relat_1(sK1)) ),
    inference(resolution,[],[f243,f59])).

fof(f243,plain,
    ( ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | k5_relat_1(sK1,k2_funct_1(sK1)) = k6_relat_1(k1_relat_1(sK1)) ),
    inference(resolution,[],[f120,f60])).

fof(f120,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v3_funct_2(X0,X1,X2)
      | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f119])).

fof(f119,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v3_funct_2(X0,X1,X2)
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(resolution,[],[f88,f70])).

fof(f88,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

fof(f366,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k5_relat_1(sK1,k2_funct_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_funct_1(k2_funct_1(sK1))
    | ~ v2_funct_1(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK1,sK0,sK0) ),
    inference(trivial_inequality_removal,[],[f365])).

fof(f365,plain,
    ( sK0 != sK0
    | k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k5_relat_1(sK1,k2_funct_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_funct_1(k2_funct_1(sK1))
    | ~ v2_funct_1(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK1,sK0,sK0) ),
    inference(duplicate_literal_removal,[],[f364])).

fof(f364,plain,
    ( sK0 != sK0
    | k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k5_relat_1(sK1,k2_funct_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_funct_1(k2_funct_1(sK1))
    | ~ v2_funct_1(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(superposition,[],[f187,f293])).

fof(f293,plain,(
    sK0 = k2_relset_1(sK0,sK0,sK1) ),
    inference(backward_demodulation,[],[f109,f289])).

fof(f289,plain,(
    sK0 = k2_relat_1(sK1) ),
    inference(resolution,[],[f286,f60])).

fof(f286,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sK0 = k2_relat_1(sK1) ) ),
    inference(resolution,[],[f285,f68])).

fof(f285,plain,
    ( ~ v1_relat_1(sK1)
    | sK0 = k2_relat_1(sK1) ),
    inference(resolution,[],[f282,f57])).

fof(f282,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | sK0 = k2_relat_1(sK1) ),
    inference(resolution,[],[f277,f60])).

fof(f277,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1)
      | sK0 = k2_relat_1(sK1) ) ),
    inference(resolution,[],[f276,f96])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f276,plain,
    ( ~ v5_relat_1(sK1,sK0)
    | sK0 = k2_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f220,f59])).

fof(f220,plain,
    ( ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | sK0 = k2_relat_1(sK1)
    | ~ v5_relat_1(sK1,sK0)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f123,f60])).

fof(f123,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X0)
      | ~ v3_funct_2(X0,X1,X2)
      | k2_relat_1(X0) = X2
      | ~ v5_relat_1(X0,X2)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f71,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_2(X1,X0)
      | k2_relat_1(X1) = X0
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_2(X2,X1)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f109,plain,(
    k2_relset_1(sK0,sK0,sK1) = k2_relat_1(sK1) ),
    inference(resolution,[],[f92,f60])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f187,plain,(
    ! [X4,X2,X3] :
      ( k2_relset_1(X4,X3,X2) != X3
      | k1_partfun1(sK0,sK0,X3,X4,sK1,k2_funct_1(X2)) = k5_relat_1(sK1,k2_funct_1(X2))
      | ~ v1_funct_1(sK1)
      | ~ v1_funct_1(k2_funct_1(X2))
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X4,X3)))
      | ~ v1_funct_2(X2,X4,X3)
      | ~ v1_funct_1(X2) ) ),
    inference(resolution,[],[f167,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
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

fof(f167,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X0)
      | k1_partfun1(sK0,sK0,X1,X2,sK1,X0) = k5_relat_1(sK1,X0)
      | ~ v1_funct_1(sK1) ) ),
    inference(resolution,[],[f66,f60])).

fof(f66,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f412,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_relat_1(sK0))
    | ~ r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0)) ),
    inference(backward_demodulation,[],[f157,f411])).

fof(f411,plain,(
    k6_relat_1(sK0) = k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) ),
    inference(resolution,[],[f410,f60])).

fof(f410,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k6_relat_1(sK0) = k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) ) ),
    inference(resolution,[],[f409,f68])).

fof(f409,plain,
    ( ~ v1_relat_1(sK1)
    | k6_relat_1(sK0) = k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) ),
    inference(resolution,[],[f408,f57])).

fof(f408,plain,
    ( ~ v1_funct_1(sK1)
    | k6_relat_1(sK0) = k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f407,f59])).

fof(f407,plain,
    ( ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_relat_1(sK1)
    | k6_relat_1(sK0) = k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1)
    | ~ v1_funct_1(sK1) ),
    inference(resolution,[],[f406,f60])).

fof(f406,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k6_relat_1(sK0) = k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1)
      | ~ v1_relat_1(sK1)
      | ~ v3_funct_2(sK1,X0,X1)
      | ~ v1_funct_1(sK1) ) ),
    inference(duplicate_literal_removal,[],[f405])).

fof(f405,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(sK1)
      | k6_relat_1(sK0) = k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1)
      | ~ v1_relat_1(sK1)
      | ~ v3_funct_2(sK1,X0,X1)
      | ~ v1_funct_1(sK1)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(resolution,[],[f403,f70])).

fof(f403,plain,
    ( ~ v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | k6_relat_1(sK0) = k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1)
    | ~ v1_relat_1(sK1) ),
    inference(duplicate_literal_removal,[],[f402])).

fof(f402,plain,
    ( ~ v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | k6_relat_1(sK0) = k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f398,f84])).

fof(f398,plain,
    ( ~ v1_funct_1(k2_funct_1(sK1))
    | ~ v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | k6_relat_1(sK0) = k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) ),
    inference(resolution,[],[f397,f58])).

fof(f397,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | k6_relat_1(sK0) = k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1)
    | ~ v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_funct_1(k2_funct_1(sK1)) ),
    inference(resolution,[],[f360,f60])).

fof(f360,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v2_funct_1(sK1)
    | k6_relat_1(sK0) = k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ v1_funct_1(k2_funct_1(sK1)) ),
    inference(forward_demodulation,[],[f359,f338])).

fof(f338,plain,(
    k6_relat_1(sK0) = k5_relat_1(k2_funct_1(sK1),sK1) ),
    inference(resolution,[],[f336,f60])).

fof(f336,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k6_relat_1(sK0) = k5_relat_1(k2_funct_1(sK1),sK1) ) ),
    inference(resolution,[],[f335,f68])).

fof(f335,plain,
    ( ~ v1_relat_1(sK1)
    | k6_relat_1(sK0) = k5_relat_1(k2_funct_1(sK1),sK1) ),
    inference(resolution,[],[f333,f57])).

fof(f333,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | k6_relat_1(sK0) = k5_relat_1(k2_funct_1(sK1),sK1) ),
    inference(resolution,[],[f330,f59])).

fof(f330,plain,
    ( ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | k6_relat_1(sK0) = k5_relat_1(k2_funct_1(sK1),sK1) ),
    inference(forward_demodulation,[],[f253,f289])).

fof(f253,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ v3_funct_2(sK1,sK0,sK0)
    | k5_relat_1(k2_funct_1(sK1),sK1) = k6_relat_1(k2_relat_1(sK1)) ),
    inference(resolution,[],[f122,f60])).

fof(f122,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v3_funct_2(X0,X1,X2)
      | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f121])).

fof(f121,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v3_funct_2(X0,X1,X2)
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(resolution,[],[f89,f70])).

fof(f89,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f359,plain,
    ( ~ v2_funct_1(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k5_relat_1(k2_funct_1(sK1),sK1)
    | ~ v1_funct_1(k2_funct_1(sK1)) ),
    inference(trivial_inequality_removal,[],[f358])).

fof(f358,plain,
    ( sK0 != sK0
    | ~ v2_funct_1(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k5_relat_1(k2_funct_1(sK1),sK1)
    | ~ v1_funct_1(k2_funct_1(sK1)) ),
    inference(duplicate_literal_removal,[],[f357])).

fof(f357,plain,
    ( sK0 != sK0
    | ~ v2_funct_1(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k5_relat_1(k2_funct_1(sK1),sK1)
    | ~ v1_funct_1(k2_funct_1(sK1)) ),
    inference(superposition,[],[f177,f293])).

fof(f177,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_1(sK1)
      | k1_partfun1(X1,X0,sK0,sK0,k2_funct_1(X2),sK1) = k5_relat_1(k2_funct_1(X2),sK1)
      | ~ v1_funct_1(k2_funct_1(X2)) ) ),
    inference(resolution,[],[f74,f164])).

fof(f164,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(sK1)
      | k1_partfun1(X1,X2,sK0,sK0,X0,sK1) = k5_relat_1(X0,sK1)
      | ~ v1_funct_1(X0) ) ),
    inference(resolution,[],[f66,f60])).

fof(f157,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_relat_1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f156,f155])).

fof(f155,plain,(
    k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    inference(resolution,[],[f154,f57])).

fof(f154,plain,
    ( ~ v1_funct_1(sK1)
    | k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    inference(resolution,[],[f151,f59])).

fof(f151,plain,
    ( ~ v3_funct_2(sK1,sK0,sK0)
    | k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ v1_funct_1(sK1) ),
    inference(resolution,[],[f148,f58])).

fof(f148,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v3_funct_2(sK1,sK0,sK0)
    | k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ v1_funct_1(sK1) ),
    inference(resolution,[],[f67,f60])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

fof(f156,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_relat_1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_relat_1(sK0)) ),
    inference(backward_demodulation,[],[f97,f155])).

fof(f97,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_relat_1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_relat_1(sK0)) ),
    inference(definition_unfolding,[],[f61,f65,f65])).

fof(f61,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f53])).

fof(f58,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f53])).

fof(f540,plain,
    ( ~ v1_funct_2(sK1,k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_relat_1(sK1) ),
    inference(forward_demodulation,[],[f499,f445])).

fof(f445,plain,(
    k1_relat_1(sK1) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK1) ),
    inference(backward_demodulation,[],[f112,f440])).

fof(f499,plain,
    ( ~ v1_funct_2(sK1,k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK1) ),
    inference(resolution,[],[f444,f104])).

fof(f104,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) ) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f444,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f60,f440])).

fof(f493,plain,
    ( ~ r2_relset_1(k1_xboole_0,k1_xboole_0,k6_relat_1(k1_relat_1(sK1)),k6_relat_1(k1_xboole_0))
    | ~ r2_relset_1(k1_xboole_0,k1_xboole_0,k6_relat_1(k1_xboole_0),k6_relat_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f476,f440])).

fof(f476,plain,
    ( ~ r2_relset_1(k1_xboole_0,k1_xboole_0,k6_relat_1(k1_xboole_0),k6_relat_1(k1_xboole_0))
    | ~ r2_relset_1(sK0,sK0,k6_relat_1(k1_relat_1(sK1)),k6_relat_1(sK0)) ),
    inference(backward_demodulation,[],[f436,f440])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:06:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.51  % (13687)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.52  % (13679)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.52  % (13667)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.52  % (13668)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.52  % (13687)Refutation not found, incomplete strategy% (13687)------------------------------
% 0.22/0.52  % (13687)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (13679)Refutation not found, incomplete strategy% (13679)------------------------------
% 0.22/0.52  % (13679)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (13671)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.53  % (13692)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.53  % (13662)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.53  % (13679)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (13679)Memory used [KB]: 10746
% 0.22/0.53  % (13679)Time elapsed: 0.107 s
% 0.22/0.53  % (13679)------------------------------
% 0.22/0.53  % (13679)------------------------------
% 0.22/0.53  % (13678)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.53  % (13687)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (13687)Memory used [KB]: 10746
% 0.22/0.53  % (13687)Time elapsed: 0.110 s
% 0.22/0.53  % (13687)------------------------------
% 0.22/0.53  % (13687)------------------------------
% 0.22/0.53  % (13684)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.54  % (13663)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.54  % (13682)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.54  % (13666)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.54  % (13670)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.54  % (13676)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.54  % (13686)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.54  % (13688)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.55  % (13665)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.55  % (13690)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.55  % (13691)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.55  % (13681)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.36/0.55  % (13680)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.36/0.55  % (13689)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.36/0.56  % (13683)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.36/0.56  % (13672)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.36/0.56  % (13669)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.36/0.56  % (13674)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.36/0.56  % (13675)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.36/0.56  % (13675)Refutation not found, incomplete strategy% (13675)------------------------------
% 1.36/0.56  % (13675)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.56  % (13675)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.56  
% 1.36/0.56  % (13675)Memory used [KB]: 10746
% 1.36/0.56  % (13675)Time elapsed: 0.150 s
% 1.36/0.56  % (13675)------------------------------
% 1.36/0.56  % (13675)------------------------------
% 1.58/0.57  % (13673)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.58/0.57  % (13668)Refutation found. Thanks to Tanya!
% 1.58/0.57  % SZS status Theorem for theBenchmark
% 1.58/0.57  % SZS output start Proof for theBenchmark
% 1.58/0.57  fof(f562,plain,(
% 1.58/0.57    $false),
% 1.58/0.57    inference(resolution,[],[f561,f98])).
% 1.58/0.57  fof(f98,plain,(
% 1.58/0.57    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.58/0.57    inference(definition_unfolding,[],[f64,f65])).
% 1.58/0.57  fof(f65,plain,(
% 1.58/0.57    ( ! [X0] : (k6_partfun1(X0) = k6_relat_1(X0)) )),
% 1.58/0.57    inference(cnf_transformation,[],[f19])).
% 1.58/0.57  fof(f19,axiom,(
% 1.58/0.57    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0)),
% 1.58/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.58/0.57  fof(f64,plain,(
% 1.58/0.57    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.58/0.57    inference(cnf_transformation,[],[f16])).
% 1.58/0.57  fof(f16,axiom,(
% 1.58/0.57    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 1.58/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 1.58/0.57  fof(f561,plain,(
% 1.58/0.57    ~m1_subset_1(k6_relat_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 1.58/0.57    inference(resolution,[],[f553,f106])).
% 1.58/0.57  fof(f106,plain,(
% 1.58/0.57    ( ! [X2,X0,X1] : (r2_relset_1(X1,X2,X0,X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 1.58/0.57    inference(condensation,[],[f62])).
% 1.58/0.57  fof(f62,plain,(
% 1.58/0.57    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.58/0.57    inference(cnf_transformation,[],[f26])).
% 1.58/0.57  fof(f26,plain,(
% 1.58/0.57    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.58/0.57    inference(flattening,[],[f25])).
% 1.58/0.57  fof(f25,plain,(
% 1.58/0.57    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.58/0.57    inference(ennf_transformation,[],[f12])).
% 1.58/0.57  fof(f12,axiom,(
% 1.58/0.57    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => r2_relset_1(X0,X1,X2,X2))),
% 1.58/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).
% 1.58/0.57  fof(f553,plain,(
% 1.58/0.57    ~r2_relset_1(k1_xboole_0,k1_xboole_0,k6_relat_1(k1_xboole_0),k6_relat_1(k1_xboole_0))),
% 1.58/0.57    inference(duplicate_literal_removal,[],[f550])).
% 1.58/0.57  fof(f550,plain,(
% 1.58/0.57    ~r2_relset_1(k1_xboole_0,k1_xboole_0,k6_relat_1(k1_xboole_0),k6_relat_1(k1_xboole_0)) | ~r2_relset_1(k1_xboole_0,k1_xboole_0,k6_relat_1(k1_xboole_0),k6_relat_1(k1_xboole_0))),
% 1.58/0.57    inference(backward_demodulation,[],[f493,f541])).
% 1.58/0.57  fof(f541,plain,(
% 1.58/0.57    k1_xboole_0 = k1_relat_1(sK1)),
% 1.58/0.57    inference(resolution,[],[f540,f442])).
% 1.58/0.57  fof(f442,plain,(
% 1.58/0.57    v1_funct_2(sK1,k1_xboole_0,k1_xboole_0)),
% 1.58/0.57    inference(backward_demodulation,[],[f58,f440])).
% 1.58/0.57  fof(f440,plain,(
% 1.58/0.57    k1_xboole_0 = sK0),
% 1.58/0.57    inference(resolution,[],[f439,f98])).
% 1.58/0.57  fof(f439,plain,(
% 1.58/0.57    ~m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k1_xboole_0 = sK0),
% 1.58/0.57    inference(resolution,[],[f438,f106])).
% 1.58/0.57  fof(f438,plain,(
% 1.58/0.57    ~r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0)) | k1_xboole_0 = sK0),
% 1.58/0.57    inference(duplicate_literal_removal,[],[f437])).
% 1.58/0.57  fof(f437,plain,(
% 1.58/0.57    ~r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0)) | ~r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0)) | k1_xboole_0 = sK0),
% 1.58/0.57    inference(superposition,[],[f436,f139])).
% 1.58/0.57  fof(f139,plain,(
% 1.58/0.57    sK0 = k1_relat_1(sK1) | k1_xboole_0 = sK0),
% 1.58/0.57    inference(resolution,[],[f136,f58])).
% 1.58/0.57  fof(f136,plain,(
% 1.58/0.57    ~v1_funct_2(sK1,sK0,sK0) | sK0 = k1_relat_1(sK1) | k1_xboole_0 = sK0),
% 1.58/0.57    inference(forward_demodulation,[],[f133,f112])).
% 1.58/0.57  fof(f112,plain,(
% 1.58/0.57    k1_relset_1(sK0,sK0,sK1) = k1_relat_1(sK1)),
% 1.58/0.57    inference(resolution,[],[f93,f60])).
% 1.58/0.57  fof(f60,plain,(
% 1.58/0.57    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.58/0.57    inference(cnf_transformation,[],[f53])).
% 1.58/0.57  fof(f53,plain,(
% 1.58/0.57    (~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 1.58/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f52])).
% 1.58/0.57  fof(f52,plain,(
% 1.58/0.57    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ((~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 1.58/0.57    introduced(choice_axiom,[])).
% 1.58/0.57  fof(f24,plain,(
% 1.58/0.57    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 1.58/0.57    inference(flattening,[],[f23])).
% 1.58/0.57  fof(f23,plain,(
% 1.58/0.57    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 1.58/0.57    inference(ennf_transformation,[],[f22])).
% 1.58/0.57  fof(f22,negated_conjecture,(
% 1.58/0.57    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 1.58/0.57    inference(negated_conjecture,[],[f21])).
% 1.58/0.57  fof(f21,conjecture,(
% 1.58/0.57    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 1.58/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_funct_2)).
% 1.58/0.57  fof(f93,plain,(
% 1.58/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.58/0.57    inference(cnf_transformation,[],[f50])).
% 1.58/0.57  fof(f50,plain,(
% 1.58/0.57    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.58/0.57    inference(ennf_transformation,[],[f10])).
% 1.58/0.57  fof(f10,axiom,(
% 1.58/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.58/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.58/0.57  fof(f133,plain,(
% 1.58/0.57    ~v1_funct_2(sK1,sK0,sK0) | k1_xboole_0 = sK0 | sK0 = k1_relset_1(sK0,sK0,sK1)),
% 1.58/0.57    inference(resolution,[],[f75,f60])).
% 1.58/0.57  fof(f75,plain,(
% 1.58/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 1.58/0.57    inference(cnf_transformation,[],[f54])).
% 1.58/0.57  fof(f54,plain,(
% 1.58/0.57    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.58/0.57    inference(nnf_transformation,[],[f37])).
% 1.58/0.57  fof(f37,plain,(
% 1.58/0.57    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.58/0.57    inference(flattening,[],[f36])).
% 1.58/0.57  fof(f36,plain,(
% 1.58/0.57    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.58/0.57    inference(ennf_transformation,[],[f14])).
% 1.58/0.57  fof(f14,axiom,(
% 1.58/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.58/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.58/0.57  fof(f436,plain,(
% 1.58/0.57    ~r2_relset_1(sK0,sK0,k6_relat_1(k1_relat_1(sK1)),k6_relat_1(sK0)) | ~r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0))),
% 1.58/0.57    inference(backward_demodulation,[],[f412,f435])).
% 1.58/0.57  fof(f435,plain,(
% 1.58/0.57    k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k6_relat_1(k1_relat_1(sK1))),
% 1.58/0.57    inference(resolution,[],[f434,f60])).
% 1.58/0.57  fof(f434,plain,(
% 1.58/0.57    ( ! [X0,X1] : (~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k6_relat_1(k1_relat_1(sK1))) )),
% 1.58/0.57    inference(resolution,[],[f433,f68])).
% 1.58/0.57  fof(f68,plain,(
% 1.58/0.57    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.58/0.57    inference(cnf_transformation,[],[f31])).
% 1.58/0.57  fof(f31,plain,(
% 1.58/0.57    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.58/0.57    inference(ennf_transformation,[],[f8])).
% 1.58/0.57  fof(f8,axiom,(
% 1.58/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.58/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.58/0.57  fof(f433,plain,(
% 1.58/0.57    ~v1_relat_1(sK1) | k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k6_relat_1(k1_relat_1(sK1))),
% 1.58/0.57    inference(resolution,[],[f432,f57])).
% 1.58/0.57  fof(f57,plain,(
% 1.58/0.57    v1_funct_1(sK1)),
% 1.58/0.57    inference(cnf_transformation,[],[f53])).
% 1.58/0.57  fof(f432,plain,(
% 1.58/0.57    ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k6_relat_1(k1_relat_1(sK1))),
% 1.58/0.57    inference(resolution,[],[f431,f59])).
% 1.58/0.57  fof(f59,plain,(
% 1.58/0.57    v3_funct_2(sK1,sK0,sK0)),
% 1.58/0.57    inference(cnf_transformation,[],[f53])).
% 1.58/0.57  fof(f431,plain,(
% 1.58/0.57    ~v3_funct_2(sK1,sK0,sK0) | ~v1_relat_1(sK1) | ~v1_funct_1(sK1) | k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k6_relat_1(k1_relat_1(sK1))),
% 1.58/0.57    inference(resolution,[],[f430,f60])).
% 1.58/0.57  fof(f430,plain,(
% 1.58/0.57    ( ! [X0,X1] : (~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~v3_funct_2(sK1,X0,X1) | k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k6_relat_1(k1_relat_1(sK1))) )),
% 1.58/0.57    inference(duplicate_literal_removal,[],[f429])).
% 1.58/0.57  fof(f429,plain,(
% 1.58/0.57    ( ! [X0,X1] : (k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k6_relat_1(k1_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~v3_funct_2(sK1,X0,X1) | ~v1_funct_1(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.58/0.57    inference(resolution,[],[f427,f70])).
% 1.58/0.57  fof(f70,plain,(
% 1.58/0.57    ( ! [X2,X0,X1] : (v2_funct_1(X2) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.58/0.57    inference(cnf_transformation,[],[f33])).
% 1.58/0.57  fof(f33,plain,(
% 1.58/0.57    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.58/0.57    inference(flattening,[],[f32])).
% 1.58/0.57  fof(f32,plain,(
% 1.58/0.57    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.58/0.57    inference(ennf_transformation,[],[f13])).
% 1.58/0.57  fof(f13,axiom,(
% 1.58/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 1.58/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).
% 1.58/0.57  fof(f427,plain,(
% 1.58/0.57    ~v2_funct_1(sK1) | k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k6_relat_1(k1_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)),
% 1.58/0.57    inference(duplicate_literal_removal,[],[f426])).
% 1.58/0.57  fof(f426,plain,(
% 1.58/0.57    ~v2_funct_1(sK1) | k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k6_relat_1(k1_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)),
% 1.58/0.57    inference(resolution,[],[f421,f84])).
% 1.58/0.57  fof(f84,plain,(
% 1.58/0.57    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.58/0.57    inference(cnf_transformation,[],[f41])).
% 1.58/0.57  fof(f41,plain,(
% 1.58/0.57    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.58/0.57    inference(flattening,[],[f40])).
% 1.58/0.57  fof(f40,plain,(
% 1.58/0.57    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.58/0.57    inference(ennf_transformation,[],[f5])).
% 1.58/0.57  fof(f5,axiom,(
% 1.58/0.57    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 1.58/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 1.58/0.57  fof(f421,plain,(
% 1.58/0.57    ~v1_funct_1(k2_funct_1(sK1)) | ~v2_funct_1(sK1) | k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k6_relat_1(k1_relat_1(sK1)) | ~v1_funct_1(sK1)),
% 1.58/0.57    inference(resolution,[],[f420,f58])).
% 1.58/0.57  fof(f420,plain,(
% 1.58/0.57    ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(k2_funct_1(sK1)) | ~v2_funct_1(sK1) | k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k6_relat_1(k1_relat_1(sK1)) | ~v1_funct_1(sK1)),
% 1.58/0.57    inference(resolution,[],[f367,f60])).
% 1.58/0.57  fof(f367,plain,(
% 1.58/0.57    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1) | ~v1_funct_1(k2_funct_1(sK1)) | ~v2_funct_1(sK1) | k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k6_relat_1(k1_relat_1(sK1)) | ~v1_funct_2(sK1,sK0,sK0)),
% 1.58/0.57    inference(forward_demodulation,[],[f366,f332])).
% 1.58/0.57  fof(f332,plain,(
% 1.58/0.57    k5_relat_1(sK1,k2_funct_1(sK1)) = k6_relat_1(k1_relat_1(sK1))),
% 1.58/0.57    inference(resolution,[],[f331,f60])).
% 1.58/0.57  fof(f331,plain,(
% 1.58/0.57    ( ! [X0,X1] : (~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k5_relat_1(sK1,k2_funct_1(sK1)) = k6_relat_1(k1_relat_1(sK1))) )),
% 1.58/0.57    inference(resolution,[],[f329,f68])).
% 1.58/0.57  fof(f329,plain,(
% 1.58/0.57    ~v1_relat_1(sK1) | k5_relat_1(sK1,k2_funct_1(sK1)) = k6_relat_1(k1_relat_1(sK1))),
% 1.58/0.57    inference(resolution,[],[f328,f57])).
% 1.58/0.57  fof(f328,plain,(
% 1.58/0.57    ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | k5_relat_1(sK1,k2_funct_1(sK1)) = k6_relat_1(k1_relat_1(sK1))),
% 1.58/0.57    inference(resolution,[],[f243,f59])).
% 1.58/0.57  fof(f243,plain,(
% 1.58/0.57    ~v3_funct_2(sK1,sK0,sK0) | ~v1_relat_1(sK1) | ~v1_funct_1(sK1) | k5_relat_1(sK1,k2_funct_1(sK1)) = k6_relat_1(k1_relat_1(sK1))),
% 1.58/0.57    inference(resolution,[],[f120,f60])).
% 1.58/0.57  fof(f120,plain,(
% 1.58/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v3_funct_2(X0,X1,X2) | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) )),
% 1.58/0.57    inference(duplicate_literal_removal,[],[f119])).
% 1.58/0.57  fof(f119,plain,(
% 1.58/0.57    ( ! [X2,X0,X1] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v3_funct_2(X0,X1,X2) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 1.58/0.57    inference(resolution,[],[f88,f70])).
% 1.58/0.57  fof(f88,plain,(
% 1.58/0.57    ( ! [X0] : (~v2_funct_1(X0) | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.58/0.57    inference(cnf_transformation,[],[f46])).
% 1.58/0.57  fof(f46,plain,(
% 1.58/0.57    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.58/0.57    inference(flattening,[],[f45])).
% 1.58/0.57  fof(f45,plain,(
% 1.58/0.57    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.58/0.57    inference(ennf_transformation,[],[f7])).
% 1.58/0.57  fof(f7,axiom,(
% 1.58/0.57    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 1.58/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).
% 1.58/0.57  fof(f366,plain,(
% 1.58/0.57    k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k5_relat_1(sK1,k2_funct_1(sK1)) | ~v1_funct_1(sK1) | ~v1_funct_1(k2_funct_1(sK1)) | ~v2_funct_1(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0)),
% 1.58/0.57    inference(trivial_inequality_removal,[],[f365])).
% 1.58/0.57  fof(f365,plain,(
% 1.58/0.57    sK0 != sK0 | k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k5_relat_1(sK1,k2_funct_1(sK1)) | ~v1_funct_1(sK1) | ~v1_funct_1(k2_funct_1(sK1)) | ~v2_funct_1(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0)),
% 1.58/0.57    inference(duplicate_literal_removal,[],[f364])).
% 1.58/0.57  fof(f364,plain,(
% 1.58/0.57    sK0 != sK0 | k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k5_relat_1(sK1,k2_funct_1(sK1)) | ~v1_funct_1(sK1) | ~v1_funct_1(k2_funct_1(sK1)) | ~v2_funct_1(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 1.58/0.57    inference(superposition,[],[f187,f293])).
% 1.58/0.57  fof(f293,plain,(
% 1.58/0.57    sK0 = k2_relset_1(sK0,sK0,sK1)),
% 1.58/0.57    inference(backward_demodulation,[],[f109,f289])).
% 1.58/0.57  fof(f289,plain,(
% 1.58/0.57    sK0 = k2_relat_1(sK1)),
% 1.58/0.57    inference(resolution,[],[f286,f60])).
% 1.58/0.57  fof(f286,plain,(
% 1.58/0.57    ( ! [X0,X1] : (~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sK0 = k2_relat_1(sK1)) )),
% 1.58/0.57    inference(resolution,[],[f285,f68])).
% 1.58/0.57  fof(f285,plain,(
% 1.58/0.57    ~v1_relat_1(sK1) | sK0 = k2_relat_1(sK1)),
% 1.58/0.57    inference(resolution,[],[f282,f57])).
% 1.58/0.57  fof(f282,plain,(
% 1.58/0.57    ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | sK0 = k2_relat_1(sK1)),
% 1.58/0.57    inference(resolution,[],[f277,f60])).
% 1.58/0.57  fof(f277,plain,(
% 1.58/0.57    ( ! [X0] : (~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | sK0 = k2_relat_1(sK1)) )),
% 1.58/0.57    inference(resolution,[],[f276,f96])).
% 1.58/0.57  fof(f96,plain,(
% 1.58/0.57    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.58/0.57    inference(cnf_transformation,[],[f51])).
% 1.58/0.57  fof(f51,plain,(
% 1.58/0.57    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.58/0.57    inference(ennf_transformation,[],[f9])).
% 1.58/0.57  fof(f9,axiom,(
% 1.58/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.58/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.58/0.57  fof(f276,plain,(
% 1.58/0.57    ~v5_relat_1(sK1,sK0) | sK0 = k2_relat_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)),
% 1.58/0.57    inference(resolution,[],[f220,f59])).
% 1.58/0.57  fof(f220,plain,(
% 1.58/0.57    ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | sK0 = k2_relat_1(sK1) | ~v5_relat_1(sK1,sK0) | ~v1_relat_1(sK1)),
% 1.58/0.57    inference(resolution,[],[f123,f60])).
% 1.58/0.57  fof(f123,plain,(
% 1.58/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X0) | ~v3_funct_2(X0,X1,X2) | k2_relat_1(X0) = X2 | ~v5_relat_1(X0,X2) | ~v1_relat_1(X0)) )),
% 1.58/0.57    inference(resolution,[],[f71,f90])).
% 1.58/0.57  fof(f90,plain,(
% 1.58/0.57    ( ! [X0,X1] : (~v2_funct_2(X1,X0) | k2_relat_1(X1) = X0 | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.58/0.57    inference(cnf_transformation,[],[f56])).
% 1.58/0.57  fof(f56,plain,(
% 1.58/0.57    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.58/0.57    inference(nnf_transformation,[],[f48])).
% 1.58/0.57  fof(f48,plain,(
% 1.58/0.57    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.58/0.57    inference(flattening,[],[f47])).
% 1.58/0.57  fof(f47,plain,(
% 1.58/0.57    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.58/0.57    inference(ennf_transformation,[],[f15])).
% 1.58/0.57  fof(f15,axiom,(
% 1.58/0.57    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 1.58/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).
% 1.58/0.57  fof(f71,plain,(
% 1.58/0.57    ( ! [X2,X0,X1] : (v2_funct_2(X2,X1) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.58/0.57    inference(cnf_transformation,[],[f33])).
% 1.58/0.57  fof(f109,plain,(
% 1.58/0.57    k2_relset_1(sK0,sK0,sK1) = k2_relat_1(sK1)),
% 1.58/0.57    inference(resolution,[],[f92,f60])).
% 1.58/0.57  fof(f92,plain,(
% 1.58/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 1.58/0.57    inference(cnf_transformation,[],[f49])).
% 1.58/0.57  fof(f49,plain,(
% 1.58/0.57    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.58/0.57    inference(ennf_transformation,[],[f11])).
% 1.58/0.57  fof(f11,axiom,(
% 1.58/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.58/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.58/0.57  fof(f187,plain,(
% 1.58/0.57    ( ! [X4,X2,X3] : (k2_relset_1(X4,X3,X2) != X3 | k1_partfun1(sK0,sK0,X3,X4,sK1,k2_funct_1(X2)) = k5_relat_1(sK1,k2_funct_1(X2)) | ~v1_funct_1(sK1) | ~v1_funct_1(k2_funct_1(X2)) | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X4,X3))) | ~v1_funct_2(X2,X4,X3) | ~v1_funct_1(X2)) )),
% 1.58/0.57    inference(resolution,[],[f167,f74])).
% 1.58/0.57  fof(f74,plain,(
% 1.58/0.57    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.58/0.57    inference(cnf_transformation,[],[f35])).
% 1.58/0.57  fof(f35,plain,(
% 1.58/0.57    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.58/0.57    inference(flattening,[],[f34])).
% 1.58/0.57  fof(f34,plain,(
% 1.58/0.57    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.58/0.57    inference(ennf_transformation,[],[f20])).
% 1.58/0.57  fof(f20,axiom,(
% 1.58/0.57    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 1.58/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).
% 1.58/0.57  fof(f167,plain,(
% 1.58/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X0) | k1_partfun1(sK0,sK0,X1,X2,sK1,X0) = k5_relat_1(sK1,X0) | ~v1_funct_1(sK1)) )),
% 1.58/0.57    inference(resolution,[],[f66,f60])).
% 1.58/0.57  fof(f66,plain,(
% 1.58/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~v1_funct_1(X4)) )),
% 1.58/0.57    inference(cnf_transformation,[],[f28])).
% 1.58/0.57  fof(f28,plain,(
% 1.58/0.57    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.58/0.57    inference(flattening,[],[f27])).
% 1.58/0.57  fof(f27,plain,(
% 1.58/0.57    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.58/0.57    inference(ennf_transformation,[],[f17])).
% 1.58/0.57  fof(f17,axiom,(
% 1.58/0.57    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 1.58/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 1.58/0.57  fof(f412,plain,(
% 1.58/0.57    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_relat_1(sK0)) | ~r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0))),
% 1.58/0.57    inference(backward_demodulation,[],[f157,f411])).
% 1.58/0.57  fof(f411,plain,(
% 1.58/0.57    k6_relat_1(sK0) = k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1)),
% 1.58/0.57    inference(resolution,[],[f410,f60])).
% 1.58/0.57  fof(f410,plain,(
% 1.58/0.57    ( ! [X0,X1] : (~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k6_relat_1(sK0) = k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1)) )),
% 1.58/0.57    inference(resolution,[],[f409,f68])).
% 1.58/0.57  fof(f409,plain,(
% 1.58/0.57    ~v1_relat_1(sK1) | k6_relat_1(sK0) = k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1)),
% 1.58/0.57    inference(resolution,[],[f408,f57])).
% 1.58/0.57  fof(f408,plain,(
% 1.58/0.57    ~v1_funct_1(sK1) | k6_relat_1(sK0) = k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) | ~v1_relat_1(sK1)),
% 1.58/0.57    inference(resolution,[],[f407,f59])).
% 1.58/0.57  fof(f407,plain,(
% 1.58/0.57    ~v3_funct_2(sK1,sK0,sK0) | ~v1_relat_1(sK1) | k6_relat_1(sK0) = k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) | ~v1_funct_1(sK1)),
% 1.58/0.57    inference(resolution,[],[f406,f60])).
% 1.58/0.57  fof(f406,plain,(
% 1.58/0.57    ( ! [X0,X1] : (~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k6_relat_1(sK0) = k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) | ~v1_relat_1(sK1) | ~v3_funct_2(sK1,X0,X1) | ~v1_funct_1(sK1)) )),
% 1.58/0.57    inference(duplicate_literal_removal,[],[f405])).
% 1.58/0.57  fof(f405,plain,(
% 1.58/0.57    ( ! [X0,X1] : (~v1_funct_1(sK1) | k6_relat_1(sK0) = k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) | ~v1_relat_1(sK1) | ~v3_funct_2(sK1,X0,X1) | ~v1_funct_1(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.58/0.57    inference(resolution,[],[f403,f70])).
% 1.58/0.57  fof(f403,plain,(
% 1.58/0.57    ~v2_funct_1(sK1) | ~v1_funct_1(sK1) | k6_relat_1(sK0) = k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) | ~v1_relat_1(sK1)),
% 1.58/0.57    inference(duplicate_literal_removal,[],[f402])).
% 1.58/0.57  fof(f402,plain,(
% 1.58/0.57    ~v2_funct_1(sK1) | ~v1_funct_1(sK1) | k6_relat_1(sK0) = k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)),
% 1.58/0.57    inference(resolution,[],[f398,f84])).
% 1.58/0.57  fof(f398,plain,(
% 1.58/0.57    ~v1_funct_1(k2_funct_1(sK1)) | ~v2_funct_1(sK1) | ~v1_funct_1(sK1) | k6_relat_1(sK0) = k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1)),
% 1.58/0.57    inference(resolution,[],[f397,f58])).
% 1.58/0.57  fof(f397,plain,(
% 1.58/0.57    ~v1_funct_2(sK1,sK0,sK0) | k6_relat_1(sK0) = k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) | ~v2_funct_1(sK1) | ~v1_funct_1(sK1) | ~v1_funct_1(k2_funct_1(sK1))),
% 1.58/0.57    inference(resolution,[],[f360,f60])).
% 1.58/0.57  fof(f360,plain,(
% 1.58/0.57    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v2_funct_1(sK1) | k6_relat_1(sK0) = k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | ~v1_funct_1(k2_funct_1(sK1))),
% 1.58/0.57    inference(forward_demodulation,[],[f359,f338])).
% 1.58/0.57  fof(f338,plain,(
% 1.58/0.57    k6_relat_1(sK0) = k5_relat_1(k2_funct_1(sK1),sK1)),
% 1.58/0.57    inference(resolution,[],[f336,f60])).
% 1.58/0.57  fof(f336,plain,(
% 1.58/0.57    ( ! [X0,X1] : (~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k6_relat_1(sK0) = k5_relat_1(k2_funct_1(sK1),sK1)) )),
% 1.58/0.57    inference(resolution,[],[f335,f68])).
% 1.58/0.57  fof(f335,plain,(
% 1.58/0.57    ~v1_relat_1(sK1) | k6_relat_1(sK0) = k5_relat_1(k2_funct_1(sK1),sK1)),
% 1.58/0.57    inference(resolution,[],[f333,f57])).
% 1.58/0.57  fof(f333,plain,(
% 1.58/0.57    ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | k6_relat_1(sK0) = k5_relat_1(k2_funct_1(sK1),sK1)),
% 1.58/0.57    inference(resolution,[],[f330,f59])).
% 1.58/0.57  fof(f330,plain,(
% 1.58/0.57    ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | k6_relat_1(sK0) = k5_relat_1(k2_funct_1(sK1),sK1)),
% 1.58/0.57    inference(forward_demodulation,[],[f253,f289])).
% 1.58/0.57  fof(f253,plain,(
% 1.58/0.57    ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~v3_funct_2(sK1,sK0,sK0) | k5_relat_1(k2_funct_1(sK1),sK1) = k6_relat_1(k2_relat_1(sK1))),
% 1.58/0.57    inference(resolution,[],[f122,f60])).
% 1.58/0.57  fof(f122,plain,(
% 1.58/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v3_funct_2(X0,X1,X2) | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))) )),
% 1.58/0.57    inference(duplicate_literal_removal,[],[f121])).
% 1.58/0.57  fof(f121,plain,(
% 1.58/0.57    ( ! [X2,X0,X1] : (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v3_funct_2(X0,X1,X2) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 1.58/0.57    inference(resolution,[],[f89,f70])).
% 1.58/0.57  fof(f89,plain,(
% 1.58/0.57    ( ! [X0] : (~v2_funct_1(X0) | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.58/0.57    inference(cnf_transformation,[],[f46])).
% 1.58/0.57  fof(f359,plain,(
% 1.58/0.57    ~v2_funct_1(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k5_relat_1(k2_funct_1(sK1),sK1) | ~v1_funct_1(k2_funct_1(sK1))),
% 1.58/0.57    inference(trivial_inequality_removal,[],[f358])).
% 1.58/0.57  fof(f358,plain,(
% 1.58/0.57    sK0 != sK0 | ~v2_funct_1(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k5_relat_1(k2_funct_1(sK1),sK1) | ~v1_funct_1(k2_funct_1(sK1))),
% 1.58/0.57    inference(duplicate_literal_removal,[],[f357])).
% 1.58/0.57  fof(f357,plain,(
% 1.58/0.57    sK0 != sK0 | ~v2_funct_1(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | ~v1_funct_1(sK1) | k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k5_relat_1(k2_funct_1(sK1),sK1) | ~v1_funct_1(k2_funct_1(sK1))),
% 1.58/0.57    inference(superposition,[],[f177,f293])).
% 1.58/0.57  fof(f177,plain,(
% 1.58/0.57    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~v1_funct_1(sK1) | k1_partfun1(X1,X0,sK0,sK0,k2_funct_1(X2),sK1) = k5_relat_1(k2_funct_1(X2),sK1) | ~v1_funct_1(k2_funct_1(X2))) )),
% 1.58/0.57    inference(resolution,[],[f74,f164])).
% 1.58/0.57  fof(f164,plain,(
% 1.58/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(sK1) | k1_partfun1(X1,X2,sK0,sK0,X0,sK1) = k5_relat_1(X0,sK1) | ~v1_funct_1(X0)) )),
% 1.58/0.57    inference(resolution,[],[f66,f60])).
% 1.58/0.57  fof(f157,plain,(
% 1.58/0.57    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_relat_1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_relat_1(sK0))),
% 1.58/0.57    inference(forward_demodulation,[],[f156,f155])).
% 1.58/0.57  fof(f155,plain,(
% 1.58/0.57    k2_funct_2(sK0,sK1) = k2_funct_1(sK1)),
% 1.58/0.57    inference(resolution,[],[f154,f57])).
% 1.58/0.57  fof(f154,plain,(
% 1.58/0.57    ~v1_funct_1(sK1) | k2_funct_2(sK0,sK1) = k2_funct_1(sK1)),
% 1.58/0.57    inference(resolution,[],[f151,f59])).
% 1.58/0.57  fof(f151,plain,(
% 1.58/0.57    ~v3_funct_2(sK1,sK0,sK0) | k2_funct_2(sK0,sK1) = k2_funct_1(sK1) | ~v1_funct_1(sK1)),
% 1.58/0.57    inference(resolution,[],[f148,f58])).
% 1.58/0.57  fof(f148,plain,(
% 1.58/0.57    ~v1_funct_2(sK1,sK0,sK0) | ~v3_funct_2(sK1,sK0,sK0) | k2_funct_2(sK0,sK1) = k2_funct_1(sK1) | ~v1_funct_1(sK1)),
% 1.58/0.57    inference(resolution,[],[f67,f60])).
% 1.58/0.57  fof(f67,plain,(
% 1.58/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | k2_funct_2(X0,X1) = k2_funct_1(X1) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 1.58/0.57    inference(cnf_transformation,[],[f30])).
% 1.58/0.57  fof(f30,plain,(
% 1.58/0.57    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 1.58/0.57    inference(flattening,[],[f29])).
% 1.58/0.57  fof(f29,plain,(
% 1.58/0.57    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 1.58/0.57    inference(ennf_transformation,[],[f18])).
% 1.58/0.57  fof(f18,axiom,(
% 1.58/0.57    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_2(X0,X1) = k2_funct_1(X1))),
% 1.58/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).
% 1.58/0.57  fof(f156,plain,(
% 1.58/0.57    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_relat_1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_relat_1(sK0))),
% 1.58/0.57    inference(backward_demodulation,[],[f97,f155])).
% 1.58/0.57  fof(f97,plain,(
% 1.58/0.57    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_relat_1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_relat_1(sK0))),
% 1.58/0.57    inference(definition_unfolding,[],[f61,f65,f65])).
% 1.58/0.57  fof(f61,plain,(
% 1.58/0.57    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))),
% 1.58/0.57    inference(cnf_transformation,[],[f53])).
% 1.58/0.57  fof(f58,plain,(
% 1.58/0.57    v1_funct_2(sK1,sK0,sK0)),
% 1.58/0.57    inference(cnf_transformation,[],[f53])).
% 1.58/0.57  fof(f540,plain,(
% 1.58/0.57    ~v1_funct_2(sK1,k1_xboole_0,k1_xboole_0) | k1_xboole_0 = k1_relat_1(sK1)),
% 1.58/0.57    inference(forward_demodulation,[],[f499,f445])).
% 1.58/0.57  fof(f445,plain,(
% 1.58/0.57    k1_relat_1(sK1) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK1)),
% 1.58/0.57    inference(backward_demodulation,[],[f112,f440])).
% 1.58/0.57  fof(f499,plain,(
% 1.58/0.57    ~v1_funct_2(sK1,k1_xboole_0,k1_xboole_0) | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK1)),
% 1.58/0.57    inference(resolution,[],[f444,f104])).
% 1.58/0.57  fof(f104,plain,(
% 1.58/0.57    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)) )),
% 1.58/0.57    inference(equality_resolution,[],[f76])).
% 1.58/0.57  fof(f76,plain,(
% 1.58/0.57    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.58/0.57    inference(cnf_transformation,[],[f54])).
% 1.58/0.57  fof(f444,plain,(
% 1.58/0.57    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 1.58/0.57    inference(backward_demodulation,[],[f60,f440])).
% 1.58/0.57  fof(f493,plain,(
% 1.58/0.57    ~r2_relset_1(k1_xboole_0,k1_xboole_0,k6_relat_1(k1_relat_1(sK1)),k6_relat_1(k1_xboole_0)) | ~r2_relset_1(k1_xboole_0,k1_xboole_0,k6_relat_1(k1_xboole_0),k6_relat_1(k1_xboole_0))),
% 1.58/0.57    inference(forward_demodulation,[],[f476,f440])).
% 1.58/0.57  fof(f476,plain,(
% 1.58/0.57    ~r2_relset_1(k1_xboole_0,k1_xboole_0,k6_relat_1(k1_xboole_0),k6_relat_1(k1_xboole_0)) | ~r2_relset_1(sK0,sK0,k6_relat_1(k1_relat_1(sK1)),k6_relat_1(sK0))),
% 1.58/0.57    inference(backward_demodulation,[],[f436,f440])).
% 1.58/0.57  % SZS output end Proof for theBenchmark
% 1.58/0.57  % (13668)------------------------------
% 1.58/0.57  % (13668)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.58/0.57  % (13668)Termination reason: Refutation
% 1.58/0.57  
% 1.58/0.57  % (13668)Memory used [KB]: 2046
% 1.58/0.57  % (13668)Time elapsed: 0.144 s
% 1.58/0.57  % (13668)------------------------------
% 1.58/0.57  % (13668)------------------------------
% 1.58/0.57  % (13690)Refutation not found, incomplete strategy% (13690)------------------------------
% 1.58/0.57  % (13690)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.58/0.57  % (13690)Termination reason: Refutation not found, incomplete strategy
% 1.58/0.57  
% 1.58/0.57  % (13690)Memory used [KB]: 6396
% 1.58/0.57  % (13690)Time elapsed: 0.145 s
% 1.58/0.57  % (13690)------------------------------
% 1.58/0.57  % (13690)------------------------------
% 1.58/0.58  % (13659)Success in time 0.208 s
%------------------------------------------------------------------------------
