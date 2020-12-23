%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:03:07 EST 2020

% Result     : Theorem 1.50s
% Output     : Refutation 1.50s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 326 expanded)
%              Number of leaves         :   21 (  98 expanded)
%              Depth                    :   26
%              Number of atoms          :  475 (2260 expanded)
%              Number of equality atoms :  126 ( 327 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f339,plain,(
    $false ),
    inference(subsumption_resolution,[],[f338,f119])).

fof(f119,plain,(
    v5_relat_1(sK2,sK1) ),
    inference(resolution,[],[f81,f56])).

fof(f56,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,
    ( ~ v2_funct_1(sK2)
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_2(sK3,sK1,sK0)
    & v1_funct_1(sK3)
    & k1_xboole_0 != sK1
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f22,f41,f40])).

fof(f40,plain,
    ( ? [X0,X1,X2] :
        ( ~ v2_funct_1(X2)
        & ? [X3] :
            ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
        & k1_xboole_0 != X1
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ~ v2_funct_1(sK2)
      & ? [X3] :
          ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
          & v1_funct_2(X3,sK1,sK0)
          & v1_funct_1(X3) )
      & k1_xboole_0 != sK1
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X3] :
        ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        & v1_funct_2(X3,sK1,sK0)
        & v1_funct_1(X3) )
   => ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      & v1_funct_2(sK3,sK1,sK0)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( ~ v2_funct_1(X2)
      & ? [X3] :
          ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( ~ v2_funct_1(X2)
      & ? [X3] :
          ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ~ ( ~ v2_funct_1(X2)
            & ? [X3] :
                ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
                & v1_funct_2(X3,X1,X0)
                & v1_funct_1(X3) )
            & k1_xboole_0 != X1 ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ~ ( ~ v2_funct_1(X2)
          & ? [X3] :
              ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
          & k1_xboole_0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_funct_2)).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f338,plain,(
    ~ v5_relat_1(sK2,sK1) ),
    inference(forward_demodulation,[],[f337,f229])).

fof(f229,plain,(
    sK1 = k1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f228,f60])).

fof(f60,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f42])).

fof(f228,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(subsumption_resolution,[],[f226,f191])).

fof(f191,plain,(
    k1_xboole_0 != sK0 ),
    inference(subsumption_resolution,[],[f190,f62])).

fof(f62,plain,(
    ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f190,plain,
    ( k1_xboole_0 != sK0
    | v2_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f189,f112])).

fof(f112,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f79,f56])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f189,plain,
    ( k1_xboole_0 != sK0
    | ~ v1_relat_1(sK2)
    | v2_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f184,f54])).

fof(f54,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f184,plain,
    ( k1_xboole_0 != sK0
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | v2_funct_1(sK2) ),
    inference(superposition,[],[f130,f176])).

fof(f176,plain,(
    sK0 = k1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f174,f56])).

fof(f174,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f172,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f172,plain,(
    sK0 = k1_relset_1(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f171,f57])).

fof(f57,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f42])).

fof(f171,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f166,f55])).

fof(f55,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f166,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2) ),
    inference(resolution,[],[f82,f56])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
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
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f32,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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

fof(f130,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v2_funct_1(X0) ) ),
    inference(subsumption_resolution,[],[f129,f108])).

fof(f108,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f73,f93])).

fof(f93,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f73,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f129,plain,(
    ! [X0] :
      ( r2_hidden(sK5(X0),k1_xboole_0)
      | v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f128])).

fof(f128,plain,(
    ! [X0] :
      ( r2_hidden(sK5(X0),k1_xboole_0)
      | v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f69,f67])).

fof(f67,plain,(
    ! [X0] :
      ( k1_xboole_0 = k2_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

fof(f69,plain,(
    ! [X0] :
      ( r2_hidden(sK5(X0),k2_relat_1(X0))
      | v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ( ( ! [X1] :
              ( k10_relat_1(X0,k1_tarski(X1)) = k1_tarski(sK4(X0,X1))
              | ~ r2_hidden(X1,k2_relat_1(X0)) )
          | ~ v2_funct_1(X0) )
        & ( v2_funct_1(X0)
          | ( ! [X4] : k1_tarski(X4) != k10_relat_1(X0,k1_tarski(sK5(X0)))
            & r2_hidden(sK5(X0),k2_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f45,f47,f46])).

fof(f46,plain,(
    ! [X1,X0] :
      ( ? [X2] : k10_relat_1(X0,k1_tarski(X1)) = k1_tarski(X2)
     => k10_relat_1(X0,k1_tarski(X1)) = k1_tarski(sK4(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0] :
      ( ? [X3] :
          ( ! [X4] : k10_relat_1(X0,k1_tarski(X3)) != k1_tarski(X4)
          & r2_hidden(X3,k2_relat_1(X0)) )
     => ( ! [X4] : k1_tarski(X4) != k10_relat_1(X0,k1_tarski(sK5(X0)))
        & r2_hidden(sK5(X0),k2_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0] :
      ( ( ( ! [X1] :
              ( ? [X2] : k10_relat_1(X0,k1_tarski(X1)) = k1_tarski(X2)
              | ~ r2_hidden(X1,k2_relat_1(X0)) )
          | ~ v2_funct_1(X0) )
        & ( v2_funct_1(X0)
          | ? [X3] :
              ( ! [X4] : k10_relat_1(X0,k1_tarski(X3)) != k1_tarski(X4)
              & r2_hidden(X3,k2_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ( ( ! [X1] :
              ( ? [X2] : k10_relat_1(X0,k1_tarski(X1)) = k1_tarski(X2)
              | ~ r2_hidden(X1,k2_relat_1(X0)) )
          | ~ v2_funct_1(X0) )
        & ( v2_funct_1(X0)
          | ? [X1] :
              ( ! [X2] : k10_relat_1(X0,k1_tarski(X1)) != k1_tarski(X2)
              & r2_hidden(X1,k2_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( ! [X1] :
            ( ? [X2] : k10_relat_1(X0,k1_tarski(X1)) = k1_tarski(X2)
            | ~ r2_hidden(X1,k2_relat_1(X0)) )
      <=> v2_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( ! [X1] :
            ( ? [X2] : k10_relat_1(X0,k1_tarski(X1)) = k1_tarski(X2)
            | ~ r2_hidden(X1,k2_relat_1(X0)) )
      <=> v2_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( ! [X1] :
            ~ ( ! [X2] : k10_relat_1(X0,k1_tarski(X1)) != k1_tarski(X2)
              & r2_hidden(X1,k2_relat_1(X0)) )
      <=> v2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_funct_1)).

fof(f226,plain,
    ( sK1 = k1_relat_1(sK3)
    | k1_xboole_0 = sK0
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(superposition,[],[f173,f80])).

fof(f173,plain,
    ( sK1 = k1_relset_1(sK1,sK0,sK3)
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f167,f59])).

fof(f59,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f167,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | k1_xboole_0 = sK0
    | sK1 = k1_relset_1(sK1,sK0,sK3) ),
    inference(resolution,[],[f82,f60])).

fof(f337,plain,(
    ~ v5_relat_1(sK2,k1_relat_1(sK3)) ),
    inference(subsumption_resolution,[],[f336,f113])).

fof(f113,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f79,f60])).

fof(f336,plain,
    ( ~ v1_relat_1(sK3)
    | ~ v5_relat_1(sK2,k1_relat_1(sK3)) ),
    inference(subsumption_resolution,[],[f335,f58])).

fof(f58,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f335,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v5_relat_1(sK2,k1_relat_1(sK3)) ),
    inference(subsumption_resolution,[],[f334,f112])).

fof(f334,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v5_relat_1(sK2,k1_relat_1(sK3)) ),
    inference(subsumption_resolution,[],[f333,f54])).

fof(f333,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v5_relat_1(sK2,k1_relat_1(sK3)) ),
    inference(subsumption_resolution,[],[f332,f62])).

fof(f332,plain,
    ( v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v5_relat_1(sK2,k1_relat_1(sK3)) ),
    inference(subsumption_resolution,[],[f326,f65])).

fof(f65,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f326,plain,
    ( ~ v2_funct_1(k6_relat_1(sK0))
    | v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v5_relat_1(sK2,k1_relat_1(sK3)) ),
    inference(superposition,[],[f162,f309])).

fof(f309,plain,(
    k6_relat_1(sK0) = k5_relat_1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f308,f54])).

fof(f308,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,sK3)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f307,f56])).

fof(f307,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f306,f58])).

fof(f306,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,sK3)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f302,f60])).

fof(f302,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(superposition,[],[f293,f90])).

fof(f90,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
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
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f293,plain,(
    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f292,f54])).

fof(f292,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f291,f56])).

fof(f291,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f290,f58])).

fof(f290,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f288,f60])).

fof(f288,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f280,f92])).

fof(f92,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f280,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0) ),
    inference(resolution,[],[f194,f102])).

fof(f102,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f61,f63])).

fof(f63,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f61,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f42])).

fof(f194,plain,(
    ! [X2,X3] :
      ( ~ r2_relset_1(X2,X2,X3,k6_relat_1(X2))
      | k6_relat_1(X2) = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ) ),
    inference(resolution,[],[f88,f103])).

fof(f103,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(forward_demodulation,[],[f66,f63])).

fof(f66,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f88,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f162,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(k5_relat_1(X0,X1))
      | v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v5_relat_1(X0,k1_relat_1(X1)) ) ),
    inference(duplicate_literal_removal,[],[f157])).

fof(f157,plain,(
    ! [X0,X1] :
      ( v2_funct_1(X0)
      | ~ v2_funct_1(k5_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v5_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f72,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
      | v2_funct_1(X1)
      | ~ v2_funct_1(k5_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_funct_1(X1)
          | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_funct_1(X1)
          | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
              & v2_funct_1(k5_relat_1(X1,X0)) )
           => v2_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n005.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 18:44:02 EST 2020
% 0.15/0.35  % CPUTime    : 
% 1.50/0.56  % (3165)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.50/0.57  % (3157)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.50/0.57  % (3156)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.50/0.57  % (3144)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.50/0.57  % (3164)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.50/0.58  % (3150)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.50/0.58  % (3162)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.50/0.58  % (3145)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.50/0.59  % (3141)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.50/0.59  % (3154)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.50/0.59  % (3143)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.50/0.59  % (3149)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.50/0.59  % (3142)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.50/0.59  % (3139)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.50/0.60  % (3168)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.50/0.60  % (3147)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.50/0.60  % (3140)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.50/0.60  % (3167)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.50/0.60  % (3146)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.50/0.60  % (3148)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.50/0.60  % (3158)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.50/0.61  % (3159)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.50/0.61  % (3160)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.50/0.61  % (3163)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.50/0.61  % (3149)Refutation not found, incomplete strategy% (3149)------------------------------
% 1.50/0.61  % (3149)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.61  % (3152)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.50/0.61  % (3149)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.61  
% 1.50/0.61  % (3149)Memory used [KB]: 11001
% 1.50/0.61  % (3149)Time elapsed: 0.165 s
% 1.50/0.61  % (3149)------------------------------
% 1.50/0.61  % (3149)------------------------------
% 1.50/0.62  % (3155)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.50/0.62  % (3166)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.50/0.62  % (3155)Refutation not found, incomplete strategy% (3155)------------------------------
% 1.50/0.62  % (3155)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.62  % (3155)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.62  
% 1.50/0.62  % (3155)Memory used [KB]: 10746
% 1.50/0.62  % (3155)Time elapsed: 0.191 s
% 1.50/0.62  % (3155)------------------------------
% 1.50/0.62  % (3155)------------------------------
% 1.50/0.62  % (3153)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.50/0.63  % (3167)Refutation not found, incomplete strategy% (3167)------------------------------
% 1.50/0.63  % (3167)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.63  % (3167)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.63  
% 1.50/0.63  % (3167)Memory used [KB]: 11001
% 1.50/0.63  % (3167)Time elapsed: 0.197 s
% 1.50/0.63  % (3167)------------------------------
% 1.50/0.63  % (3167)------------------------------
% 1.50/0.63  % (3148)Refutation found. Thanks to Tanya!
% 1.50/0.63  % SZS status Theorem for theBenchmark
% 1.50/0.63  % SZS output start Proof for theBenchmark
% 1.50/0.63  fof(f339,plain,(
% 1.50/0.63    $false),
% 1.50/0.63    inference(subsumption_resolution,[],[f338,f119])).
% 1.50/0.63  fof(f119,plain,(
% 1.50/0.63    v5_relat_1(sK2,sK1)),
% 1.50/0.63    inference(resolution,[],[f81,f56])).
% 1.50/0.63  fof(f56,plain,(
% 1.50/0.63    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.50/0.63    inference(cnf_transformation,[],[f42])).
% 1.50/0.63  fof(f42,plain,(
% 1.50/0.63    ~v2_funct_1(sK2) & (r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & k1_xboole_0 != sK1 & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 1.50/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f22,f41,f40])).
% 1.50/0.63  fof(f40,plain,(
% 1.50/0.63    ? [X0,X1,X2] : (~v2_funct_1(X2) & ? [X3] : (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (~v2_funct_1(sK2) & ? [X3] : (r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & k1_xboole_0 != sK1 & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 1.50/0.63    introduced(choice_axiom,[])).
% 1.50/0.63  fof(f41,plain,(
% 1.50/0.63    ? [X3] : (r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) => (r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3))),
% 1.50/0.63    introduced(choice_axiom,[])).
% 1.50/0.63  fof(f22,plain,(
% 1.50/0.63    ? [X0,X1,X2] : (~v2_funct_1(X2) & ? [X3] : (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.50/0.63    inference(flattening,[],[f21])).
% 1.50/0.63  fof(f21,plain,(
% 1.50/0.63    ? [X0,X1,X2] : ((~v2_funct_1(X2) & ? [X3] : (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.50/0.63    inference(ennf_transformation,[],[f18])).
% 1.50/0.63  fof(f18,negated_conjecture,(
% 1.50/0.63    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ~(~v2_funct_1(X2) & ? [X3] : (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & k1_xboole_0 != X1))),
% 1.50/0.63    inference(negated_conjecture,[],[f17])).
% 1.50/0.63  fof(f17,conjecture,(
% 1.50/0.63    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ~(~v2_funct_1(X2) & ? [X3] : (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & k1_xboole_0 != X1))),
% 1.50/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_funct_2)).
% 1.50/0.63  fof(f81,plain,(
% 1.50/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 1.50/0.63    inference(cnf_transformation,[],[f31])).
% 1.50/0.63  fof(f31,plain,(
% 1.50/0.63    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.50/0.63    inference(ennf_transformation,[],[f20])).
% 1.50/0.63  fof(f20,plain,(
% 1.50/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 1.50/0.63    inference(pure_predicate_removal,[],[f9])).
% 1.50/0.63  fof(f9,axiom,(
% 1.50/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.50/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.50/0.63  fof(f338,plain,(
% 1.50/0.63    ~v5_relat_1(sK2,sK1)),
% 1.50/0.63    inference(forward_demodulation,[],[f337,f229])).
% 1.50/0.63  fof(f229,plain,(
% 1.50/0.63    sK1 = k1_relat_1(sK3)),
% 1.50/0.63    inference(subsumption_resolution,[],[f228,f60])).
% 1.50/0.63  fof(f60,plain,(
% 1.50/0.63    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.50/0.63    inference(cnf_transformation,[],[f42])).
% 1.50/0.63  fof(f228,plain,(
% 1.50/0.63    sK1 = k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.50/0.63    inference(subsumption_resolution,[],[f226,f191])).
% 1.50/0.63  fof(f191,plain,(
% 1.50/0.63    k1_xboole_0 != sK0),
% 1.50/0.63    inference(subsumption_resolution,[],[f190,f62])).
% 1.50/0.63  fof(f62,plain,(
% 1.50/0.63    ~v2_funct_1(sK2)),
% 1.50/0.63    inference(cnf_transformation,[],[f42])).
% 1.50/0.63  fof(f190,plain,(
% 1.50/0.63    k1_xboole_0 != sK0 | v2_funct_1(sK2)),
% 1.50/0.63    inference(subsumption_resolution,[],[f189,f112])).
% 1.50/0.63  fof(f112,plain,(
% 1.50/0.63    v1_relat_1(sK2)),
% 1.50/0.63    inference(resolution,[],[f79,f56])).
% 1.50/0.63  fof(f79,plain,(
% 1.50/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.50/0.63    inference(cnf_transformation,[],[f29])).
% 1.50/0.63  fof(f29,plain,(
% 1.50/0.63    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.50/0.63    inference(ennf_transformation,[],[f8])).
% 1.50/0.63  fof(f8,axiom,(
% 1.50/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.50/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.50/0.63  fof(f189,plain,(
% 1.50/0.63    k1_xboole_0 != sK0 | ~v1_relat_1(sK2) | v2_funct_1(sK2)),
% 1.50/0.63    inference(subsumption_resolution,[],[f184,f54])).
% 1.50/0.63  fof(f54,plain,(
% 1.50/0.63    v1_funct_1(sK2)),
% 1.50/0.63    inference(cnf_transformation,[],[f42])).
% 1.50/0.63  fof(f184,plain,(
% 1.50/0.63    k1_xboole_0 != sK0 | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | v2_funct_1(sK2)),
% 1.50/0.63    inference(superposition,[],[f130,f176])).
% 1.50/0.63  fof(f176,plain,(
% 1.50/0.63    sK0 = k1_relat_1(sK2)),
% 1.50/0.63    inference(subsumption_resolution,[],[f174,f56])).
% 1.50/0.63  fof(f174,plain,(
% 1.50/0.63    sK0 = k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.50/0.63    inference(superposition,[],[f172,f80])).
% 1.50/0.63  fof(f80,plain,(
% 1.50/0.63    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.50/0.63    inference(cnf_transformation,[],[f30])).
% 1.50/0.63  fof(f30,plain,(
% 1.50/0.63    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.50/0.63    inference(ennf_transformation,[],[f10])).
% 1.50/0.63  fof(f10,axiom,(
% 1.50/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.50/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.50/0.63  fof(f172,plain,(
% 1.50/0.63    sK0 = k1_relset_1(sK0,sK1,sK2)),
% 1.50/0.63    inference(subsumption_resolution,[],[f171,f57])).
% 1.50/0.63  fof(f57,plain,(
% 1.50/0.63    k1_xboole_0 != sK1),
% 1.50/0.63    inference(cnf_transformation,[],[f42])).
% 1.50/0.63  fof(f171,plain,(
% 1.50/0.63    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2)),
% 1.50/0.63    inference(subsumption_resolution,[],[f166,f55])).
% 1.50/0.63  fof(f55,plain,(
% 1.50/0.63    v1_funct_2(sK2,sK0,sK1)),
% 1.50/0.63    inference(cnf_transformation,[],[f42])).
% 1.50/0.63  fof(f166,plain,(
% 1.50/0.63    ~v1_funct_2(sK2,sK0,sK1) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2)),
% 1.50/0.63    inference(resolution,[],[f82,f56])).
% 1.50/0.63  fof(f82,plain,(
% 1.50/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 1.50/0.63    inference(cnf_transformation,[],[f52])).
% 1.50/0.63  fof(f52,plain,(
% 1.50/0.63    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.50/0.63    inference(nnf_transformation,[],[f33])).
% 1.50/0.63  fof(f33,plain,(
% 1.50/0.63    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.50/0.63    inference(flattening,[],[f32])).
% 1.50/0.63  fof(f32,plain,(
% 1.50/0.63    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.50/0.63    inference(ennf_transformation,[],[f12])).
% 1.50/0.63  fof(f12,axiom,(
% 1.50/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.50/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.50/0.63  fof(f130,plain,(
% 1.50/0.63    ( ! [X0] : (k1_xboole_0 != k1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | v2_funct_1(X0)) )),
% 1.50/0.63    inference(subsumption_resolution,[],[f129,f108])).
% 1.50/0.63  fof(f108,plain,(
% 1.50/0.63    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.50/0.63    inference(superposition,[],[f73,f93])).
% 1.50/0.63  fof(f93,plain,(
% 1.50/0.63    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.50/0.63    inference(equality_resolution,[],[f78])).
% 1.50/0.63  fof(f78,plain,(
% 1.50/0.63    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 1.50/0.63    inference(cnf_transformation,[],[f51])).
% 1.50/0.63  fof(f51,plain,(
% 1.50/0.63    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 1.50/0.63    inference(flattening,[],[f50])).
% 1.50/0.63  fof(f50,plain,(
% 1.50/0.63    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 1.50/0.63    inference(nnf_transformation,[],[f1])).
% 1.50/0.63  fof(f1,axiom,(
% 1.50/0.63    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.50/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.50/0.63  fof(f73,plain,(
% 1.50/0.63    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 1.50/0.63    inference(cnf_transformation,[],[f2])).
% 1.50/0.63  fof(f2,axiom,(
% 1.50/0.63    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 1.50/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).
% 1.50/0.63  fof(f129,plain,(
% 1.50/0.63    ( ! [X0] : (r2_hidden(sK5(X0),k1_xboole_0) | v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0)) )),
% 1.50/0.63    inference(duplicate_literal_removal,[],[f128])).
% 1.50/0.63  fof(f128,plain,(
% 1.50/0.63    ( ! [X0] : (r2_hidden(sK5(X0),k1_xboole_0) | v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 1.50/0.63    inference(superposition,[],[f69,f67])).
% 1.50/0.63  fof(f67,plain,(
% 1.50/0.63    ( ! [X0] : (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 1.50/0.63    inference(cnf_transformation,[],[f43])).
% 1.50/0.63  fof(f43,plain,(
% 1.50/0.63    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.50/0.63    inference(nnf_transformation,[],[f23])).
% 1.50/0.63  fof(f23,plain,(
% 1.50/0.63    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.50/0.63    inference(ennf_transformation,[],[f4])).
% 1.50/0.63  fof(f4,axiom,(
% 1.50/0.63    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 1.50/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).
% 1.50/0.63  fof(f69,plain,(
% 1.50/0.63    ( ! [X0] : (r2_hidden(sK5(X0),k2_relat_1(X0)) | v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.50/0.63    inference(cnf_transformation,[],[f48])).
% 1.50/0.63  fof(f48,plain,(
% 1.50/0.63    ! [X0] : (((! [X1] : (k10_relat_1(X0,k1_tarski(X1)) = k1_tarski(sK4(X0,X1)) | ~r2_hidden(X1,k2_relat_1(X0))) | ~v2_funct_1(X0)) & (v2_funct_1(X0) | (! [X4] : k1_tarski(X4) != k10_relat_1(X0,k1_tarski(sK5(X0))) & r2_hidden(sK5(X0),k2_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.50/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f45,f47,f46])).
% 1.50/0.63  fof(f46,plain,(
% 1.50/0.63    ! [X1,X0] : (? [X2] : k10_relat_1(X0,k1_tarski(X1)) = k1_tarski(X2) => k10_relat_1(X0,k1_tarski(X1)) = k1_tarski(sK4(X0,X1)))),
% 1.50/0.63    introduced(choice_axiom,[])).
% 1.50/0.63  fof(f47,plain,(
% 1.50/0.63    ! [X0] : (? [X3] : (! [X4] : k10_relat_1(X0,k1_tarski(X3)) != k1_tarski(X4) & r2_hidden(X3,k2_relat_1(X0))) => (! [X4] : k1_tarski(X4) != k10_relat_1(X0,k1_tarski(sK5(X0))) & r2_hidden(sK5(X0),k2_relat_1(X0))))),
% 1.50/0.63    introduced(choice_axiom,[])).
% 1.50/0.63  fof(f45,plain,(
% 1.50/0.63    ! [X0] : (((! [X1] : (? [X2] : k10_relat_1(X0,k1_tarski(X1)) = k1_tarski(X2) | ~r2_hidden(X1,k2_relat_1(X0))) | ~v2_funct_1(X0)) & (v2_funct_1(X0) | ? [X3] : (! [X4] : k10_relat_1(X0,k1_tarski(X3)) != k1_tarski(X4) & r2_hidden(X3,k2_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.50/0.63    inference(rectify,[],[f44])).
% 1.50/0.63  fof(f44,plain,(
% 1.50/0.63    ! [X0] : (((! [X1] : (? [X2] : k10_relat_1(X0,k1_tarski(X1)) = k1_tarski(X2) | ~r2_hidden(X1,k2_relat_1(X0))) | ~v2_funct_1(X0)) & (v2_funct_1(X0) | ? [X1] : (! [X2] : k10_relat_1(X0,k1_tarski(X1)) != k1_tarski(X2) & r2_hidden(X1,k2_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.50/0.63    inference(nnf_transformation,[],[f25])).
% 1.50/0.63  fof(f25,plain,(
% 1.50/0.63    ! [X0] : ((! [X1] : (? [X2] : k10_relat_1(X0,k1_tarski(X1)) = k1_tarski(X2) | ~r2_hidden(X1,k2_relat_1(X0))) <=> v2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.50/0.63    inference(flattening,[],[f24])).
% 1.50/0.63  fof(f24,plain,(
% 1.50/0.63    ! [X0] : ((! [X1] : (? [X2] : k10_relat_1(X0,k1_tarski(X1)) = k1_tarski(X2) | ~r2_hidden(X1,k2_relat_1(X0))) <=> v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.50/0.63    inference(ennf_transformation,[],[f6])).
% 1.50/0.63  fof(f6,axiom,(
% 1.50/0.63    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (! [X1] : ~(! [X2] : k10_relat_1(X0,k1_tarski(X1)) != k1_tarski(X2) & r2_hidden(X1,k2_relat_1(X0))) <=> v2_funct_1(X0)))),
% 1.50/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_funct_1)).
% 1.50/0.63  fof(f226,plain,(
% 1.50/0.63    sK1 = k1_relat_1(sK3) | k1_xboole_0 = sK0 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.50/0.63    inference(superposition,[],[f173,f80])).
% 1.50/0.63  fof(f173,plain,(
% 1.50/0.63    sK1 = k1_relset_1(sK1,sK0,sK3) | k1_xboole_0 = sK0),
% 1.50/0.63    inference(subsumption_resolution,[],[f167,f59])).
% 1.50/0.63  fof(f59,plain,(
% 1.50/0.63    v1_funct_2(sK3,sK1,sK0)),
% 1.50/0.63    inference(cnf_transformation,[],[f42])).
% 1.50/0.63  fof(f167,plain,(
% 1.50/0.63    ~v1_funct_2(sK3,sK1,sK0) | k1_xboole_0 = sK0 | sK1 = k1_relset_1(sK1,sK0,sK3)),
% 1.50/0.63    inference(resolution,[],[f82,f60])).
% 1.50/0.63  fof(f337,plain,(
% 1.50/0.63    ~v5_relat_1(sK2,k1_relat_1(sK3))),
% 1.50/0.63    inference(subsumption_resolution,[],[f336,f113])).
% 1.50/0.63  fof(f113,plain,(
% 1.50/0.63    v1_relat_1(sK3)),
% 1.50/0.63    inference(resolution,[],[f79,f60])).
% 1.50/0.63  fof(f336,plain,(
% 1.50/0.63    ~v1_relat_1(sK3) | ~v5_relat_1(sK2,k1_relat_1(sK3))),
% 1.50/0.63    inference(subsumption_resolution,[],[f335,f58])).
% 1.50/0.63  fof(f58,plain,(
% 1.50/0.63    v1_funct_1(sK3)),
% 1.50/0.63    inference(cnf_transformation,[],[f42])).
% 1.50/0.63  fof(f335,plain,(
% 1.50/0.63    ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v5_relat_1(sK2,k1_relat_1(sK3))),
% 1.50/0.63    inference(subsumption_resolution,[],[f334,f112])).
% 1.50/0.63  fof(f334,plain,(
% 1.50/0.63    ~v1_relat_1(sK2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v5_relat_1(sK2,k1_relat_1(sK3))),
% 1.50/0.63    inference(subsumption_resolution,[],[f333,f54])).
% 1.50/0.63  fof(f333,plain,(
% 1.50/0.63    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v5_relat_1(sK2,k1_relat_1(sK3))),
% 1.50/0.63    inference(subsumption_resolution,[],[f332,f62])).
% 1.50/0.63  fof(f332,plain,(
% 1.50/0.63    v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v5_relat_1(sK2,k1_relat_1(sK3))),
% 1.50/0.63    inference(subsumption_resolution,[],[f326,f65])).
% 1.50/0.63  fof(f65,plain,(
% 1.50/0.63    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 1.50/0.63    inference(cnf_transformation,[],[f5])).
% 1.50/0.63  fof(f5,axiom,(
% 1.50/0.63    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.50/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).
% 1.50/0.63  fof(f326,plain,(
% 1.50/0.63    ~v2_funct_1(k6_relat_1(sK0)) | v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v5_relat_1(sK2,k1_relat_1(sK3))),
% 1.50/0.63    inference(superposition,[],[f162,f309])).
% 1.50/0.63  fof(f309,plain,(
% 1.50/0.63    k6_relat_1(sK0) = k5_relat_1(sK2,sK3)),
% 1.50/0.63    inference(subsumption_resolution,[],[f308,f54])).
% 1.50/0.63  fof(f308,plain,(
% 1.50/0.63    k6_relat_1(sK0) = k5_relat_1(sK2,sK3) | ~v1_funct_1(sK2)),
% 1.50/0.63    inference(subsumption_resolution,[],[f307,f56])).
% 1.50/0.63  fof(f307,plain,(
% 1.50/0.63    k6_relat_1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2)),
% 1.50/0.63    inference(subsumption_resolution,[],[f306,f58])).
% 1.50/0.63  fof(f306,plain,(
% 1.50/0.63    k6_relat_1(sK0) = k5_relat_1(sK2,sK3) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2)),
% 1.50/0.63    inference(subsumption_resolution,[],[f302,f60])).
% 1.50/0.63  fof(f302,plain,(
% 1.50/0.63    k6_relat_1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2)),
% 1.50/0.63    inference(superposition,[],[f293,f90])).
% 1.50/0.63  fof(f90,plain,(
% 1.50/0.63    ( ! [X4,X2,X0,X5,X3,X1] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.50/0.63    inference(cnf_transformation,[],[f37])).
% 1.50/0.63  fof(f37,plain,(
% 1.50/0.63    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.50/0.63    inference(flattening,[],[f36])).
% 1.50/0.63  fof(f36,plain,(
% 1.50/0.63    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.50/0.63    inference(ennf_transformation,[],[f15])).
% 1.50/0.63  fof(f15,axiom,(
% 1.50/0.63    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 1.50/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 1.50/0.63  fof(f293,plain,(
% 1.50/0.63    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0)),
% 1.50/0.63    inference(subsumption_resolution,[],[f292,f54])).
% 1.50/0.63  fof(f292,plain,(
% 1.50/0.63    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0) | ~v1_funct_1(sK2)),
% 1.50/0.63    inference(subsumption_resolution,[],[f291,f56])).
% 1.50/0.63  fof(f291,plain,(
% 1.50/0.63    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2)),
% 1.50/0.63    inference(subsumption_resolution,[],[f290,f58])).
% 1.50/0.63  fof(f290,plain,(
% 1.50/0.63    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2)),
% 1.50/0.63    inference(subsumption_resolution,[],[f288,f60])).
% 1.50/0.63  fof(f288,plain,(
% 1.50/0.63    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2)),
% 1.50/0.63    inference(resolution,[],[f280,f92])).
% 1.50/0.63  fof(f92,plain,(
% 1.50/0.63    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.50/0.63    inference(cnf_transformation,[],[f39])).
% 1.50/0.63  fof(f39,plain,(
% 1.50/0.63    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.50/0.63    inference(flattening,[],[f38])).
% 1.50/0.63  fof(f38,plain,(
% 1.50/0.63    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.50/0.63    inference(ennf_transformation,[],[f13])).
% 1.50/0.63  fof(f13,axiom,(
% 1.50/0.63    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 1.50/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 1.50/0.63  fof(f280,plain,(
% 1.50/0.63    ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0)),
% 1.50/0.63    inference(resolution,[],[f194,f102])).
% 1.50/0.63  fof(f102,plain,(
% 1.50/0.63    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0))),
% 1.50/0.63    inference(forward_demodulation,[],[f61,f63])).
% 1.50/0.63  fof(f63,plain,(
% 1.50/0.63    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 1.50/0.63    inference(cnf_transformation,[],[f16])).
% 1.50/0.63  fof(f16,axiom,(
% 1.50/0.63    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 1.50/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.50/0.63  fof(f61,plain,(
% 1.50/0.63    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 1.50/0.63    inference(cnf_transformation,[],[f42])).
% 1.50/0.63  fof(f194,plain,(
% 1.50/0.63    ( ! [X2,X3] : (~r2_relset_1(X2,X2,X3,k6_relat_1(X2)) | k6_relat_1(X2) = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))) )),
% 1.50/0.63    inference(resolution,[],[f88,f103])).
% 1.50/0.63  fof(f103,plain,(
% 1.50/0.63    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.50/0.63    inference(forward_demodulation,[],[f66,f63])).
% 1.50/0.63  fof(f66,plain,(
% 1.50/0.63    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.50/0.63    inference(cnf_transformation,[],[f19])).
% 1.50/0.63  fof(f19,plain,(
% 1.50/0.63    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 1.50/0.63    inference(pure_predicate_removal,[],[f14])).
% 1.50/0.63  fof(f14,axiom,(
% 1.50/0.63    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 1.50/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 1.50/0.63  fof(f88,plain,(
% 1.50/0.63    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.50/0.63    inference(cnf_transformation,[],[f53])).
% 1.50/0.63  fof(f53,plain,(
% 1.50/0.63    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.50/0.63    inference(nnf_transformation,[],[f35])).
% 1.50/0.63  fof(f35,plain,(
% 1.50/0.63    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.50/0.63    inference(flattening,[],[f34])).
% 1.50/0.63  fof(f34,plain,(
% 1.50/0.63    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.50/0.63    inference(ennf_transformation,[],[f11])).
% 1.50/0.63  fof(f11,axiom,(
% 1.50/0.63    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.50/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.50/0.63  fof(f162,plain,(
% 1.50/0.63    ( ! [X0,X1] : (~v2_funct_1(k5_relat_1(X0,X1)) | v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v5_relat_1(X0,k1_relat_1(X1))) )),
% 1.50/0.63    inference(duplicate_literal_removal,[],[f157])).
% 1.50/0.63  fof(f157,plain,(
% 1.50/0.63    ( ! [X0,X1] : (v2_funct_1(X0) | ~v2_funct_1(k5_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v5_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X0)) )),
% 1.50/0.63    inference(resolution,[],[f72,f74])).
% 1.50/0.63  fof(f74,plain,(
% 1.50/0.63    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.50/0.63    inference(cnf_transformation,[],[f49])).
% 1.50/0.63  fof(f49,plain,(
% 1.50/0.63    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.50/0.63    inference(nnf_transformation,[],[f28])).
% 1.50/0.63  fof(f28,plain,(
% 1.50/0.63    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.50/0.63    inference(ennf_transformation,[],[f3])).
% 1.50/0.63  fof(f3,axiom,(
% 1.50/0.63    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.50/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 1.50/0.63  fof(f72,plain,(
% 1.50/0.63    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | v2_funct_1(X1) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.50/0.63    inference(cnf_transformation,[],[f27])).
% 1.50/0.63  fof(f27,plain,(
% 1.50/0.63    ! [X0] : (! [X1] : (v2_funct_1(X1) | ~r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.50/0.63    inference(flattening,[],[f26])).
% 1.50/0.63  fof(f26,plain,(
% 1.50/0.63    ! [X0] : (! [X1] : ((v2_funct_1(X1) | (~r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | ~v2_funct_1(k5_relat_1(X1,X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.50/0.63    inference(ennf_transformation,[],[f7])).
% 1.50/0.63  fof(f7,axiom,(
% 1.50/0.63    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) & v2_funct_1(k5_relat_1(X1,X0))) => v2_funct_1(X1))))),
% 1.50/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_funct_1)).
% 1.50/0.63  % SZS output end Proof for theBenchmark
% 1.50/0.63  % (3148)------------------------------
% 1.50/0.63  % (3148)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.63  % (3148)Termination reason: Refutation
% 1.50/0.63  
% 1.50/0.63  % (3148)Memory used [KB]: 1918
% 1.50/0.63  % (3148)Time elapsed: 0.200 s
% 1.50/0.63  % (3148)------------------------------
% 1.50/0.63  % (3148)------------------------------
% 1.50/0.63  % (3151)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.50/0.64  % (3161)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 2.19/0.66  % (3138)Success in time 0.294 s
%------------------------------------------------------------------------------
