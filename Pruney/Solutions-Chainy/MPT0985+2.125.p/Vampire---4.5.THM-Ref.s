%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:19 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  141 (5891 expanded)
%              Number of leaves         :   20 (1424 expanded)
%              Depth                    :   30
%              Number of atoms          :  413 (34781 expanded)
%              Number of equality atoms :  138 (5872 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f720,plain,(
    $false ),
    inference(subsumption_resolution,[],[f719,f142])).

fof(f142,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(superposition,[],[f78,f135])).

fof(f135,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f134,f82])).

fof(f82,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f134,plain,(
    r1_tarski(k6_relat_1(k1_xboole_0),k1_xboole_0) ),
    inference(resolution,[],[f132,f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f132,plain,(
    m1_subset_1(k6_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[],[f126,f119])).

fof(f119,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f102])).

fof(f102,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f126,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(forward_demodulation,[],[f79,f76])).

fof(f76,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f79,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f78,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f719,plain,(
    ~ v1_funct_1(k1_xboole_0) ),
    inference(forward_demodulation,[],[f718,f694])).

fof(f694,plain,(
    k1_xboole_0 = k2_funct_1(k1_xboole_0) ),
    inference(subsumption_resolution,[],[f693,f74])).

fof(f74,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f693,plain,
    ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | k1_xboole_0 = k2_funct_1(k1_xboole_0) ),
    inference(forward_demodulation,[],[f674,f627])).

fof(f627,plain,(
    k1_xboole_0 = sK3 ),
    inference(subsumption_resolution,[],[f346,f625])).

fof(f625,plain,(
    k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f624,f171])).

fof(f171,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f107,f69])).

fof(f69,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
      | ~ v1_funct_1(k2_funct_1(sK3)) )
    & sK2 = k2_relset_1(sK1,sK2,sK3)
    & v2_funct_1(sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK3,sK1,sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f28,f47])).

fof(f47,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
          | ~ v1_funct_1(k2_funct_1(X2)) )
        & k2_relset_1(X0,X1,X2) = X1
        & v2_funct_1(X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
        | ~ v1_funct_1(k2_funct_1(sK3)) )
      & sK2 = k2_relset_1(sK1,sK2,sK3)
      & v2_funct_1(sK3)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_2(sK3,sK1,sK2)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
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

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f624,plain,
    ( k1_xboole_0 = sK2
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f623,f67])).

fof(f67,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f48])).

fof(f623,plain,
    ( k1_xboole_0 = sK2
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f616,f87])).

fof(f87,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f616,plain,
    ( ~ v1_funct_1(k2_funct_1(sK3))
    | k1_xboole_0 = sK2 ),
    inference(global_subsumption,[],[f72,f604,f609])).

fof(f609,plain,
    ( v1_funct_2(k2_funct_1(sK3),sK2,sK1)
    | ~ v1_funct_1(k2_funct_1(sK3))
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f511,f592])).

fof(f592,plain,
    ( sK1 = k1_relat_1(sK3)
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f590,f289])).

fof(f289,plain,(
    k1_relat_1(sK3) = k1_relset_1(sK1,sK2,sK3) ),
    inference(resolution,[],[f108,f69])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f590,plain,
    ( sK1 = k1_relset_1(sK1,sK2,sK3)
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f587,f212])).

fof(f212,plain,(
    sP0(sK1,sK3,sK2) ),
    inference(resolution,[],[f114,f69])).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP0(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & sP0(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & sP0(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f44,f45])).

fof(f45,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f44,plain,(
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
    inference(flattening,[],[f43])).

fof(f43,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
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

fof(f587,plain,
    ( sK1 = k1_relset_1(sK1,sK2,sK3)
    | k1_xboole_0 = sK2
    | ~ sP0(sK1,sK3,sK2) ),
    inference(resolution,[],[f110,f68])).

fof(f68,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f48])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X1,X0,X2)
      | k1_relset_1(X0,X2,X1) = X0
      | k1_xboole_0 = X2
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X2 )
      | ~ sP0(X0,X1,X2) ) ),
    inference(rectify,[],[f64])).

fof(f64,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f45])).

fof(f511,plain,
    ( v1_funct_2(k2_funct_1(sK3),sK2,k1_relat_1(sK3))
    | ~ v1_funct_1(k2_funct_1(sK3)) ),
    inference(subsumption_resolution,[],[f338,f507])).

fof(f507,plain,(
    v1_relat_1(k2_funct_1(sK3)) ),
    inference(resolution,[],[f502,f107])).

fof(f502,plain,(
    m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3)))) ),
    inference(forward_demodulation,[],[f501,f336])).

fof(f336,plain,(
    sK2 = k1_relat_1(k2_funct_1(sK3)) ),
    inference(backward_demodulation,[],[f272,f332])).

fof(f332,plain,(
    sK2 = k2_relat_1(sK3) ),
    inference(forward_demodulation,[],[f327,f71])).

fof(f71,plain,(
    sK2 = k2_relset_1(sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f48])).

fof(f327,plain,(
    k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
    inference(resolution,[],[f109,f69])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f272,plain,(
    k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3)) ),
    inference(subsumption_resolution,[],[f271,f171])).

fof(f271,plain,
    ( k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f270,f67])).

fof(f270,plain,
    ( k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f88,f70])).

fof(f70,plain,(
    v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f48])).

% (29854)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
fof(f88,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f501,plain,(
    m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK3)),k1_relat_1(sK3)))) ),
    inference(forward_demodulation,[],[f500,f280])).

fof(f280,plain,(
    k1_relat_1(sK3) = k2_relat_1(k2_funct_1(sK3)) ),
    inference(subsumption_resolution,[],[f279,f171])).

fof(f279,plain,
    ( k1_relat_1(sK3) = k2_relat_1(k2_funct_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f278,f67])).

fof(f278,plain,
    ( k1_relat_1(sK3) = k2_relat_1(k2_funct_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f89,f70])).

fof(f89,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f500,plain,(
    m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK3)),k2_relat_1(k2_funct_1(sK3))))) ),
    inference(subsumption_resolution,[],[f495,f171])).

fof(f495,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK3)),k2_relat_1(k2_funct_1(sK3)))))
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f254,f67])).

fof(f254,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(X0)),k2_relat_1(k2_funct_1(X0)))))
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f247,f86])).

fof(f86,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f247,plain,(
    ! [X0] :
      ( m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(X0)),k2_relat_1(k2_funct_1(X0)))))
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f85,f87])).

fof(f85,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
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

fof(f338,plain,
    ( v1_funct_2(k2_funct_1(sK3),sK2,k1_relat_1(sK3))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(k2_funct_1(sK3)) ),
    inference(backward_demodulation,[],[f281,f332])).

fof(f281,plain,
    ( v1_funct_2(k2_funct_1(sK3),k2_relat_1(sK3),k1_relat_1(sK3))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(k2_funct_1(sK3)) ),
    inference(backward_demodulation,[],[f273,f280])).

fof(f273,plain,
    ( v1_funct_2(k2_funct_1(sK3),k2_relat_1(sK3),k2_relat_1(k2_funct_1(sK3)))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(k2_funct_1(sK3)) ),
    inference(superposition,[],[f84,f272])).

fof(f84,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f604,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f502,f592])).

fof(f72,plain,
    ( ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
    | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK3)) ),
    inference(cnf_transformation,[],[f48])).

fof(f346,plain,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 = sK3 ),
    inference(subsumption_resolution,[],[f343,f171])).

fof(f343,plain,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 = sK3
    | ~ v1_relat_1(sK3) ),
    inference(superposition,[],[f81,f332])).

fof(f81,plain,(
    ! [X0] :
      ( k1_xboole_0 != k2_relat_1(X0)
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

fof(f674,plain,
    ( k1_xboole_0 = k2_funct_1(k1_xboole_0)
    | k1_xboole_0 != k1_relat_1(sK3) ),
    inference(backward_demodulation,[],[f513,f627])).

fof(f513,plain,
    ( k1_xboole_0 != k1_relat_1(sK3)
    | k1_xboole_0 = k2_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f284,f507])).

fof(f284,plain,
    ( k1_xboole_0 != k1_relat_1(sK3)
    | k1_xboole_0 = k2_funct_1(sK3)
    | ~ v1_relat_1(k2_funct_1(sK3)) ),
    inference(superposition,[],[f81,f280])).

fof(f718,plain,(
    ~ v1_funct_1(k2_funct_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f717,f627])).

fof(f717,plain,(
    ~ v1_funct_1(k2_funct_1(sK3)) ),
    inference(subsumption_resolution,[],[f716,f182])).

fof(f182,plain,(
    ! [X1] : v1_funct_2(k1_xboole_0,k1_xboole_0,X1) ),
    inference(superposition,[],[f106,f177])).

fof(f177,plain,(
    ! [X0] : k1_xboole_0 = sK8(k1_xboole_0,X0) ),
    inference(resolution,[],[f175,f82])).

fof(f175,plain,(
    ! [X0] : r1_tarski(sK8(k1_xboole_0,X0),k1_xboole_0) ),
    inference(resolution,[],[f159,f98])).

fof(f159,plain,(
    ! [X1] : m1_subset_1(sK8(k1_xboole_0,X1),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[],[f103,f120])).

fof(f120,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f101])).

fof(f101,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f61])).

fof(f103,plain,(
    ! [X0,X1] : m1_subset_1(sK8(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( v1_funct_2(sK8(X0,X1),X0,X1)
      & v1_funct_1(sK8(X0,X1))
      & v1_relat_1(sK8(X0,X1))
      & m1_subset_1(sK8(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f25,f62])).

fof(f62,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2)
          & v1_relat_1(X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( v1_funct_2(sK8(X0,X1),X0,X1)
        & v1_funct_1(sK8(X0,X1))
        & v1_relat_1(sK8(X0,X1))
        & m1_subset_1(sK8(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2)
      & v1_relat_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(pure_predicate_removal,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2)
      & v4_relat_1(X2,X0)
      & v1_relat_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(pure_predicate_removal,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2)
      & v5_relat_1(X2,X1)
      & v4_relat_1(X2,X0)
      & v1_relat_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_funct_2)).

fof(f106,plain,(
    ! [X0,X1] : v1_funct_2(sK8(X0,X1),X0,X1) ),
    inference(cnf_transformation,[],[f63])).

fof(f716,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,sK1)
    | ~ v1_funct_1(k2_funct_1(sK3)) ),
    inference(forward_demodulation,[],[f715,f694])).

fof(f715,plain,
    ( ~ v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK1)
    | ~ v1_funct_1(k2_funct_1(sK3)) ),
    inference(forward_demodulation,[],[f714,f627])).

fof(f714,plain,
    ( ~ v1_funct_2(k2_funct_1(sK3),k1_xboole_0,sK1)
    | ~ v1_funct_1(k2_funct_1(sK3)) ),
    inference(forward_demodulation,[],[f713,f625])).

fof(f713,plain,
    ( ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
    | ~ v1_funct_1(k2_funct_1(sK3)) ),
    inference(subsumption_resolution,[],[f712,f137])).

fof(f137,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(backward_demodulation,[],[f132,f135])).

fof(f712,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
    | ~ v1_funct_1(k2_funct_1(sK3)) ),
    inference(forward_demodulation,[],[f711,f694])).

fof(f711,plain,
    ( ~ m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
    | ~ v1_funct_1(k2_funct_1(sK3)) ),
    inference(forward_demodulation,[],[f710,f627])).

fof(f710,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
    | ~ v1_funct_1(k2_funct_1(sK3)) ),
    inference(forward_demodulation,[],[f631,f120])).

fof(f631,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
    | ~ v1_funct_1(k2_funct_1(sK3)) ),
    inference(backward_demodulation,[],[f72,f625])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:55:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (29834)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.51  % (29853)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.52  % (29851)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.52  % (29833)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.52  % (29845)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.52  % (29839)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.53  % (29843)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.54  % (29835)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.54  % (29827)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.55  % (29835)Refutation not found, incomplete strategy% (29835)------------------------------
% 0.22/0.55  % (29835)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (29835)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (29835)Memory used [KB]: 10746
% 0.22/0.55  % (29835)Time elapsed: 0.104 s
% 0.22/0.55  % (29835)------------------------------
% 0.22/0.55  % (29835)------------------------------
% 0.22/0.55  % (29830)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.55  % (29834)Refutation found. Thanks to Tanya!
% 0.22/0.55  % SZS status Theorem for theBenchmark
% 0.22/0.55  % SZS output start Proof for theBenchmark
% 0.22/0.55  fof(f720,plain,(
% 0.22/0.55    $false),
% 0.22/0.55    inference(subsumption_resolution,[],[f719,f142])).
% 0.22/0.55  fof(f142,plain,(
% 0.22/0.55    v1_funct_1(k1_xboole_0)),
% 0.22/0.55    inference(superposition,[],[f78,f135])).
% 0.22/0.55  fof(f135,plain,(
% 0.22/0.55    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.22/0.55    inference(resolution,[],[f134,f82])).
% 0.22/0.55  fof(f82,plain,(
% 0.22/0.55    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.22/0.55    inference(cnf_transformation,[],[f31])).
% 0.22/0.55  fof(f31,plain,(
% 0.22/0.55    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.22/0.55    inference(ennf_transformation,[],[f4])).
% 0.22/0.55  fof(f4,axiom,(
% 0.22/0.55    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.22/0.55  fof(f134,plain,(
% 0.22/0.55    r1_tarski(k6_relat_1(k1_xboole_0),k1_xboole_0)),
% 0.22/0.55    inference(resolution,[],[f132,f98])).
% 0.22/0.55  fof(f98,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f59])).
% 0.22/0.55  fof(f59,plain,(
% 0.22/0.55    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.22/0.55    inference(nnf_transformation,[],[f6])).
% 0.22/0.55  fof(f6,axiom,(
% 0.22/0.55    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.55  fof(f132,plain,(
% 0.22/0.55    m1_subset_1(k6_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))),
% 0.22/0.55    inference(superposition,[],[f126,f119])).
% 0.22/0.55  fof(f119,plain,(
% 0.22/0.55    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.22/0.55    inference(equality_resolution,[],[f102])).
% 0.22/0.55  fof(f102,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.22/0.55    inference(cnf_transformation,[],[f61])).
% 0.22/0.55  fof(f61,plain,(
% 0.22/0.55    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.22/0.55    inference(flattening,[],[f60])).
% 0.22/0.55  fof(f60,plain,(
% 0.22/0.55    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.22/0.55    inference(nnf_transformation,[],[f5])).
% 0.22/0.55  fof(f5,axiom,(
% 0.22/0.55    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.22/0.55  fof(f126,plain,(
% 0.22/0.55    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.22/0.55    inference(forward_demodulation,[],[f79,f76])).
% 0.22/0.55  fof(f76,plain,(
% 0.22/0.55    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f19])).
% 0.22/0.55  fof(f19,axiom,(
% 0.22/0.55    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 0.22/0.55  fof(f79,plain,(
% 0.22/0.55    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f26])).
% 0.22/0.55  fof(f26,plain,(
% 0.22/0.55    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 0.22/0.55    inference(pure_predicate_removal,[],[f17])).
% 0.22/0.55  fof(f17,axiom,(
% 0.22/0.55    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 0.22/0.55  fof(f78,plain,(
% 0.22/0.55    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f11])).
% 0.22/0.55  fof(f11,axiom,(
% 0.22/0.55    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.22/0.55  fof(f719,plain,(
% 0.22/0.55    ~v1_funct_1(k1_xboole_0)),
% 0.22/0.55    inference(forward_demodulation,[],[f718,f694])).
% 0.22/0.55  fof(f694,plain,(
% 0.22/0.55    k1_xboole_0 = k2_funct_1(k1_xboole_0)),
% 0.22/0.55    inference(subsumption_resolution,[],[f693,f74])).
% 0.22/0.55  fof(f74,plain,(
% 0.22/0.55    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.55    inference(cnf_transformation,[],[f8])).
% 0.22/0.55  fof(f8,axiom,(
% 0.22/0.55    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.22/0.55  fof(f693,plain,(
% 0.22/0.55    k1_xboole_0 != k1_relat_1(k1_xboole_0) | k1_xboole_0 = k2_funct_1(k1_xboole_0)),
% 0.22/0.55    inference(forward_demodulation,[],[f674,f627])).
% 0.22/0.55  fof(f627,plain,(
% 0.22/0.55    k1_xboole_0 = sK3),
% 0.22/0.55    inference(subsumption_resolution,[],[f346,f625])).
% 0.22/0.55  fof(f625,plain,(
% 0.22/0.55    k1_xboole_0 = sK2),
% 0.22/0.55    inference(subsumption_resolution,[],[f624,f171])).
% 0.22/0.55  fof(f171,plain,(
% 0.22/0.55    v1_relat_1(sK3)),
% 0.22/0.55    inference(resolution,[],[f107,f69])).
% 0.22/0.55  fof(f69,plain,(
% 0.22/0.55    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.22/0.55    inference(cnf_transformation,[],[f48])).
% 0.22/0.55  fof(f48,plain,(
% 0.22/0.55    (~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))) & sK2 = k2_relset_1(sK1,sK2,sK3) & v2_funct_1(sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)),
% 0.22/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f28,f47])).
% 0.22/0.55  fof(f47,plain,(
% 0.22/0.55    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))) & sK2 = k2_relset_1(sK1,sK2,sK3) & v2_funct_1(sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3))),
% 0.22/0.55    introduced(choice_axiom,[])).
% 0.22/0.55  fof(f28,plain,(
% 0.22/0.55    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.22/0.55    inference(flattening,[],[f27])).
% 0.22/0.55  fof(f27,plain,(
% 0.22/0.55    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.22/0.55    inference(ennf_transformation,[],[f22])).
% 0.22/0.55  fof(f22,negated_conjecture,(
% 0.22/0.55    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.22/0.55    inference(negated_conjecture,[],[f21])).
% 0.22/0.55  fof(f21,conjecture,(
% 0.22/0.55    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).
% 0.22/0.55  fof(f107,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f40])).
% 0.22/0.55  fof(f40,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.55    inference(ennf_transformation,[],[f13])).
% 0.22/0.55  fof(f13,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.55  fof(f624,plain,(
% 0.22/0.55    k1_xboole_0 = sK2 | ~v1_relat_1(sK3)),
% 0.22/0.55    inference(subsumption_resolution,[],[f623,f67])).
% 0.22/0.55  fof(f67,plain,(
% 0.22/0.55    v1_funct_1(sK3)),
% 0.22/0.55    inference(cnf_transformation,[],[f48])).
% 0.22/0.55  fof(f623,plain,(
% 0.22/0.55    k1_xboole_0 = sK2 | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)),
% 0.22/0.55    inference(resolution,[],[f616,f87])).
% 0.22/0.55  fof(f87,plain,(
% 0.22/0.55    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f35])).
% 0.22/0.55  fof(f35,plain,(
% 0.22/0.55    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.55    inference(flattening,[],[f34])).
% 0.22/0.55  fof(f34,plain,(
% 0.22/0.55    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.55    inference(ennf_transformation,[],[f10])).
% 0.22/0.55  fof(f10,axiom,(
% 0.22/0.55    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.22/0.55  fof(f616,plain,(
% 0.22/0.55    ~v1_funct_1(k2_funct_1(sK3)) | k1_xboole_0 = sK2),
% 0.22/0.55    inference(global_subsumption,[],[f72,f604,f609])).
% 0.22/0.55  fof(f609,plain,(
% 0.22/0.55    v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3)) | k1_xboole_0 = sK2),
% 0.22/0.55    inference(superposition,[],[f511,f592])).
% 0.22/0.55  fof(f592,plain,(
% 0.22/0.55    sK1 = k1_relat_1(sK3) | k1_xboole_0 = sK2),
% 0.22/0.55    inference(superposition,[],[f590,f289])).
% 0.22/0.55  fof(f289,plain,(
% 0.22/0.55    k1_relat_1(sK3) = k1_relset_1(sK1,sK2,sK3)),
% 0.22/0.55    inference(resolution,[],[f108,f69])).
% 0.22/0.55  fof(f108,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f41])).
% 0.22/0.55  fof(f41,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.55    inference(ennf_transformation,[],[f14])).
% 0.22/0.55  fof(f14,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.55  fof(f590,plain,(
% 0.22/0.55    sK1 = k1_relset_1(sK1,sK2,sK3) | k1_xboole_0 = sK2),
% 0.22/0.55    inference(subsumption_resolution,[],[f587,f212])).
% 0.22/0.55  fof(f212,plain,(
% 0.22/0.55    sP0(sK1,sK3,sK2)),
% 0.22/0.55    inference(resolution,[],[f114,f69])).
% 0.22/0.55  fof(f114,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP0(X0,X2,X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f66])).
% 0.22/0.55  fof(f66,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & sP0(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.55    inference(nnf_transformation,[],[f46])).
% 0.22/0.55  fof(f46,plain,(
% 0.22/0.55    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & sP0(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.55    inference(definition_folding,[],[f44,f45])).
% 0.22/0.55  fof(f45,plain,(
% 0.22/0.55    ! [X0,X2,X1] : ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X2,X1))),
% 0.22/0.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.22/0.55  fof(f44,plain,(
% 0.22/0.55    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.55    inference(flattening,[],[f43])).
% 0.22/0.56  fof(f43,plain,(
% 0.22/0.56    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.56    inference(ennf_transformation,[],[f16])).
% 0.22/0.56  fof(f16,axiom,(
% 0.22/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.22/0.56  fof(f587,plain,(
% 0.22/0.56    sK1 = k1_relset_1(sK1,sK2,sK3) | k1_xboole_0 = sK2 | ~sP0(sK1,sK3,sK2)),
% 0.22/0.56    inference(resolution,[],[f110,f68])).
% 0.22/0.56  fof(f68,plain,(
% 0.22/0.56    v1_funct_2(sK3,sK1,sK2)),
% 0.22/0.56    inference(cnf_transformation,[],[f48])).
% 0.22/0.56  fof(f110,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) = X0 | k1_xboole_0 = X2 | ~sP0(X0,X1,X2)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f65])).
% 0.22/0.56  fof(f65,plain,(
% 0.22/0.56    ! [X0,X1,X2] : (((v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0) & (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X2) | ~sP0(X0,X1,X2))),
% 0.22/0.56    inference(rectify,[],[f64])).
% 0.22/0.56  fof(f64,plain,(
% 0.22/0.56    ! [X0,X2,X1] : (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X2,X1))),
% 0.22/0.56    inference(nnf_transformation,[],[f45])).
% 0.22/0.56  fof(f511,plain,(
% 0.22/0.56    v1_funct_2(k2_funct_1(sK3),sK2,k1_relat_1(sK3)) | ~v1_funct_1(k2_funct_1(sK3))),
% 0.22/0.56    inference(subsumption_resolution,[],[f338,f507])).
% 0.22/0.56  fof(f507,plain,(
% 0.22/0.56    v1_relat_1(k2_funct_1(sK3))),
% 0.22/0.56    inference(resolution,[],[f502,f107])).
% 0.22/0.56  fof(f502,plain,(
% 0.22/0.56    m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3))))),
% 0.22/0.56    inference(forward_demodulation,[],[f501,f336])).
% 0.22/0.56  fof(f336,plain,(
% 0.22/0.56    sK2 = k1_relat_1(k2_funct_1(sK3))),
% 0.22/0.56    inference(backward_demodulation,[],[f272,f332])).
% 0.22/0.56  fof(f332,plain,(
% 0.22/0.56    sK2 = k2_relat_1(sK3)),
% 0.22/0.56    inference(forward_demodulation,[],[f327,f71])).
% 0.22/0.56  fof(f71,plain,(
% 0.22/0.56    sK2 = k2_relset_1(sK1,sK2,sK3)),
% 0.22/0.56    inference(cnf_transformation,[],[f48])).
% 0.22/0.56  fof(f327,plain,(
% 0.22/0.56    k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3)),
% 0.22/0.56    inference(resolution,[],[f109,f69])).
% 0.22/0.56  fof(f109,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f42])).
% 0.22/0.56  fof(f42,plain,(
% 0.22/0.56    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.56    inference(ennf_transformation,[],[f15])).
% 0.22/0.56  fof(f15,axiom,(
% 0.22/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.22/0.57  fof(f272,plain,(
% 0.22/0.57    k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3))),
% 0.22/0.57    inference(subsumption_resolution,[],[f271,f171])).
% 0.22/0.57  fof(f271,plain,(
% 0.22/0.57    k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3)) | ~v1_relat_1(sK3)),
% 0.22/0.57    inference(subsumption_resolution,[],[f270,f67])).
% 0.22/0.57  fof(f270,plain,(
% 0.22/0.57    k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)),
% 0.22/0.57    inference(resolution,[],[f88,f70])).
% 0.22/0.57  fof(f70,plain,(
% 0.22/0.57    v2_funct_1(sK3)),
% 0.22/0.57    inference(cnf_transformation,[],[f48])).
% 0.22/0.57  % (29854)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.57  fof(f88,plain,(
% 0.22/0.57    ( ! [X0] : (~v2_funct_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f37])).
% 0.22/0.57  fof(f37,plain,(
% 0.22/0.57    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.57    inference(flattening,[],[f36])).
% 0.22/0.57  fof(f36,plain,(
% 0.22/0.57    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.57    inference(ennf_transformation,[],[f12])).
% 0.22/0.57  fof(f12,axiom,(
% 0.22/0.57    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 0.22/0.57  fof(f501,plain,(
% 0.22/0.57    m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK3)),k1_relat_1(sK3))))),
% 0.22/0.57    inference(forward_demodulation,[],[f500,f280])).
% 0.22/0.57  fof(f280,plain,(
% 0.22/0.57    k1_relat_1(sK3) = k2_relat_1(k2_funct_1(sK3))),
% 0.22/0.57    inference(subsumption_resolution,[],[f279,f171])).
% 0.22/0.57  fof(f279,plain,(
% 0.22/0.57    k1_relat_1(sK3) = k2_relat_1(k2_funct_1(sK3)) | ~v1_relat_1(sK3)),
% 0.22/0.57    inference(subsumption_resolution,[],[f278,f67])).
% 0.22/0.57  fof(f278,plain,(
% 0.22/0.57    k1_relat_1(sK3) = k2_relat_1(k2_funct_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)),
% 0.22/0.57    inference(resolution,[],[f89,f70])).
% 0.22/0.57  fof(f89,plain,(
% 0.22/0.57    ( ! [X0] : (~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f37])).
% 0.22/0.57  fof(f500,plain,(
% 0.22/0.57    m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK3)),k2_relat_1(k2_funct_1(sK3)))))),
% 0.22/0.57    inference(subsumption_resolution,[],[f495,f171])).
% 0.22/0.57  fof(f495,plain,(
% 0.22/0.57    m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK3)),k2_relat_1(k2_funct_1(sK3))))) | ~v1_relat_1(sK3)),
% 0.22/0.57    inference(resolution,[],[f254,f67])).
% 0.22/0.57  fof(f254,plain,(
% 0.22/0.57    ( ! [X0] : (~v1_funct_1(X0) | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(X0)),k2_relat_1(k2_funct_1(X0))))) | ~v1_relat_1(X0)) )),
% 0.22/0.57    inference(subsumption_resolution,[],[f247,f86])).
% 0.22/0.57  fof(f86,plain,(
% 0.22/0.57    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f35])).
% 0.22/0.57  fof(f247,plain,(
% 0.22/0.57    ( ! [X0] : (m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(X0)),k2_relat_1(k2_funct_1(X0))))) | ~v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.57    inference(resolution,[],[f85,f87])).
% 0.22/0.57  fof(f85,plain,(
% 0.22/0.57    ( ! [X0] : (~v1_funct_1(X0) | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_relat_1(X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f33])).
% 0.22/0.57  fof(f33,plain,(
% 0.22/0.57    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.57    inference(flattening,[],[f32])).
% 0.22/0.57  fof(f32,plain,(
% 0.22/0.57    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.57    inference(ennf_transformation,[],[f20])).
% 0.22/0.57  fof(f20,axiom,(
% 0.22/0.57    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).
% 0.22/0.57  fof(f338,plain,(
% 0.22/0.57    v1_funct_2(k2_funct_1(sK3),sK2,k1_relat_1(sK3)) | ~v1_funct_1(k2_funct_1(sK3)) | ~v1_relat_1(k2_funct_1(sK3))),
% 0.22/0.57    inference(backward_demodulation,[],[f281,f332])).
% 0.22/0.57  fof(f281,plain,(
% 0.22/0.57    v1_funct_2(k2_funct_1(sK3),k2_relat_1(sK3),k1_relat_1(sK3)) | ~v1_funct_1(k2_funct_1(sK3)) | ~v1_relat_1(k2_funct_1(sK3))),
% 0.22/0.57    inference(backward_demodulation,[],[f273,f280])).
% 0.22/0.57  fof(f273,plain,(
% 0.22/0.57    v1_funct_2(k2_funct_1(sK3),k2_relat_1(sK3),k2_relat_1(k2_funct_1(sK3))) | ~v1_funct_1(k2_funct_1(sK3)) | ~v1_relat_1(k2_funct_1(sK3))),
% 0.22/0.57    inference(superposition,[],[f84,f272])).
% 0.22/0.57  fof(f84,plain,(
% 0.22/0.57    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f33])).
% 0.22/0.57  fof(f604,plain,(
% 0.22/0.57    m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | k1_xboole_0 = sK2),
% 0.22/0.57    inference(superposition,[],[f502,f592])).
% 0.22/0.57  fof(f72,plain,(
% 0.22/0.57    ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(k2_funct_1(sK3))),
% 0.22/0.57    inference(cnf_transformation,[],[f48])).
% 0.22/0.57  fof(f346,plain,(
% 0.22/0.57    k1_xboole_0 != sK2 | k1_xboole_0 = sK3),
% 0.22/0.57    inference(subsumption_resolution,[],[f343,f171])).
% 0.22/0.57  fof(f343,plain,(
% 0.22/0.57    k1_xboole_0 != sK2 | k1_xboole_0 = sK3 | ~v1_relat_1(sK3)),
% 0.22/0.57    inference(superposition,[],[f81,f332])).
% 0.22/0.57  fof(f81,plain,(
% 0.22/0.57    ( ! [X0] : (k1_xboole_0 != k2_relat_1(X0) | k1_xboole_0 = X0 | ~v1_relat_1(X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f30])).
% 0.22/0.57  fof(f30,plain,(
% 0.22/0.57    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.22/0.57    inference(flattening,[],[f29])).
% 0.22/0.57  fof(f29,plain,(
% 0.22/0.57    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.57    inference(ennf_transformation,[],[f9])).
% 0.22/0.57  fof(f9,axiom,(
% 0.22/0.57    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).
% 0.22/0.57  fof(f674,plain,(
% 0.22/0.57    k1_xboole_0 = k2_funct_1(k1_xboole_0) | k1_xboole_0 != k1_relat_1(sK3)),
% 0.22/0.57    inference(backward_demodulation,[],[f513,f627])).
% 0.22/0.57  fof(f513,plain,(
% 0.22/0.57    k1_xboole_0 != k1_relat_1(sK3) | k1_xboole_0 = k2_funct_1(sK3)),
% 0.22/0.57    inference(subsumption_resolution,[],[f284,f507])).
% 0.22/0.57  fof(f284,plain,(
% 0.22/0.57    k1_xboole_0 != k1_relat_1(sK3) | k1_xboole_0 = k2_funct_1(sK3) | ~v1_relat_1(k2_funct_1(sK3))),
% 0.22/0.57    inference(superposition,[],[f81,f280])).
% 0.22/0.57  fof(f718,plain,(
% 0.22/0.57    ~v1_funct_1(k2_funct_1(k1_xboole_0))),
% 0.22/0.57    inference(forward_demodulation,[],[f717,f627])).
% 0.22/0.57  fof(f717,plain,(
% 0.22/0.57    ~v1_funct_1(k2_funct_1(sK3))),
% 0.22/0.57    inference(subsumption_resolution,[],[f716,f182])).
% 0.22/0.57  fof(f182,plain,(
% 0.22/0.57    ( ! [X1] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X1)) )),
% 0.22/0.57    inference(superposition,[],[f106,f177])).
% 0.22/0.57  fof(f177,plain,(
% 0.22/0.57    ( ! [X0] : (k1_xboole_0 = sK8(k1_xboole_0,X0)) )),
% 0.22/0.57    inference(resolution,[],[f175,f82])).
% 0.22/0.57  fof(f175,plain,(
% 0.22/0.57    ( ! [X0] : (r1_tarski(sK8(k1_xboole_0,X0),k1_xboole_0)) )),
% 0.22/0.57    inference(resolution,[],[f159,f98])).
% 0.22/0.57  fof(f159,plain,(
% 0.22/0.57    ( ! [X1] : (m1_subset_1(sK8(k1_xboole_0,X1),k1_zfmisc_1(k1_xboole_0))) )),
% 0.22/0.57    inference(superposition,[],[f103,f120])).
% 0.22/0.57  fof(f120,plain,(
% 0.22/0.57    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.22/0.57    inference(equality_resolution,[],[f101])).
% 0.22/0.57  fof(f101,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 0.22/0.57    inference(cnf_transformation,[],[f61])).
% 0.22/0.57  fof(f103,plain,(
% 0.22/0.57    ( ! [X0,X1] : (m1_subset_1(sK8(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.57    inference(cnf_transformation,[],[f63])).
% 0.22/0.57  fof(f63,plain,(
% 0.22/0.57    ! [X0,X1] : (v1_funct_2(sK8(X0,X1),X0,X1) & v1_funct_1(sK8(X0,X1)) & v1_relat_1(sK8(X0,X1)) & m1_subset_1(sK8(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f25,f62])).
% 0.22/0.57  fof(f62,plain,(
% 0.22/0.57    ! [X1,X0] : (? [X2] : (v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & v1_relat_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (v1_funct_2(sK8(X0,X1),X0,X1) & v1_funct_1(sK8(X0,X1)) & v1_relat_1(sK8(X0,X1)) & m1_subset_1(sK8(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.22/0.57    introduced(choice_axiom,[])).
% 0.22/0.57  fof(f25,plain,(
% 0.22/0.57    ! [X0,X1] : ? [X2] : (v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & v1_relat_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.57    inference(pure_predicate_removal,[],[f24])).
% 0.22/0.57  fof(f24,plain,(
% 0.22/0.57    ! [X0,X1] : ? [X2] : (v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & v4_relat_1(X2,X0) & v1_relat_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.57    inference(pure_predicate_removal,[],[f18])).
% 0.22/0.57  fof(f18,axiom,(
% 0.22/0.57    ! [X0,X1] : ? [X2] : (v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & v5_relat_1(X2,X1) & v4_relat_1(X2,X0) & v1_relat_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_funct_2)).
% 0.22/0.57  fof(f106,plain,(
% 0.22/0.57    ( ! [X0,X1] : (v1_funct_2(sK8(X0,X1),X0,X1)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f63])).
% 0.22/0.57  fof(f716,plain,(
% 0.22/0.57    ~v1_funct_2(k1_xboole_0,k1_xboole_0,sK1) | ~v1_funct_1(k2_funct_1(sK3))),
% 0.22/0.57    inference(forward_demodulation,[],[f715,f694])).
% 0.22/0.57  fof(f715,plain,(
% 0.22/0.57    ~v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK1) | ~v1_funct_1(k2_funct_1(sK3))),
% 0.22/0.57    inference(forward_demodulation,[],[f714,f627])).
% 0.22/0.57  fof(f714,plain,(
% 0.22/0.57    ~v1_funct_2(k2_funct_1(sK3),k1_xboole_0,sK1) | ~v1_funct_1(k2_funct_1(sK3))),
% 0.22/0.57    inference(forward_demodulation,[],[f713,f625])).
% 0.22/0.57  fof(f713,plain,(
% 0.22/0.57    ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))),
% 0.22/0.57    inference(subsumption_resolution,[],[f712,f137])).
% 0.22/0.57  fof(f137,plain,(
% 0.22/0.57    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 0.22/0.57    inference(backward_demodulation,[],[f132,f135])).
% 0.22/0.57  fof(f712,plain,(
% 0.22/0.57    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))),
% 0.22/0.57    inference(forward_demodulation,[],[f711,f694])).
% 0.22/0.57  fof(f711,plain,(
% 0.22/0.57    ~m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))),
% 0.22/0.57    inference(forward_demodulation,[],[f710,f627])).
% 0.22/0.57  fof(f710,plain,(
% 0.22/0.57    ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))),
% 0.22/0.57    inference(forward_demodulation,[],[f631,f120])).
% 0.22/0.57  fof(f631,plain,(
% 0.22/0.57    ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))),
% 0.22/0.57    inference(backward_demodulation,[],[f72,f625])).
% 0.22/0.57  % SZS output end Proof for theBenchmark
% 0.22/0.57  % (29848)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.57  % (29834)------------------------------
% 0.22/0.57  % (29834)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (29834)Termination reason: Refutation
% 0.22/0.57  
% 0.22/0.57  % (29834)Memory used [KB]: 6780
% 0.22/0.57  % (29834)Time elapsed: 0.117 s
% 0.22/0.57  % (29834)------------------------------
% 0.22/0.57  % (29834)------------------------------
% 0.22/0.57  % (29820)Success in time 0.207 s
%------------------------------------------------------------------------------
