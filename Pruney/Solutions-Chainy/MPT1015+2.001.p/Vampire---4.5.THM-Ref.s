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
% DateTime   : Thu Dec  3 13:05:25 EST 2020

% Result     : Theorem 6.82s
% Output     : Refutation 6.90s
% Verified   : 
% Statistics : Number of formulae       :  239 (4593 expanded)
%              Number of leaves         :   28 (1339 expanded)
%              Depth                    :   68
%              Number of atoms          : 1188 (33744 expanded)
%              Number of equality atoms :  166 (1463 expanded)
%              Maximal formula depth    :   23 (   8 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2859,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2858,f148])).

fof(f148,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(backward_demodulation,[],[f138,f146])).

fof(f146,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f145,f138])).

fof(f145,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f140,f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f140,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f92,f78])).

fof(f78,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
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

fof(f138,plain,(
    m1_subset_1(k6_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[],[f126,f132])).

fof(f132,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f126,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f81,f79])).

fof(f79,plain,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f81,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f2858,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f2857,f132])).

fof(f2857,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(resolution,[],[f2391,f135])).

fof(f135,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(duplicate_literal_removal,[],[f134])).

fof(f134,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f120])).

fof(f120,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f2391,plain,(
    ~ r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f1870,f2382])).

fof(f2382,plain,(
    k1_xboole_0 = sK4 ),
    inference(subsumption_resolution,[],[f2381,f78])).

fof(f2381,plain,
    ( ~ r1_tarski(k1_xboole_0,sK4)
    | k1_xboole_0 = sK4 ),
    inference(forward_demodulation,[],[f2380,f132])).

fof(f2380,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),sK4)
    | k1_xboole_0 = sK4 ),
    inference(forward_demodulation,[],[f2379,f1713])).

fof(f1713,plain,(
    k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f1712,f287])).

fof(f287,plain,(
    r2_relset_1(sK2,sK2,sK3,sK3) ),
    inference(backward_demodulation,[],[f75,f285])).

fof(f285,plain,(
    sK3 = k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3) ),
    inference(subsumption_resolution,[],[f284,f72])).

fof(f72,plain,(
    v1_funct_1(sK4) ),
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_funct_2)).

fof(f284,plain,
    ( sK3 = k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3)
    | ~ v1_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f283,f74])).

fof(f74,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(cnf_transformation,[],[f55])).

fof(f283,plain,
    ( sK3 = k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v1_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f282,f69])).

fof(f69,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f55])).

fof(f282,plain,
    ( sK3 = k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v1_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f279,f71])).

fof(f71,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(cnf_transformation,[],[f55])).

fof(f279,plain,
    ( sK3 = k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v1_funct_1(sK4) ),
    inference(resolution,[],[f210,f123])).

fof(f123,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f210,plain,
    ( ~ m1_subset_1(k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | sK3 = k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3) ),
    inference(subsumption_resolution,[],[f203,f71])).

fof(f203,plain,
    ( sK3 = k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ m1_subset_1(k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(resolution,[],[f119,f75])).

fof(f119,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f75,plain,(
    r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3),sK3) ),
    inference(cnf_transformation,[],[f55])).

fof(f1712,plain,
    ( ~ r2_relset_1(sK2,sK2,sK3,sK3)
    | k1_xboole_0 = sK2 ),
    inference(forward_demodulation,[],[f1711,f304])).

fof(f304,plain,(
    sK3 = k5_relat_1(sK4,sK3) ),
    inference(subsumption_resolution,[],[f303,f72])).

fof(f303,plain,
    ( sK3 = k5_relat_1(sK4,sK3)
    | ~ v1_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f302,f74])).

fof(f302,plain,
    ( sK3 = k5_relat_1(sK4,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v1_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f301,f69])).

fof(f301,plain,
    ( sK3 = k5_relat_1(sK4,sK3)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v1_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f295,f71])).

fof(f295,plain,
    ( sK3 = k5_relat_1(sK4,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v1_funct_1(sK4) ),
    inference(superposition,[],[f285,f121])).

fof(f121,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f1711,plain,
    ( k1_xboole_0 = sK2
    | ~ r2_relset_1(sK2,sK2,k5_relat_1(sK4,sK3),sK3) ),
    inference(subsumption_resolution,[],[f1710,f72])).

fof(f1710,plain,
    ( k1_xboole_0 = sK2
    | ~ v1_funct_1(sK4)
    | ~ r2_relset_1(sK2,sK2,k5_relat_1(sK4,sK3),sK3) ),
    inference(subsumption_resolution,[],[f1709,f73])).

fof(f73,plain,(
    v1_funct_2(sK4,sK2,sK2) ),
    inference(cnf_transformation,[],[f55])).

fof(f1709,plain,
    ( k1_xboole_0 = sK2
    | ~ v1_funct_2(sK4,sK2,sK2)
    | ~ v1_funct_1(sK4)
    | ~ r2_relset_1(sK2,sK2,k5_relat_1(sK4,sK3),sK3) ),
    inference(subsumption_resolution,[],[f1708,f74])).

fof(f1708,plain,
    ( k1_xboole_0 = sK2
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v1_funct_2(sK4,sK2,sK2)
    | ~ v1_funct_1(sK4)
    | ~ r2_relset_1(sK2,sK2,k5_relat_1(sK4,sK3),sK3) ),
    inference(duplicate_literal_removal,[],[f1703])).

fof(f1703,plain,
    ( k1_xboole_0 = sK2
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v1_funct_2(sK4,sK2,sK2)
    | ~ v1_funct_1(sK4)
    | k1_xboole_0 = sK2
    | ~ r2_relset_1(sK2,sK2,k5_relat_1(sK4,sK3),sK3) ),
    inference(resolution,[],[f1638,f1125])).

fof(f1125,plain,(
    ! [X3] :
      ( r2_relset_1(sK2,sK2,X3,sK4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
      | ~ v1_funct_2(X3,sK2,sK2)
      | ~ v1_funct_1(X3)
      | k1_xboole_0 = sK2
      | ~ r2_relset_1(sK2,sK2,k5_relat_1(X3,sK3),sK3) ) ),
    inference(subsumption_resolution,[],[f1124,f74])).

fof(f1124,plain,(
    ! [X3] :
      ( ~ r2_relset_1(sK2,sK2,k5_relat_1(X3,sK3),sK3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
      | ~ v1_funct_2(X3,sK2,sK2)
      | ~ v1_funct_1(X3)
      | k1_xboole_0 = sK2
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
      | r2_relset_1(sK2,sK2,X3,sK4) ) ),
    inference(subsumption_resolution,[],[f1123,f73])).

fof(f1123,plain,(
    ! [X3] :
      ( ~ r2_relset_1(sK2,sK2,k5_relat_1(X3,sK3),sK3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
      | ~ v1_funct_2(X3,sK2,sK2)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(sK4,sK2,sK2)
      | k1_xboole_0 = sK2
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
      | r2_relset_1(sK2,sK2,X3,sK4) ) ),
    inference(subsumption_resolution,[],[f1118,f72])).

fof(f1118,plain,(
    ! [X3] :
      ( ~ r2_relset_1(sK2,sK2,k5_relat_1(X3,sK3),sK3)
      | ~ v1_funct_1(sK4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
      | ~ v1_funct_2(X3,sK2,sK2)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(sK4,sK2,sK2)
      | k1_xboole_0 = sK2
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
      | r2_relset_1(sK2,sK2,X3,sK4) ) ),
    inference(superposition,[],[f856,f285])).

fof(f856,plain,(
    ! [X10,X11,X9] :
      ( ~ r2_relset_1(X10,sK2,k5_relat_1(X11,sK3),k1_partfun1(X10,sK2,sK2,sK2,X9,sK3))
      | ~ v1_funct_1(X9)
      | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X10,sK2)))
      | ~ v1_funct_2(X11,X10,sK2)
      | ~ v1_funct_1(X11)
      | ~ v1_funct_2(X9,X10,sK2)
      | k1_xboole_0 = sK2
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X10,sK2)))
      | r2_relset_1(X10,sK2,X11,X9) ) ),
    inference(subsumption_resolution,[],[f843,f71])).

fof(f843,plain,(
    ! [X10,X11,X9] :
      ( ~ v1_funct_2(X9,X10,sK2)
      | ~ v1_funct_1(X9)
      | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X10,sK2)))
      | ~ v1_funct_2(X11,X10,sK2)
      | ~ v1_funct_1(X11)
      | ~ r2_relset_1(X10,sK2,k5_relat_1(X11,sK3),k1_partfun1(X10,sK2,sK2,sK2,X9,sK3))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
      | k1_xboole_0 = sK2
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X10,sK2)))
      | r2_relset_1(X10,sK2,X11,X9) ) ),
    inference(duplicate_literal_removal,[],[f841])).

fof(f841,plain,(
    ! [X10,X11,X9] :
      ( ~ v1_funct_2(X9,X10,sK2)
      | ~ v1_funct_1(X9)
      | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X10,sK2)))
      | ~ v1_funct_2(X11,X10,sK2)
      | ~ v1_funct_1(X11)
      | ~ r2_relset_1(X10,sK2,k5_relat_1(X11,sK3),k1_partfun1(X10,sK2,sK2,sK2,X9,sK3))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
      | k1_xboole_0 = sK2
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X10,sK2)))
      | r2_relset_1(X10,sK2,X11,X9)
      | k1_xboole_0 = sK2 ) ),
    inference(resolution,[],[f642,f70])).

fof(f70,plain,(
    v1_funct_2(sK3,sK2,sK2) ),
    inference(cnf_transformation,[],[f55])).

fof(f642,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_2(sK3,X2,X4)
      | ~ v1_funct_2(X0,X1,X2)
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X3,X1,X2)
      | ~ v1_funct_1(X3)
      | ~ r2_relset_1(X1,X4,k5_relat_1(X3,sK3),k1_partfun1(X1,X2,X2,X4,X0,sK3))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | r2_relset_1(X1,X2,X3,X0)
      | k1_xboole_0 = X4 ) ),
    inference(subsumption_resolution,[],[f640,f69])).

fof(f640,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X0,X1,X2)
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X3,X1,X2)
      | ~ v1_funct_1(X3)
      | ~ r2_relset_1(X1,X4,k5_relat_1(X3,sK3),k1_partfun1(X1,X2,X2,X4,X0,sK3))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
      | ~ v1_funct_1(sK3)
      | k1_xboole_0 = X2
      | ~ v1_funct_2(sK3,X2,X4)
      | r2_relset_1(X1,X2,X3,X0)
      | k1_xboole_0 = X4 ) ),
    inference(resolution,[],[f417,f76])).

fof(f76,plain,(
    v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f55])).

fof(f417,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v2_funct_1(X5)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ r2_relset_1(X0,X4,k5_relat_1(X2,X5),k1_partfun1(X0,X1,X1,X4,X3,X5))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X4)))
      | ~ v1_funct_1(X5)
      | k1_xboole_0 = X1
      | ~ v1_funct_2(X5,X1,X4)
      | r2_relset_1(X0,X1,X2,X3)
      | k1_xboole_0 = X4 ) ),
    inference(duplicate_literal_removal,[],[f413])).

fof(f413,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ r2_relset_1(X0,X4,k5_relat_1(X2,X5),k1_partfun1(X0,X1,X1,X4,X3,X5))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X4)))
      | ~ v1_funct_1(X5)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X4)))
      | ~ v1_funct_2(X5,X1,X4)
      | ~ v1_funct_1(X5)
      | ~ v2_funct_1(X5)
      | k1_xboole_0 = X4 ) ),
    inference(resolution,[],[f275,f217])).

fof(f217,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X2,X0)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X2,X1,X0)
      | ~ v1_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f118,f107])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ v2_funct_1(X1)
      | sP0(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1,X2] :
      ( ( ( v2_funct_1(X1)
          | ~ sP0(X2,X1,X0) )
        & ( sP0(X2,X1,X0)
          | ~ v2_funct_1(X1) ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f61])).

fof(f61,plain,(
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

fof(f118,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_funct_2)).

fof(f275,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ sP0(X1,X4,X2)
      | r2_relset_1(X0,X1,X3,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X5,X0,X1)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ r2_relset_1(X0,X2,k5_relat_1(X3,X4),k1_partfun1(X0,X1,X1,X2,X5,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4) ) ),
    inference(duplicate_literal_removal,[],[f272])).

fof(f272,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r2_relset_1(X0,X2,k5_relat_1(X3,X4),k1_partfun1(X0,X1,X1,X2,X5,X4))
      | r2_relset_1(X0,X1,X3,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X5,X0,X1)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ sP0(X1,X4,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3) ) ),
    inference(superposition,[],[f109,f121])).

fof(f109,plain,(
    ! [X6,X2,X0,X8,X7,X1] :
      ( ~ r2_relset_1(X6,X2,k1_partfun1(X6,X0,X0,X2,X7,X1),k1_partfun1(X6,X0,X0,X2,X8,X1))
      | r2_relset_1(X6,X0,X7,X8)
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X0)))
      | ~ v1_funct_2(X8,X6,X0)
      | ~ v1_funct_1(X8)
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X6,X0)))
      | ~ v1_funct_2(X7,X6,X0)
      | ~ v1_funct_1(X7)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f64,f66,f65])).

fof(f65,plain,(
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

fof(f66,plain,(
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

fof(f64,plain,(
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
    inference(rectify,[],[f63])).

fof(f63,plain,(
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

fof(f1638,plain,
    ( ~ r2_relset_1(sK2,sK2,sK4,sK4)
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f125,f1629])).

fof(f1629,plain,
    ( sK4 = k6_relat_1(sK2)
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f1628,f126])).

fof(f1628,plain,
    ( k1_xboole_0 = sK2
    | sK4 = k6_relat_1(sK2)
    | ~ m1_subset_1(k6_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(subsumption_resolution,[],[f1627,f1595])).

fof(f1595,plain,(
    v1_funct_1(k6_relat_1(sK2)) ),
    inference(resolution,[],[f1587,f71])).

fof(f1587,plain,(
    ! [X10,X9] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))
      | v1_funct_1(k6_relat_1(sK2)) ) ),
    inference(resolution,[],[f1579,f71])).

fof(f1579,plain,(
    ! [X14,X15,X13,X16] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))
      | v1_funct_1(k6_relat_1(sK2))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X15,X16))) ) ),
    inference(resolution,[],[f1571,f71])).

fof(f1571,plain,(
    ! [X21,X19,X17,X22,X20,X18] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X21,X22)))
      | v1_funct_1(k6_relat_1(sK2))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X17,X18))) ) ),
    inference(resolution,[],[f1562,f71])).

fof(f1562,plain,(
    ! [X28,X26,X24,X23,X21,X27,X25,X22] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X27,X28)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))
      | v1_funct_1(k6_relat_1(sK2))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X21,X22))) ) ),
    inference(resolution,[],[f1552,f71])).

fof(f1552,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | v1_funct_1(k6_relat_1(sK2))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(resolution,[],[f1540,f85])).

fof(f85,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f1540,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( ~ v1_relat_1(X4)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X4))
      | v1_funct_1(k6_relat_1(sK2))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X7,X8))) ) ),
    inference(resolution,[],[f1533,f85])).

fof(f1533,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( ~ v1_relat_1(X7)
      | v1_funct_1(k6_relat_1(sK2))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X6))
      | ~ v1_relat_1(X6)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X7))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(subsumption_resolution,[],[f1530,f130])).

fof(f130,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f57])).

fof(f1530,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_funct_1(k6_relat_1(sK2))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X6))
      | ~ v1_relat_1(X6)
      | ~ r1_tarski(k2_relat_1(sK3),k2_relat_1(sK3))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X7))
      | ~ v1_relat_1(X7) ) ),
    inference(resolution,[],[f1522,f211])).

fof(f211,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
      | ~ r1_tarski(k2_relat_1(sK3),X0)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f199,f82])).

fof(f82,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f199,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK3)
      | ~ r1_tarski(k2_relat_1(sK3),X0)
      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) ) ),
    inference(subsumption_resolution,[],[f197,f69])).

fof(f197,plain,(
    ! [X0] :
      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
      | ~ r1_tarski(k2_relat_1(sK3),X0)
      | ~ v1_funct_1(sK3)
      | ~ v1_relat_1(sK3) ) ),
    inference(superposition,[],[f88,f192])).

fof(f192,plain,(
    sK2 = k1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f189,f71])).

fof(f189,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | sK2 = k1_relat_1(sK3) ),
    inference(resolution,[],[f183,f70])).

fof(f183,plain,(
    ! [X0] :
      ( ~ v1_funct_2(sK3,X0,X0)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | k1_relat_1(sK3) = X0 ) ),
    inference(resolution,[],[f182,f69])).

fof(f182,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | k1_relat_1(X1) = X0 ) ),
    inference(duplicate_literal_removal,[],[f179])).

fof(f179,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(superposition,[],[f89,f99])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f89,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
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
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k1_relset_1(X0,X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_2)).

fof(f88,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

fof(f1522,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_relat_1(sK3))))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | v1_funct_1(k6_relat_1(sK2))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X6))
      | ~ v1_relat_1(X6) ) ),
    inference(resolution,[],[f1514,f82])).

fof(f1514,plain,(
    ! [X12,X10,X8,X7,X11,X9] :
      ( ~ v1_relat_1(sK3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))
      | v1_funct_1(k6_relat_1(sK2))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_relat_1(sK3)))) ) ),
    inference(forward_demodulation,[],[f1513,f192])).

fof(f1513,plain,(
    ! [X12,X10,X8,X7,X11,X9] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))
      | v1_funct_1(k6_relat_1(sK2))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))
      | ~ v1_relat_1(sK3) ) ),
    inference(subsumption_resolution,[],[f1512,f69])).

fof(f1512,plain,(
    ! [X12,X10,X8,X7,X11,X9] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))
      | v1_funct_1(k6_relat_1(sK2))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))
      | ~ v1_funct_1(sK3)
      | ~ v1_relat_1(sK3) ) ),
    inference(subsumption_resolution,[],[f1508,f130])).

fof(f1508,plain,(
    ! [X12,X10,X8,X7,X11,X9] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))
      | v1_funct_1(k6_relat_1(sK2))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))
      | ~ r1_tarski(k2_relat_1(sK3),k2_relat_1(sK3))
      | ~ v1_funct_1(sK3)
      | ~ v1_relat_1(sK3) ) ),
    inference(resolution,[],[f1504,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f1504,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_2(sK3,X6,k2_relat_1(sK3))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | v1_funct_1(k6_relat_1(sK2))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X6,k2_relat_1(sK3))))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f1484])).

fof(f1484,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( k2_relat_1(sK3) != X6
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | v1_funct_1(k6_relat_1(sK2))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X7,X6)))
      | ~ v1_funct_2(sK3,X7,X6) ) ),
    inference(resolution,[],[f1475,f322])).

fof(f322,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k2_relat_1(sK3) != X1
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(sK3,X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f321])).

fof(f321,plain,(
    ! [X0,X1] :
      ( k2_relat_1(sK3) != X1
      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(sK3,X0,X1)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(superposition,[],[f248,f98])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f248,plain,(
    ! [X0,X1] :
      ( k2_relset_1(X0,X1,sK3) != X1
      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(sK3,X0,X1) ) ),
    inference(subsumption_resolution,[],[f246,f69])).

fof(f246,plain,(
    ! [X0,X1] :
      ( k2_relset_1(X0,X1,sK3) != X1
      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(sK3,X0,X1)
      | ~ v1_funct_1(sK3) ) ),
    inference(resolution,[],[f106,f76])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

fof(f1475,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | v1_funct_1(k6_relat_1(sK2))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) ) ),
    inference(resolution,[],[f1458,f130])).

fof(f1458,plain,(
    ! [X14,X12,X10,X17,X15,X13,X11,X9,X18,X16] :
      ( ~ r1_tarski(k2_zfmisc_1(sK2,sK2),k2_zfmisc_1(X17,X18))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))
      | v1_funct_1(k6_relat_1(sK2))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))
      | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X15,X16)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X9,X10))) ) ),
    inference(resolution,[],[f1452,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f1452,plain,(
    ! [X30,X28,X26,X33,X31,X29,X27,X25,X34,X32] :
      ( ~ m1_subset_1(k2_zfmisc_1(sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(X31,X32)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X27,X28)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))
      | v1_funct_1(k6_relat_1(sK2))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))
      | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X33,X34))) ) ),
    inference(resolution,[],[f1403,f71])).

fof(f1403,plain,(
    ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1,X9] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(X2))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
      | v1_funct_1(k6_relat_1(sK2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
      | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X9,X10))) ) ),
    inference(resolution,[],[f1322,f85])).

fof(f1322,plain,(
    ! [X26,X24,X23,X21,X19,X27,X25,X22,X20,X18] :
      ( ~ v1_relat_1(X27)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X22))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))
      | v1_funct_1(k6_relat_1(sK2))
      | ~ m1_subset_1(X22,k1_zfmisc_1(X27))
      | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X18,X19))) ) ),
    inference(resolution,[],[f1311,f82])).

fof(f1311,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( ~ v1_relat_1(X6)
      | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X6))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
      | v1_funct_1(k6_relat_1(sK2)) ) ),
    inference(resolution,[],[f1307,f85])).

fof(f1307,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( ~ v1_relat_1(X7)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X6))
      | ~ v1_relat_1(X6)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X7))
      | v1_funct_1(k6_relat_1(sK2)) ) ),
    inference(subsumption_resolution,[],[f1304,f130])).

fof(f1304,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( v1_funct_1(k6_relat_1(sK2))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X6))
      | ~ v1_relat_1(X6)
      | ~ r1_tarski(k2_relat_1(sK3),k2_relat_1(sK3))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X7))
      | ~ v1_relat_1(X7) ) ),
    inference(resolution,[],[f1301,f211])).

fof(f1301,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_relat_1(sK3))))
      | v1_funct_1(k6_relat_1(sK2))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X6))
      | ~ v1_relat_1(X6) ) ),
    inference(resolution,[],[f1295,f82])).

fof(f1295,plain,(
    ! [X12,X10,X8,X7,X11,X9] :
      ( ~ v1_relat_1(sK3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
      | v1_funct_1(k6_relat_1(sK2))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))
      | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X11,X12)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_relat_1(sK3)))) ) ),
    inference(forward_demodulation,[],[f1294,f192])).

fof(f1294,plain,(
    ! [X12,X10,X8,X7,X11,X9] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))))
      | v1_funct_1(k6_relat_1(sK2))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))
      | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X11,X12)))
      | ~ v1_relat_1(sK3) ) ),
    inference(subsumption_resolution,[],[f1293,f69])).

fof(f1293,plain,(
    ! [X12,X10,X8,X7,X11,X9] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))))
      | v1_funct_1(k6_relat_1(sK2))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))
      | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X11,X12)))
      | ~ v1_funct_1(sK3)
      | ~ v1_relat_1(sK3) ) ),
    inference(subsumption_resolution,[],[f1289,f130])).

fof(f1289,plain,(
    ! [X12,X10,X8,X7,X11,X9] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))))
      | v1_funct_1(k6_relat_1(sK2))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))
      | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X11,X12)))
      | ~ r1_tarski(k2_relat_1(sK3),k2_relat_1(sK3))
      | ~ v1_funct_1(sK3)
      | ~ v1_relat_1(sK3) ) ),
    inference(resolution,[],[f1285,f87])).

fof(f1285,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_2(sK3,X2,k2_relat_1(sK3))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,k2_relat_1(sK3))))
      | v1_funct_1(k6_relat_1(sK2))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ) ),
    inference(equality_resolution,[],[f1278])).

fof(f1278,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( k2_relat_1(sK3) != X5
      | v1_funct_1(k6_relat_1(sK2))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | ~ v1_funct_2(sK3,X4,X5)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
      | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(resolution,[],[f1277,f85])).

fof(f1277,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( ~ v1_relat_1(X6)
      | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | v1_funct_1(k6_relat_1(sK2))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(sK3,X0,X1)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X6))
      | k2_relat_1(sK3) != X1 ) ),
    inference(duplicate_literal_removal,[],[f1276])).

fof(f1276,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( k2_relat_1(sK3) != X1
      | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | v1_funct_1(k6_relat_1(sK2))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(sK3,X0,X1)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X6))
      | ~ v1_relat_1(X6)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(superposition,[],[f1049,f98])).

fof(f1049,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( k2_relset_1(X4,X5,sK3) != X5
      | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | v1_funct_1(k6_relat_1(sK2))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | ~ v1_funct_2(sK3,X4,X5)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X6))
      | ~ v1_relat_1(X6) ) ),
    inference(resolution,[],[f875,f82])).

fof(f875,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_relat_1(sK3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | v1_funct_1(k6_relat_1(sK2))
      | k2_relset_1(X4,X5,sK3) != X5
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | ~ v1_funct_2(sK3,X4,X5) ) ),
    inference(forward_demodulation,[],[f874,f192])).

fof(f874,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_1(k6_relat_1(k1_relat_1(sK3)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_relat_1(sK3)
      | k2_relset_1(X4,X5,sK3) != X5
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | ~ v1_funct_2(sK3,X4,X5) ) ),
    inference(subsumption_resolution,[],[f872,f69])).

fof(f872,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_1(k6_relat_1(k1_relat_1(sK3)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(sK3)
      | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_relat_1(sK3)
      | k2_relset_1(X4,X5,sK3) != X5
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | ~ v1_funct_2(sK3,X4,X5) ) ),
    inference(resolution,[],[f505,f76])).

fof(f505,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( ~ v2_funct_1(X0)
      | v1_funct_1(k6_relat_1(k1_relat_1(X0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_relat_1(X0)
      | k2_relset_1(X5,X6,X0) != X6
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
      | ~ v1_funct_2(X0,X5,X6) ) ),
    inference(duplicate_literal_removal,[],[f504])).

fof(f504,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | v1_funct_1(k6_relat_1(k1_relat_1(X0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k2_relset_1(X5,X6,X0) != X6
      | ~ v2_funct_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
      | ~ v1_funct_2(X0,X5,X6)
      | ~ v1_funct_1(X0) ) ),
    inference(resolution,[],[f338,f104])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(k2_funct_1(X2))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f338,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_1(k2_funct_1(X0))
      | ~ m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | v1_funct_1(k6_relat_1(k1_relat_1(X0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f334])).

fof(f334,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_1(k6_relat_1(k1_relat_1(X0)))
      | ~ m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(k2_funct_1(X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f253,f83])).

fof(f83,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
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

fof(f253,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_1(k5_relat_1(X4,X5))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(duplicate_literal_removal,[],[f252])).

fof(f252,plain,(
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
    inference(superposition,[],[f122,f121])).

fof(f122,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f1627,plain,
    ( k1_xboole_0 = sK2
    | sK4 = k6_relat_1(sK2)
    | ~ v1_funct_1(k6_relat_1(sK2))
    | ~ m1_subset_1(k6_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(subsumption_resolution,[],[f1626,f127])).

fof(f127,plain,(
    ! [X0] : v1_partfun1(k6_relat_1(X0),X0) ),
    inference(definition_unfolding,[],[f80,f79])).

fof(f80,plain,(
    ! [X0] : v1_partfun1(k6_partfun1(X0),X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f1626,plain,
    ( k1_xboole_0 = sK2
    | sK4 = k6_relat_1(sK2)
    | ~ v1_partfun1(k6_relat_1(sK2),sK2)
    | ~ v1_funct_1(k6_relat_1(sK2))
    | ~ m1_subset_1(k6_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(resolution,[],[f1613,f103])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v1_partfun1(X2,X0)
          & v1_funct_1(X2) )
       => ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_2)).

fof(f1613,plain,
    ( ~ v1_funct_2(k6_relat_1(sK2),sK2,sK2)
    | k1_xboole_0 = sK2
    | sK4 = k6_relat_1(sK2) ),
    inference(resolution,[],[f1595,f1133])).

fof(f1133,plain,
    ( ~ v1_funct_1(k6_relat_1(sK2))
    | ~ v1_funct_2(k6_relat_1(sK2),sK2,sK2)
    | k1_xboole_0 = sK2
    | sK4 = k6_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f1132,f71])).

fof(f1132,plain,
    ( ~ v1_funct_2(k6_relat_1(sK2),sK2,sK2)
    | ~ v1_funct_1(k6_relat_1(sK2))
    | k1_xboole_0 = sK2
    | sK4 = k6_relat_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(subsumption_resolution,[],[f1129,f126])).

fof(f1129,plain,
    ( ~ v1_funct_2(k6_relat_1(sK2),sK2,sK2)
    | ~ v1_funct_1(k6_relat_1(sK2))
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(k6_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | sK4 = k6_relat_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(resolution,[],[f1128,f236])).

fof(f236,plain,(
    ! [X4,X5,X3] :
      ( r2_relset_1(X3,X4,k5_relat_1(k6_relat_1(X3),X5),X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ) ),
    inference(subsumption_resolution,[],[f233,f126])).

fof(f233,plain,(
    ! [X4,X5,X3] :
      ( r2_relset_1(X3,X4,k5_relat_1(k6_relat_1(X3),X5),X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ m1_subset_1(k6_relat_1(X3),k1_zfmisc_1(k2_zfmisc_1(X3,X3))) ) ),
    inference(duplicate_literal_removal,[],[f232])).

fof(f232,plain,(
    ! [X4,X5,X3] :
      ( r2_relset_1(X3,X4,k5_relat_1(k6_relat_1(X3),X5),X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ m1_subset_1(k6_relat_1(X3),k1_zfmisc_1(k2_zfmisc_1(X3,X3))) ) ),
    inference(superposition,[],[f129,f124])).

fof(f124,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

fof(f129,plain,(
    ! [X2,X0,X1] :
      ( r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_relat_1(X0),X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_unfolding,[],[f100,f79])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_2)).

fof(f1128,plain,(
    ! [X0] :
      ( ~ r2_relset_1(sK2,sK2,k5_relat_1(X0,sK3),sK3)
      | ~ v1_funct_2(X0,sK2,sK2)
      | ~ v1_funct_1(X0)
      | k1_xboole_0 = sK2
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
      | sK4 = X0 ) ),
    inference(subsumption_resolution,[],[f1127,f74])).

fof(f1127,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
      | ~ v1_funct_2(X0,sK2,sK2)
      | ~ v1_funct_1(X0)
      | k1_xboole_0 = sK2
      | ~ r2_relset_1(sK2,sK2,k5_relat_1(X0,sK3),sK3)
      | sK4 = X0
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ) ),
    inference(duplicate_literal_removal,[],[f1126])).

fof(f1126,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
      | ~ v1_funct_2(X0,sK2,sK2)
      | ~ v1_funct_1(X0)
      | k1_xboole_0 = sK2
      | ~ r2_relset_1(sK2,sK2,k5_relat_1(X0,sK3),sK3)
      | sK4 = X0
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ) ),
    inference(resolution,[],[f1125,f119])).

fof(f125,plain,(
    ~ r2_relset_1(sK2,sK2,sK4,k6_relat_1(sK2)) ),
    inference(definition_unfolding,[],[f77,f79])).

fof(f77,plain,(
    ~ r2_relset_1(sK2,sK2,sK4,k6_partfun1(sK2)) ),
    inference(cnf_transformation,[],[f55])).

fof(f2379,plain,
    ( k1_xboole_0 = sK4
    | ~ r1_tarski(k2_zfmisc_1(sK2,sK2),sK4) ),
    inference(forward_demodulation,[],[f1722,f132])).

fof(f1722,plain,
    ( sK4 = k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
    | ~ r1_tarski(k2_zfmisc_1(sK2,sK2),sK4) ),
    inference(backward_demodulation,[],[f165,f1713])).

fof(f165,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK2,sK2),sK4)
    | k2_zfmisc_1(sK2,sK2) = sK4 ),
    inference(resolution,[],[f159,f94])).

fof(f159,plain,
    ( ~ m1_subset_1(k2_zfmisc_1(sK2,sK2),k1_zfmisc_1(sK4))
    | k2_zfmisc_1(sK2,sK2) = sK4 ),
    inference(resolution,[],[f157,f74])).

fof(f157,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(X2))
      | X2 = X3
      | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ) ),
    inference(resolution,[],[f142,f93])).

fof(f142,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ) ),
    inference(resolution,[],[f92,f93])).

fof(f1870,plain,(
    ~ r2_relset_1(k1_xboole_0,k1_xboole_0,sK4,k1_xboole_0) ),
    inference(forward_demodulation,[],[f1718,f146])).

fof(f1718,plain,(
    ~ r2_relset_1(k1_xboole_0,k1_xboole_0,sK4,k6_relat_1(k1_xboole_0)) ),
    inference(backward_demodulation,[],[f125,f1713])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:41:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.52  % (32100)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.52  % (32109)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.53  % (32108)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.53  % (32096)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.54  % (32117)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.54  % (32095)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.54  % (32097)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.54  % (32098)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.54  % (32099)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.55  % (32101)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.55  % (32120)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.55  % (32111)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.55  % (32121)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.55  % (32123)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.55  % (32111)Refutation not found, incomplete strategy% (32111)------------------------------
% 0.22/0.55  % (32111)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (32111)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (32111)Memory used [KB]: 10746
% 0.22/0.55  % (32111)Time elapsed: 0.137 s
% 0.22/0.55  % (32111)------------------------------
% 0.22/0.55  % (32111)------------------------------
% 0.22/0.55  % (32104)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.56  % (32106)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.56  % (32105)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.56  % (32103)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.56  % (32107)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.56  % (32124)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.56  % (32113)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.56  % (32114)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.56  % (32115)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.56  % (32112)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.57  % (32116)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.57  % (32119)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.57  % (32122)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.57  % (32118)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.58  % (32110)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.59  % (32102)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 2.75/0.75  % (32095)Refutation not found, incomplete strategy% (32095)------------------------------
% 2.75/0.75  % (32095)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.75/0.76  % (32095)Termination reason: Refutation not found, incomplete strategy
% 2.75/0.76  
% 2.75/0.76  % (32095)Memory used [KB]: 1791
% 2.75/0.76  % (32095)Time elapsed: 0.310 s
% 2.75/0.76  % (32095)------------------------------
% 2.75/0.76  % (32095)------------------------------
% 2.75/0.77  % (32130)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 3.12/0.81  % (32105)Refutation not found, incomplete strategy% (32105)------------------------------
% 3.12/0.81  % (32105)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.12/0.81  % (32105)Termination reason: Refutation not found, incomplete strategy
% 3.12/0.81  
% 3.12/0.81  % (32105)Memory used [KB]: 12025
% 3.12/0.81  % (32105)Time elapsed: 0.387 s
% 3.12/0.81  % (32105)------------------------------
% 3.12/0.81  % (32105)------------------------------
% 3.12/0.83  % (32119)Time limit reached!
% 3.12/0.83  % (32119)------------------------------
% 3.12/0.83  % (32119)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.12/0.83  % (32119)Termination reason: Time limit
% 3.12/0.83  % (32119)Termination phase: Saturation
% 3.12/0.83  
% 3.12/0.83  % (32119)Memory used [KB]: 12537
% 3.12/0.83  % (32119)Time elapsed: 0.400 s
% 3.12/0.83  % (32119)------------------------------
% 3.12/0.83  % (32119)------------------------------
% 3.64/0.85  % (32097)Time limit reached!
% 3.64/0.85  % (32097)------------------------------
% 3.64/0.85  % (32097)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.64/0.85  % (32097)Termination reason: Time limit
% 3.64/0.85  % (32097)Termination phase: Saturation
% 3.64/0.85  
% 3.64/0.85  % (32097)Memory used [KB]: 6652
% 3.64/0.85  % (32097)Time elapsed: 0.400 s
% 3.64/0.85  % (32097)------------------------------
% 3.64/0.85  % (32097)------------------------------
% 4.14/0.93  % (32101)Time limit reached!
% 4.14/0.93  % (32101)------------------------------
% 4.14/0.93  % (32101)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.14/0.93  % (32101)Termination reason: Time limit
% 4.14/0.93  
% 4.14/0.93  % (32101)Memory used [KB]: 13944
% 4.14/0.93  % (32101)Time elapsed: 0.518 s
% 4.14/0.93  % (32101)------------------------------
% 4.14/0.93  % (32101)------------------------------
% 4.14/0.94  % (32156)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 4.14/0.94  % (32124)Time limit reached!
% 4.14/0.94  % (32124)------------------------------
% 4.14/0.94  % (32124)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.14/0.94  % (32124)Termination reason: Time limit
% 4.14/0.94  
% 4.14/0.94  % (32124)Memory used [KB]: 3837
% 4.14/0.94  % (32124)Time elapsed: 0.520 s
% 4.14/0.94  % (32124)------------------------------
% 4.14/0.94  % (32124)------------------------------
% 4.14/0.94  % (32158)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 4.14/0.94  % (32158)Refutation not found, incomplete strategy% (32158)------------------------------
% 4.14/0.94  % (32158)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.14/0.94  % (32158)Termination reason: Refutation not found, incomplete strategy
% 4.14/0.94  
% 4.14/0.94  % (32158)Memory used [KB]: 6268
% 4.14/0.94  % (32158)Time elapsed: 0.107 s
% 4.14/0.94  % (32158)------------------------------
% 4.14/0.94  % (32158)------------------------------
% 4.39/0.96  % (32109)Time limit reached!
% 4.39/0.96  % (32109)------------------------------
% 4.39/0.96  % (32109)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.39/0.96  % (32109)Termination reason: Time limit
% 4.39/0.96  % (32109)Termination phase: Saturation
% 4.39/0.96  
% 4.39/0.96  % (32109)Memory used [KB]: 4989
% 4.39/0.96  % (32109)Time elapsed: 0.500 s
% 4.39/0.96  % (32109)------------------------------
% 4.39/0.96  % (32109)------------------------------
% 4.39/0.99  % (32160)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 4.39/1.01  % (32159)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 4.82/1.05  % (32163)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 4.82/1.06  % (32162)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 4.82/1.07  % (32165)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 5.07/1.09  % (32123)Refutation not found, incomplete strategy% (32123)------------------------------
% 5.07/1.09  % (32123)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.07/1.09  % (32123)Termination reason: Refutation not found, incomplete strategy
% 5.07/1.09  
% 5.07/1.09  % (32123)Memory used [KB]: 13176
% 5.07/1.09  % (32123)Time elapsed: 0.667 s
% 5.07/1.09  % (32123)------------------------------
% 5.07/1.09  % (32123)------------------------------
% 5.07/1.10  % (32102)Time limit reached!
% 5.07/1.10  % (32102)------------------------------
% 5.07/1.10  % (32102)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.07/1.10  % (32102)Termination reason: Time limit
% 5.07/1.10  % (32102)Termination phase: Saturation
% 5.07/1.10  
% 5.07/1.10  % (32102)Memory used [KB]: 5628
% 5.07/1.10  % (32102)Time elapsed: 0.600 s
% 5.07/1.10  % (32102)------------------------------
% 5.07/1.10  % (32102)------------------------------
% 5.07/1.11  % (32166)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 6.45/1.20  % (32169)lrs+1010_3:2_afr=on:afp=100000:afq=1.1:anc=none:gsp=input_only:irw=on:lwlo=on:nm=2:newcnf=on:nwc=1.7:stl=30:sac=on:sp=occurrence_95 on theBenchmark
% 6.45/1.23  % (32168)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_4 on theBenchmark
% 6.45/1.24  % (32096)Time limit reached!
% 6.45/1.24  % (32096)------------------------------
% 6.45/1.24  % (32096)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.82/1.24  % (32117)Refutation found. Thanks to Tanya!
% 6.82/1.24  % SZS status Theorem for theBenchmark
% 6.82/1.24  % (32096)Termination reason: Time limit
% 6.82/1.24  
% 6.82/1.24  % (32096)Memory used [KB]: 5756
% 6.82/1.24  % (32096)Time elapsed: 0.815 s
% 6.82/1.24  % (32096)------------------------------
% 6.82/1.24  % (32096)------------------------------
% 6.90/1.25  % SZS output start Proof for theBenchmark
% 6.90/1.25  fof(f2859,plain,(
% 6.90/1.25    $false),
% 6.90/1.25    inference(subsumption_resolution,[],[f2858,f148])).
% 6.90/1.25  fof(f148,plain,(
% 6.90/1.25    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 6.90/1.25    inference(backward_demodulation,[],[f138,f146])).
% 6.90/1.25  fof(f146,plain,(
% 6.90/1.25    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 6.90/1.25    inference(resolution,[],[f145,f138])).
% 6.90/1.25  fof(f145,plain,(
% 6.90/1.25    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = X0) )),
% 6.90/1.25    inference(resolution,[],[f140,f93])).
% 6.90/1.25  fof(f93,plain,(
% 6.90/1.25    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 6.90/1.25    inference(cnf_transformation,[],[f58])).
% 6.90/1.25  fof(f58,plain,(
% 6.90/1.25    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 6.90/1.25    inference(nnf_transformation,[],[f4])).
% 6.90/1.25  fof(f4,axiom,(
% 6.90/1.25    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 6.90/1.25    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 6.90/1.25  fof(f140,plain,(
% 6.90/1.25    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 6.90/1.25    inference(resolution,[],[f92,f78])).
% 6.90/1.25  fof(f78,plain,(
% 6.90/1.25    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 6.90/1.25    inference(cnf_transformation,[],[f2])).
% 6.90/1.25  fof(f2,axiom,(
% 6.90/1.25    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 6.90/1.25    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 6.90/1.25  fof(f92,plain,(
% 6.90/1.25    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 6.90/1.25    inference(cnf_transformation,[],[f57])).
% 6.90/1.25  fof(f57,plain,(
% 6.90/1.25    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 6.90/1.25    inference(flattening,[],[f56])).
% 6.90/1.25  fof(f56,plain,(
% 6.90/1.25    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 6.90/1.25    inference(nnf_transformation,[],[f1])).
% 6.90/1.25  fof(f1,axiom,(
% 6.90/1.25    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 6.90/1.25    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 6.90/1.25  fof(f138,plain,(
% 6.90/1.25    m1_subset_1(k6_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))),
% 6.90/1.25    inference(superposition,[],[f126,f132])).
% 6.90/1.25  fof(f132,plain,(
% 6.90/1.25    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 6.90/1.25    inference(equality_resolution,[],[f97])).
% 6.90/1.25  fof(f97,plain,(
% 6.90/1.25    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 6.90/1.25    inference(cnf_transformation,[],[f60])).
% 6.90/1.25  fof(f60,plain,(
% 6.90/1.25    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 6.90/1.25    inference(flattening,[],[f59])).
% 6.90/1.25  fof(f59,plain,(
% 6.90/1.25    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 6.90/1.25    inference(nnf_transformation,[],[f3])).
% 6.90/1.25  fof(f3,axiom,(
% 6.90/1.25    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 6.90/1.25    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 6.90/1.25  fof(f126,plain,(
% 6.90/1.25    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 6.90/1.25    inference(definition_unfolding,[],[f81,f79])).
% 6.90/1.25  fof(f79,plain,(
% 6.90/1.25    ( ! [X0] : (k6_partfun1(X0) = k6_relat_1(X0)) )),
% 6.90/1.25    inference(cnf_transformation,[],[f16])).
% 6.90/1.25  fof(f16,axiom,(
% 6.90/1.25    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0)),
% 6.90/1.25    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 6.90/1.25  fof(f81,plain,(
% 6.90/1.25    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 6.90/1.25    inference(cnf_transformation,[],[f14])).
% 6.90/1.25  fof(f14,axiom,(
% 6.90/1.25    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 6.90/1.25    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 6.90/1.25  fof(f2858,plain,(
% 6.90/1.25    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 6.90/1.25    inference(forward_demodulation,[],[f2857,f132])).
% 6.90/1.25  fof(f2857,plain,(
% 6.90/1.25    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 6.90/1.25    inference(resolution,[],[f2391,f135])).
% 6.90/1.25  fof(f135,plain,(
% 6.90/1.25    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.90/1.25    inference(duplicate_literal_removal,[],[f134])).
% 6.90/1.25  fof(f134,plain,(
% 6.90/1.25    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.90/1.25    inference(equality_resolution,[],[f120])).
% 6.90/1.25  fof(f120,plain,(
% 6.90/1.25    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.90/1.25    inference(cnf_transformation,[],[f68])).
% 6.90/1.25  fof(f68,plain,(
% 6.90/1.25    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.90/1.25    inference(nnf_transformation,[],[f43])).
% 6.90/1.25  fof(f43,plain,(
% 6.90/1.25    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.90/1.25    inference(flattening,[],[f42])).
% 6.90/1.25  fof(f42,plain,(
% 6.90/1.25    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 6.90/1.25    inference(ennf_transformation,[],[f11])).
% 6.90/1.25  fof(f11,axiom,(
% 6.90/1.25    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 6.90/1.25    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 6.90/1.25  fof(f2391,plain,(
% 6.90/1.25    ~r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 6.90/1.25    inference(backward_demodulation,[],[f1870,f2382])).
% 6.90/1.25  fof(f2382,plain,(
% 6.90/1.25    k1_xboole_0 = sK4),
% 6.90/1.25    inference(subsumption_resolution,[],[f2381,f78])).
% 6.90/1.25  fof(f2381,plain,(
% 6.90/1.25    ~r1_tarski(k1_xboole_0,sK4) | k1_xboole_0 = sK4),
% 6.90/1.25    inference(forward_demodulation,[],[f2380,f132])).
% 6.90/1.25  fof(f2380,plain,(
% 6.90/1.25    ~r1_tarski(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),sK4) | k1_xboole_0 = sK4),
% 6.90/1.25    inference(forward_demodulation,[],[f2379,f1713])).
% 6.90/1.25  fof(f1713,plain,(
% 6.90/1.25    k1_xboole_0 = sK2),
% 6.90/1.25    inference(subsumption_resolution,[],[f1712,f287])).
% 6.90/1.25  fof(f287,plain,(
% 6.90/1.25    r2_relset_1(sK2,sK2,sK3,sK3)),
% 6.90/1.25    inference(backward_demodulation,[],[f75,f285])).
% 6.90/1.25  fof(f285,plain,(
% 6.90/1.25    sK3 = k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3)),
% 6.90/1.25    inference(subsumption_resolution,[],[f284,f72])).
% 6.90/1.25  fof(f72,plain,(
% 6.90/1.25    v1_funct_1(sK4)),
% 6.90/1.25    inference(cnf_transformation,[],[f55])).
% 6.90/1.25  fof(f55,plain,(
% 6.90/1.25    (~r2_relset_1(sK2,sK2,sK4,k6_partfun1(sK2)) & v2_funct_1(sK3) & r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3),sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v1_funct_2(sK4,sK2,sK2) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v1_funct_2(sK3,sK2,sK2) & v1_funct_1(sK3)),
% 6.90/1.25    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f25,f54,f53])).
% 6.90/1.25  fof(f53,plain,(
% 6.90/1.25    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k6_partfun1(X0)) & v2_funct_1(X1) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (? [X2] : (~r2_relset_1(sK2,sK2,X2,k6_partfun1(sK2)) & v2_funct_1(sK3) & r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,X2,sK3),sK3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v1_funct_2(X2,sK2,sK2) & v1_funct_1(X2)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v1_funct_2(sK3,sK2,sK2) & v1_funct_1(sK3))),
% 6.90/1.25    introduced(choice_axiom,[])).
% 6.90/1.25  fof(f54,plain,(
% 6.90/1.25    ? [X2] : (~r2_relset_1(sK2,sK2,X2,k6_partfun1(sK2)) & v2_funct_1(sK3) & r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,X2,sK3),sK3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v1_funct_2(X2,sK2,sK2) & v1_funct_1(X2)) => (~r2_relset_1(sK2,sK2,sK4,k6_partfun1(sK2)) & v2_funct_1(sK3) & r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3),sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v1_funct_2(sK4,sK2,sK2) & v1_funct_1(sK4))),
% 6.90/1.25    introduced(choice_axiom,[])).
% 6.90/1.25  fof(f25,plain,(
% 6.90/1.25    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k6_partfun1(X0)) & v2_funct_1(X1) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 6.90/1.25    inference(flattening,[],[f24])).
% 6.90/1.25  fof(f24,plain,(
% 6.90/1.25    ? [X0,X1] : (? [X2] : ((~r2_relset_1(X0,X0,X2,k6_partfun1(X0)) & (v2_funct_1(X1) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 6.90/1.25    inference(ennf_transformation,[],[f23])).
% 6.90/1.25  fof(f23,negated_conjecture,(
% 6.90/1.25    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => ((v2_funct_1(X1) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1)) => r2_relset_1(X0,X0,X2,k6_partfun1(X0)))))),
% 6.90/1.25    inference(negated_conjecture,[],[f22])).
% 6.90/1.25  fof(f22,conjecture,(
% 6.90/1.25    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => ((v2_funct_1(X1) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1)) => r2_relset_1(X0,X0,X2,k6_partfun1(X0)))))),
% 6.90/1.25    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_funct_2)).
% 6.90/1.25  fof(f284,plain,(
% 6.90/1.25    sK3 = k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3) | ~v1_funct_1(sK4)),
% 6.90/1.25    inference(subsumption_resolution,[],[f283,f74])).
% 6.90/1.25  fof(f74,plain,(
% 6.90/1.25    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))),
% 6.90/1.25    inference(cnf_transformation,[],[f55])).
% 6.90/1.25  fof(f283,plain,(
% 6.90/1.25    sK3 = k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_1(sK4)),
% 6.90/1.25    inference(subsumption_resolution,[],[f282,f69])).
% 6.90/1.25  fof(f69,plain,(
% 6.90/1.25    v1_funct_1(sK3)),
% 6.90/1.25    inference(cnf_transformation,[],[f55])).
% 6.90/1.25  fof(f282,plain,(
% 6.90/1.25    sK3 = k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3) | ~v1_funct_1(sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_1(sK4)),
% 6.90/1.25    inference(subsumption_resolution,[],[f279,f71])).
% 6.90/1.25  fof(f71,plain,(
% 6.90/1.25    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))),
% 6.90/1.25    inference(cnf_transformation,[],[f55])).
% 6.90/1.25  fof(f279,plain,(
% 6.90/1.25    sK3 = k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_1(sK4)),
% 6.90/1.25    inference(resolution,[],[f210,f123])).
% 6.90/1.25  fof(f123,plain,(
% 6.90/1.25    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 6.90/1.25    inference(cnf_transformation,[],[f47])).
% 6.90/1.25  fof(f47,plain,(
% 6.90/1.25    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 6.90/1.25    inference(flattening,[],[f46])).
% 6.90/1.25  fof(f46,plain,(
% 6.90/1.25    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 6.90/1.25    inference(ennf_transformation,[],[f13])).
% 6.90/1.25  fof(f13,axiom,(
% 6.90/1.25    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 6.90/1.25    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 6.90/1.25  fof(f210,plain,(
% 6.90/1.25    ~m1_subset_1(k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | sK3 = k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3)),
% 6.90/1.25    inference(subsumption_resolution,[],[f203,f71])).
% 6.90/1.25  fof(f203,plain,(
% 6.90/1.25    sK3 = k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~m1_subset_1(k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))),
% 6.90/1.25    inference(resolution,[],[f119,f75])).
% 6.90/1.25  fof(f119,plain,(
% 6.90/1.25    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.90/1.25    inference(cnf_transformation,[],[f68])).
% 6.90/1.25  fof(f75,plain,(
% 6.90/1.25    r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3),sK3)),
% 6.90/1.25    inference(cnf_transformation,[],[f55])).
% 6.90/1.25  fof(f1712,plain,(
% 6.90/1.25    ~r2_relset_1(sK2,sK2,sK3,sK3) | k1_xboole_0 = sK2),
% 6.90/1.25    inference(forward_demodulation,[],[f1711,f304])).
% 6.90/1.25  fof(f304,plain,(
% 6.90/1.25    sK3 = k5_relat_1(sK4,sK3)),
% 6.90/1.25    inference(subsumption_resolution,[],[f303,f72])).
% 6.90/1.25  fof(f303,plain,(
% 6.90/1.25    sK3 = k5_relat_1(sK4,sK3) | ~v1_funct_1(sK4)),
% 6.90/1.25    inference(subsumption_resolution,[],[f302,f74])).
% 6.90/1.25  fof(f302,plain,(
% 6.90/1.25    sK3 = k5_relat_1(sK4,sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_1(sK4)),
% 6.90/1.25    inference(subsumption_resolution,[],[f301,f69])).
% 6.90/1.25  fof(f301,plain,(
% 6.90/1.25    sK3 = k5_relat_1(sK4,sK3) | ~v1_funct_1(sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_1(sK4)),
% 6.90/1.25    inference(subsumption_resolution,[],[f295,f71])).
% 6.90/1.25  fof(f295,plain,(
% 6.90/1.25    sK3 = k5_relat_1(sK4,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_1(sK4)),
% 6.90/1.25    inference(superposition,[],[f285,f121])).
% 6.90/1.25  fof(f121,plain,(
% 6.90/1.25    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 6.90/1.25    inference(cnf_transformation,[],[f45])).
% 6.90/1.25  fof(f45,plain,(
% 6.90/1.25    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 6.90/1.25    inference(flattening,[],[f44])).
% 6.90/1.25  fof(f44,plain,(
% 6.90/1.25    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 6.90/1.25    inference(ennf_transformation,[],[f15])).
% 6.90/1.25  fof(f15,axiom,(
% 6.90/1.25    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 6.90/1.25    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 6.90/1.25  fof(f1711,plain,(
% 6.90/1.25    k1_xboole_0 = sK2 | ~r2_relset_1(sK2,sK2,k5_relat_1(sK4,sK3),sK3)),
% 6.90/1.25    inference(subsumption_resolution,[],[f1710,f72])).
% 6.90/1.25  fof(f1710,plain,(
% 6.90/1.25    k1_xboole_0 = sK2 | ~v1_funct_1(sK4) | ~r2_relset_1(sK2,sK2,k5_relat_1(sK4,sK3),sK3)),
% 6.90/1.25    inference(subsumption_resolution,[],[f1709,f73])).
% 6.90/1.25  fof(f73,plain,(
% 6.90/1.25    v1_funct_2(sK4,sK2,sK2)),
% 6.90/1.25    inference(cnf_transformation,[],[f55])).
% 6.90/1.25  fof(f1709,plain,(
% 6.90/1.25    k1_xboole_0 = sK2 | ~v1_funct_2(sK4,sK2,sK2) | ~v1_funct_1(sK4) | ~r2_relset_1(sK2,sK2,k5_relat_1(sK4,sK3),sK3)),
% 6.90/1.25    inference(subsumption_resolution,[],[f1708,f74])).
% 6.90/1.25  fof(f1708,plain,(
% 6.90/1.25    k1_xboole_0 = sK2 | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_2(sK4,sK2,sK2) | ~v1_funct_1(sK4) | ~r2_relset_1(sK2,sK2,k5_relat_1(sK4,sK3),sK3)),
% 6.90/1.25    inference(duplicate_literal_removal,[],[f1703])).
% 6.90/1.25  fof(f1703,plain,(
% 6.90/1.25    k1_xboole_0 = sK2 | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_2(sK4,sK2,sK2) | ~v1_funct_1(sK4) | k1_xboole_0 = sK2 | ~r2_relset_1(sK2,sK2,k5_relat_1(sK4,sK3),sK3)),
% 6.90/1.25    inference(resolution,[],[f1638,f1125])).
% 6.90/1.25  fof(f1125,plain,(
% 6.90/1.25    ( ! [X3] : (r2_relset_1(sK2,sK2,X3,sK4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_2(X3,sK2,sK2) | ~v1_funct_1(X3) | k1_xboole_0 = sK2 | ~r2_relset_1(sK2,sK2,k5_relat_1(X3,sK3),sK3)) )),
% 6.90/1.25    inference(subsumption_resolution,[],[f1124,f74])).
% 6.90/1.25  fof(f1124,plain,(
% 6.90/1.25    ( ! [X3] : (~r2_relset_1(sK2,sK2,k5_relat_1(X3,sK3),sK3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_2(X3,sK2,sK2) | ~v1_funct_1(X3) | k1_xboole_0 = sK2 | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | r2_relset_1(sK2,sK2,X3,sK4)) )),
% 6.90/1.25    inference(subsumption_resolution,[],[f1123,f73])).
% 6.90/1.25  fof(f1123,plain,(
% 6.90/1.25    ( ! [X3] : (~r2_relset_1(sK2,sK2,k5_relat_1(X3,sK3),sK3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_2(X3,sK2,sK2) | ~v1_funct_1(X3) | ~v1_funct_2(sK4,sK2,sK2) | k1_xboole_0 = sK2 | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | r2_relset_1(sK2,sK2,X3,sK4)) )),
% 6.90/1.25    inference(subsumption_resolution,[],[f1118,f72])).
% 6.90/1.25  fof(f1118,plain,(
% 6.90/1.25    ( ! [X3] : (~r2_relset_1(sK2,sK2,k5_relat_1(X3,sK3),sK3) | ~v1_funct_1(sK4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_2(X3,sK2,sK2) | ~v1_funct_1(X3) | ~v1_funct_2(sK4,sK2,sK2) | k1_xboole_0 = sK2 | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | r2_relset_1(sK2,sK2,X3,sK4)) )),
% 6.90/1.25    inference(superposition,[],[f856,f285])).
% 6.90/1.25  fof(f856,plain,(
% 6.90/1.25    ( ! [X10,X11,X9] : (~r2_relset_1(X10,sK2,k5_relat_1(X11,sK3),k1_partfun1(X10,sK2,sK2,sK2,X9,sK3)) | ~v1_funct_1(X9) | ~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X10,sK2))) | ~v1_funct_2(X11,X10,sK2) | ~v1_funct_1(X11) | ~v1_funct_2(X9,X10,sK2) | k1_xboole_0 = sK2 | ~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X10,sK2))) | r2_relset_1(X10,sK2,X11,X9)) )),
% 6.90/1.25    inference(subsumption_resolution,[],[f843,f71])).
% 6.90/1.25  fof(f843,plain,(
% 6.90/1.25    ( ! [X10,X11,X9] : (~v1_funct_2(X9,X10,sK2) | ~v1_funct_1(X9) | ~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X10,sK2))) | ~v1_funct_2(X11,X10,sK2) | ~v1_funct_1(X11) | ~r2_relset_1(X10,sK2,k5_relat_1(X11,sK3),k1_partfun1(X10,sK2,sK2,sK2,X9,sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | k1_xboole_0 = sK2 | ~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X10,sK2))) | r2_relset_1(X10,sK2,X11,X9)) )),
% 6.90/1.25    inference(duplicate_literal_removal,[],[f841])).
% 6.90/1.25  fof(f841,plain,(
% 6.90/1.25    ( ! [X10,X11,X9] : (~v1_funct_2(X9,X10,sK2) | ~v1_funct_1(X9) | ~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X10,sK2))) | ~v1_funct_2(X11,X10,sK2) | ~v1_funct_1(X11) | ~r2_relset_1(X10,sK2,k5_relat_1(X11,sK3),k1_partfun1(X10,sK2,sK2,sK2,X9,sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | k1_xboole_0 = sK2 | ~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X10,sK2))) | r2_relset_1(X10,sK2,X11,X9) | k1_xboole_0 = sK2) )),
% 6.90/1.25    inference(resolution,[],[f642,f70])).
% 6.90/1.25  fof(f70,plain,(
% 6.90/1.25    v1_funct_2(sK3,sK2,sK2)),
% 6.90/1.25    inference(cnf_transformation,[],[f55])).
% 6.90/1.25  fof(f642,plain,(
% 6.90/1.25    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_2(sK3,X2,X4) | ~v1_funct_2(X0,X1,X2) | ~v1_funct_1(X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3) | ~r2_relset_1(X1,X4,k5_relat_1(X3,sK3),k1_partfun1(X1,X2,X2,X4,X0,sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X4))) | k1_xboole_0 = X2 | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | r2_relset_1(X1,X2,X3,X0) | k1_xboole_0 = X4) )),
% 6.90/1.25    inference(subsumption_resolution,[],[f640,f69])).
% 6.90/1.25  fof(f640,plain,(
% 6.90/1.25    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X0,X1,X2) | ~v1_funct_1(X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3) | ~r2_relset_1(X1,X4,k5_relat_1(X3,sK3),k1_partfun1(X1,X2,X2,X4,X0,sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X4))) | ~v1_funct_1(sK3) | k1_xboole_0 = X2 | ~v1_funct_2(sK3,X2,X4) | r2_relset_1(X1,X2,X3,X0) | k1_xboole_0 = X4) )),
% 6.90/1.25    inference(resolution,[],[f417,f76])).
% 6.90/1.25  fof(f76,plain,(
% 6.90/1.25    v2_funct_1(sK3)),
% 6.90/1.25    inference(cnf_transformation,[],[f55])).
% 6.90/1.25  fof(f417,plain,(
% 6.90/1.25    ( ! [X4,X2,X0,X5,X3,X1] : (~v2_funct_1(X5) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~r2_relset_1(X0,X4,k5_relat_1(X2,X5),k1_partfun1(X0,X1,X1,X4,X3,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X4))) | ~v1_funct_1(X5) | k1_xboole_0 = X1 | ~v1_funct_2(X5,X1,X4) | r2_relset_1(X0,X1,X2,X3) | k1_xboole_0 = X4) )),
% 6.90/1.25    inference(duplicate_literal_removal,[],[f413])).
% 6.90/1.25  fof(f413,plain,(
% 6.90/1.25    ( ! [X4,X2,X0,X5,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~r2_relset_1(X0,X4,k5_relat_1(X2,X5),k1_partfun1(X0,X1,X1,X4,X3,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X4))) | ~v1_funct_1(X5) | k1_xboole_0 = X1 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X4))) | ~v1_funct_2(X5,X1,X4) | ~v1_funct_1(X5) | ~v2_funct_1(X5) | k1_xboole_0 = X4) )),
% 6.90/1.25    inference(resolution,[],[f275,f217])).
% 6.90/1.25  fof(f217,plain,(
% 6.90/1.25    ( ! [X2,X0,X1] : (sP0(X1,X2,X0) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X2,X1,X0) | ~v1_funct_1(X2) | ~v2_funct_1(X2) | k1_xboole_0 = X0) )),
% 6.90/1.25    inference(resolution,[],[f118,f107])).
% 6.90/1.25  fof(f107,plain,(
% 6.90/1.25    ( ! [X2,X0,X1] : (~sP1(X0,X1,X2) | ~v2_funct_1(X1) | sP0(X2,X1,X0)) )),
% 6.90/1.25    inference(cnf_transformation,[],[f62])).
% 6.90/1.25  fof(f62,plain,(
% 6.90/1.25    ! [X0,X1,X2] : (((v2_funct_1(X1) | ~sP0(X2,X1,X0)) & (sP0(X2,X1,X0) | ~v2_funct_1(X1))) | ~sP1(X0,X1,X2))),
% 6.90/1.25    inference(rectify,[],[f61])).
% 6.90/1.25  fof(f61,plain,(
% 6.90/1.25    ! [X1,X2,X0] : (((v2_funct_1(X2) | ~sP0(X0,X2,X1)) & (sP0(X0,X2,X1) | ~v2_funct_1(X2))) | ~sP1(X1,X2,X0))),
% 6.90/1.25    inference(nnf_transformation,[],[f51])).
% 6.90/1.25  fof(f51,plain,(
% 6.90/1.25    ! [X1,X2,X0] : ((v2_funct_1(X2) <=> sP0(X0,X2,X1)) | ~sP1(X1,X2,X0))),
% 6.90/1.25    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 6.90/1.25  fof(f118,plain,(
% 6.90/1.25    ( ! [X2,X0,X1] : (sP1(X1,X2,X0) | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 6.90/1.25    inference(cnf_transformation,[],[f52])).
% 6.90/1.25  fof(f52,plain,(
% 6.90/1.25    ! [X0,X1,X2] : (sP1(X1,X2,X0) | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 6.90/1.25    inference(definition_folding,[],[f41,f51,f50])).
% 6.90/1.25  fof(f50,plain,(
% 6.90/1.25    ! [X0,X2,X1] : (sP0(X0,X2,X1) <=> ! [X3,X4] : (! [X5] : (r2_relset_1(X3,X0,X4,X5) | ~r2_relset_1(X3,X1,k1_partfun1(X3,X0,X0,X1,X4,X2),k1_partfun1(X3,X0,X0,X1,X5,X2)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) | ~v1_funct_2(X5,X3,X0) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) | ~v1_funct_2(X4,X3,X0) | ~v1_funct_1(X4)))),
% 6.90/1.25    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 6.90/1.25  fof(f41,plain,(
% 6.90/1.25    ! [X0,X1,X2] : ((v2_funct_1(X2) <=> ! [X3,X4] : (! [X5] : (r2_relset_1(X3,X0,X4,X5) | ~r2_relset_1(X3,X1,k1_partfun1(X3,X0,X0,X1,X4,X2),k1_partfun1(X3,X0,X0,X1,X5,X2)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) | ~v1_funct_2(X5,X3,X0) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) | ~v1_funct_2(X4,X3,X0) | ~v1_funct_1(X4))) | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 6.90/1.25    inference(flattening,[],[f40])).
% 6.90/1.25  fof(f40,plain,(
% 6.90/1.25    ! [X0,X1,X2] : (((v2_funct_1(X2) <=> ! [X3,X4] : (! [X5] : ((r2_relset_1(X3,X0,X4,X5) | ~r2_relset_1(X3,X1,k1_partfun1(X3,X0,X0,X1,X4,X2),k1_partfun1(X3,X0,X0,X1,X5,X2))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) | ~v1_funct_2(X5,X3,X0) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) | ~v1_funct_2(X4,X3,X0) | ~v1_funct_1(X4)))) | k1_xboole_0 = X1 | k1_xboole_0 = X0) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 6.90/1.25    inference(ennf_transformation,[],[f18])).
% 6.90/1.25  fof(f18,axiom,(
% 6.90/1.25    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ~(~(v2_funct_1(X2) <=> ! [X3,X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) & v1_funct_2(X4,X3,X0) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) & v1_funct_2(X5,X3,X0) & v1_funct_1(X5)) => (r2_relset_1(X3,X1,k1_partfun1(X3,X0,X0,X1,X4,X2),k1_partfun1(X3,X0,X0,X1,X5,X2)) => r2_relset_1(X3,X0,X4,X5))))) & k1_xboole_0 != X1 & k1_xboole_0 != X0))),
% 6.90/1.25    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_funct_2)).
% 6.90/1.25  fof(f275,plain,(
% 6.90/1.25    ( ! [X4,X2,X0,X5,X3,X1] : (~sP0(X1,X4,X2) | r2_relset_1(X0,X1,X3,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X5,X0,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~r2_relset_1(X0,X2,k5_relat_1(X3,X4),k1_partfun1(X0,X1,X1,X2,X5,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4)) )),
% 6.90/1.25    inference(duplicate_literal_removal,[],[f272])).
% 6.90/1.25  fof(f272,plain,(
% 6.90/1.25    ( ! [X4,X2,X0,X5,X3,X1] : (~r2_relset_1(X0,X2,k5_relat_1(X3,X4),k1_partfun1(X0,X1,X1,X2,X5,X4)) | r2_relset_1(X0,X1,X3,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X5,X0,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~sP0(X1,X4,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3)) )),
% 6.90/1.25    inference(superposition,[],[f109,f121])).
% 6.90/1.25  fof(f109,plain,(
% 6.90/1.25    ( ! [X6,X2,X0,X8,X7,X1] : (~r2_relset_1(X6,X2,k1_partfun1(X6,X0,X0,X2,X7,X1),k1_partfun1(X6,X0,X0,X2,X8,X1)) | r2_relset_1(X6,X0,X7,X8) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X0))) | ~v1_funct_2(X8,X6,X0) | ~v1_funct_1(X8) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X6,X0))) | ~v1_funct_2(X7,X6,X0) | ~v1_funct_1(X7) | ~sP0(X0,X1,X2)) )),
% 6.90/1.25    inference(cnf_transformation,[],[f67])).
% 6.90/1.25  fof(f67,plain,(
% 6.90/1.25    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((~r2_relset_1(sK5(X0,X1,X2),X0,sK6(X0,X1,X2),sK7(X0,X1,X2)) & r2_relset_1(sK5(X0,X1,X2),X2,k1_partfun1(sK5(X0,X1,X2),X0,X0,X2,sK6(X0,X1,X2),X1),k1_partfun1(sK5(X0,X1,X2),X0,X0,X2,sK7(X0,X1,X2),X1)) & m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(sK5(X0,X1,X2),X0))) & v1_funct_2(sK7(X0,X1,X2),sK5(X0,X1,X2),X0) & v1_funct_1(sK7(X0,X1,X2))) & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(sK5(X0,X1,X2),X0))) & v1_funct_2(sK6(X0,X1,X2),sK5(X0,X1,X2),X0) & v1_funct_1(sK6(X0,X1,X2)))) & (! [X6,X7] : (! [X8] : (r2_relset_1(X6,X0,X7,X8) | ~r2_relset_1(X6,X2,k1_partfun1(X6,X0,X0,X2,X7,X1),k1_partfun1(X6,X0,X0,X2,X8,X1)) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X0))) | ~v1_funct_2(X8,X6,X0) | ~v1_funct_1(X8)) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X6,X0))) | ~v1_funct_2(X7,X6,X0) | ~v1_funct_1(X7)) | ~sP0(X0,X1,X2)))),
% 6.90/1.25    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f64,f66,f65])).
% 6.90/1.25  fof(f65,plain,(
% 6.90/1.25    ! [X2,X1,X0] : (? [X3,X4] : (? [X5] : (~r2_relset_1(X3,X0,X4,X5) & r2_relset_1(X3,X2,k1_partfun1(X3,X0,X0,X2,X4,X1),k1_partfun1(X3,X0,X0,X2,X5,X1)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) & v1_funct_2(X5,X3,X0) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) & v1_funct_2(X4,X3,X0) & v1_funct_1(X4)) => (? [X5] : (~r2_relset_1(sK5(X0,X1,X2),X0,sK6(X0,X1,X2),X5) & r2_relset_1(sK5(X0,X1,X2),X2,k1_partfun1(sK5(X0,X1,X2),X0,X0,X2,sK6(X0,X1,X2),X1),k1_partfun1(sK5(X0,X1,X2),X0,X0,X2,X5,X1)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK5(X0,X1,X2),X0))) & v1_funct_2(X5,sK5(X0,X1,X2),X0) & v1_funct_1(X5)) & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(sK5(X0,X1,X2),X0))) & v1_funct_2(sK6(X0,X1,X2),sK5(X0,X1,X2),X0) & v1_funct_1(sK6(X0,X1,X2))))),
% 6.90/1.25    introduced(choice_axiom,[])).
% 6.90/1.25  fof(f66,plain,(
% 6.90/1.25    ! [X2,X1,X0] : (? [X5] : (~r2_relset_1(sK5(X0,X1,X2),X0,sK6(X0,X1,X2),X5) & r2_relset_1(sK5(X0,X1,X2),X2,k1_partfun1(sK5(X0,X1,X2),X0,X0,X2,sK6(X0,X1,X2),X1),k1_partfun1(sK5(X0,X1,X2),X0,X0,X2,X5,X1)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK5(X0,X1,X2),X0))) & v1_funct_2(X5,sK5(X0,X1,X2),X0) & v1_funct_1(X5)) => (~r2_relset_1(sK5(X0,X1,X2),X0,sK6(X0,X1,X2),sK7(X0,X1,X2)) & r2_relset_1(sK5(X0,X1,X2),X2,k1_partfun1(sK5(X0,X1,X2),X0,X0,X2,sK6(X0,X1,X2),X1),k1_partfun1(sK5(X0,X1,X2),X0,X0,X2,sK7(X0,X1,X2),X1)) & m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(sK5(X0,X1,X2),X0))) & v1_funct_2(sK7(X0,X1,X2),sK5(X0,X1,X2),X0) & v1_funct_1(sK7(X0,X1,X2))))),
% 6.90/1.25    introduced(choice_axiom,[])).
% 6.90/1.25  fof(f64,plain,(
% 6.90/1.25    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3,X4] : (? [X5] : (~r2_relset_1(X3,X0,X4,X5) & r2_relset_1(X3,X2,k1_partfun1(X3,X0,X0,X2,X4,X1),k1_partfun1(X3,X0,X0,X2,X5,X1)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) & v1_funct_2(X5,X3,X0) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) & v1_funct_2(X4,X3,X0) & v1_funct_1(X4))) & (! [X6,X7] : (! [X8] : (r2_relset_1(X6,X0,X7,X8) | ~r2_relset_1(X6,X2,k1_partfun1(X6,X0,X0,X2,X7,X1),k1_partfun1(X6,X0,X0,X2,X8,X1)) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X0))) | ~v1_funct_2(X8,X6,X0) | ~v1_funct_1(X8)) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X6,X0))) | ~v1_funct_2(X7,X6,X0) | ~v1_funct_1(X7)) | ~sP0(X0,X1,X2)))),
% 6.90/1.25    inference(rectify,[],[f63])).
% 6.90/1.25  fof(f63,plain,(
% 6.90/1.25    ! [X0,X2,X1] : ((sP0(X0,X2,X1) | ? [X3,X4] : (? [X5] : (~r2_relset_1(X3,X0,X4,X5) & r2_relset_1(X3,X1,k1_partfun1(X3,X0,X0,X1,X4,X2),k1_partfun1(X3,X0,X0,X1,X5,X2)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) & v1_funct_2(X5,X3,X0) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) & v1_funct_2(X4,X3,X0) & v1_funct_1(X4))) & (! [X3,X4] : (! [X5] : (r2_relset_1(X3,X0,X4,X5) | ~r2_relset_1(X3,X1,k1_partfun1(X3,X0,X0,X1,X4,X2),k1_partfun1(X3,X0,X0,X1,X5,X2)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) | ~v1_funct_2(X5,X3,X0) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) | ~v1_funct_2(X4,X3,X0) | ~v1_funct_1(X4)) | ~sP0(X0,X2,X1)))),
% 6.90/1.25    inference(nnf_transformation,[],[f50])).
% 6.90/1.25  fof(f1638,plain,(
% 6.90/1.25    ~r2_relset_1(sK2,sK2,sK4,sK4) | k1_xboole_0 = sK2),
% 6.90/1.25    inference(superposition,[],[f125,f1629])).
% 6.90/1.25  fof(f1629,plain,(
% 6.90/1.25    sK4 = k6_relat_1(sK2) | k1_xboole_0 = sK2),
% 6.90/1.25    inference(subsumption_resolution,[],[f1628,f126])).
% 6.90/1.25  fof(f1628,plain,(
% 6.90/1.25    k1_xboole_0 = sK2 | sK4 = k6_relat_1(sK2) | ~m1_subset_1(k6_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))),
% 6.90/1.25    inference(subsumption_resolution,[],[f1627,f1595])).
% 6.90/1.25  fof(f1595,plain,(
% 6.90/1.25    v1_funct_1(k6_relat_1(sK2))),
% 6.90/1.25    inference(resolution,[],[f1587,f71])).
% 6.90/1.25  fof(f1587,plain,(
% 6.90/1.25    ( ! [X10,X9] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X9,X10))) | v1_funct_1(k6_relat_1(sK2))) )),
% 6.90/1.25    inference(resolution,[],[f1579,f71])).
% 6.90/1.25  fof(f1579,plain,(
% 6.90/1.25    ( ! [X14,X15,X13,X16] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X13,X14))) | v1_funct_1(k6_relat_1(sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X15,X16)))) )),
% 6.90/1.25    inference(resolution,[],[f1571,f71])).
% 6.90/1.25  fof(f1571,plain,(
% 6.90/1.25    ( ! [X21,X19,X17,X22,X20,X18] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X21,X22))) | v1_funct_1(k6_relat_1(sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X19,X20))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X17,X18)))) )),
% 6.90/1.25    inference(resolution,[],[f1562,f71])).
% 6.90/1.25  fof(f1562,plain,(
% 6.90/1.25    ( ! [X28,X26,X24,X23,X21,X27,X25,X22] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X27,X28))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X23,X24))) | v1_funct_1(k6_relat_1(sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X25,X26))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X21,X22)))) )),
% 6.90/1.25    inference(resolution,[],[f1552,f71])).
% 6.90/1.25  fof(f1552,plain,(
% 6.90/1.25    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X8,X9))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | v1_funct_1(k6_relat_1(sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.90/1.25    inference(resolution,[],[f1540,f85])).
% 6.90/1.25  fof(f85,plain,(
% 6.90/1.25    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 6.90/1.25    inference(cnf_transformation,[],[f6])).
% 6.90/1.25  fof(f6,axiom,(
% 6.90/1.25    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 6.90/1.25    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 6.90/1.25  fof(f1540,plain,(
% 6.90/1.25    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (~v1_relat_1(X4) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(sK3,k1_zfmisc_1(X4)) | v1_funct_1(k6_relat_1(sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))) )),
% 6.90/1.25    inference(resolution,[],[f1533,f85])).
% 6.90/1.25  fof(f1533,plain,(
% 6.90/1.25    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (~v1_relat_1(X7) | v1_funct_1(k6_relat_1(sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | ~m1_subset_1(sK3,k1_zfmisc_1(X6)) | ~v1_relat_1(X6) | ~m1_subset_1(sK3,k1_zfmisc_1(X7)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.90/1.25    inference(subsumption_resolution,[],[f1530,f130])).
% 6.90/1.25  fof(f130,plain,(
% 6.90/1.25    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 6.90/1.25    inference(equality_resolution,[],[f91])).
% 6.90/1.25  fof(f91,plain,(
% 6.90/1.25    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 6.90/1.25    inference(cnf_transformation,[],[f57])).
% 6.90/1.25  fof(f1530,plain,(
% 6.90/1.25    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_funct_1(k6_relat_1(sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | ~m1_subset_1(sK3,k1_zfmisc_1(X6)) | ~v1_relat_1(X6) | ~r1_tarski(k2_relat_1(sK3),k2_relat_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(X7)) | ~v1_relat_1(X7)) )),
% 6.90/1.25    inference(resolution,[],[f1522,f211])).
% 6.90/1.25  fof(f211,plain,(
% 6.90/1.25    ( ! [X0,X1] : (m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~r1_tarski(k2_relat_1(sK3),X0) | ~m1_subset_1(sK3,k1_zfmisc_1(X1)) | ~v1_relat_1(X1)) )),
% 6.90/1.25    inference(resolution,[],[f199,f82])).
% 6.90/1.25  fof(f82,plain,(
% 6.90/1.25    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 6.90/1.25    inference(cnf_transformation,[],[f26])).
% 6.90/1.25  fof(f26,plain,(
% 6.90/1.25    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 6.90/1.25    inference(ennf_transformation,[],[f5])).
% 6.90/1.25  fof(f5,axiom,(
% 6.90/1.25    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 6.90/1.25    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 6.90/1.25  fof(f199,plain,(
% 6.90/1.25    ( ! [X0] : (~v1_relat_1(sK3) | ~r1_tarski(k2_relat_1(sK3),X0) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))) )),
% 6.90/1.25    inference(subsumption_resolution,[],[f197,f69])).
% 6.90/1.25  fof(f197,plain,(
% 6.90/1.25    ( ! [X0] : (m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~r1_tarski(k2_relat_1(sK3),X0) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)) )),
% 6.90/1.25    inference(superposition,[],[f88,f192])).
% 6.90/1.25  fof(f192,plain,(
% 6.90/1.25    sK2 = k1_relat_1(sK3)),
% 6.90/1.25    inference(subsumption_resolution,[],[f189,f71])).
% 6.90/1.25  fof(f189,plain,(
% 6.90/1.25    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | sK2 = k1_relat_1(sK3)),
% 6.90/1.25    inference(resolution,[],[f183,f70])).
% 6.90/1.25  fof(f183,plain,(
% 6.90/1.25    ( ! [X0] : (~v1_funct_2(sK3,X0,X0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | k1_relat_1(sK3) = X0) )),
% 6.90/1.25    inference(resolution,[],[f182,f69])).
% 6.90/1.25  fof(f182,plain,(
% 6.90/1.25    ( ! [X0,X1] : (~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | k1_relat_1(X1) = X0) )),
% 6.90/1.25    inference(duplicate_literal_removal,[],[f179])).
% 6.90/1.25  fof(f179,plain,(
% 6.90/1.25    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 6.90/1.25    inference(superposition,[],[f89,f99])).
% 6.90/1.25  fof(f99,plain,(
% 6.90/1.25    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.90/1.25    inference(cnf_transformation,[],[f34])).
% 6.90/1.25  fof(f34,plain,(
% 6.90/1.25    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.90/1.25    inference(ennf_transformation,[],[f8])).
% 6.90/1.25  fof(f8,axiom,(
% 6.90/1.25    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 6.90/1.25    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 6.90/1.25  fof(f89,plain,(
% 6.90/1.25    ( ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 6.90/1.25    inference(cnf_transformation,[],[f32])).
% 6.90/1.25  fof(f32,plain,(
% 6.90/1.25    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 6.90/1.25    inference(flattening,[],[f31])).
% 6.90/1.25  fof(f31,plain,(
% 6.90/1.25    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 6.90/1.25    inference(ennf_transformation,[],[f21])).
% 6.90/1.25  fof(f21,axiom,(
% 6.90/1.25    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k1_relset_1(X0,X0,X1) = X0)),
% 6.90/1.25    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_2)).
% 6.90/1.25  fof(f88,plain,(
% 6.90/1.25    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 6.90/1.25    inference(cnf_transformation,[],[f30])).
% 6.90/1.25  fof(f30,plain,(
% 6.90/1.25    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 6.90/1.25    inference(flattening,[],[f29])).
% 6.90/1.25  fof(f29,plain,(
% 6.90/1.25    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 6.90/1.25    inference(ennf_transformation,[],[f20])).
% 6.90/1.25  fof(f20,axiom,(
% 6.90/1.25    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 6.90/1.25    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).
% 6.90/1.25  fof(f1522,plain,(
% 6.90/1.25    ( ! [X6,X4,X2,X0,X5,X3,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_relat_1(sK3)))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | v1_funct_1(k6_relat_1(sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(sK3,k1_zfmisc_1(X6)) | ~v1_relat_1(X6)) )),
% 6.90/1.25    inference(resolution,[],[f1514,f82])).
% 6.90/1.25  fof(f1514,plain,(
% 6.90/1.25    ( ! [X12,X10,X8,X7,X11,X9] : (~v1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X7,X8))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X9,X10))) | v1_funct_1(k6_relat_1(sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X11,X12))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_relat_1(sK3))))) )),
% 6.90/1.25    inference(forward_demodulation,[],[f1513,f192])).
% 6.90/1.25  fof(f1513,plain,(
% 6.90/1.25    ( ! [X12,X10,X8,X7,X11,X9] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X7,X8))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X9,X10))) | v1_funct_1(k6_relat_1(sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X11,X12))) | ~v1_relat_1(sK3)) )),
% 6.90/1.25    inference(subsumption_resolution,[],[f1512,f69])).
% 6.90/1.25  fof(f1512,plain,(
% 6.90/1.25    ( ! [X12,X10,X8,X7,X11,X9] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X7,X8))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X9,X10))) | v1_funct_1(k6_relat_1(sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X11,X12))) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)) )),
% 6.90/1.25    inference(subsumption_resolution,[],[f1508,f130])).
% 6.90/1.25  fof(f1508,plain,(
% 6.90/1.25    ( ! [X12,X10,X8,X7,X11,X9] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X7,X8))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X9,X10))) | v1_funct_1(k6_relat_1(sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X11,X12))) | ~r1_tarski(k2_relat_1(sK3),k2_relat_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)) )),
% 6.90/1.25    inference(resolution,[],[f1504,f87])).
% 6.90/1.25  fof(f87,plain,(
% 6.90/1.25    ( ! [X0,X1] : (v1_funct_2(X1,k1_relat_1(X1),X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 6.90/1.25    inference(cnf_transformation,[],[f30])).
% 6.90/1.25  fof(f1504,plain,(
% 6.90/1.25    ( ! [X6,X4,X2,X0,X5,X3,X1] : (~v1_funct_2(sK3,X6,k2_relat_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | v1_funct_1(k6_relat_1(sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X6,k2_relat_1(sK3)))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.90/1.25    inference(equality_resolution,[],[f1484])).
% 6.90/1.25  fof(f1484,plain,(
% 6.90/1.25    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_relat_1(sK3) != X6 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | v1_funct_1(k6_relat_1(sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X7,X6))) | ~v1_funct_2(sK3,X7,X6)) )),
% 6.90/1.25    inference(resolution,[],[f1475,f322])).
% 6.90/1.25  fof(f322,plain,(
% 6.90/1.25    ( ! [X0,X1] : (m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relat_1(sK3) != X1 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK3,X0,X1)) )),
% 6.90/1.25    inference(duplicate_literal_removal,[],[f321])).
% 6.90/1.25  fof(f321,plain,(
% 6.90/1.25    ( ! [X0,X1] : (k2_relat_1(sK3) != X1 | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK3,X0,X1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.90/1.25    inference(superposition,[],[f248,f98])).
% 6.90/1.25  fof(f98,plain,(
% 6.90/1.25    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.90/1.25    inference(cnf_transformation,[],[f33])).
% 6.90/1.25  fof(f33,plain,(
% 6.90/1.25    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.90/1.25    inference(ennf_transformation,[],[f9])).
% 6.90/1.25  fof(f9,axiom,(
% 6.90/1.25    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 6.90/1.25    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 6.90/1.25  fof(f248,plain,(
% 6.90/1.25    ( ! [X0,X1] : (k2_relset_1(X0,X1,sK3) != X1 | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK3,X0,X1)) )),
% 6.90/1.25    inference(subsumption_resolution,[],[f246,f69])).
% 6.90/1.25  fof(f246,plain,(
% 6.90/1.25    ( ! [X0,X1] : (k2_relset_1(X0,X1,sK3) != X1 | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK3,X0,X1) | ~v1_funct_1(sK3)) )),
% 6.90/1.25    inference(resolution,[],[f106,f76])).
% 6.90/1.25  fof(f106,plain,(
% 6.90/1.25    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 6.90/1.25    inference(cnf_transformation,[],[f39])).
% 6.90/1.25  fof(f39,plain,(
% 6.90/1.25    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 6.90/1.25    inference(flattening,[],[f38])).
% 6.90/1.25  fof(f38,plain,(
% 6.90/1.25    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 6.90/1.25    inference(ennf_transformation,[],[f19])).
% 6.90/1.25  fof(f19,axiom,(
% 6.90/1.25    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 6.90/1.25    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).
% 6.90/1.25  fof(f1475,plain,(
% 6.90/1.25    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | v1_funct_1(k6_relat_1(sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))) )),
% 6.90/1.25    inference(resolution,[],[f1458,f130])).
% 6.90/1.25  fof(f1458,plain,(
% 6.90/1.25    ( ! [X14,X12,X10,X17,X15,X13,X11,X9,X18,X16] : (~r1_tarski(k2_zfmisc_1(sK2,sK2),k2_zfmisc_1(X17,X18)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X11,X12))) | v1_funct_1(k6_relat_1(sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X13,X14))) | ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X15,X16))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))) )),
% 6.90/1.25    inference(resolution,[],[f1452,f94])).
% 6.90/1.26  fof(f94,plain,(
% 6.90/1.26    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 6.90/1.26    inference(cnf_transformation,[],[f58])).
% 6.90/1.26  fof(f1452,plain,(
% 6.90/1.26    ( ! [X30,X28,X26,X33,X31,X29,X27,X25,X34,X32] : (~m1_subset_1(k2_zfmisc_1(sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(X31,X32))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X27,X28))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X29,X30))) | v1_funct_1(k6_relat_1(sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X25,X26))) | ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X33,X34)))) )),
% 6.90/1.26    inference(resolution,[],[f1403,f71])).
% 6.90/1.26  fof(f1403,plain,(
% 6.90/1.26    ( ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1,X9] : (~m1_subset_1(sK3,k1_zfmisc_1(X2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) | v1_funct_1(k6_relat_1(sK2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X7,X8))) | ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X9,X10)))) )),
% 6.90/1.26    inference(resolution,[],[f1322,f85])).
% 6.90/1.26  fof(f1322,plain,(
% 6.90/1.26    ( ! [X26,X24,X23,X21,X19,X27,X25,X22,X20,X18] : (~v1_relat_1(X27) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X20,X21))) | ~m1_subset_1(sK3,k1_zfmisc_1(X22)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X23,X24))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X25,X26))) | v1_funct_1(k6_relat_1(sK2)) | ~m1_subset_1(X22,k1_zfmisc_1(X27)) | ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X18,X19)))) )),
% 6.90/1.26    inference(resolution,[],[f1311,f82])).
% 6.90/1.26  fof(f1311,plain,(
% 6.90/1.26    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (~v1_relat_1(X6) | ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | ~m1_subset_1(sK3,k1_zfmisc_1(X6)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X7,X8))) | v1_funct_1(k6_relat_1(sK2))) )),
% 6.90/1.26    inference(resolution,[],[f1307,f85])).
% 6.90/1.26  fof(f1307,plain,(
% 6.90/1.26    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (~v1_relat_1(X7) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | ~m1_subset_1(sK3,k1_zfmisc_1(X6)) | ~v1_relat_1(X6) | ~m1_subset_1(sK3,k1_zfmisc_1(X7)) | v1_funct_1(k6_relat_1(sK2))) )),
% 6.90/1.26    inference(subsumption_resolution,[],[f1304,f130])).
% 6.90/1.26  fof(f1304,plain,(
% 6.90/1.26    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (v1_funct_1(k6_relat_1(sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | ~m1_subset_1(sK3,k1_zfmisc_1(X6)) | ~v1_relat_1(X6) | ~r1_tarski(k2_relat_1(sK3),k2_relat_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(X7)) | ~v1_relat_1(X7)) )),
% 6.90/1.26    inference(resolution,[],[f1301,f211])).
% 6.90/1.26  fof(f1301,plain,(
% 6.90/1.26    ( ! [X6,X4,X2,X0,X5,X3,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_relat_1(sK3)))) | v1_funct_1(k6_relat_1(sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(sK3,k1_zfmisc_1(X6)) | ~v1_relat_1(X6)) )),
% 6.90/1.26    inference(resolution,[],[f1295,f82])).
% 6.90/1.26  fof(f1295,plain,(
% 6.90/1.26    ( ! [X12,X10,X8,X7,X11,X9] : (~v1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X7,X8))) | v1_funct_1(k6_relat_1(sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X9,X10))) | ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X11,X12))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_relat_1(sK3))))) )),
% 6.90/1.26    inference(forward_demodulation,[],[f1294,f192])).
% 6.90/1.26  fof(f1294,plain,(
% 6.90/1.26    ( ! [X12,X10,X8,X7,X11,X9] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X7,X8))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))) | v1_funct_1(k6_relat_1(sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X9,X10))) | ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X11,X12))) | ~v1_relat_1(sK3)) )),
% 6.90/1.26    inference(subsumption_resolution,[],[f1293,f69])).
% 6.90/1.26  fof(f1293,plain,(
% 6.90/1.26    ( ! [X12,X10,X8,X7,X11,X9] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X7,X8))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))) | v1_funct_1(k6_relat_1(sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X9,X10))) | ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X11,X12))) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)) )),
% 6.90/1.26    inference(subsumption_resolution,[],[f1289,f130])).
% 6.90/1.26  fof(f1289,plain,(
% 6.90/1.26    ( ! [X12,X10,X8,X7,X11,X9] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X7,X8))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))) | v1_funct_1(k6_relat_1(sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X9,X10))) | ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X11,X12))) | ~r1_tarski(k2_relat_1(sK3),k2_relat_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)) )),
% 6.90/1.26    inference(resolution,[],[f1285,f87])).
% 6.90/1.26  fof(f1285,plain,(
% 6.90/1.26    ( ! [X6,X4,X2,X0,X5,X3,X1] : (~v1_funct_2(sK3,X2,k2_relat_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,k2_relat_1(sK3)))) | v1_funct_1(k6_relat_1(sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X5,X6)))) )),
% 6.90/1.26    inference(equality_resolution,[],[f1278])).
% 6.90/1.26  fof(f1278,plain,(
% 6.90/1.26    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_relat_1(sK3) != X5 | v1_funct_1(k6_relat_1(sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | ~v1_funct_2(sK3,X4,X5) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) | ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.90/1.26    inference(resolution,[],[f1277,f85])).
% 6.90/1.26  fof(f1277,plain,(
% 6.90/1.26    ( ! [X6,X4,X2,X0,X5,X3,X1] : (~v1_relat_1(X6) | ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | v1_funct_1(k6_relat_1(sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK3,X0,X1) | ~m1_subset_1(sK3,k1_zfmisc_1(X6)) | k2_relat_1(sK3) != X1) )),
% 6.90/1.26    inference(duplicate_literal_removal,[],[f1276])).
% 6.90/1.26  fof(f1276,plain,(
% 6.90/1.26    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_relat_1(sK3) != X1 | ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | v1_funct_1(k6_relat_1(sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK3,X0,X1) | ~m1_subset_1(sK3,k1_zfmisc_1(X6)) | ~v1_relat_1(X6) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.90/1.26    inference(superposition,[],[f1049,f98])).
% 6.90/1.26  fof(f1049,plain,(
% 6.90/1.26    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_relset_1(X4,X5,sK3) != X5 | ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | v1_funct_1(k6_relat_1(sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | ~v1_funct_2(sK3,X4,X5) | ~m1_subset_1(sK3,k1_zfmisc_1(X6)) | ~v1_relat_1(X6)) )),
% 6.90/1.26    inference(resolution,[],[f875,f82])).
% 6.90/1.26  fof(f875,plain,(
% 6.90/1.26    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | v1_funct_1(k6_relat_1(sK2)) | k2_relset_1(X4,X5,sK3) != X5 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | ~v1_funct_2(sK3,X4,X5)) )),
% 6.90/1.26    inference(forward_demodulation,[],[f874,f192])).
% 6.90/1.26  fof(f874,plain,(
% 6.90/1.26    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k6_relat_1(k1_relat_1(sK3))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_relat_1(sK3) | k2_relset_1(X4,X5,sK3) != X5 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | ~v1_funct_2(sK3,X4,X5)) )),
% 6.90/1.26    inference(subsumption_resolution,[],[f872,f69])).
% 6.90/1.26  fof(f872,plain,(
% 6.90/1.26    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k6_relat_1(k1_relat_1(sK3))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(sK3) | ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_relat_1(sK3) | k2_relset_1(X4,X5,sK3) != X5 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | ~v1_funct_2(sK3,X4,X5)) )),
% 6.90/1.26    inference(resolution,[],[f505,f76])).
% 6.90/1.26  fof(f505,plain,(
% 6.90/1.26    ( ! [X6,X4,X2,X0,X5,X3,X1] : (~v2_funct_1(X0) | v1_funct_1(k6_relat_1(k1_relat_1(X0))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_1(X0) | ~m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_relat_1(X0) | k2_relset_1(X5,X6,X0) != X6 | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) | ~v1_funct_2(X0,X5,X6)) )),
% 6.90/1.26    inference(duplicate_literal_removal,[],[f504])).
% 6.90/1.26  fof(f504,plain,(
% 6.90/1.26    ( ! [X6,X4,X2,X0,X5,X3,X1] : (~m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_funct_1(k6_relat_1(k1_relat_1(X0))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0) | k2_relset_1(X5,X6,X0) != X6 | ~v2_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) | ~v1_funct_2(X0,X5,X6) | ~v1_funct_1(X0)) )),
% 6.90/1.26    inference(resolution,[],[f338,f104])).
% 6.90/1.26  fof(f104,plain,(
% 6.90/1.26    ( ! [X2,X0,X1] : (v1_funct_1(k2_funct_1(X2)) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 6.90/1.26    inference(cnf_transformation,[],[f39])).
% 6.90/1.26  fof(f338,plain,(
% 6.90/1.26    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_1(k2_funct_1(X0)) | ~m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_funct_1(k6_relat_1(k1_relat_1(X0))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 6.90/1.26    inference(duplicate_literal_removal,[],[f334])).
% 6.90/1.26  fof(f334,plain,(
% 6.90/1.26    ( ! [X4,X2,X0,X3,X1] : (v1_funct_1(k6_relat_1(k1_relat_1(X0))) | ~m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(k2_funct_1(X0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 6.90/1.26    inference(superposition,[],[f253,f83])).
% 6.90/1.26  fof(f83,plain,(
% 6.90/1.26    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 6.90/1.26    inference(cnf_transformation,[],[f28])).
% 6.90/1.26  fof(f28,plain,(
% 6.90/1.26    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 6.90/1.26    inference(flattening,[],[f27])).
% 6.90/1.26  fof(f27,plain,(
% 6.90/1.26    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 6.90/1.26    inference(ennf_transformation,[],[f7])).
% 6.90/1.26  fof(f7,axiom,(
% 6.90/1.26    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 6.90/1.26    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).
% 6.90/1.26  fof(f253,plain,(
% 6.90/1.26    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k5_relat_1(X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 6.90/1.26    inference(duplicate_literal_removal,[],[f252])).
% 6.90/1.26  fof(f252,plain,(
% 6.90/1.26    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k5_relat_1(X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 6.90/1.26    inference(superposition,[],[f122,f121])).
% 6.90/1.26  fof(f122,plain,(
% 6.90/1.26    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 6.90/1.26    inference(cnf_transformation,[],[f47])).
% 6.90/1.26  fof(f1627,plain,(
% 6.90/1.26    k1_xboole_0 = sK2 | sK4 = k6_relat_1(sK2) | ~v1_funct_1(k6_relat_1(sK2)) | ~m1_subset_1(k6_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))),
% 6.90/1.26    inference(subsumption_resolution,[],[f1626,f127])).
% 6.90/1.26  fof(f127,plain,(
% 6.90/1.26    ( ! [X0] : (v1_partfun1(k6_relat_1(X0),X0)) )),
% 6.90/1.26    inference(definition_unfolding,[],[f80,f79])).
% 6.90/1.26  fof(f80,plain,(
% 6.90/1.26    ( ! [X0] : (v1_partfun1(k6_partfun1(X0),X0)) )),
% 6.90/1.26    inference(cnf_transformation,[],[f14])).
% 6.90/1.26  fof(f1626,plain,(
% 6.90/1.26    k1_xboole_0 = sK2 | sK4 = k6_relat_1(sK2) | ~v1_partfun1(k6_relat_1(sK2),sK2) | ~v1_funct_1(k6_relat_1(sK2)) | ~m1_subset_1(k6_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))),
% 6.90/1.26    inference(resolution,[],[f1613,f103])).
% 6.90/1.26  fof(f103,plain,(
% 6.90/1.26    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.90/1.26    inference(cnf_transformation,[],[f37])).
% 6.90/1.26  fof(f37,plain,(
% 6.90/1.26    ! [X0,X1,X2] : ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.90/1.26    inference(flattening,[],[f36])).
% 6.90/1.26  fof(f36,plain,(
% 6.90/1.26    ! [X0,X1,X2] : (((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~v1_partfun1(X2,X0) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.90/1.26    inference(ennf_transformation,[],[f12])).
% 6.90/1.26  fof(f12,axiom,(
% 6.90/1.26    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_partfun1(X2,X0) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 6.90/1.26    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_2)).
% 6.90/1.26  fof(f1613,plain,(
% 6.90/1.26    ~v1_funct_2(k6_relat_1(sK2),sK2,sK2) | k1_xboole_0 = sK2 | sK4 = k6_relat_1(sK2)),
% 6.90/1.26    inference(resolution,[],[f1595,f1133])).
% 6.90/1.26  fof(f1133,plain,(
% 6.90/1.26    ~v1_funct_1(k6_relat_1(sK2)) | ~v1_funct_2(k6_relat_1(sK2),sK2,sK2) | k1_xboole_0 = sK2 | sK4 = k6_relat_1(sK2)),
% 6.90/1.26    inference(subsumption_resolution,[],[f1132,f71])).
% 6.90/1.26  fof(f1132,plain,(
% 6.90/1.26    ~v1_funct_2(k6_relat_1(sK2),sK2,sK2) | ~v1_funct_1(k6_relat_1(sK2)) | k1_xboole_0 = sK2 | sK4 = k6_relat_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))),
% 6.90/1.26    inference(subsumption_resolution,[],[f1129,f126])).
% 6.90/1.26  fof(f1129,plain,(
% 6.90/1.26    ~v1_funct_2(k6_relat_1(sK2),sK2,sK2) | ~v1_funct_1(k6_relat_1(sK2)) | k1_xboole_0 = sK2 | ~m1_subset_1(k6_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | sK4 = k6_relat_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))),
% 6.90/1.26    inference(resolution,[],[f1128,f236])).
% 6.90/1.26  fof(f236,plain,(
% 6.90/1.26    ( ! [X4,X5,X3] : (r2_relset_1(X3,X4,k5_relat_1(k6_relat_1(X3),X5),X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) )),
% 6.90/1.26    inference(subsumption_resolution,[],[f233,f126])).
% 6.90/1.26  fof(f233,plain,(
% 6.90/1.26    ( ! [X4,X5,X3] : (r2_relset_1(X3,X4,k5_relat_1(k6_relat_1(X3),X5),X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~m1_subset_1(k6_relat_1(X3),k1_zfmisc_1(k2_zfmisc_1(X3,X3)))) )),
% 6.90/1.26    inference(duplicate_literal_removal,[],[f232])).
% 6.90/1.26  fof(f232,plain,(
% 6.90/1.26    ( ! [X4,X5,X3] : (r2_relset_1(X3,X4,k5_relat_1(k6_relat_1(X3),X5),X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~m1_subset_1(k6_relat_1(X3),k1_zfmisc_1(k2_zfmisc_1(X3,X3)))) )),
% 6.90/1.26    inference(superposition,[],[f129,f124])).
% 6.90/1.26  fof(f124,plain,(
% 6.90/1.26    ( ! [X4,X2,X0,X5,X3,X1] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.90/1.26    inference(cnf_transformation,[],[f49])).
% 6.90/1.26  fof(f49,plain,(
% 6.90/1.26    ! [X0,X1,X2,X3,X4,X5] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.90/1.26    inference(flattening,[],[f48])).
% 6.90/1.26  fof(f48,plain,(
% 6.90/1.26    ! [X0,X1,X2,X3,X4,X5] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 6.90/1.26    inference(ennf_transformation,[],[f10])).
% 6.90/1.26  fof(f10,axiom,(
% 6.90/1.26    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 6.90/1.26    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_relset_1)).
% 6.90/1.26  fof(f129,plain,(
% 6.90/1.26    ( ! [X2,X0,X1] : (r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_relat_1(X0),X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.90/1.26    inference(definition_unfolding,[],[f100,f79])).
% 6.90/1.26  fof(f100,plain,(
% 6.90/1.26    ( ! [X2,X0,X1] : (r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.90/1.26    inference(cnf_transformation,[],[f35])).
% 6.90/1.26  fof(f35,plain,(
% 6.90/1.26    ! [X0,X1,X2] : ((r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2) & r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.90/1.26    inference(ennf_transformation,[],[f17])).
% 6.90/1.26  fof(f17,axiom,(
% 6.90/1.26    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2) & r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2)))),
% 6.90/1.26    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_2)).
% 6.90/1.26  fof(f1128,plain,(
% 6.90/1.26    ( ! [X0] : (~r2_relset_1(sK2,sK2,k5_relat_1(X0,sK3),sK3) | ~v1_funct_2(X0,sK2,sK2) | ~v1_funct_1(X0) | k1_xboole_0 = sK2 | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | sK4 = X0) )),
% 6.90/1.26    inference(subsumption_resolution,[],[f1127,f74])).
% 6.90/1.26  fof(f1127,plain,(
% 6.90/1.26    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_2(X0,sK2,sK2) | ~v1_funct_1(X0) | k1_xboole_0 = sK2 | ~r2_relset_1(sK2,sK2,k5_relat_1(X0,sK3),sK3) | sK4 = X0 | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))) )),
% 6.90/1.26    inference(duplicate_literal_removal,[],[f1126])).
% 6.90/1.26  fof(f1126,plain,(
% 6.90/1.26    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_2(X0,sK2,sK2) | ~v1_funct_1(X0) | k1_xboole_0 = sK2 | ~r2_relset_1(sK2,sK2,k5_relat_1(X0,sK3),sK3) | sK4 = X0 | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))) )),
% 6.90/1.26    inference(resolution,[],[f1125,f119])).
% 6.90/1.26  fof(f125,plain,(
% 6.90/1.26    ~r2_relset_1(sK2,sK2,sK4,k6_relat_1(sK2))),
% 6.90/1.26    inference(definition_unfolding,[],[f77,f79])).
% 6.90/1.26  fof(f77,plain,(
% 6.90/1.26    ~r2_relset_1(sK2,sK2,sK4,k6_partfun1(sK2))),
% 6.90/1.26    inference(cnf_transformation,[],[f55])).
% 6.90/1.26  fof(f2379,plain,(
% 6.90/1.26    k1_xboole_0 = sK4 | ~r1_tarski(k2_zfmisc_1(sK2,sK2),sK4)),
% 6.90/1.26    inference(forward_demodulation,[],[f1722,f132])).
% 6.90/1.26  fof(f1722,plain,(
% 6.90/1.26    sK4 = k2_zfmisc_1(k1_xboole_0,k1_xboole_0) | ~r1_tarski(k2_zfmisc_1(sK2,sK2),sK4)),
% 6.90/1.26    inference(backward_demodulation,[],[f165,f1713])).
% 6.90/1.26  fof(f165,plain,(
% 6.90/1.26    ~r1_tarski(k2_zfmisc_1(sK2,sK2),sK4) | k2_zfmisc_1(sK2,sK2) = sK4),
% 6.90/1.26    inference(resolution,[],[f159,f94])).
% 6.90/1.26  fof(f159,plain,(
% 6.90/1.26    ~m1_subset_1(k2_zfmisc_1(sK2,sK2),k1_zfmisc_1(sK4)) | k2_zfmisc_1(sK2,sK2) = sK4),
% 6.90/1.26    inference(resolution,[],[f157,f74])).
% 6.90/1.26  fof(f157,plain,(
% 6.90/1.26    ( ! [X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(X2)) | X2 = X3 | ~m1_subset_1(X2,k1_zfmisc_1(X3))) )),
% 6.90/1.26    inference(resolution,[],[f142,f93])).
% 6.90/1.26  fof(f142,plain,(
% 6.90/1.26    ( ! [X2,X3] : (~r1_tarski(X2,X3) | X2 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(X2))) )),
% 6.90/1.26    inference(resolution,[],[f92,f93])).
% 6.90/1.26  fof(f1870,plain,(
% 6.90/1.26    ~r2_relset_1(k1_xboole_0,k1_xboole_0,sK4,k1_xboole_0)),
% 6.90/1.26    inference(forward_demodulation,[],[f1718,f146])).
% 6.90/1.26  fof(f1718,plain,(
% 6.90/1.26    ~r2_relset_1(k1_xboole_0,k1_xboole_0,sK4,k6_relat_1(k1_xboole_0))),
% 6.90/1.26    inference(backward_demodulation,[],[f125,f1713])).
% 6.90/1.26  % SZS output end Proof for theBenchmark
% 6.90/1.26  % (32117)------------------------------
% 6.90/1.26  % (32117)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.90/1.26  % (32117)Termination reason: Refutation
% 6.90/1.26  
% 6.90/1.26  % (32117)Memory used [KB]: 9850
% 6.90/1.26  % (32117)Time elapsed: 0.836 s
% 6.90/1.26  % (32117)------------------------------
% 6.90/1.26  % (32117)------------------------------
% 6.90/1.26  % (32094)Success in time 0.886 s
%------------------------------------------------------------------------------
