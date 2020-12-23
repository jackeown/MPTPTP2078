%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:05:25 EST 2020

% Result     : Theorem 5.91s
% Output     : Refutation 6.31s
% Verified   : 
% Statistics : Number of formulae       :  244 (4632 expanded)
%              Number of leaves         :   33 (1306 expanded)
%              Depth                    :   59
%              Number of atoms          : 1073 (31262 expanded)
%              Number of equality atoms :  164 (1668 expanded)
%              Maximal formula depth    :   21 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3543,plain,(
    $false ),
    inference(subsumption_resolution,[],[f3542,f174])).

fof(f174,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(backward_demodulation,[],[f155,f170])).

fof(f170,plain,(
    k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    inference(resolution,[],[f167,f157])).

fof(f157,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f113,f88])).

fof(f88,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f113,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

fof(f167,plain,(
    v1_xboole_0(k6_partfun1(k1_xboole_0)) ),
    inference(resolution,[],[f166,f155])).

fof(f166,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
      | v1_xboole_0(X0) ) ),
    inference(forward_demodulation,[],[f165,f151])).

fof(f151,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f112])).

fof(f112,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f165,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f100,f88])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

fof(f155,plain,(
    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[],[f93,f151])).

fof(f93,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f3542,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f3529,f151])).

fof(f3529,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(resolution,[],[f3179,f154])).

fof(f154,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(duplicate_literal_removal,[],[f153])).

fof(f153,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f138])).

fof(f138,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f78,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f3179,plain,(
    ~ r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f2941,f3153])).

fof(f3153,plain,(
    k1_xboole_0 = sK4 ),
    inference(subsumption_resolution,[],[f3152,f232])).

fof(f232,plain,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    inference(subsumption_resolution,[],[f231,f174])).

fof(f231,plain,(
    ! [X1] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
      | r1_tarski(k1_xboole_0,X1) ) ),
    inference(superposition,[],[f201,f152])).

fof(f152,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f111])).

fof(f111,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f70])).

fof(f201,plain,(
    ! [X4,X3] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X4,X3)))
      | r1_tarski(k1_xboole_0,X3) ) ),
    inference(superposition,[],[f164,f182])).

fof(f182,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f145,f170])).

fof(f145,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f95,f89])).

fof(f89,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f95,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f164,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_relat_1(X0),X2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(subsumption_resolution,[],[f163,f114])).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f163,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | r1_tarski(k2_relat_1(X0),X2)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f118,f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f118,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f3152,plain,
    ( ~ r1_tarski(k1_xboole_0,sK4)
    | k1_xboole_0 = sK4 ),
    inference(forward_demodulation,[],[f3151,f151])).

fof(f3151,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),sK4)
    | k1_xboole_0 = sK4 ),
    inference(forward_demodulation,[],[f3150,f2839])).

fof(f2839,plain,(
    k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f2831,f81])).

fof(f81,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,
    ( ~ r2_relset_1(sK2,sK2,sK4,k6_partfun1(sK2))
    & v2_funct_1(sK3)
    & r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3),sK3)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    & v1_funct_2(sK4,sK2,sK2)
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    & v1_funct_2(sK3,sK2,sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f30,f63,f62])).

fof(f62,plain,
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

fof(f63,plain,
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

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f28])).

fof(f28,negated_conjecture,(
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
    inference(negated_conjecture,[],[f27])).

fof(f27,conjecture,(
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

fof(f2831,plain,
    ( k1_xboole_0 = sK2
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(resolution,[],[f2824,f323])).

fof(f323,plain,(
    ! [X2,X0,X1] :
      ( r2_relset_1(X0,X1,k5_relat_1(k6_partfun1(X0),X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(subsumption_resolution,[],[f322,f93])).

fof(f322,plain,(
    ! [X2,X0,X1] :
      ( r2_relset_1(X0,X1,k5_relat_1(k6_partfun1(X0),X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(duplicate_literal_removal,[],[f319])).

fof(f319,plain,(
    ! [X2,X0,X1] :
      ( r2_relset_1(X0,X1,k5_relat_1(k6_partfun1(X0),X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(superposition,[],[f119,f142])).

fof(f142,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

fof(f119,plain,(
    ! [X2,X0,X1] :
      ( r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2)
        & r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2)
        & r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_2)).

fof(f2824,plain,
    ( ~ r2_relset_1(sK2,sK2,k5_relat_1(k6_partfun1(sK2),sK3),sK3)
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f2823,f2757])).

fof(f2757,plain,(
    v1_funct_1(k6_partfun1(sK2)) ),
    inference(resolution,[],[f2747,f81])).

fof(f2747,plain,(
    ! [X6,X7] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
      | v1_funct_1(k6_partfun1(sK2)) ) ),
    inference(resolution,[],[f2741,f81])).

fof(f2741,plain,(
    ! [X10,X8,X11,X9] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))
      | v1_funct_1(k6_partfun1(sK2))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X10,X11))) ) ),
    inference(resolution,[],[f2730,f81])).

fof(f2730,plain,(
    ! [X12,X10,X8,X13,X11,X9] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X12,X13)))
      | v1_funct_1(k6_partfun1(sK2))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X8,X9))) ) ),
    inference(trivial_inequality_removal,[],[f2728])).

fof(f2728,plain,(
    ! [X12,X10,X8,X13,X11,X9] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))
      | v1_funct_1(k6_partfun1(sK2))
      | k2_relat_1(sK3) != k2_relat_1(sK3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X12,X13))) ) ),
    inference(resolution,[],[f2689,f149])).

fof(f149,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f106])).

fof(f106,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f2689,plain,(
    ! [X6,X4,X10,X8,X7,X5,X9] :
      ( ~ r1_tarski(k2_relat_1(sK3),X8)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
      | v1_funct_1(k6_partfun1(sK2))
      | k2_relat_1(sK3) != X8
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X9,X10))) ) ),
    inference(resolution,[],[f2685,f454])).

fof(f454,plain,(
    ! [X17,X15,X16] :
      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,X15)))
      | ~ r1_tarski(k2_relat_1(sK3),X15)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X16,X17))) ) ),
    inference(forward_demodulation,[],[f450,f439])).

fof(f439,plain,(
    sK2 = k1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f438,f79])).

fof(f79,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f64])).

fof(f438,plain,
    ( sK2 = k1_relat_1(sK3)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f433,f81])).

fof(f433,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | sK2 = k1_relat_1(sK3)
    | ~ v1_funct_1(sK3) ),
    inference(resolution,[],[f251,f80])).

fof(f80,plain,(
    v1_funct_2(sK3,sK2,sK2) ),
    inference(cnf_transformation,[],[f64])).

fof(f251,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(X1,X0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | k1_relat_1(X1) = X0
      | ~ v1_funct_1(X1) ) ),
    inference(duplicate_literal_removal,[],[f248])).

fof(f248,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(superposition,[],[f104,f115])).

fof(f115,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f104,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k1_relset_1(X0,X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_2)).

fof(f450,plain,(
    ! [X17,X15,X16] :
      ( ~ r1_tarski(k2_relat_1(sK3),X15)
      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X15)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X16,X17))) ) ),
    inference(resolution,[],[f222,f79])).

fof(f222,plain,(
    ! [X4,X2,X5,X3] :
      ( ~ v1_funct_1(X2)
      | ~ r1_tarski(k2_relat_1(X2),X3)
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X3)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) ) ),
    inference(resolution,[],[f103,f114])).

fof(f103,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

fof(f2685,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,X4)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | v1_funct_1(k6_partfun1(sK2))
      | k2_relat_1(sK3) != X4 ) ),
    inference(forward_demodulation,[],[f2684,f439])).

fof(f2684,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | v1_funct_1(k6_partfun1(sK2))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X4)))
      | k2_relat_1(sK3) != X4 ) ),
    inference(subsumption_resolution,[],[f2683,f114])).

fof(f2683,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | v1_funct_1(k6_partfun1(sK2))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X4)))
      | k2_relat_1(sK3) != X4
      | ~ v1_relat_1(sK3) ) ),
    inference(subsumption_resolution,[],[f2682,f164])).

fof(f2682,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | v1_funct_1(k6_partfun1(sK2))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X4)))
      | k2_relat_1(sK3) != X4
      | ~ r1_tarski(k2_relat_1(sK3),X4)
      | ~ v1_relat_1(sK3) ) ),
    inference(subsumption_resolution,[],[f2679,f79])).

fof(f2679,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | v1_funct_1(k6_partfun1(sK2))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X4)))
      | k2_relat_1(sK3) != X4
      | ~ r1_tarski(k2_relat_1(sK3),X4)
      | ~ v1_funct_1(sK3)
      | ~ v1_relat_1(sK3) ) ),
    inference(resolution,[],[f2673,f102])).

fof(f102,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f2673,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_2(sK3,X0,X1)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | v1_funct_1(k6_partfun1(sK2))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relat_1(sK3) != X1 ) ),
    inference(duplicate_literal_removal,[],[f2672])).

fof(f2672,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k2_relat_1(sK3) != X1
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | v1_funct_1(k6_partfun1(sK2))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(sK3,X0,X1)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(superposition,[],[f2429,f116])).

fof(f116,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f2429,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k2_relset_1(X4,X5,sK3) != X5
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | v1_funct_1(k6_partfun1(sK2))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | ~ v1_funct_2(sK3,X4,X5) ) ),
    inference(subsumption_resolution,[],[f2428,f79])).

fof(f2428,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_1(k6_partfun1(sK2))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k2_relset_1(X4,X5,sK3) != X5
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | ~ v1_funct_2(sK3,X4,X5)
      | ~ v1_funct_1(sK3) ) ),
    inference(subsumption_resolution,[],[f2423,f86])).

fof(f86,plain,(
    v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f64])).

fof(f2423,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_1(k6_partfun1(sK2))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k2_relset_1(X4,X5,sK3) != X5
      | ~ v2_funct_1(sK3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | ~ v1_funct_2(sK3,X4,X5)
      | ~ v1_funct_1(sK3) ) ),
    inference(resolution,[],[f2422,f123])).

fof(f123,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
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

fof(f2422,plain,(
    ! [X12,X10,X8,X13,X11,X9] :
      ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X8,X9)))
      | v1_funct_1(k6_partfun1(sK2))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X12,X13))) ) ),
    inference(trivial_inequality_removal,[],[f2420])).

fof(f2420,plain,(
    ! [X12,X10,X8,X13,X11,X9] :
      ( k2_relat_1(sK3) != k2_relat_1(sK3)
      | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X8,X9)))
      | v1_funct_1(k6_partfun1(sK2))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X12,X13))) ) ),
    inference(resolution,[],[f2281,f149])).

fof(f2281,plain,(
    ! [X6,X4,X10,X8,X7,X5,X9] :
      ( ~ r1_tarski(k2_relat_1(sK3),X6)
      | k2_relat_1(sK3) != X6
      | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
      | v1_funct_1(k6_partfun1(sK2))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X9,X10))) ) ),
    inference(resolution,[],[f2279,f454])).

fof(f2279,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,X2)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relat_1(sK3) != X2
      | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | v1_funct_1(k6_partfun1(sK2)) ) ),
    inference(forward_demodulation,[],[f2278,f439])).

fof(f2278,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relat_1(sK3) != X2
      | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X2)))
      | v1_funct_1(k6_partfun1(sK2)) ) ),
    inference(subsumption_resolution,[],[f2277,f114])).

fof(f2277,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relat_1(sK3) != X2
      | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X2)))
      | v1_funct_1(k6_partfun1(sK2))
      | ~ v1_relat_1(sK3) ) ),
    inference(subsumption_resolution,[],[f2276,f164])).

fof(f2276,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relat_1(sK3) != X2
      | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X2)))
      | v1_funct_1(k6_partfun1(sK2))
      | ~ r1_tarski(k2_relat_1(sK3),X2)
      | ~ v1_relat_1(sK3) ) ),
    inference(subsumption_resolution,[],[f2273,f79])).

fof(f2273,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relat_1(sK3) != X2
      | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X2)))
      | v1_funct_1(k6_partfun1(sK2))
      | ~ r1_tarski(k2_relat_1(sK3),X2)
      | ~ v1_funct_1(sK3)
      | ~ v1_relat_1(sK3) ) ),
    inference(resolution,[],[f2270,f102])).

fof(f2270,plain,(
    ! [X26,X24,X23,X27,X25,X22] :
      ( ~ v1_funct_2(sK3,X27,X24)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X22,X23)))
      | k2_relat_1(sK3) != X24
      | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X25,X26)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X27,X24)))
      | v1_funct_1(k6_partfun1(sK2)) ) ),
    inference(forward_demodulation,[],[f2269,f439])).

fof(f2269,plain,(
    ! [X26,X24,X23,X27,X25,X22] :
      ( v1_funct_1(k6_partfun1(k1_relat_1(sK3)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X22,X23)))
      | k2_relat_1(sK3) != X24
      | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X25,X26)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X27,X24)))
      | ~ v1_funct_2(sK3,X27,X24) ) ),
    inference(subsumption_resolution,[],[f2265,f79])).

fof(f2265,plain,(
    ! [X26,X24,X23,X27,X25,X22] :
      ( v1_funct_1(k6_partfun1(k1_relat_1(sK3)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X22,X23)))
      | ~ v1_funct_1(sK3)
      | k2_relat_1(sK3) != X24
      | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X25,X26)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X27,X24)))
      | ~ v1_funct_2(sK3,X27,X24) ) ),
    inference(resolution,[],[f1405,f86])).

fof(f1405,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( ~ v2_funct_1(X2)
      | v1_funct_1(k6_partfun1(k1_relat_1(X2)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_1(X2)
      | k2_relat_1(X2) != X1
      | ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f1404])).

fof(f1404,plain,(
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
    inference(superposition,[],[f745,f116])).

fof(f745,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( k2_relset_1(X5,X6,X0) != X6
      | v1_funct_1(k6_partfun1(k1_relat_1(X0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
      | ~ v1_funct_2(X0,X5,X6) ) ),
    inference(duplicate_literal_removal,[],[f744])).

fof(f744,plain,(
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
    inference(resolution,[],[f465,f121])).

fof(f121,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(k2_funct_1(X2))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f465,plain,(
    ! [X6,X8,X7,X5,X9] :
      ( ~ v1_funct_1(k2_funct_1(X5))
      | ~ m1_subset_1(k2_funct_1(X5),k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
      | v1_funct_1(k6_partfun1(k1_relat_1(X5)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))
      | ~ v1_funct_1(X5)
      | ~ v2_funct_1(X5) ) ),
    inference(subsumption_resolution,[],[f462,f114])).

fof(f462,plain,(
    ! [X6,X8,X7,X5,X9] :
      ( v1_funct_1(k6_partfun1(k1_relat_1(X5)))
      | ~ m1_subset_1(k2_funct_1(X5),k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
      | ~ v1_funct_1(k2_funct_1(X5))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))
      | ~ v1_funct_1(X5)
      | ~ v2_funct_1(X5)
      | ~ v1_relat_1(X5) ) ),
    inference(duplicate_literal_removal,[],[f460])).

fof(f460,plain,(
    ! [X6,X8,X7,X5,X9] :
      ( v1_funct_1(k6_partfun1(k1_relat_1(X5)))
      | ~ m1_subset_1(k2_funct_1(X5),k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
      | ~ v1_funct_1(k2_funct_1(X5))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))
      | ~ v1_funct_1(X5)
      | ~ v2_funct_1(X5)
      | ~ v1_funct_1(X5)
      | ~ v1_relat_1(X5) ) ),
    inference(superposition,[],[f360,f148])).

fof(f148,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f96,f89])).

fof(f96,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

fof(f360,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_1(k5_relat_1(X4,X5))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(duplicate_literal_removal,[],[f359])).

fof(f359,plain,(
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
    inference(superposition,[],[f140,f139])).

fof(f139,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f140,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f2823,plain,
    ( ~ r2_relset_1(sK2,sK2,k5_relat_1(k6_partfun1(sK2),sK3),sK3)
    | k1_xboole_0 = sK2
    | ~ v1_funct_1(k6_partfun1(sK2)) ),
    inference(subsumption_resolution,[],[f2822,f93])).

fof(f2822,plain,
    ( ~ r2_relset_1(sK2,sK2,k5_relat_1(k6_partfun1(sK2),sK3),sK3)
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(k6_partfun1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v1_funct_1(k6_partfun1(sK2)) ),
    inference(subsumption_resolution,[],[f2821,f79])).

fof(f2821,plain,
    ( ~ r2_relset_1(sK2,sK2,k5_relat_1(k6_partfun1(sK2),sK3),sK3)
    | k1_xboole_0 = sK2
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(k6_partfun1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v1_funct_1(k6_partfun1(sK2)) ),
    inference(subsumption_resolution,[],[f2812,f81])).

fof(f2812,plain,
    ( ~ r2_relset_1(sK2,sK2,k5_relat_1(k6_partfun1(sK2),sK3),sK3)
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(k6_partfun1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v1_funct_1(k6_partfun1(sK2)) ),
    inference(superposition,[],[f2798,f139])).

fof(f2798,plain,
    ( ~ r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,k6_partfun1(sK2),sK3),sK3)
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f2795,f2757])).

fof(f2795,plain,
    ( ~ r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,k6_partfun1(sK2),sK3),sK3)
    | ~ v1_funct_1(k6_partfun1(sK2))
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f2788,f2187])).

fof(f2187,plain,
    ( ~ v1_funct_2(k6_partfun1(sK2),sK2,sK2)
    | ~ r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,k6_partfun1(sK2),sK3),sK3)
    | ~ v1_funct_1(k6_partfun1(sK2))
    | k1_xboole_0 = sK2 ),
    inference(forward_demodulation,[],[f2186,f398])).

fof(f398,plain,(
    sK3 = k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3) ),
    inference(subsumption_resolution,[],[f397,f82])).

fof(f82,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f64])).

fof(f397,plain,
    ( sK3 = k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3)
    | ~ v1_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f396,f84])).

fof(f84,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(cnf_transformation,[],[f64])).

fof(f396,plain,
    ( sK3 = k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v1_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f395,f79])).

fof(f395,plain,
    ( sK3 = k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v1_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f392,f81])).

fof(f392,plain,
    ( sK3 = k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v1_funct_1(sK4) ),
    inference(resolution,[],[f293,f141])).

fof(f141,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f293,plain,
    ( ~ m1_subset_1(k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | sK3 = k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3) ),
    inference(subsumption_resolution,[],[f286,f81])).

fof(f286,plain,
    ( sK3 = k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ m1_subset_1(k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(resolution,[],[f137,f85])).

fof(f85,plain,(
    r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3),sK3) ),
    inference(cnf_transformation,[],[f64])).

fof(f137,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f2186,plain,
    ( ~ r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,k6_partfun1(sK2),sK3),k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3))
    | ~ v1_funct_2(k6_partfun1(sK2),sK2,sK2)
    | ~ v1_funct_1(k6_partfun1(sK2))
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f2185,f93])).

fof(f2185,plain,
    ( ~ r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,k6_partfun1(sK2),sK3),k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3))
    | ~ m1_subset_1(k6_partfun1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v1_funct_2(k6_partfun1(sK2),sK2,sK2)
    | ~ v1_funct_1(k6_partfun1(sK2))
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f2184,f82])).

fof(f2184,plain,
    ( ~ r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,k6_partfun1(sK2),sK3),k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(k6_partfun1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v1_funct_2(k6_partfun1(sK2),sK2,sK2)
    | ~ v1_funct_1(k6_partfun1(sK2))
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f2183,f83])).

fof(f83,plain,(
    v1_funct_2(sK4,sK2,sK2) ),
    inference(cnf_transformation,[],[f64])).

fof(f2183,plain,
    ( ~ r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,k6_partfun1(sK2),sK3),k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3))
    | ~ v1_funct_2(sK4,sK2,sK2)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(k6_partfun1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v1_funct_2(k6_partfun1(sK2),sK2,sK2)
    | ~ v1_funct_1(k6_partfun1(sK2))
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f2173,f84])).

fof(f2173,plain,
    ( ~ r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,k6_partfun1(sK2),sK3),k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v1_funct_2(sK4,sK2,sK2)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(k6_partfun1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v1_funct_2(k6_partfun1(sK2),sK2,sK2)
    | ~ v1_funct_1(k6_partfun1(sK2))
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f1555,f308])).

fof(f308,plain,(
    ~ r2_relset_1(sK2,sK2,k6_partfun1(sK2),sK4) ),
    inference(subsumption_resolution,[],[f307,f93])).

fof(f307,plain,
    ( ~ r2_relset_1(sK2,sK2,k6_partfun1(sK2),sK4)
    | ~ m1_subset_1(k6_partfun1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(subsumption_resolution,[],[f303,f84])).

fof(f303,plain,
    ( ~ r2_relset_1(sK2,sK2,k6_partfun1(sK2),sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ m1_subset_1(k6_partfun1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(resolution,[],[f136,f87])).

fof(f87,plain,(
    ~ r2_relset_1(sK2,sK2,sK4,k6_partfun1(sK2)) ),
    inference(cnf_transformation,[],[f64])).

fof(f136,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X2)
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X3,X2)
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X3,X2)
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
       => r2_relset_1(X0,X1,X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r2_relset_1)).

fof(f1555,plain,(
    ! [X6,X4,X5] :
      ( r2_relset_1(X4,sK2,X5,X6)
      | ~ r2_relset_1(X4,sK2,k1_partfun1(X4,sK2,sK2,sK2,X5,sK3),k1_partfun1(X4,sK2,sK2,sK2,X6,sK3))
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,sK2)))
      | ~ v1_funct_2(X6,X4,sK2)
      | ~ v1_funct_1(X6)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,sK2)))
      | ~ v1_funct_2(X5,X4,sK2)
      | ~ v1_funct_1(X5)
      | k1_xboole_0 = sK2 ) ),
    inference(subsumption_resolution,[],[f1543,f81])).

fof(f1543,plain,(
    ! [X6,X4,X5] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
      | k1_xboole_0 = sK2
      | ~ r2_relset_1(X4,sK2,k1_partfun1(X4,sK2,sK2,sK2,X5,sK3),k1_partfun1(X4,sK2,sK2,sK2,X6,sK3))
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,sK2)))
      | ~ v1_funct_2(X6,X4,sK2)
      | ~ v1_funct_1(X6)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,sK2)))
      | ~ v1_funct_2(X5,X4,sK2)
      | ~ v1_funct_1(X5)
      | r2_relset_1(X4,sK2,X5,X6) ) ),
    inference(duplicate_literal_removal,[],[f1541])).

fof(f1541,plain,(
    ! [X6,X4,X5] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK2
      | ~ r2_relset_1(X4,sK2,k1_partfun1(X4,sK2,sK2,sK2,X5,sK3),k1_partfun1(X4,sK2,sK2,sK2,X6,sK3))
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,sK2)))
      | ~ v1_funct_2(X6,X4,sK2)
      | ~ v1_funct_1(X6)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,sK2)))
      | ~ v1_funct_2(X5,X4,sK2)
      | ~ v1_funct_1(X5)
      | r2_relset_1(X4,sK2,X5,X6) ) ),
    inference(resolution,[],[f960,f80])).

fof(f960,plain,(
    ! [X23,X21,X19,X22,X20] :
      ( ~ v1_funct_2(sK3,X19,X20)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))
      | k1_xboole_0 = X19
      | k1_xboole_0 = X20
      | ~ r2_relset_1(X21,X20,k1_partfun1(X21,X19,X19,X20,X22,sK3),k1_partfun1(X21,X19,X19,X20,X23,sK3))
      | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X19)))
      | ~ v1_funct_2(X23,X21,X19)
      | ~ v1_funct_1(X23)
      | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X21,X19)))
      | ~ v1_funct_2(X22,X21,X19)
      | ~ v1_funct_1(X22)
      | r2_relset_1(X21,X19,X22,X23) ) ),
    inference(subsumption_resolution,[],[f959,f79])).

fof(f959,plain,(
    ! [X23,X21,X19,X22,X20] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))
      | ~ v1_funct_2(sK3,X19,X20)
      | ~ v1_funct_1(sK3)
      | k1_xboole_0 = X19
      | k1_xboole_0 = X20
      | ~ r2_relset_1(X21,X20,k1_partfun1(X21,X19,X19,X20,X22,sK3),k1_partfun1(X21,X19,X19,X20,X23,sK3))
      | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X19)))
      | ~ v1_funct_2(X23,X21,X19)
      | ~ v1_funct_1(X23)
      | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X21,X19)))
      | ~ v1_funct_2(X22,X21,X19)
      | ~ v1_funct_1(X22)
      | r2_relset_1(X21,X19,X22,X23) ) ),
    inference(resolution,[],[f481,f86])).

fof(f481,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
      | ~ v1_funct_2(X1,X0,X2)
      | ~ v1_funct_1(X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2
      | ~ r2_relset_1(X3,X2,k1_partfun1(X3,X0,X0,X2,X4,X1),k1_partfun1(X3,X0,X0,X2,X5,X1))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0)))
      | ~ v1_funct_2(X5,X3,X0)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X0)))
      | ~ v1_funct_2(X4,X3,X0)
      | ~ v1_funct_1(X4)
      | r2_relset_1(X3,X0,X4,X5) ) ),
    inference(resolution,[],[f300,f126])).

fof(f126,plain,(
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
    inference(cnf_transformation,[],[f77])).

fof(f77,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f74,f76,f75])).

fof(f75,plain,(
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

fof(f76,plain,(
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

fof(f74,plain,(
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
    inference(rectify,[],[f73])).

fof(f73,plain,(
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
    inference(nnf_transformation,[],[f59])).

fof(f59,plain,(
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

fof(f300,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X2,X0)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X2,X1,X0)
      | ~ v1_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f135,f124])).

fof(f124,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ v2_funct_1(X1)
      | sP0(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,(
    ! [X0,X1,X2] :
      ( ( ( v2_funct_1(X1)
          | ~ sP0(X2,X1,X0) )
        & ( sP0(X2,X1,X0)
          | ~ v2_funct_1(X1) ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f71])).

fof(f71,plain,(
    ! [X1,X2,X0] :
      ( ( ( v2_funct_1(X2)
          | ~ sP0(X0,X2,X1) )
        & ( sP0(X0,X2,X1)
          | ~ v2_funct_1(X2) ) )
      | ~ sP1(X1,X2,X0) ) ),
    inference(nnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X1,X2,X0] :
      ( ( v2_funct_1(X2)
      <=> sP0(X0,X2,X1) )
      | ~ sP1(X1,X2,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f135,plain,(
    ! [X2,X0,X1] :
      ( sP1(X1,X2,X0)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1,X2] :
      ( sP1(X1,X2,X0)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(definition_folding,[],[f48,f60,f59])).

fof(f48,plain,(
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
    inference(flattening,[],[f47])).

fof(f47,plain,(
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
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
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

fof(f2788,plain,(
    v1_funct_2(k6_partfun1(sK2),sK2,sK2) ),
    inference(resolution,[],[f2767,f149])).

fof(f2767,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK2,X0)
      | v1_funct_2(k6_partfun1(sK2),sK2,X0) ) ),
    inference(resolution,[],[f2757,f189])).

fof(f189,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(k6_partfun1(X0))
      | v1_funct_2(k6_partfun1(X0),X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(forward_demodulation,[],[f188,f145])).

fof(f188,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k6_partfun1(X0),X0,X1)
      | ~ r1_tarski(k2_relat_1(k6_partfun1(X0)),X1)
      | ~ v1_funct_1(k6_partfun1(X0)) ) ),
    inference(subsumption_resolution,[],[f187,f144])).

fof(f144,plain,(
    ! [X0] : v1_relat_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f90,f89])).

fof(f90,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f187,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k6_partfun1(X0),X0,X1)
      | ~ r1_tarski(k2_relat_1(k6_partfun1(X0)),X1)
      | ~ v1_funct_1(k6_partfun1(X0))
      | ~ v1_relat_1(k6_partfun1(X0)) ) ),
    inference(superposition,[],[f102,f146])).

fof(f146,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f94,f89])).

fof(f94,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f3150,plain,
    ( k1_xboole_0 = sK4
    | ~ r1_tarski(k2_zfmisc_1(sK2,sK2),sK4) ),
    inference(forward_demodulation,[],[f2849,f151])).

fof(f2849,plain,
    ( sK4 = k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
    | ~ r1_tarski(k2_zfmisc_1(sK2,sK2),sK4) ),
    inference(backward_demodulation,[],[f391,f2839])).

fof(f391,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK2,sK2),sK4)
    | k2_zfmisc_1(sK2,sK2) = sK4 ),
    inference(resolution,[],[f377,f109])).

fof(f109,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f377,plain,
    ( ~ m1_subset_1(k2_zfmisc_1(sK2,sK2),k1_zfmisc_1(sK4))
    | k2_zfmisc_1(sK2,sK2) = sK4 ),
    inference(resolution,[],[f196,f84])).

fof(f196,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X1))
      | X1 = X2
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ) ),
    inference(resolution,[],[f162,f108])).

fof(f108,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f162,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X1,X2)
      | X1 = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ) ),
    inference(resolution,[],[f107,f108])).

fof(f107,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f2941,plain,(
    ~ r2_relset_1(k1_xboole_0,k1_xboole_0,sK4,k1_xboole_0) ),
    inference(forward_demodulation,[],[f2844,f170])).

fof(f2844,plain,(
    ~ r2_relset_1(k1_xboole_0,k1_xboole_0,sK4,k6_partfun1(k1_xboole_0)) ),
    inference(backward_demodulation,[],[f87,f2839])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:49:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.36  ipcrm: permission denied for id (739803137)
% 0.13/0.36  ipcrm: permission denied for id (741376002)
% 0.13/0.37  ipcrm: permission denied for id (745013251)
% 0.13/0.37  ipcrm: permission denied for id (741441540)
% 0.13/0.37  ipcrm: permission denied for id (739868677)
% 0.13/0.37  ipcrm: permission denied for id (745078791)
% 0.13/0.37  ipcrm: permission denied for id (745111560)
% 0.13/0.37  ipcrm: permission denied for id (745177098)
% 0.13/0.38  ipcrm: permission denied for id (745209867)
% 0.13/0.38  ipcrm: permission denied for id (741670924)
% 0.13/0.38  ipcrm: permission denied for id (739966990)
% 0.13/0.38  ipcrm: permission denied for id (745275407)
% 0.13/0.38  ipcrm: permission denied for id (741769232)
% 0.13/0.38  ipcrm: permission denied for id (741834769)
% 0.13/0.39  ipcrm: permission denied for id (745340947)
% 0.13/0.39  ipcrm: permission denied for id (739999764)
% 0.13/0.39  ipcrm: permission denied for id (741933077)
% 0.13/0.39  ipcrm: permission denied for id (745373718)
% 0.13/0.39  ipcrm: permission denied for id (741998615)
% 0.13/0.39  ipcrm: permission denied for id (742031384)
% 0.13/0.39  ipcrm: permission denied for id (740065305)
% 0.13/0.40  ipcrm: permission denied for id (745439259)
% 0.13/0.40  ipcrm: permission denied for id (742129692)
% 0.13/0.40  ipcrm: permission denied for id (745472029)
% 0.13/0.40  ipcrm: permission denied for id (742195230)
% 0.13/0.40  ipcrm: permission denied for id (745504799)
% 0.13/0.40  ipcrm: permission denied for id (742326306)
% 0.13/0.41  ipcrm: permission denied for id (745701414)
% 0.21/0.41  ipcrm: permission denied for id (745734183)
% 0.21/0.41  ipcrm: permission denied for id (745766952)
% 0.21/0.41  ipcrm: permission denied for id (742555689)
% 0.21/0.41  ipcrm: permission denied for id (742588458)
% 0.21/0.42  ipcrm: permission denied for id (740294699)
% 0.21/0.42  ipcrm: permission denied for id (745799724)
% 0.21/0.42  ipcrm: permission denied for id (745865262)
% 0.21/0.42  ipcrm: permission denied for id (742752304)
% 0.21/0.42  ipcrm: permission denied for id (742817842)
% 0.21/0.43  ipcrm: permission denied for id (742850611)
% 0.21/0.43  ipcrm: permission denied for id (742883380)
% 0.21/0.43  ipcrm: permission denied for id (745963573)
% 0.21/0.43  ipcrm: permission denied for id (742948918)
% 0.21/0.43  ipcrm: permission denied for id (745996343)
% 0.21/0.43  ipcrm: permission denied for id (740425785)
% 0.21/0.43  ipcrm: permission denied for id (743047226)
% 0.21/0.44  ipcrm: permission denied for id (740458555)
% 0.21/0.44  ipcrm: permission denied for id (743079996)
% 0.21/0.44  ipcrm: permission denied for id (746127423)
% 0.21/0.44  ipcrm: permission denied for id (743211072)
% 0.21/0.44  ipcrm: permission denied for id (743243841)
% 0.21/0.44  ipcrm: permission denied for id (746160194)
% 0.21/0.45  ipcrm: permission denied for id (740556868)
% 0.21/0.45  ipcrm: permission denied for id (743342149)
% 0.21/0.45  ipcrm: permission denied for id (746225734)
% 0.21/0.45  ipcrm: permission denied for id (743407687)
% 0.21/0.45  ipcrm: permission denied for id (740589640)
% 0.21/0.45  ipcrm: permission denied for id (743440457)
% 0.21/0.46  ipcrm: permission denied for id (746291275)
% 0.21/0.46  ipcrm: permission denied for id (743571533)
% 0.21/0.46  ipcrm: permission denied for id (746356814)
% 0.21/0.46  ipcrm: permission denied for id (743637071)
% 0.21/0.46  ipcrm: permission denied for id (743702609)
% 0.21/0.46  ipcrm: permission denied for id (746422354)
% 0.21/0.47  ipcrm: permission denied for id (743768147)
% 0.21/0.47  ipcrm: permission denied for id (746455124)
% 0.21/0.47  ipcrm: permission denied for id (746487893)
% 0.21/0.47  ipcrm: permission denied for id (743931992)
% 0.21/0.47  ipcrm: permission denied for id (743997530)
% 0.21/0.47  ipcrm: permission denied for id (744030299)
% 0.21/0.48  ipcrm: permission denied for id (744063068)
% 0.21/0.48  ipcrm: permission denied for id (746684511)
% 0.21/0.48  ipcrm: permission denied for id (744194144)
% 0.21/0.48  ipcrm: permission denied for id (744226913)
% 0.21/0.48  ipcrm: permission denied for id (746750051)
% 0.21/0.49  ipcrm: permission denied for id (744325220)
% 0.21/0.49  ipcrm: permission denied for id (744390757)
% 0.21/0.49  ipcrm: permission denied for id (740819047)
% 0.21/0.49  ipcrm: permission denied for id (740851816)
% 0.21/0.49  ipcrm: permission denied for id (744456297)
% 0.21/0.49  ipcrm: permission denied for id (744489066)
% 0.21/0.50  ipcrm: permission denied for id (740917355)
% 0.21/0.50  ipcrm: permission denied for id (740950124)
% 0.21/0.50  ipcrm: permission denied for id (744521837)
% 0.21/0.50  ipcrm: permission denied for id (744554606)
% 0.21/0.50  ipcrm: permission denied for id (744587375)
% 0.21/0.50  ipcrm: permission denied for id (744620144)
% 0.21/0.50  ipcrm: permission denied for id (746815601)
% 0.21/0.51  ipcrm: permission denied for id (740982899)
% 0.21/0.51  ipcrm: permission denied for id (744783989)
% 0.21/0.51  ipcrm: permission denied for id (741048440)
% 0.21/0.51  ipcrm: permission denied for id (744915066)
% 0.21/0.51  ipcrm: permission denied for id (741146747)
% 0.21/0.52  ipcrm: permission denied for id (741212284)
% 0.21/0.52  ipcrm: permission denied for id (741245053)
% 0.21/0.52  ipcrm: permission denied for id (741277822)
% 1.23/0.67  % (13173)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.23/0.68  % (13181)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.23/0.68  % (13179)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.23/0.68  % (13187)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.23/0.68  % (13197)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.23/0.68  % (13189)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.23/0.69  % (13185)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.23/0.69  % (13195)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.23/0.69  % (13177)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.23/0.70  % (13185)Refutation not found, incomplete strategy% (13185)------------------------------
% 1.23/0.70  % (13185)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.23/0.70  % (13169)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.23/0.70  % (13192)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.23/0.70  % (13171)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.23/0.70  % (13174)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.23/0.70  % (13182)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.23/0.71  % (13191)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.23/0.71  % (13185)Termination reason: Refutation not found, incomplete strategy
% 1.23/0.71  
% 1.23/0.71  % (13185)Memory used [KB]: 10874
% 1.23/0.71  % (13185)Time elapsed: 0.122 s
% 1.23/0.71  % (13185)------------------------------
% 1.23/0.71  % (13185)------------------------------
% 1.23/0.71  % (13180)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.23/0.71  % (13170)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.23/0.71  % (13175)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.23/0.71  % (13183)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.23/0.71  % (13178)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.23/0.71  % (13184)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.23/0.72  % (13190)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.23/0.72  % (13188)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.23/0.72  % (13172)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.23/0.72  % (13176)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.23/0.72  % (13198)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.23/0.72  % (13193)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.23/0.72  % (13196)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.23/0.73  % (13186)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.79/0.74  % (13194)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 2.79/0.87  % (13224)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.79/0.92  % (13169)Refutation not found, incomplete strategy% (13169)------------------------------
% 2.79/0.92  % (13169)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.25/0.94  % (13169)Termination reason: Refutation not found, incomplete strategy
% 3.25/0.94  
% 3.25/0.94  % (13169)Memory used [KB]: 1918
% 3.25/0.94  % (13169)Time elapsed: 0.341 s
% 3.25/0.94  % (13169)------------------------------
% 3.25/0.94  % (13169)------------------------------
% 3.51/1.02  % (13193)Time limit reached!
% 3.51/1.02  % (13193)------------------------------
% 3.51/1.02  % (13193)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.51/1.02  % (13193)Termination reason: Time limit
% 3.51/1.02  
% 3.51/1.02  % (13193)Memory used [KB]: 13048
% 3.51/1.02  % (13193)Time elapsed: 0.408 s
% 3.51/1.02  % (13193)------------------------------
% 3.51/1.02  % (13193)------------------------------
% 3.51/1.03  % (13171)Time limit reached!
% 3.51/1.03  % (13171)------------------------------
% 3.51/1.03  % (13171)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.51/1.03  % (13171)Termination reason: Time limit
% 3.51/1.03  
% 3.51/1.03  % (13171)Memory used [KB]: 6780
% 3.51/1.03  % (13171)Time elapsed: 0.429 s
% 3.51/1.03  % (13171)------------------------------
% 3.51/1.03  % (13171)------------------------------
% 4.30/1.07  % (13344)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 4.30/1.11  % (13198)Time limit reached!
% 4.30/1.11  % (13198)------------------------------
% 4.30/1.11  % (13198)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.30/1.11  % (13198)Termination reason: Time limit
% 4.30/1.11  
% 4.30/1.11  % (13198)Memory used [KB]: 4093
% 4.30/1.11  % (13198)Time elapsed: 0.530 s
% 4.30/1.11  % (13198)------------------------------
% 4.30/1.11  % (13198)------------------------------
% 4.30/1.12  % (13175)Time limit reached!
% 4.30/1.12  % (13175)------------------------------
% 4.30/1.12  % (13175)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.30/1.12  % (13175)Termination reason: Time limit
% 4.30/1.12  
% 4.30/1.12  % (13175)Memory used [KB]: 14456
% 4.30/1.12  % (13175)Time elapsed: 0.502 s
% 4.30/1.12  % (13175)------------------------------
% 4.30/1.12  % (13175)------------------------------
% 4.30/1.14  % (13183)Time limit reached!
% 4.30/1.14  % (13183)------------------------------
% 4.30/1.14  % (13183)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.30/1.14  % (13183)Termination reason: Time limit
% 4.30/1.14  
% 4.30/1.14  % (13183)Memory used [KB]: 5500
% 4.30/1.14  % (13183)Time elapsed: 0.519 s
% 4.30/1.14  % (13183)------------------------------
% 4.30/1.14  % (13183)------------------------------
% 5.01/1.16  % (13363)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 5.01/1.17  % (13362)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 5.26/1.20  % (13176)Time limit reached!
% 5.26/1.20  % (13176)------------------------------
% 5.26/1.20  % (13176)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.26/1.20  % (13176)Termination reason: Time limit
% 5.26/1.20  
% 5.26/1.20  % (13176)Memory used [KB]: 6140
% 5.26/1.20  % (13176)Time elapsed: 0.628 s
% 5.26/1.20  % (13176)------------------------------
% 5.26/1.20  % (13176)------------------------------
% 5.71/1.24  % (13387)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 5.71/1.25  % (13390)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 5.91/1.27  % (13391)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 5.91/1.31  % (13179)Refutation not found, incomplete strategy% (13179)------------------------------
% 5.91/1.31  % (13179)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.91/1.31  % (13179)Termination reason: Refutation not found, incomplete strategy
% 5.91/1.31  
% 5.91/1.31  % (13179)Memory used [KB]: 14328
% 5.91/1.31  % (13179)Time elapsed: 0.719 s
% 5.91/1.31  % (13179)------------------------------
% 5.91/1.31  % (13179)------------------------------
% 5.91/1.32  % (13399)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 5.91/1.32  % (13191)Refutation found. Thanks to Tanya!
% 5.91/1.32  % SZS status Theorem for theBenchmark
% 5.91/1.32  % SZS output start Proof for theBenchmark
% 5.91/1.32  fof(f3543,plain,(
% 5.91/1.32    $false),
% 5.91/1.32    inference(subsumption_resolution,[],[f3542,f174])).
% 5.91/1.32  fof(f174,plain,(
% 5.91/1.32    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 5.91/1.32    inference(backward_demodulation,[],[f155,f170])).
% 5.91/1.32  fof(f170,plain,(
% 5.91/1.32    k1_xboole_0 = k6_partfun1(k1_xboole_0)),
% 5.91/1.32    inference(resolution,[],[f167,f157])).
% 5.91/1.32  fof(f157,plain,(
% 5.91/1.32    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 5.91/1.32    inference(resolution,[],[f113,f88])).
% 5.91/1.32  fof(f88,plain,(
% 5.91/1.32    v1_xboole_0(k1_xboole_0)),
% 5.91/1.32    inference(cnf_transformation,[],[f1])).
% 5.91/1.32  fof(f1,axiom,(
% 5.91/1.32    v1_xboole_0(k1_xboole_0)),
% 5.91/1.32    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 5.91/1.32  fof(f113,plain,(
% 5.91/1.32    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 5.91/1.32    inference(cnf_transformation,[],[f39])).
% 5.91/1.32  fof(f39,plain,(
% 5.91/1.32    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 5.91/1.32    inference(ennf_transformation,[],[f3])).
% 5.91/1.32  fof(f3,axiom,(
% 5.91/1.32    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 5.91/1.32    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).
% 5.91/1.32  fof(f167,plain,(
% 5.91/1.32    v1_xboole_0(k6_partfun1(k1_xboole_0))),
% 5.91/1.32    inference(resolution,[],[f166,f155])).
% 5.91/1.32  fof(f166,plain,(
% 5.91/1.32    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | v1_xboole_0(X0)) )),
% 5.91/1.32    inference(forward_demodulation,[],[f165,f151])).
% 5.91/1.32  fof(f151,plain,(
% 5.91/1.32    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 5.91/1.32    inference(equality_resolution,[],[f112])).
% 5.91/1.32  fof(f112,plain,(
% 5.91/1.32    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 5.91/1.32    inference(cnf_transformation,[],[f70])).
% 5.91/1.32  fof(f70,plain,(
% 5.91/1.32    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 5.91/1.32    inference(flattening,[],[f69])).
% 5.91/1.32  fof(f69,plain,(
% 5.91/1.32    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 5.91/1.32    inference(nnf_transformation,[],[f4])).
% 5.91/1.32  fof(f4,axiom,(
% 5.91/1.32    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 5.91/1.32    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 5.91/1.32  fof(f165,plain,(
% 5.91/1.32    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) | v1_xboole_0(X0)) )),
% 5.91/1.32    inference(resolution,[],[f100,f88])).
% 5.91/1.32  fof(f100,plain,(
% 5.91/1.32    ( ! [X2,X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | v1_xboole_0(X2)) )),
% 5.91/1.32    inference(cnf_transformation,[],[f34])).
% 5.91/1.32  fof(f34,plain,(
% 5.91/1.32    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 5.91/1.32    inference(ennf_transformation,[],[f12])).
% 5.91/1.32  fof(f12,axiom,(
% 5.91/1.32    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 5.91/1.32    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).
% 5.91/1.32  fof(f155,plain,(
% 5.91/1.32    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))),
% 5.91/1.32    inference(superposition,[],[f93,f151])).
% 5.91/1.32  fof(f93,plain,(
% 5.91/1.32    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 5.91/1.32    inference(cnf_transformation,[],[f19])).
% 5.91/1.32  fof(f19,axiom,(
% 5.91/1.32    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 5.91/1.32    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 5.91/1.32  fof(f3542,plain,(
% 5.91/1.32    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 5.91/1.32    inference(forward_demodulation,[],[f3529,f151])).
% 5.91/1.32  fof(f3529,plain,(
% 5.91/1.32    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 5.91/1.32    inference(resolution,[],[f3179,f154])).
% 5.91/1.32  fof(f154,plain,(
% 5.91/1.32    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 5.91/1.32    inference(duplicate_literal_removal,[],[f153])).
% 5.91/1.32  fof(f153,plain,(
% 5.91/1.32    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 5.91/1.32    inference(equality_resolution,[],[f138])).
% 5.91/1.32  fof(f138,plain,(
% 5.91/1.32    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 5.91/1.32    inference(cnf_transformation,[],[f78])).
% 5.91/1.32  fof(f78,plain,(
% 5.91/1.32    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 5.91/1.32    inference(nnf_transformation,[],[f52])).
% 5.91/1.32  fof(f52,plain,(
% 5.91/1.32    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 5.91/1.32    inference(flattening,[],[f51])).
% 5.91/1.32  fof(f51,plain,(
% 5.91/1.32    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 5.91/1.32    inference(ennf_transformation,[],[f16])).
% 5.91/1.32  fof(f16,axiom,(
% 5.91/1.32    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 5.91/1.32    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 5.91/1.32  fof(f3179,plain,(
% 5.91/1.32    ~r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 5.91/1.32    inference(backward_demodulation,[],[f2941,f3153])).
% 5.91/1.32  fof(f3153,plain,(
% 5.91/1.32    k1_xboole_0 = sK4),
% 5.91/1.32    inference(subsumption_resolution,[],[f3152,f232])).
% 5.91/1.32  fof(f232,plain,(
% 5.91/1.32    ( ! [X1] : (r1_tarski(k1_xboole_0,X1)) )),
% 5.91/1.32    inference(subsumption_resolution,[],[f231,f174])).
% 6.31/1.32  fof(f231,plain,(
% 6.31/1.32    ( ! [X1] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | r1_tarski(k1_xboole_0,X1)) )),
% 6.31/1.32    inference(superposition,[],[f201,f152])).
% 6.31/1.33  fof(f152,plain,(
% 6.31/1.33    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 6.31/1.33    inference(equality_resolution,[],[f111])).
% 6.31/1.33  fof(f111,plain,(
% 6.31/1.33    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 6.31/1.33    inference(cnf_transformation,[],[f70])).
% 6.31/1.33  fof(f201,plain,(
% 6.31/1.33    ( ! [X4,X3] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X4,X3))) | r1_tarski(k1_xboole_0,X3)) )),
% 6.31/1.33    inference(superposition,[],[f164,f182])).
% 6.31/1.33  fof(f182,plain,(
% 6.31/1.33    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 6.31/1.33    inference(superposition,[],[f145,f170])).
% 6.31/1.33  fof(f145,plain,(
% 6.31/1.33    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 6.31/1.33    inference(definition_unfolding,[],[f95,f89])).
% 6.31/1.33  fof(f89,plain,(
% 6.31/1.33    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 6.31/1.33    inference(cnf_transformation,[],[f21])).
% 6.31/1.33  fof(f21,axiom,(
% 6.31/1.33    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 6.31/1.33    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 6.31/1.33  fof(f95,plain,(
% 6.31/1.33    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 6.31/1.33    inference(cnf_transformation,[],[f7])).
% 6.31/1.33  fof(f7,axiom,(
% 6.31/1.33    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 6.31/1.33    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 6.31/1.33  fof(f164,plain,(
% 6.31/1.33    ( ! [X2,X0,X1] : (r1_tarski(k2_relat_1(X0),X2) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 6.31/1.33    inference(subsumption_resolution,[],[f163,f114])).
% 6.31/1.33  fof(f114,plain,(
% 6.31/1.33    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.31/1.33    inference(cnf_transformation,[],[f40])).
% 6.31/1.33  fof(f40,plain,(
% 6.31/1.33    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.31/1.33    inference(ennf_transformation,[],[f10])).
% 6.31/1.33  fof(f10,axiom,(
% 6.31/1.33    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 6.31/1.33    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 6.31/1.33  fof(f163,plain,(
% 6.31/1.33    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | r1_tarski(k2_relat_1(X0),X2) | ~v1_relat_1(X0)) )),
% 6.31/1.33    inference(resolution,[],[f118,f98])).
% 6.31/1.33  fof(f98,plain,(
% 6.31/1.33    ( ! [X0,X1] : (~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 6.31/1.33    inference(cnf_transformation,[],[f65])).
% 6.31/1.33  fof(f65,plain,(
% 6.31/1.33    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 6.31/1.33    inference(nnf_transformation,[],[f33])).
% 6.31/1.33  fof(f33,plain,(
% 6.31/1.33    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 6.31/1.33    inference(ennf_transformation,[],[f6])).
% 6.31/1.33  fof(f6,axiom,(
% 6.31/1.33    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 6.31/1.33    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 6.31/1.33  fof(f118,plain,(
% 6.31/1.33    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.31/1.33    inference(cnf_transformation,[],[f43])).
% 6.31/1.33  fof(f43,plain,(
% 6.31/1.33    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.31/1.33    inference(ennf_transformation,[],[f11])).
% 6.31/1.33  fof(f11,axiom,(
% 6.31/1.33    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 6.31/1.33    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 6.31/1.33  fof(f3152,plain,(
% 6.31/1.33    ~r1_tarski(k1_xboole_0,sK4) | k1_xboole_0 = sK4),
% 6.31/1.33    inference(forward_demodulation,[],[f3151,f151])).
% 6.31/1.33  fof(f3151,plain,(
% 6.31/1.33    ~r1_tarski(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),sK4) | k1_xboole_0 = sK4),
% 6.31/1.33    inference(forward_demodulation,[],[f3150,f2839])).
% 6.31/1.33  fof(f2839,plain,(
% 6.31/1.33    k1_xboole_0 = sK2),
% 6.31/1.33    inference(subsumption_resolution,[],[f2831,f81])).
% 6.31/1.33  fof(f81,plain,(
% 6.31/1.33    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))),
% 6.31/1.33    inference(cnf_transformation,[],[f64])).
% 6.31/1.33  fof(f64,plain,(
% 6.31/1.33    (~r2_relset_1(sK2,sK2,sK4,k6_partfun1(sK2)) & v2_funct_1(sK3) & r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3),sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v1_funct_2(sK4,sK2,sK2) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v1_funct_2(sK3,sK2,sK2) & v1_funct_1(sK3)),
% 6.31/1.33    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f30,f63,f62])).
% 6.31/1.33  fof(f62,plain,(
% 6.31/1.33    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k6_partfun1(X0)) & v2_funct_1(X1) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (? [X2] : (~r2_relset_1(sK2,sK2,X2,k6_partfun1(sK2)) & v2_funct_1(sK3) & r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,X2,sK3),sK3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v1_funct_2(X2,sK2,sK2) & v1_funct_1(X2)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v1_funct_2(sK3,sK2,sK2) & v1_funct_1(sK3))),
% 6.31/1.33    introduced(choice_axiom,[])).
% 6.31/1.33  fof(f63,plain,(
% 6.31/1.33    ? [X2] : (~r2_relset_1(sK2,sK2,X2,k6_partfun1(sK2)) & v2_funct_1(sK3) & r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,X2,sK3),sK3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v1_funct_2(X2,sK2,sK2) & v1_funct_1(X2)) => (~r2_relset_1(sK2,sK2,sK4,k6_partfun1(sK2)) & v2_funct_1(sK3) & r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3),sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v1_funct_2(sK4,sK2,sK2) & v1_funct_1(sK4))),
% 6.31/1.33    introduced(choice_axiom,[])).
% 6.31/1.33  fof(f30,plain,(
% 6.31/1.33    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k6_partfun1(X0)) & v2_funct_1(X1) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 6.31/1.33    inference(flattening,[],[f29])).
% 6.31/1.33  fof(f29,plain,(
% 6.31/1.33    ? [X0,X1] : (? [X2] : ((~r2_relset_1(X0,X0,X2,k6_partfun1(X0)) & (v2_funct_1(X1) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 6.31/1.33    inference(ennf_transformation,[],[f28])).
% 6.31/1.33  fof(f28,negated_conjecture,(
% 6.31/1.33    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => ((v2_funct_1(X1) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1)) => r2_relset_1(X0,X0,X2,k6_partfun1(X0)))))),
% 6.31/1.33    inference(negated_conjecture,[],[f27])).
% 6.31/1.33  fof(f27,conjecture,(
% 6.31/1.33    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => ((v2_funct_1(X1) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1)) => r2_relset_1(X0,X0,X2,k6_partfun1(X0)))))),
% 6.31/1.33    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_funct_2)).
% 6.31/1.33  fof(f2831,plain,(
% 6.31/1.33    k1_xboole_0 = sK2 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))),
% 6.31/1.33    inference(resolution,[],[f2824,f323])).
% 6.31/1.33  fof(f323,plain,(
% 6.31/1.33    ( ! [X2,X0,X1] : (r2_relset_1(X0,X1,k5_relat_1(k6_partfun1(X0),X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.31/1.33    inference(subsumption_resolution,[],[f322,f93])).
% 6.31/1.33  fof(f322,plain,(
% 6.31/1.33    ( ! [X2,X0,X1] : (r2_relset_1(X0,X1,k5_relat_1(k6_partfun1(X0),X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 6.31/1.33    inference(duplicate_literal_removal,[],[f319])).
% 6.31/1.33  fof(f319,plain,(
% 6.31/1.33    ( ! [X2,X0,X1] : (r2_relset_1(X0,X1,k5_relat_1(k6_partfun1(X0),X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 6.31/1.33    inference(superposition,[],[f119,f142])).
% 6.31/1.33  fof(f142,plain,(
% 6.31/1.33    ( ! [X4,X2,X0,X5,X3,X1] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.31/1.33    inference(cnf_transformation,[],[f58])).
% 6.31/1.33  fof(f58,plain,(
% 6.31/1.33    ! [X0,X1,X2,X3,X4,X5] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.31/1.33    inference(flattening,[],[f57])).
% 6.31/1.33  fof(f57,plain,(
% 6.31/1.33    ! [X0,X1,X2,X3,X4,X5] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 6.31/1.33    inference(ennf_transformation,[],[f15])).
% 6.31/1.33  fof(f15,axiom,(
% 6.31/1.33    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 6.31/1.33    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_relset_1)).
% 6.31/1.33  fof(f119,plain,(
% 6.31/1.33    ( ! [X2,X0,X1] : (r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.31/1.33    inference(cnf_transformation,[],[f44])).
% 6.31/1.33  fof(f44,plain,(
% 6.31/1.33    ! [X0,X1,X2] : ((r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2) & r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.31/1.33    inference(ennf_transformation,[],[f22])).
% 6.31/1.33  fof(f22,axiom,(
% 6.31/1.33    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2) & r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2)))),
% 6.31/1.33    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_2)).
% 6.31/1.33  fof(f2824,plain,(
% 6.31/1.33    ~r2_relset_1(sK2,sK2,k5_relat_1(k6_partfun1(sK2),sK3),sK3) | k1_xboole_0 = sK2),
% 6.31/1.33    inference(subsumption_resolution,[],[f2823,f2757])).
% 6.31/1.33  fof(f2757,plain,(
% 6.31/1.33    v1_funct_1(k6_partfun1(sK2))),
% 6.31/1.33    inference(resolution,[],[f2747,f81])).
% 6.31/1.33  fof(f2747,plain,(
% 6.31/1.33    ( ! [X6,X7] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) | v1_funct_1(k6_partfun1(sK2))) )),
% 6.31/1.33    inference(resolution,[],[f2741,f81])).
% 6.31/1.33  fof(f2741,plain,(
% 6.31/1.33    ( ! [X10,X8,X11,X9] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X8,X9))) | v1_funct_1(k6_partfun1(sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))) )),
% 6.31/1.33    inference(resolution,[],[f2730,f81])).
% 6.31/1.33  fof(f2730,plain,(
% 6.31/1.33    ( ! [X12,X10,X8,X13,X11,X9] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X12,X13))) | v1_funct_1(k6_partfun1(sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X10,X11))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))) )),
% 6.31/1.33    inference(trivial_inequality_removal,[],[f2728])).
% 6.31/1.33  fof(f2728,plain,(
% 6.31/1.33    ( ! [X12,X10,X8,X13,X11,X9] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X8,X9))) | v1_funct_1(k6_partfun1(sK2)) | k2_relat_1(sK3) != k2_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X10,X11))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X12,X13)))) )),
% 6.31/1.33    inference(resolution,[],[f2689,f149])).
% 6.31/1.33  fof(f149,plain,(
% 6.31/1.33    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 6.31/1.33    inference(equality_resolution,[],[f106])).
% 6.31/1.33  fof(f106,plain,(
% 6.31/1.33    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 6.31/1.33    inference(cnf_transformation,[],[f67])).
% 6.31/1.33  fof(f67,plain,(
% 6.31/1.33    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 6.31/1.33    inference(flattening,[],[f66])).
% 6.31/1.33  fof(f66,plain,(
% 6.31/1.33    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 6.31/1.33    inference(nnf_transformation,[],[f2])).
% 6.31/1.33  fof(f2,axiom,(
% 6.31/1.33    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 6.31/1.33    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 6.31/1.33  fof(f2689,plain,(
% 6.31/1.33    ( ! [X6,X4,X10,X8,X7,X5,X9] : (~r1_tarski(k2_relat_1(sK3),X8) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) | v1_funct_1(k6_partfun1(sK2)) | k2_relat_1(sK3) != X8 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))) )),
% 6.31/1.33    inference(resolution,[],[f2685,f454])).
% 6.31/1.33  fof(f454,plain,(
% 6.31/1.33    ( ! [X17,X15,X16] : (m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,X15))) | ~r1_tarski(k2_relat_1(sK3),X15) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X16,X17)))) )),
% 6.31/1.33    inference(forward_demodulation,[],[f450,f439])).
% 6.31/1.33  fof(f439,plain,(
% 6.31/1.33    sK2 = k1_relat_1(sK3)),
% 6.31/1.33    inference(subsumption_resolution,[],[f438,f79])).
% 6.31/1.33  fof(f79,plain,(
% 6.31/1.33    v1_funct_1(sK3)),
% 6.31/1.33    inference(cnf_transformation,[],[f64])).
% 6.31/1.33  fof(f438,plain,(
% 6.31/1.33    sK2 = k1_relat_1(sK3) | ~v1_funct_1(sK3)),
% 6.31/1.33    inference(subsumption_resolution,[],[f433,f81])).
% 6.31/1.33  fof(f433,plain,(
% 6.31/1.33    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | sK2 = k1_relat_1(sK3) | ~v1_funct_1(sK3)),
% 6.31/1.33    inference(resolution,[],[f251,f80])).
% 6.31/1.33  fof(f80,plain,(
% 6.31/1.33    v1_funct_2(sK3,sK2,sK2)),
% 6.31/1.33    inference(cnf_transformation,[],[f64])).
% 6.31/1.33  fof(f251,plain,(
% 6.31/1.33    ( ! [X0,X1] : (~v1_funct_2(X1,X0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | k1_relat_1(X1) = X0 | ~v1_funct_1(X1)) )),
% 6.31/1.33    inference(duplicate_literal_removal,[],[f248])).
% 6.31/1.33  fof(f248,plain,(
% 6.31/1.33    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 6.31/1.33    inference(superposition,[],[f104,f115])).
% 6.31/1.33  fof(f115,plain,(
% 6.31/1.33    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.31/1.33    inference(cnf_transformation,[],[f41])).
% 6.31/1.33  fof(f41,plain,(
% 6.31/1.33    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.31/1.33    inference(ennf_transformation,[],[f13])).
% 6.31/1.33  fof(f13,axiom,(
% 6.31/1.33    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 6.31/1.33    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 6.31/1.33  fof(f104,plain,(
% 6.31/1.33    ( ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 6.31/1.33    inference(cnf_transformation,[],[f38])).
% 6.31/1.33  fof(f38,plain,(
% 6.31/1.33    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 6.31/1.33    inference(flattening,[],[f37])).
% 6.31/1.33  fof(f37,plain,(
% 6.31/1.33    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 6.31/1.33    inference(ennf_transformation,[],[f26])).
% 6.31/1.33  fof(f26,axiom,(
% 6.31/1.33    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k1_relset_1(X0,X0,X1) = X0)),
% 6.31/1.33    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_2)).
% 6.31/1.33  fof(f450,plain,(
% 6.31/1.33    ( ! [X17,X15,X16] : (~r1_tarski(k2_relat_1(sK3),X15) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X15))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X16,X17)))) )),
% 6.31/1.33    inference(resolution,[],[f222,f79])).
% 6.31/1.33  fof(f222,plain,(
% 6.31/1.33    ( ! [X4,X2,X5,X3] : (~v1_funct_1(X2) | ~r1_tarski(k2_relat_1(X2),X3) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))) )),
% 6.31/1.33    inference(resolution,[],[f103,f114])).
% 6.31/1.33  fof(f103,plain,(
% 6.31/1.33    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))) )),
% 6.31/1.33    inference(cnf_transformation,[],[f36])).
% 6.31/1.33  fof(f36,plain,(
% 6.31/1.33    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 6.31/1.33    inference(flattening,[],[f35])).
% 6.31/1.33  fof(f35,plain,(
% 6.31/1.33    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 6.31/1.33    inference(ennf_transformation,[],[f25])).
% 6.31/1.33  fof(f25,axiom,(
% 6.31/1.33    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 6.31/1.33    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).
% 6.31/1.33  fof(f2685,plain,(
% 6.31/1.33    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,X4))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | v1_funct_1(k6_partfun1(sK2)) | k2_relat_1(sK3) != X4) )),
% 6.31/1.33    inference(forward_demodulation,[],[f2684,f439])).
% 6.31/1.33  fof(f2684,plain,(
% 6.31/1.33    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | v1_funct_1(k6_partfun1(sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X4))) | k2_relat_1(sK3) != X4) )),
% 6.31/1.33    inference(subsumption_resolution,[],[f2683,f114])).
% 6.31/1.33  fof(f2683,plain,(
% 6.31/1.33    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | v1_funct_1(k6_partfun1(sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X4))) | k2_relat_1(sK3) != X4 | ~v1_relat_1(sK3)) )),
% 6.31/1.33    inference(subsumption_resolution,[],[f2682,f164])).
% 6.31/1.33  fof(f2682,plain,(
% 6.31/1.33    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | v1_funct_1(k6_partfun1(sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X4))) | k2_relat_1(sK3) != X4 | ~r1_tarski(k2_relat_1(sK3),X4) | ~v1_relat_1(sK3)) )),
% 6.31/1.33    inference(subsumption_resolution,[],[f2679,f79])).
% 6.31/1.33  fof(f2679,plain,(
% 6.31/1.33    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | v1_funct_1(k6_partfun1(sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X4))) | k2_relat_1(sK3) != X4 | ~r1_tarski(k2_relat_1(sK3),X4) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)) )),
% 6.31/1.33    inference(resolution,[],[f2673,f102])).
% 6.31/1.33  fof(f102,plain,(
% 6.31/1.33    ( ! [X0,X1] : (v1_funct_2(X1,k1_relat_1(X1),X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 6.31/1.33    inference(cnf_transformation,[],[f36])).
% 6.31/1.33  fof(f2673,plain,(
% 6.31/1.33    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_funct_2(sK3,X0,X1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | v1_funct_1(k6_partfun1(sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relat_1(sK3) != X1) )),
% 6.31/1.33    inference(duplicate_literal_removal,[],[f2672])).
% 6.31/1.33  fof(f2672,plain,(
% 6.31/1.33    ( ! [X4,X2,X0,X5,X3,X1] : (k2_relat_1(sK3) != X1 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | v1_funct_1(k6_partfun1(sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK3,X0,X1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.31/1.33    inference(superposition,[],[f2429,f116])).
% 6.31/1.33  fof(f116,plain,(
% 6.31/1.33    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.31/1.33    inference(cnf_transformation,[],[f42])).
% 6.31/1.33  fof(f42,plain,(
% 6.31/1.33    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.31/1.33    inference(ennf_transformation,[],[f14])).
% 6.31/1.33  fof(f14,axiom,(
% 6.31/1.33    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 6.31/1.33    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 6.31/1.33  fof(f2429,plain,(
% 6.31/1.33    ( ! [X4,X2,X0,X5,X3,X1] : (k2_relset_1(X4,X5,sK3) != X5 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | v1_funct_1(k6_partfun1(sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | ~v1_funct_2(sK3,X4,X5)) )),
% 6.31/1.33    inference(subsumption_resolution,[],[f2428,f79])).
% 6.31/1.33  fof(f2428,plain,(
% 6.31/1.33    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k6_partfun1(sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k2_relset_1(X4,X5,sK3) != X5 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | ~v1_funct_2(sK3,X4,X5) | ~v1_funct_1(sK3)) )),
% 6.31/1.33    inference(subsumption_resolution,[],[f2423,f86])).
% 6.31/1.33  fof(f86,plain,(
% 6.31/1.33    v2_funct_1(sK3)),
% 6.31/1.33    inference(cnf_transformation,[],[f64])).
% 6.31/1.33  fof(f2423,plain,(
% 6.31/1.33    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k6_partfun1(sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k2_relset_1(X4,X5,sK3) != X5 | ~v2_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | ~v1_funct_2(sK3,X4,X5) | ~v1_funct_1(sK3)) )),
% 6.31/1.33    inference(resolution,[],[f2422,f123])).
% 6.31/1.33  fof(f123,plain,(
% 6.31/1.33    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 6.31/1.33    inference(cnf_transformation,[],[f46])).
% 6.31/1.33  fof(f46,plain,(
% 6.31/1.33    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 6.31/1.33    inference(flattening,[],[f45])).
% 6.31/1.33  fof(f45,plain,(
% 6.31/1.33    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 6.31/1.33    inference(ennf_transformation,[],[f24])).
% 6.31/1.33  fof(f24,axiom,(
% 6.31/1.33    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 6.31/1.33    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).
% 6.31/1.33  fof(f2422,plain,(
% 6.31/1.33    ( ! [X12,X10,X8,X13,X11,X9] : (~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X8,X9))) | v1_funct_1(k6_partfun1(sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X10,X11))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X12,X13)))) )),
% 6.31/1.33    inference(trivial_inequality_removal,[],[f2420])).
% 6.31/1.33  fof(f2420,plain,(
% 6.31/1.33    ( ! [X12,X10,X8,X13,X11,X9] : (k2_relat_1(sK3) != k2_relat_1(sK3) | ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X8,X9))) | v1_funct_1(k6_partfun1(sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X10,X11))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X12,X13)))) )),
% 6.31/1.33    inference(resolution,[],[f2281,f149])).
% 6.31/1.33  fof(f2281,plain,(
% 6.31/1.33    ( ! [X6,X4,X10,X8,X7,X5,X9] : (~r1_tarski(k2_relat_1(sK3),X6) | k2_relat_1(sK3) != X6 | ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X7,X8))) | v1_funct_1(k6_partfun1(sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))) )),
% 6.31/1.33    inference(resolution,[],[f2279,f454])).
% 6.31/1.33  fof(f2279,plain,(
% 6.31/1.33    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,X2))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relat_1(sK3) != X2 | ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | v1_funct_1(k6_partfun1(sK2))) )),
% 6.31/1.33    inference(forward_demodulation,[],[f2278,f439])).
% 6.31/1.33  fof(f2278,plain,(
% 6.31/1.33    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relat_1(sK3) != X2 | ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X2))) | v1_funct_1(k6_partfun1(sK2))) )),
% 6.31/1.33    inference(subsumption_resolution,[],[f2277,f114])).
% 6.31/1.33  fof(f2277,plain,(
% 6.31/1.33    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relat_1(sK3) != X2 | ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X2))) | v1_funct_1(k6_partfun1(sK2)) | ~v1_relat_1(sK3)) )),
% 6.31/1.33    inference(subsumption_resolution,[],[f2276,f164])).
% 6.31/1.33  fof(f2276,plain,(
% 6.31/1.33    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relat_1(sK3) != X2 | ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X2))) | v1_funct_1(k6_partfun1(sK2)) | ~r1_tarski(k2_relat_1(sK3),X2) | ~v1_relat_1(sK3)) )),
% 6.31/1.33    inference(subsumption_resolution,[],[f2273,f79])).
% 6.31/1.33  fof(f2273,plain,(
% 6.31/1.33    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relat_1(sK3) != X2 | ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X2))) | v1_funct_1(k6_partfun1(sK2)) | ~r1_tarski(k2_relat_1(sK3),X2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)) )),
% 6.31/1.33    inference(resolution,[],[f2270,f102])).
% 6.31/1.33  fof(f2270,plain,(
% 6.31/1.33    ( ! [X26,X24,X23,X27,X25,X22] : (~v1_funct_2(sK3,X27,X24) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X22,X23))) | k2_relat_1(sK3) != X24 | ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X25,X26))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X27,X24))) | v1_funct_1(k6_partfun1(sK2))) )),
% 6.31/1.33    inference(forward_demodulation,[],[f2269,f439])).
% 6.31/1.33  fof(f2269,plain,(
% 6.31/1.33    ( ! [X26,X24,X23,X27,X25,X22] : (v1_funct_1(k6_partfun1(k1_relat_1(sK3))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X22,X23))) | k2_relat_1(sK3) != X24 | ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X25,X26))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X27,X24))) | ~v1_funct_2(sK3,X27,X24)) )),
% 6.31/1.33    inference(subsumption_resolution,[],[f2265,f79])).
% 6.31/1.33  fof(f2265,plain,(
% 6.31/1.33    ( ! [X26,X24,X23,X27,X25,X22] : (v1_funct_1(k6_partfun1(k1_relat_1(sK3))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X22,X23))) | ~v1_funct_1(sK3) | k2_relat_1(sK3) != X24 | ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X25,X26))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X27,X24))) | ~v1_funct_2(sK3,X27,X24)) )),
% 6.31/1.33    inference(resolution,[],[f1405,f86])).
% 6.31/1.33  fof(f1405,plain,(
% 6.31/1.33    ( ! [X6,X4,X2,X0,X5,X3,X1] : (~v2_funct_1(X2) | v1_funct_1(k6_partfun1(k1_relat_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_1(X2) | k2_relat_1(X2) != X1 | ~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X5,X6))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1)) )),
% 6.31/1.33    inference(duplicate_literal_removal,[],[f1404])).
% 6.31/1.33  fof(f1404,plain,(
% 6.31/1.33    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_relat_1(X2) != X1 | v1_funct_1(k6_partfun1(k1_relat_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_1(X2) | ~v2_funct_1(X2) | ~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X5,X6))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.31/1.33    inference(superposition,[],[f745,f116])).
% 6.31/1.33  fof(f745,plain,(
% 6.31/1.33    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_relset_1(X5,X6,X0) != X6 | v1_funct_1(k6_partfun1(k1_relat_1(X0))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) | ~v1_funct_2(X0,X5,X6)) )),
% 6.31/1.33    inference(duplicate_literal_removal,[],[f744])).
% 6.31/1.33  fof(f744,plain,(
% 6.31/1.33    ( ! [X6,X4,X2,X0,X5,X3,X1] : (~m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_funct_1(k6_partfun1(k1_relat_1(X0))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k2_relset_1(X5,X6,X0) != X6 | ~v2_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) | ~v1_funct_2(X0,X5,X6) | ~v1_funct_1(X0)) )),
% 6.31/1.33    inference(resolution,[],[f465,f121])).
% 6.31/1.33  fof(f121,plain,(
% 6.31/1.33    ( ! [X2,X0,X1] : (v1_funct_1(k2_funct_1(X2)) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 6.31/1.33    inference(cnf_transformation,[],[f46])).
% 6.31/1.33  fof(f465,plain,(
% 6.31/1.33    ( ! [X6,X8,X7,X5,X9] : (~v1_funct_1(k2_funct_1(X5)) | ~m1_subset_1(k2_funct_1(X5),k1_zfmisc_1(k2_zfmisc_1(X6,X7))) | v1_funct_1(k6_partfun1(k1_relat_1(X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X8,X9))) | ~v1_funct_1(X5) | ~v2_funct_1(X5)) )),
% 6.31/1.33    inference(subsumption_resolution,[],[f462,f114])).
% 6.31/1.33  fof(f462,plain,(
% 6.31/1.33    ( ! [X6,X8,X7,X5,X9] : (v1_funct_1(k6_partfun1(k1_relat_1(X5))) | ~m1_subset_1(k2_funct_1(X5),k1_zfmisc_1(k2_zfmisc_1(X6,X7))) | ~v1_funct_1(k2_funct_1(X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X8,X9))) | ~v1_funct_1(X5) | ~v2_funct_1(X5) | ~v1_relat_1(X5)) )),
% 6.31/1.33    inference(duplicate_literal_removal,[],[f460])).
% 6.31/1.33  fof(f460,plain,(
% 6.31/1.33    ( ! [X6,X8,X7,X5,X9] : (v1_funct_1(k6_partfun1(k1_relat_1(X5))) | ~m1_subset_1(k2_funct_1(X5),k1_zfmisc_1(k2_zfmisc_1(X6,X7))) | ~v1_funct_1(k2_funct_1(X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X8,X9))) | ~v1_funct_1(X5) | ~v2_funct_1(X5) | ~v1_funct_1(X5) | ~v1_relat_1(X5)) )),
% 6.31/1.33    inference(superposition,[],[f360,f148])).
% 6.31/1.33  fof(f148,plain,(
% 6.31/1.33    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 6.31/1.33    inference(definition_unfolding,[],[f96,f89])).
% 6.31/1.33  fof(f96,plain,(
% 6.31/1.33    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 6.31/1.33    inference(cnf_transformation,[],[f32])).
% 6.31/1.33  fof(f32,plain,(
% 6.31/1.33    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 6.31/1.33    inference(flattening,[],[f31])).
% 6.31/1.33  fof(f31,plain,(
% 6.31/1.33    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 6.31/1.33    inference(ennf_transformation,[],[f9])).
% 6.31/1.33  fof(f9,axiom,(
% 6.31/1.33    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 6.31/1.33    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).
% 6.31/1.33  fof(f360,plain,(
% 6.31/1.33    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k5_relat_1(X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 6.31/1.33    inference(duplicate_literal_removal,[],[f359])).
% 6.31/1.33  fof(f359,plain,(
% 6.31/1.33    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k5_relat_1(X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 6.31/1.33    inference(superposition,[],[f140,f139])).
% 6.31/1.33  fof(f139,plain,(
% 6.31/1.33    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 6.31/1.33    inference(cnf_transformation,[],[f54])).
% 6.31/1.33  fof(f54,plain,(
% 6.31/1.33    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 6.31/1.33    inference(flattening,[],[f53])).
% 6.31/1.33  fof(f53,plain,(
% 6.31/1.33    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 6.31/1.33    inference(ennf_transformation,[],[f20])).
% 6.31/1.33  fof(f20,axiom,(
% 6.31/1.33    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 6.31/1.33    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 6.31/1.33  fof(f140,plain,(
% 6.31/1.33    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 6.31/1.33    inference(cnf_transformation,[],[f56])).
% 6.31/1.33  fof(f56,plain,(
% 6.31/1.33    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 6.31/1.33    inference(flattening,[],[f55])).
% 6.31/1.33  fof(f55,plain,(
% 6.31/1.33    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 6.31/1.33    inference(ennf_transformation,[],[f18])).
% 6.31/1.33  fof(f18,axiom,(
% 6.31/1.33    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 6.31/1.33    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 6.31/1.33  fof(f2823,plain,(
% 6.31/1.33    ~r2_relset_1(sK2,sK2,k5_relat_1(k6_partfun1(sK2),sK3),sK3) | k1_xboole_0 = sK2 | ~v1_funct_1(k6_partfun1(sK2))),
% 6.31/1.33    inference(subsumption_resolution,[],[f2822,f93])).
% 6.31/1.33  fof(f2822,plain,(
% 6.31/1.33    ~r2_relset_1(sK2,sK2,k5_relat_1(k6_partfun1(sK2),sK3),sK3) | k1_xboole_0 = sK2 | ~m1_subset_1(k6_partfun1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_1(k6_partfun1(sK2))),
% 6.31/1.33    inference(subsumption_resolution,[],[f2821,f79])).
% 6.31/1.33  fof(f2821,plain,(
% 6.31/1.33    ~r2_relset_1(sK2,sK2,k5_relat_1(k6_partfun1(sK2),sK3),sK3) | k1_xboole_0 = sK2 | ~v1_funct_1(sK3) | ~m1_subset_1(k6_partfun1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_1(k6_partfun1(sK2))),
% 6.31/1.33    inference(subsumption_resolution,[],[f2812,f81])).
% 6.31/1.33  fof(f2812,plain,(
% 6.31/1.33    ~r2_relset_1(sK2,sK2,k5_relat_1(k6_partfun1(sK2),sK3),sK3) | k1_xboole_0 = sK2 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_1(sK3) | ~m1_subset_1(k6_partfun1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_1(k6_partfun1(sK2))),
% 6.31/1.33    inference(superposition,[],[f2798,f139])).
% 6.31/1.33  fof(f2798,plain,(
% 6.31/1.33    ~r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,k6_partfun1(sK2),sK3),sK3) | k1_xboole_0 = sK2),
% 6.31/1.33    inference(subsumption_resolution,[],[f2795,f2757])).
% 6.31/1.33  fof(f2795,plain,(
% 6.31/1.33    ~r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,k6_partfun1(sK2),sK3),sK3) | ~v1_funct_1(k6_partfun1(sK2)) | k1_xboole_0 = sK2),
% 6.31/1.33    inference(resolution,[],[f2788,f2187])).
% 6.31/1.33  fof(f2187,plain,(
% 6.31/1.33    ~v1_funct_2(k6_partfun1(sK2),sK2,sK2) | ~r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,k6_partfun1(sK2),sK3),sK3) | ~v1_funct_1(k6_partfun1(sK2)) | k1_xboole_0 = sK2),
% 6.31/1.33    inference(forward_demodulation,[],[f2186,f398])).
% 6.31/1.33  fof(f398,plain,(
% 6.31/1.33    sK3 = k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3)),
% 6.31/1.33    inference(subsumption_resolution,[],[f397,f82])).
% 6.31/1.33  fof(f82,plain,(
% 6.31/1.33    v1_funct_1(sK4)),
% 6.31/1.33    inference(cnf_transformation,[],[f64])).
% 6.31/1.33  fof(f397,plain,(
% 6.31/1.33    sK3 = k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3) | ~v1_funct_1(sK4)),
% 6.31/1.33    inference(subsumption_resolution,[],[f396,f84])).
% 6.31/1.33  fof(f84,plain,(
% 6.31/1.33    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))),
% 6.31/1.33    inference(cnf_transformation,[],[f64])).
% 6.31/1.33  fof(f396,plain,(
% 6.31/1.33    sK3 = k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_1(sK4)),
% 6.31/1.33    inference(subsumption_resolution,[],[f395,f79])).
% 6.31/1.33  fof(f395,plain,(
% 6.31/1.33    sK3 = k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3) | ~v1_funct_1(sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_1(sK4)),
% 6.31/1.33    inference(subsumption_resolution,[],[f392,f81])).
% 6.31/1.33  fof(f392,plain,(
% 6.31/1.33    sK3 = k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_1(sK4)),
% 6.31/1.33    inference(resolution,[],[f293,f141])).
% 6.31/1.33  fof(f141,plain,(
% 6.31/1.33    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 6.31/1.33    inference(cnf_transformation,[],[f56])).
% 6.31/1.33  fof(f293,plain,(
% 6.31/1.33    ~m1_subset_1(k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | sK3 = k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3)),
% 6.31/1.33    inference(subsumption_resolution,[],[f286,f81])).
% 6.31/1.33  fof(f286,plain,(
% 6.31/1.33    sK3 = k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~m1_subset_1(k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))),
% 6.31/1.33    inference(resolution,[],[f137,f85])).
% 6.31/1.33  fof(f85,plain,(
% 6.31/1.33    r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3),sK3)),
% 6.31/1.33    inference(cnf_transformation,[],[f64])).
% 6.31/1.33  fof(f137,plain,(
% 6.31/1.33    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.31/1.33    inference(cnf_transformation,[],[f78])).
% 6.31/1.33  fof(f2186,plain,(
% 6.31/1.33    ~r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,k6_partfun1(sK2),sK3),k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3)) | ~v1_funct_2(k6_partfun1(sK2),sK2,sK2) | ~v1_funct_1(k6_partfun1(sK2)) | k1_xboole_0 = sK2),
% 6.31/1.33    inference(subsumption_resolution,[],[f2185,f93])).
% 6.31/1.33  fof(f2185,plain,(
% 6.31/1.33    ~r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,k6_partfun1(sK2),sK3),k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3)) | ~m1_subset_1(k6_partfun1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_2(k6_partfun1(sK2),sK2,sK2) | ~v1_funct_1(k6_partfun1(sK2)) | k1_xboole_0 = sK2),
% 6.31/1.33    inference(subsumption_resolution,[],[f2184,f82])).
% 6.31/1.33  fof(f2184,plain,(
% 6.31/1.33    ~r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,k6_partfun1(sK2),sK3),k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3)) | ~v1_funct_1(sK4) | ~m1_subset_1(k6_partfun1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_2(k6_partfun1(sK2),sK2,sK2) | ~v1_funct_1(k6_partfun1(sK2)) | k1_xboole_0 = sK2),
% 6.31/1.33    inference(subsumption_resolution,[],[f2183,f83])).
% 6.31/1.33  fof(f83,plain,(
% 6.31/1.33    v1_funct_2(sK4,sK2,sK2)),
% 6.31/1.33    inference(cnf_transformation,[],[f64])).
% 6.31/1.33  fof(f2183,plain,(
% 6.31/1.33    ~r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,k6_partfun1(sK2),sK3),k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3)) | ~v1_funct_2(sK4,sK2,sK2) | ~v1_funct_1(sK4) | ~m1_subset_1(k6_partfun1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_2(k6_partfun1(sK2),sK2,sK2) | ~v1_funct_1(k6_partfun1(sK2)) | k1_xboole_0 = sK2),
% 6.31/1.33    inference(subsumption_resolution,[],[f2173,f84])).
% 6.31/1.33  fof(f2173,plain,(
% 6.31/1.33    ~r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,k6_partfun1(sK2),sK3),k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_2(sK4,sK2,sK2) | ~v1_funct_1(sK4) | ~m1_subset_1(k6_partfun1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_2(k6_partfun1(sK2),sK2,sK2) | ~v1_funct_1(k6_partfun1(sK2)) | k1_xboole_0 = sK2),
% 6.31/1.33    inference(resolution,[],[f1555,f308])).
% 6.31/1.33  fof(f308,plain,(
% 6.31/1.33    ~r2_relset_1(sK2,sK2,k6_partfun1(sK2),sK4)),
% 6.31/1.33    inference(subsumption_resolution,[],[f307,f93])).
% 6.31/1.33  fof(f307,plain,(
% 6.31/1.33    ~r2_relset_1(sK2,sK2,k6_partfun1(sK2),sK4) | ~m1_subset_1(k6_partfun1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))),
% 6.31/1.33    inference(subsumption_resolution,[],[f303,f84])).
% 6.31/1.33  fof(f303,plain,(
% 6.31/1.33    ~r2_relset_1(sK2,sK2,k6_partfun1(sK2),sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~m1_subset_1(k6_partfun1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))),
% 6.31/1.33    inference(resolution,[],[f136,f87])).
% 6.31/1.33  fof(f87,plain,(
% 6.31/1.33    ~r2_relset_1(sK2,sK2,sK4,k6_partfun1(sK2))),
% 6.31/1.33    inference(cnf_transformation,[],[f64])).
% 6.31/1.33  fof(f136,plain,(
% 6.31/1.33    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X3,X2) | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.31/1.33    inference(cnf_transformation,[],[f50])).
% 6.31/1.33  fof(f50,plain,(
% 6.31/1.33    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X3,X2) | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.31/1.33    inference(flattening,[],[f49])).
% 6.31/1.33  fof(f49,plain,(
% 6.31/1.33    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X3,X2) | ~r2_relset_1(X0,X1,X2,X3)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 6.31/1.33    inference(ennf_transformation,[],[f17])).
% 6.31/1.33  fof(f17,axiom,(
% 6.31/1.33    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) => r2_relset_1(X0,X1,X3,X2)))),
% 6.31/1.33    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r2_relset_1)).
% 6.31/1.33  fof(f1555,plain,(
% 6.31/1.33    ( ! [X6,X4,X5] : (r2_relset_1(X4,sK2,X5,X6) | ~r2_relset_1(X4,sK2,k1_partfun1(X4,sK2,sK2,sK2,X5,sK3),k1_partfun1(X4,sK2,sK2,sK2,X6,sK3)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,sK2))) | ~v1_funct_2(X6,X4,sK2) | ~v1_funct_1(X6) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,sK2))) | ~v1_funct_2(X5,X4,sK2) | ~v1_funct_1(X5) | k1_xboole_0 = sK2) )),
% 6.31/1.33    inference(subsumption_resolution,[],[f1543,f81])).
% 6.31/1.33  fof(f1543,plain,(
% 6.31/1.33    ( ! [X6,X4,X5] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | k1_xboole_0 = sK2 | ~r2_relset_1(X4,sK2,k1_partfun1(X4,sK2,sK2,sK2,X5,sK3),k1_partfun1(X4,sK2,sK2,sK2,X6,sK3)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,sK2))) | ~v1_funct_2(X6,X4,sK2) | ~v1_funct_1(X6) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,sK2))) | ~v1_funct_2(X5,X4,sK2) | ~v1_funct_1(X5) | r2_relset_1(X4,sK2,X5,X6)) )),
% 6.31/1.33    inference(duplicate_literal_removal,[],[f1541])).
% 6.31/1.33  fof(f1541,plain,(
% 6.31/1.33    ( ! [X6,X4,X5] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | k1_xboole_0 = sK2 | k1_xboole_0 = sK2 | ~r2_relset_1(X4,sK2,k1_partfun1(X4,sK2,sK2,sK2,X5,sK3),k1_partfun1(X4,sK2,sK2,sK2,X6,sK3)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,sK2))) | ~v1_funct_2(X6,X4,sK2) | ~v1_funct_1(X6) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,sK2))) | ~v1_funct_2(X5,X4,sK2) | ~v1_funct_1(X5) | r2_relset_1(X4,sK2,X5,X6)) )),
% 6.31/1.33    inference(resolution,[],[f960,f80])).
% 6.31/1.33  fof(f960,plain,(
% 6.31/1.33    ( ! [X23,X21,X19,X22,X20] : (~v1_funct_2(sK3,X19,X20) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X19,X20))) | k1_xboole_0 = X19 | k1_xboole_0 = X20 | ~r2_relset_1(X21,X20,k1_partfun1(X21,X19,X19,X20,X22,sK3),k1_partfun1(X21,X19,X19,X20,X23,sK3)) | ~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X19))) | ~v1_funct_2(X23,X21,X19) | ~v1_funct_1(X23) | ~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X21,X19))) | ~v1_funct_2(X22,X21,X19) | ~v1_funct_1(X22) | r2_relset_1(X21,X19,X22,X23)) )),
% 6.31/1.33    inference(subsumption_resolution,[],[f959,f79])).
% 6.31/1.33  fof(f959,plain,(
% 6.31/1.33    ( ! [X23,X21,X19,X22,X20] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X19,X20))) | ~v1_funct_2(sK3,X19,X20) | ~v1_funct_1(sK3) | k1_xboole_0 = X19 | k1_xboole_0 = X20 | ~r2_relset_1(X21,X20,k1_partfun1(X21,X19,X19,X20,X22,sK3),k1_partfun1(X21,X19,X19,X20,X23,sK3)) | ~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X19))) | ~v1_funct_2(X23,X21,X19) | ~v1_funct_1(X23) | ~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X21,X19))) | ~v1_funct_2(X22,X21,X19) | ~v1_funct_1(X22) | r2_relset_1(X21,X19,X22,X23)) )),
% 6.31/1.33    inference(resolution,[],[f481,f86])).
% 6.31/1.33  fof(f481,plain,(
% 6.31/1.33    ( ! [X4,X2,X0,X5,X3,X1] : (~v2_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X1,X0,X2) | ~v1_funct_1(X1) | k1_xboole_0 = X0 | k1_xboole_0 = X2 | ~r2_relset_1(X3,X2,k1_partfun1(X3,X0,X0,X2,X4,X1),k1_partfun1(X3,X0,X0,X2,X5,X1)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) | ~v1_funct_2(X5,X3,X0) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) | ~v1_funct_2(X4,X3,X0) | ~v1_funct_1(X4) | r2_relset_1(X3,X0,X4,X5)) )),
% 6.31/1.33    inference(resolution,[],[f300,f126])).
% 6.31/1.33  fof(f126,plain,(
% 6.31/1.33    ( ! [X6,X2,X0,X8,X7,X1] : (~sP0(X0,X1,X2) | ~r2_relset_1(X6,X2,k1_partfun1(X6,X0,X0,X2,X7,X1),k1_partfun1(X6,X0,X0,X2,X8,X1)) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X0))) | ~v1_funct_2(X8,X6,X0) | ~v1_funct_1(X8) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X6,X0))) | ~v1_funct_2(X7,X6,X0) | ~v1_funct_1(X7) | r2_relset_1(X6,X0,X7,X8)) )),
% 6.31/1.33    inference(cnf_transformation,[],[f77])).
% 6.31/1.33  fof(f77,plain,(
% 6.31/1.33    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((~r2_relset_1(sK5(X0,X1,X2),X0,sK6(X0,X1,X2),sK7(X0,X1,X2)) & r2_relset_1(sK5(X0,X1,X2),X2,k1_partfun1(sK5(X0,X1,X2),X0,X0,X2,sK6(X0,X1,X2),X1),k1_partfun1(sK5(X0,X1,X2),X0,X0,X2,sK7(X0,X1,X2),X1)) & m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(sK5(X0,X1,X2),X0))) & v1_funct_2(sK7(X0,X1,X2),sK5(X0,X1,X2),X0) & v1_funct_1(sK7(X0,X1,X2))) & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(sK5(X0,X1,X2),X0))) & v1_funct_2(sK6(X0,X1,X2),sK5(X0,X1,X2),X0) & v1_funct_1(sK6(X0,X1,X2)))) & (! [X6,X7] : (! [X8] : (r2_relset_1(X6,X0,X7,X8) | ~r2_relset_1(X6,X2,k1_partfun1(X6,X0,X0,X2,X7,X1),k1_partfun1(X6,X0,X0,X2,X8,X1)) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X0))) | ~v1_funct_2(X8,X6,X0) | ~v1_funct_1(X8)) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X6,X0))) | ~v1_funct_2(X7,X6,X0) | ~v1_funct_1(X7)) | ~sP0(X0,X1,X2)))),
% 6.31/1.33    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f74,f76,f75])).
% 6.31/1.33  fof(f75,plain,(
% 6.31/1.33    ! [X2,X1,X0] : (? [X3,X4] : (? [X5] : (~r2_relset_1(X3,X0,X4,X5) & r2_relset_1(X3,X2,k1_partfun1(X3,X0,X0,X2,X4,X1),k1_partfun1(X3,X0,X0,X2,X5,X1)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) & v1_funct_2(X5,X3,X0) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) & v1_funct_2(X4,X3,X0) & v1_funct_1(X4)) => (? [X5] : (~r2_relset_1(sK5(X0,X1,X2),X0,sK6(X0,X1,X2),X5) & r2_relset_1(sK5(X0,X1,X2),X2,k1_partfun1(sK5(X0,X1,X2),X0,X0,X2,sK6(X0,X1,X2),X1),k1_partfun1(sK5(X0,X1,X2),X0,X0,X2,X5,X1)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK5(X0,X1,X2),X0))) & v1_funct_2(X5,sK5(X0,X1,X2),X0) & v1_funct_1(X5)) & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(sK5(X0,X1,X2),X0))) & v1_funct_2(sK6(X0,X1,X2),sK5(X0,X1,X2),X0) & v1_funct_1(sK6(X0,X1,X2))))),
% 6.31/1.33    introduced(choice_axiom,[])).
% 6.31/1.33  fof(f76,plain,(
% 6.31/1.33    ! [X2,X1,X0] : (? [X5] : (~r2_relset_1(sK5(X0,X1,X2),X0,sK6(X0,X1,X2),X5) & r2_relset_1(sK5(X0,X1,X2),X2,k1_partfun1(sK5(X0,X1,X2),X0,X0,X2,sK6(X0,X1,X2),X1),k1_partfun1(sK5(X0,X1,X2),X0,X0,X2,X5,X1)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK5(X0,X1,X2),X0))) & v1_funct_2(X5,sK5(X0,X1,X2),X0) & v1_funct_1(X5)) => (~r2_relset_1(sK5(X0,X1,X2),X0,sK6(X0,X1,X2),sK7(X0,X1,X2)) & r2_relset_1(sK5(X0,X1,X2),X2,k1_partfun1(sK5(X0,X1,X2),X0,X0,X2,sK6(X0,X1,X2),X1),k1_partfun1(sK5(X0,X1,X2),X0,X0,X2,sK7(X0,X1,X2),X1)) & m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(sK5(X0,X1,X2),X0))) & v1_funct_2(sK7(X0,X1,X2),sK5(X0,X1,X2),X0) & v1_funct_1(sK7(X0,X1,X2))))),
% 6.31/1.33    introduced(choice_axiom,[])).
% 6.31/1.33  fof(f74,plain,(
% 6.31/1.33    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3,X4] : (? [X5] : (~r2_relset_1(X3,X0,X4,X5) & r2_relset_1(X3,X2,k1_partfun1(X3,X0,X0,X2,X4,X1),k1_partfun1(X3,X0,X0,X2,X5,X1)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) & v1_funct_2(X5,X3,X0) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) & v1_funct_2(X4,X3,X0) & v1_funct_1(X4))) & (! [X6,X7] : (! [X8] : (r2_relset_1(X6,X0,X7,X8) | ~r2_relset_1(X6,X2,k1_partfun1(X6,X0,X0,X2,X7,X1),k1_partfun1(X6,X0,X0,X2,X8,X1)) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X0))) | ~v1_funct_2(X8,X6,X0) | ~v1_funct_1(X8)) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X6,X0))) | ~v1_funct_2(X7,X6,X0) | ~v1_funct_1(X7)) | ~sP0(X0,X1,X2)))),
% 6.31/1.33    inference(rectify,[],[f73])).
% 6.31/1.33  fof(f73,plain,(
% 6.31/1.33    ! [X0,X2,X1] : ((sP0(X0,X2,X1) | ? [X3,X4] : (? [X5] : (~r2_relset_1(X3,X0,X4,X5) & r2_relset_1(X3,X1,k1_partfun1(X3,X0,X0,X1,X4,X2),k1_partfun1(X3,X0,X0,X1,X5,X2)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) & v1_funct_2(X5,X3,X0) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) & v1_funct_2(X4,X3,X0) & v1_funct_1(X4))) & (! [X3,X4] : (! [X5] : (r2_relset_1(X3,X0,X4,X5) | ~r2_relset_1(X3,X1,k1_partfun1(X3,X0,X0,X1,X4,X2),k1_partfun1(X3,X0,X0,X1,X5,X2)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) | ~v1_funct_2(X5,X3,X0) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) | ~v1_funct_2(X4,X3,X0) | ~v1_funct_1(X4)) | ~sP0(X0,X2,X1)))),
% 6.31/1.33    inference(nnf_transformation,[],[f59])).
% 6.31/1.33  fof(f59,plain,(
% 6.31/1.33    ! [X0,X2,X1] : (sP0(X0,X2,X1) <=> ! [X3,X4] : (! [X5] : (r2_relset_1(X3,X0,X4,X5) | ~r2_relset_1(X3,X1,k1_partfun1(X3,X0,X0,X1,X4,X2),k1_partfun1(X3,X0,X0,X1,X5,X2)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) | ~v1_funct_2(X5,X3,X0) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) | ~v1_funct_2(X4,X3,X0) | ~v1_funct_1(X4)))),
% 6.31/1.33    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 6.31/1.33  fof(f300,plain,(
% 6.31/1.33    ( ! [X2,X0,X1] : (sP0(X1,X2,X0) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X2,X1,X0) | ~v1_funct_1(X2) | ~v2_funct_1(X2) | k1_xboole_0 = X0) )),
% 6.31/1.33    inference(resolution,[],[f135,f124])).
% 6.31/1.33  fof(f124,plain,(
% 6.31/1.33    ( ! [X2,X0,X1] : (~sP1(X0,X1,X2) | ~v2_funct_1(X1) | sP0(X2,X1,X0)) )),
% 6.31/1.33    inference(cnf_transformation,[],[f72])).
% 6.31/1.33  fof(f72,plain,(
% 6.31/1.33    ! [X0,X1,X2] : (((v2_funct_1(X1) | ~sP0(X2,X1,X0)) & (sP0(X2,X1,X0) | ~v2_funct_1(X1))) | ~sP1(X0,X1,X2))),
% 6.31/1.33    inference(rectify,[],[f71])).
% 6.31/1.33  fof(f71,plain,(
% 6.31/1.33    ! [X1,X2,X0] : (((v2_funct_1(X2) | ~sP0(X0,X2,X1)) & (sP0(X0,X2,X1) | ~v2_funct_1(X2))) | ~sP1(X1,X2,X0))),
% 6.31/1.33    inference(nnf_transformation,[],[f60])).
% 6.31/1.33  fof(f60,plain,(
% 6.31/1.33    ! [X1,X2,X0] : ((v2_funct_1(X2) <=> sP0(X0,X2,X1)) | ~sP1(X1,X2,X0))),
% 6.31/1.33    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 6.31/1.33  fof(f135,plain,(
% 6.31/1.33    ( ! [X2,X0,X1] : (sP1(X1,X2,X0) | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 6.31/1.33    inference(cnf_transformation,[],[f61])).
% 6.31/1.33  fof(f61,plain,(
% 6.31/1.33    ! [X0,X1,X2] : (sP1(X1,X2,X0) | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 6.31/1.33    inference(definition_folding,[],[f48,f60,f59])).
% 6.31/1.33  fof(f48,plain,(
% 6.31/1.33    ! [X0,X1,X2] : ((v2_funct_1(X2) <=> ! [X3,X4] : (! [X5] : (r2_relset_1(X3,X0,X4,X5) | ~r2_relset_1(X3,X1,k1_partfun1(X3,X0,X0,X1,X4,X2),k1_partfun1(X3,X0,X0,X1,X5,X2)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) | ~v1_funct_2(X5,X3,X0) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) | ~v1_funct_2(X4,X3,X0) | ~v1_funct_1(X4))) | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 6.31/1.33    inference(flattening,[],[f47])).
% 6.31/1.33  fof(f47,plain,(
% 6.31/1.33    ! [X0,X1,X2] : (((v2_funct_1(X2) <=> ! [X3,X4] : (! [X5] : ((r2_relset_1(X3,X0,X4,X5) | ~r2_relset_1(X3,X1,k1_partfun1(X3,X0,X0,X1,X4,X2),k1_partfun1(X3,X0,X0,X1,X5,X2))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) | ~v1_funct_2(X5,X3,X0) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) | ~v1_funct_2(X4,X3,X0) | ~v1_funct_1(X4)))) | k1_xboole_0 = X1 | k1_xboole_0 = X0) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 6.31/1.33    inference(ennf_transformation,[],[f23])).
% 6.31/1.33  fof(f23,axiom,(
% 6.31/1.33    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ~(~(v2_funct_1(X2) <=> ! [X3,X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) & v1_funct_2(X4,X3,X0) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) & v1_funct_2(X5,X3,X0) & v1_funct_1(X5)) => (r2_relset_1(X3,X1,k1_partfun1(X3,X0,X0,X1,X4,X2),k1_partfun1(X3,X0,X0,X1,X5,X2)) => r2_relset_1(X3,X0,X4,X5))))) & k1_xboole_0 != X1 & k1_xboole_0 != X0))),
% 6.31/1.33    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_funct_2)).
% 6.31/1.33  fof(f2788,plain,(
% 6.31/1.33    v1_funct_2(k6_partfun1(sK2),sK2,sK2)),
% 6.31/1.33    inference(resolution,[],[f2767,f149])).
% 6.31/1.33  fof(f2767,plain,(
% 6.31/1.33    ( ! [X0] : (~r1_tarski(sK2,X0) | v1_funct_2(k6_partfun1(sK2),sK2,X0)) )),
% 6.31/1.33    inference(resolution,[],[f2757,f189])).
% 6.31/1.33  fof(f189,plain,(
% 6.31/1.33    ( ! [X0,X1] : (~v1_funct_1(k6_partfun1(X0)) | v1_funct_2(k6_partfun1(X0),X0,X1) | ~r1_tarski(X0,X1)) )),
% 6.31/1.33    inference(forward_demodulation,[],[f188,f145])).
% 6.31/1.33  fof(f188,plain,(
% 6.31/1.33    ( ! [X0,X1] : (v1_funct_2(k6_partfun1(X0),X0,X1) | ~r1_tarski(k2_relat_1(k6_partfun1(X0)),X1) | ~v1_funct_1(k6_partfun1(X0))) )),
% 6.31/1.33    inference(subsumption_resolution,[],[f187,f144])).
% 6.31/1.33  fof(f144,plain,(
% 6.31/1.33    ( ! [X0] : (v1_relat_1(k6_partfun1(X0))) )),
% 6.31/1.33    inference(definition_unfolding,[],[f90,f89])).
% 6.31/1.34  fof(f90,plain,(
% 6.31/1.34    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 6.31/1.34    inference(cnf_transformation,[],[f8])).
% 6.31/1.34  fof(f8,axiom,(
% 6.31/1.34    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 6.31/1.34    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).
% 6.31/1.34  fof(f187,plain,(
% 6.31/1.34    ( ! [X0,X1] : (v1_funct_2(k6_partfun1(X0),X0,X1) | ~r1_tarski(k2_relat_1(k6_partfun1(X0)),X1) | ~v1_funct_1(k6_partfun1(X0)) | ~v1_relat_1(k6_partfun1(X0))) )),
% 6.31/1.34    inference(superposition,[],[f102,f146])).
% 6.31/1.34  fof(f146,plain,(
% 6.31/1.34    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 6.31/1.34    inference(definition_unfolding,[],[f94,f89])).
% 6.31/1.34  fof(f94,plain,(
% 6.31/1.34    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 6.31/1.34    inference(cnf_transformation,[],[f7])).
% 6.31/1.34  fof(f3150,plain,(
% 6.31/1.34    k1_xboole_0 = sK4 | ~r1_tarski(k2_zfmisc_1(sK2,sK2),sK4)),
% 6.31/1.34    inference(forward_demodulation,[],[f2849,f151])).
% 6.31/1.34  fof(f2849,plain,(
% 6.31/1.34    sK4 = k2_zfmisc_1(k1_xboole_0,k1_xboole_0) | ~r1_tarski(k2_zfmisc_1(sK2,sK2),sK4)),
% 6.31/1.34    inference(backward_demodulation,[],[f391,f2839])).
% 6.31/1.34  fof(f391,plain,(
% 6.31/1.34    ~r1_tarski(k2_zfmisc_1(sK2,sK2),sK4) | k2_zfmisc_1(sK2,sK2) = sK4),
% 6.31/1.34    inference(resolution,[],[f377,f109])).
% 6.31/1.34  fof(f109,plain,(
% 6.31/1.34    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 6.31/1.34    inference(cnf_transformation,[],[f68])).
% 6.31/1.34  fof(f68,plain,(
% 6.31/1.34    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 6.31/1.34    inference(nnf_transformation,[],[f5])).
% 6.31/1.34  fof(f5,axiom,(
% 6.31/1.34    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 6.31/1.34    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 6.31/1.34  fof(f377,plain,(
% 6.31/1.34    ~m1_subset_1(k2_zfmisc_1(sK2,sK2),k1_zfmisc_1(sK4)) | k2_zfmisc_1(sK2,sK2) = sK4),
% 6.31/1.34    inference(resolution,[],[f196,f84])).
% 6.31/1.34  fof(f196,plain,(
% 6.31/1.34    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X1)) | X1 = X2 | ~m1_subset_1(X1,k1_zfmisc_1(X2))) )),
% 6.31/1.34    inference(resolution,[],[f162,f108])).
% 6.31/1.34  fof(f108,plain,(
% 6.31/1.34    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 6.31/1.34    inference(cnf_transformation,[],[f68])).
% 6.31/1.34  fof(f162,plain,(
% 6.31/1.34    ( ! [X2,X1] : (~r1_tarski(X1,X2) | X1 = X2 | ~m1_subset_1(X2,k1_zfmisc_1(X1))) )),
% 6.31/1.34    inference(resolution,[],[f107,f108])).
% 6.31/1.34  fof(f107,plain,(
% 6.31/1.34    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 6.31/1.34    inference(cnf_transformation,[],[f67])).
% 6.31/1.34  fof(f2941,plain,(
% 6.31/1.34    ~r2_relset_1(k1_xboole_0,k1_xboole_0,sK4,k1_xboole_0)),
% 6.31/1.34    inference(forward_demodulation,[],[f2844,f170])).
% 6.31/1.34  fof(f2844,plain,(
% 6.31/1.34    ~r2_relset_1(k1_xboole_0,k1_xboole_0,sK4,k6_partfun1(k1_xboole_0))),
% 6.31/1.34    inference(backward_demodulation,[],[f87,f2839])).
% 6.31/1.34  % SZS output end Proof for theBenchmark
% 6.31/1.34  % (13191)------------------------------
% 6.31/1.34  % (13191)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.31/1.34  % (13191)Termination reason: Refutation
% 6.31/1.34  
% 6.31/1.34  % (13191)Memory used [KB]: 9978
% 6.31/1.34  % (13191)Time elapsed: 0.689 s
% 6.31/1.34  % (13191)------------------------------
% 6.31/1.34  % (13191)------------------------------
% 6.31/1.35  % (13029)Success in time 0.982 s
%------------------------------------------------------------------------------
