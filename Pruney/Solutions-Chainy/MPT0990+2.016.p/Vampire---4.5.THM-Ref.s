%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:30 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 527 expanded)
%              Number of leaves         :   19 ( 162 expanded)
%              Depth                    :   18
%              Number of atoms          :  446 (5018 expanded)
%              Number of equality atoms :  141 (1716 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f925,plain,(
    $false ),
    inference(subsumption_resolution,[],[f924,f62])).

fof(f62,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,
    ( k2_funct_1(sK2) != sK3
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & v2_funct_1(sK2)
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    & sK1 = k2_relset_1(sK0,sK1,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_2(sK3,sK1,sK0)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f23,f47,f46])).

fof(f46,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( k2_funct_1(X2) != X3
            & k1_xboole_0 != X1
            & k1_xboole_0 != X0
            & v2_funct_1(X2)
            & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
            & k2_relset_1(X0,X1,X2) = X1
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( k2_funct_1(sK2) != X3
          & k1_xboole_0 != sK1
          & k1_xboole_0 != sK0
          & v2_funct_1(sK2)
          & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
          & sK1 = k2_relset_1(sK0,sK1,sK2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
          & v1_funct_2(X3,sK1,sK0)
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( ? [X3] :
        ( k2_funct_1(sK2) != X3
        & k1_xboole_0 != sK1
        & k1_xboole_0 != sK0
        & v2_funct_1(sK2)
        & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
        & sK1 = k2_relset_1(sK0,sK1,sK2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        & v1_funct_2(X3,sK1,sK0)
        & v1_funct_1(X3) )
   => ( k2_funct_1(sK2) != sK3
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0
      & v2_funct_1(sK2)
      & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
      & sK1 = k2_relset_1(sK0,sK1,sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      & v1_funct_2(sK3,sK1,sK0)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & v2_funct_1(X2)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & v2_funct_1(X2)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
           => ( ( v2_funct_1(X2)
                & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
                & k2_relset_1(X0,X1,X2) = X1 )
             => ( k2_funct_1(X2) = X3
                | k1_xboole_0 = X1
                | k1_xboole_0 = X0 ) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( ( v2_funct_1(X2)
              & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
              & k2_relset_1(X0,X1,X2) = X1 )
           => ( k2_funct_1(X2) = X3
              | k1_xboole_0 = X1
              | k1_xboole_0 = X0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).

fof(f924,plain,(
    k2_funct_1(sK2) = sK3 ),
    inference(backward_demodulation,[],[f181,f923])).

fof(f923,plain,(
    sK3 = k5_relat_1(k2_funct_1(sK2),k6_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f922,f279])).

fof(f279,plain,(
    sK3 = k5_relat_1(k6_relat_1(sK1),sK3) ),
    inference(subsumption_resolution,[],[f275,f99])).

fof(f99,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f78,f56])).

fof(f56,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f48])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f275,plain,
    ( sK3 = k5_relat_1(k6_relat_1(sK1),sK3)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f173,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X1),X0)
      | k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k5_relat_1(k6_relat_1(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).

fof(f173,plain,(
    r1_tarski(k1_relat_1(sK3),sK1) ),
    inference(subsumption_resolution,[],[f172,f99])).

fof(f172,plain,
    ( r1_tarski(k1_relat_1(sK3),sK1)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f105,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f105,plain,(
    v4_relat_1(sK3,sK1) ),
    inference(resolution,[],[f80,f56])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f922,plain,(
    k5_relat_1(k2_funct_1(sK2),k6_relat_1(sK0)) = k5_relat_1(k6_relat_1(sK1),sK3) ),
    inference(forward_demodulation,[],[f909,f132])).

fof(f132,plain,(
    k6_relat_1(sK1) = k5_relat_1(k2_funct_1(sK2),sK2) ),
    inference(forward_demodulation,[],[f131,f122])).

fof(f122,plain,(
    sK1 = k2_relat_1(sK2) ),
    inference(forward_demodulation,[],[f119,f57])).

fof(f57,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f48])).

fof(f119,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f79,f53])).

fof(f53,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f48])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f131,plain,(
    k6_relat_1(k2_relat_1(sK2)) = k5_relat_1(k2_funct_1(sK2),sK2) ),
    inference(subsumption_resolution,[],[f130,f98])).

fof(f98,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f78,f53])).

fof(f130,plain,
    ( k6_relat_1(k2_relat_1(sK2)) = k5_relat_1(k2_funct_1(sK2),sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f129,f51])).

fof(f51,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f48])).

fof(f129,plain,
    ( k6_relat_1(k2_relat_1(sK2)) = k5_relat_1(k2_funct_1(sK2),sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f74,f59])).

fof(f59,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f48])).

fof(f74,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
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
       => ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

fof(f909,plain,(
    k5_relat_1(k2_funct_1(sK2),k6_relat_1(sK0)) = k5_relat_1(k5_relat_1(k2_funct_1(sK2),sK2),sK3) ),
    inference(resolution,[],[f466,f174])).

fof(f174,plain,(
    v1_relat_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f94,f98])).

fof(f94,plain,
    ( ~ v1_relat_1(sK2)
    | v1_relat_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f69,f51])).

fof(f69,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | v1_relat_1(k2_funct_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f466,plain,(
    ! [X4] :
      ( ~ v1_relat_1(X4)
      | k5_relat_1(X4,k6_relat_1(sK0)) = k5_relat_1(k5_relat_1(X4,sK2),sK3) ) ),
    inference(forward_demodulation,[],[f464,f356])).

fof(f356,plain,(
    k6_relat_1(sK0) = k5_relat_1(sK2,sK3) ),
    inference(resolution,[],[f243,f224])).

fof(f224,plain,
    ( ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_relat_1(sK0) = k5_relat_1(sK2,sK3) ),
    inference(forward_demodulation,[],[f222,f220])).

fof(f220,plain,(
    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f217,f51])).

fof(f217,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f146,f53])).

fof(f146,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | k1_partfun1(X3,X4,sK1,sK0,X5,sK3) = k5_relat_1(X5,sK3)
      | ~ v1_funct_1(X5) ) ),
    inference(subsumption_resolution,[],[f143,f54])).

fof(f54,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f48])).

fof(f143,plain,(
    ! [X4,X5,X3] :
      ( k1_partfun1(X3,X4,sK1,sK0,X5,sK3) = k5_relat_1(X5,sK3)
      | ~ v1_funct_1(sK3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_1(X5) ) ),
    inference(resolution,[],[f85,f56])).

fof(f85,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
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

fof(f222,plain,
    ( ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0) ),
    inference(backward_demodulation,[],[f136,f220])).

fof(f136,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0)
    | ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subsumption_resolution,[],[f135,f91])).

fof(f91,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(forward_demodulation,[],[f64,f63])).

fof(f63,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f64,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f135,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0)
    | ~ m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f83,f90])).

fof(f90,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f58,f63])).

fof(f58,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f48])).

fof(f83,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f243,plain,(
    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(forward_demodulation,[],[f242,f220])).

fof(f242,plain,(
    m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subsumption_resolution,[],[f239,f51])).

fof(f239,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f151,f53])).

fof(f151,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | m1_subset_1(k1_partfun1(X3,X4,sK1,sK0,X5,sK3),k1_zfmisc_1(k2_zfmisc_1(X3,sK0)))
      | ~ v1_funct_1(X5) ) ),
    inference(subsumption_resolution,[],[f148,f54])).

fof(f148,plain,(
    ! [X4,X5,X3] :
      ( m1_subset_1(k1_partfun1(X3,X4,sK1,sK0,X5,sK3),k1_zfmisc_1(k2_zfmisc_1(X3,sK0)))
      | ~ v1_funct_1(sK3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_1(X5) ) ),
    inference(resolution,[],[f87,f56])).

fof(f87,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
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

fof(f464,plain,(
    ! [X4] :
      ( k5_relat_1(X4,k5_relat_1(sK2,sK3)) = k5_relat_1(k5_relat_1(X4,sK2),sK3)
      | ~ v1_relat_1(X4) ) ),
    inference(resolution,[],[f134,f98])).

fof(f134,plain,(
    ! [X2,X3] :
      ( ~ v1_relat_1(X3)
      | k5_relat_1(k5_relat_1(X2,X3),sK3) = k5_relat_1(X2,k5_relat_1(X3,sK3))
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f68,f99])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

fof(f181,plain,(
    k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f180,f167])).

fof(f167,plain,(
    k6_relat_1(sK0) = k6_relat_1(k1_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f128,f166])).

fof(f166,plain,(
    k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f165,f51])).

fof(f165,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f164,f53])).

fof(f164,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f163,f57])).

fof(f163,plain,
    ( sK1 != k2_relset_1(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f162,f59])).

fof(f162,plain,
    ( ~ v2_funct_1(sK2)
    | sK1 != k2_relset_1(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f160,f61])).

fof(f61,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f48])).

fof(f160,plain,
    ( k1_xboole_0 = sK1
    | ~ v2_funct_1(sK2)
    | sK1 != k2_relset_1(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f93,f52])).

fof(f52,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k6_relat_1(X0) = k5_relat_1(X2,k2_funct_1(X2))
      | ~ v1_funct_1(X2) ) ),
    inference(forward_demodulation,[],[f81,f63])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
            & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_2)).

fof(f128,plain,(
    k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f127,f98])).

fof(f127,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f126,f51])).

fof(f126,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f73,f59])).

fof(f73,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f180,plain,(
    k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_relat_1(k1_relat_1(sK2))) ),
    inference(forward_demodulation,[],[f179,f115])).

fof(f115,plain,(
    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f114,f98])).

fof(f114,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f113,f51])).

fof(f113,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f72,f59])).

fof(f72,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f179,plain,(
    k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_relat_1(k2_relat_1(k2_funct_1(sK2)))) ),
    inference(resolution,[],[f174,f67])).

fof(f67,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:56:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (23930)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.50  % (23925)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.51  % (23926)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.51  % (23936)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.51  % (23938)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.51  % (23932)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.51  % (23951)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.52  % (23924)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.52  % (23934)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.52  % (23935)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.52  % (23946)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.52  % (23942)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.52  % (23927)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.53  % (23945)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.53  % (23937)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.53  % (23947)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.53  % (23928)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.53  % (23931)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.54  % (23939)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.54  % (23950)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.54  % (23952)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.54  % (23929)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.54  % (23943)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.54  % (23949)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.54  % (23944)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.54  % (23933)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.54  % (23923)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.54  % (23948)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.55  % (23939)Refutation not found, incomplete strategy% (23939)------------------------------
% 0.20/0.55  % (23939)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (23939)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (23939)Memory used [KB]: 10746
% 0.20/0.55  % (23939)Time elapsed: 0.143 s
% 0.20/0.55  % (23939)------------------------------
% 0.20/0.55  % (23939)------------------------------
% 0.20/0.55  % (23941)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.55  % (23940)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.57  % (23930)Refutation found. Thanks to Tanya!
% 0.20/0.57  % SZS status Theorem for theBenchmark
% 0.20/0.57  % SZS output start Proof for theBenchmark
% 0.20/0.57  fof(f925,plain,(
% 0.20/0.57    $false),
% 0.20/0.57    inference(subsumption_resolution,[],[f924,f62])).
% 0.20/0.57  fof(f62,plain,(
% 0.20/0.57    k2_funct_1(sK2) != sK3),
% 0.20/0.57    inference(cnf_transformation,[],[f48])).
% 0.20/0.57  fof(f48,plain,(
% 0.20/0.57    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 0.20/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f23,f47,f46])).
% 0.20/0.57  fof(f46,plain,(
% 0.20/0.57    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 0.20/0.57    introduced(choice_axiom,[])).
% 0.20/0.57  fof(f47,plain,(
% 0.20/0.57    ? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) => (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3))),
% 0.20/0.57    introduced(choice_axiom,[])).
% 0.20/0.57  fof(f23,plain,(
% 0.20/0.57    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.20/0.57    inference(flattening,[],[f22])).
% 0.20/0.57  fof(f22,plain,(
% 0.20/0.57    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.20/0.57    inference(ennf_transformation,[],[f19])).
% 0.20/0.57  fof(f19,negated_conjecture,(
% 0.20/0.57    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 0.20/0.57    inference(negated_conjecture,[],[f18])).
% 0.20/0.57  fof(f18,conjecture,(
% 0.20/0.57    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).
% 0.20/0.57  fof(f924,plain,(
% 0.20/0.57    k2_funct_1(sK2) = sK3),
% 0.20/0.57    inference(backward_demodulation,[],[f181,f923])).
% 0.20/0.57  fof(f923,plain,(
% 0.20/0.57    sK3 = k5_relat_1(k2_funct_1(sK2),k6_relat_1(sK0))),
% 0.20/0.57    inference(forward_demodulation,[],[f922,f279])).
% 0.20/0.57  fof(f279,plain,(
% 0.20/0.57    sK3 = k5_relat_1(k6_relat_1(sK1),sK3)),
% 0.20/0.57    inference(subsumption_resolution,[],[f275,f99])).
% 0.20/0.57  fof(f99,plain,(
% 0.20/0.57    v1_relat_1(sK3)),
% 0.20/0.57    inference(resolution,[],[f78,f56])).
% 0.20/0.57  fof(f56,plain,(
% 0.20/0.57    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.20/0.57    inference(cnf_transformation,[],[f48])).
% 0.20/0.57  fof(f78,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f35])).
% 0.20/0.57  fof(f35,plain,(
% 0.20/0.57    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.57    inference(ennf_transformation,[],[f9])).
% 0.20/0.57  fof(f9,axiom,(
% 0.20/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.20/0.57  fof(f275,plain,(
% 0.20/0.57    sK3 = k5_relat_1(k6_relat_1(sK1),sK3) | ~v1_relat_1(sK3)),
% 0.20/0.57    inference(resolution,[],[f173,f75])).
% 0.20/0.57  fof(f75,plain,(
% 0.20/0.57    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X1),X0) | k5_relat_1(k6_relat_1(X0),X1) = X1 | ~v1_relat_1(X1)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f33])).
% 0.20/0.57  fof(f33,plain,(
% 0.20/0.57    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.20/0.57    inference(flattening,[],[f32])).
% 0.20/0.57  fof(f32,plain,(
% 0.20/0.57    ! [X0,X1] : ((k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.57    inference(ennf_transformation,[],[f4])).
% 0.20/0.57  fof(f4,axiom,(
% 0.20/0.57    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k5_relat_1(k6_relat_1(X0),X1) = X1))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).
% 0.20/0.57  fof(f173,plain,(
% 0.20/0.57    r1_tarski(k1_relat_1(sK3),sK1)),
% 0.20/0.57    inference(subsumption_resolution,[],[f172,f99])).
% 0.20/0.57  fof(f172,plain,(
% 0.20/0.57    r1_tarski(k1_relat_1(sK3),sK1) | ~v1_relat_1(sK3)),
% 0.20/0.57    inference(resolution,[],[f105,f76])).
% 0.20/0.57  fof(f76,plain,(
% 0.20/0.57    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f49])).
% 0.20/0.57  fof(f49,plain,(
% 0.20/0.57    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.20/0.57    inference(nnf_transformation,[],[f34])).
% 0.20/0.57  fof(f34,plain,(
% 0.20/0.57    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.57    inference(ennf_transformation,[],[f1])).
% 0.20/0.57  fof(f1,axiom,(
% 0.20/0.57    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 0.20/0.57  fof(f105,plain,(
% 0.20/0.57    v4_relat_1(sK3,sK1)),
% 0.20/0.57    inference(resolution,[],[f80,f56])).
% 0.20/0.57  fof(f80,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f37])).
% 0.20/0.57  fof(f37,plain,(
% 0.20/0.57    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.57    inference(ennf_transformation,[],[f21])).
% 0.20/0.57  fof(f21,plain,(
% 0.20/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.20/0.57    inference(pure_predicate_removal,[],[f10])).
% 0.20/0.57  fof(f10,axiom,(
% 0.20/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.20/0.57  fof(f922,plain,(
% 0.20/0.57    k5_relat_1(k2_funct_1(sK2),k6_relat_1(sK0)) = k5_relat_1(k6_relat_1(sK1),sK3)),
% 0.20/0.57    inference(forward_demodulation,[],[f909,f132])).
% 0.20/0.57  fof(f132,plain,(
% 0.20/0.57    k6_relat_1(sK1) = k5_relat_1(k2_funct_1(sK2),sK2)),
% 0.20/0.57    inference(forward_demodulation,[],[f131,f122])).
% 0.20/0.57  fof(f122,plain,(
% 0.20/0.57    sK1 = k2_relat_1(sK2)),
% 0.20/0.57    inference(forward_demodulation,[],[f119,f57])).
% 0.20/0.57  fof(f57,plain,(
% 0.20/0.57    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.20/0.57    inference(cnf_transformation,[],[f48])).
% 0.20/0.57  fof(f119,plain,(
% 0.20/0.57    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 0.20/0.57    inference(resolution,[],[f79,f53])).
% 0.20/0.57  fof(f53,plain,(
% 0.20/0.57    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.57    inference(cnf_transformation,[],[f48])).
% 0.20/0.57  fof(f79,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f36])).
% 0.20/0.57  fof(f36,plain,(
% 0.20/0.57    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.57    inference(ennf_transformation,[],[f11])).
% 0.20/0.57  fof(f11,axiom,(
% 0.20/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.20/0.57  fof(f131,plain,(
% 0.20/0.57    k6_relat_1(k2_relat_1(sK2)) = k5_relat_1(k2_funct_1(sK2),sK2)),
% 0.20/0.57    inference(subsumption_resolution,[],[f130,f98])).
% 0.20/0.57  fof(f98,plain,(
% 0.20/0.57    v1_relat_1(sK2)),
% 0.20/0.57    inference(resolution,[],[f78,f53])).
% 0.20/0.57  fof(f130,plain,(
% 0.20/0.57    k6_relat_1(k2_relat_1(sK2)) = k5_relat_1(k2_funct_1(sK2),sK2) | ~v1_relat_1(sK2)),
% 0.20/0.57    inference(subsumption_resolution,[],[f129,f51])).
% 0.20/0.57  fof(f51,plain,(
% 0.20/0.57    v1_funct_1(sK2)),
% 0.20/0.57    inference(cnf_transformation,[],[f48])).
% 0.20/0.57  fof(f129,plain,(
% 0.20/0.57    k6_relat_1(k2_relat_1(sK2)) = k5_relat_1(k2_funct_1(sK2),sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.20/0.57    inference(resolution,[],[f74,f59])).
% 0.20/0.57  fof(f59,plain,(
% 0.20/0.57    v2_funct_1(sK2)),
% 0.20/0.57    inference(cnf_transformation,[],[f48])).
% 0.20/0.57  fof(f74,plain,(
% 0.20/0.57    ( ! [X0] : (~v2_funct_1(X0) | k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f31])).
% 0.20/0.57  fof(f31,plain,(
% 0.20/0.57    ! [X0] : ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.57    inference(flattening,[],[f30])).
% 0.20/0.57  fof(f30,plain,(
% 0.20/0.57    ! [X0] : (((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.57    inference(ennf_transformation,[],[f8])).
% 0.20/0.57  fof(f8,axiom,(
% 0.20/0.57    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).
% 0.20/0.57  fof(f909,plain,(
% 0.20/0.57    k5_relat_1(k2_funct_1(sK2),k6_relat_1(sK0)) = k5_relat_1(k5_relat_1(k2_funct_1(sK2),sK2),sK3)),
% 0.20/0.57    inference(resolution,[],[f466,f174])).
% 0.20/0.57  fof(f174,plain,(
% 0.20/0.57    v1_relat_1(k2_funct_1(sK2))),
% 0.20/0.57    inference(resolution,[],[f94,f98])).
% 0.20/0.57  fof(f94,plain,(
% 0.20/0.57    ~v1_relat_1(sK2) | v1_relat_1(k2_funct_1(sK2))),
% 0.20/0.57    inference(resolution,[],[f69,f51])).
% 0.20/0.57  fof(f69,plain,(
% 0.20/0.57    ( ! [X0] : (~v1_funct_1(X0) | v1_relat_1(k2_funct_1(X0)) | ~v1_relat_1(X0)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f27])).
% 0.20/0.57  fof(f27,plain,(
% 0.20/0.57    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.57    inference(flattening,[],[f26])).
% 0.20/0.57  fof(f26,plain,(
% 0.20/0.57    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.57    inference(ennf_transformation,[],[f6])).
% 0.20/0.57  fof(f6,axiom,(
% 0.20/0.57    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.20/0.57  fof(f466,plain,(
% 0.20/0.57    ( ! [X4] : (~v1_relat_1(X4) | k5_relat_1(X4,k6_relat_1(sK0)) = k5_relat_1(k5_relat_1(X4,sK2),sK3)) )),
% 0.20/0.57    inference(forward_demodulation,[],[f464,f356])).
% 0.20/0.57  fof(f356,plain,(
% 0.20/0.57    k6_relat_1(sK0) = k5_relat_1(sK2,sK3)),
% 0.20/0.57    inference(resolution,[],[f243,f224])).
% 0.20/0.57  fof(f224,plain,(
% 0.20/0.57    ~m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k6_relat_1(sK0) = k5_relat_1(sK2,sK3)),
% 0.20/0.57    inference(forward_demodulation,[],[f222,f220])).
% 0.20/0.57  fof(f220,plain,(
% 0.20/0.57    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)),
% 0.20/0.57    inference(subsumption_resolution,[],[f217,f51])).
% 0.20/0.57  fof(f217,plain,(
% 0.20/0.57    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) | ~v1_funct_1(sK2)),
% 0.20/0.57    inference(resolution,[],[f146,f53])).
% 0.20/0.57  fof(f146,plain,(
% 0.20/0.57    ( ! [X4,X5,X3] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | k1_partfun1(X3,X4,sK1,sK0,X5,sK3) = k5_relat_1(X5,sK3) | ~v1_funct_1(X5)) )),
% 0.20/0.57    inference(subsumption_resolution,[],[f143,f54])).
% 0.20/0.57  fof(f54,plain,(
% 0.20/0.57    v1_funct_1(sK3)),
% 0.20/0.57    inference(cnf_transformation,[],[f48])).
% 0.20/0.57  fof(f143,plain,(
% 0.20/0.57    ( ! [X4,X5,X3] : (k1_partfun1(X3,X4,sK1,sK0,X5,sK3) = k5_relat_1(X5,sK3) | ~v1_funct_1(sK3) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_1(X5)) )),
% 0.20/0.57    inference(resolution,[],[f85,f56])).
% 0.20/0.57  fof(f85,plain,(
% 0.20/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f43])).
% 0.20/0.57  fof(f43,plain,(
% 0.20/0.57    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 0.20/0.57    inference(flattening,[],[f42])).
% 0.20/0.57  fof(f42,plain,(
% 0.20/0.57    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 0.20/0.57    inference(ennf_transformation,[],[f15])).
% 0.20/0.57  fof(f15,axiom,(
% 0.20/0.57    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 0.20/0.57  fof(f222,plain,(
% 0.20/0.57    ~m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0)),
% 0.20/0.57    inference(backward_demodulation,[],[f136,f220])).
% 0.20/0.57  fof(f136,plain,(
% 0.20/0.57    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0) | ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.20/0.57    inference(subsumption_resolution,[],[f135,f91])).
% 0.20/0.57  fof(f91,plain,(
% 0.20/0.57    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.20/0.57    inference(forward_demodulation,[],[f64,f63])).
% 0.20/0.57  fof(f63,plain,(
% 0.20/0.57    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f16])).
% 0.20/0.57  fof(f16,axiom,(
% 0.20/0.57    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 0.20/0.57  fof(f64,plain,(
% 0.20/0.57    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.20/0.57    inference(cnf_transformation,[],[f20])).
% 0.20/0.57  fof(f20,plain,(
% 0.20/0.57    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 0.20/0.57    inference(pure_predicate_removal,[],[f14])).
% 0.20/0.57  fof(f14,axiom,(
% 0.20/0.57    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 0.20/0.57  fof(f135,plain,(
% 0.20/0.57    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0) | ~m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.20/0.57    inference(resolution,[],[f83,f90])).
% 0.20/0.57  fof(f90,plain,(
% 0.20/0.57    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0))),
% 0.20/0.57    inference(forward_demodulation,[],[f58,f63])).
% 0.20/0.57  fof(f58,plain,(
% 0.20/0.57    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 0.20/0.57    inference(cnf_transformation,[],[f48])).
% 0.20/0.57  fof(f83,plain,(
% 0.20/0.57    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.57    inference(cnf_transformation,[],[f50])).
% 0.20/0.57  fof(f50,plain,(
% 0.20/0.57    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.57    inference(nnf_transformation,[],[f41])).
% 0.20/0.57  fof(f41,plain,(
% 0.20/0.57    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.57    inference(flattening,[],[f40])).
% 0.20/0.57  fof(f40,plain,(
% 0.20/0.57    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.20/0.57    inference(ennf_transformation,[],[f12])).
% 0.20/0.57  fof(f12,axiom,(
% 0.20/0.57    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 0.20/0.57  fof(f243,plain,(
% 0.20/0.57    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.20/0.57    inference(forward_demodulation,[],[f242,f220])).
% 0.20/0.57  fof(f242,plain,(
% 0.20/0.57    m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.20/0.57    inference(subsumption_resolution,[],[f239,f51])).
% 0.20/0.57  fof(f239,plain,(
% 0.20/0.57    m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK2)),
% 0.20/0.57    inference(resolution,[],[f151,f53])).
% 0.20/0.57  fof(f151,plain,(
% 0.20/0.57    ( ! [X4,X5,X3] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | m1_subset_1(k1_partfun1(X3,X4,sK1,sK0,X5,sK3),k1_zfmisc_1(k2_zfmisc_1(X3,sK0))) | ~v1_funct_1(X5)) )),
% 0.20/0.57    inference(subsumption_resolution,[],[f148,f54])).
% 0.20/0.57  fof(f148,plain,(
% 0.20/0.57    ( ! [X4,X5,X3] : (m1_subset_1(k1_partfun1(X3,X4,sK1,sK0,X5,sK3),k1_zfmisc_1(k2_zfmisc_1(X3,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_1(X5)) )),
% 0.20/0.57    inference(resolution,[],[f87,f56])).
% 0.20/0.57  fof(f87,plain,(
% 0.20/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f45])).
% 0.20/0.57  fof(f45,plain,(
% 0.20/0.57    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 0.20/0.57    inference(flattening,[],[f44])).
% 0.20/0.57  fof(f44,plain,(
% 0.20/0.57    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 0.20/0.57    inference(ennf_transformation,[],[f13])).
% 0.20/0.57  fof(f13,axiom,(
% 0.20/0.57    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 0.20/0.57  fof(f464,plain,(
% 0.20/0.57    ( ! [X4] : (k5_relat_1(X4,k5_relat_1(sK2,sK3)) = k5_relat_1(k5_relat_1(X4,sK2),sK3) | ~v1_relat_1(X4)) )),
% 0.20/0.57    inference(resolution,[],[f134,f98])).
% 0.20/0.57  fof(f134,plain,(
% 0.20/0.57    ( ! [X2,X3] : (~v1_relat_1(X3) | k5_relat_1(k5_relat_1(X2,X3),sK3) = k5_relat_1(X2,k5_relat_1(X3,sK3)) | ~v1_relat_1(X2)) )),
% 0.20/0.57    inference(resolution,[],[f68,f99])).
% 0.20/0.57  fof(f68,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f25])).
% 0.20/0.57  fof(f25,plain,(
% 0.20/0.57    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.57    inference(ennf_transformation,[],[f2])).
% 0.20/0.57  fof(f2,axiom,(
% 0.20/0.57    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)))))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).
% 0.20/0.57  fof(f181,plain,(
% 0.20/0.57    k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_relat_1(sK0))),
% 0.20/0.57    inference(forward_demodulation,[],[f180,f167])).
% 0.20/0.57  fof(f167,plain,(
% 0.20/0.57    k6_relat_1(sK0) = k6_relat_1(k1_relat_1(sK2))),
% 0.20/0.57    inference(backward_demodulation,[],[f128,f166])).
% 0.20/0.57  fof(f166,plain,(
% 0.20/0.57    k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 0.20/0.57    inference(subsumption_resolution,[],[f165,f51])).
% 0.20/0.57  fof(f165,plain,(
% 0.20/0.57    k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~v1_funct_1(sK2)),
% 0.20/0.57    inference(subsumption_resolution,[],[f164,f53])).
% 0.20/0.57  fof(f164,plain,(
% 0.20/0.57    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~v1_funct_1(sK2)),
% 0.20/0.57    inference(subsumption_resolution,[],[f163,f57])).
% 0.20/0.57  fof(f163,plain,(
% 0.20/0.57    sK1 != k2_relset_1(sK0,sK1,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~v1_funct_1(sK2)),
% 0.20/0.57    inference(subsumption_resolution,[],[f162,f59])).
% 0.20/0.57  fof(f162,plain,(
% 0.20/0.57    ~v2_funct_1(sK2) | sK1 != k2_relset_1(sK0,sK1,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~v1_funct_1(sK2)),
% 0.20/0.57    inference(subsumption_resolution,[],[f160,f61])).
% 0.20/0.57  fof(f61,plain,(
% 0.20/0.57    k1_xboole_0 != sK1),
% 0.20/0.57    inference(cnf_transformation,[],[f48])).
% 0.20/0.57  fof(f160,plain,(
% 0.20/0.57    k1_xboole_0 = sK1 | ~v2_funct_1(sK2) | sK1 != k2_relset_1(sK0,sK1,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~v1_funct_1(sK2)),
% 0.20/0.57    inference(resolution,[],[f93,f52])).
% 0.20/0.57  fof(f52,plain,(
% 0.20/0.57    v1_funct_2(sK2,sK0,sK1)),
% 0.20/0.57    inference(cnf_transformation,[],[f48])).
% 0.20/0.57  fof(f93,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k6_relat_1(X0) = k5_relat_1(X2,k2_funct_1(X2)) | ~v1_funct_1(X2)) )),
% 0.20/0.57    inference(forward_demodulation,[],[f81,f63])).
% 0.20/0.57  fof(f81,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f39])).
% 0.20/0.57  fof(f39,plain,(
% 0.20/0.57    ! [X0,X1,X2] : ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.20/0.58    inference(flattening,[],[f38])).
% 0.20/0.58  fof(f38,plain,(
% 0.20/0.58    ! [X0,X1,X2] : ((((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.20/0.58    inference(ennf_transformation,[],[f17])).
% 0.20/0.58  fof(f17,axiom,(
% 0.20/0.58    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1)))),
% 0.20/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_2)).
% 0.20/0.58  fof(f128,plain,(
% 0.20/0.58    k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2))),
% 0.20/0.58    inference(subsumption_resolution,[],[f127,f98])).
% 0.20/0.58  fof(f127,plain,(
% 0.20/0.58    k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2)) | ~v1_relat_1(sK2)),
% 0.20/0.58    inference(subsumption_resolution,[],[f126,f51])).
% 0.20/0.58  fof(f126,plain,(
% 0.20/0.58    k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.20/0.58    inference(resolution,[],[f73,f59])).
% 0.20/0.58  fof(f73,plain,(
% 0.20/0.58    ( ! [X0] : (~v2_funct_1(X0) | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f31])).
% 0.20/0.58  fof(f180,plain,(
% 0.20/0.58    k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_relat_1(k1_relat_1(sK2)))),
% 0.20/0.58    inference(forward_demodulation,[],[f179,f115])).
% 0.20/0.58  fof(f115,plain,(
% 0.20/0.58    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 0.20/0.58    inference(subsumption_resolution,[],[f114,f98])).
% 0.20/0.58  fof(f114,plain,(
% 0.20/0.58    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 0.20/0.58    inference(subsumption_resolution,[],[f113,f51])).
% 0.20/0.58  fof(f113,plain,(
% 0.20/0.58    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.20/0.58    inference(resolution,[],[f72,f59])).
% 0.20/0.58  fof(f72,plain,(
% 0.20/0.58    ( ! [X0] : (~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f29])).
% 0.20/0.58  fof(f29,plain,(
% 0.20/0.58    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.58    inference(flattening,[],[f28])).
% 0.20/0.58  fof(f28,plain,(
% 0.20/0.58    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.58    inference(ennf_transformation,[],[f7])).
% 0.20/0.58  fof(f7,axiom,(
% 0.20/0.58    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.20/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 0.20/0.58  fof(f179,plain,(
% 0.20/0.58    k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_relat_1(k2_relat_1(k2_funct_1(sK2))))),
% 0.20/0.58    inference(resolution,[],[f174,f67])).
% 0.20/0.58  fof(f67,plain,(
% 0.20/0.58    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0) )),
% 0.20/0.58    inference(cnf_transformation,[],[f24])).
% 0.20/0.58  fof(f24,plain,(
% 0.20/0.58    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 0.20/0.58    inference(ennf_transformation,[],[f5])).
% 0.20/0.58  fof(f5,axiom,(
% 0.20/0.58    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 0.20/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).
% 0.20/0.58  % SZS output end Proof for theBenchmark
% 0.20/0.58  % (23930)------------------------------
% 0.20/0.58  % (23930)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.58  % (23930)Termination reason: Refutation
% 0.20/0.58  
% 0.20/0.58  % (23930)Memory used [KB]: 2686
% 0.20/0.58  % (23930)Time elapsed: 0.165 s
% 0.20/0.58  % (23930)------------------------------
% 0.20/0.58  % (23930)------------------------------
% 0.20/0.58  % (23922)Success in time 0.221 s
%------------------------------------------------------------------------------
