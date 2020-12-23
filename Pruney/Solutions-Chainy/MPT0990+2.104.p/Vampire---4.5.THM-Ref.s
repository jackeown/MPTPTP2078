%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:46 EST 2020

% Result     : Theorem 2.08s
% Output     : Refutation 2.08s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 479 expanded)
%              Number of leaves         :   21 ( 146 expanded)
%              Depth                    :   23
%              Number of atoms          :  411 (3929 expanded)
%              Number of equality atoms :  114 (1296 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1805,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f241,f1804])).

fof(f1804,plain,(
    ~ spl4_7 ),
    inference(avatar_contradiction_clause,[],[f1803])).

fof(f1803,plain,
    ( $false
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f1802,f205])).

fof(f205,plain,(
    sK3 != k4_relat_1(sK2) ),
    inference(superposition,[],[f71,f203])).

fof(f203,plain,(
    k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f202,f121])).

fof(f121,plain,(
    v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f118,f91])).

fof(f91,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f118,plain,
    ( v1_relat_1(sK2)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f83,f62])).

fof(f62,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f27,f54,f53])).

fof(f53,plain,
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

fof(f54,plain,
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

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f25])).

fof(f25,negated_conjecture,(
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
    inference(negated_conjecture,[],[f24])).

fof(f24,conjecture,(
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

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f202,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f201,f60])).

fof(f60,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f55])).

fof(f201,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f86,f68])).

fof(f68,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f55])).

fof(f86,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

fof(f71,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f55])).

fof(f1802,plain,
    ( sK3 = k4_relat_1(sK2)
    | ~ spl4_7 ),
    inference(forward_demodulation,[],[f1801,f471])).

fof(f471,plain,(
    sK3 = k5_relat_1(k6_partfun1(sK1),sK3) ),
    inference(subsumption_resolution,[],[f467,f122])).

fof(f122,plain,(
    v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f119,f91])).

fof(f119,plain,
    ( v1_relat_1(sK3)
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(resolution,[],[f83,f65])).

fof(f65,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f55])).

fof(f467,plain,
    ( ~ v1_relat_1(sK3)
    | sK3 = k5_relat_1(k6_partfun1(sK1),sK3) ),
    inference(resolution,[],[f254,f170])).

fof(f170,plain,(
    v4_relat_1(sK3,sK1) ),
    inference(resolution,[],[f99,f65])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f254,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1)
      | k5_relat_1(k6_partfun1(X0),X1) = X1 ) ),
    inference(duplicate_literal_removal,[],[f250])).

fof(f250,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_partfun1(X0),X1) = X1
      | ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f112,f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f112,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X1),X0)
      | k5_relat_1(k6_partfun1(X0),X1) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f92,f72])).

fof(f72,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f92,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k5_relat_1(k6_relat_1(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).

fof(f1801,plain,
    ( k4_relat_1(sK2) = k5_relat_1(k6_partfun1(sK1),sK3)
    | ~ spl4_7 ),
    inference(forward_demodulation,[],[f1800,f547])).

fof(f547,plain,(
    k4_relat_1(sK2) = k5_relat_1(k4_relat_1(sK2),k6_partfun1(sK0)) ),
    inference(superposition,[],[f398,f470])).

fof(f470,plain,(
    sK2 = k5_relat_1(k6_partfun1(sK0),sK2) ),
    inference(subsumption_resolution,[],[f466,f121])).

fof(f466,plain,
    ( ~ v1_relat_1(sK2)
    | sK2 = k5_relat_1(k6_partfun1(sK0),sK2) ),
    inference(resolution,[],[f254,f169])).

fof(f169,plain,(
    v4_relat_1(sK2,sK0) ),
    inference(resolution,[],[f99,f62])).

fof(f398,plain,(
    ! [X4] : k4_relat_1(k5_relat_1(k6_partfun1(X4),sK2)) = k5_relat_1(k4_relat_1(sK2),k6_partfun1(X4)) ),
    inference(forward_demodulation,[],[f393,f106])).

fof(f106,plain,(
    ! [X0] : k6_partfun1(X0) = k4_relat_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f73,f72,f72])).

fof(f73,plain,(
    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_relat_1)).

fof(f393,plain,(
    ! [X4] : k4_relat_1(k5_relat_1(k6_partfun1(X4),sK2)) = k5_relat_1(k4_relat_1(sK2),k4_relat_1(k6_partfun1(X4))) ),
    inference(resolution,[],[f286,f123])).

fof(f123,plain,(
    ! [X0] : v1_relat_1(k6_partfun1(X0)) ),
    inference(subsumption_resolution,[],[f120,f91])).

fof(f120,plain,(
    ! [X0] :
      ( v1_relat_1(k6_partfun1(X0))
      | ~ v1_relat_1(k2_zfmisc_1(X0,X0)) ) ),
    inference(resolution,[],[f83,f75])).

fof(f75,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f286,plain,(
    ! [X10] :
      ( ~ v1_relat_1(X10)
      | k4_relat_1(k5_relat_1(X10,sK2)) = k5_relat_1(k4_relat_1(sK2),k4_relat_1(X10)) ) ),
    inference(resolution,[],[f81,f121])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_relat_1)).

fof(f1800,plain,
    ( k5_relat_1(k6_partfun1(sK1),sK3) = k5_relat_1(k4_relat_1(sK2),k6_partfun1(sK0))
    | ~ spl4_7 ),
    inference(forward_demodulation,[],[f1787,f302])).

fof(f302,plain,(
    k6_partfun1(sK1) = k5_relat_1(k4_relat_1(sK2),sK2) ),
    inference(forward_demodulation,[],[f301,f265])).

fof(f265,plain,(
    sK1 = k2_relat_1(sK2) ),
    inference(forward_demodulation,[],[f262,f66])).

fof(f66,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f55])).

fof(f262,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f98,f62])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f301,plain,(
    k6_partfun1(k2_relat_1(sK2)) = k5_relat_1(k4_relat_1(sK2),sK2) ),
    inference(forward_demodulation,[],[f300,f203])).

fof(f300,plain,(
    k6_partfun1(k2_relat_1(sK2)) = k5_relat_1(k2_funct_1(sK2),sK2) ),
    inference(subsumption_resolution,[],[f299,f121])).

fof(f299,plain,
    ( k6_partfun1(k2_relat_1(sK2)) = k5_relat_1(k2_funct_1(sK2),sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f298,f60])).

fof(f298,plain,
    ( k6_partfun1(k2_relat_1(sK2)) = k5_relat_1(k2_funct_1(sK2),sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f110,f68])).

fof(f110,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f90,f72])).

fof(f90,plain,(
    ! [X0] :
      ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

fof(f1787,plain,
    ( k5_relat_1(k4_relat_1(sK2),k6_partfun1(sK0)) = k5_relat_1(k5_relat_1(k4_relat_1(sK2),sK2),sK3)
    | ~ spl4_7 ),
    inference(resolution,[],[f1681,f224])).

fof(f224,plain,
    ( v1_relat_1(k4_relat_1(sK2))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f223])).

fof(f223,plain,
    ( spl4_7
  <=> v1_relat_1(k4_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f1681,plain,(
    ! [X27] :
      ( ~ v1_relat_1(X27)
      | k5_relat_1(k5_relat_1(X27,sK2),sK3) = k5_relat_1(X27,k6_partfun1(sK0)) ) ),
    inference(forward_demodulation,[],[f1679,f1001])).

fof(f1001,plain,(
    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) ),
    inference(global_subsumption,[],[f980,f1000])).

fof(f1000,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f974,f348])).

fof(f348,plain,(
    ! [X2,X3] :
      ( ~ r2_relset_1(X2,X2,X3,k6_partfun1(X2))
      | k6_partfun1(X2) = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ) ),
    inference(resolution,[],[f101,f75])).

fof(f101,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f974,plain,(
    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0)) ),
    inference(backward_demodulation,[],[f67,f716])).

fof(f716,plain,(
    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f713,f60])).

fof(f713,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f387,f62])).

fof(f387,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | k1_partfun1(X3,X4,sK1,sK0,X5,sK3) = k5_relat_1(X5,sK3)
      | ~ v1_funct_1(X5) ) ),
    inference(subsumption_resolution,[],[f384,f63])).

fof(f63,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f55])).

fof(f384,plain,(
    ! [X4,X5,X3] :
      ( k1_partfun1(X3,X4,sK1,sK0,X5,sK3) = k5_relat_1(X5,sK3)
      | ~ v1_funct_1(sK3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_1(X5) ) ),
    inference(resolution,[],[f103,f65])).

fof(f103,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f67,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f55])).

fof(f980,plain,(
    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subsumption_resolution,[],[f979,f60])).

fof(f979,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f978,f62])).

fof(f978,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f977,f63])).

fof(f977,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f975,f65])).

fof(f975,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(superposition,[],[f105,f716])).

fof(f105,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
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
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f1679,plain,(
    ! [X27] :
      ( k5_relat_1(k5_relat_1(X27,sK2),sK3) = k5_relat_1(X27,k5_relat_1(sK2,sK3))
      | ~ v1_relat_1(X27) ) ),
    inference(resolution,[],[f331,f121])).

fof(f331,plain,(
    ! [X17,X18] :
      ( ~ v1_relat_1(X18)
      | k5_relat_1(k5_relat_1(X17,X18),sK3) = k5_relat_1(X17,k5_relat_1(X18,sK3))
      | ~ v1_relat_1(X17) ) ),
    inference(resolution,[],[f82,f122])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

fof(f241,plain,(
    spl4_7 ),
    inference(avatar_contradiction_clause,[],[f240])).

fof(f240,plain,
    ( $false
    | spl4_7 ),
    inference(subsumption_resolution,[],[f239,f121])).

fof(f239,plain,
    ( ~ v1_relat_1(sK2)
    | spl4_7 ),
    inference(resolution,[],[f225,f78])).

fof(f78,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(f225,plain,
    ( ~ v1_relat_1(k4_relat_1(sK2))
    | spl4_7 ),
    inference(avatar_component_clause,[],[f223])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:00:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.50  % (26701)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.51  % (26696)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.51  % (26723)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.51  % (26714)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.52  % (26705)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.52  % (26697)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.53  % (26707)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.53  % (26692)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.53  % (26694)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.54  % (26700)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.54  % (26725)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.54  % (26709)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.54  % (26716)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.54  % (26703)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.54  % (26711)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.54  % (26724)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.55  % (26698)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.55  % (26699)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.55  % (26719)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.55  % (26704)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.55  % (26715)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.55  % (26710)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.56  % (26706)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.56  % (26695)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.56  % (26709)Refutation not found, incomplete strategy% (26709)------------------------------
% 0.22/0.56  % (26709)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (26709)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (26709)Memory used [KB]: 10746
% 0.22/0.56  % (26709)Time elapsed: 0.157 s
% 0.22/0.56  % (26709)------------------------------
% 0.22/0.56  % (26709)------------------------------
% 0.22/0.56  % (26722)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.56  % (26717)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.57  % (26708)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.57  % (26720)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.58  % (26712)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.58  % (26702)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 2.08/0.65  % (26699)Refutation found. Thanks to Tanya!
% 2.08/0.65  % SZS status Theorem for theBenchmark
% 2.08/0.66  % SZS output start Proof for theBenchmark
% 2.08/0.66  fof(f1805,plain,(
% 2.08/0.66    $false),
% 2.08/0.66    inference(avatar_sat_refutation,[],[f241,f1804])).
% 2.08/0.66  fof(f1804,plain,(
% 2.08/0.66    ~spl4_7),
% 2.08/0.66    inference(avatar_contradiction_clause,[],[f1803])).
% 2.08/0.66  fof(f1803,plain,(
% 2.08/0.66    $false | ~spl4_7),
% 2.08/0.66    inference(subsumption_resolution,[],[f1802,f205])).
% 2.08/0.66  fof(f205,plain,(
% 2.08/0.66    sK3 != k4_relat_1(sK2)),
% 2.08/0.66    inference(superposition,[],[f71,f203])).
% 2.08/0.66  fof(f203,plain,(
% 2.08/0.66    k2_funct_1(sK2) = k4_relat_1(sK2)),
% 2.08/0.66    inference(subsumption_resolution,[],[f202,f121])).
% 2.08/0.66  fof(f121,plain,(
% 2.08/0.66    v1_relat_1(sK2)),
% 2.08/0.66    inference(subsumption_resolution,[],[f118,f91])).
% 2.08/0.66  fof(f91,plain,(
% 2.08/0.66    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.08/0.66    inference(cnf_transformation,[],[f5])).
% 2.08/0.66  fof(f5,axiom,(
% 2.08/0.66    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.08/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 2.08/0.66  fof(f118,plain,(
% 2.08/0.66    v1_relat_1(sK2) | ~v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 2.08/0.66    inference(resolution,[],[f83,f62])).
% 2.08/0.66  fof(f62,plain,(
% 2.08/0.66    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.08/0.66    inference(cnf_transformation,[],[f55])).
% 2.08/0.66  fof(f55,plain,(
% 2.08/0.66    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 2.08/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f27,f54,f53])).
% 2.08/0.66  fof(f53,plain,(
% 2.08/0.66    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 2.08/0.66    introduced(choice_axiom,[])).
% 2.08/0.66  fof(f54,plain,(
% 2.08/0.66    ? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) => (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3))),
% 2.08/0.66    introduced(choice_axiom,[])).
% 2.08/0.66  fof(f27,plain,(
% 2.08/0.66    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.08/0.66    inference(flattening,[],[f26])).
% 2.08/0.66  fof(f26,plain,(
% 2.08/0.66    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.08/0.66    inference(ennf_transformation,[],[f25])).
% 2.08/0.66  fof(f25,negated_conjecture,(
% 2.08/0.66    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 2.08/0.66    inference(negated_conjecture,[],[f24])).
% 2.08/0.66  fof(f24,conjecture,(
% 2.08/0.66    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 2.08/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).
% 2.08/0.66  fof(f83,plain,(
% 2.08/0.66    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.08/0.66    inference(cnf_transformation,[],[f33])).
% 2.08/0.66  fof(f33,plain,(
% 2.08/0.66    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.08/0.66    inference(ennf_transformation,[],[f2])).
% 2.08/0.66  fof(f2,axiom,(
% 2.08/0.66    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.08/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 2.08/0.66  fof(f202,plain,(
% 2.08/0.66    k2_funct_1(sK2) = k4_relat_1(sK2) | ~v1_relat_1(sK2)),
% 2.08/0.66    inference(subsumption_resolution,[],[f201,f60])).
% 2.08/0.66  fof(f60,plain,(
% 2.08/0.66    v1_funct_1(sK2)),
% 2.08/0.66    inference(cnf_transformation,[],[f55])).
% 2.08/0.66  fof(f201,plain,(
% 2.08/0.66    k2_funct_1(sK2) = k4_relat_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 2.08/0.66    inference(resolution,[],[f86,f68])).
% 2.08/0.66  fof(f68,plain,(
% 2.08/0.66    v2_funct_1(sK2)),
% 2.08/0.66    inference(cnf_transformation,[],[f55])).
% 2.08/0.66  fof(f86,plain,(
% 2.08/0.66    ( ! [X0] : (~v2_funct_1(X0) | k4_relat_1(X0) = k2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.08/0.66    inference(cnf_transformation,[],[f37])).
% 2.08/0.66  fof(f37,plain,(
% 2.08/0.66    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.08/0.66    inference(flattening,[],[f36])).
% 2.08/0.66  fof(f36,plain,(
% 2.08/0.66    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.08/0.66    inference(ennf_transformation,[],[f13])).
% 2.08/0.66  fof(f13,axiom,(
% 2.08/0.66    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 2.08/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).
% 2.08/0.66  fof(f71,plain,(
% 2.08/0.66    k2_funct_1(sK2) != sK3),
% 2.08/0.66    inference(cnf_transformation,[],[f55])).
% 2.08/0.66  fof(f1802,plain,(
% 2.08/0.66    sK3 = k4_relat_1(sK2) | ~spl4_7),
% 2.08/0.66    inference(forward_demodulation,[],[f1801,f471])).
% 2.08/0.66  fof(f471,plain,(
% 2.08/0.66    sK3 = k5_relat_1(k6_partfun1(sK1),sK3)),
% 2.08/0.66    inference(subsumption_resolution,[],[f467,f122])).
% 2.08/0.66  fof(f122,plain,(
% 2.08/0.66    v1_relat_1(sK3)),
% 2.08/0.66    inference(subsumption_resolution,[],[f119,f91])).
% 2.08/0.66  fof(f119,plain,(
% 2.08/0.66    v1_relat_1(sK3) | ~v1_relat_1(k2_zfmisc_1(sK1,sK0))),
% 2.08/0.66    inference(resolution,[],[f83,f65])).
% 2.08/0.66  fof(f65,plain,(
% 2.08/0.66    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.08/0.66    inference(cnf_transformation,[],[f55])).
% 2.08/0.66  fof(f467,plain,(
% 2.08/0.66    ~v1_relat_1(sK3) | sK3 = k5_relat_1(k6_partfun1(sK1),sK3)),
% 2.08/0.66    inference(resolution,[],[f254,f170])).
% 2.08/0.66  fof(f170,plain,(
% 2.08/0.66    v4_relat_1(sK3,sK1)),
% 2.08/0.66    inference(resolution,[],[f99,f65])).
% 2.08/0.66  fof(f99,plain,(
% 2.08/0.66    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 2.08/0.66    inference(cnf_transformation,[],[f46])).
% 2.08/0.66  fof(f46,plain,(
% 2.08/0.66    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.08/0.66    inference(ennf_transformation,[],[f17])).
% 2.08/0.66  fof(f17,axiom,(
% 2.08/0.66    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.08/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 2.08/0.66  fof(f254,plain,(
% 2.08/0.66    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | ~v1_relat_1(X1) | k5_relat_1(k6_partfun1(X0),X1) = X1) )),
% 2.08/0.66    inference(duplicate_literal_removal,[],[f250])).
% 2.08/0.66  fof(f250,plain,(
% 2.08/0.66    ( ! [X0,X1] : (k5_relat_1(k6_partfun1(X0),X1) = X1 | ~v1_relat_1(X1) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.08/0.66    inference(resolution,[],[f112,f93])).
% 2.08/0.66  fof(f93,plain,(
% 2.08/0.66    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.08/0.66    inference(cnf_transformation,[],[f56])).
% 2.08/0.66  fof(f56,plain,(
% 2.08/0.66    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.08/0.66    inference(nnf_transformation,[],[f44])).
% 2.08/0.66  fof(f44,plain,(
% 2.08/0.66    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.08/0.66    inference(ennf_transformation,[],[f3])).
% 2.08/0.66  fof(f3,axiom,(
% 2.08/0.66    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 2.08/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 2.08/0.66  fof(f112,plain,(
% 2.08/0.66    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X1),X0) | k5_relat_1(k6_partfun1(X0),X1) = X1 | ~v1_relat_1(X1)) )),
% 2.08/0.66    inference(definition_unfolding,[],[f92,f72])).
% 2.08/0.66  fof(f72,plain,(
% 2.08/0.66    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 2.08/0.66    inference(cnf_transformation,[],[f23])).
% 2.08/0.66  fof(f23,axiom,(
% 2.08/0.66    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 2.08/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 2.08/0.66  fof(f92,plain,(
% 2.08/0.66    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 2.08/0.66    inference(cnf_transformation,[],[f43])).
% 2.08/0.66  fof(f43,plain,(
% 2.08/0.66    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 2.08/0.66    inference(flattening,[],[f42])).
% 2.08/0.66  fof(f42,plain,(
% 2.08/0.66    ! [X0,X1] : ((k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.08/0.66    inference(ennf_transformation,[],[f11])).
% 2.08/0.66  fof(f11,axiom,(
% 2.08/0.66    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k5_relat_1(k6_relat_1(X0),X1) = X1))),
% 2.08/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).
% 2.08/0.66  fof(f1801,plain,(
% 2.08/0.66    k4_relat_1(sK2) = k5_relat_1(k6_partfun1(sK1),sK3) | ~spl4_7),
% 2.08/0.66    inference(forward_demodulation,[],[f1800,f547])).
% 2.08/0.66  fof(f547,plain,(
% 2.08/0.66    k4_relat_1(sK2) = k5_relat_1(k4_relat_1(sK2),k6_partfun1(sK0))),
% 2.08/0.66    inference(superposition,[],[f398,f470])).
% 2.08/0.67  fof(f470,plain,(
% 2.08/0.67    sK2 = k5_relat_1(k6_partfun1(sK0),sK2)),
% 2.08/0.67    inference(subsumption_resolution,[],[f466,f121])).
% 2.08/0.67  fof(f466,plain,(
% 2.08/0.67    ~v1_relat_1(sK2) | sK2 = k5_relat_1(k6_partfun1(sK0),sK2)),
% 2.08/0.67    inference(resolution,[],[f254,f169])).
% 2.08/0.67  fof(f169,plain,(
% 2.08/0.67    v4_relat_1(sK2,sK0)),
% 2.08/0.67    inference(resolution,[],[f99,f62])).
% 2.08/0.67  fof(f398,plain,(
% 2.08/0.67    ( ! [X4] : (k4_relat_1(k5_relat_1(k6_partfun1(X4),sK2)) = k5_relat_1(k4_relat_1(sK2),k6_partfun1(X4))) )),
% 2.08/0.67    inference(forward_demodulation,[],[f393,f106])).
% 2.08/0.67  fof(f106,plain,(
% 2.08/0.67    ( ! [X0] : (k6_partfun1(X0) = k4_relat_1(k6_partfun1(X0))) )),
% 2.08/0.67    inference(definition_unfolding,[],[f73,f72,f72])).
% 2.08/0.67  fof(f73,plain,(
% 2.08/0.67    ( ! [X0] : (k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))) )),
% 2.08/0.67    inference(cnf_transformation,[],[f10])).
% 2.08/0.67  fof(f10,axiom,(
% 2.08/0.67    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))),
% 2.08/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_relat_1)).
% 2.08/0.67  fof(f393,plain,(
% 2.08/0.67    ( ! [X4] : (k4_relat_1(k5_relat_1(k6_partfun1(X4),sK2)) = k5_relat_1(k4_relat_1(sK2),k4_relat_1(k6_partfun1(X4)))) )),
% 2.08/0.67    inference(resolution,[],[f286,f123])).
% 2.08/0.67  fof(f123,plain,(
% 2.08/0.67    ( ! [X0] : (v1_relat_1(k6_partfun1(X0))) )),
% 2.08/0.67    inference(subsumption_resolution,[],[f120,f91])).
% 2.08/0.67  fof(f120,plain,(
% 2.08/0.67    ( ! [X0] : (v1_relat_1(k6_partfun1(X0)) | ~v1_relat_1(k2_zfmisc_1(X0,X0))) )),
% 2.08/0.67    inference(resolution,[],[f83,f75])).
% 2.08/0.67  fof(f75,plain,(
% 2.08/0.67    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.08/0.67    inference(cnf_transformation,[],[f21])).
% 2.08/0.67  fof(f21,axiom,(
% 2.08/0.67    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 2.08/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 2.08/0.67  fof(f286,plain,(
% 2.08/0.67    ( ! [X10] : (~v1_relat_1(X10) | k4_relat_1(k5_relat_1(X10,sK2)) = k5_relat_1(k4_relat_1(sK2),k4_relat_1(X10))) )),
% 2.08/0.67    inference(resolution,[],[f81,f121])).
% 2.08/0.67  fof(f81,plain,(
% 2.08/0.67    ( ! [X0,X1] : (~v1_relat_1(X1) | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 2.08/0.67    inference(cnf_transformation,[],[f31])).
% 2.08/0.67  fof(f31,plain,(
% 2.08/0.67    ! [X0] : (! [X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.08/0.67    inference(ennf_transformation,[],[f7])).
% 2.08/0.67  fof(f7,axiom,(
% 2.08/0.67    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))))),
% 2.08/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_relat_1)).
% 2.08/0.67  fof(f1800,plain,(
% 2.08/0.67    k5_relat_1(k6_partfun1(sK1),sK3) = k5_relat_1(k4_relat_1(sK2),k6_partfun1(sK0)) | ~spl4_7),
% 2.08/0.67    inference(forward_demodulation,[],[f1787,f302])).
% 2.08/0.67  fof(f302,plain,(
% 2.08/0.67    k6_partfun1(sK1) = k5_relat_1(k4_relat_1(sK2),sK2)),
% 2.08/0.67    inference(forward_demodulation,[],[f301,f265])).
% 2.08/0.67  fof(f265,plain,(
% 2.08/0.67    sK1 = k2_relat_1(sK2)),
% 2.08/0.67    inference(forward_demodulation,[],[f262,f66])).
% 2.08/0.67  fof(f66,plain,(
% 2.08/0.67    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 2.08/0.67    inference(cnf_transformation,[],[f55])).
% 2.08/0.67  fof(f262,plain,(
% 2.08/0.67    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 2.08/0.67    inference(resolution,[],[f98,f62])).
% 2.08/0.67  fof(f98,plain,(
% 2.08/0.67    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 2.08/0.67    inference(cnf_transformation,[],[f45])).
% 2.08/0.67  fof(f45,plain,(
% 2.08/0.67    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.08/0.67    inference(ennf_transformation,[],[f18])).
% 2.08/0.67  fof(f18,axiom,(
% 2.08/0.67    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 2.08/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 2.08/0.67  fof(f301,plain,(
% 2.08/0.67    k6_partfun1(k2_relat_1(sK2)) = k5_relat_1(k4_relat_1(sK2),sK2)),
% 2.08/0.67    inference(forward_demodulation,[],[f300,f203])).
% 2.08/0.67  fof(f300,plain,(
% 2.08/0.67    k6_partfun1(k2_relat_1(sK2)) = k5_relat_1(k2_funct_1(sK2),sK2)),
% 2.08/0.67    inference(subsumption_resolution,[],[f299,f121])).
% 2.08/0.67  fof(f299,plain,(
% 2.08/0.67    k6_partfun1(k2_relat_1(sK2)) = k5_relat_1(k2_funct_1(sK2),sK2) | ~v1_relat_1(sK2)),
% 2.08/0.67    inference(subsumption_resolution,[],[f298,f60])).
% 2.08/0.67  fof(f298,plain,(
% 2.08/0.67    k6_partfun1(k2_relat_1(sK2)) = k5_relat_1(k2_funct_1(sK2),sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 2.08/0.67    inference(resolution,[],[f110,f68])).
% 2.08/0.67  fof(f110,plain,(
% 2.08/0.67    ( ! [X0] : (~v2_funct_1(X0) | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.08/0.67    inference(definition_unfolding,[],[f90,f72])).
% 2.08/0.67  fof(f90,plain,(
% 2.08/0.67    ( ! [X0] : (k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.08/0.67    inference(cnf_transformation,[],[f41])).
% 2.08/0.67  fof(f41,plain,(
% 2.08/0.67    ! [X0] : ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.08/0.67    inference(flattening,[],[f40])).
% 2.08/0.67  fof(f40,plain,(
% 2.08/0.67    ! [X0] : (((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.08/0.67    inference(ennf_transformation,[],[f16])).
% 2.08/0.67  fof(f16,axiom,(
% 2.08/0.67    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 2.08/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).
% 2.08/0.67  fof(f1787,plain,(
% 2.08/0.67    k5_relat_1(k4_relat_1(sK2),k6_partfun1(sK0)) = k5_relat_1(k5_relat_1(k4_relat_1(sK2),sK2),sK3) | ~spl4_7),
% 2.08/0.67    inference(resolution,[],[f1681,f224])).
% 2.08/0.67  fof(f224,plain,(
% 2.08/0.67    v1_relat_1(k4_relat_1(sK2)) | ~spl4_7),
% 2.08/0.67    inference(avatar_component_clause,[],[f223])).
% 2.08/0.67  fof(f223,plain,(
% 2.08/0.67    spl4_7 <=> v1_relat_1(k4_relat_1(sK2))),
% 2.08/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 2.08/0.67  fof(f1681,plain,(
% 2.08/0.67    ( ! [X27] : (~v1_relat_1(X27) | k5_relat_1(k5_relat_1(X27,sK2),sK3) = k5_relat_1(X27,k6_partfun1(sK0))) )),
% 2.08/0.67    inference(forward_demodulation,[],[f1679,f1001])).
% 2.08/0.67  fof(f1001,plain,(
% 2.08/0.67    k6_partfun1(sK0) = k5_relat_1(sK2,sK3)),
% 2.08/0.67    inference(global_subsumption,[],[f980,f1000])).
% 2.08/0.67  fof(f1000,plain,(
% 2.08/0.67    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.08/0.67    inference(resolution,[],[f974,f348])).
% 2.08/0.67  fof(f348,plain,(
% 2.08/0.67    ( ! [X2,X3] : (~r2_relset_1(X2,X2,X3,k6_partfun1(X2)) | k6_partfun1(X2) = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))) )),
% 2.08/0.67    inference(resolution,[],[f101,f75])).
% 2.08/0.67  fof(f101,plain,(
% 2.08/0.67    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.08/0.67    inference(cnf_transformation,[],[f59])).
% 2.08/0.67  fof(f59,plain,(
% 2.08/0.67    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.08/0.67    inference(nnf_transformation,[],[f48])).
% 2.08/0.67  fof(f48,plain,(
% 2.08/0.67    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.08/0.67    inference(flattening,[],[f47])).
% 2.08/0.67  fof(f47,plain,(
% 2.08/0.67    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.08/0.67    inference(ennf_transformation,[],[f19])).
% 2.08/0.67  fof(f19,axiom,(
% 2.08/0.67    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 2.08/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 2.08/0.67  fof(f974,plain,(
% 2.08/0.67    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0))),
% 2.08/0.67    inference(backward_demodulation,[],[f67,f716])).
% 2.08/0.67  fof(f716,plain,(
% 2.08/0.67    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)),
% 2.08/0.67    inference(subsumption_resolution,[],[f713,f60])).
% 2.08/0.67  fof(f713,plain,(
% 2.08/0.67    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) | ~v1_funct_1(sK2)),
% 2.08/0.67    inference(resolution,[],[f387,f62])).
% 2.08/0.67  fof(f387,plain,(
% 2.08/0.67    ( ! [X4,X5,X3] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | k1_partfun1(X3,X4,sK1,sK0,X5,sK3) = k5_relat_1(X5,sK3) | ~v1_funct_1(X5)) )),
% 2.08/0.67    inference(subsumption_resolution,[],[f384,f63])).
% 2.08/0.67  fof(f63,plain,(
% 2.08/0.67    v1_funct_1(sK3)),
% 2.08/0.67    inference(cnf_transformation,[],[f55])).
% 2.08/0.67  fof(f384,plain,(
% 2.08/0.67    ( ! [X4,X5,X3] : (k1_partfun1(X3,X4,sK1,sK0,X5,sK3) = k5_relat_1(X5,sK3) | ~v1_funct_1(sK3) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_1(X5)) )),
% 2.08/0.67    inference(resolution,[],[f103,f65])).
% 2.08/0.67  fof(f103,plain,(
% 2.08/0.67    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 2.08/0.67    inference(cnf_transformation,[],[f50])).
% 2.08/0.67  fof(f50,plain,(
% 2.08/0.67    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.08/0.67    inference(flattening,[],[f49])).
% 2.08/0.67  fof(f49,plain,(
% 2.08/0.67    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.08/0.67    inference(ennf_transformation,[],[f22])).
% 2.08/0.67  fof(f22,axiom,(
% 2.08/0.67    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 2.08/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 2.08/0.67  fof(f67,plain,(
% 2.08/0.67    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 2.08/0.67    inference(cnf_transformation,[],[f55])).
% 2.08/0.67  fof(f980,plain,(
% 2.08/0.67    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.08/0.67    inference(subsumption_resolution,[],[f979,f60])).
% 2.08/0.67  fof(f979,plain,(
% 2.08/0.67    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK2)),
% 2.08/0.67    inference(subsumption_resolution,[],[f978,f62])).
% 2.08/0.67  fof(f978,plain,(
% 2.08/0.67    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2)),
% 2.08/0.67    inference(subsumption_resolution,[],[f977,f63])).
% 2.08/0.67  fof(f977,plain,(
% 2.08/0.67    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2)),
% 2.08/0.67    inference(subsumption_resolution,[],[f975,f65])).
% 2.08/0.67  fof(f975,plain,(
% 2.08/0.67    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2)),
% 2.08/0.67    inference(superposition,[],[f105,f716])).
% 2.08/0.68  fof(f105,plain,(
% 2.08/0.68    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 2.08/0.68    inference(cnf_transformation,[],[f52])).
% 2.08/0.68  fof(f52,plain,(
% 2.08/0.68    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.08/0.68    inference(flattening,[],[f51])).
% 2.08/0.68  fof(f51,plain,(
% 2.08/0.68    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.08/0.68    inference(ennf_transformation,[],[f20])).
% 2.08/0.68  fof(f20,axiom,(
% 2.08/0.68    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 2.08/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 2.08/0.68  fof(f1679,plain,(
% 2.08/0.68    ( ! [X27] : (k5_relat_1(k5_relat_1(X27,sK2),sK3) = k5_relat_1(X27,k5_relat_1(sK2,sK3)) | ~v1_relat_1(X27)) )),
% 2.08/0.68    inference(resolution,[],[f331,f121])).
% 2.08/0.68  fof(f331,plain,(
% 2.08/0.68    ( ! [X17,X18] : (~v1_relat_1(X18) | k5_relat_1(k5_relat_1(X17,X18),sK3) = k5_relat_1(X17,k5_relat_1(X18,sK3)) | ~v1_relat_1(X17)) )),
% 2.08/0.68    inference(resolution,[],[f82,f122])).
% 2.08/0.68  fof(f82,plain,(
% 2.08/0.68    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.08/0.68    inference(cnf_transformation,[],[f32])).
% 2.08/0.68  fof(f32,plain,(
% 2.08/0.68    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.08/0.68    inference(ennf_transformation,[],[f8])).
% 2.08/0.68  fof(f8,axiom,(
% 2.08/0.68    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)))))),
% 2.08/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).
% 2.08/0.68  fof(f241,plain,(
% 2.08/0.68    spl4_7),
% 2.08/0.68    inference(avatar_contradiction_clause,[],[f240])).
% 2.08/0.68  fof(f240,plain,(
% 2.08/0.68    $false | spl4_7),
% 2.08/0.68    inference(subsumption_resolution,[],[f239,f121])).
% 2.08/0.68  fof(f239,plain,(
% 2.08/0.68    ~v1_relat_1(sK2) | spl4_7),
% 2.08/0.68    inference(resolution,[],[f225,f78])).
% 2.08/0.68  fof(f78,plain,(
% 2.08/0.68    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 2.08/0.68    inference(cnf_transformation,[],[f28])).
% 2.08/0.68  fof(f28,plain,(
% 2.08/0.68    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 2.08/0.68    inference(ennf_transformation,[],[f4])).
% 2.08/0.68  fof(f4,axiom,(
% 2.08/0.68    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 2.08/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).
% 2.08/0.68  fof(f225,plain,(
% 2.08/0.68    ~v1_relat_1(k4_relat_1(sK2)) | spl4_7),
% 2.08/0.68    inference(avatar_component_clause,[],[f223])).
% 2.08/0.68  % SZS output end Proof for theBenchmark
% 2.08/0.68  % (26699)------------------------------
% 2.08/0.68  % (26699)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.08/0.68  % (26699)Termination reason: Refutation
% 2.08/0.68  
% 2.08/0.68  % (26699)Memory used [KB]: 12025
% 2.08/0.68  % (26699)Time elapsed: 0.258 s
% 2.08/0.68  % (26699)------------------------------
% 2.08/0.68  % (26699)------------------------------
% 2.08/0.68  % (26687)Success in time 0.31 s
%------------------------------------------------------------------------------
