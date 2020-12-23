%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:02:21 EST 2020

% Result     : Theorem 3.04s
% Output     : CNFRefutation 3.04s
% Verified   : 
% Statistics : Number of formulae       :  213 (3322 expanded)
%              Number of clauses        :  143 (1162 expanded)
%              Number of leaves         :   22 ( 634 expanded)
%              Depth                    :   27
%              Number of atoms          :  659 (17089 expanded)
%              Number of equality atoms :  318 (3511 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f21,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
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
    inference(ennf_transformation,[],[f21])).

fof(f47,plain,(
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
    inference(flattening,[],[f46])).

fof(f56,plain,(
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
    inference(nnf_transformation,[],[f47])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f23,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f50,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f51,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f50])).

fof(f57,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
          | ~ v1_funct_1(k2_funct_1(X2)) )
        & k2_relset_1(X0,X1,X2) = X1
        & v2_funct_1(X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
        | ~ v1_funct_1(k2_funct_1(sK2)) )
      & k2_relset_1(sK0,sK1,sK2) = sK1
      & v2_funct_1(sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
      | ~ v1_funct_1(k2_funct_1(sK2)) )
    & k2_relset_1(sK0,sK1,sK2) = sK1
    & v2_funct_1(sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f51,f57])).

fof(f98,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f58])).

fof(f99,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f58])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f14,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f38,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f37])).

fof(f78,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f100,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f58])).

fof(f97,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f58])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f101,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f58])).

fof(f16,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f42,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f41])).

fof(f81,plain,(
    ! [X0] :
      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f48])).

fof(f96,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f15,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f40,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f39])).

fof(f79,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f80,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f82,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f52])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f104,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f61])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f109,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f89])).

fof(f95,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f102,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f58])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f60,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f54,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f72,plain,(
    ! [X0] :
      ( k1_xboole_0 = k2_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f32,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f69,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_34,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_42,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1308,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK0 != X1
    | sK1 != X2
    | sK2 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_34,c_42])).

cnf(c_1309,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_relset_1(sK0,sK1,sK2) = sK0
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_1308])).

cnf(c_41,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_1311,plain,
    ( k1_relset_1(sK0,sK1,sK2) = sK0
    | k1_xboole_0 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1309,c_41])).

cnf(c_2360,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_2363,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_4634,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_2360,c_2363])).

cnf(c_4738,plain,
    ( k1_relat_1(sK2) = sK0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1311,c_4634])).

cnf(c_26,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_2364,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_3858,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2360,c_2364])).

cnf(c_19,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(X0) = k4_relat_1(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_40,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_516,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(X0) = k4_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_40])).

cnf(c_517,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_516])).

cnf(c_43,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_519,plain,
    ( ~ v1_relat_1(sK2)
    | k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_517,c_43])).

cnf(c_2353,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_519])).

cnf(c_4029,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_3858,c_2353])).

cnf(c_28,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_2362,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_3946,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_2360,c_2362])).

cnf(c_39,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f101])).

cnf(c_3948,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_3946,c_39])).

cnf(c_23,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_488,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_40])).

cnf(c_489,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_488])).

cnf(c_491,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_489,c_43])).

cnf(c_2355,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_491])).

cnf(c_4004,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = sK1
    | v1_relat_1(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3948,c_2355])).

cnf(c_46,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_2698,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_2838,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_2698])).

cnf(c_2839,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2838])).

cnf(c_4104,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4004,c_46,c_2839])).

cnf(c_4235,plain,
    ( k1_relat_1(k4_relat_1(sK2)) = sK1 ),
    inference(demodulation,[status(thm)],[c_4029,c_4104])).

cnf(c_35,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_2361,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_5443,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) = iProver_top
    | r1_tarski(k2_relat_1(k4_relat_1(sK2)),X0) != iProver_top
    | v1_funct_1(k4_relat_1(sK2)) != iProver_top
    | v1_relat_1(k4_relat_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4235,c_2361])).

cnf(c_44,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_21,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_2367,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_4728,plain,
    ( v1_funct_1(sK2) != iProver_top
    | v1_relat_1(k4_relat_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4029,c_2367])).

cnf(c_20,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_2368,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_funct_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_5166,plain,
    ( v1_funct_1(k4_relat_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4029,c_2368])).

cnf(c_6362,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) = iProver_top
    | r1_tarski(k2_relat_1(k4_relat_1(sK2)),X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5443,c_44,c_46,c_2839,c_4728,c_5166])).

cnf(c_22,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_502,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_40])).

cnf(c_503,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_502])).

cnf(c_505,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_503,c_43])).

cnf(c_2354,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_505])).

cnf(c_4028,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_3858,c_2354])).

cnf(c_4032,plain,
    ( k2_relat_1(k4_relat_1(sK2)) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_4028,c_4029])).

cnf(c_6368,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) = iProver_top
    | r1_tarski(k1_relat_1(sK2),X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6362,c_4032])).

cnf(c_4,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_2378,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_6374,plain,
    ( k1_relset_1(sK1,X0,k4_relat_1(sK2)) = k1_relat_1(k4_relat_1(sK2))
    | r1_tarski(k1_relat_1(sK2),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6368,c_2363])).

cnf(c_6384,plain,
    ( k1_relset_1(sK1,X0,k4_relat_1(sK2)) = sK1
    | r1_tarski(k1_relat_1(sK2),X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6374,c_4235])).

cnf(c_6470,plain,
    ( k1_relset_1(sK1,k1_relat_1(sK2),k4_relat_1(sK2)) = sK1 ),
    inference(superposition,[status(thm)],[c_2378,c_6384])).

cnf(c_6639,plain,
    ( k1_relset_1(sK1,sK0,k4_relat_1(sK2)) = sK1
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4738,c_6470])).

cnf(c_33,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f109])).

cnf(c_36,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1207,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ r1_tarski(k2_relat_1(X2),X3)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | X2 != X0
    | X3 != X1
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
    | k1_relat_1(X2) != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_33,c_36])).

cnf(c_1208,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
    | k1_relat_1(X0) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_1207])).

cnf(c_1224,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
    | k1_relat_1(X0) != k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1208,c_26])).

cnf(c_2349,plain,
    ( k1_relset_1(k1_xboole_0,X0,X1) = k1_xboole_0
    | k1_relat_1(X1) != k1_xboole_0
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top
    | r1_tarski(k2_relat_1(X1),X0) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1224])).

cnf(c_4110,plain,
    ( k1_relset_1(k1_xboole_0,X0,k2_funct_1(sK2)) = k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top
    | r1_tarski(k2_relat_1(k2_funct_1(sK2)),X0) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4104,c_2349])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1674,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2865,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_1674])).

cnf(c_38,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_1319,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(X0)
    | k2_funct_1(sK2) != X0
    | k1_relat_1(X0) != sK1
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_36,c_38])).

cnf(c_1320,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
    inference(unflattening,[status(thm)],[c_1319])).

cnf(c_1332,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1320,c_26])).

cnf(c_2344,plain,
    ( k1_relat_1(k2_funct_1(sK2)) != sK1
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1332])).

cnf(c_1337,plain,
    ( k1_relat_1(k2_funct_1(sK2)) != sK1
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1332])).

cnf(c_2689,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_2690,plain,
    ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2689])).

cnf(c_3005,plain,
    ( r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2344,c_44,c_46,c_1337,c_2690,c_2839])).

cnf(c_3006,plain,
    ( k1_relat_1(k2_funct_1(sK2)) != sK1
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3005])).

cnf(c_3007,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0)
    | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3006])).

cnf(c_3068,plain,
    ( ~ v1_funct_1(sK2)
    | v1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_3069,plain,
    ( v1_funct_1(sK2) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3068])).

cnf(c_1675,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2853,plain,
    ( X0 != X1
    | k2_funct_1(sK2) != X1
    | k2_funct_1(sK2) = X0 ),
    inference(instantiation,[status(thm)],[c_1675])).

cnf(c_3295,plain,
    ( X0 != k4_relat_1(sK2)
    | k2_funct_1(sK2) = X0
    | k2_funct_1(sK2) != k4_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_2853])).

cnf(c_3296,plain,
    ( k2_funct_1(sK2) != k4_relat_1(sK2)
    | k2_funct_1(sK2) = k1_xboole_0
    | k1_xboole_0 != k4_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_3295])).

cnf(c_1679,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2744,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
    | X1 != k1_zfmisc_1(X2)
    | X0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1679])).

cnf(c_2910,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | X0 != k1_xboole_0
    | k1_zfmisc_1(X1) != k1_zfmisc_1(X1) ),
    inference(instantiation,[status(thm)],[c_2744])).

cnf(c_3367,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | k2_funct_1(sK2) != k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_2910])).

cnf(c_1677,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2739,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(X2),X3)
    | X3 != X1
    | k2_relat_1(X2) != X0 ),
    inference(instantiation,[status(thm)],[c_1677])).

cnf(c_3130,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0)
    | k2_relat_1(k2_funct_1(sK2)) != X0
    | sK0 != X1 ),
    inference(instantiation,[status(thm)],[c_2739])).

cnf(c_3454,plain,
    ( ~ r1_tarski(X0,sK0)
    | r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0)
    | k2_relat_1(k2_funct_1(sK2)) != X0
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_3130])).

cnf(c_3456,plain,
    ( r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0)
    | ~ r1_tarski(k1_xboole_0,sK0)
    | k2_relat_1(k2_funct_1(sK2)) != k1_xboole_0
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_3454])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_3474,plain,
    ( ~ v1_xboole_0(k4_relat_1(sK2))
    | k1_xboole_0 = k4_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1676,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_3887,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK1)
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_1676])).

cnf(c_3889,plain,
    ( v1_xboole_0(sK1)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK1 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3887])).

cnf(c_14,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) = k1_xboole_0
    | k1_relat_1(X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_2370,plain,
    ( k2_relat_1(X0) = k1_xboole_0
    | k1_relat_1(X0) != k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_4109,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_xboole_0
    | sK1 != k1_xboole_0
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4104,c_2370])).

cnf(c_5,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_4195,plain,
    ( r1_tarski(k1_xboole_0,sK0) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_4736,plain,
    ( ~ v1_funct_1(sK2)
    | v1_relat_1(k4_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4728])).

cnf(c_6,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_2724,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_5005,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(instantiation,[status(thm)],[c_2724])).

cnf(c_10,plain,
    ( ~ v1_relat_1(X0)
    | v1_xboole_0(X0)
    | ~ v1_xboole_0(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_2372,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(k1_relat_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_5236,plain,
    ( v1_relat_1(k4_relat_1(sK2)) != iProver_top
    | v1_xboole_0(k4_relat_1(sK2)) = iProver_top
    | v1_xboole_0(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4235,c_2372])).

cnf(c_5252,plain,
    ( ~ v1_relat_1(k4_relat_1(sK2))
    | v1_xboole_0(k4_relat_1(sK2))
    | ~ v1_xboole_0(sK1) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5236])).

cnf(c_2911,plain,
    ( k1_zfmisc_1(X0) = k1_zfmisc_1(X0) ),
    inference(instantiation,[status(thm)],[c_1674])).

cnf(c_5638,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) = k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_2911])).

cnf(c_5650,plain,
    ( sK1 != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4110,c_43,c_44,c_41,c_46,c_0,c_517,c_2838,c_2839,c_2865,c_3007,c_3069,c_3296,c_3367,c_3456,c_3474,c_3889,c_4004,c_4109,c_4195,c_4736,c_5005,c_5252,c_5638])).

cnf(c_6845,plain,
    ( k1_relset_1(sK1,sK0,k4_relat_1(sK2)) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6639,c_43,c_44,c_41,c_46,c_0,c_517,c_2838,c_2839,c_2865,c_3007,c_3069,c_3296,c_3367,c_3456,c_3474,c_3889,c_4004,c_4109,c_4195,c_4736,c_5005,c_5252,c_5638])).

cnf(c_32,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1292,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_relset_1(X1,X2,X0) != X1
    | k2_funct_1(sK2) != X0
    | sK0 != X2
    | sK1 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_32,c_38])).

cnf(c_1293,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_relset_1(sK1,sK0,k2_funct_1(sK2)) != sK1
    | k1_xboole_0 = sK0 ),
    inference(unflattening,[status(thm)],[c_1292])).

cnf(c_2345,plain,
    ( k1_relset_1(sK1,sK0,k2_funct_1(sK2)) != sK1
    | k1_xboole_0 = sK0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1293])).

cnf(c_1294,plain,
    ( k1_relset_1(sK1,sK0,k2_funct_1(sK2)) != sK1
    | k1_xboole_0 = sK0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1293])).

cnf(c_2870,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | k1_xboole_0 = sK0
    | k1_relset_1(sK1,sK0,k2_funct_1(sK2)) != sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2345,c_44,c_46,c_1294,c_2690,c_2839])).

cnf(c_2871,plain,
    ( k1_relset_1(sK1,sK0,k2_funct_1(sK2)) != sK1
    | k1_xboole_0 = sK0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2870])).

cnf(c_4238,plain,
    ( k1_relset_1(sK1,sK0,k4_relat_1(sK2)) != sK1
    | sK0 = k1_xboole_0
    | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4029,c_2871])).

cnf(c_6848,plain,
    ( sK0 = k1_xboole_0
    | sK1 != sK1
    | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6845,c_4238])).

cnf(c_6958,plain,
    ( sK0 = k1_xboole_0
    | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_6848])).

cnf(c_4903,plain,
    ( k2_relat_1(sK2) = k1_xboole_0
    | sK0 != k1_xboole_0
    | sK1 = k1_xboole_0
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4738,c_2370])).

cnf(c_4922,plain,
    ( sK0 != k1_xboole_0
    | sK1 = k1_xboole_0
    | v1_relat_1(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4903,c_3948])).

cnf(c_4929,plain,
    ( ~ v1_relat_1(sK2)
    | sK0 != k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4922])).

cnf(c_4931,plain,
    ( sK1 = k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4922,c_41,c_2838,c_4929])).

cnf(c_4932,plain,
    ( sK0 != k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_4931])).

cnf(c_6960,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6958,c_43,c_44,c_41,c_46,c_0,c_517,c_2838,c_2839,c_2865,c_3007,c_3069,c_3296,c_3367,c_3456,c_3474,c_3889,c_4004,c_4109,c_4195,c_4238,c_4736,c_4929,c_5005,c_5252,c_5638,c_6639])).

cnf(c_6965,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6368,c_6960])).

cnf(c_7580,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(sK0,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4738,c_6965])).

cnf(c_4087,plain,
    ( r1_tarski(sK0,sK0) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_4090,plain,
    ( r1_tarski(sK0,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4087])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7580,c_5650,c_4090])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:41:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.04/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.04/0.99  
% 3.04/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.04/0.99  
% 3.04/0.99  ------  iProver source info
% 3.04/0.99  
% 3.04/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.04/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.04/0.99  git: non_committed_changes: false
% 3.04/0.99  git: last_make_outside_of_git: false
% 3.04/0.99  
% 3.04/0.99  ------ 
% 3.04/0.99  
% 3.04/0.99  ------ Input Options
% 3.04/0.99  
% 3.04/0.99  --out_options                           all
% 3.04/0.99  --tptp_safe_out                         true
% 3.04/0.99  --problem_path                          ""
% 3.04/0.99  --include_path                          ""
% 3.04/0.99  --clausifier                            res/vclausify_rel
% 3.04/0.99  --clausifier_options                    --mode clausify
% 3.04/0.99  --stdin                                 false
% 3.04/0.99  --stats_out                             all
% 3.04/0.99  
% 3.04/0.99  ------ General Options
% 3.04/0.99  
% 3.04/0.99  --fof                                   false
% 3.04/0.99  --time_out_real                         305.
% 3.04/0.99  --time_out_virtual                      -1.
% 3.04/0.99  --symbol_type_check                     false
% 3.04/0.99  --clausify_out                          false
% 3.04/0.99  --sig_cnt_out                           false
% 3.04/0.99  --trig_cnt_out                          false
% 3.04/0.99  --trig_cnt_out_tolerance                1.
% 3.04/0.99  --trig_cnt_out_sk_spl                   false
% 3.04/0.99  --abstr_cl_out                          false
% 3.04/0.99  
% 3.04/0.99  ------ Global Options
% 3.04/0.99  
% 3.04/0.99  --schedule                              default
% 3.04/0.99  --add_important_lit                     false
% 3.04/0.99  --prop_solver_per_cl                    1000
% 3.04/0.99  --min_unsat_core                        false
% 3.04/0.99  --soft_assumptions                      false
% 3.04/0.99  --soft_lemma_size                       3
% 3.04/0.99  --prop_impl_unit_size                   0
% 3.04/0.99  --prop_impl_unit                        []
% 3.04/0.99  --share_sel_clauses                     true
% 3.04/0.99  --reset_solvers                         false
% 3.04/0.99  --bc_imp_inh                            [conj_cone]
% 3.04/0.99  --conj_cone_tolerance                   3.
% 3.04/0.99  --extra_neg_conj                        none
% 3.04/0.99  --large_theory_mode                     true
% 3.04/0.99  --prolific_symb_bound                   200
% 3.04/0.99  --lt_threshold                          2000
% 3.04/0.99  --clause_weak_htbl                      true
% 3.04/0.99  --gc_record_bc_elim                     false
% 3.04/0.99  
% 3.04/0.99  ------ Preprocessing Options
% 3.04/0.99  
% 3.04/0.99  --preprocessing_flag                    true
% 3.04/0.99  --time_out_prep_mult                    0.1
% 3.04/0.99  --splitting_mode                        input
% 3.04/0.99  --splitting_grd                         true
% 3.04/0.99  --splitting_cvd                         false
% 3.04/0.99  --splitting_cvd_svl                     false
% 3.04/0.99  --splitting_nvd                         32
% 3.04/0.99  --sub_typing                            true
% 3.04/0.99  --prep_gs_sim                           true
% 3.04/0.99  --prep_unflatten                        true
% 3.04/0.99  --prep_res_sim                          true
% 3.04/0.99  --prep_upred                            true
% 3.04/0.99  --prep_sem_filter                       exhaustive
% 3.04/0.99  --prep_sem_filter_out                   false
% 3.04/0.99  --pred_elim                             true
% 3.04/0.99  --res_sim_input                         true
% 3.04/0.99  --eq_ax_congr_red                       true
% 3.04/0.99  --pure_diseq_elim                       true
% 3.04/0.99  --brand_transform                       false
% 3.04/0.99  --non_eq_to_eq                          false
% 3.04/0.99  --prep_def_merge                        true
% 3.04/0.99  --prep_def_merge_prop_impl              false
% 3.04/0.99  --prep_def_merge_mbd                    true
% 3.04/0.99  --prep_def_merge_tr_red                 false
% 3.04/0.99  --prep_def_merge_tr_cl                  false
% 3.04/0.99  --smt_preprocessing                     true
% 3.04/0.99  --smt_ac_axioms                         fast
% 3.04/0.99  --preprocessed_out                      false
% 3.04/0.99  --preprocessed_stats                    false
% 3.04/0.99  
% 3.04/0.99  ------ Abstraction refinement Options
% 3.04/0.99  
% 3.04/0.99  --abstr_ref                             []
% 3.04/0.99  --abstr_ref_prep                        false
% 3.04/0.99  --abstr_ref_until_sat                   false
% 3.04/0.99  --abstr_ref_sig_restrict                funpre
% 3.04/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.04/0.99  --abstr_ref_under                       []
% 3.04/0.99  
% 3.04/0.99  ------ SAT Options
% 3.04/0.99  
% 3.04/0.99  --sat_mode                              false
% 3.04/0.99  --sat_fm_restart_options                ""
% 3.04/0.99  --sat_gr_def                            false
% 3.04/0.99  --sat_epr_types                         true
% 3.04/0.99  --sat_non_cyclic_types                  false
% 3.04/0.99  --sat_finite_models                     false
% 3.04/0.99  --sat_fm_lemmas                         false
% 3.04/0.99  --sat_fm_prep                           false
% 3.04/0.99  --sat_fm_uc_incr                        true
% 3.04/0.99  --sat_out_model                         small
% 3.04/0.99  --sat_out_clauses                       false
% 3.04/0.99  
% 3.04/0.99  ------ QBF Options
% 3.04/0.99  
% 3.04/0.99  --qbf_mode                              false
% 3.04/0.99  --qbf_elim_univ                         false
% 3.04/0.99  --qbf_dom_inst                          none
% 3.04/0.99  --qbf_dom_pre_inst                      false
% 3.04/0.99  --qbf_sk_in                             false
% 3.04/0.99  --qbf_pred_elim                         true
% 3.04/0.99  --qbf_split                             512
% 3.04/0.99  
% 3.04/0.99  ------ BMC1 Options
% 3.04/0.99  
% 3.04/0.99  --bmc1_incremental                      false
% 3.04/0.99  --bmc1_axioms                           reachable_all
% 3.04/0.99  --bmc1_min_bound                        0
% 3.04/0.99  --bmc1_max_bound                        -1
% 3.04/0.99  --bmc1_max_bound_default                -1
% 3.04/0.99  --bmc1_symbol_reachability              true
% 3.04/0.99  --bmc1_property_lemmas                  false
% 3.04/0.99  --bmc1_k_induction                      false
% 3.04/0.99  --bmc1_non_equiv_states                 false
% 3.04/0.99  --bmc1_deadlock                         false
% 3.04/0.99  --bmc1_ucm                              false
% 3.04/0.99  --bmc1_add_unsat_core                   none
% 3.04/0.99  --bmc1_unsat_core_children              false
% 3.04/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.04/0.99  --bmc1_out_stat                         full
% 3.04/0.99  --bmc1_ground_init                      false
% 3.04/0.99  --bmc1_pre_inst_next_state              false
% 3.04/0.99  --bmc1_pre_inst_state                   false
% 3.04/0.99  --bmc1_pre_inst_reach_state             false
% 3.04/0.99  --bmc1_out_unsat_core                   false
% 3.04/0.99  --bmc1_aig_witness_out                  false
% 3.04/0.99  --bmc1_verbose                          false
% 3.04/0.99  --bmc1_dump_clauses_tptp                false
% 3.04/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.04/0.99  --bmc1_dump_file                        -
% 3.04/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.04/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.04/0.99  --bmc1_ucm_extend_mode                  1
% 3.04/0.99  --bmc1_ucm_init_mode                    2
% 3.04/0.99  --bmc1_ucm_cone_mode                    none
% 3.04/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.04/0.99  --bmc1_ucm_relax_model                  4
% 3.04/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.04/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.04/0.99  --bmc1_ucm_layered_model                none
% 3.04/0.99  --bmc1_ucm_max_lemma_size               10
% 3.04/0.99  
% 3.04/0.99  ------ AIG Options
% 3.04/0.99  
% 3.04/0.99  --aig_mode                              false
% 3.04/0.99  
% 3.04/0.99  ------ Instantiation Options
% 3.04/0.99  
% 3.04/0.99  --instantiation_flag                    true
% 3.04/0.99  --inst_sos_flag                         false
% 3.04/0.99  --inst_sos_phase                        true
% 3.04/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.04/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.04/0.99  --inst_lit_sel_side                     num_symb
% 3.04/0.99  --inst_solver_per_active                1400
% 3.04/0.99  --inst_solver_calls_frac                1.
% 3.04/0.99  --inst_passive_queue_type               priority_queues
% 3.04/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.04/0.99  --inst_passive_queues_freq              [25;2]
% 3.04/0.99  --inst_dismatching                      true
% 3.04/0.99  --inst_eager_unprocessed_to_passive     true
% 3.04/0.99  --inst_prop_sim_given                   true
% 3.04/0.99  --inst_prop_sim_new                     false
% 3.04/0.99  --inst_subs_new                         false
% 3.04/0.99  --inst_eq_res_simp                      false
% 3.04/0.99  --inst_subs_given                       false
% 3.04/0.99  --inst_orphan_elimination               true
% 3.04/0.99  --inst_learning_loop_flag               true
% 3.04/0.99  --inst_learning_start                   3000
% 3.04/0.99  --inst_learning_factor                  2
% 3.04/0.99  --inst_start_prop_sim_after_learn       3
% 3.04/0.99  --inst_sel_renew                        solver
% 3.04/0.99  --inst_lit_activity_flag                true
% 3.04/0.99  --inst_restr_to_given                   false
% 3.04/0.99  --inst_activity_threshold               500
% 3.04/0.99  --inst_out_proof                        true
% 3.04/0.99  
% 3.04/0.99  ------ Resolution Options
% 3.04/0.99  
% 3.04/0.99  --resolution_flag                       true
% 3.04/0.99  --res_lit_sel                           adaptive
% 3.04/0.99  --res_lit_sel_side                      none
% 3.04/0.99  --res_ordering                          kbo
% 3.04/0.99  --res_to_prop_solver                    active
% 3.04/0.99  --res_prop_simpl_new                    false
% 3.04/0.99  --res_prop_simpl_given                  true
% 3.04/0.99  --res_passive_queue_type                priority_queues
% 3.04/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.04/0.99  --res_passive_queues_freq               [15;5]
% 3.04/0.99  --res_forward_subs                      full
% 3.04/0.99  --res_backward_subs                     full
% 3.04/0.99  --res_forward_subs_resolution           true
% 3.04/0.99  --res_backward_subs_resolution          true
% 3.04/0.99  --res_orphan_elimination                true
% 3.04/0.99  --res_time_limit                        2.
% 3.04/0.99  --res_out_proof                         true
% 3.04/0.99  
% 3.04/0.99  ------ Superposition Options
% 3.04/0.99  
% 3.04/0.99  --superposition_flag                    true
% 3.04/0.99  --sup_passive_queue_type                priority_queues
% 3.04/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.04/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.04/0.99  --demod_completeness_check              fast
% 3.04/0.99  --demod_use_ground                      true
% 3.04/0.99  --sup_to_prop_solver                    passive
% 3.04/0.99  --sup_prop_simpl_new                    true
% 3.04/0.99  --sup_prop_simpl_given                  true
% 3.04/0.99  --sup_fun_splitting                     false
% 3.04/0.99  --sup_smt_interval                      50000
% 3.04/0.99  
% 3.04/0.99  ------ Superposition Simplification Setup
% 3.04/0.99  
% 3.04/0.99  --sup_indices_passive                   []
% 3.04/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.04/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.04/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.04/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.04/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.04/0.99  --sup_full_bw                           [BwDemod]
% 3.04/0.99  --sup_immed_triv                        [TrivRules]
% 3.04/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.04/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.04/0.99  --sup_immed_bw_main                     []
% 3.04/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.04/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.04/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.04/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.04/0.99  
% 3.04/0.99  ------ Combination Options
% 3.04/0.99  
% 3.04/0.99  --comb_res_mult                         3
% 3.04/0.99  --comb_sup_mult                         2
% 3.04/0.99  --comb_inst_mult                        10
% 3.04/0.99  
% 3.04/0.99  ------ Debug Options
% 3.04/0.99  
% 3.04/0.99  --dbg_backtrace                         false
% 3.04/0.99  --dbg_dump_prop_clauses                 false
% 3.04/0.99  --dbg_dump_prop_clauses_file            -
% 3.04/0.99  --dbg_out_stat                          false
% 3.04/0.99  ------ Parsing...
% 3.04/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.04/0.99  
% 3.04/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.04/0.99  
% 3.04/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.04/0.99  
% 3.04/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.04/0.99  ------ Proving...
% 3.04/0.99  ------ Problem Properties 
% 3.04/0.99  
% 3.04/0.99  
% 3.04/0.99  clauses                                 43
% 3.04/0.99  conjectures                             3
% 3.04/0.99  EPR                                     10
% 3.04/0.99  Horn                                    39
% 3.04/0.99  unary                                   11
% 3.04/0.99  binary                                  15
% 3.04/0.99  lits                                    107
% 3.04/0.99  lits eq                                 40
% 3.04/0.99  fd_pure                                 0
% 3.04/0.99  fd_pseudo                               0
% 3.04/0.99  fd_cond                                 3
% 3.04/0.99  fd_pseudo_cond                          1
% 3.04/0.99  AC symbols                              0
% 3.04/0.99  
% 3.04/0.99  ------ Schedule dynamic 5 is on 
% 3.04/0.99  
% 3.04/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.04/0.99  
% 3.04/0.99  
% 3.04/0.99  ------ 
% 3.04/0.99  Current options:
% 3.04/0.99  ------ 
% 3.04/0.99  
% 3.04/0.99  ------ Input Options
% 3.04/0.99  
% 3.04/0.99  --out_options                           all
% 3.04/0.99  --tptp_safe_out                         true
% 3.04/0.99  --problem_path                          ""
% 3.04/0.99  --include_path                          ""
% 3.04/0.99  --clausifier                            res/vclausify_rel
% 3.04/0.99  --clausifier_options                    --mode clausify
% 3.04/0.99  --stdin                                 false
% 3.04/0.99  --stats_out                             all
% 3.04/0.99  
% 3.04/0.99  ------ General Options
% 3.04/0.99  
% 3.04/0.99  --fof                                   false
% 3.04/0.99  --time_out_real                         305.
% 3.04/0.99  --time_out_virtual                      -1.
% 3.04/0.99  --symbol_type_check                     false
% 3.04/0.99  --clausify_out                          false
% 3.04/0.99  --sig_cnt_out                           false
% 3.04/0.99  --trig_cnt_out                          false
% 3.04/0.99  --trig_cnt_out_tolerance                1.
% 3.04/0.99  --trig_cnt_out_sk_spl                   false
% 3.04/0.99  --abstr_cl_out                          false
% 3.04/0.99  
% 3.04/0.99  ------ Global Options
% 3.04/0.99  
% 3.04/0.99  --schedule                              default
% 3.04/0.99  --add_important_lit                     false
% 3.04/0.99  --prop_solver_per_cl                    1000
% 3.04/0.99  --min_unsat_core                        false
% 3.04/0.99  --soft_assumptions                      false
% 3.04/0.99  --soft_lemma_size                       3
% 3.04/0.99  --prop_impl_unit_size                   0
% 3.04/0.99  --prop_impl_unit                        []
% 3.04/0.99  --share_sel_clauses                     true
% 3.04/0.99  --reset_solvers                         false
% 3.04/0.99  --bc_imp_inh                            [conj_cone]
% 3.04/0.99  --conj_cone_tolerance                   3.
% 3.04/0.99  --extra_neg_conj                        none
% 3.04/0.99  --large_theory_mode                     true
% 3.04/0.99  --prolific_symb_bound                   200
% 3.04/0.99  --lt_threshold                          2000
% 3.04/0.99  --clause_weak_htbl                      true
% 3.04/0.99  --gc_record_bc_elim                     false
% 3.04/0.99  
% 3.04/0.99  ------ Preprocessing Options
% 3.04/0.99  
% 3.04/0.99  --preprocessing_flag                    true
% 3.04/0.99  --time_out_prep_mult                    0.1
% 3.04/0.99  --splitting_mode                        input
% 3.04/0.99  --splitting_grd                         true
% 3.04/0.99  --splitting_cvd                         false
% 3.04/0.99  --splitting_cvd_svl                     false
% 3.04/0.99  --splitting_nvd                         32
% 3.04/0.99  --sub_typing                            true
% 3.04/0.99  --prep_gs_sim                           true
% 3.04/0.99  --prep_unflatten                        true
% 3.04/0.99  --prep_res_sim                          true
% 3.04/0.99  --prep_upred                            true
% 3.04/0.99  --prep_sem_filter                       exhaustive
% 3.04/0.99  --prep_sem_filter_out                   false
% 3.04/0.99  --pred_elim                             true
% 3.04/0.99  --res_sim_input                         true
% 3.04/0.99  --eq_ax_congr_red                       true
% 3.04/0.99  --pure_diseq_elim                       true
% 3.04/0.99  --brand_transform                       false
% 3.04/0.99  --non_eq_to_eq                          false
% 3.04/0.99  --prep_def_merge                        true
% 3.04/0.99  --prep_def_merge_prop_impl              false
% 3.04/0.99  --prep_def_merge_mbd                    true
% 3.04/0.99  --prep_def_merge_tr_red                 false
% 3.04/0.99  --prep_def_merge_tr_cl                  false
% 3.04/0.99  --smt_preprocessing                     true
% 3.04/0.99  --smt_ac_axioms                         fast
% 3.04/0.99  --preprocessed_out                      false
% 3.04/0.99  --preprocessed_stats                    false
% 3.04/0.99  
% 3.04/0.99  ------ Abstraction refinement Options
% 3.04/0.99  
% 3.04/0.99  --abstr_ref                             []
% 3.04/0.99  --abstr_ref_prep                        false
% 3.04/0.99  --abstr_ref_until_sat                   false
% 3.04/0.99  --abstr_ref_sig_restrict                funpre
% 3.04/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.04/0.99  --abstr_ref_under                       []
% 3.04/0.99  
% 3.04/0.99  ------ SAT Options
% 3.04/0.99  
% 3.04/0.99  --sat_mode                              false
% 3.04/0.99  --sat_fm_restart_options                ""
% 3.04/0.99  --sat_gr_def                            false
% 3.04/0.99  --sat_epr_types                         true
% 3.04/0.99  --sat_non_cyclic_types                  false
% 3.04/0.99  --sat_finite_models                     false
% 3.04/0.99  --sat_fm_lemmas                         false
% 3.04/0.99  --sat_fm_prep                           false
% 3.04/0.99  --sat_fm_uc_incr                        true
% 3.04/0.99  --sat_out_model                         small
% 3.04/0.99  --sat_out_clauses                       false
% 3.04/0.99  
% 3.04/0.99  ------ QBF Options
% 3.04/0.99  
% 3.04/0.99  --qbf_mode                              false
% 3.04/0.99  --qbf_elim_univ                         false
% 3.04/0.99  --qbf_dom_inst                          none
% 3.04/0.99  --qbf_dom_pre_inst                      false
% 3.04/0.99  --qbf_sk_in                             false
% 3.04/0.99  --qbf_pred_elim                         true
% 3.04/0.99  --qbf_split                             512
% 3.04/0.99  
% 3.04/0.99  ------ BMC1 Options
% 3.04/0.99  
% 3.04/0.99  --bmc1_incremental                      false
% 3.04/0.99  --bmc1_axioms                           reachable_all
% 3.04/0.99  --bmc1_min_bound                        0
% 3.04/0.99  --bmc1_max_bound                        -1
% 3.04/0.99  --bmc1_max_bound_default                -1
% 3.04/0.99  --bmc1_symbol_reachability              true
% 3.04/0.99  --bmc1_property_lemmas                  false
% 3.04/0.99  --bmc1_k_induction                      false
% 3.04/0.99  --bmc1_non_equiv_states                 false
% 3.04/0.99  --bmc1_deadlock                         false
% 3.04/0.99  --bmc1_ucm                              false
% 3.04/0.99  --bmc1_add_unsat_core                   none
% 3.04/0.99  --bmc1_unsat_core_children              false
% 3.04/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.04/0.99  --bmc1_out_stat                         full
% 3.04/0.99  --bmc1_ground_init                      false
% 3.04/0.99  --bmc1_pre_inst_next_state              false
% 3.04/0.99  --bmc1_pre_inst_state                   false
% 3.04/0.99  --bmc1_pre_inst_reach_state             false
% 3.04/0.99  --bmc1_out_unsat_core                   false
% 3.04/0.99  --bmc1_aig_witness_out                  false
% 3.04/0.99  --bmc1_verbose                          false
% 3.04/0.99  --bmc1_dump_clauses_tptp                false
% 3.04/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.04/0.99  --bmc1_dump_file                        -
% 3.04/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.04/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.04/0.99  --bmc1_ucm_extend_mode                  1
% 3.04/0.99  --bmc1_ucm_init_mode                    2
% 3.04/0.99  --bmc1_ucm_cone_mode                    none
% 3.04/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.04/0.99  --bmc1_ucm_relax_model                  4
% 3.04/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.04/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.04/0.99  --bmc1_ucm_layered_model                none
% 3.04/0.99  --bmc1_ucm_max_lemma_size               10
% 3.04/0.99  
% 3.04/0.99  ------ AIG Options
% 3.04/0.99  
% 3.04/0.99  --aig_mode                              false
% 3.04/0.99  
% 3.04/0.99  ------ Instantiation Options
% 3.04/0.99  
% 3.04/0.99  --instantiation_flag                    true
% 3.04/0.99  --inst_sos_flag                         false
% 3.04/0.99  --inst_sos_phase                        true
% 3.04/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.04/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.04/0.99  --inst_lit_sel_side                     none
% 3.04/0.99  --inst_solver_per_active                1400
% 3.04/0.99  --inst_solver_calls_frac                1.
% 3.04/0.99  --inst_passive_queue_type               priority_queues
% 3.04/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.04/0.99  --inst_passive_queues_freq              [25;2]
% 3.04/0.99  --inst_dismatching                      true
% 3.04/0.99  --inst_eager_unprocessed_to_passive     true
% 3.04/0.99  --inst_prop_sim_given                   true
% 3.04/0.99  --inst_prop_sim_new                     false
% 3.04/0.99  --inst_subs_new                         false
% 3.04/0.99  --inst_eq_res_simp                      false
% 3.04/0.99  --inst_subs_given                       false
% 3.04/0.99  --inst_orphan_elimination               true
% 3.04/0.99  --inst_learning_loop_flag               true
% 3.04/0.99  --inst_learning_start                   3000
% 3.04/0.99  --inst_learning_factor                  2
% 3.04/0.99  --inst_start_prop_sim_after_learn       3
% 3.04/0.99  --inst_sel_renew                        solver
% 3.04/0.99  --inst_lit_activity_flag                true
% 3.04/0.99  --inst_restr_to_given                   false
% 3.04/0.99  --inst_activity_threshold               500
% 3.04/0.99  --inst_out_proof                        true
% 3.04/0.99  
% 3.04/0.99  ------ Resolution Options
% 3.04/0.99  
% 3.04/0.99  --resolution_flag                       false
% 3.04/0.99  --res_lit_sel                           adaptive
% 3.04/0.99  --res_lit_sel_side                      none
% 3.04/0.99  --res_ordering                          kbo
% 3.04/0.99  --res_to_prop_solver                    active
% 3.04/0.99  --res_prop_simpl_new                    false
% 3.04/0.99  --res_prop_simpl_given                  true
% 3.04/0.99  --res_passive_queue_type                priority_queues
% 3.04/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.04/0.99  --res_passive_queues_freq               [15;5]
% 3.04/0.99  --res_forward_subs                      full
% 3.04/0.99  --res_backward_subs                     full
% 3.04/0.99  --res_forward_subs_resolution           true
% 3.04/0.99  --res_backward_subs_resolution          true
% 3.04/0.99  --res_orphan_elimination                true
% 3.04/0.99  --res_time_limit                        2.
% 3.04/0.99  --res_out_proof                         true
% 3.04/0.99  
% 3.04/0.99  ------ Superposition Options
% 3.04/0.99  
% 3.04/0.99  --superposition_flag                    true
% 3.04/0.99  --sup_passive_queue_type                priority_queues
% 3.04/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.04/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.04/0.99  --demod_completeness_check              fast
% 3.04/0.99  --demod_use_ground                      true
% 3.04/0.99  --sup_to_prop_solver                    passive
% 3.04/0.99  --sup_prop_simpl_new                    true
% 3.04/0.99  --sup_prop_simpl_given                  true
% 3.04/0.99  --sup_fun_splitting                     false
% 3.04/0.99  --sup_smt_interval                      50000
% 3.04/0.99  
% 3.04/0.99  ------ Superposition Simplification Setup
% 3.04/0.99  
% 3.04/0.99  --sup_indices_passive                   []
% 3.04/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.04/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.04/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.04/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.04/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.04/0.99  --sup_full_bw                           [BwDemod]
% 3.04/0.99  --sup_immed_triv                        [TrivRules]
% 3.04/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.04/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.04/0.99  --sup_immed_bw_main                     []
% 3.04/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.04/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.04/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.04/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.04/0.99  
% 3.04/0.99  ------ Combination Options
% 3.04/0.99  
% 3.04/0.99  --comb_res_mult                         3
% 3.04/0.99  --comb_sup_mult                         2
% 3.04/0.99  --comb_inst_mult                        10
% 3.04/0.99  
% 3.04/0.99  ------ Debug Options
% 3.04/0.99  
% 3.04/0.99  --dbg_backtrace                         false
% 3.04/0.99  --dbg_dump_prop_clauses                 false
% 3.04/0.99  --dbg_dump_prop_clauses_file            -
% 3.04/0.99  --dbg_out_stat                          false
% 3.04/0.99  
% 3.04/0.99  
% 3.04/0.99  
% 3.04/0.99  
% 3.04/0.99  ------ Proving...
% 3.04/0.99  
% 3.04/0.99  
% 3.04/0.99  % SZS status Theorem for theBenchmark.p
% 3.04/0.99  
% 3.04/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.04/0.99  
% 3.04/0.99  fof(f21,axiom,(
% 3.04/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.04/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.04/0.99  
% 3.04/0.99  fof(f46,plain,(
% 3.04/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.04/0.99    inference(ennf_transformation,[],[f21])).
% 3.04/0.99  
% 3.04/0.99  fof(f47,plain,(
% 3.04/0.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.04/0.99    inference(flattening,[],[f46])).
% 3.04/0.99  
% 3.04/0.99  fof(f56,plain,(
% 3.04/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.04/0.99    inference(nnf_transformation,[],[f47])).
% 3.04/0.99  
% 3.04/0.99  fof(f88,plain,(
% 3.04/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.04/0.99    inference(cnf_transformation,[],[f56])).
% 3.04/0.99  
% 3.04/0.99  fof(f23,conjecture,(
% 3.04/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 3.04/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.04/0.99  
% 3.04/0.99  fof(f24,negated_conjecture,(
% 3.04/0.99    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 3.04/0.99    inference(negated_conjecture,[],[f23])).
% 3.04/0.99  
% 3.04/0.99  fof(f50,plain,(
% 3.04/0.99    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.04/0.99    inference(ennf_transformation,[],[f24])).
% 3.04/0.99  
% 3.04/0.99  fof(f51,plain,(
% 3.04/0.99    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 3.04/0.99    inference(flattening,[],[f50])).
% 3.04/0.99  
% 3.04/0.99  fof(f57,plain,(
% 3.04/0.99    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & k2_relset_1(sK0,sK1,sK2) = sK1 & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 3.04/0.99    introduced(choice_axiom,[])).
% 3.04/0.99  
% 3.04/0.99  fof(f58,plain,(
% 3.04/0.99    (~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & k2_relset_1(sK0,sK1,sK2) = sK1 & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 3.04/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f51,f57])).
% 3.04/0.99  
% 3.04/0.99  fof(f98,plain,(
% 3.04/0.99    v1_funct_2(sK2,sK0,sK1)),
% 3.04/0.99    inference(cnf_transformation,[],[f58])).
% 3.04/0.99  
% 3.04/0.99  fof(f99,plain,(
% 3.04/0.99    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 3.04/0.99    inference(cnf_transformation,[],[f58])).
% 3.04/0.99  
% 3.04/0.99  fof(f19,axiom,(
% 3.04/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.04/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.04/0.99  
% 3.04/0.99  fof(f44,plain,(
% 3.04/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.04/0.99    inference(ennf_transformation,[],[f19])).
% 3.04/0.99  
% 3.04/0.99  fof(f86,plain,(
% 3.04/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.04/0.99    inference(cnf_transformation,[],[f44])).
% 3.04/0.99  
% 3.04/0.99  fof(f18,axiom,(
% 3.04/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.04/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.04/0.99  
% 3.04/0.99  fof(f43,plain,(
% 3.04/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.04/0.99    inference(ennf_transformation,[],[f18])).
% 3.04/0.99  
% 3.04/0.99  fof(f85,plain,(
% 3.04/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.04/0.99    inference(cnf_transformation,[],[f43])).
% 3.04/0.99  
% 3.04/0.99  fof(f14,axiom,(
% 3.04/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 3.04/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.04/0.99  
% 3.04/0.99  fof(f37,plain,(
% 3.04/0.99    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.04/0.99    inference(ennf_transformation,[],[f14])).
% 3.04/0.99  
% 3.04/0.99  fof(f38,plain,(
% 3.04/0.99    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.04/0.99    inference(flattening,[],[f37])).
% 3.04/0.99  
% 3.04/0.99  fof(f78,plain,(
% 3.04/0.99    ( ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.04/0.99    inference(cnf_transformation,[],[f38])).
% 3.04/0.99  
% 3.04/0.99  fof(f100,plain,(
% 3.04/0.99    v2_funct_1(sK2)),
% 3.04/0.99    inference(cnf_transformation,[],[f58])).
% 3.04/0.99  
% 3.04/0.99  fof(f97,plain,(
% 3.04/0.99    v1_funct_1(sK2)),
% 3.04/0.99    inference(cnf_transformation,[],[f58])).
% 3.04/0.99  
% 3.04/0.99  fof(f20,axiom,(
% 3.04/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.04/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.04/0.99  
% 3.04/0.99  fof(f45,plain,(
% 3.04/0.99    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.04/0.99    inference(ennf_transformation,[],[f20])).
% 3.04/0.99  
% 3.04/0.99  fof(f87,plain,(
% 3.04/0.99    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.04/0.99    inference(cnf_transformation,[],[f45])).
% 3.04/0.99  
% 3.04/0.99  fof(f101,plain,(
% 3.04/0.99    k2_relset_1(sK0,sK1,sK2) = sK1),
% 3.04/0.99    inference(cnf_transformation,[],[f58])).
% 3.04/0.99  
% 3.04/0.99  fof(f16,axiom,(
% 3.04/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0))))),
% 3.04/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.04/0.99  
% 3.04/0.99  fof(f41,plain,(
% 3.04/0.99    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.04/0.99    inference(ennf_transformation,[],[f16])).
% 3.04/0.99  
% 3.04/0.99  fof(f42,plain,(
% 3.04/0.99    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.04/0.99    inference(flattening,[],[f41])).
% 3.04/0.99  
% 3.04/0.99  fof(f81,plain,(
% 3.04/0.99    ( ! [X0] : (k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.04/0.99    inference(cnf_transformation,[],[f42])).
% 3.04/0.99  
% 3.04/0.99  fof(f22,axiom,(
% 3.04/0.99    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 3.04/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.04/0.99  
% 3.04/0.99  fof(f48,plain,(
% 3.04/0.99    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.04/0.99    inference(ennf_transformation,[],[f22])).
% 3.04/0.99  
% 3.04/0.99  fof(f49,plain,(
% 3.04/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.04/0.99    inference(flattening,[],[f48])).
% 3.04/0.99  
% 3.04/0.99  fof(f96,plain,(
% 3.04/0.99    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.04/0.99    inference(cnf_transformation,[],[f49])).
% 3.04/0.99  
% 3.04/0.99  fof(f15,axiom,(
% 3.04/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 3.04/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.04/0.99  
% 3.04/0.99  fof(f39,plain,(
% 3.04/0.99    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.04/0.99    inference(ennf_transformation,[],[f15])).
% 3.04/0.99  
% 3.04/0.99  fof(f40,plain,(
% 3.04/0.99    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.04/0.99    inference(flattening,[],[f39])).
% 3.04/0.99  
% 3.04/0.99  fof(f79,plain,(
% 3.04/0.99    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.04/0.99    inference(cnf_transformation,[],[f40])).
% 3.04/0.99  
% 3.04/0.99  fof(f80,plain,(
% 3.04/0.99    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.04/0.99    inference(cnf_transformation,[],[f40])).
% 3.04/0.99  
% 3.04/0.99  fof(f82,plain,(
% 3.04/0.99    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.04/0.99    inference(cnf_transformation,[],[f42])).
% 3.04/0.99  
% 3.04/0.99  fof(f3,axiom,(
% 3.04/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.04/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.04/0.99  
% 3.04/0.99  fof(f52,plain,(
% 3.04/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.04/0.99    inference(nnf_transformation,[],[f3])).
% 3.04/0.99  
% 3.04/0.99  fof(f53,plain,(
% 3.04/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.04/0.99    inference(flattening,[],[f52])).
% 3.04/0.99  
% 3.04/0.99  fof(f61,plain,(
% 3.04/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.04/0.99    inference(cnf_transformation,[],[f53])).
% 3.04/0.99  
% 3.04/0.99  fof(f104,plain,(
% 3.04/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.04/0.99    inference(equality_resolution,[],[f61])).
% 3.04/0.99  
% 3.04/0.99  fof(f89,plain,(
% 3.04/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.04/0.99    inference(cnf_transformation,[],[f56])).
% 3.04/0.99  
% 3.04/0.99  fof(f109,plain,(
% 3.04/0.99    ( ! [X2,X1] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 3.04/0.99    inference(equality_resolution,[],[f89])).
% 3.04/0.99  
% 3.04/0.99  fof(f95,plain,(
% 3.04/0.99    ( ! [X0,X1] : (v1_funct_2(X1,k1_relat_1(X1),X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.04/0.99    inference(cnf_transformation,[],[f49])).
% 3.04/0.99  
% 3.04/0.99  fof(f1,axiom,(
% 3.04/0.99    v1_xboole_0(k1_xboole_0)),
% 3.04/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.04/0.99  
% 3.04/0.99  fof(f59,plain,(
% 3.04/0.99    v1_xboole_0(k1_xboole_0)),
% 3.04/0.99    inference(cnf_transformation,[],[f1])).
% 3.04/0.99  
% 3.04/0.99  fof(f102,plain,(
% 3.04/0.99    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))),
% 3.04/0.99    inference(cnf_transformation,[],[f58])).
% 3.04/0.99  
% 3.04/0.99  fof(f2,axiom,(
% 3.04/0.99    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 3.04/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.04/0.99  
% 3.04/0.99  fof(f28,plain,(
% 3.04/0.99    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 3.04/0.99    inference(ennf_transformation,[],[f2])).
% 3.04/0.99  
% 3.04/0.99  fof(f60,plain,(
% 3.04/0.99    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 3.04/0.99    inference(cnf_transformation,[],[f28])).
% 3.04/0.99  
% 3.04/0.99  fof(f11,axiom,(
% 3.04/0.99    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 3.04/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.04/0.99  
% 3.04/0.99  fof(f33,plain,(
% 3.04/0.99    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 3.04/0.99    inference(ennf_transformation,[],[f11])).
% 3.04/0.99  
% 3.04/0.99  fof(f54,plain,(
% 3.04/0.99    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 3.04/0.99    inference(nnf_transformation,[],[f33])).
% 3.04/0.99  
% 3.04/0.99  fof(f72,plain,(
% 3.04/0.99    ( ! [X0] : (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.04/0.99    inference(cnf_transformation,[],[f54])).
% 3.04/0.99  
% 3.04/0.99  fof(f4,axiom,(
% 3.04/0.99    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.04/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.04/0.99  
% 3.04/0.99  fof(f64,plain,(
% 3.04/0.99    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.04/0.99    inference(cnf_transformation,[],[f4])).
% 3.04/0.99  
% 3.04/0.99  fof(f5,axiom,(
% 3.04/0.99    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 3.04/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.04/0.99  
% 3.04/0.99  fof(f65,plain,(
% 3.04/0.99    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 3.04/0.99    inference(cnf_transformation,[],[f5])).
% 3.04/0.99  
% 3.04/0.99  fof(f9,axiom,(
% 3.04/0.99    ! [X0] : ((v1_relat_1(X0) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k1_relat_1(X0)))),
% 3.04/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.04/0.99  
% 3.04/0.99  fof(f31,plain,(
% 3.04/0.99    ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | (~v1_relat_1(X0) | v1_xboole_0(X0)))),
% 3.04/0.99    inference(ennf_transformation,[],[f9])).
% 3.04/0.99  
% 3.04/0.99  fof(f32,plain,(
% 3.04/0.99    ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0))),
% 3.04/0.99    inference(flattening,[],[f31])).
% 3.04/0.99  
% 3.04/0.99  fof(f69,plain,(
% 3.04/0.99    ( ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0)) )),
% 3.04/0.99    inference(cnf_transformation,[],[f32])).
% 3.04/0.99  
% 3.04/0.99  fof(f90,plain,(
% 3.04/0.99    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.04/0.99    inference(cnf_transformation,[],[f56])).
% 3.04/0.99  
% 3.04/0.99  cnf(c_34,plain,
% 3.04/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.04/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.04/0.99      | k1_relset_1(X1,X2,X0) = X1
% 3.04/0.99      | k1_xboole_0 = X2 ),
% 3.04/0.99      inference(cnf_transformation,[],[f88]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_42,negated_conjecture,
% 3.04/0.99      ( v1_funct_2(sK2,sK0,sK1) ),
% 3.04/0.99      inference(cnf_transformation,[],[f98]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1308,plain,
% 3.04/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.04/0.99      | k1_relset_1(X1,X2,X0) = X1
% 3.04/0.99      | sK0 != X1
% 3.04/0.99      | sK1 != X2
% 3.04/0.99      | sK2 != X0
% 3.04/0.99      | k1_xboole_0 = X2 ),
% 3.04/0.99      inference(resolution_lifted,[status(thm)],[c_34,c_42]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1309,plain,
% 3.04/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.04/0.99      | k1_relset_1(sK0,sK1,sK2) = sK0
% 3.04/0.99      | k1_xboole_0 = sK1 ),
% 3.04/0.99      inference(unflattening,[status(thm)],[c_1308]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_41,negated_conjecture,
% 3.04/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 3.04/0.99      inference(cnf_transformation,[],[f99]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1311,plain,
% 3.04/0.99      ( k1_relset_1(sK0,sK1,sK2) = sK0 | k1_xboole_0 = sK1 ),
% 3.04/0.99      inference(global_propositional_subsumption,
% 3.04/0.99                [status(thm)],
% 3.04/0.99                [c_1309,c_41]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_2360,plain,
% 3.04/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.04/0.99      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_27,plain,
% 3.04/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.04/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.04/0.99      inference(cnf_transformation,[],[f86]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_2363,plain,
% 3.04/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.04/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.04/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_4634,plain,
% 3.04/0.99      ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
% 3.04/0.99      inference(superposition,[status(thm)],[c_2360,c_2363]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_4738,plain,
% 3.04/0.99      ( k1_relat_1(sK2) = sK0 | sK1 = k1_xboole_0 ),
% 3.04/0.99      inference(superposition,[status(thm)],[c_1311,c_4634]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_26,plain,
% 3.04/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.04/0.99      | v1_relat_1(X0) ),
% 3.04/0.99      inference(cnf_transformation,[],[f85]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_2364,plain,
% 3.04/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.04/0.99      | v1_relat_1(X0) = iProver_top ),
% 3.04/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_3858,plain,
% 3.04/0.99      ( v1_relat_1(sK2) = iProver_top ),
% 3.04/0.99      inference(superposition,[status(thm)],[c_2360,c_2364]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_19,plain,
% 3.04/0.99      ( ~ v2_funct_1(X0)
% 3.04/0.99      | ~ v1_funct_1(X0)
% 3.04/0.99      | ~ v1_relat_1(X0)
% 3.04/0.99      | k2_funct_1(X0) = k4_relat_1(X0) ),
% 3.04/0.99      inference(cnf_transformation,[],[f78]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_40,negated_conjecture,
% 3.04/0.99      ( v2_funct_1(sK2) ),
% 3.04/0.99      inference(cnf_transformation,[],[f100]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_516,plain,
% 3.04/0.99      ( ~ v1_funct_1(X0)
% 3.04/0.99      | ~ v1_relat_1(X0)
% 3.04/0.99      | k2_funct_1(X0) = k4_relat_1(X0)
% 3.04/0.99      | sK2 != X0 ),
% 3.04/0.99      inference(resolution_lifted,[status(thm)],[c_19,c_40]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_517,plain,
% 3.04/0.99      ( ~ v1_funct_1(sK2)
% 3.04/0.99      | ~ v1_relat_1(sK2)
% 3.04/0.99      | k2_funct_1(sK2) = k4_relat_1(sK2) ),
% 3.04/0.99      inference(unflattening,[status(thm)],[c_516]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_43,negated_conjecture,
% 3.04/0.99      ( v1_funct_1(sK2) ),
% 3.04/0.99      inference(cnf_transformation,[],[f97]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_519,plain,
% 3.04/0.99      ( ~ v1_relat_1(sK2) | k2_funct_1(sK2) = k4_relat_1(sK2) ),
% 3.04/0.99      inference(global_propositional_subsumption,
% 3.04/0.99                [status(thm)],
% 3.04/0.99                [c_517,c_43]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_2353,plain,
% 3.04/0.99      ( k2_funct_1(sK2) = k4_relat_1(sK2)
% 3.04/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.04/0.99      inference(predicate_to_equality,[status(thm)],[c_519]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_4029,plain,
% 3.04/0.99      ( k2_funct_1(sK2) = k4_relat_1(sK2) ),
% 3.04/0.99      inference(superposition,[status(thm)],[c_3858,c_2353]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_28,plain,
% 3.04/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.04/0.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.04/0.99      inference(cnf_transformation,[],[f87]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_2362,plain,
% 3.04/0.99      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.04/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.04/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_3946,plain,
% 3.04/0.99      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 3.04/0.99      inference(superposition,[status(thm)],[c_2360,c_2362]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_39,negated_conjecture,
% 3.04/0.99      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 3.04/0.99      inference(cnf_transformation,[],[f101]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_3948,plain,
% 3.04/0.99      ( k2_relat_1(sK2) = sK1 ),
% 3.04/0.99      inference(light_normalisation,[status(thm)],[c_3946,c_39]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_23,plain,
% 3.04/0.99      ( ~ v2_funct_1(X0)
% 3.04/0.99      | ~ v1_funct_1(X0)
% 3.04/0.99      | ~ v1_relat_1(X0)
% 3.04/0.99      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 3.04/0.99      inference(cnf_transformation,[],[f81]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_488,plain,
% 3.04/0.99      ( ~ v1_funct_1(X0)
% 3.04/0.99      | ~ v1_relat_1(X0)
% 3.04/0.99      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 3.04/0.99      | sK2 != X0 ),
% 3.04/0.99      inference(resolution_lifted,[status(thm)],[c_23,c_40]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_489,plain,
% 3.04/0.99      ( ~ v1_funct_1(sK2)
% 3.04/0.99      | ~ v1_relat_1(sK2)
% 3.04/0.99      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 3.04/0.99      inference(unflattening,[status(thm)],[c_488]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_491,plain,
% 3.04/0.99      ( ~ v1_relat_1(sK2)
% 3.04/0.99      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 3.04/0.99      inference(global_propositional_subsumption,
% 3.04/0.99                [status(thm)],
% 3.04/0.99                [c_489,c_43]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_2355,plain,
% 3.04/0.99      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
% 3.04/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.04/0.99      inference(predicate_to_equality,[status(thm)],[c_491]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_4004,plain,
% 3.04/0.99      ( k1_relat_1(k2_funct_1(sK2)) = sK1
% 3.04/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.04/0.99      inference(demodulation,[status(thm)],[c_3948,c_2355]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_46,plain,
% 3.04/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.04/0.99      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_2698,plain,
% 3.04/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.04/0.99      | v1_relat_1(sK2) ),
% 3.04/0.99      inference(instantiation,[status(thm)],[c_26]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_2838,plain,
% 3.04/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.04/0.99      | v1_relat_1(sK2) ),
% 3.04/0.99      inference(instantiation,[status(thm)],[c_2698]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_2839,plain,
% 3.04/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.04/0.99      | v1_relat_1(sK2) = iProver_top ),
% 3.04/0.99      inference(predicate_to_equality,[status(thm)],[c_2838]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_4104,plain,
% 3.04/0.99      ( k1_relat_1(k2_funct_1(sK2)) = sK1 ),
% 3.04/0.99      inference(global_propositional_subsumption,
% 3.04/0.99                [status(thm)],
% 3.04/0.99                [c_4004,c_46,c_2839]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_4235,plain,
% 3.04/0.99      ( k1_relat_1(k4_relat_1(sK2)) = sK1 ),
% 3.04/0.99      inference(demodulation,[status(thm)],[c_4029,c_4104]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_35,plain,
% 3.04/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 3.04/0.99      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.04/0.99      | ~ v1_funct_1(X0)
% 3.04/0.99      | ~ v1_relat_1(X0) ),
% 3.04/0.99      inference(cnf_transformation,[],[f96]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_2361,plain,
% 3.04/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
% 3.04/0.99      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 3.04/0.99      | v1_funct_1(X0) != iProver_top
% 3.04/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.04/0.99      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_5443,plain,
% 3.04/0.99      ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) = iProver_top
% 3.04/0.99      | r1_tarski(k2_relat_1(k4_relat_1(sK2)),X0) != iProver_top
% 3.04/0.99      | v1_funct_1(k4_relat_1(sK2)) != iProver_top
% 3.04/0.99      | v1_relat_1(k4_relat_1(sK2)) != iProver_top ),
% 3.04/0.99      inference(superposition,[status(thm)],[c_4235,c_2361]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_44,plain,
% 3.04/0.99      ( v1_funct_1(sK2) = iProver_top ),
% 3.04/0.99      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_21,plain,
% 3.04/0.99      ( ~ v1_funct_1(X0)
% 3.04/0.99      | ~ v1_relat_1(X0)
% 3.04/0.99      | v1_relat_1(k2_funct_1(X0)) ),
% 3.04/0.99      inference(cnf_transformation,[],[f79]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_2367,plain,
% 3.04/0.99      ( v1_funct_1(X0) != iProver_top
% 3.04/0.99      | v1_relat_1(X0) != iProver_top
% 3.04/0.99      | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
% 3.04/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_4728,plain,
% 3.04/0.99      ( v1_funct_1(sK2) != iProver_top
% 3.04/0.99      | v1_relat_1(k4_relat_1(sK2)) = iProver_top
% 3.04/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.04/0.99      inference(superposition,[status(thm)],[c_4029,c_2367]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_20,plain,
% 3.04/0.99      ( ~ v1_funct_1(X0)
% 3.04/0.99      | v1_funct_1(k2_funct_1(X0))
% 3.04/0.99      | ~ v1_relat_1(X0) ),
% 3.04/0.99      inference(cnf_transformation,[],[f80]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_2368,plain,
% 3.04/0.99      ( v1_funct_1(X0) != iProver_top
% 3.04/0.99      | v1_funct_1(k2_funct_1(X0)) = iProver_top
% 3.04/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.04/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_5166,plain,
% 3.04/0.99      ( v1_funct_1(k4_relat_1(sK2)) = iProver_top
% 3.04/0.99      | v1_funct_1(sK2) != iProver_top
% 3.04/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.04/0.99      inference(superposition,[status(thm)],[c_4029,c_2368]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_6362,plain,
% 3.04/0.99      ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) = iProver_top
% 3.04/0.99      | r1_tarski(k2_relat_1(k4_relat_1(sK2)),X0) != iProver_top ),
% 3.04/0.99      inference(global_propositional_subsumption,
% 3.04/0.99                [status(thm)],
% 3.04/0.99                [c_5443,c_44,c_46,c_2839,c_4728,c_5166]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_22,plain,
% 3.04/0.99      ( ~ v2_funct_1(X0)
% 3.04/0.99      | ~ v1_funct_1(X0)
% 3.04/0.99      | ~ v1_relat_1(X0)
% 3.04/0.99      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 3.04/0.99      inference(cnf_transformation,[],[f82]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_502,plain,
% 3.04/0.99      ( ~ v1_funct_1(X0)
% 3.04/0.99      | ~ v1_relat_1(X0)
% 3.04/0.99      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 3.04/0.99      | sK2 != X0 ),
% 3.04/0.99      inference(resolution_lifted,[status(thm)],[c_22,c_40]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_503,plain,
% 3.04/0.99      ( ~ v1_funct_1(sK2)
% 3.04/0.99      | ~ v1_relat_1(sK2)
% 3.04/0.99      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 3.04/0.99      inference(unflattening,[status(thm)],[c_502]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_505,plain,
% 3.04/0.99      ( ~ v1_relat_1(sK2)
% 3.04/0.99      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 3.04/0.99      inference(global_propositional_subsumption,
% 3.04/0.99                [status(thm)],
% 3.04/0.99                [c_503,c_43]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_2354,plain,
% 3.04/0.99      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 3.04/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.04/0.99      inference(predicate_to_equality,[status(thm)],[c_505]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_4028,plain,
% 3.04/0.99      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 3.04/0.99      inference(superposition,[status(thm)],[c_3858,c_2354]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_4032,plain,
% 3.04/0.99      ( k2_relat_1(k4_relat_1(sK2)) = k1_relat_1(sK2) ),
% 3.04/0.99      inference(light_normalisation,[status(thm)],[c_4028,c_4029]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_6368,plain,
% 3.04/0.99      ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) = iProver_top
% 3.04/0.99      | r1_tarski(k1_relat_1(sK2),X0) != iProver_top ),
% 3.04/0.99      inference(light_normalisation,[status(thm)],[c_6362,c_4032]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_4,plain,
% 3.04/0.99      ( r1_tarski(X0,X0) ),
% 3.04/0.99      inference(cnf_transformation,[],[f104]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_2378,plain,
% 3.04/0.99      ( r1_tarski(X0,X0) = iProver_top ),
% 3.04/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_6374,plain,
% 3.04/0.99      ( k1_relset_1(sK1,X0,k4_relat_1(sK2)) = k1_relat_1(k4_relat_1(sK2))
% 3.04/0.99      | r1_tarski(k1_relat_1(sK2),X0) != iProver_top ),
% 3.04/0.99      inference(superposition,[status(thm)],[c_6368,c_2363]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_6384,plain,
% 3.04/0.99      ( k1_relset_1(sK1,X0,k4_relat_1(sK2)) = sK1
% 3.04/0.99      | r1_tarski(k1_relat_1(sK2),X0) != iProver_top ),
% 3.04/0.99      inference(light_normalisation,[status(thm)],[c_6374,c_4235]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_6470,plain,
% 3.04/0.99      ( k1_relset_1(sK1,k1_relat_1(sK2),k4_relat_1(sK2)) = sK1 ),
% 3.04/0.99      inference(superposition,[status(thm)],[c_2378,c_6384]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_6639,plain,
% 3.04/0.99      ( k1_relset_1(sK1,sK0,k4_relat_1(sK2)) = sK1 | sK1 = k1_xboole_0 ),
% 3.04/0.99      inference(superposition,[status(thm)],[c_4738,c_6470]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_33,plain,
% 3.04/0.99      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 3.04/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.04/0.99      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 3.04/0.99      inference(cnf_transformation,[],[f109]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_36,plain,
% 3.04/0.99      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 3.04/0.99      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.04/0.99      | ~ v1_funct_1(X0)
% 3.04/0.99      | ~ v1_relat_1(X0) ),
% 3.04/0.99      inference(cnf_transformation,[],[f95]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1207,plain,
% 3.04/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.04/0.99      | ~ r1_tarski(k2_relat_1(X2),X3)
% 3.04/0.99      | ~ v1_funct_1(X2)
% 3.04/0.99      | ~ v1_relat_1(X2)
% 3.04/0.99      | X2 != X0
% 3.04/0.99      | X3 != X1
% 3.04/0.99      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
% 3.04/0.99      | k1_relat_1(X2) != k1_xboole_0 ),
% 3.04/0.99      inference(resolution_lifted,[status(thm)],[c_33,c_36]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1208,plain,
% 3.04/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.04/0.99      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.04/0.99      | ~ v1_funct_1(X0)
% 3.04/0.99      | ~ v1_relat_1(X0)
% 3.04/0.99      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
% 3.04/0.99      | k1_relat_1(X0) != k1_xboole_0 ),
% 3.04/0.99      inference(unflattening,[status(thm)],[c_1207]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1224,plain,
% 3.04/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.04/0.99      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.04/0.99      | ~ v1_funct_1(X0)
% 3.04/0.99      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
% 3.04/0.99      | k1_relat_1(X0) != k1_xboole_0 ),
% 3.04/0.99      inference(forward_subsumption_resolution,
% 3.04/0.99                [status(thm)],
% 3.04/0.99                [c_1208,c_26]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_2349,plain,
% 3.04/0.99      ( k1_relset_1(k1_xboole_0,X0,X1) = k1_xboole_0
% 3.04/0.99      | k1_relat_1(X1) != k1_xboole_0
% 3.04/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top
% 3.04/0.99      | r1_tarski(k2_relat_1(X1),X0) != iProver_top
% 3.04/0.99      | v1_funct_1(X1) != iProver_top ),
% 3.04/0.99      inference(predicate_to_equality,[status(thm)],[c_1224]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_4110,plain,
% 3.04/0.99      ( k1_relset_1(k1_xboole_0,X0,k2_funct_1(sK2)) = k1_xboole_0
% 3.04/0.99      | sK1 != k1_xboole_0
% 3.04/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top
% 3.04/0.99      | r1_tarski(k2_relat_1(k2_funct_1(sK2)),X0) != iProver_top
% 3.04/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.04/0.99      inference(superposition,[status(thm)],[c_4104,c_2349]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_0,plain,
% 3.04/0.99      ( v1_xboole_0(k1_xboole_0) ),
% 3.04/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1674,plain,( X0 = X0 ),theory(equality) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_2865,plain,
% 3.04/0.99      ( sK0 = sK0 ),
% 3.04/0.99      inference(instantiation,[status(thm)],[c_1674]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_38,negated_conjecture,
% 3.04/0.99      ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
% 3.04/0.99      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.04/0.99      | ~ v1_funct_1(k2_funct_1(sK2)) ),
% 3.04/0.99      inference(cnf_transformation,[],[f102]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1319,plain,
% 3.04/0.99      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.04/0.99      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.04/0.99      | ~ v1_funct_1(X0)
% 3.04/0.99      | ~ v1_funct_1(k2_funct_1(sK2))
% 3.04/0.99      | ~ v1_relat_1(X0)
% 3.04/0.99      | k2_funct_1(sK2) != X0
% 3.04/0.99      | k1_relat_1(X0) != sK1
% 3.04/0.99      | sK0 != X1 ),
% 3.04/0.99      inference(resolution_lifted,[status(thm)],[c_36,c_38]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1320,plain,
% 3.04/0.99      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.04/0.99      | ~ r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0)
% 3.04/0.99      | ~ v1_funct_1(k2_funct_1(sK2))
% 3.04/0.99      | ~ v1_relat_1(k2_funct_1(sK2))
% 3.04/0.99      | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
% 3.04/0.99      inference(unflattening,[status(thm)],[c_1319]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1332,plain,
% 3.04/0.99      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.04/0.99      | ~ r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0)
% 3.04/0.99      | ~ v1_funct_1(k2_funct_1(sK2))
% 3.04/0.99      | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
% 3.04/0.99      inference(forward_subsumption_resolution,
% 3.04/0.99                [status(thm)],
% 3.04/0.99                [c_1320,c_26]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_2344,plain,
% 3.04/0.99      ( k1_relat_1(k2_funct_1(sK2)) != sK1
% 3.04/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.04/0.99      | r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0) != iProver_top
% 3.04/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.04/0.99      inference(predicate_to_equality,[status(thm)],[c_1332]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1337,plain,
% 3.04/0.99      ( k1_relat_1(k2_funct_1(sK2)) != sK1
% 3.04/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.04/0.99      | r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0) != iProver_top
% 3.04/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.04/0.99      inference(predicate_to_equality,[status(thm)],[c_1332]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_2689,plain,
% 3.04/0.99      ( v1_funct_1(k2_funct_1(sK2))
% 3.04/0.99      | ~ v1_funct_1(sK2)
% 3.04/0.99      | ~ v1_relat_1(sK2) ),
% 3.04/0.99      inference(instantiation,[status(thm)],[c_20]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_2690,plain,
% 3.04/0.99      ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
% 3.04/0.99      | v1_funct_1(sK2) != iProver_top
% 3.04/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.04/0.99      inference(predicate_to_equality,[status(thm)],[c_2689]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_3005,plain,
% 3.04/0.99      ( r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0) != iProver_top
% 3.04/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.04/0.99      | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
% 3.04/0.99      inference(global_propositional_subsumption,
% 3.04/0.99                [status(thm)],
% 3.04/0.99                [c_2344,c_44,c_46,c_1337,c_2690,c_2839]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_3006,plain,
% 3.04/0.99      ( k1_relat_1(k2_funct_1(sK2)) != sK1
% 3.04/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.04/0.99      | r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0) != iProver_top ),
% 3.04/0.99      inference(renaming,[status(thm)],[c_3005]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_3007,plain,
% 3.04/0.99      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.04/0.99      | ~ r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0)
% 3.04/0.99      | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
% 3.04/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_3006]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_3068,plain,
% 3.04/0.99      ( ~ v1_funct_1(sK2)
% 3.04/0.99      | v1_relat_1(k2_funct_1(sK2))
% 3.04/0.99      | ~ v1_relat_1(sK2) ),
% 3.04/0.99      inference(instantiation,[status(thm)],[c_21]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_3069,plain,
% 3.04/0.99      ( v1_funct_1(sK2) != iProver_top
% 3.04/0.99      | v1_relat_1(k2_funct_1(sK2)) = iProver_top
% 3.04/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.04/0.99      inference(predicate_to_equality,[status(thm)],[c_3068]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1675,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_2853,plain,
% 3.04/0.99      ( X0 != X1 | k2_funct_1(sK2) != X1 | k2_funct_1(sK2) = X0 ),
% 3.04/0.99      inference(instantiation,[status(thm)],[c_1675]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_3295,plain,
% 3.04/0.99      ( X0 != k4_relat_1(sK2)
% 3.04/0.99      | k2_funct_1(sK2) = X0
% 3.04/0.99      | k2_funct_1(sK2) != k4_relat_1(sK2) ),
% 3.04/0.99      inference(instantiation,[status(thm)],[c_2853]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_3296,plain,
% 3.04/0.99      ( k2_funct_1(sK2) != k4_relat_1(sK2)
% 3.04/0.99      | k2_funct_1(sK2) = k1_xboole_0
% 3.04/0.99      | k1_xboole_0 != k4_relat_1(sK2) ),
% 3.04/0.99      inference(instantiation,[status(thm)],[c_3295]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1679,plain,
% 3.04/0.99      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.04/0.99      theory(equality) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_2744,plain,
% 3.04/0.99      ( m1_subset_1(X0,X1)
% 3.04/0.99      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
% 3.04/0.99      | X1 != k1_zfmisc_1(X2)
% 3.04/0.99      | X0 != k1_xboole_0 ),
% 3.04/0.99      inference(instantiation,[status(thm)],[c_1679]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_2910,plain,
% 3.04/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.04/0.99      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
% 3.04/0.99      | X0 != k1_xboole_0
% 3.04/0.99      | k1_zfmisc_1(X1) != k1_zfmisc_1(X1) ),
% 3.04/0.99      inference(instantiation,[status(thm)],[c_2744]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_3367,plain,
% 3.04/0.99      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.04/0.99      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.04/0.99      | k2_funct_1(sK2) != k1_xboole_0
% 3.04/0.99      | k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
% 3.04/0.99      inference(instantiation,[status(thm)],[c_2910]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1677,plain,
% 3.04/0.99      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.04/0.99      theory(equality) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_2739,plain,
% 3.04/0.99      ( ~ r1_tarski(X0,X1)
% 3.04/0.99      | r1_tarski(k2_relat_1(X2),X3)
% 3.04/0.99      | X3 != X1
% 3.04/0.99      | k2_relat_1(X2) != X0 ),
% 3.04/0.99      inference(instantiation,[status(thm)],[c_1677]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_3130,plain,
% 3.04/0.99      ( ~ r1_tarski(X0,X1)
% 3.04/0.99      | r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0)
% 3.04/0.99      | k2_relat_1(k2_funct_1(sK2)) != X0
% 3.04/0.99      | sK0 != X1 ),
% 3.04/0.99      inference(instantiation,[status(thm)],[c_2739]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_3454,plain,
% 3.04/0.99      ( ~ r1_tarski(X0,sK0)
% 3.04/0.99      | r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0)
% 3.04/0.99      | k2_relat_1(k2_funct_1(sK2)) != X0
% 3.04/0.99      | sK0 != sK0 ),
% 3.04/0.99      inference(instantiation,[status(thm)],[c_3130]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_3456,plain,
% 3.04/0.99      ( r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0)
% 3.04/0.99      | ~ r1_tarski(k1_xboole_0,sK0)
% 3.04/0.99      | k2_relat_1(k2_funct_1(sK2)) != k1_xboole_0
% 3.04/0.99      | sK0 != sK0 ),
% 3.04/0.99      inference(instantiation,[status(thm)],[c_3454]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1,plain,
% 3.04/0.99      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 3.04/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_3474,plain,
% 3.04/0.99      ( ~ v1_xboole_0(k4_relat_1(sK2)) | k1_xboole_0 = k4_relat_1(sK2) ),
% 3.04/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1676,plain,
% 3.04/0.99      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 3.04/0.99      theory(equality) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_3887,plain,
% 3.04/0.99      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK1) | sK1 != X0 ),
% 3.04/0.99      inference(instantiation,[status(thm)],[c_1676]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_3889,plain,
% 3.04/0.99      ( v1_xboole_0(sK1)
% 3.04/0.99      | ~ v1_xboole_0(k1_xboole_0)
% 3.04/0.99      | sK1 != k1_xboole_0 ),
% 3.04/0.99      inference(instantiation,[status(thm)],[c_3887]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_14,plain,
% 3.04/0.99      ( ~ v1_relat_1(X0)
% 3.04/0.99      | k2_relat_1(X0) = k1_xboole_0
% 3.04/0.99      | k1_relat_1(X0) != k1_xboole_0 ),
% 3.04/0.99      inference(cnf_transformation,[],[f72]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_2370,plain,
% 3.04/0.99      ( k2_relat_1(X0) = k1_xboole_0
% 3.04/0.99      | k1_relat_1(X0) != k1_xboole_0
% 3.04/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.04/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_4109,plain,
% 3.04/0.99      ( k2_relat_1(k2_funct_1(sK2)) = k1_xboole_0
% 3.04/0.99      | sK1 != k1_xboole_0
% 3.04/0.99      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 3.04/0.99      inference(superposition,[status(thm)],[c_4104,c_2370]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_5,plain,
% 3.04/0.99      ( r1_tarski(k1_xboole_0,X0) ),
% 3.04/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_4195,plain,
% 3.04/0.99      ( r1_tarski(k1_xboole_0,sK0) ),
% 3.04/0.99      inference(instantiation,[status(thm)],[c_5]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_4736,plain,
% 3.04/0.99      ( ~ v1_funct_1(sK2)
% 3.04/0.99      | v1_relat_1(k4_relat_1(sK2))
% 3.04/0.99      | ~ v1_relat_1(sK2) ),
% 3.04/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_4728]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_6,plain,
% 3.04/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 3.04/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_2724,plain,
% 3.04/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 3.04/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_5005,plain,
% 3.04/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 3.04/0.99      inference(instantiation,[status(thm)],[c_2724]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_10,plain,
% 3.04/0.99      ( ~ v1_relat_1(X0)
% 3.04/0.99      | v1_xboole_0(X0)
% 3.04/0.99      | ~ v1_xboole_0(k1_relat_1(X0)) ),
% 3.04/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_2372,plain,
% 3.04/0.99      ( v1_relat_1(X0) != iProver_top
% 3.04/0.99      | v1_xboole_0(X0) = iProver_top
% 3.04/0.99      | v1_xboole_0(k1_relat_1(X0)) != iProver_top ),
% 3.04/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_5236,plain,
% 3.04/0.99      ( v1_relat_1(k4_relat_1(sK2)) != iProver_top
% 3.04/0.99      | v1_xboole_0(k4_relat_1(sK2)) = iProver_top
% 3.04/0.99      | v1_xboole_0(sK1) != iProver_top ),
% 3.04/0.99      inference(superposition,[status(thm)],[c_4235,c_2372]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_5252,plain,
% 3.04/0.99      ( ~ v1_relat_1(k4_relat_1(sK2))
% 3.04/0.99      | v1_xboole_0(k4_relat_1(sK2))
% 3.04/0.99      | ~ v1_xboole_0(sK1) ),
% 3.04/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_5236]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_2911,plain,
% 3.04/0.99      ( k1_zfmisc_1(X0) = k1_zfmisc_1(X0) ),
% 3.04/0.99      inference(instantiation,[status(thm)],[c_1674]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_5638,plain,
% 3.04/0.99      ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) = k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
% 3.04/0.99      inference(instantiation,[status(thm)],[c_2911]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_5650,plain,
% 3.04/0.99      ( sK1 != k1_xboole_0 ),
% 3.04/0.99      inference(global_propositional_subsumption,
% 3.04/0.99                [status(thm)],
% 3.04/0.99                [c_4110,c_43,c_44,c_41,c_46,c_0,c_517,c_2838,c_2839,
% 3.04/0.99                 c_2865,c_3007,c_3069,c_3296,c_3367,c_3456,c_3474,c_3889,
% 3.04/0.99                 c_4004,c_4109,c_4195,c_4736,c_5005,c_5252,c_5638]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_6845,plain,
% 3.04/0.99      ( k1_relset_1(sK1,sK0,k4_relat_1(sK2)) = sK1 ),
% 3.04/0.99      inference(global_propositional_subsumption,
% 3.04/0.99                [status(thm)],
% 3.04/0.99                [c_6639,c_43,c_44,c_41,c_46,c_0,c_517,c_2838,c_2839,
% 3.04/0.99                 c_2865,c_3007,c_3069,c_3296,c_3367,c_3456,c_3474,c_3889,
% 3.04/0.99                 c_4004,c_4109,c_4195,c_4736,c_5005,c_5252,c_5638]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_32,plain,
% 3.04/0.99      ( v1_funct_2(X0,X1,X2)
% 3.04/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.04/0.99      | k1_relset_1(X1,X2,X0) != X1
% 3.04/0.99      | k1_xboole_0 = X2 ),
% 3.04/0.99      inference(cnf_transformation,[],[f90]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1292,plain,
% 3.04/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.04/0.99      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.04/0.99      | ~ v1_funct_1(k2_funct_1(sK2))
% 3.04/0.99      | k1_relset_1(X1,X2,X0) != X1
% 3.04/0.99      | k2_funct_1(sK2) != X0
% 3.04/0.99      | sK0 != X2
% 3.04/0.99      | sK1 != X1
% 3.04/0.99      | k1_xboole_0 = X2 ),
% 3.04/0.99      inference(resolution_lifted,[status(thm)],[c_32,c_38]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1293,plain,
% 3.04/0.99      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.04/0.99      | ~ v1_funct_1(k2_funct_1(sK2))
% 3.04/0.99      | k1_relset_1(sK1,sK0,k2_funct_1(sK2)) != sK1
% 3.04/0.99      | k1_xboole_0 = sK0 ),
% 3.04/0.99      inference(unflattening,[status(thm)],[c_1292]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_2345,plain,
% 3.04/0.99      ( k1_relset_1(sK1,sK0,k2_funct_1(sK2)) != sK1
% 3.04/0.99      | k1_xboole_0 = sK0
% 3.04/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.04/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.04/0.99      inference(predicate_to_equality,[status(thm)],[c_1293]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1294,plain,
% 3.04/0.99      ( k1_relset_1(sK1,sK0,k2_funct_1(sK2)) != sK1
% 3.04/0.99      | k1_xboole_0 = sK0
% 3.04/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.04/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.04/0.99      inference(predicate_to_equality,[status(thm)],[c_1293]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_2870,plain,
% 3.04/0.99      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.04/0.99      | k1_xboole_0 = sK0
% 3.04/0.99      | k1_relset_1(sK1,sK0,k2_funct_1(sK2)) != sK1 ),
% 3.04/0.99      inference(global_propositional_subsumption,
% 3.04/0.99                [status(thm)],
% 3.04/0.99                [c_2345,c_44,c_46,c_1294,c_2690,c_2839]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_2871,plain,
% 3.04/0.99      ( k1_relset_1(sK1,sK0,k2_funct_1(sK2)) != sK1
% 3.04/0.99      | k1_xboole_0 = sK0
% 3.04/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 3.04/0.99      inference(renaming,[status(thm)],[c_2870]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_4238,plain,
% 3.04/0.99      ( k1_relset_1(sK1,sK0,k4_relat_1(sK2)) != sK1
% 3.04/0.99      | sK0 = k1_xboole_0
% 3.04/0.99      | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 3.04/0.99      inference(demodulation,[status(thm)],[c_4029,c_2871]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_6848,plain,
% 3.04/0.99      ( sK0 = k1_xboole_0
% 3.04/0.99      | sK1 != sK1
% 3.04/0.99      | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 3.04/0.99      inference(demodulation,[status(thm)],[c_6845,c_4238]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_6958,plain,
% 3.04/0.99      ( sK0 = k1_xboole_0
% 3.04/0.99      | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 3.04/0.99      inference(equality_resolution_simp,[status(thm)],[c_6848]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_4903,plain,
% 3.04/0.99      ( k2_relat_1(sK2) = k1_xboole_0
% 3.04/0.99      | sK0 != k1_xboole_0
% 3.04/0.99      | sK1 = k1_xboole_0
% 3.04/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.04/0.99      inference(superposition,[status(thm)],[c_4738,c_2370]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_4922,plain,
% 3.04/0.99      ( sK0 != k1_xboole_0
% 3.04/0.99      | sK1 = k1_xboole_0
% 3.04/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.04/0.99      inference(demodulation,[status(thm)],[c_4903,c_3948]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_4929,plain,
% 3.04/0.99      ( ~ v1_relat_1(sK2) | sK0 != k1_xboole_0 | sK1 = k1_xboole_0 ),
% 3.04/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_4922]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_4931,plain,
% 3.04/0.99      ( sK1 = k1_xboole_0 | sK0 != k1_xboole_0 ),
% 3.04/0.99      inference(global_propositional_subsumption,
% 3.04/0.99                [status(thm)],
% 3.04/0.99                [c_4922,c_41,c_2838,c_4929]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_4932,plain,
% 3.04/0.99      ( sK0 != k1_xboole_0 | sK1 = k1_xboole_0 ),
% 3.04/0.99      inference(renaming,[status(thm)],[c_4931]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_6960,plain,
% 3.04/0.99      ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 3.04/0.99      inference(global_propositional_subsumption,
% 3.04/0.99                [status(thm)],
% 3.04/0.99                [c_6958,c_43,c_44,c_41,c_46,c_0,c_517,c_2838,c_2839,
% 3.04/0.99                 c_2865,c_3007,c_3069,c_3296,c_3367,c_3456,c_3474,c_3889,
% 3.04/0.99                 c_4004,c_4109,c_4195,c_4238,c_4736,c_4929,c_5005,c_5252,
% 3.04/0.99                 c_5638,c_6639]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_6965,plain,
% 3.04/0.99      ( r1_tarski(k1_relat_1(sK2),sK0) != iProver_top ),
% 3.04/0.99      inference(superposition,[status(thm)],[c_6368,c_6960]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_7580,plain,
% 3.04/0.99      ( sK1 = k1_xboole_0 | r1_tarski(sK0,sK0) != iProver_top ),
% 3.04/0.99      inference(superposition,[status(thm)],[c_4738,c_6965]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_4087,plain,
% 3.04/0.99      ( r1_tarski(sK0,sK0) ),
% 3.04/0.99      inference(instantiation,[status(thm)],[c_4]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_4090,plain,
% 3.04/0.99      ( r1_tarski(sK0,sK0) = iProver_top ),
% 3.04/0.99      inference(predicate_to_equality,[status(thm)],[c_4087]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(contradiction,plain,
% 3.04/0.99      ( $false ),
% 3.04/0.99      inference(minisat,[status(thm)],[c_7580,c_5650,c_4090]) ).
% 3.04/0.99  
% 3.04/0.99  
% 3.04/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.04/0.99  
% 3.04/0.99  ------                               Statistics
% 3.04/0.99  
% 3.04/0.99  ------ General
% 3.04/0.99  
% 3.04/0.99  abstr_ref_over_cycles:                  0
% 3.04/0.99  abstr_ref_under_cycles:                 0
% 3.04/0.99  gc_basic_clause_elim:                   0
% 3.04/0.99  forced_gc_time:                         0
% 3.04/0.99  parsing_time:                           0.009
% 3.04/0.99  unif_index_cands_time:                  0.
% 3.04/0.99  unif_index_add_time:                    0.
% 3.04/0.99  orderings_time:                         0.
% 3.04/0.99  out_proof_time:                         0.011
% 3.04/0.99  total_time:                             0.199
% 3.04/0.99  num_of_symbols:                         50
% 3.04/0.99  num_of_terms:                           4723
% 3.04/0.99  
% 3.04/0.99  ------ Preprocessing
% 3.04/0.99  
% 3.04/0.99  num_of_splits:                          0
% 3.04/0.99  num_of_split_atoms:                     0
% 3.04/0.99  num_of_reused_defs:                     0
% 3.04/0.99  num_eq_ax_congr_red:                    4
% 3.04/0.99  num_of_sem_filtered_clauses:            1
% 3.04/0.99  num_of_subtypes:                        0
% 3.04/0.99  monotx_restored_types:                  0
% 3.04/0.99  sat_num_of_epr_types:                   0
% 3.04/0.99  sat_num_of_non_cyclic_types:            0
% 3.04/0.99  sat_guarded_non_collapsed_types:        0
% 3.04/0.99  num_pure_diseq_elim:                    0
% 3.04/0.99  simp_replaced_by:                       0
% 3.04/0.99  res_preprocessed:                       200
% 3.04/0.99  prep_upred:                             0
% 3.04/0.99  prep_unflattend:                        72
% 3.04/0.99  smt_new_axioms:                         0
% 3.04/0.99  pred_elim_cands:                        5
% 3.04/0.99  pred_elim:                              2
% 3.04/0.99  pred_elim_cl:                           -3
% 3.04/0.99  pred_elim_cycles:                       5
% 3.04/0.99  merged_defs:                            0
% 3.04/0.99  merged_defs_ncl:                        0
% 3.04/0.99  bin_hyper_res:                          0
% 3.04/0.99  prep_cycles:                            4
% 3.04/0.99  pred_elim_time:                         0.022
% 3.04/0.99  splitting_time:                         0.
% 3.04/0.99  sem_filter_time:                        0.
% 3.04/0.99  monotx_time:                            0.
% 3.04/0.99  subtype_inf_time:                       0.
% 3.04/0.99  
% 3.04/0.99  ------ Problem properties
% 3.04/0.99  
% 3.04/0.99  clauses:                                43
% 3.04/0.99  conjectures:                            3
% 3.04/0.99  epr:                                    10
% 3.04/0.99  horn:                                   39
% 3.04/0.99  ground:                                 19
% 3.04/0.99  unary:                                  11
% 3.04/0.99  binary:                                 15
% 3.04/0.99  lits:                                   107
% 3.04/0.99  lits_eq:                                40
% 3.04/0.99  fd_pure:                                0
% 3.04/0.99  fd_pseudo:                              0
% 3.04/0.99  fd_cond:                                3
% 3.04/0.99  fd_pseudo_cond:                         1
% 3.04/0.99  ac_symbols:                             0
% 3.04/0.99  
% 3.04/0.99  ------ Propositional Solver
% 3.04/0.99  
% 3.04/0.99  prop_solver_calls:                      28
% 3.04/0.99  prop_fast_solver_calls:                 1552
% 3.04/0.99  smt_solver_calls:                       0
% 3.04/0.99  smt_fast_solver_calls:                  0
% 3.04/0.99  prop_num_of_clauses:                    2431
% 3.04/0.99  prop_preprocess_simplified:             7872
% 3.04/0.99  prop_fo_subsumed:                       79
% 3.04/0.99  prop_solver_time:                       0.
% 3.04/0.99  smt_solver_time:                        0.
% 3.04/0.99  smt_fast_solver_time:                   0.
% 3.04/0.99  prop_fast_solver_time:                  0.
% 3.04/0.99  prop_unsat_core_time:                   0.
% 3.04/0.99  
% 3.04/0.99  ------ QBF
% 3.04/0.99  
% 3.04/0.99  qbf_q_res:                              0
% 3.04/0.99  qbf_num_tautologies:                    0
% 3.04/0.99  qbf_prep_cycles:                        0
% 3.04/0.99  
% 3.04/0.99  ------ BMC1
% 3.04/0.99  
% 3.04/0.99  bmc1_current_bound:                     -1
% 3.04/0.99  bmc1_last_solved_bound:                 -1
% 3.04/0.99  bmc1_unsat_core_size:                   -1
% 3.04/0.99  bmc1_unsat_core_parents_size:           -1
% 3.04/0.99  bmc1_merge_next_fun:                    0
% 3.04/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.04/0.99  
% 3.04/0.99  ------ Instantiation
% 3.04/0.99  
% 3.04/0.99  inst_num_of_clauses:                    778
% 3.04/0.99  inst_num_in_passive:                    101
% 3.04/0.99  inst_num_in_active:                     383
% 3.04/0.99  inst_num_in_unprocessed:                294
% 3.04/0.99  inst_num_of_loops:                      500
% 3.04/0.99  inst_num_of_learning_restarts:          0
% 3.04/0.99  inst_num_moves_active_passive:          113
% 3.04/0.99  inst_lit_activity:                      0
% 3.04/0.99  inst_lit_activity_moves:                0
% 3.04/0.99  inst_num_tautologies:                   0
% 3.04/0.99  inst_num_prop_implied:                  0
% 3.04/0.99  inst_num_existing_simplified:           0
% 3.04/0.99  inst_num_eq_res_simplified:             0
% 3.04/0.99  inst_num_child_elim:                    0
% 3.04/0.99  inst_num_of_dismatching_blockings:      234
% 3.04/0.99  inst_num_of_non_proper_insts:           779
% 3.04/0.99  inst_num_of_duplicates:                 0
% 3.04/0.99  inst_inst_num_from_inst_to_res:         0
% 3.04/0.99  inst_dismatching_checking_time:         0.
% 3.04/0.99  
% 3.04/0.99  ------ Resolution
% 3.04/0.99  
% 3.04/0.99  res_num_of_clauses:                     0
% 3.04/0.99  res_num_in_passive:                     0
% 3.04/0.99  res_num_in_active:                      0
% 3.04/0.99  res_num_of_loops:                       204
% 3.04/0.99  res_forward_subset_subsumed:            78
% 3.04/0.99  res_backward_subset_subsumed:           4
% 3.04/0.99  res_forward_subsumed:                   1
% 3.04/0.99  res_backward_subsumed:                  0
% 3.04/0.99  res_forward_subsumption_resolution:     4
% 3.04/0.99  res_backward_subsumption_resolution:    0
% 3.04/0.99  res_clause_to_clause_subsumption:       318
% 3.04/0.99  res_orphan_elimination:                 0
% 3.04/0.99  res_tautology_del:                      94
% 3.04/0.99  res_num_eq_res_simplified:              0
% 3.04/0.99  res_num_sel_changes:                    0
% 3.04/0.99  res_moves_from_active_to_pass:          0
% 3.04/0.99  
% 3.04/0.99  ------ Superposition
% 3.04/0.99  
% 3.04/0.99  sup_time_total:                         0.
% 3.04/0.99  sup_time_generating:                    0.
% 3.04/0.99  sup_time_sim_full:                      0.
% 3.04/0.99  sup_time_sim_immed:                     0.
% 3.04/0.99  
% 3.04/0.99  sup_num_of_clauses:                     95
% 3.04/0.99  sup_num_in_active:                      85
% 3.04/0.99  sup_num_in_passive:                     10
% 3.04/0.99  sup_num_of_loops:                       99
% 3.04/0.99  sup_fw_superposition:                   75
% 3.04/0.99  sup_bw_superposition:                   28
% 3.04/0.99  sup_immediate_simplified:               39
% 3.04/0.99  sup_given_eliminated:                   0
% 3.04/0.99  comparisons_done:                       0
% 3.04/0.99  comparisons_avoided:                    10
% 3.04/0.99  
% 3.04/0.99  ------ Simplifications
% 3.04/0.99  
% 3.04/0.99  
% 3.04/0.99  sim_fw_subset_subsumed:                 12
% 3.04/0.99  sim_bw_subset_subsumed:                 5
% 3.04/0.99  sim_fw_subsumed:                        1
% 3.04/0.99  sim_bw_subsumed:                        0
% 3.04/0.99  sim_fw_subsumption_res:                 0
% 3.04/0.99  sim_bw_subsumption_res:                 0
% 3.04/0.99  sim_tautology_del:                      4
% 3.04/0.99  sim_eq_tautology_del:                   15
% 3.04/0.99  sim_eq_res_simp:                        2
% 3.04/0.99  sim_fw_demodulated:                     6
% 3.04/0.99  sim_bw_demodulated:                     12
% 3.04/0.99  sim_light_normalised:                   27
% 3.04/0.99  sim_joinable_taut:                      0
% 3.04/0.99  sim_joinable_simp:                      0
% 3.04/0.99  sim_ac_normalised:                      0
% 3.04/0.99  sim_smt_subsumption:                    0
% 3.04/0.99  
%------------------------------------------------------------------------------
