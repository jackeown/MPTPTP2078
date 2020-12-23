%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:02:49 EST 2020

% Result     : Theorem 8.11s
% Output     : CNFRefutation 8.11s
% Verified   : 
% Statistics : Number of formulae       :  320 (27716 expanded)
%              Number of clauses        :  225 (11572 expanded)
%              Number of leaves         :   24 (4845 expanded)
%              Depth                    :   38
%              Number of atoms          :  934 (119070 expanded)
%              Number of equality atoms :  463 (22513 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f48])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
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

fof(f51,plain,(
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
    inference(flattening,[],[f50])).

fof(f60,plain,(
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
    inference(nnf_transformation,[],[f51])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f116,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f96])).

fof(f22,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2)
      & v5_relat_1(X2,X1)
      & v4_relat_1(X2,X0)
      & v1_relat_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2)
      & v4_relat_1(X2,X0)
      & v1_relat_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(pure_predicate_removal,[],[f22])).

fof(f61,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2)
          & v4_relat_1(X2,X0)
          & v1_relat_1(X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( v1_funct_2(sK0(X0,X1),X0,X1)
        & v1_funct_1(sK0(X0,X1))
        & v4_relat_1(sK0(X0,X1),X0)
        & v1_relat_1(sK0(X0,X1))
        & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
    ! [X0,X1] :
      ( v1_funct_2(sK0(X0,X1),X0,X1)
      & v1_funct_1(sK0(X0,X1))
      & v4_relat_1(sK0(X0,X1),X0)
      & v1_relat_1(sK0(X0,X1))
      & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f61])).

fof(f102,plain,(
    ! [X0,X1] : v1_funct_2(sK0(X0,X1),X0,X1) ),
    inference(cnf_transformation,[],[f62])).

fof(f98,plain,(
    ! [X0,X1] : m1_subset_1(sK0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f62])).

fof(f99,plain,(
    ! [X0,X1] : v1_relat_1(sK0(X0,X1)) ),
    inference(cnf_transformation,[],[f62])).

fof(f8,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f72,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f71,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f80,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f56])).

fof(f67,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f24,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f24])).

fof(f54,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f55,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f54])).

fof(f63,plain,
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
      & k2_relset_1(sK1,sK2,sK3) = sK2
      & v2_funct_1(sK3)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_2(sK3,sK1,sK2)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
      | ~ v1_funct_1(k2_funct_1(sK3)) )
    & k2_relset_1(sK1,sK2,sK3) = sK2
    & v2_funct_1(sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK3,sK1,sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f55,f63])).

fof(f108,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f64])).

fof(f12,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f37,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f36])).

fof(f81,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f109,plain,(
    v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f64])).

fof(f106,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f64])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X2
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f114,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k1_xboole_0,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f97])).

fof(f115,plain,(
    ! [X0] :
      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f114])).

fof(f111,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
    | ~ v1_funct_1(k2_funct_1(sK3)) ),
    inference(cnf_transformation,[],[f64])).

fof(f13,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f39,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f38])).

fof(f83,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f107,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f64])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f110,plain,(
    k2_relset_1(sK1,sK2,sK3) = sK2 ),
    inference(cnf_transformation,[],[f64])).

fof(f15,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f43,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f42])).

fof(f85,plain,(
    ! [X0] :
      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f23,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f53,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f52])).

fof(f104,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f82,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f86,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f79,plain,(
    ! [X0] :
      ( k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f57])).

fof(f112,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f66])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f75,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f105,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f117,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f95])).

cnf(c_26,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k2_relat_1(X0),X2)
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1939,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | r1_tarski(k2_relat_1(X0),X2) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_4,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1953,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_28,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f116])).

cnf(c_33,plain,
    ( v1_funct_2(sK0(X0,X1),X0,X1) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_725,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | X2 != X1
    | sK0(X2,X3) != X0
    | k1_xboole_0 != X3
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_33])).

cnf(c_726,plain,
    ( ~ m1_subset_1(sK0(X0,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | k1_xboole_0 = X0
    | k1_xboole_0 = sK0(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_725])).

cnf(c_37,plain,
    ( m1_subset_1(sK0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_736,plain,
    ( k1_xboole_0 = X0
    | k1_xboole_0 = sK0(X0,k1_xboole_0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_726,c_37])).

cnf(c_36,plain,
    ( v1_relat_1(sK0(X0,X1)) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_1937,plain,
    ( v1_relat_1(sK0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_3068,plain,
    ( k1_xboole_0 = X0
    | v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_736,c_1937])).

cnf(c_11,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_137,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_5,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_359,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_5])).

cnf(c_360,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_359])).

cnf(c_431,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_7,c_360])).

cnf(c_2193,plain,
    ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_431])).

cnf(c_2588,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,X1))
    | ~ v1_relat_1(k2_zfmisc_1(X0,X1))
    | v1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2193])).

cnf(c_2589,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,X1)) != iProver_top
    | v1_relat_1(k2_zfmisc_1(X0,X1)) != iProver_top
    | v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2588])).

cnf(c_3181,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_3182,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3181])).

cnf(c_6258,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3068,c_137,c_2589,c_3182])).

cnf(c_14,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1946,plain,
    ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_6265,plain,
    ( k2_relat_1(k4_relat_1(k1_xboole_0)) = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_6258,c_1946])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1941,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_6196,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | r1_tarski(k2_relat_1(X2),X1) != iProver_top
    | r1_tarski(k1_relat_1(X2),X0) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1939,c_1941])).

cnf(c_37723,plain,
    ( k1_relset_1(X0,X1,k4_relat_1(k1_xboole_0)) = k1_relat_1(k4_relat_1(k1_xboole_0))
    | r1_tarski(k1_relat_1(k4_relat_1(k1_xboole_0)),X0) != iProver_top
    | r1_tarski(k1_relat_1(k1_xboole_0),X1) != iProver_top
    | v1_relat_1(k4_relat_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6265,c_6196])).

cnf(c_1952,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_4347,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | r1_tarski(X2,k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1952,c_1941])).

cnf(c_12337,plain,
    ( k1_relset_1(X0,X1,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1953,c_4347])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1942,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_12375,plain,
    ( m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(X0)) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_12337,c_1942])).

cnf(c_14033,plain,
    ( m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(X0)) = iProver_top
    | r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1952,c_12375])).

cnf(c_14043,plain,
    ( m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14033,c_3182])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1951,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_14049,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_14043,c_1951])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1956,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_5207,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1953,c_1956])).

cnf(c_15079,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_14049,c_5207])).

cnf(c_44,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_1934,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_3837,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK1,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1934,c_1951])).

cnf(c_1932,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_431])).

cnf(c_13883,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_3837,c_1932])).

cnf(c_49,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_2248,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | r1_tarski(sK3,k2_zfmisc_1(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2478,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | r1_tarski(sK3,k2_zfmisc_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_2248])).

cnf(c_2479,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | r1_tarski(sK3,k2_zfmisc_1(sK1,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2478])).

cnf(c_2621,plain,
    ( ~ r1_tarski(sK3,k2_zfmisc_1(sK1,sK2))
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK2))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2193])).

cnf(c_2622,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK1,sK2)) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK1,sK2)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2621])).

cnf(c_2711,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_2712,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2711])).

cnf(c_14288,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13883,c_49,c_2479,c_2622,c_2712])).

cnf(c_16,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(X0) = k4_relat_1(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_43,negated_conjecture,
    ( v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_665,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(X0) = k4_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_43])).

cnf(c_666,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | k2_funct_1(sK3) = k4_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_665])).

cnf(c_46,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_668,plain,
    ( ~ v1_relat_1(sK3)
    | k2_funct_1(sK3) = k4_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_666,c_46])).

cnf(c_1926,plain,
    ( k2_funct_1(sK3) = k4_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_668])).

cnf(c_14304,plain,
    ( k2_funct_1(sK3) = k4_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_14288,c_1926])).

cnf(c_27,plain,
    ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f115])).

cnf(c_41,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
    | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK3)) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_699,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | k2_funct_1(sK3) != k1_xboole_0
    | sK1 != k1_xboole_0
    | sK2 != X0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_41])).

cnf(c_700,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | k2_funct_1(sK3) != k1_xboole_0
    | sK1 != k1_xboole_0
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_699])).

cnf(c_1925,plain,
    ( k2_funct_1(sK3) != k1_xboole_0
    | sK1 != k1_xboole_0
    | k1_xboole_0 = sK2
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_700])).

cnf(c_47,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_701,plain,
    ( k2_funct_1(sK3) != k1_xboole_0
    | sK1 != k1_xboole_0
    | k1_xboole_0 = sK2
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_700])).

cnf(c_17,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_2031,plain,
    ( v1_funct_1(k2_funct_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_2032,plain,
    ( v1_funct_1(k2_funct_1(sK3)) = iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2031])).

cnf(c_2837,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | k1_xboole_0 = sK2
    | sK1 != k1_xboole_0
    | k2_funct_1(sK3) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1925,c_47,c_49,c_701,c_2032,c_2479,c_2622,c_2712])).

cnf(c_2838,plain,
    ( k2_funct_1(sK3) != k1_xboole_0
    | sK1 != k1_xboole_0
    | k1_xboole_0 = sK2
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2837])).

cnf(c_14579,plain,
    ( k4_relat_1(sK3) != k1_xboole_0
    | sK1 != k1_xboole_0
    | sK2 = k1_xboole_0
    | m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_14304,c_2838])).

cnf(c_32,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_45,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_900,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK1 != X1
    | sK2 != X2
    | sK3 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_32,c_45])).

cnf(c_901,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k1_relset_1(sK1,sK2,sK3) = sK1
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_900])).

cnf(c_903,plain,
    ( k1_relset_1(sK1,sK2,sK3) = sK1
    | k1_xboole_0 = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_901,c_44])).

cnf(c_4349,plain,
    ( k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1934,c_1941])).

cnf(c_4475,plain,
    ( k1_relat_1(sK3) = sK1
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_903,c_4349])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1940,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_4201,plain,
    ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1934,c_1940])).

cnf(c_42,negated_conjecture,
    ( k2_relset_1(sK1,sK2,sK3) = sK2 ),
    inference(cnf_transformation,[],[f110])).

cnf(c_4202,plain,
    ( k2_relat_1(sK3) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_4201,c_42])).

cnf(c_21,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_619,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_43])).

cnf(c_620,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_619])).

cnf(c_622,plain,
    ( ~ v1_relat_1(sK3)
    | k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_620,c_46])).

cnf(c_1929,plain,
    ( k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_622])).

cnf(c_4342,plain,
    ( k1_relat_1(k2_funct_1(sK3)) = sK2
    | v1_relat_1(sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4202,c_1929])).

cnf(c_4589,plain,
    ( k1_relat_1(k2_funct_1(sK3)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4342,c_49,c_2479,c_2622,c_2712])).

cnf(c_39,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_924,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(X0)
    | k2_funct_1(sK3) != X0
    | k2_relat_1(X0) != sK1
    | k1_relat_1(X0) != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_39,c_41])).

cnf(c_925,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | k2_relat_1(k2_funct_1(sK3)) != sK1
    | k1_relat_1(k2_funct_1(sK3)) != sK2 ),
    inference(unflattening,[status(thm)],[c_924])).

cnf(c_1916,plain,
    ( k2_relat_1(k2_funct_1(sK3)) != sK1
    | k1_relat_1(k2_funct_1(sK3)) != sK2
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_925])).

cnf(c_926,plain,
    ( k2_relat_1(k2_funct_1(sK3)) != sK1
    | k1_relat_1(k2_funct_1(sK3)) != sK2
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_925])).

cnf(c_18,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_2428,plain,
    ( ~ v1_funct_1(sK3)
    | v1_relat_1(k2_funct_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_2429,plain,
    ( v1_funct_1(sK3) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2428])).

cnf(c_2756,plain,
    ( k2_relat_1(k2_funct_1(sK3)) != sK1
    | k1_relat_1(k2_funct_1(sK3)) != sK2
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1916,c_47,c_49,c_926,c_2032,c_2429,c_2479,c_2622,c_2712])).

cnf(c_4591,plain,
    ( k2_relat_1(k2_funct_1(sK3)) != sK1
    | sK2 != sK2
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4589,c_2756])).

cnf(c_4869,plain,
    ( k2_relat_1(k2_funct_1(sK3)) != sK1
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_4591])).

cnf(c_14577,plain,
    ( k2_relat_1(k4_relat_1(sK3)) != sK1
    | m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_14304,c_4869])).

cnf(c_20,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_633,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_43])).

cnf(c_634,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_633])).

cnf(c_636,plain,
    ( ~ v1_relat_1(sK3)
    | k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_634,c_46])).

cnf(c_1928,plain,
    ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_636])).

cnf(c_14303,plain,
    ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_14288,c_1928])).

cnf(c_14305,plain,
    ( k2_relat_1(k4_relat_1(sK3)) = k1_relat_1(sK3) ),
    inference(demodulation,[status(thm)],[c_14303,c_14304])).

cnf(c_14586,plain,
    ( k1_relat_1(sK3) != sK1
    | m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_14577,c_14305])).

cnf(c_15553,plain,
    ( m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_14579,c_4475,c_14586])).

cnf(c_15554,plain,
    ( sK2 = k1_xboole_0
    | m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(renaming,[status(thm)],[c_15553])).

cnf(c_15558,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(k2_relat_1(k4_relat_1(sK3)),sK1) != iProver_top
    | r1_tarski(k1_relat_1(k4_relat_1(sK3)),sK2) != iProver_top
    | v1_relat_1(k4_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1939,c_15554])).

cnf(c_15,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1945,plain,
    ( k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_14301,plain,
    ( k1_relat_1(k4_relat_1(sK3)) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_14288,c_1945])).

cnf(c_14307,plain,
    ( k1_relat_1(k4_relat_1(sK3)) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_14301,c_4202])).

cnf(c_15559,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(k1_relat_1(sK3),sK1) != iProver_top
    | r1_tarski(sK2,sK2) != iProver_top
    | v1_relat_1(k4_relat_1(sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_15558,c_14305,c_14307])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_4012,plain,
    ( r1_tarski(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_4013,plain,
    ( r1_tarski(sK2,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4012])).

cnf(c_22,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_9,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_583,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_22,c_9])).

cnf(c_2905,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
    | r1_tarski(k1_relat_1(X0),sK1)
    | ~ v1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_583])).

cnf(c_4772,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | r1_tarski(k1_relat_1(sK3),sK1)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2905])).

cnf(c_4773,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | r1_tarski(k1_relat_1(sK3),sK1) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4772])).

cnf(c_10,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k4_relat_1(X0)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_12666,plain,
    ( v1_relat_1(k4_relat_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_12667,plain,
    ( v1_relat_1(k4_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12666])).

cnf(c_15614,plain,
    ( sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_15559,c_49,c_2479,c_2622,c_2712,c_4013,c_4773,c_12667])).

cnf(c_764,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | sK1 != X1
    | sK2 != k1_xboole_0
    | sK3 != X0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_45])).

cnf(c_765,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
    | sK2 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_764])).

cnf(c_1923,plain,
    ( sK2 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK3
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_765])).

cnf(c_15659,plain,
    ( sK1 = k1_xboole_0
    | sK3 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_15614,c_1923])).

cnf(c_15664,plain,
    ( sK1 = k1_xboole_0
    | sK3 = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_15659])).

cnf(c_2481,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ r1_tarski(sK3,k2_zfmisc_1(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_8463,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
    | ~ r1_tarski(sK3,k2_zfmisc_1(sK1,X0)) ),
    inference(instantiation,[status(thm)],[c_2481])).

cnf(c_8465,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) = iProver_top
    | r1_tarski(sK3,k2_zfmisc_1(sK1,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8463])).

cnf(c_8467,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) = iProver_top
    | r1_tarski(sK3,k2_zfmisc_1(sK1,k1_xboole_0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_8465])).

cnf(c_15658,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK1,k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_15614,c_3837])).

cnf(c_25921,plain,
    ( sK3 = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_15664,c_8467,c_15658])).

cnf(c_25922,plain,
    ( sK1 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_25921])).

cnf(c_15663,plain,
    ( k2_relset_1(sK1,k1_xboole_0,sK3) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_15614,c_42])).

cnf(c_25962,plain,
    ( k2_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_25922,c_15663])).

cnf(c_740,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | X2 != X0
    | k2_relat_1(X2) != k1_xboole_0
    | k1_relat_1(X2) != X1
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_39])).

cnf(c_741,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k1_xboole_0)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = k1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_740])).

cnf(c_2715,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k1_xboole_0)))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | k2_relat_1(sK3) != k1_xboole_0
    | k1_xboole_0 = k1_relat_1(sK3)
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_741])).

cnf(c_2637,plain,
    ( ~ r1_tarski(X0,sK3)
    | ~ r1_tarski(sK3,X0)
    | X0 = sK3 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2730,plain,
    ( ~ r1_tarski(sK3,sK3)
    | sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_2637])).

cnf(c_1027,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2529,plain,
    ( X0 != X1
    | sK3 != X1
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_1027])).

cnf(c_3170,plain,
    ( X0 != sK3
    | sK3 = X0
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_2529])).

cnf(c_3171,plain,
    ( sK3 != sK3
    | sK3 = k1_xboole_0
    | k1_xboole_0 != sK3 ),
    inference(instantiation,[status(thm)],[c_3170])).

cnf(c_3719,plain,
    ( r1_tarski(sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_3818,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ r1_tarski(k2_relat_1(k2_funct_1(sK3)),sK1)
    | ~ r1_tarski(k1_relat_1(k2_funct_1(sK3)),sK2)
    | ~ v1_relat_1(k2_funct_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_2889,plain,
    ( X0 != X1
    | X0 = sK1
    | sK1 != X1 ),
    inference(instantiation,[status(thm)],[c_1027])).

cnf(c_4738,plain,
    ( k2_relat_1(k2_funct_1(sK3)) != X0
    | k2_relat_1(k2_funct_1(sK3)) = sK1
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_2889])).

cnf(c_4739,plain,
    ( k2_relat_1(k2_funct_1(sK3)) = sK1
    | k2_relat_1(k2_funct_1(sK3)) != k1_xboole_0
    | sK1 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4738])).

cnf(c_8450,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k1_xboole_0)))
    | ~ r1_tarski(sK3,k2_zfmisc_1(k1_relat_1(sK3),k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_2481])).

cnf(c_1028,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X1)
    | X2 != X0 ),
    theory(equality)).

cnf(c_2363,plain,
    ( ~ r1_tarski(X0,sK1)
    | r1_tarski(X1,sK1)
    | X1 != X0 ),
    inference(instantiation,[status(thm)],[c_1028])).

cnf(c_3016,plain,
    ( r1_tarski(X0,sK1)
    | ~ r1_tarski(k1_relat_1(X1),sK1)
    | X0 != k1_relat_1(X1) ),
    inference(instantiation,[status(thm)],[c_2363])).

cnf(c_6037,plain,
    ( r1_tarski(X0,sK1)
    | ~ r1_tarski(k1_relat_1(sK3),sK1)
    | X0 != k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_3016])).

cnf(c_11272,plain,
    ( r1_tarski(k2_relat_1(k2_funct_1(sK3)),sK1)
    | ~ r1_tarski(k1_relat_1(sK3),sK1)
    | k2_relat_1(k2_funct_1(sK3)) != k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_6037])).

cnf(c_38,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_1935,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_6162,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2))) = iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4202,c_1935])).

cnf(c_6334,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6162,c_47,c_49,c_2479,c_2622,c_2712])).

cnf(c_6339,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(k1_relat_1(sK3),sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6334,c_1951])).

cnf(c_15650,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(k1_relat_1(sK3),k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_15614,c_6339])).

cnf(c_15695,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(k1_relat_1(sK3),k1_xboole_0)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_15650])).

cnf(c_15657,plain,
    ( k2_relat_1(sK3) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_15614,c_4202])).

cnf(c_2344,plain,
    ( ~ r1_tarski(X0,sK2)
    | r1_tarski(X1,sK2)
    | X1 != X0 ),
    inference(instantiation,[status(thm)],[c_1028])).

cnf(c_2930,plain,
    ( r1_tarski(X0,sK2)
    | ~ r1_tarski(sK2,sK2)
    | X0 != sK2 ),
    inference(instantiation,[status(thm)],[c_2344])).

cnf(c_7882,plain,
    ( r1_tarski(k1_relat_1(X0),sK2)
    | ~ r1_tarski(sK2,sK2)
    | k1_relat_1(X0) != sK2 ),
    inference(instantiation,[status(thm)],[c_2930])).

cnf(c_24413,plain,
    ( r1_tarski(k1_relat_1(k2_funct_1(sK3)),sK2)
    | ~ r1_tarski(sK2,sK2)
    | k1_relat_1(k2_funct_1(sK3)) != sK2 ),
    inference(instantiation,[status(thm)],[c_7882])).

cnf(c_11383,plain,
    ( X0 != X1
    | k2_relat_1(k2_funct_1(sK3)) != X1
    | k2_relat_1(k2_funct_1(sK3)) = X0 ),
    inference(instantiation,[status(thm)],[c_1027])).

cnf(c_26094,plain,
    ( X0 != k1_relat_1(sK3)
    | k2_relat_1(k2_funct_1(sK3)) = X0
    | k2_relat_1(k2_funct_1(sK3)) != k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_11383])).

cnf(c_26095,plain,
    ( k2_relat_1(k2_funct_1(sK3)) != k1_relat_1(sK3)
    | k2_relat_1(k2_funct_1(sK3)) = k1_xboole_0
    | k1_xboole_0 != k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_26094])).

cnf(c_26112,plain,
    ( sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_25962,c_46,c_44,c_49,c_634,c_925,c_2031,c_2428,c_2478,c_2479,c_2621,c_2622,c_2711,c_2712,c_2715,c_2730,c_3171,c_3719,c_3818,c_4012,c_4342,c_4739,c_4772,c_8450,c_11272,c_15695,c_15657,c_24413,c_25922,c_26095])).

cnf(c_15624,plain,
    ( k1_relat_1(k4_relat_1(sK3)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_15614,c_14307])).

cnf(c_26178,plain,
    ( k1_relat_1(k4_relat_1(k1_xboole_0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_26112,c_15624])).

cnf(c_37753,plain,
    ( k1_relset_1(X0,X1,k4_relat_1(k1_xboole_0)) = k1_xboole_0
    | r1_tarski(k1_xboole_0,X0) != iProver_top
    | r1_tarski(k1_xboole_0,X1) != iProver_top
    | v1_relat_1(k4_relat_1(k1_xboole_0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_37723,c_15079,c_26178])).

cnf(c_140,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k4_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_142,plain,
    ( v1_relat_1(k4_relat_1(k1_xboole_0)) = iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_140])).

cnf(c_156,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_38129,plain,
    ( r1_tarski(k1_xboole_0,X1) != iProver_top
    | k1_relset_1(X0,X1,k4_relat_1(k1_xboole_0)) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_37753,c_137,c_142,c_156,c_2589,c_3182])).

cnf(c_38130,plain,
    ( k1_relset_1(X0,X1,k4_relat_1(k1_xboole_0)) = k1_xboole_0
    | r1_tarski(k1_xboole_0,X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_38129])).

cnf(c_38134,plain,
    ( k1_relset_1(X0,X1,k4_relat_1(k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1953,c_38130])).

cnf(c_29,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f117])).

cnf(c_817,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
    | k2_funct_1(sK3) != X0
    | sK1 != X1
    | sK2 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_41])).

cnf(c_818,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
    | sK2 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_817])).

cnf(c_1921,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_818])).

cnf(c_819,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_818])).

cnf(c_2761,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | sK2 != k1_xboole_0
    | k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1921,c_47,c_49,c_819,c_2032,c_2479,c_2622,c_2712])).

cnf(c_2762,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2761])).

cnf(c_14580,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k4_relat_1(sK3)) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_14304,c_2762])).

cnf(c_17046,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k4_relat_1(sK3)) != k1_xboole_0
    | m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14580,c_49,c_2479,c_2622,c_2712,c_4013,c_4773,c_12667,c_15559])).

cnf(c_17050,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k4_relat_1(sK3)) != k1_xboole_0
    | m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_17046,c_15614])).

cnf(c_26168,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k4_relat_1(k1_xboole_0)) != k1_xboole_0
    | m1_subset_1(k4_relat_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_26112,c_17050])).

cnf(c_38302,plain,
    ( k1_xboole_0 != k1_xboole_0
    | m1_subset_1(k4_relat_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_38134,c_26168])).

cnf(c_38527,plain,
    ( m1_subset_1(k4_relat_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_38302])).

cnf(c_38530,plain,
    ( r1_tarski(k2_relat_1(k4_relat_1(k1_xboole_0)),sK1) != iProver_top
    | r1_tarski(k1_relat_1(k4_relat_1(k1_xboole_0)),k1_xboole_0) != iProver_top
    | v1_relat_1(k4_relat_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1939,c_38527])).

cnf(c_38531,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),sK1) != iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
    | v1_relat_1(k4_relat_1(k1_xboole_0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_38530,c_6265,c_26178])).

cnf(c_38532,plain,
    ( r1_tarski(k1_xboole_0,sK1) != iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
    | v1_relat_1(k4_relat_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_38531,c_15079])).

cnf(c_4496,plain,
    ( r1_tarski(k1_xboole_0,sK1) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_4497,plain,
    ( r1_tarski(k1_xboole_0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4496])).

cnf(c_158,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_156])).

cnf(c_38535,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
    inference(grounding,[status(thm)],[c_3182:[bind(X1,$fot(k1_xboole_0)),bind(X0,$fot(k1_xboole_0))]])).

cnf(c_38536,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top
    | v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top
    | v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(grounding,[status(thm)],[c_2589:[bind(X1,$fot(k1_xboole_0)),bind(X0,$fot(k1_xboole_0))]])).

cnf(c_38537,plain,
    ( v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
    inference(grounding,[status(thm)],[c_137:[bind(X1,$fot(k1_xboole_0)),bind(X0,$fot(k1_xboole_0))]])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_38532,c_4497,c_38535,c_38536,c_158,c_142,c_38537])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:12:17 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 8.11/1.47  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.11/1.47  
% 8.11/1.47  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 8.11/1.47  
% 8.11/1.47  ------  iProver source info
% 8.11/1.47  
% 8.11/1.47  git: date: 2020-06-30 10:37:57 +0100
% 8.11/1.47  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 8.11/1.47  git: non_committed_changes: false
% 8.11/1.47  git: last_make_outside_of_git: false
% 8.11/1.47  
% 8.11/1.47  ------ 
% 8.11/1.47  
% 8.11/1.47  ------ Input Options
% 8.11/1.47  
% 8.11/1.47  --out_options                           all
% 8.11/1.47  --tptp_safe_out                         true
% 8.11/1.47  --problem_path                          ""
% 8.11/1.47  --include_path                          ""
% 8.11/1.47  --clausifier                            res/vclausify_rel
% 8.11/1.47  --clausifier_options                    ""
% 8.11/1.47  --stdin                                 false
% 8.11/1.47  --stats_out                             all
% 8.11/1.47  
% 8.11/1.47  ------ General Options
% 8.11/1.47  
% 8.11/1.47  --fof                                   false
% 8.11/1.47  --time_out_real                         305.
% 8.11/1.47  --time_out_virtual                      -1.
% 8.11/1.47  --symbol_type_check                     false
% 8.11/1.47  --clausify_out                          false
% 8.11/1.47  --sig_cnt_out                           false
% 8.11/1.47  --trig_cnt_out                          false
% 8.11/1.47  --trig_cnt_out_tolerance                1.
% 8.11/1.47  --trig_cnt_out_sk_spl                   false
% 8.11/1.47  --abstr_cl_out                          false
% 8.11/1.47  
% 8.11/1.47  ------ Global Options
% 8.11/1.47  
% 8.11/1.47  --schedule                              default
% 8.11/1.47  --add_important_lit                     false
% 8.11/1.47  --prop_solver_per_cl                    1000
% 8.11/1.47  --min_unsat_core                        false
% 8.11/1.47  --soft_assumptions                      false
% 8.11/1.47  --soft_lemma_size                       3
% 8.11/1.47  --prop_impl_unit_size                   0
% 8.11/1.47  --prop_impl_unit                        []
% 8.11/1.47  --share_sel_clauses                     true
% 8.11/1.47  --reset_solvers                         false
% 8.11/1.47  --bc_imp_inh                            [conj_cone]
% 8.11/1.47  --conj_cone_tolerance                   3.
% 8.11/1.47  --extra_neg_conj                        none
% 8.11/1.47  --large_theory_mode                     true
% 8.11/1.47  --prolific_symb_bound                   200
% 8.11/1.47  --lt_threshold                          2000
% 8.11/1.47  --clause_weak_htbl                      true
% 8.11/1.47  --gc_record_bc_elim                     false
% 8.11/1.47  
% 8.11/1.47  ------ Preprocessing Options
% 8.11/1.47  
% 8.11/1.47  --preprocessing_flag                    true
% 8.11/1.47  --time_out_prep_mult                    0.1
% 8.11/1.47  --splitting_mode                        input
% 8.11/1.47  --splitting_grd                         true
% 8.11/1.47  --splitting_cvd                         false
% 8.11/1.47  --splitting_cvd_svl                     false
% 8.11/1.47  --splitting_nvd                         32
% 8.11/1.47  --sub_typing                            true
% 8.11/1.47  --prep_gs_sim                           true
% 8.11/1.47  --prep_unflatten                        true
% 8.11/1.47  --prep_res_sim                          true
% 8.11/1.47  --prep_upred                            true
% 8.11/1.47  --prep_sem_filter                       exhaustive
% 8.11/1.47  --prep_sem_filter_out                   false
% 8.11/1.47  --pred_elim                             true
% 8.11/1.47  --res_sim_input                         true
% 8.11/1.47  --eq_ax_congr_red                       true
% 8.11/1.47  --pure_diseq_elim                       true
% 8.11/1.47  --brand_transform                       false
% 8.11/1.47  --non_eq_to_eq                          false
% 8.11/1.47  --prep_def_merge                        true
% 8.11/1.47  --prep_def_merge_prop_impl              false
% 8.11/1.47  --prep_def_merge_mbd                    true
% 8.11/1.47  --prep_def_merge_tr_red                 false
% 8.11/1.47  --prep_def_merge_tr_cl                  false
% 8.11/1.47  --smt_preprocessing                     true
% 8.11/1.47  --smt_ac_axioms                         fast
% 8.11/1.47  --preprocessed_out                      false
% 8.11/1.47  --preprocessed_stats                    false
% 8.11/1.47  
% 8.11/1.47  ------ Abstraction refinement Options
% 8.11/1.47  
% 8.11/1.47  --abstr_ref                             []
% 8.11/1.47  --abstr_ref_prep                        false
% 8.11/1.47  --abstr_ref_until_sat                   false
% 8.11/1.47  --abstr_ref_sig_restrict                funpre
% 8.11/1.47  --abstr_ref_af_restrict_to_split_sk     false
% 8.11/1.47  --abstr_ref_under                       []
% 8.11/1.47  
% 8.11/1.47  ------ SAT Options
% 8.11/1.47  
% 8.11/1.47  --sat_mode                              false
% 8.11/1.47  --sat_fm_restart_options                ""
% 8.11/1.47  --sat_gr_def                            false
% 8.11/1.47  --sat_epr_types                         true
% 8.11/1.47  --sat_non_cyclic_types                  false
% 8.11/1.47  --sat_finite_models                     false
% 8.11/1.47  --sat_fm_lemmas                         false
% 8.11/1.47  --sat_fm_prep                           false
% 8.11/1.47  --sat_fm_uc_incr                        true
% 8.11/1.47  --sat_out_model                         small
% 8.11/1.47  --sat_out_clauses                       false
% 8.11/1.47  
% 8.11/1.47  ------ QBF Options
% 8.11/1.47  
% 8.11/1.47  --qbf_mode                              false
% 8.11/1.47  --qbf_elim_univ                         false
% 8.11/1.47  --qbf_dom_inst                          none
% 8.11/1.47  --qbf_dom_pre_inst                      false
% 8.11/1.47  --qbf_sk_in                             false
% 8.11/1.47  --qbf_pred_elim                         true
% 8.11/1.47  --qbf_split                             512
% 8.11/1.47  
% 8.11/1.47  ------ BMC1 Options
% 8.11/1.47  
% 8.11/1.47  --bmc1_incremental                      false
% 8.11/1.47  --bmc1_axioms                           reachable_all
% 8.11/1.47  --bmc1_min_bound                        0
% 8.11/1.47  --bmc1_max_bound                        -1
% 8.11/1.47  --bmc1_max_bound_default                -1
% 8.11/1.47  --bmc1_symbol_reachability              true
% 8.11/1.47  --bmc1_property_lemmas                  false
% 8.11/1.47  --bmc1_k_induction                      false
% 8.11/1.47  --bmc1_non_equiv_states                 false
% 8.11/1.47  --bmc1_deadlock                         false
% 8.11/1.47  --bmc1_ucm                              false
% 8.11/1.47  --bmc1_add_unsat_core                   none
% 8.11/1.47  --bmc1_unsat_core_children              false
% 8.11/1.47  --bmc1_unsat_core_extrapolate_axioms    false
% 8.11/1.47  --bmc1_out_stat                         full
% 8.11/1.47  --bmc1_ground_init                      false
% 8.11/1.47  --bmc1_pre_inst_next_state              false
% 8.11/1.47  --bmc1_pre_inst_state                   false
% 8.11/1.47  --bmc1_pre_inst_reach_state             false
% 8.11/1.47  --bmc1_out_unsat_core                   false
% 8.11/1.47  --bmc1_aig_witness_out                  false
% 8.11/1.47  --bmc1_verbose                          false
% 8.11/1.47  --bmc1_dump_clauses_tptp                false
% 8.11/1.47  --bmc1_dump_unsat_core_tptp             false
% 8.11/1.47  --bmc1_dump_file                        -
% 8.11/1.47  --bmc1_ucm_expand_uc_limit              128
% 8.11/1.47  --bmc1_ucm_n_expand_iterations          6
% 8.11/1.47  --bmc1_ucm_extend_mode                  1
% 8.11/1.47  --bmc1_ucm_init_mode                    2
% 8.11/1.47  --bmc1_ucm_cone_mode                    none
% 8.11/1.47  --bmc1_ucm_reduced_relation_type        0
% 8.11/1.47  --bmc1_ucm_relax_model                  4
% 8.11/1.47  --bmc1_ucm_full_tr_after_sat            true
% 8.11/1.47  --bmc1_ucm_expand_neg_assumptions       false
% 8.11/1.47  --bmc1_ucm_layered_model                none
% 8.11/1.47  --bmc1_ucm_max_lemma_size               10
% 8.11/1.47  
% 8.11/1.47  ------ AIG Options
% 8.11/1.47  
% 8.11/1.47  --aig_mode                              false
% 8.11/1.47  
% 8.11/1.47  ------ Instantiation Options
% 8.11/1.47  
% 8.11/1.47  --instantiation_flag                    true
% 8.11/1.47  --inst_sos_flag                         true
% 8.11/1.47  --inst_sos_phase                        true
% 8.11/1.47  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 8.11/1.47  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 8.11/1.47  --inst_lit_sel_side                     num_symb
% 8.11/1.47  --inst_solver_per_active                1400
% 8.11/1.47  --inst_solver_calls_frac                1.
% 8.11/1.47  --inst_passive_queue_type               priority_queues
% 8.11/1.47  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 8.11/1.47  --inst_passive_queues_freq              [25;2]
% 8.11/1.47  --inst_dismatching                      true
% 8.11/1.47  --inst_eager_unprocessed_to_passive     true
% 8.11/1.47  --inst_prop_sim_given                   true
% 8.11/1.47  --inst_prop_sim_new                     false
% 8.11/1.47  --inst_subs_new                         false
% 8.11/1.47  --inst_eq_res_simp                      false
% 8.11/1.47  --inst_subs_given                       false
% 8.11/1.47  --inst_orphan_elimination               true
% 8.11/1.47  --inst_learning_loop_flag               true
% 8.11/1.47  --inst_learning_start                   3000
% 8.11/1.47  --inst_learning_factor                  2
% 8.11/1.47  --inst_start_prop_sim_after_learn       3
% 8.11/1.47  --inst_sel_renew                        solver
% 8.11/1.47  --inst_lit_activity_flag                true
% 8.11/1.47  --inst_restr_to_given                   false
% 8.11/1.47  --inst_activity_threshold               500
% 8.11/1.47  --inst_out_proof                        true
% 8.11/1.47  
% 8.11/1.47  ------ Resolution Options
% 8.11/1.47  
% 8.11/1.47  --resolution_flag                       true
% 8.11/1.47  --res_lit_sel                           adaptive
% 8.11/1.47  --res_lit_sel_side                      none
% 8.11/1.47  --res_ordering                          kbo
% 8.11/1.47  --res_to_prop_solver                    active
% 8.11/1.47  --res_prop_simpl_new                    false
% 8.11/1.47  --res_prop_simpl_given                  true
% 8.11/1.47  --res_passive_queue_type                priority_queues
% 8.11/1.47  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 8.11/1.47  --res_passive_queues_freq               [15;5]
% 8.11/1.47  --res_forward_subs                      full
% 8.11/1.47  --res_backward_subs                     full
% 8.11/1.47  --res_forward_subs_resolution           true
% 8.11/1.47  --res_backward_subs_resolution          true
% 8.11/1.47  --res_orphan_elimination                true
% 8.11/1.47  --res_time_limit                        2.
% 8.11/1.47  --res_out_proof                         true
% 8.11/1.47  
% 8.11/1.47  ------ Superposition Options
% 8.11/1.47  
% 8.11/1.47  --superposition_flag                    true
% 8.11/1.47  --sup_passive_queue_type                priority_queues
% 8.11/1.47  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 8.11/1.47  --sup_passive_queues_freq               [8;1;4]
% 8.11/1.47  --demod_completeness_check              fast
% 8.11/1.47  --demod_use_ground                      true
% 8.11/1.47  --sup_to_prop_solver                    passive
% 8.11/1.47  --sup_prop_simpl_new                    true
% 8.11/1.47  --sup_prop_simpl_given                  true
% 8.11/1.47  --sup_fun_splitting                     true
% 8.11/1.47  --sup_smt_interval                      50000
% 8.11/1.47  
% 8.11/1.47  ------ Superposition Simplification Setup
% 8.11/1.47  
% 8.11/1.47  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 8.11/1.47  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 8.11/1.47  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 8.11/1.47  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 8.11/1.47  --sup_full_triv                         [TrivRules;PropSubs]
% 8.11/1.47  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 8.11/1.47  --sup_full_bw                           [BwDemod;BwSubsumption]
% 8.11/1.47  --sup_immed_triv                        [TrivRules]
% 8.11/1.47  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 8.11/1.47  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 8.11/1.47  --sup_immed_bw_main                     []
% 8.11/1.47  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 8.11/1.47  --sup_input_triv                        [Unflattening;TrivRules]
% 8.11/1.47  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 8.11/1.47  --sup_input_bw                          []
% 8.11/1.47  
% 8.11/1.47  ------ Combination Options
% 8.11/1.47  
% 8.11/1.47  --comb_res_mult                         3
% 8.11/1.47  --comb_sup_mult                         2
% 8.11/1.47  --comb_inst_mult                        10
% 8.11/1.47  
% 8.11/1.47  ------ Debug Options
% 8.11/1.47  
% 8.11/1.47  --dbg_backtrace                         false
% 8.11/1.47  --dbg_dump_prop_clauses                 false
% 8.11/1.47  --dbg_dump_prop_clauses_file            -
% 8.11/1.47  --dbg_out_stat                          false
% 8.11/1.47  ------ Parsing...
% 8.11/1.47  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 8.11/1.47  
% 8.11/1.47  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e 
% 8.11/1.47  
% 8.11/1.47  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 8.11/1.47  
% 8.11/1.47  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 8.11/1.47  ------ Proving...
% 8.11/1.47  ------ Problem Properties 
% 8.11/1.47  
% 8.11/1.47  
% 8.11/1.47  clauses                                 47
% 8.11/1.47  conjectures                             3
% 8.11/1.47  EPR                                     6
% 8.11/1.47  Horn                                    41
% 8.11/1.47  unary                                   11
% 8.11/1.47  binary                                  17
% 8.11/1.47  lits                                    119
% 8.11/1.47  lits eq                                 43
% 8.11/1.47  fd_pure                                 0
% 8.11/1.47  fd_pseudo                               0
% 8.11/1.47  fd_cond                                 2
% 8.11/1.47  fd_pseudo_cond                          1
% 8.11/1.47  AC symbols                              0
% 8.11/1.47  
% 8.11/1.47  ------ Schedule dynamic 5 is on 
% 8.11/1.47  
% 8.11/1.47  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 8.11/1.47  
% 8.11/1.47  
% 8.11/1.47  ------ 
% 8.11/1.47  Current options:
% 8.11/1.47  ------ 
% 8.11/1.47  
% 8.11/1.47  ------ Input Options
% 8.11/1.47  
% 8.11/1.47  --out_options                           all
% 8.11/1.47  --tptp_safe_out                         true
% 8.11/1.47  --problem_path                          ""
% 8.11/1.47  --include_path                          ""
% 8.11/1.47  --clausifier                            res/vclausify_rel
% 8.11/1.47  --clausifier_options                    ""
% 8.11/1.47  --stdin                                 false
% 8.11/1.47  --stats_out                             all
% 8.11/1.47  
% 8.11/1.47  ------ General Options
% 8.11/1.47  
% 8.11/1.47  --fof                                   false
% 8.11/1.47  --time_out_real                         305.
% 8.11/1.47  --time_out_virtual                      -1.
% 8.11/1.47  --symbol_type_check                     false
% 8.11/1.47  --clausify_out                          false
% 8.11/1.47  --sig_cnt_out                           false
% 8.11/1.47  --trig_cnt_out                          false
% 8.11/1.47  --trig_cnt_out_tolerance                1.
% 8.11/1.47  --trig_cnt_out_sk_spl                   false
% 8.11/1.47  --abstr_cl_out                          false
% 8.11/1.47  
% 8.11/1.47  ------ Global Options
% 8.11/1.47  
% 8.11/1.47  --schedule                              default
% 8.11/1.47  --add_important_lit                     false
% 8.11/1.47  --prop_solver_per_cl                    1000
% 8.11/1.47  --min_unsat_core                        false
% 8.11/1.47  --soft_assumptions                      false
% 8.11/1.47  --soft_lemma_size                       3
% 8.11/1.47  --prop_impl_unit_size                   0
% 8.11/1.47  --prop_impl_unit                        []
% 8.11/1.47  --share_sel_clauses                     true
% 8.11/1.47  --reset_solvers                         false
% 8.11/1.47  --bc_imp_inh                            [conj_cone]
% 8.11/1.47  --conj_cone_tolerance                   3.
% 8.11/1.47  --extra_neg_conj                        none
% 8.11/1.47  --large_theory_mode                     true
% 8.11/1.47  --prolific_symb_bound                   200
% 8.11/1.47  --lt_threshold                          2000
% 8.11/1.47  --clause_weak_htbl                      true
% 8.11/1.47  --gc_record_bc_elim                     false
% 8.11/1.47  
% 8.11/1.47  ------ Preprocessing Options
% 8.11/1.47  
% 8.11/1.47  --preprocessing_flag                    true
% 8.11/1.47  --time_out_prep_mult                    0.1
% 8.11/1.47  --splitting_mode                        input
% 8.11/1.47  --splitting_grd                         true
% 8.11/1.47  --splitting_cvd                         false
% 8.11/1.47  --splitting_cvd_svl                     false
% 8.11/1.47  --splitting_nvd                         32
% 8.11/1.47  --sub_typing                            true
% 8.11/1.47  --prep_gs_sim                           true
% 8.11/1.47  --prep_unflatten                        true
% 8.11/1.47  --prep_res_sim                          true
% 8.11/1.47  --prep_upred                            true
% 8.11/1.47  --prep_sem_filter                       exhaustive
% 8.11/1.47  --prep_sem_filter_out                   false
% 8.11/1.47  --pred_elim                             true
% 8.11/1.47  --res_sim_input                         true
% 8.11/1.47  --eq_ax_congr_red                       true
% 8.11/1.47  --pure_diseq_elim                       true
% 8.11/1.47  --brand_transform                       false
% 8.11/1.47  --non_eq_to_eq                          false
% 8.11/1.47  --prep_def_merge                        true
% 8.11/1.47  --prep_def_merge_prop_impl              false
% 8.11/1.47  --prep_def_merge_mbd                    true
% 8.11/1.47  --prep_def_merge_tr_red                 false
% 8.11/1.47  --prep_def_merge_tr_cl                  false
% 8.11/1.47  --smt_preprocessing                     true
% 8.11/1.47  --smt_ac_axioms                         fast
% 8.11/1.47  --preprocessed_out                      false
% 8.11/1.47  --preprocessed_stats                    false
% 8.11/1.47  
% 8.11/1.47  ------ Abstraction refinement Options
% 8.11/1.47  
% 8.11/1.47  --abstr_ref                             []
% 8.11/1.47  --abstr_ref_prep                        false
% 8.11/1.47  --abstr_ref_until_sat                   false
% 8.11/1.47  --abstr_ref_sig_restrict                funpre
% 8.11/1.47  --abstr_ref_af_restrict_to_split_sk     false
% 8.11/1.47  --abstr_ref_under                       []
% 8.11/1.47  
% 8.11/1.47  ------ SAT Options
% 8.11/1.47  
% 8.11/1.47  --sat_mode                              false
% 8.11/1.47  --sat_fm_restart_options                ""
% 8.11/1.47  --sat_gr_def                            false
% 8.11/1.47  --sat_epr_types                         true
% 8.11/1.47  --sat_non_cyclic_types                  false
% 8.11/1.47  --sat_finite_models                     false
% 8.11/1.47  --sat_fm_lemmas                         false
% 8.11/1.47  --sat_fm_prep                           false
% 8.11/1.47  --sat_fm_uc_incr                        true
% 8.11/1.47  --sat_out_model                         small
% 8.11/1.47  --sat_out_clauses                       false
% 8.11/1.47  
% 8.11/1.47  ------ QBF Options
% 8.11/1.47  
% 8.11/1.47  --qbf_mode                              false
% 8.11/1.47  --qbf_elim_univ                         false
% 8.11/1.47  --qbf_dom_inst                          none
% 8.11/1.47  --qbf_dom_pre_inst                      false
% 8.11/1.47  --qbf_sk_in                             false
% 8.11/1.47  --qbf_pred_elim                         true
% 8.11/1.47  --qbf_split                             512
% 8.11/1.47  
% 8.11/1.47  ------ BMC1 Options
% 8.11/1.47  
% 8.11/1.47  --bmc1_incremental                      false
% 8.11/1.47  --bmc1_axioms                           reachable_all
% 8.11/1.47  --bmc1_min_bound                        0
% 8.11/1.47  --bmc1_max_bound                        -1
% 8.11/1.47  --bmc1_max_bound_default                -1
% 8.11/1.47  --bmc1_symbol_reachability              true
% 8.11/1.47  --bmc1_property_lemmas                  false
% 8.11/1.47  --bmc1_k_induction                      false
% 8.11/1.47  --bmc1_non_equiv_states                 false
% 8.11/1.47  --bmc1_deadlock                         false
% 8.11/1.47  --bmc1_ucm                              false
% 8.11/1.47  --bmc1_add_unsat_core                   none
% 8.11/1.47  --bmc1_unsat_core_children              false
% 8.11/1.47  --bmc1_unsat_core_extrapolate_axioms    false
% 8.11/1.47  --bmc1_out_stat                         full
% 8.11/1.47  --bmc1_ground_init                      false
% 8.11/1.47  --bmc1_pre_inst_next_state              false
% 8.11/1.47  --bmc1_pre_inst_state                   false
% 8.11/1.47  --bmc1_pre_inst_reach_state             false
% 8.11/1.47  --bmc1_out_unsat_core                   false
% 8.11/1.47  --bmc1_aig_witness_out                  false
% 8.11/1.47  --bmc1_verbose                          false
% 8.11/1.47  --bmc1_dump_clauses_tptp                false
% 8.11/1.47  --bmc1_dump_unsat_core_tptp             false
% 8.11/1.47  --bmc1_dump_file                        -
% 8.11/1.47  --bmc1_ucm_expand_uc_limit              128
% 8.11/1.47  --bmc1_ucm_n_expand_iterations          6
% 8.11/1.47  --bmc1_ucm_extend_mode                  1
% 8.11/1.47  --bmc1_ucm_init_mode                    2
% 8.11/1.47  --bmc1_ucm_cone_mode                    none
% 8.11/1.47  --bmc1_ucm_reduced_relation_type        0
% 8.11/1.47  --bmc1_ucm_relax_model                  4
% 8.11/1.47  --bmc1_ucm_full_tr_after_sat            true
% 8.11/1.47  --bmc1_ucm_expand_neg_assumptions       false
% 8.11/1.47  --bmc1_ucm_layered_model                none
% 8.11/1.47  --bmc1_ucm_max_lemma_size               10
% 8.11/1.47  
% 8.11/1.47  ------ AIG Options
% 8.11/1.47  
% 8.11/1.47  --aig_mode                              false
% 8.11/1.47  
% 8.11/1.47  ------ Instantiation Options
% 8.11/1.47  
% 8.11/1.47  --instantiation_flag                    true
% 8.11/1.47  --inst_sos_flag                         true
% 8.11/1.47  --inst_sos_phase                        true
% 8.11/1.47  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 8.11/1.47  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 8.11/1.47  --inst_lit_sel_side                     none
% 8.11/1.47  --inst_solver_per_active                1400
% 8.11/1.47  --inst_solver_calls_frac                1.
% 8.11/1.47  --inst_passive_queue_type               priority_queues
% 8.11/1.47  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 8.11/1.47  --inst_passive_queues_freq              [25;2]
% 8.11/1.47  --inst_dismatching                      true
% 8.11/1.47  --inst_eager_unprocessed_to_passive     true
% 8.11/1.47  --inst_prop_sim_given                   true
% 8.11/1.47  --inst_prop_sim_new                     false
% 8.11/1.47  --inst_subs_new                         false
% 8.11/1.47  --inst_eq_res_simp                      false
% 8.11/1.47  --inst_subs_given                       false
% 8.11/1.47  --inst_orphan_elimination               true
% 8.11/1.47  --inst_learning_loop_flag               true
% 8.11/1.47  --inst_learning_start                   3000
% 8.11/1.47  --inst_learning_factor                  2
% 8.11/1.47  --inst_start_prop_sim_after_learn       3
% 8.11/1.47  --inst_sel_renew                        solver
% 8.11/1.47  --inst_lit_activity_flag                true
% 8.11/1.47  --inst_restr_to_given                   false
% 8.11/1.47  --inst_activity_threshold               500
% 8.11/1.47  --inst_out_proof                        true
% 8.11/1.47  
% 8.11/1.47  ------ Resolution Options
% 8.11/1.47  
% 8.11/1.47  --resolution_flag                       false
% 8.11/1.47  --res_lit_sel                           adaptive
% 8.11/1.47  --res_lit_sel_side                      none
% 8.11/1.47  --res_ordering                          kbo
% 8.11/1.47  --res_to_prop_solver                    active
% 8.11/1.47  --res_prop_simpl_new                    false
% 8.11/1.47  --res_prop_simpl_given                  true
% 8.11/1.47  --res_passive_queue_type                priority_queues
% 8.11/1.47  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 8.11/1.47  --res_passive_queues_freq               [15;5]
% 8.11/1.47  --res_forward_subs                      full
% 8.11/1.47  --res_backward_subs                     full
% 8.11/1.47  --res_forward_subs_resolution           true
% 8.11/1.47  --res_backward_subs_resolution          true
% 8.11/1.47  --res_orphan_elimination                true
% 8.11/1.47  --res_time_limit                        2.
% 8.11/1.47  --res_out_proof                         true
% 8.11/1.47  
% 8.11/1.47  ------ Superposition Options
% 8.11/1.47  
% 8.11/1.47  --superposition_flag                    true
% 8.11/1.47  --sup_passive_queue_type                priority_queues
% 8.11/1.47  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 8.11/1.47  --sup_passive_queues_freq               [8;1;4]
% 8.11/1.47  --demod_completeness_check              fast
% 8.11/1.47  --demod_use_ground                      true
% 8.11/1.47  --sup_to_prop_solver                    passive
% 8.11/1.47  --sup_prop_simpl_new                    true
% 8.11/1.47  --sup_prop_simpl_given                  true
% 8.11/1.47  --sup_fun_splitting                     true
% 8.11/1.47  --sup_smt_interval                      50000
% 8.11/1.47  
% 8.11/1.47  ------ Superposition Simplification Setup
% 8.11/1.47  
% 8.11/1.47  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 8.11/1.47  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 8.11/1.47  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 8.11/1.47  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 8.11/1.47  --sup_full_triv                         [TrivRules;PropSubs]
% 8.11/1.47  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 8.11/1.47  --sup_full_bw                           [BwDemod;BwSubsumption]
% 8.11/1.47  --sup_immed_triv                        [TrivRules]
% 8.11/1.47  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 8.11/1.47  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 8.11/1.47  --sup_immed_bw_main                     []
% 8.11/1.47  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 8.11/1.47  --sup_input_triv                        [Unflattening;TrivRules]
% 8.11/1.47  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 8.11/1.47  --sup_input_bw                          []
% 8.11/1.47  
% 8.11/1.47  ------ Combination Options
% 8.11/1.47  
% 8.11/1.47  --comb_res_mult                         3
% 8.11/1.47  --comb_sup_mult                         2
% 8.11/1.47  --comb_inst_mult                        10
% 8.11/1.47  
% 8.11/1.47  ------ Debug Options
% 8.11/1.47  
% 8.11/1.47  --dbg_backtrace                         false
% 8.11/1.47  --dbg_dump_prop_clauses                 false
% 8.11/1.47  --dbg_dump_prop_clauses_file            -
% 8.11/1.47  --dbg_out_stat                          false
% 8.11/1.47  
% 8.11/1.47  
% 8.11/1.47  
% 8.11/1.47  
% 8.11/1.47  ------ Proving...
% 8.11/1.47  
% 8.11/1.47  
% 8.11/1.47  % SZS status Theorem for theBenchmark.p
% 8.11/1.47  
% 8.11/1.47  % SZS output start CNFRefutation for theBenchmark.p
% 8.11/1.47  
% 8.11/1.47  fof(f20,axiom,(
% 8.11/1.47    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 8.11/1.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.11/1.47  
% 8.11/1.47  fof(f48,plain,(
% 8.11/1.47    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 8.11/1.47    inference(ennf_transformation,[],[f20])).
% 8.11/1.47  
% 8.11/1.47  fof(f49,plain,(
% 8.11/1.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 8.11/1.47    inference(flattening,[],[f48])).
% 8.11/1.47  
% 8.11/1.47  fof(f91,plain,(
% 8.11/1.47    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 8.11/1.47    inference(cnf_transformation,[],[f49])).
% 8.11/1.47  
% 8.11/1.47  fof(f3,axiom,(
% 8.11/1.47    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 8.11/1.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.11/1.47  
% 8.11/1.47  fof(f69,plain,(
% 8.11/1.47    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 8.11/1.47    inference(cnf_transformation,[],[f3])).
% 8.11/1.47  
% 8.11/1.47  fof(f21,axiom,(
% 8.11/1.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 8.11/1.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.11/1.47  
% 8.11/1.47  fof(f50,plain,(
% 8.11/1.47    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 8.11/1.47    inference(ennf_transformation,[],[f21])).
% 8.11/1.47  
% 8.11/1.47  fof(f51,plain,(
% 8.11/1.47    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 8.11/1.47    inference(flattening,[],[f50])).
% 8.11/1.47  
% 8.11/1.47  fof(f60,plain,(
% 8.11/1.47    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 8.11/1.47    inference(nnf_transformation,[],[f51])).
% 8.11/1.47  
% 8.11/1.47  fof(f96,plain,(
% 8.11/1.47    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 8.11/1.47    inference(cnf_transformation,[],[f60])).
% 8.11/1.47  
% 8.11/1.47  fof(f116,plain,(
% 8.11/1.47    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 8.11/1.47    inference(equality_resolution,[],[f96])).
% 8.11/1.47  
% 8.11/1.47  fof(f22,axiom,(
% 8.11/1.47    ! [X0,X1] : ? [X2] : (v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & v5_relat_1(X2,X1) & v4_relat_1(X2,X0) & v1_relat_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 8.11/1.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.11/1.47  
% 8.11/1.47  fof(f26,plain,(
% 8.11/1.47    ! [X0,X1] : ? [X2] : (v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & v4_relat_1(X2,X0) & v1_relat_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 8.11/1.47    inference(pure_predicate_removal,[],[f22])).
% 8.11/1.47  
% 8.11/1.47  fof(f61,plain,(
% 8.11/1.47    ! [X1,X0] : (? [X2] : (v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & v4_relat_1(X2,X0) & v1_relat_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (v1_funct_2(sK0(X0,X1),X0,X1) & v1_funct_1(sK0(X0,X1)) & v4_relat_1(sK0(X0,X1),X0) & v1_relat_1(sK0(X0,X1)) & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 8.11/1.47    introduced(choice_axiom,[])).
% 8.11/1.47  
% 8.11/1.47  fof(f62,plain,(
% 8.11/1.47    ! [X0,X1] : (v1_funct_2(sK0(X0,X1),X0,X1) & v1_funct_1(sK0(X0,X1)) & v4_relat_1(sK0(X0,X1),X0) & v1_relat_1(sK0(X0,X1)) & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 8.11/1.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f61])).
% 8.11/1.47  
% 8.11/1.47  fof(f102,plain,(
% 8.11/1.47    ( ! [X0,X1] : (v1_funct_2(sK0(X0,X1),X0,X1)) )),
% 8.11/1.47    inference(cnf_transformation,[],[f62])).
% 8.11/1.47  
% 8.11/1.47  fof(f98,plain,(
% 8.11/1.47    ( ! [X0,X1] : (m1_subset_1(sK0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 8.11/1.47    inference(cnf_transformation,[],[f62])).
% 8.11/1.47  
% 8.11/1.47  fof(f99,plain,(
% 8.11/1.47    ( ! [X0,X1] : (v1_relat_1(sK0(X0,X1))) )),
% 8.11/1.47    inference(cnf_transformation,[],[f62])).
% 8.11/1.47  
% 8.11/1.47  fof(f8,axiom,(
% 8.11/1.47    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 8.11/1.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.11/1.47  
% 8.11/1.47  fof(f76,plain,(
% 8.11/1.47    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 8.11/1.47    inference(cnf_transformation,[],[f8])).
% 8.11/1.47  
% 8.11/1.47  fof(f5,axiom,(
% 8.11/1.47    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 8.11/1.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.11/1.47  
% 8.11/1.47  fof(f30,plain,(
% 8.11/1.47    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 8.11/1.47    inference(ennf_transformation,[],[f5])).
% 8.11/1.47  
% 8.11/1.47  fof(f72,plain,(
% 8.11/1.47    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 8.11/1.47    inference(cnf_transformation,[],[f30])).
% 8.11/1.47  
% 8.11/1.47  fof(f4,axiom,(
% 8.11/1.47    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 8.11/1.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.11/1.47  
% 8.11/1.47  fof(f58,plain,(
% 8.11/1.47    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 8.11/1.47    inference(nnf_transformation,[],[f4])).
% 8.11/1.47  
% 8.11/1.47  fof(f71,plain,(
% 8.11/1.47    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 8.11/1.47    inference(cnf_transformation,[],[f58])).
% 8.11/1.47  
% 8.11/1.47  fof(f11,axiom,(
% 8.11/1.47    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0)))),
% 8.11/1.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.11/1.47  
% 8.11/1.47  fof(f35,plain,(
% 8.11/1.47    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 8.11/1.47    inference(ennf_transformation,[],[f11])).
% 8.11/1.47  
% 8.11/1.47  fof(f80,plain,(
% 8.11/1.47    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 8.11/1.47    inference(cnf_transformation,[],[f35])).
% 8.11/1.47  
% 8.11/1.47  fof(f18,axiom,(
% 8.11/1.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 8.11/1.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.11/1.47  
% 8.11/1.47  fof(f46,plain,(
% 8.11/1.47    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 8.11/1.47    inference(ennf_transformation,[],[f18])).
% 8.11/1.47  
% 8.11/1.47  fof(f89,plain,(
% 8.11/1.47    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 8.11/1.47    inference(cnf_transformation,[],[f46])).
% 8.11/1.47  
% 8.11/1.47  fof(f17,axiom,(
% 8.11/1.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 8.11/1.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.11/1.47  
% 8.11/1.47  fof(f45,plain,(
% 8.11/1.47    ! [X0,X1,X2] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 8.11/1.47    inference(ennf_transformation,[],[f17])).
% 8.11/1.47  
% 8.11/1.47  fof(f88,plain,(
% 8.11/1.47    ( ! [X2,X0,X1] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 8.11/1.47    inference(cnf_transformation,[],[f45])).
% 8.11/1.47  
% 8.11/1.47  fof(f70,plain,(
% 8.11/1.47    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 8.11/1.47    inference(cnf_transformation,[],[f58])).
% 8.11/1.47  
% 8.11/1.47  fof(f1,axiom,(
% 8.11/1.47    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 8.11/1.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.11/1.47  
% 8.11/1.47  fof(f56,plain,(
% 8.11/1.47    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 8.11/1.47    inference(nnf_transformation,[],[f1])).
% 8.11/1.47  
% 8.11/1.47  fof(f57,plain,(
% 8.11/1.47    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 8.11/1.47    inference(flattening,[],[f56])).
% 8.11/1.47  
% 8.11/1.47  fof(f67,plain,(
% 8.11/1.47    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 8.11/1.47    inference(cnf_transformation,[],[f57])).
% 8.11/1.47  
% 8.11/1.47  fof(f24,conjecture,(
% 8.11/1.47    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 8.11/1.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.11/1.47  
% 8.11/1.47  fof(f25,negated_conjecture,(
% 8.11/1.47    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 8.11/1.47    inference(negated_conjecture,[],[f24])).
% 8.11/1.47  
% 8.11/1.47  fof(f54,plain,(
% 8.11/1.47    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 8.11/1.47    inference(ennf_transformation,[],[f25])).
% 8.11/1.47  
% 8.11/1.47  fof(f55,plain,(
% 8.11/1.47    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 8.11/1.47    inference(flattening,[],[f54])).
% 8.11/1.47  
% 8.11/1.47  fof(f63,plain,(
% 8.11/1.47    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))) & k2_relset_1(sK1,sK2,sK3) = sK2 & v2_funct_1(sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3))),
% 8.11/1.47    introduced(choice_axiom,[])).
% 8.11/1.47  
% 8.11/1.47  fof(f64,plain,(
% 8.11/1.47    (~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))) & k2_relset_1(sK1,sK2,sK3) = sK2 & v2_funct_1(sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)),
% 8.11/1.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f55,f63])).
% 8.11/1.47  
% 8.11/1.47  fof(f108,plain,(
% 8.11/1.47    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 8.11/1.47    inference(cnf_transformation,[],[f64])).
% 8.11/1.47  
% 8.11/1.47  fof(f12,axiom,(
% 8.11/1.47    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 8.11/1.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.11/1.47  
% 8.11/1.47  fof(f36,plain,(
% 8.11/1.47    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 8.11/1.47    inference(ennf_transformation,[],[f12])).
% 8.11/1.47  
% 8.11/1.47  fof(f37,plain,(
% 8.11/1.47    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 8.11/1.47    inference(flattening,[],[f36])).
% 8.11/1.47  
% 8.11/1.47  fof(f81,plain,(
% 8.11/1.47    ( ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 8.11/1.47    inference(cnf_transformation,[],[f37])).
% 8.11/1.47  
% 8.11/1.47  fof(f109,plain,(
% 8.11/1.47    v2_funct_1(sK3)),
% 8.11/1.47    inference(cnf_transformation,[],[f64])).
% 8.11/1.47  
% 8.11/1.47  fof(f106,plain,(
% 8.11/1.47    v1_funct_1(sK3)),
% 8.11/1.47    inference(cnf_transformation,[],[f64])).
% 8.11/1.47  
% 8.11/1.47  fof(f97,plain,(
% 8.11/1.47    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2 | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 8.11/1.47    inference(cnf_transformation,[],[f60])).
% 8.11/1.47  
% 8.11/1.47  fof(f114,plain,(
% 8.11/1.47    ( ! [X0,X1] : (v1_funct_2(k1_xboole_0,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 8.11/1.47    inference(equality_resolution,[],[f97])).
% 8.11/1.47  
% 8.11/1.47  fof(f115,plain,(
% 8.11/1.47    ( ! [X0] : (v1_funct_2(k1_xboole_0,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 8.11/1.47    inference(equality_resolution,[],[f114])).
% 8.11/1.47  
% 8.11/1.47  fof(f111,plain,(
% 8.11/1.47    ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))),
% 8.11/1.47    inference(cnf_transformation,[],[f64])).
% 8.11/1.47  
% 8.11/1.47  fof(f13,axiom,(
% 8.11/1.47    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 8.11/1.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.11/1.47  
% 8.11/1.47  fof(f38,plain,(
% 8.11/1.47    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 8.11/1.47    inference(ennf_transformation,[],[f13])).
% 8.11/1.47  
% 8.11/1.47  fof(f39,plain,(
% 8.11/1.47    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 8.11/1.47    inference(flattening,[],[f38])).
% 8.11/1.47  
% 8.11/1.47  fof(f83,plain,(
% 8.11/1.47    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 8.11/1.47    inference(cnf_transformation,[],[f39])).
% 8.11/1.47  
% 8.11/1.47  fof(f92,plain,(
% 8.11/1.47    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 8.11/1.47    inference(cnf_transformation,[],[f60])).
% 8.11/1.47  
% 8.11/1.47  fof(f107,plain,(
% 8.11/1.47    v1_funct_2(sK3,sK1,sK2)),
% 8.11/1.47    inference(cnf_transformation,[],[f64])).
% 8.11/1.47  
% 8.11/1.47  fof(f19,axiom,(
% 8.11/1.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 8.11/1.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.11/1.47  
% 8.11/1.47  fof(f47,plain,(
% 8.11/1.47    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 8.11/1.47    inference(ennf_transformation,[],[f19])).
% 8.11/1.47  
% 8.11/1.47  fof(f90,plain,(
% 8.11/1.47    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 8.11/1.47    inference(cnf_transformation,[],[f47])).
% 8.11/1.47  
% 8.11/1.47  fof(f110,plain,(
% 8.11/1.47    k2_relset_1(sK1,sK2,sK3) = sK2),
% 8.11/1.47    inference(cnf_transformation,[],[f64])).
% 8.11/1.47  
% 8.11/1.47  fof(f15,axiom,(
% 8.11/1.47    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0))))),
% 8.11/1.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.11/1.47  
% 8.11/1.47  fof(f42,plain,(
% 8.11/1.47    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 8.11/1.47    inference(ennf_transformation,[],[f15])).
% 8.11/1.47  
% 8.11/1.47  fof(f43,plain,(
% 8.11/1.47    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 8.11/1.47    inference(flattening,[],[f42])).
% 8.11/1.47  
% 8.11/1.47  fof(f85,plain,(
% 8.11/1.47    ( ! [X0] : (k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 8.11/1.47    inference(cnf_transformation,[],[f43])).
% 8.11/1.47  
% 8.11/1.47  fof(f23,axiom,(
% 8.11/1.47    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 8.11/1.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.11/1.47  
% 8.11/1.47  fof(f52,plain,(
% 8.11/1.47    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 8.11/1.47    inference(ennf_transformation,[],[f23])).
% 8.11/1.47  
% 8.11/1.47  fof(f53,plain,(
% 8.11/1.47    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 8.11/1.47    inference(flattening,[],[f52])).
% 8.11/1.47  
% 8.11/1.47  fof(f104,plain,(
% 8.11/1.47    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 8.11/1.47    inference(cnf_transformation,[],[f53])).
% 8.11/1.47  
% 8.11/1.47  fof(f82,plain,(
% 8.11/1.47    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 8.11/1.47    inference(cnf_transformation,[],[f39])).
% 8.11/1.47  
% 8.11/1.47  fof(f86,plain,(
% 8.11/1.47    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 8.11/1.47    inference(cnf_transformation,[],[f43])).
% 8.11/1.47  
% 8.11/1.47  fof(f79,plain,(
% 8.11/1.47    ( ! [X0] : (k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 8.11/1.47    inference(cnf_transformation,[],[f35])).
% 8.11/1.47  
% 8.11/1.47  fof(f66,plain,(
% 8.11/1.47    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 8.11/1.47    inference(cnf_transformation,[],[f57])).
% 8.11/1.47  
% 8.11/1.47  fof(f112,plain,(
% 8.11/1.47    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 8.11/1.47    inference(equality_resolution,[],[f66])).
% 8.11/1.47  
% 8.11/1.47  fof(f16,axiom,(
% 8.11/1.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 8.11/1.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.11/1.47  
% 8.11/1.47  fof(f27,plain,(
% 8.11/1.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 8.11/1.47    inference(pure_predicate_removal,[],[f16])).
% 8.11/1.47  
% 8.11/1.47  fof(f44,plain,(
% 8.11/1.47    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 8.11/1.47    inference(ennf_transformation,[],[f27])).
% 8.11/1.47  
% 8.11/1.47  fof(f87,plain,(
% 8.11/1.47    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 8.11/1.47    inference(cnf_transformation,[],[f44])).
% 8.11/1.47  
% 8.11/1.47  fof(f6,axiom,(
% 8.11/1.47    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 8.11/1.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.11/1.47  
% 8.11/1.47  fof(f31,plain,(
% 8.11/1.47    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 8.11/1.47    inference(ennf_transformation,[],[f6])).
% 8.11/1.47  
% 8.11/1.47  fof(f59,plain,(
% 8.11/1.47    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 8.11/1.47    inference(nnf_transformation,[],[f31])).
% 8.11/1.47  
% 8.11/1.47  fof(f73,plain,(
% 8.11/1.47    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 8.11/1.47    inference(cnf_transformation,[],[f59])).
% 8.11/1.47  
% 8.11/1.47  fof(f7,axiom,(
% 8.11/1.47    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 8.11/1.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.11/1.47  
% 8.11/1.47  fof(f32,plain,(
% 8.11/1.47    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 8.11/1.47    inference(ennf_transformation,[],[f7])).
% 8.11/1.47  
% 8.11/1.47  fof(f75,plain,(
% 8.11/1.47    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 8.11/1.47    inference(cnf_transformation,[],[f32])).
% 8.11/1.47  
% 8.11/1.47  fof(f105,plain,(
% 8.11/1.47    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 8.11/1.47    inference(cnf_transformation,[],[f53])).
% 8.11/1.47  
% 8.11/1.47  fof(f95,plain,(
% 8.11/1.47    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 8.11/1.47    inference(cnf_transformation,[],[f60])).
% 8.11/1.47  
% 8.11/1.47  fof(f117,plain,(
% 8.11/1.47    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 8.11/1.47    inference(equality_resolution,[],[f95])).
% 8.11/1.47  
% 8.11/1.47  cnf(c_26,plain,
% 8.11/1.47      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 8.11/1.47      | ~ r1_tarski(k2_relat_1(X0),X2)
% 8.11/1.47      | ~ r1_tarski(k1_relat_1(X0),X1)
% 8.11/1.47      | ~ v1_relat_1(X0) ),
% 8.11/1.47      inference(cnf_transformation,[],[f91]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_1939,plain,
% 8.11/1.47      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 8.11/1.47      | r1_tarski(k2_relat_1(X0),X2) != iProver_top
% 8.11/1.47      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 8.11/1.47      | v1_relat_1(X0) != iProver_top ),
% 8.11/1.47      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_4,plain,
% 8.11/1.47      ( r1_tarski(k1_xboole_0,X0) ),
% 8.11/1.47      inference(cnf_transformation,[],[f69]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_1953,plain,
% 8.11/1.47      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 8.11/1.47      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_28,plain,
% 8.11/1.47      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 8.11/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 8.11/1.47      | k1_xboole_0 = X1
% 8.11/1.47      | k1_xboole_0 = X0 ),
% 8.11/1.47      inference(cnf_transformation,[],[f116]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_33,plain,
% 8.11/1.47      ( v1_funct_2(sK0(X0,X1),X0,X1) ),
% 8.11/1.47      inference(cnf_transformation,[],[f102]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_725,plain,
% 8.11/1.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 8.11/1.47      | X2 != X1
% 8.11/1.47      | sK0(X2,X3) != X0
% 8.11/1.47      | k1_xboole_0 != X3
% 8.11/1.47      | k1_xboole_0 = X0
% 8.11/1.47      | k1_xboole_0 = X1 ),
% 8.11/1.47      inference(resolution_lifted,[status(thm)],[c_28,c_33]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_726,plain,
% 8.11/1.47      ( ~ m1_subset_1(sK0(X0,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 8.11/1.47      | k1_xboole_0 = X0
% 8.11/1.47      | k1_xboole_0 = sK0(X0,k1_xboole_0) ),
% 8.11/1.47      inference(unflattening,[status(thm)],[c_725]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_37,plain,
% 8.11/1.47      ( m1_subset_1(sK0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 8.11/1.47      inference(cnf_transformation,[],[f98]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_736,plain,
% 8.11/1.47      ( k1_xboole_0 = X0 | k1_xboole_0 = sK0(X0,k1_xboole_0) ),
% 8.11/1.47      inference(forward_subsumption_resolution,
% 8.11/1.47                [status(thm)],
% 8.11/1.47                [c_726,c_37]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_36,plain,
% 8.11/1.47      ( v1_relat_1(sK0(X0,X1)) ),
% 8.11/1.47      inference(cnf_transformation,[],[f99]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_1937,plain,
% 8.11/1.47      ( v1_relat_1(sK0(X0,X1)) = iProver_top ),
% 8.11/1.47      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_3068,plain,
% 8.11/1.47      ( k1_xboole_0 = X0 | v1_relat_1(k1_xboole_0) = iProver_top ),
% 8.11/1.47      inference(superposition,[status(thm)],[c_736,c_1937]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_11,plain,
% 8.11/1.47      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 8.11/1.47      inference(cnf_transformation,[],[f76]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_137,plain,
% 8.11/1.47      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 8.11/1.47      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_7,plain,
% 8.11/1.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 8.11/1.47      | ~ v1_relat_1(X1)
% 8.11/1.47      | v1_relat_1(X0) ),
% 8.11/1.47      inference(cnf_transformation,[],[f72]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_5,plain,
% 8.11/1.47      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 8.11/1.47      inference(cnf_transformation,[],[f71]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_359,plain,
% 8.11/1.47      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 8.11/1.47      inference(prop_impl,[status(thm)],[c_5]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_360,plain,
% 8.11/1.47      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 8.11/1.47      inference(renaming,[status(thm)],[c_359]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_431,plain,
% 8.11/1.47      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 8.11/1.47      inference(bin_hyper_res,[status(thm)],[c_7,c_360]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_2193,plain,
% 8.11/1.47      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
% 8.11/1.47      | v1_relat_1(X0)
% 8.11/1.47      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 8.11/1.47      inference(instantiation,[status(thm)],[c_431]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_2588,plain,
% 8.11/1.47      ( ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,X1))
% 8.11/1.47      | ~ v1_relat_1(k2_zfmisc_1(X0,X1))
% 8.11/1.47      | v1_relat_1(k1_xboole_0) ),
% 8.11/1.47      inference(instantiation,[status(thm)],[c_2193]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_2589,plain,
% 8.11/1.47      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,X1)) != iProver_top
% 8.11/1.47      | v1_relat_1(k2_zfmisc_1(X0,X1)) != iProver_top
% 8.11/1.47      | v1_relat_1(k1_xboole_0) = iProver_top ),
% 8.11/1.47      inference(predicate_to_equality,[status(thm)],[c_2588]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_3181,plain,
% 8.11/1.47      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,X1)) ),
% 8.11/1.47      inference(instantiation,[status(thm)],[c_4]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_3182,plain,
% 8.11/1.47      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,X1)) = iProver_top ),
% 8.11/1.47      inference(predicate_to_equality,[status(thm)],[c_3181]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_6258,plain,
% 8.11/1.47      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 8.11/1.47      inference(global_propositional_subsumption,
% 8.11/1.47                [status(thm)],
% 8.11/1.47                [c_3068,c_137,c_2589,c_3182]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_14,plain,
% 8.11/1.47      ( ~ v1_relat_1(X0) | k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) ),
% 8.11/1.47      inference(cnf_transformation,[],[f80]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_1946,plain,
% 8.11/1.47      ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
% 8.11/1.47      | v1_relat_1(X0) != iProver_top ),
% 8.11/1.47      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_6265,plain,
% 8.11/1.47      ( k2_relat_1(k4_relat_1(k1_xboole_0)) = k1_relat_1(k1_xboole_0) ),
% 8.11/1.47      inference(superposition,[status(thm)],[c_6258,c_1946]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_24,plain,
% 8.11/1.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 8.11/1.47      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 8.11/1.47      inference(cnf_transformation,[],[f89]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_1941,plain,
% 8.11/1.47      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 8.11/1.47      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 8.11/1.47      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_6196,plain,
% 8.11/1.47      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 8.11/1.47      | r1_tarski(k2_relat_1(X2),X1) != iProver_top
% 8.11/1.47      | r1_tarski(k1_relat_1(X2),X0) != iProver_top
% 8.11/1.47      | v1_relat_1(X2) != iProver_top ),
% 8.11/1.47      inference(superposition,[status(thm)],[c_1939,c_1941]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_37723,plain,
% 8.11/1.47      ( k1_relset_1(X0,X1,k4_relat_1(k1_xboole_0)) = k1_relat_1(k4_relat_1(k1_xboole_0))
% 8.11/1.47      | r1_tarski(k1_relat_1(k4_relat_1(k1_xboole_0)),X0) != iProver_top
% 8.11/1.47      | r1_tarski(k1_relat_1(k1_xboole_0),X1) != iProver_top
% 8.11/1.47      | v1_relat_1(k4_relat_1(k1_xboole_0)) != iProver_top ),
% 8.11/1.47      inference(superposition,[status(thm)],[c_6265,c_6196]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_1952,plain,
% 8.11/1.47      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 8.11/1.47      | r1_tarski(X0,X1) != iProver_top ),
% 8.11/1.47      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_4347,plain,
% 8.11/1.47      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 8.11/1.47      | r1_tarski(X2,k2_zfmisc_1(X0,X1)) != iProver_top ),
% 8.11/1.47      inference(superposition,[status(thm)],[c_1952,c_1941]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_12337,plain,
% 8.11/1.47      ( k1_relset_1(X0,X1,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
% 8.11/1.47      inference(superposition,[status(thm)],[c_1953,c_4347]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_23,plain,
% 8.11/1.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 8.11/1.47      | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
% 8.11/1.47      inference(cnf_transformation,[],[f88]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_1942,plain,
% 8.11/1.47      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 8.11/1.47      | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 8.11/1.47      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_12375,plain,
% 8.11/1.47      ( m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(X0)) = iProver_top
% 8.11/1.47      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 8.11/1.47      inference(superposition,[status(thm)],[c_12337,c_1942]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_14033,plain,
% 8.11/1.47      ( m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(X0)) = iProver_top
% 8.11/1.47      | r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,X1)) != iProver_top ),
% 8.11/1.47      inference(superposition,[status(thm)],[c_1952,c_12375]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_14043,plain,
% 8.11/1.47      ( m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(X0)) = iProver_top ),
% 8.11/1.47      inference(global_propositional_subsumption,
% 8.11/1.47                [status(thm)],
% 8.11/1.47                [c_14033,c_3182]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_6,plain,
% 8.11/1.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 8.11/1.47      inference(cnf_transformation,[],[f70]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_1951,plain,
% 8.11/1.47      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 8.11/1.47      | r1_tarski(X0,X1) = iProver_top ),
% 8.11/1.47      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_14049,plain,
% 8.11/1.47      ( r1_tarski(k1_relat_1(k1_xboole_0),X0) = iProver_top ),
% 8.11/1.47      inference(superposition,[status(thm)],[c_14043,c_1951]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_0,plain,
% 8.11/1.47      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 8.11/1.47      inference(cnf_transformation,[],[f67]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_1956,plain,
% 8.11/1.47      ( X0 = X1
% 8.11/1.47      | r1_tarski(X0,X1) != iProver_top
% 8.11/1.47      | r1_tarski(X1,X0) != iProver_top ),
% 8.11/1.47      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_5207,plain,
% 8.11/1.47      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 8.11/1.47      inference(superposition,[status(thm)],[c_1953,c_1956]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_15079,plain,
% 8.11/1.47      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 8.11/1.47      inference(superposition,[status(thm)],[c_14049,c_5207]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_44,negated_conjecture,
% 8.11/1.47      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 8.11/1.47      inference(cnf_transformation,[],[f108]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_1934,plain,
% 8.11/1.47      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 8.11/1.47      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_3837,plain,
% 8.11/1.47      ( r1_tarski(sK3,k2_zfmisc_1(sK1,sK2)) = iProver_top ),
% 8.11/1.47      inference(superposition,[status(thm)],[c_1934,c_1951]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_1932,plain,
% 8.11/1.47      ( r1_tarski(X0,X1) != iProver_top
% 8.11/1.47      | v1_relat_1(X1) != iProver_top
% 8.11/1.47      | v1_relat_1(X0) = iProver_top ),
% 8.11/1.47      inference(predicate_to_equality,[status(thm)],[c_431]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_13883,plain,
% 8.11/1.47      ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) != iProver_top
% 8.11/1.47      | v1_relat_1(sK3) = iProver_top ),
% 8.11/1.47      inference(superposition,[status(thm)],[c_3837,c_1932]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_49,plain,
% 8.11/1.47      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 8.11/1.47      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_2248,plain,
% 8.11/1.47      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 8.11/1.47      | r1_tarski(sK3,k2_zfmisc_1(X0,X1)) ),
% 8.11/1.47      inference(instantiation,[status(thm)],[c_6]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_2478,plain,
% 8.11/1.47      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 8.11/1.47      | r1_tarski(sK3,k2_zfmisc_1(sK1,sK2)) ),
% 8.11/1.47      inference(instantiation,[status(thm)],[c_2248]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_2479,plain,
% 8.11/1.47      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 8.11/1.47      | r1_tarski(sK3,k2_zfmisc_1(sK1,sK2)) = iProver_top ),
% 8.11/1.47      inference(predicate_to_equality,[status(thm)],[c_2478]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_2621,plain,
% 8.11/1.47      ( ~ r1_tarski(sK3,k2_zfmisc_1(sK1,sK2))
% 8.11/1.47      | ~ v1_relat_1(k2_zfmisc_1(sK1,sK2))
% 8.11/1.47      | v1_relat_1(sK3) ),
% 8.11/1.47      inference(instantiation,[status(thm)],[c_2193]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_2622,plain,
% 8.11/1.47      ( r1_tarski(sK3,k2_zfmisc_1(sK1,sK2)) != iProver_top
% 8.11/1.47      | v1_relat_1(k2_zfmisc_1(sK1,sK2)) != iProver_top
% 8.11/1.47      | v1_relat_1(sK3) = iProver_top ),
% 8.11/1.47      inference(predicate_to_equality,[status(thm)],[c_2621]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_2711,plain,
% 8.11/1.47      ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) ),
% 8.11/1.47      inference(instantiation,[status(thm)],[c_11]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_2712,plain,
% 8.11/1.47      ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) = iProver_top ),
% 8.11/1.47      inference(predicate_to_equality,[status(thm)],[c_2711]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_14288,plain,
% 8.11/1.47      ( v1_relat_1(sK3) = iProver_top ),
% 8.11/1.47      inference(global_propositional_subsumption,
% 8.11/1.47                [status(thm)],
% 8.11/1.47                [c_13883,c_49,c_2479,c_2622,c_2712]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_16,plain,
% 8.11/1.47      ( ~ v1_funct_1(X0)
% 8.11/1.47      | ~ v2_funct_1(X0)
% 8.11/1.47      | ~ v1_relat_1(X0)
% 8.11/1.47      | k2_funct_1(X0) = k4_relat_1(X0) ),
% 8.11/1.47      inference(cnf_transformation,[],[f81]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_43,negated_conjecture,
% 8.11/1.47      ( v2_funct_1(sK3) ),
% 8.11/1.47      inference(cnf_transformation,[],[f109]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_665,plain,
% 8.11/1.47      ( ~ v1_funct_1(X0)
% 8.11/1.47      | ~ v1_relat_1(X0)
% 8.11/1.47      | k2_funct_1(X0) = k4_relat_1(X0)
% 8.11/1.47      | sK3 != X0 ),
% 8.11/1.47      inference(resolution_lifted,[status(thm)],[c_16,c_43]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_666,plain,
% 8.11/1.47      ( ~ v1_funct_1(sK3)
% 8.11/1.47      | ~ v1_relat_1(sK3)
% 8.11/1.47      | k2_funct_1(sK3) = k4_relat_1(sK3) ),
% 8.11/1.47      inference(unflattening,[status(thm)],[c_665]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_46,negated_conjecture,
% 8.11/1.47      ( v1_funct_1(sK3) ),
% 8.11/1.47      inference(cnf_transformation,[],[f106]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_668,plain,
% 8.11/1.47      ( ~ v1_relat_1(sK3) | k2_funct_1(sK3) = k4_relat_1(sK3) ),
% 8.11/1.47      inference(global_propositional_subsumption,
% 8.11/1.47                [status(thm)],
% 8.11/1.47                [c_666,c_46]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_1926,plain,
% 8.11/1.47      ( k2_funct_1(sK3) = k4_relat_1(sK3)
% 8.11/1.47      | v1_relat_1(sK3) != iProver_top ),
% 8.11/1.47      inference(predicate_to_equality,[status(thm)],[c_668]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_14304,plain,
% 8.11/1.47      ( k2_funct_1(sK3) = k4_relat_1(sK3) ),
% 8.11/1.47      inference(superposition,[status(thm)],[c_14288,c_1926]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_27,plain,
% 8.11/1.47      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
% 8.11/1.47      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 8.11/1.47      | k1_xboole_0 = X0 ),
% 8.11/1.47      inference(cnf_transformation,[],[f115]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_41,negated_conjecture,
% 8.11/1.47      ( ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
% 8.11/1.47      | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 8.11/1.47      | ~ v1_funct_1(k2_funct_1(sK3)) ),
% 8.11/1.47      inference(cnf_transformation,[],[f111]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_699,plain,
% 8.11/1.47      ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 8.11/1.47      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 8.11/1.47      | ~ v1_funct_1(k2_funct_1(sK3))
% 8.11/1.47      | k2_funct_1(sK3) != k1_xboole_0
% 8.11/1.47      | sK1 != k1_xboole_0
% 8.11/1.47      | sK2 != X0
% 8.11/1.47      | k1_xboole_0 = X0 ),
% 8.11/1.47      inference(resolution_lifted,[status(thm)],[c_27,c_41]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_700,plain,
% 8.11/1.47      ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 8.11/1.47      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))
% 8.11/1.47      | ~ v1_funct_1(k2_funct_1(sK3))
% 8.11/1.47      | k2_funct_1(sK3) != k1_xboole_0
% 8.11/1.47      | sK1 != k1_xboole_0
% 8.11/1.47      | k1_xboole_0 = sK2 ),
% 8.11/1.47      inference(unflattening,[status(thm)],[c_699]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_1925,plain,
% 8.11/1.47      ( k2_funct_1(sK3) != k1_xboole_0
% 8.11/1.47      | sK1 != k1_xboole_0
% 8.11/1.47      | k1_xboole_0 = sK2
% 8.11/1.47      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 8.11/1.47      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top
% 8.11/1.47      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 8.11/1.47      inference(predicate_to_equality,[status(thm)],[c_700]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_47,plain,
% 8.11/1.47      ( v1_funct_1(sK3) = iProver_top ),
% 8.11/1.47      inference(predicate_to_equality,[status(thm)],[c_46]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_701,plain,
% 8.11/1.47      ( k2_funct_1(sK3) != k1_xboole_0
% 8.11/1.47      | sK1 != k1_xboole_0
% 8.11/1.47      | k1_xboole_0 = sK2
% 8.11/1.47      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 8.11/1.47      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top
% 8.11/1.47      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 8.11/1.47      inference(predicate_to_equality,[status(thm)],[c_700]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_17,plain,
% 8.11/1.47      ( ~ v1_funct_1(X0)
% 8.11/1.47      | v1_funct_1(k2_funct_1(X0))
% 8.11/1.47      | ~ v1_relat_1(X0) ),
% 8.11/1.47      inference(cnf_transformation,[],[f83]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_2031,plain,
% 8.11/1.47      ( v1_funct_1(k2_funct_1(sK3))
% 8.11/1.47      | ~ v1_funct_1(sK3)
% 8.11/1.47      | ~ v1_relat_1(sK3) ),
% 8.11/1.47      inference(instantiation,[status(thm)],[c_17]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_2032,plain,
% 8.11/1.47      ( v1_funct_1(k2_funct_1(sK3)) = iProver_top
% 8.11/1.47      | v1_funct_1(sK3) != iProver_top
% 8.11/1.47      | v1_relat_1(sK3) != iProver_top ),
% 8.11/1.47      inference(predicate_to_equality,[status(thm)],[c_2031]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_2837,plain,
% 8.11/1.47      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top
% 8.11/1.47      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 8.11/1.47      | k1_xboole_0 = sK2
% 8.11/1.47      | sK1 != k1_xboole_0
% 8.11/1.47      | k2_funct_1(sK3) != k1_xboole_0 ),
% 8.11/1.47      inference(global_propositional_subsumption,
% 8.11/1.47                [status(thm)],
% 8.11/1.47                [c_1925,c_47,c_49,c_701,c_2032,c_2479,c_2622,c_2712]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_2838,plain,
% 8.11/1.47      ( k2_funct_1(sK3) != k1_xboole_0
% 8.11/1.47      | sK1 != k1_xboole_0
% 8.11/1.47      | k1_xboole_0 = sK2
% 8.11/1.47      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 8.11/1.47      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
% 8.11/1.47      inference(renaming,[status(thm)],[c_2837]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_14579,plain,
% 8.11/1.47      ( k4_relat_1(sK3) != k1_xboole_0
% 8.11/1.47      | sK1 != k1_xboole_0
% 8.11/1.47      | sK2 = k1_xboole_0
% 8.11/1.47      | m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 8.11/1.47      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
% 8.11/1.47      inference(demodulation,[status(thm)],[c_14304,c_2838]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_32,plain,
% 8.11/1.47      ( ~ v1_funct_2(X0,X1,X2)
% 8.11/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 8.11/1.47      | k1_relset_1(X1,X2,X0) = X1
% 8.11/1.47      | k1_xboole_0 = X2 ),
% 8.11/1.47      inference(cnf_transformation,[],[f92]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_45,negated_conjecture,
% 8.11/1.47      ( v1_funct_2(sK3,sK1,sK2) ),
% 8.11/1.47      inference(cnf_transformation,[],[f107]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_900,plain,
% 8.11/1.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 8.11/1.47      | k1_relset_1(X1,X2,X0) = X1
% 8.11/1.47      | sK1 != X1
% 8.11/1.47      | sK2 != X2
% 8.11/1.47      | sK3 != X0
% 8.11/1.47      | k1_xboole_0 = X2 ),
% 8.11/1.47      inference(resolution_lifted,[status(thm)],[c_32,c_45]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_901,plain,
% 8.11/1.47      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 8.11/1.47      | k1_relset_1(sK1,sK2,sK3) = sK1
% 8.11/1.47      | k1_xboole_0 = sK2 ),
% 8.11/1.47      inference(unflattening,[status(thm)],[c_900]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_903,plain,
% 8.11/1.47      ( k1_relset_1(sK1,sK2,sK3) = sK1 | k1_xboole_0 = sK2 ),
% 8.11/1.47      inference(global_propositional_subsumption,
% 8.11/1.47                [status(thm)],
% 8.11/1.47                [c_901,c_44]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_4349,plain,
% 8.11/1.47      ( k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
% 8.11/1.47      inference(superposition,[status(thm)],[c_1934,c_1941]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_4475,plain,
% 8.11/1.47      ( k1_relat_1(sK3) = sK1 | sK2 = k1_xboole_0 ),
% 8.11/1.47      inference(superposition,[status(thm)],[c_903,c_4349]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_25,plain,
% 8.11/1.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 8.11/1.47      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 8.11/1.47      inference(cnf_transformation,[],[f90]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_1940,plain,
% 8.11/1.47      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 8.11/1.47      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 8.11/1.47      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_4201,plain,
% 8.11/1.47      ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
% 8.11/1.47      inference(superposition,[status(thm)],[c_1934,c_1940]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_42,negated_conjecture,
% 8.11/1.47      ( k2_relset_1(sK1,sK2,sK3) = sK2 ),
% 8.11/1.47      inference(cnf_transformation,[],[f110]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_4202,plain,
% 8.11/1.47      ( k2_relat_1(sK3) = sK2 ),
% 8.11/1.47      inference(light_normalisation,[status(thm)],[c_4201,c_42]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_21,plain,
% 8.11/1.47      ( ~ v1_funct_1(X0)
% 8.11/1.47      | ~ v2_funct_1(X0)
% 8.11/1.47      | ~ v1_relat_1(X0)
% 8.11/1.47      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 8.11/1.47      inference(cnf_transformation,[],[f85]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_619,plain,
% 8.11/1.47      ( ~ v1_funct_1(X0)
% 8.11/1.47      | ~ v1_relat_1(X0)
% 8.11/1.47      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 8.11/1.47      | sK3 != X0 ),
% 8.11/1.47      inference(resolution_lifted,[status(thm)],[c_21,c_43]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_620,plain,
% 8.11/1.47      ( ~ v1_funct_1(sK3)
% 8.11/1.47      | ~ v1_relat_1(sK3)
% 8.11/1.47      | k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
% 8.11/1.47      inference(unflattening,[status(thm)],[c_619]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_622,plain,
% 8.11/1.47      ( ~ v1_relat_1(sK3)
% 8.11/1.47      | k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
% 8.11/1.47      inference(global_propositional_subsumption,
% 8.11/1.47                [status(thm)],
% 8.11/1.47                [c_620,c_46]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_1929,plain,
% 8.11/1.47      ( k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3)
% 8.11/1.47      | v1_relat_1(sK3) != iProver_top ),
% 8.11/1.47      inference(predicate_to_equality,[status(thm)],[c_622]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_4342,plain,
% 8.11/1.47      ( k1_relat_1(k2_funct_1(sK3)) = sK2
% 8.11/1.47      | v1_relat_1(sK3) != iProver_top ),
% 8.11/1.47      inference(demodulation,[status(thm)],[c_4202,c_1929]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_4589,plain,
% 8.11/1.47      ( k1_relat_1(k2_funct_1(sK3)) = sK2 ),
% 8.11/1.47      inference(global_propositional_subsumption,
% 8.11/1.47                [status(thm)],
% 8.11/1.47                [c_4342,c_49,c_2479,c_2622,c_2712]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_39,plain,
% 8.11/1.47      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
% 8.11/1.47      | ~ v1_funct_1(X0)
% 8.11/1.47      | ~ v1_relat_1(X0) ),
% 8.11/1.47      inference(cnf_transformation,[],[f104]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_924,plain,
% 8.11/1.47      ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 8.11/1.47      | ~ v1_funct_1(X0)
% 8.11/1.47      | ~ v1_funct_1(k2_funct_1(sK3))
% 8.11/1.47      | ~ v1_relat_1(X0)
% 8.11/1.47      | k2_funct_1(sK3) != X0
% 8.11/1.47      | k2_relat_1(X0) != sK1
% 8.11/1.47      | k1_relat_1(X0) != sK2 ),
% 8.11/1.47      inference(resolution_lifted,[status(thm)],[c_39,c_41]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_925,plain,
% 8.11/1.47      ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 8.11/1.47      | ~ v1_funct_1(k2_funct_1(sK3))
% 8.11/1.47      | ~ v1_relat_1(k2_funct_1(sK3))
% 8.11/1.47      | k2_relat_1(k2_funct_1(sK3)) != sK1
% 8.11/1.47      | k1_relat_1(k2_funct_1(sK3)) != sK2 ),
% 8.11/1.47      inference(unflattening,[status(thm)],[c_924]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_1916,plain,
% 8.11/1.47      ( k2_relat_1(k2_funct_1(sK3)) != sK1
% 8.11/1.47      | k1_relat_1(k2_funct_1(sK3)) != sK2
% 8.11/1.47      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 8.11/1.47      | v1_funct_1(k2_funct_1(sK3)) != iProver_top
% 8.11/1.47      | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
% 8.11/1.47      inference(predicate_to_equality,[status(thm)],[c_925]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_926,plain,
% 8.11/1.47      ( k2_relat_1(k2_funct_1(sK3)) != sK1
% 8.11/1.47      | k1_relat_1(k2_funct_1(sK3)) != sK2
% 8.11/1.47      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 8.11/1.47      | v1_funct_1(k2_funct_1(sK3)) != iProver_top
% 8.11/1.47      | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
% 8.11/1.47      inference(predicate_to_equality,[status(thm)],[c_925]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_18,plain,
% 8.11/1.47      ( ~ v1_funct_1(X0)
% 8.11/1.47      | ~ v1_relat_1(X0)
% 8.11/1.47      | v1_relat_1(k2_funct_1(X0)) ),
% 8.11/1.47      inference(cnf_transformation,[],[f82]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_2428,plain,
% 8.11/1.47      ( ~ v1_funct_1(sK3)
% 8.11/1.47      | v1_relat_1(k2_funct_1(sK3))
% 8.11/1.47      | ~ v1_relat_1(sK3) ),
% 8.11/1.47      inference(instantiation,[status(thm)],[c_18]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_2429,plain,
% 8.11/1.47      ( v1_funct_1(sK3) != iProver_top
% 8.11/1.47      | v1_relat_1(k2_funct_1(sK3)) = iProver_top
% 8.11/1.47      | v1_relat_1(sK3) != iProver_top ),
% 8.11/1.47      inference(predicate_to_equality,[status(thm)],[c_2428]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_2756,plain,
% 8.11/1.47      ( k2_relat_1(k2_funct_1(sK3)) != sK1
% 8.11/1.47      | k1_relat_1(k2_funct_1(sK3)) != sK2
% 8.11/1.47      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 8.11/1.47      inference(global_propositional_subsumption,
% 8.11/1.47                [status(thm)],
% 8.11/1.47                [c_1916,c_47,c_49,c_926,c_2032,c_2429,c_2479,c_2622,
% 8.11/1.47                 c_2712]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_4591,plain,
% 8.11/1.47      ( k2_relat_1(k2_funct_1(sK3)) != sK1
% 8.11/1.47      | sK2 != sK2
% 8.11/1.47      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 8.11/1.47      inference(demodulation,[status(thm)],[c_4589,c_2756]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_4869,plain,
% 8.11/1.47      ( k2_relat_1(k2_funct_1(sK3)) != sK1
% 8.11/1.47      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 8.11/1.47      inference(equality_resolution_simp,[status(thm)],[c_4591]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_14577,plain,
% 8.11/1.47      ( k2_relat_1(k4_relat_1(sK3)) != sK1
% 8.11/1.47      | m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 8.11/1.47      inference(demodulation,[status(thm)],[c_14304,c_4869]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_20,plain,
% 8.11/1.47      ( ~ v1_funct_1(X0)
% 8.11/1.47      | ~ v2_funct_1(X0)
% 8.11/1.47      | ~ v1_relat_1(X0)
% 8.11/1.47      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 8.11/1.47      inference(cnf_transformation,[],[f86]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_633,plain,
% 8.11/1.47      ( ~ v1_funct_1(X0)
% 8.11/1.47      | ~ v1_relat_1(X0)
% 8.11/1.47      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 8.11/1.47      | sK3 != X0 ),
% 8.11/1.47      inference(resolution_lifted,[status(thm)],[c_20,c_43]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_634,plain,
% 8.11/1.47      ( ~ v1_funct_1(sK3)
% 8.11/1.47      | ~ v1_relat_1(sK3)
% 8.11/1.47      | k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
% 8.11/1.47      inference(unflattening,[status(thm)],[c_633]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_636,plain,
% 8.11/1.47      ( ~ v1_relat_1(sK3)
% 8.11/1.47      | k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
% 8.11/1.47      inference(global_propositional_subsumption,
% 8.11/1.47                [status(thm)],
% 8.11/1.47                [c_634,c_46]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_1928,plain,
% 8.11/1.47      ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3)
% 8.11/1.47      | v1_relat_1(sK3) != iProver_top ),
% 8.11/1.47      inference(predicate_to_equality,[status(thm)],[c_636]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_14303,plain,
% 8.11/1.47      ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
% 8.11/1.47      inference(superposition,[status(thm)],[c_14288,c_1928]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_14305,plain,
% 8.11/1.47      ( k2_relat_1(k4_relat_1(sK3)) = k1_relat_1(sK3) ),
% 8.11/1.47      inference(demodulation,[status(thm)],[c_14303,c_14304]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_14586,plain,
% 8.11/1.47      ( k1_relat_1(sK3) != sK1
% 8.11/1.47      | m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 8.11/1.47      inference(light_normalisation,[status(thm)],[c_14577,c_14305]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_15553,plain,
% 8.11/1.47      ( m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 8.11/1.47      | sK2 = k1_xboole_0 ),
% 8.11/1.47      inference(global_propositional_subsumption,
% 8.11/1.47                [status(thm)],
% 8.11/1.47                [c_14579,c_4475,c_14586]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_15554,plain,
% 8.11/1.47      ( sK2 = k1_xboole_0
% 8.11/1.47      | m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 8.11/1.47      inference(renaming,[status(thm)],[c_15553]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_15558,plain,
% 8.11/1.47      ( sK2 = k1_xboole_0
% 8.11/1.47      | r1_tarski(k2_relat_1(k4_relat_1(sK3)),sK1) != iProver_top
% 8.11/1.47      | r1_tarski(k1_relat_1(k4_relat_1(sK3)),sK2) != iProver_top
% 8.11/1.47      | v1_relat_1(k4_relat_1(sK3)) != iProver_top ),
% 8.11/1.47      inference(superposition,[status(thm)],[c_1939,c_15554]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_15,plain,
% 8.11/1.47      ( ~ v1_relat_1(X0) | k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0) ),
% 8.11/1.47      inference(cnf_transformation,[],[f79]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_1945,plain,
% 8.11/1.47      ( k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0)
% 8.11/1.47      | v1_relat_1(X0) != iProver_top ),
% 8.11/1.47      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_14301,plain,
% 8.11/1.47      ( k1_relat_1(k4_relat_1(sK3)) = k2_relat_1(sK3) ),
% 8.11/1.47      inference(superposition,[status(thm)],[c_14288,c_1945]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_14307,plain,
% 8.11/1.47      ( k1_relat_1(k4_relat_1(sK3)) = sK2 ),
% 8.11/1.47      inference(light_normalisation,[status(thm)],[c_14301,c_4202]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_15559,plain,
% 8.11/1.47      ( sK2 = k1_xboole_0
% 8.11/1.47      | r1_tarski(k1_relat_1(sK3),sK1) != iProver_top
% 8.11/1.47      | r1_tarski(sK2,sK2) != iProver_top
% 8.11/1.47      | v1_relat_1(k4_relat_1(sK3)) != iProver_top ),
% 8.11/1.47      inference(light_normalisation,
% 8.11/1.47                [status(thm)],
% 8.11/1.47                [c_15558,c_14305,c_14307]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_1,plain,
% 8.11/1.47      ( r1_tarski(X0,X0) ),
% 8.11/1.47      inference(cnf_transformation,[],[f112]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_4012,plain,
% 8.11/1.47      ( r1_tarski(sK2,sK2) ),
% 8.11/1.47      inference(instantiation,[status(thm)],[c_1]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_4013,plain,
% 8.11/1.47      ( r1_tarski(sK2,sK2) = iProver_top ),
% 8.11/1.47      inference(predicate_to_equality,[status(thm)],[c_4012]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_22,plain,
% 8.11/1.47      ( v4_relat_1(X0,X1)
% 8.11/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 8.11/1.47      inference(cnf_transformation,[],[f87]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_9,plain,
% 8.11/1.47      ( ~ v4_relat_1(X0,X1)
% 8.11/1.47      | r1_tarski(k1_relat_1(X0),X1)
% 8.11/1.47      | ~ v1_relat_1(X0) ),
% 8.11/1.47      inference(cnf_transformation,[],[f73]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_583,plain,
% 8.11/1.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 8.11/1.47      | r1_tarski(k1_relat_1(X0),X1)
% 8.11/1.47      | ~ v1_relat_1(X0) ),
% 8.11/1.47      inference(resolution,[status(thm)],[c_22,c_9]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_2905,plain,
% 8.11/1.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
% 8.11/1.47      | r1_tarski(k1_relat_1(X0),sK1)
% 8.11/1.47      | ~ v1_relat_1(X0) ),
% 8.11/1.47      inference(instantiation,[status(thm)],[c_583]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_4772,plain,
% 8.11/1.47      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 8.11/1.47      | r1_tarski(k1_relat_1(sK3),sK1)
% 8.11/1.47      | ~ v1_relat_1(sK3) ),
% 8.11/1.47      inference(instantiation,[status(thm)],[c_2905]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_4773,plain,
% 8.11/1.47      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 8.11/1.47      | r1_tarski(k1_relat_1(sK3),sK1) = iProver_top
% 8.11/1.47      | v1_relat_1(sK3) != iProver_top ),
% 8.11/1.47      inference(predicate_to_equality,[status(thm)],[c_4772]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_10,plain,
% 8.11/1.47      ( ~ v1_relat_1(X0) | v1_relat_1(k4_relat_1(X0)) ),
% 8.11/1.47      inference(cnf_transformation,[],[f75]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_12666,plain,
% 8.11/1.47      ( v1_relat_1(k4_relat_1(sK3)) | ~ v1_relat_1(sK3) ),
% 8.11/1.47      inference(instantiation,[status(thm)],[c_10]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_12667,plain,
% 8.11/1.47      ( v1_relat_1(k4_relat_1(sK3)) = iProver_top
% 8.11/1.47      | v1_relat_1(sK3) != iProver_top ),
% 8.11/1.47      inference(predicate_to_equality,[status(thm)],[c_12666]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_15614,plain,
% 8.11/1.47      ( sK2 = k1_xboole_0 ),
% 8.11/1.47      inference(global_propositional_subsumption,
% 8.11/1.47                [status(thm)],
% 8.11/1.47                [c_15559,c_49,c_2479,c_2622,c_2712,c_4013,c_4773,c_12667]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_764,plain,
% 8.11/1.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 8.11/1.47      | sK1 != X1
% 8.11/1.47      | sK2 != k1_xboole_0
% 8.11/1.47      | sK3 != X0
% 8.11/1.47      | k1_xboole_0 = X0
% 8.11/1.47      | k1_xboole_0 = X1 ),
% 8.11/1.47      inference(resolution_lifted,[status(thm)],[c_28,c_45]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_765,plain,
% 8.11/1.47      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
% 8.11/1.47      | sK2 != k1_xboole_0
% 8.11/1.47      | k1_xboole_0 = sK1
% 8.11/1.47      | k1_xboole_0 = sK3 ),
% 8.11/1.47      inference(unflattening,[status(thm)],[c_764]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_1923,plain,
% 8.11/1.47      ( sK2 != k1_xboole_0
% 8.11/1.47      | k1_xboole_0 = sK1
% 8.11/1.47      | k1_xboole_0 = sK3
% 8.11/1.47      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) != iProver_top ),
% 8.11/1.47      inference(predicate_to_equality,[status(thm)],[c_765]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_15659,plain,
% 8.11/1.47      ( sK1 = k1_xboole_0
% 8.11/1.47      | sK3 = k1_xboole_0
% 8.11/1.47      | k1_xboole_0 != k1_xboole_0
% 8.11/1.47      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) != iProver_top ),
% 8.11/1.47      inference(demodulation,[status(thm)],[c_15614,c_1923]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_15664,plain,
% 8.11/1.47      ( sK1 = k1_xboole_0
% 8.11/1.47      | sK3 = k1_xboole_0
% 8.11/1.47      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) != iProver_top ),
% 8.11/1.47      inference(equality_resolution_simp,[status(thm)],[c_15659]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_2481,plain,
% 8.11/1.47      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 8.11/1.47      | ~ r1_tarski(sK3,k2_zfmisc_1(X0,X1)) ),
% 8.11/1.47      inference(instantiation,[status(thm)],[c_5]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_8463,plain,
% 8.11/1.47      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
% 8.11/1.47      | ~ r1_tarski(sK3,k2_zfmisc_1(sK1,X0)) ),
% 8.11/1.47      inference(instantiation,[status(thm)],[c_2481]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_8465,plain,
% 8.11/1.47      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) = iProver_top
% 8.11/1.47      | r1_tarski(sK3,k2_zfmisc_1(sK1,X0)) != iProver_top ),
% 8.11/1.47      inference(predicate_to_equality,[status(thm)],[c_8463]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_8467,plain,
% 8.11/1.47      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) = iProver_top
% 8.11/1.47      | r1_tarski(sK3,k2_zfmisc_1(sK1,k1_xboole_0)) != iProver_top ),
% 8.11/1.47      inference(instantiation,[status(thm)],[c_8465]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_15658,plain,
% 8.11/1.47      ( r1_tarski(sK3,k2_zfmisc_1(sK1,k1_xboole_0)) = iProver_top ),
% 8.11/1.47      inference(demodulation,[status(thm)],[c_15614,c_3837]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_25921,plain,
% 8.11/1.47      ( sK3 = k1_xboole_0 | sK1 = k1_xboole_0 ),
% 8.11/1.47      inference(global_propositional_subsumption,
% 8.11/1.47                [status(thm)],
% 8.11/1.47                [c_15664,c_8467,c_15658]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_25922,plain,
% 8.11/1.47      ( sK1 = k1_xboole_0 | sK3 = k1_xboole_0 ),
% 8.11/1.47      inference(renaming,[status(thm)],[c_25921]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_15663,plain,
% 8.11/1.47      ( k2_relset_1(sK1,k1_xboole_0,sK3) = k1_xboole_0 ),
% 8.11/1.47      inference(demodulation,[status(thm)],[c_15614,c_42]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_25962,plain,
% 8.11/1.47      ( k2_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0
% 8.11/1.47      | sK3 = k1_xboole_0 ),
% 8.11/1.47      inference(superposition,[status(thm)],[c_25922,c_15663]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_740,plain,
% 8.11/1.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 8.11/1.47      | ~ v1_funct_1(X2)
% 8.11/1.47      | ~ v1_relat_1(X2)
% 8.11/1.47      | X2 != X0
% 8.11/1.47      | k2_relat_1(X2) != k1_xboole_0
% 8.11/1.47      | k1_relat_1(X2) != X1
% 8.11/1.47      | k1_xboole_0 = X0
% 8.11/1.47      | k1_xboole_0 = X1 ),
% 8.11/1.47      inference(resolution_lifted,[status(thm)],[c_28,c_39]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_741,plain,
% 8.11/1.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k1_xboole_0)))
% 8.11/1.47      | ~ v1_funct_1(X0)
% 8.11/1.47      | ~ v1_relat_1(X0)
% 8.11/1.47      | k2_relat_1(X0) != k1_xboole_0
% 8.11/1.47      | k1_xboole_0 = X0
% 8.11/1.47      | k1_xboole_0 = k1_relat_1(X0) ),
% 8.11/1.47      inference(unflattening,[status(thm)],[c_740]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_2715,plain,
% 8.11/1.47      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k1_xboole_0)))
% 8.11/1.47      | ~ v1_funct_1(sK3)
% 8.11/1.47      | ~ v1_relat_1(sK3)
% 8.11/1.47      | k2_relat_1(sK3) != k1_xboole_0
% 8.11/1.47      | k1_xboole_0 = k1_relat_1(sK3)
% 8.11/1.47      | k1_xboole_0 = sK3 ),
% 8.11/1.47      inference(instantiation,[status(thm)],[c_741]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_2637,plain,
% 8.11/1.47      ( ~ r1_tarski(X0,sK3) | ~ r1_tarski(sK3,X0) | X0 = sK3 ),
% 8.11/1.47      inference(instantiation,[status(thm)],[c_0]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_2730,plain,
% 8.11/1.47      ( ~ r1_tarski(sK3,sK3) | sK3 = sK3 ),
% 8.11/1.47      inference(instantiation,[status(thm)],[c_2637]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_1027,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_2529,plain,
% 8.11/1.47      ( X0 != X1 | sK3 != X1 | sK3 = X0 ),
% 8.11/1.47      inference(instantiation,[status(thm)],[c_1027]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_3170,plain,
% 8.11/1.47      ( X0 != sK3 | sK3 = X0 | sK3 != sK3 ),
% 8.11/1.47      inference(instantiation,[status(thm)],[c_2529]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_3171,plain,
% 8.11/1.47      ( sK3 != sK3 | sK3 = k1_xboole_0 | k1_xboole_0 != sK3 ),
% 8.11/1.47      inference(instantiation,[status(thm)],[c_3170]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_3719,plain,
% 8.11/1.47      ( r1_tarski(sK3,sK3) ),
% 8.11/1.47      inference(instantiation,[status(thm)],[c_1]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_3818,plain,
% 8.11/1.47      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 8.11/1.47      | ~ r1_tarski(k2_relat_1(k2_funct_1(sK3)),sK1)
% 8.11/1.47      | ~ r1_tarski(k1_relat_1(k2_funct_1(sK3)),sK2)
% 8.11/1.47      | ~ v1_relat_1(k2_funct_1(sK3)) ),
% 8.11/1.47      inference(instantiation,[status(thm)],[c_26]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_2889,plain,
% 8.11/1.47      ( X0 != X1 | X0 = sK1 | sK1 != X1 ),
% 8.11/1.47      inference(instantiation,[status(thm)],[c_1027]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_4738,plain,
% 8.11/1.47      ( k2_relat_1(k2_funct_1(sK3)) != X0
% 8.11/1.47      | k2_relat_1(k2_funct_1(sK3)) = sK1
% 8.11/1.47      | sK1 != X0 ),
% 8.11/1.47      inference(instantiation,[status(thm)],[c_2889]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_4739,plain,
% 8.11/1.47      ( k2_relat_1(k2_funct_1(sK3)) = sK1
% 8.11/1.47      | k2_relat_1(k2_funct_1(sK3)) != k1_xboole_0
% 8.11/1.47      | sK1 != k1_xboole_0 ),
% 8.11/1.47      inference(instantiation,[status(thm)],[c_4738]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_8450,plain,
% 8.11/1.47      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k1_xboole_0)))
% 8.11/1.47      | ~ r1_tarski(sK3,k2_zfmisc_1(k1_relat_1(sK3),k1_xboole_0)) ),
% 8.11/1.47      inference(instantiation,[status(thm)],[c_2481]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_1028,plain,
% 8.11/1.47      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X1) | X2 != X0 ),
% 8.11/1.47      theory(equality) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_2363,plain,
% 8.11/1.47      ( ~ r1_tarski(X0,sK1) | r1_tarski(X1,sK1) | X1 != X0 ),
% 8.11/1.47      inference(instantiation,[status(thm)],[c_1028]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_3016,plain,
% 8.11/1.47      ( r1_tarski(X0,sK1)
% 8.11/1.47      | ~ r1_tarski(k1_relat_1(X1),sK1)
% 8.11/1.47      | X0 != k1_relat_1(X1) ),
% 8.11/1.47      inference(instantiation,[status(thm)],[c_2363]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_6037,plain,
% 8.11/1.47      ( r1_tarski(X0,sK1)
% 8.11/1.47      | ~ r1_tarski(k1_relat_1(sK3),sK1)
% 8.11/1.47      | X0 != k1_relat_1(sK3) ),
% 8.11/1.47      inference(instantiation,[status(thm)],[c_3016]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_11272,plain,
% 8.11/1.47      ( r1_tarski(k2_relat_1(k2_funct_1(sK3)),sK1)
% 8.11/1.47      | ~ r1_tarski(k1_relat_1(sK3),sK1)
% 8.11/1.47      | k2_relat_1(k2_funct_1(sK3)) != k1_relat_1(sK3) ),
% 8.11/1.47      inference(instantiation,[status(thm)],[c_6037]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_38,plain,
% 8.11/1.47      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 8.11/1.47      | ~ v1_funct_1(X0)
% 8.11/1.47      | ~ v1_relat_1(X0) ),
% 8.11/1.47      inference(cnf_transformation,[],[f105]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_1935,plain,
% 8.11/1.47      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
% 8.11/1.47      | v1_funct_1(X0) != iProver_top
% 8.11/1.47      | v1_relat_1(X0) != iProver_top ),
% 8.11/1.47      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_6162,plain,
% 8.11/1.47      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2))) = iProver_top
% 8.11/1.47      | v1_funct_1(sK3) != iProver_top
% 8.11/1.47      | v1_relat_1(sK3) != iProver_top ),
% 8.11/1.47      inference(superposition,[status(thm)],[c_4202,c_1935]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_6334,plain,
% 8.11/1.47      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2))) = iProver_top ),
% 8.11/1.47      inference(global_propositional_subsumption,
% 8.11/1.47                [status(thm)],
% 8.11/1.47                [c_6162,c_47,c_49,c_2479,c_2622,c_2712]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_6339,plain,
% 8.11/1.47      ( r1_tarski(sK3,k2_zfmisc_1(k1_relat_1(sK3),sK2)) = iProver_top ),
% 8.11/1.47      inference(superposition,[status(thm)],[c_6334,c_1951]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_15650,plain,
% 8.11/1.47      ( r1_tarski(sK3,k2_zfmisc_1(k1_relat_1(sK3),k1_xboole_0)) = iProver_top ),
% 8.11/1.47      inference(demodulation,[status(thm)],[c_15614,c_6339]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_15695,plain,
% 8.11/1.47      ( r1_tarski(sK3,k2_zfmisc_1(k1_relat_1(sK3),k1_xboole_0)) ),
% 8.11/1.47      inference(predicate_to_equality_rev,[status(thm)],[c_15650]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_15657,plain,
% 8.11/1.47      ( k2_relat_1(sK3) = k1_xboole_0 ),
% 8.11/1.47      inference(demodulation,[status(thm)],[c_15614,c_4202]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_2344,plain,
% 8.11/1.47      ( ~ r1_tarski(X0,sK2) | r1_tarski(X1,sK2) | X1 != X0 ),
% 8.11/1.47      inference(instantiation,[status(thm)],[c_1028]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_2930,plain,
% 8.11/1.47      ( r1_tarski(X0,sK2) | ~ r1_tarski(sK2,sK2) | X0 != sK2 ),
% 8.11/1.47      inference(instantiation,[status(thm)],[c_2344]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_7882,plain,
% 8.11/1.47      ( r1_tarski(k1_relat_1(X0),sK2)
% 8.11/1.47      | ~ r1_tarski(sK2,sK2)
% 8.11/1.47      | k1_relat_1(X0) != sK2 ),
% 8.11/1.47      inference(instantiation,[status(thm)],[c_2930]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_24413,plain,
% 8.11/1.47      ( r1_tarski(k1_relat_1(k2_funct_1(sK3)),sK2)
% 8.11/1.47      | ~ r1_tarski(sK2,sK2)
% 8.11/1.47      | k1_relat_1(k2_funct_1(sK3)) != sK2 ),
% 8.11/1.47      inference(instantiation,[status(thm)],[c_7882]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_11383,plain,
% 8.11/1.47      ( X0 != X1
% 8.11/1.47      | k2_relat_1(k2_funct_1(sK3)) != X1
% 8.11/1.47      | k2_relat_1(k2_funct_1(sK3)) = X0 ),
% 8.11/1.47      inference(instantiation,[status(thm)],[c_1027]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_26094,plain,
% 8.11/1.47      ( X0 != k1_relat_1(sK3)
% 8.11/1.47      | k2_relat_1(k2_funct_1(sK3)) = X0
% 8.11/1.47      | k2_relat_1(k2_funct_1(sK3)) != k1_relat_1(sK3) ),
% 8.11/1.47      inference(instantiation,[status(thm)],[c_11383]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_26095,plain,
% 8.11/1.47      ( k2_relat_1(k2_funct_1(sK3)) != k1_relat_1(sK3)
% 8.11/1.47      | k2_relat_1(k2_funct_1(sK3)) = k1_xboole_0
% 8.11/1.47      | k1_xboole_0 != k1_relat_1(sK3) ),
% 8.11/1.47      inference(instantiation,[status(thm)],[c_26094]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_26112,plain,
% 8.11/1.47      ( sK3 = k1_xboole_0 ),
% 8.11/1.47      inference(global_propositional_subsumption,
% 8.11/1.47                [status(thm)],
% 8.11/1.47                [c_25962,c_46,c_44,c_49,c_634,c_925,c_2031,c_2428,c_2478,
% 8.11/1.47                 c_2479,c_2621,c_2622,c_2711,c_2712,c_2715,c_2730,c_3171,
% 8.11/1.47                 c_3719,c_3818,c_4012,c_4342,c_4739,c_4772,c_8450,
% 8.11/1.47                 c_11272,c_15695,c_15657,c_24413,c_25922,c_26095]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_15624,plain,
% 8.11/1.47      ( k1_relat_1(k4_relat_1(sK3)) = k1_xboole_0 ),
% 8.11/1.47      inference(demodulation,[status(thm)],[c_15614,c_14307]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_26178,plain,
% 8.11/1.47      ( k1_relat_1(k4_relat_1(k1_xboole_0)) = k1_xboole_0 ),
% 8.11/1.47      inference(demodulation,[status(thm)],[c_26112,c_15624]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_37753,plain,
% 8.11/1.47      ( k1_relset_1(X0,X1,k4_relat_1(k1_xboole_0)) = k1_xboole_0
% 8.11/1.47      | r1_tarski(k1_xboole_0,X0) != iProver_top
% 8.11/1.47      | r1_tarski(k1_xboole_0,X1) != iProver_top
% 8.11/1.47      | v1_relat_1(k4_relat_1(k1_xboole_0)) != iProver_top ),
% 8.11/1.47      inference(light_normalisation,
% 8.11/1.47                [status(thm)],
% 8.11/1.47                [c_37723,c_15079,c_26178]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_140,plain,
% 8.11/1.47      ( v1_relat_1(X0) != iProver_top
% 8.11/1.47      | v1_relat_1(k4_relat_1(X0)) = iProver_top ),
% 8.11/1.47      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_142,plain,
% 8.11/1.47      ( v1_relat_1(k4_relat_1(k1_xboole_0)) = iProver_top
% 8.11/1.47      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 8.11/1.47      inference(instantiation,[status(thm)],[c_140]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_156,plain,
% 8.11/1.47      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 8.11/1.47      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_38129,plain,
% 8.11/1.47      ( r1_tarski(k1_xboole_0,X1) != iProver_top
% 8.11/1.47      | k1_relset_1(X0,X1,k4_relat_1(k1_xboole_0)) = k1_xboole_0 ),
% 8.11/1.47      inference(global_propositional_subsumption,
% 8.11/1.47                [status(thm)],
% 8.11/1.47                [c_37753,c_137,c_142,c_156,c_2589,c_3182]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_38130,plain,
% 8.11/1.47      ( k1_relset_1(X0,X1,k4_relat_1(k1_xboole_0)) = k1_xboole_0
% 8.11/1.47      | r1_tarski(k1_xboole_0,X1) != iProver_top ),
% 8.11/1.47      inference(renaming,[status(thm)],[c_38129]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_38134,plain,
% 8.11/1.47      ( k1_relset_1(X0,X1,k4_relat_1(k1_xboole_0)) = k1_xboole_0 ),
% 8.11/1.47      inference(superposition,[status(thm)],[c_1953,c_38130]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_29,plain,
% 8.11/1.47      ( v1_funct_2(X0,k1_xboole_0,X1)
% 8.11/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 8.11/1.47      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 8.11/1.47      inference(cnf_transformation,[],[f117]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_817,plain,
% 8.11/1.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 8.11/1.47      | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 8.11/1.47      | ~ v1_funct_1(k2_funct_1(sK3))
% 8.11/1.47      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
% 8.11/1.47      | k2_funct_1(sK3) != X0
% 8.11/1.47      | sK1 != X1
% 8.11/1.47      | sK2 != k1_xboole_0 ),
% 8.11/1.47      inference(resolution_lifted,[status(thm)],[c_29,c_41]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_818,plain,
% 8.11/1.47      ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 8.11/1.47      | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
% 8.11/1.47      | ~ v1_funct_1(k2_funct_1(sK3))
% 8.11/1.47      | k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
% 8.11/1.47      | sK2 != k1_xboole_0 ),
% 8.11/1.47      inference(unflattening,[status(thm)],[c_817]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_1921,plain,
% 8.11/1.47      ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
% 8.11/1.47      | sK2 != k1_xboole_0
% 8.11/1.47      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 8.11/1.47      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top
% 8.11/1.47      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 8.11/1.47      inference(predicate_to_equality,[status(thm)],[c_818]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_819,plain,
% 8.11/1.47      ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
% 8.11/1.47      | sK2 != k1_xboole_0
% 8.11/1.47      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 8.11/1.47      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top
% 8.11/1.47      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 8.11/1.47      inference(predicate_to_equality,[status(thm)],[c_818]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_2761,plain,
% 8.11/1.47      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top
% 8.11/1.47      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 8.11/1.47      | sK2 != k1_xboole_0
% 8.11/1.47      | k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0 ),
% 8.11/1.47      inference(global_propositional_subsumption,
% 8.11/1.47                [status(thm)],
% 8.11/1.47                [c_1921,c_47,c_49,c_819,c_2032,c_2479,c_2622,c_2712]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_2762,plain,
% 8.11/1.47      ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
% 8.11/1.47      | sK2 != k1_xboole_0
% 8.11/1.47      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 8.11/1.47      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top ),
% 8.11/1.47      inference(renaming,[status(thm)],[c_2761]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_14580,plain,
% 8.11/1.47      ( k1_relset_1(k1_xboole_0,sK1,k4_relat_1(sK3)) != k1_xboole_0
% 8.11/1.47      | sK2 != k1_xboole_0
% 8.11/1.47      | m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 8.11/1.47      | m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top ),
% 8.11/1.47      inference(demodulation,[status(thm)],[c_14304,c_2762]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_17046,plain,
% 8.11/1.47      ( k1_relset_1(k1_xboole_0,sK1,k4_relat_1(sK3)) != k1_xboole_0
% 8.11/1.47      | m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 8.11/1.47      | m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top ),
% 8.11/1.47      inference(global_propositional_subsumption,
% 8.11/1.47                [status(thm)],
% 8.11/1.47                [c_14580,c_49,c_2479,c_2622,c_2712,c_4013,c_4773,c_12667,
% 8.11/1.47                 c_15559]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_17050,plain,
% 8.11/1.47      ( k1_relset_1(k1_xboole_0,sK1,k4_relat_1(sK3)) != k1_xboole_0
% 8.11/1.47      | m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top ),
% 8.11/1.47      inference(light_normalisation,[status(thm)],[c_17046,c_15614]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_26168,plain,
% 8.11/1.47      ( k1_relset_1(k1_xboole_0,sK1,k4_relat_1(k1_xboole_0)) != k1_xboole_0
% 8.11/1.47      | m1_subset_1(k4_relat_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top ),
% 8.11/1.47      inference(demodulation,[status(thm)],[c_26112,c_17050]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_38302,plain,
% 8.11/1.47      ( k1_xboole_0 != k1_xboole_0
% 8.11/1.47      | m1_subset_1(k4_relat_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top ),
% 8.11/1.47      inference(demodulation,[status(thm)],[c_38134,c_26168]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_38527,plain,
% 8.11/1.47      ( m1_subset_1(k4_relat_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top ),
% 8.11/1.47      inference(equality_resolution_simp,[status(thm)],[c_38302]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_38530,plain,
% 8.11/1.47      ( r1_tarski(k2_relat_1(k4_relat_1(k1_xboole_0)),sK1) != iProver_top
% 8.11/1.47      | r1_tarski(k1_relat_1(k4_relat_1(k1_xboole_0)),k1_xboole_0) != iProver_top
% 8.11/1.47      | v1_relat_1(k4_relat_1(k1_xboole_0)) != iProver_top ),
% 8.11/1.47      inference(superposition,[status(thm)],[c_1939,c_38527]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_38531,plain,
% 8.11/1.47      ( r1_tarski(k1_relat_1(k1_xboole_0),sK1) != iProver_top
% 8.11/1.47      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
% 8.11/1.47      | v1_relat_1(k4_relat_1(k1_xboole_0)) != iProver_top ),
% 8.11/1.47      inference(light_normalisation,
% 8.11/1.47                [status(thm)],
% 8.11/1.47                [c_38530,c_6265,c_26178]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_38532,plain,
% 8.11/1.47      ( r1_tarski(k1_xboole_0,sK1) != iProver_top
% 8.11/1.47      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
% 8.11/1.47      | v1_relat_1(k4_relat_1(k1_xboole_0)) != iProver_top ),
% 8.11/1.47      inference(demodulation,[status(thm)],[c_38531,c_15079]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_4496,plain,
% 8.11/1.47      ( r1_tarski(k1_xboole_0,sK1) ),
% 8.11/1.47      inference(instantiation,[status(thm)],[c_4]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_4497,plain,
% 8.11/1.47      ( r1_tarski(k1_xboole_0,sK1) = iProver_top ),
% 8.11/1.47      inference(predicate_to_equality,[status(thm)],[c_4496]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_158,plain,
% 8.11/1.47      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 8.11/1.47      inference(instantiation,[status(thm)],[c_156]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_38535,plain,
% 8.11/1.47      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
% 8.11/1.47      inference(grounding,
% 8.11/1.47                [status(thm)],
% 8.11/1.47                [c_3182:[bind(X1,$fot(k1_xboole_0)),
% 8.11/1.47                 bind(X0,$fot(k1_xboole_0))]]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_38536,plain,
% 8.11/1.47      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top
% 8.11/1.47      | v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top
% 8.11/1.47      | v1_relat_1(k1_xboole_0) = iProver_top ),
% 8.11/1.47      inference(grounding,
% 8.11/1.47                [status(thm)],
% 8.11/1.47                [c_2589:[bind(X1,$fot(k1_xboole_0)),
% 8.11/1.47                 bind(X0,$fot(k1_xboole_0))]]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(c_38537,plain,
% 8.11/1.47      ( v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
% 8.11/1.47      inference(grounding,
% 8.11/1.47                [status(thm)],
% 8.11/1.47                [c_137:[bind(X1,$fot(k1_xboole_0)),
% 8.11/1.47                 bind(X0,$fot(k1_xboole_0))]]) ).
% 8.11/1.47  
% 8.11/1.47  cnf(contradiction,plain,
% 8.11/1.47      ( $false ),
% 8.11/1.47      inference(minisat,
% 8.11/1.47                [status(thm)],
% 8.11/1.47                [c_38532,c_4497,c_38535,c_38536,c_158,c_142,c_38537]) ).
% 8.11/1.47  
% 8.11/1.47  
% 8.11/1.47  % SZS output end CNFRefutation for theBenchmark.p
% 8.11/1.47  
% 8.11/1.47  ------                               Statistics
% 8.11/1.47  
% 8.11/1.47  ------ General
% 8.11/1.47  
% 8.11/1.47  abstr_ref_over_cycles:                  0
% 8.11/1.47  abstr_ref_under_cycles:                 0
% 8.11/1.47  gc_basic_clause_elim:                   0
% 8.11/1.47  forced_gc_time:                         0
% 8.11/1.47  parsing_time:                           0.009
% 8.11/1.47  unif_index_cands_time:                  0.
% 8.11/1.47  unif_index_add_time:                    0.
% 8.11/1.47  orderings_time:                         0.
% 8.11/1.47  out_proof_time:                         0.02
% 8.11/1.47  total_time:                             0.927
% 8.11/1.47  num_of_symbols:                         53
% 8.11/1.47  num_of_terms:                           25074
% 8.11/1.47  
% 8.11/1.47  ------ Preprocessing
% 8.11/1.47  
% 8.11/1.47  num_of_splits:                          0
% 8.11/1.47  num_of_split_atoms:                     0
% 8.11/1.47  num_of_reused_defs:                     0
% 8.11/1.47  num_eq_ax_congr_red:                    9
% 8.11/1.47  num_of_sem_filtered_clauses:            1
% 8.11/1.47  num_of_subtypes:                        0
% 8.11/1.47  monotx_restored_types:                  0
% 8.11/1.47  sat_num_of_epr_types:                   0
% 8.11/1.47  sat_num_of_non_cyclic_types:            0
% 8.11/1.47  sat_guarded_non_collapsed_types:        0
% 8.11/1.47  num_pure_diseq_elim:                    0
% 8.11/1.47  simp_replaced_by:                       0
% 8.11/1.47  res_preprocessed:                       174
% 8.11/1.47  prep_upred:                             0
% 8.11/1.47  prep_unflattend:                        58
% 8.11/1.47  smt_new_axioms:                         0
% 8.11/1.47  pred_elim_cands:                        7
% 8.11/1.47  pred_elim:                              3
% 8.11/1.47  pred_elim_cl:                           -2
% 8.11/1.47  pred_elim_cycles:                       4
% 8.11/1.47  merged_defs:                            6
% 8.11/1.47  merged_defs_ncl:                        0
% 8.11/1.47  bin_hyper_res:                          7
% 8.11/1.47  prep_cycles:                            3
% 8.11/1.47  pred_elim_time:                         0.01
% 8.11/1.47  splitting_time:                         0.
% 8.11/1.47  sem_filter_time:                        0.
% 8.11/1.47  monotx_time:                            0.001
% 8.11/1.47  subtype_inf_time:                       0.
% 8.11/1.47  
% 8.11/1.47  ------ Problem properties
% 8.11/1.47  
% 8.11/1.47  clauses:                                47
% 8.11/1.47  conjectures:                            3
% 8.11/1.47  epr:                                    6
% 8.11/1.47  horn:                                   41
% 8.11/1.47  ground:                                 15
% 8.11/1.47  unary:                                  11
% 8.11/1.47  binary:                                 17
% 8.11/1.47  lits:                                   119
% 8.11/1.47  lits_eq:                                43
% 8.11/1.47  fd_pure:                                0
% 8.11/1.47  fd_pseudo:                              0
% 8.11/1.47  fd_cond:                                2
% 8.11/1.47  fd_pseudo_cond:                         1
% 8.11/1.47  ac_symbols:                             0
% 8.11/1.47  
% 8.11/1.47  ------ Propositional Solver
% 8.11/1.47  
% 8.11/1.47  prop_solver_calls:                      27
% 8.11/1.47  prop_fast_solver_calls:                 2470
% 8.11/1.47  smt_solver_calls:                       0
% 8.11/1.47  smt_fast_solver_calls:                  0
% 8.11/1.47  prop_num_of_clauses:                    15002
% 8.11/1.47  prop_preprocess_simplified:             27906
% 8.11/1.47  prop_fo_subsumed:                       179
% 8.11/1.47  prop_solver_time:                       0.
% 8.11/1.47  smt_solver_time:                        0.
% 8.11/1.47  smt_fast_solver_time:                   0.
% 8.11/1.47  prop_fast_solver_time:                  0.
% 8.11/1.47  prop_unsat_core_time:                   0.001
% 8.11/1.47  
% 8.11/1.47  ------ QBF
% 8.11/1.47  
% 8.11/1.47  qbf_q_res:                              0
% 8.11/1.47  qbf_num_tautologies:                    0
% 8.11/1.47  qbf_prep_cycles:                        0
% 8.11/1.47  
% 8.11/1.47  ------ BMC1
% 8.11/1.47  
% 8.11/1.47  bmc1_current_bound:                     -1
% 8.11/1.47  bmc1_last_solved_bound:                 -1
% 8.11/1.47  bmc1_unsat_core_size:                   -1
% 8.11/1.47  bmc1_unsat_core_parents_size:           -1
% 8.11/1.47  bmc1_merge_next_fun:                    0
% 8.11/1.47  bmc1_unsat_core_clauses_time:           0.
% 8.11/1.47  
% 8.11/1.47  ------ Instantiation
% 8.11/1.47  
% 8.11/1.47  inst_num_of_clauses:                    3932
% 8.11/1.47  inst_num_in_passive:                    848
% 8.11/1.47  inst_num_in_active:                     1718
% 8.11/1.47  inst_num_in_unprocessed:                1369
% 8.11/1.47  inst_num_of_loops:                      2350
% 8.11/1.47  inst_num_of_learning_restarts:          0
% 8.11/1.47  inst_num_moves_active_passive:          630
% 8.11/1.47  inst_lit_activity:                      0
% 8.11/1.47  inst_lit_activity_moves:                0
% 8.11/1.47  inst_num_tautologies:                   0
% 8.11/1.47  inst_num_prop_implied:                  0
% 8.11/1.47  inst_num_existing_simplified:           0
% 8.11/1.47  inst_num_eq_res_simplified:             0
% 8.11/1.47  inst_num_child_elim:                    0
% 8.11/1.47  inst_num_of_dismatching_blockings:      2550
% 8.11/1.47  inst_num_of_non_proper_insts:           5738
% 8.11/1.47  inst_num_of_duplicates:                 0
% 8.11/1.47  inst_inst_num_from_inst_to_res:         0
% 8.11/1.47  inst_dismatching_checking_time:         0.
% 8.11/1.47  
% 8.11/1.47  ------ Resolution
% 8.11/1.47  
% 8.11/1.47  res_num_of_clauses:                     0
% 8.11/1.47  res_num_in_passive:                     0
% 8.11/1.47  res_num_in_active:                      0
% 8.11/1.47  res_num_of_loops:                       177
% 8.11/1.47  res_forward_subset_subsumed:            239
% 8.11/1.47  res_backward_subset_subsumed:           6
% 8.11/1.47  res_forward_subsumed:                   0
% 8.11/1.47  res_backward_subsumed:                  0
% 8.11/1.47  res_forward_subsumption_resolution:     2
% 8.11/1.47  res_backward_subsumption_resolution:    0
% 8.11/1.47  res_clause_to_clause_subsumption:       5146
% 8.11/1.47  res_orphan_elimination:                 0
% 8.11/1.47  res_tautology_del:                      764
% 8.11/1.47  res_num_eq_res_simplified:              0
% 8.11/1.47  res_num_sel_changes:                    0
% 8.11/1.47  res_moves_from_active_to_pass:          0
% 8.11/1.47  
% 8.11/1.47  ------ Superposition
% 8.11/1.47  
% 8.11/1.47  sup_time_total:                         0.
% 8.11/1.47  sup_time_generating:                    0.
% 8.11/1.47  sup_time_sim_full:                      0.
% 8.11/1.47  sup_time_sim_immed:                     0.
% 8.11/1.47  
% 8.11/1.47  sup_num_of_clauses:                     983
% 8.11/1.47  sup_num_in_active:                      240
% 8.11/1.47  sup_num_in_passive:                     743
% 8.11/1.47  sup_num_of_loops:                       468
% 8.11/1.47  sup_fw_superposition:                   907
% 8.11/1.47  sup_bw_superposition:                   881
% 8.11/1.47  sup_immediate_simplified:               741
% 8.11/1.47  sup_given_eliminated:                   4
% 8.11/1.47  comparisons_done:                       0
% 8.11/1.47  comparisons_avoided:                    59
% 8.11/1.47  
% 8.11/1.47  ------ Simplifications
% 8.11/1.47  
% 8.11/1.47  
% 8.11/1.47  sim_fw_subset_subsumed:                 97
% 8.11/1.47  sim_bw_subset_subsumed:                 66
% 8.11/1.47  sim_fw_subsumed:                        155
% 8.11/1.47  sim_bw_subsumed:                        50
% 8.11/1.47  sim_fw_subsumption_res:                 0
% 8.11/1.47  sim_bw_subsumption_res:                 0
% 8.11/1.47  sim_tautology_del:                      16
% 8.11/1.47  sim_eq_tautology_del:                   123
% 8.11/1.47  sim_eq_res_simp:                        5
% 8.11/1.47  sim_fw_demodulated:                     140
% 8.11/1.47  sim_bw_demodulated:                     197
% 8.11/1.47  sim_light_normalised:                   544
% 8.11/1.47  sim_joinable_taut:                      0
% 8.11/1.47  sim_joinable_simp:                      0
% 8.11/1.47  sim_ac_normalised:                      0
% 8.11/1.47  sim_smt_subsumption:                    0
% 8.11/1.47  
%------------------------------------------------------------------------------
