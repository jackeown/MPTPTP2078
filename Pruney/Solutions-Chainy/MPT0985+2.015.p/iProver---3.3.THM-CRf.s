%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:02:22 EST 2020

% Result     : Theorem 2.90s
% Output     : CNFRefutation 2.90s
% Verified   : 
% Statistics : Number of formulae       :  215 (4354 expanded)
%              Number of clauses        :  147 (1536 expanded)
%              Number of leaves         :   21 ( 841 expanded)
%              Depth                    :   26
%              Number of atoms          :  666 (22298 expanded)
%              Number of equality atoms :  325 (4647 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18,axiom,(
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

fof(f42,plain,(
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
    inference(ennf_transformation,[],[f18])).

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
    inference(flattening,[],[f42])).

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
    inference(nnf_transformation,[],[f43])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f52])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f48,plain,(
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

fof(f49,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f48])).

fof(f53,plain,
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

fof(f54,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
      | ~ v1_funct_1(k2_funct_1(sK2)) )
    & k2_relset_1(sK0,sK1,sK2) = sK1
    & v2_funct_1(sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f49,f53])).

fof(f93,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f54])).

fof(f94,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f54])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f13,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f38,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f37])).

fof(f74,plain,(
    ! [X0] :
      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f95,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f54])).

fof(f92,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f54])).

fof(f11,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f34,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f33])).

fof(f70,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f100,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f84])).

fof(f19,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f45,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f44])).

fof(f87,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f73,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f96,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f54])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f56,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f46])).

fof(f90,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f97,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f54])).

fof(f12,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f36,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f35])).

fof(f72,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f71,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f29,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f63,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f88,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f8,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

cnf(c_30,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_41,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_958,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK0 != X1
    | sK1 != X2
    | sK2 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_41])).

cnf(c_959,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_relset_1(sK0,sK1,sK2) = sK0
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_958])).

cnf(c_40,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_961,plain,
    ( k1_relset_1(sK0,sK1,sK2) = sK0
    | k1_xboole_0 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_959,c_40])).

cnf(c_2264,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_2268,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_4372,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_2264,c_2268])).

cnf(c_4457,plain,
    ( k1_relat_1(sK2) = sK0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_961,c_4372])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_2269,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3764,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2264,c_2269])).

cnf(c_18,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_39,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_661,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_39])).

cnf(c_662,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_661])).

cnf(c_42,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_664,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_662,c_42])).

cnf(c_2258,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_664])).

cnf(c_3824,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_3764,c_2258])).

cnf(c_15,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(X0) = k4_relat_1(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_675,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(X0) = k4_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_39])).

cnf(c_676,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_675])).

cnf(c_678,plain,
    ( ~ v1_relat_1(sK2)
    | k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_676,c_42])).

cnf(c_2257,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_678])).

cnf(c_3825,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_3764,c_2257])).

cnf(c_3828,plain,
    ( k2_relat_1(k4_relat_1(sK2)) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_3824,c_3825])).

cnf(c_26,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f100])).

cnf(c_32,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_738,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | X2 != X0
    | k1_relat_1(X2) != X1
    | k2_relat_1(X2) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_32])).

cnf(c_739,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k1_xboole_0)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = k1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_738])).

cnf(c_755,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k1_xboole_0)))
    | ~ v1_funct_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = k1_relat_1(X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_739,c_22])).

cnf(c_2255,plain,
    ( k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = k1_relat_1(X0)
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k1_xboole_0))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_755])).

cnf(c_6415,plain,
    ( k1_relat_1(k4_relat_1(sK2)) = k1_xboole_0
    | k1_relat_1(sK2) != k1_xboole_0
    | k4_relat_1(sK2) = k1_xboole_0
    | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k4_relat_1(sK2)),k1_xboole_0))) != iProver_top
    | v1_funct_1(k4_relat_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3828,c_2255])).

cnf(c_19,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_647,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_39])).

cnf(c_648,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_647])).

cnf(c_650,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_648,c_42])).

cnf(c_2259,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_650])).

cnf(c_3823,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_3764,c_2259])).

cnf(c_3831,plain,
    ( k1_relat_1(k4_relat_1(sK2)) = k2_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_3823,c_3825])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_2267,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_4275,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_2264,c_2267])).

cnf(c_38,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f96])).

cnf(c_4277,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_4275,c_38])).

cnf(c_4753,plain,
    ( k1_relat_1(k4_relat_1(sK2)) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_3831,c_4277])).

cnf(c_6421,plain,
    ( k1_relat_1(k4_relat_1(sK2)) = k1_xboole_0
    | k1_relat_1(sK2) != k1_xboole_0
    | k4_relat_1(sK2) = k1_xboole_0
    | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) != iProver_top
    | v1_funct_1(k4_relat_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6415,c_4753])).

cnf(c_6422,plain,
    ( k1_relat_1(sK2) != k1_xboole_0
    | k4_relat_1(sK2) = k1_xboole_0
    | sK1 = k1_xboole_0
    | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) != iProver_top
    | v1_funct_1(k4_relat_1(sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6421,c_4753])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_132,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_2,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_35,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_37,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_988,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(X0)
    | k2_funct_1(sK2) != X0
    | k1_relat_1(X0) != sK1
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_35,c_37])).

cnf(c_989,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
    inference(unflattening,[status(thm)],[c_988])).

cnf(c_1001,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_989,c_22])).

cnf(c_1184,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_relat_1(k2_funct_1(sK2)) != sK1
    | k2_relat_1(k2_funct_1(sK2)) != k1_xboole_0
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_1001])).

cnf(c_1185,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_relat_1(k2_funct_1(sK2)) != sK1
    | k2_relat_1(k2_funct_1(sK2)) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_1184])).

cnf(c_16,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_2621,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_2630,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_2757,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_2630])).

cnf(c_1341,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2791,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_1341])).

cnf(c_1342,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2908,plain,
    ( k1_relat_1(k2_funct_1(sK2)) != X0
    | k1_relat_1(k2_funct_1(sK2)) = sK1
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_1342])).

cnf(c_3024,plain,
    ( k1_relat_1(k2_funct_1(sK2)) != k2_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = sK1
    | sK1 != k2_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_2908])).

cnf(c_2769,plain,
    ( X0 != X1
    | k2_funct_1(sK2) != X1
    | k2_funct_1(sK2) = X0 ),
    inference(instantiation,[status(thm)],[c_1342])).

cnf(c_3047,plain,
    ( X0 != k4_relat_1(sK2)
    | k2_funct_1(sK2) = X0
    | k2_funct_1(sK2) != k4_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_2769])).

cnf(c_3048,plain,
    ( k2_funct_1(sK2) != k4_relat_1(sK2)
    | k2_funct_1(sK2) = k1_xboole_0
    | k1_xboole_0 != k4_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_3047])).

cnf(c_1346,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2707,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | X0 != X2
    | X1 != k1_zfmisc_1(X3) ),
    inference(instantiation,[status(thm)],[c_1346])).

cnf(c_2881,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(X2,k1_zfmisc_1(X1))
    | X2 != X0
    | k1_zfmisc_1(X1) != k1_zfmisc_1(X1) ),
    inference(instantiation,[status(thm)],[c_2707])).

cnf(c_3239,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | k2_funct_1(sK2) != X0
    | k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_2881])).

cnf(c_3241,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | k2_funct_1(sK2) != k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_3239])).

cnf(c_3339,plain,
    ( ~ v1_xboole_0(k4_relat_1(sK2))
    | k1_xboole_0 = k4_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2882,plain,
    ( k1_zfmisc_1(X0) = k1_zfmisc_1(X0) ),
    inference(instantiation,[status(thm)],[c_1341])).

cnf(c_3362,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) = k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_2882])).

cnf(c_2792,plain,
    ( X0 != X1
    | sK1 != X1
    | sK1 = X0 ),
    inference(instantiation,[status(thm)],[c_1342])).

cnf(c_3500,plain,
    ( k2_relat_1(sK2) != X0
    | sK1 != X0
    | sK1 = k2_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_2792])).

cnf(c_4146,plain,
    ( k2_relat_1(sK2) != sK1
    | sK1 = k2_relat_1(sK2)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_3500])).

cnf(c_17,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_2272,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_4447,plain,
    ( v1_funct_1(sK2) != iProver_top
    | v1_relat_1(k4_relat_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3825,c_2272])).

cnf(c_4455,plain,
    ( ~ v1_funct_1(sK2)
    | v1_relat_1(k4_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4447])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | v1_xboole_0(X0)
    | ~ v1_xboole_0(k2_relat_1(X0)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_2275,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(k2_relat_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_4943,plain,
    ( v1_relat_1(k4_relat_1(sK2)) != iProver_top
    | v1_xboole_0(k1_relat_1(sK2)) != iProver_top
    | v1_xboole_0(k4_relat_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3828,c_2275])).

cnf(c_4957,plain,
    ( ~ v1_relat_1(k4_relat_1(sK2))
    | ~ v1_xboole_0(k1_relat_1(sK2))
    | v1_xboole_0(k4_relat_1(sK2)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4943])).

cnf(c_3,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_2659,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_5288,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ r1_tarski(X0,k2_zfmisc_1(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_2659])).

cnf(c_5290,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_5288])).

cnf(c_1343,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_5445,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k1_relat_1(sK2))
    | k1_relat_1(sK2) != X0 ),
    inference(instantiation,[status(thm)],[c_1343])).

cnf(c_5447,plain,
    ( v1_xboole_0(k1_relat_1(sK2))
    | ~ v1_xboole_0(k1_xboole_0)
    | k1_relat_1(sK2) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5445])).

cnf(c_4121,plain,
    ( X0 != X1
    | k2_relat_1(k2_funct_1(sK2)) != X1
    | k2_relat_1(k2_funct_1(sK2)) = X0 ),
    inference(instantiation,[status(thm)],[c_1342])).

cnf(c_5685,plain,
    ( X0 != k1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = X0
    | k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_4121])).

cnf(c_5686,plain,
    ( k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_xboole_0
    | k1_xboole_0 != k1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_5685])).

cnf(c_5938,plain,
    ( X0 != X1
    | X0 = k1_relat_1(sK2)
    | k1_relat_1(sK2) != X1 ),
    inference(instantiation,[status(thm)],[c_1342])).

cnf(c_5939,plain,
    ( k1_relat_1(sK2) != k1_xboole_0
    | k1_xboole_0 = k1_relat_1(sK2)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5938])).

cnf(c_2816,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_6629,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_2816])).

cnf(c_6655,plain,
    ( k1_relat_1(sK2) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6422,c_42,c_40,c_132,c_0,c_648,c_662,c_676,c_1185,c_2621,c_2757,c_2791,c_3024,c_3048,c_3241,c_3339,c_3362,c_4146,c_4277,c_4455,c_4957,c_5290,c_5447,c_5686,c_5939,c_6629])).

cnf(c_6658,plain,
    ( sK0 != k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4457,c_6655])).

cnf(c_31,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_2266,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_4982,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k4_relat_1(sK2)),k1_relat_1(sK2)))) = iProver_top
    | v1_funct_1(k4_relat_1(sK2)) != iProver_top
    | v1_relat_1(k4_relat_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3828,c_2266])).

cnf(c_5002,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) = iProver_top
    | v1_funct_1(k4_relat_1(sK2)) != iProver_top
    | v1_relat_1(k4_relat_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4982,c_4753])).

cnf(c_43,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_45,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_2758,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2757])).

cnf(c_2273,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_funct_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_4916,plain,
    ( v1_funct_1(k4_relat_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3825,c_2273])).

cnf(c_5364,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5002,c_43,c_45,c_2758,c_4447,c_4916])).

cnf(c_5369,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4457,c_5364])).

cnf(c_5371,plain,
    ( k1_relset_1(sK1,k1_relat_1(sK2),k4_relat_1(sK2)) = k1_relat_1(k4_relat_1(sK2)) ),
    inference(superposition,[status(thm)],[c_5364,c_2268])).

cnf(c_5378,plain,
    ( k1_relset_1(sK1,k1_relat_1(sK2),k4_relat_1(sK2)) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_5371,c_4753])).

cnf(c_5389,plain,
    ( k1_relset_1(sK1,sK0,k4_relat_1(sK2)) = sK1
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4457,c_5378])).

cnf(c_28,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_942,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_relset_1(X1,X2,X0) != X1
    | k2_funct_1(sK2) != X0
    | sK0 != X2
    | sK1 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_37])).

cnf(c_943,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_relset_1(sK1,sK0,k2_funct_1(sK2)) != sK1
    | k1_xboole_0 = sK0 ),
    inference(unflattening,[status(thm)],[c_942])).

cnf(c_2246,plain,
    ( k1_relset_1(sK1,sK0,k2_funct_1(sK2)) != sK1
    | k1_xboole_0 = sK0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_943])).

cnf(c_944,plain,
    ( k1_relset_1(sK1,sK0,k2_funct_1(sK2)) != sK1
    | k1_xboole_0 = sK0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_943])).

cnf(c_2622,plain,
    ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2621])).

cnf(c_2783,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | k1_xboole_0 = sK0
    | k1_relset_1(sK1,sK0,k2_funct_1(sK2)) != sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2246,c_43,c_45,c_944,c_2622,c_2758])).

cnf(c_2784,plain,
    ( k1_relset_1(sK1,sK0,k2_funct_1(sK2)) != sK1
    | k1_xboole_0 = sK0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2783])).

cnf(c_3904,plain,
    ( k1_relset_1(sK1,sK0,k4_relat_1(sK2)) != sK1
    | sK0 = k1_xboole_0
    | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3825,c_2784])).

cnf(c_5452,plain,
    ( sK0 = k1_xboole_0
    | sK1 = k1_xboole_0
    | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5389,c_3904])).

cnf(c_6741,plain,
    ( sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6658,c_5369,c_5452])).

cnf(c_6414,plain,
    ( k1_relat_1(sK2) = k1_xboole_0
    | sK1 != k1_xboole_0
    | sK2 = k1_xboole_0
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4277,c_2255])).

cnf(c_6647,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0))) != iProver_top
    | sK2 = k1_xboole_0
    | sK1 != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6414,c_42,c_43,c_40,c_132,c_0,c_648,c_662,c_676,c_1185,c_2621,c_2757,c_2791,c_3024,c_3048,c_3241,c_3339,c_3362,c_4146,c_4277,c_4455,c_4957,c_5290,c_5447,c_5686,c_5939,c_6629])).

cnf(c_6648,plain,
    ( sK1 != k1_xboole_0
    | sK2 = k1_xboole_0
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_6647])).

cnf(c_6744,plain,
    ( sK2 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6741,c_6648])).

cnf(c_6844,plain,
    ( sK2 = k1_xboole_0
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_6744])).

cnf(c_4981,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4277,c_2266])).

cnf(c_5147,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4981,c_43,c_45,c_2758])).

cnf(c_6754,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6741,c_5147])).

cnf(c_6847,plain,
    ( sK2 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6844,c_6754])).

cnf(c_7078,plain,
    ( k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6847,c_6655])).

cnf(c_10,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_7090,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_7078,c_10])).

cnf(c_7091,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_7090])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:16:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.90/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.90/0.98  
% 2.90/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.90/0.98  
% 2.90/0.98  ------  iProver source info
% 2.90/0.98  
% 2.90/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.90/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.90/0.98  git: non_committed_changes: false
% 2.90/0.98  git: last_make_outside_of_git: false
% 2.90/0.98  
% 2.90/0.98  ------ 
% 2.90/0.98  
% 2.90/0.98  ------ Input Options
% 2.90/0.98  
% 2.90/0.98  --out_options                           all
% 2.90/0.98  --tptp_safe_out                         true
% 2.90/0.98  --problem_path                          ""
% 2.90/0.98  --include_path                          ""
% 2.90/0.98  --clausifier                            res/vclausify_rel
% 2.90/0.98  --clausifier_options                    --mode clausify
% 2.90/0.98  --stdin                                 false
% 2.90/0.98  --stats_out                             all
% 2.90/0.98  
% 2.90/0.98  ------ General Options
% 2.90/0.98  
% 2.90/0.98  --fof                                   false
% 2.90/0.98  --time_out_real                         305.
% 2.90/0.98  --time_out_virtual                      -1.
% 2.90/0.98  --symbol_type_check                     false
% 2.90/0.98  --clausify_out                          false
% 2.90/0.98  --sig_cnt_out                           false
% 2.90/0.98  --trig_cnt_out                          false
% 2.90/0.98  --trig_cnt_out_tolerance                1.
% 2.90/0.98  --trig_cnt_out_sk_spl                   false
% 2.90/0.98  --abstr_cl_out                          false
% 2.90/0.98  
% 2.90/0.98  ------ Global Options
% 2.90/0.98  
% 2.90/0.98  --schedule                              default
% 2.90/0.98  --add_important_lit                     false
% 2.90/0.98  --prop_solver_per_cl                    1000
% 2.90/0.98  --min_unsat_core                        false
% 2.90/0.98  --soft_assumptions                      false
% 2.90/0.98  --soft_lemma_size                       3
% 2.90/0.98  --prop_impl_unit_size                   0
% 2.90/0.98  --prop_impl_unit                        []
% 2.90/0.98  --share_sel_clauses                     true
% 2.90/0.98  --reset_solvers                         false
% 2.90/0.98  --bc_imp_inh                            [conj_cone]
% 2.90/0.98  --conj_cone_tolerance                   3.
% 2.90/0.98  --extra_neg_conj                        none
% 2.90/0.98  --large_theory_mode                     true
% 2.90/0.98  --prolific_symb_bound                   200
% 2.90/0.98  --lt_threshold                          2000
% 2.90/0.98  --clause_weak_htbl                      true
% 2.90/0.98  --gc_record_bc_elim                     false
% 2.90/0.98  
% 2.90/0.98  ------ Preprocessing Options
% 2.90/0.98  
% 2.90/0.98  --preprocessing_flag                    true
% 2.90/0.98  --time_out_prep_mult                    0.1
% 2.90/0.98  --splitting_mode                        input
% 2.90/0.98  --splitting_grd                         true
% 2.90/0.98  --splitting_cvd                         false
% 2.90/0.98  --splitting_cvd_svl                     false
% 2.90/0.98  --splitting_nvd                         32
% 2.90/0.98  --sub_typing                            true
% 2.90/0.98  --prep_gs_sim                           true
% 2.90/0.98  --prep_unflatten                        true
% 2.90/0.98  --prep_res_sim                          true
% 2.90/0.98  --prep_upred                            true
% 2.90/0.98  --prep_sem_filter                       exhaustive
% 2.90/0.98  --prep_sem_filter_out                   false
% 2.90/0.98  --pred_elim                             true
% 2.90/0.98  --res_sim_input                         true
% 2.90/0.98  --eq_ax_congr_red                       true
% 2.90/0.98  --pure_diseq_elim                       true
% 2.90/0.98  --brand_transform                       false
% 2.90/0.98  --non_eq_to_eq                          false
% 2.90/0.98  --prep_def_merge                        true
% 2.90/0.98  --prep_def_merge_prop_impl              false
% 2.90/0.98  --prep_def_merge_mbd                    true
% 2.90/0.98  --prep_def_merge_tr_red                 false
% 2.90/0.98  --prep_def_merge_tr_cl                  false
% 2.90/0.98  --smt_preprocessing                     true
% 2.90/0.98  --smt_ac_axioms                         fast
% 2.90/0.98  --preprocessed_out                      false
% 2.90/0.98  --preprocessed_stats                    false
% 2.90/0.98  
% 2.90/0.98  ------ Abstraction refinement Options
% 2.90/0.98  
% 2.90/0.98  --abstr_ref                             []
% 2.90/0.98  --abstr_ref_prep                        false
% 2.90/0.98  --abstr_ref_until_sat                   false
% 2.90/0.98  --abstr_ref_sig_restrict                funpre
% 2.90/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.90/0.98  --abstr_ref_under                       []
% 2.90/0.98  
% 2.90/0.98  ------ SAT Options
% 2.90/0.98  
% 2.90/0.98  --sat_mode                              false
% 2.90/0.98  --sat_fm_restart_options                ""
% 2.90/0.98  --sat_gr_def                            false
% 2.90/0.98  --sat_epr_types                         true
% 2.90/0.98  --sat_non_cyclic_types                  false
% 2.90/0.98  --sat_finite_models                     false
% 2.90/0.98  --sat_fm_lemmas                         false
% 2.90/0.98  --sat_fm_prep                           false
% 2.90/0.98  --sat_fm_uc_incr                        true
% 2.90/0.98  --sat_out_model                         small
% 2.90/0.98  --sat_out_clauses                       false
% 2.90/0.98  
% 2.90/0.98  ------ QBF Options
% 2.90/0.98  
% 2.90/0.98  --qbf_mode                              false
% 2.90/0.98  --qbf_elim_univ                         false
% 2.90/0.98  --qbf_dom_inst                          none
% 2.90/0.98  --qbf_dom_pre_inst                      false
% 2.90/0.98  --qbf_sk_in                             false
% 2.90/0.98  --qbf_pred_elim                         true
% 2.90/0.98  --qbf_split                             512
% 2.90/0.98  
% 2.90/0.98  ------ BMC1 Options
% 2.90/0.98  
% 2.90/0.98  --bmc1_incremental                      false
% 2.90/0.98  --bmc1_axioms                           reachable_all
% 2.90/0.98  --bmc1_min_bound                        0
% 2.90/0.98  --bmc1_max_bound                        -1
% 2.90/0.98  --bmc1_max_bound_default                -1
% 2.90/0.98  --bmc1_symbol_reachability              true
% 2.90/0.98  --bmc1_property_lemmas                  false
% 2.90/0.98  --bmc1_k_induction                      false
% 2.90/0.98  --bmc1_non_equiv_states                 false
% 2.90/0.98  --bmc1_deadlock                         false
% 2.90/0.98  --bmc1_ucm                              false
% 2.90/0.98  --bmc1_add_unsat_core                   none
% 2.90/0.98  --bmc1_unsat_core_children              false
% 2.90/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.90/0.98  --bmc1_out_stat                         full
% 2.90/0.98  --bmc1_ground_init                      false
% 2.90/0.98  --bmc1_pre_inst_next_state              false
% 2.90/0.98  --bmc1_pre_inst_state                   false
% 2.90/0.98  --bmc1_pre_inst_reach_state             false
% 2.90/0.98  --bmc1_out_unsat_core                   false
% 2.90/0.98  --bmc1_aig_witness_out                  false
% 2.90/0.98  --bmc1_verbose                          false
% 2.90/0.98  --bmc1_dump_clauses_tptp                false
% 2.90/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.90/0.98  --bmc1_dump_file                        -
% 2.90/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.90/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.90/0.98  --bmc1_ucm_extend_mode                  1
% 2.90/0.98  --bmc1_ucm_init_mode                    2
% 2.90/0.98  --bmc1_ucm_cone_mode                    none
% 2.90/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.90/0.98  --bmc1_ucm_relax_model                  4
% 2.90/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.90/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.90/0.98  --bmc1_ucm_layered_model                none
% 2.90/0.99  --bmc1_ucm_max_lemma_size               10
% 2.90/0.99  
% 2.90/0.99  ------ AIG Options
% 2.90/0.99  
% 2.90/0.99  --aig_mode                              false
% 2.90/0.99  
% 2.90/0.99  ------ Instantiation Options
% 2.90/0.99  
% 2.90/0.99  --instantiation_flag                    true
% 2.90/0.99  --inst_sos_flag                         false
% 2.90/0.99  --inst_sos_phase                        true
% 2.90/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.90/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.90/0.99  --inst_lit_sel_side                     num_symb
% 2.90/0.99  --inst_solver_per_active                1400
% 2.90/0.99  --inst_solver_calls_frac                1.
% 2.90/0.99  --inst_passive_queue_type               priority_queues
% 2.90/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.90/0.99  --inst_passive_queues_freq              [25;2]
% 2.90/0.99  --inst_dismatching                      true
% 2.90/0.99  --inst_eager_unprocessed_to_passive     true
% 2.90/0.99  --inst_prop_sim_given                   true
% 2.90/0.99  --inst_prop_sim_new                     false
% 2.90/0.99  --inst_subs_new                         false
% 2.90/0.99  --inst_eq_res_simp                      false
% 2.90/0.99  --inst_subs_given                       false
% 2.90/0.99  --inst_orphan_elimination               true
% 2.90/0.99  --inst_learning_loop_flag               true
% 2.90/0.99  --inst_learning_start                   3000
% 2.90/0.99  --inst_learning_factor                  2
% 2.90/0.99  --inst_start_prop_sim_after_learn       3
% 2.90/0.99  --inst_sel_renew                        solver
% 2.90/0.99  --inst_lit_activity_flag                true
% 2.90/0.99  --inst_restr_to_given                   false
% 2.90/0.99  --inst_activity_threshold               500
% 2.90/0.99  --inst_out_proof                        true
% 2.90/0.99  
% 2.90/0.99  ------ Resolution Options
% 2.90/0.99  
% 2.90/0.99  --resolution_flag                       true
% 2.90/0.99  --res_lit_sel                           adaptive
% 2.90/0.99  --res_lit_sel_side                      none
% 2.90/0.99  --res_ordering                          kbo
% 2.90/0.99  --res_to_prop_solver                    active
% 2.90/0.99  --res_prop_simpl_new                    false
% 2.90/0.99  --res_prop_simpl_given                  true
% 2.90/0.99  --res_passive_queue_type                priority_queues
% 2.90/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.90/0.99  --res_passive_queues_freq               [15;5]
% 2.90/0.99  --res_forward_subs                      full
% 2.90/0.99  --res_backward_subs                     full
% 2.90/0.99  --res_forward_subs_resolution           true
% 2.90/0.99  --res_backward_subs_resolution          true
% 2.90/0.99  --res_orphan_elimination                true
% 2.90/0.99  --res_time_limit                        2.
% 2.90/0.99  --res_out_proof                         true
% 2.90/0.99  
% 2.90/0.99  ------ Superposition Options
% 2.90/0.99  
% 2.90/0.99  --superposition_flag                    true
% 2.90/0.99  --sup_passive_queue_type                priority_queues
% 2.90/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.90/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.90/0.99  --demod_completeness_check              fast
% 2.90/0.99  --demod_use_ground                      true
% 2.90/0.99  --sup_to_prop_solver                    passive
% 2.90/0.99  --sup_prop_simpl_new                    true
% 2.90/0.99  --sup_prop_simpl_given                  true
% 2.90/0.99  --sup_fun_splitting                     false
% 2.90/0.99  --sup_smt_interval                      50000
% 2.90/0.99  
% 2.90/0.99  ------ Superposition Simplification Setup
% 2.90/0.99  
% 2.90/0.99  --sup_indices_passive                   []
% 2.90/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.90/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.90/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.90/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.90/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.90/0.99  --sup_full_bw                           [BwDemod]
% 2.90/0.99  --sup_immed_triv                        [TrivRules]
% 2.90/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.90/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.90/0.99  --sup_immed_bw_main                     []
% 2.90/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.90/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.90/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.90/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.90/0.99  
% 2.90/0.99  ------ Combination Options
% 2.90/0.99  
% 2.90/0.99  --comb_res_mult                         3
% 2.90/0.99  --comb_sup_mult                         2
% 2.90/0.99  --comb_inst_mult                        10
% 2.90/0.99  
% 2.90/0.99  ------ Debug Options
% 2.90/0.99  
% 2.90/0.99  --dbg_backtrace                         false
% 2.90/0.99  --dbg_dump_prop_clauses                 false
% 2.90/0.99  --dbg_dump_prop_clauses_file            -
% 2.90/0.99  --dbg_out_stat                          false
% 2.90/0.99  ------ Parsing...
% 2.90/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.90/0.99  
% 2.90/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e 
% 2.90/0.99  
% 2.90/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.90/0.99  
% 2.90/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.90/0.99  ------ Proving...
% 2.90/0.99  ------ Problem Properties 
% 2.90/0.99  
% 2.90/0.99  
% 2.90/0.99  clauses                                 45
% 2.90/0.99  conjectures                             3
% 2.90/0.99  EPR                                     8
% 2.90/0.99  Horn                                    39
% 2.90/0.99  unary                                   9
% 2.90/0.99  binary                                  17
% 2.90/0.99  lits                                    120
% 2.90/0.99  lits eq                                 44
% 2.90/0.99  fd_pure                                 0
% 2.90/0.99  fd_pseudo                               0
% 2.90/0.99  fd_cond                                 4
% 2.90/0.99  fd_pseudo_cond                          0
% 2.90/0.99  AC symbols                              0
% 2.90/0.99  
% 2.90/0.99  ------ Schedule dynamic 5 is on 
% 2.90/0.99  
% 2.90/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.90/0.99  
% 2.90/0.99  
% 2.90/0.99  ------ 
% 2.90/0.99  Current options:
% 2.90/0.99  ------ 
% 2.90/0.99  
% 2.90/0.99  ------ Input Options
% 2.90/0.99  
% 2.90/0.99  --out_options                           all
% 2.90/0.99  --tptp_safe_out                         true
% 2.90/0.99  --problem_path                          ""
% 2.90/0.99  --include_path                          ""
% 2.90/0.99  --clausifier                            res/vclausify_rel
% 2.90/0.99  --clausifier_options                    --mode clausify
% 2.90/0.99  --stdin                                 false
% 2.90/0.99  --stats_out                             all
% 2.90/0.99  
% 2.90/0.99  ------ General Options
% 2.90/0.99  
% 2.90/0.99  --fof                                   false
% 2.90/0.99  --time_out_real                         305.
% 2.90/0.99  --time_out_virtual                      -1.
% 2.90/0.99  --symbol_type_check                     false
% 2.90/0.99  --clausify_out                          false
% 2.90/0.99  --sig_cnt_out                           false
% 2.90/0.99  --trig_cnt_out                          false
% 2.90/0.99  --trig_cnt_out_tolerance                1.
% 2.90/0.99  --trig_cnt_out_sk_spl                   false
% 2.90/0.99  --abstr_cl_out                          false
% 2.90/0.99  
% 2.90/0.99  ------ Global Options
% 2.90/0.99  
% 2.90/0.99  --schedule                              default
% 2.90/0.99  --add_important_lit                     false
% 2.90/0.99  --prop_solver_per_cl                    1000
% 2.90/0.99  --min_unsat_core                        false
% 2.90/0.99  --soft_assumptions                      false
% 2.90/0.99  --soft_lemma_size                       3
% 2.90/0.99  --prop_impl_unit_size                   0
% 2.90/0.99  --prop_impl_unit                        []
% 2.90/0.99  --share_sel_clauses                     true
% 2.90/0.99  --reset_solvers                         false
% 2.90/0.99  --bc_imp_inh                            [conj_cone]
% 2.90/0.99  --conj_cone_tolerance                   3.
% 2.90/0.99  --extra_neg_conj                        none
% 2.90/0.99  --large_theory_mode                     true
% 2.90/0.99  --prolific_symb_bound                   200
% 2.90/0.99  --lt_threshold                          2000
% 2.90/0.99  --clause_weak_htbl                      true
% 2.90/0.99  --gc_record_bc_elim                     false
% 2.90/0.99  
% 2.90/0.99  ------ Preprocessing Options
% 2.90/0.99  
% 2.90/0.99  --preprocessing_flag                    true
% 2.90/0.99  --time_out_prep_mult                    0.1
% 2.90/0.99  --splitting_mode                        input
% 2.90/0.99  --splitting_grd                         true
% 2.90/0.99  --splitting_cvd                         false
% 2.90/0.99  --splitting_cvd_svl                     false
% 2.90/0.99  --splitting_nvd                         32
% 2.90/0.99  --sub_typing                            true
% 2.90/0.99  --prep_gs_sim                           true
% 2.90/0.99  --prep_unflatten                        true
% 2.90/0.99  --prep_res_sim                          true
% 2.90/0.99  --prep_upred                            true
% 2.90/0.99  --prep_sem_filter                       exhaustive
% 2.90/0.99  --prep_sem_filter_out                   false
% 2.90/0.99  --pred_elim                             true
% 2.90/0.99  --res_sim_input                         true
% 2.90/0.99  --eq_ax_congr_red                       true
% 2.90/0.99  --pure_diseq_elim                       true
% 2.90/0.99  --brand_transform                       false
% 2.90/0.99  --non_eq_to_eq                          false
% 2.90/0.99  --prep_def_merge                        true
% 2.90/0.99  --prep_def_merge_prop_impl              false
% 2.90/0.99  --prep_def_merge_mbd                    true
% 2.90/0.99  --prep_def_merge_tr_red                 false
% 2.90/0.99  --prep_def_merge_tr_cl                  false
% 2.90/0.99  --smt_preprocessing                     true
% 2.90/0.99  --smt_ac_axioms                         fast
% 2.90/0.99  --preprocessed_out                      false
% 2.90/0.99  --preprocessed_stats                    false
% 2.90/0.99  
% 2.90/0.99  ------ Abstraction refinement Options
% 2.90/0.99  
% 2.90/0.99  --abstr_ref                             []
% 2.90/0.99  --abstr_ref_prep                        false
% 2.90/0.99  --abstr_ref_until_sat                   false
% 2.90/0.99  --abstr_ref_sig_restrict                funpre
% 2.90/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.90/0.99  --abstr_ref_under                       []
% 2.90/0.99  
% 2.90/0.99  ------ SAT Options
% 2.90/0.99  
% 2.90/0.99  --sat_mode                              false
% 2.90/0.99  --sat_fm_restart_options                ""
% 2.90/0.99  --sat_gr_def                            false
% 2.90/0.99  --sat_epr_types                         true
% 2.90/0.99  --sat_non_cyclic_types                  false
% 2.90/0.99  --sat_finite_models                     false
% 2.90/0.99  --sat_fm_lemmas                         false
% 2.90/0.99  --sat_fm_prep                           false
% 2.90/0.99  --sat_fm_uc_incr                        true
% 2.90/0.99  --sat_out_model                         small
% 2.90/0.99  --sat_out_clauses                       false
% 2.90/0.99  
% 2.90/0.99  ------ QBF Options
% 2.90/0.99  
% 2.90/0.99  --qbf_mode                              false
% 2.90/0.99  --qbf_elim_univ                         false
% 2.90/0.99  --qbf_dom_inst                          none
% 2.90/0.99  --qbf_dom_pre_inst                      false
% 2.90/0.99  --qbf_sk_in                             false
% 2.90/0.99  --qbf_pred_elim                         true
% 2.90/0.99  --qbf_split                             512
% 2.90/0.99  
% 2.90/0.99  ------ BMC1 Options
% 2.90/0.99  
% 2.90/0.99  --bmc1_incremental                      false
% 2.90/0.99  --bmc1_axioms                           reachable_all
% 2.90/0.99  --bmc1_min_bound                        0
% 2.90/0.99  --bmc1_max_bound                        -1
% 2.90/0.99  --bmc1_max_bound_default                -1
% 2.90/0.99  --bmc1_symbol_reachability              true
% 2.90/0.99  --bmc1_property_lemmas                  false
% 2.90/0.99  --bmc1_k_induction                      false
% 2.90/0.99  --bmc1_non_equiv_states                 false
% 2.90/0.99  --bmc1_deadlock                         false
% 2.90/0.99  --bmc1_ucm                              false
% 2.90/0.99  --bmc1_add_unsat_core                   none
% 2.90/0.99  --bmc1_unsat_core_children              false
% 2.90/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.90/0.99  --bmc1_out_stat                         full
% 2.90/0.99  --bmc1_ground_init                      false
% 2.90/0.99  --bmc1_pre_inst_next_state              false
% 2.90/0.99  --bmc1_pre_inst_state                   false
% 2.90/0.99  --bmc1_pre_inst_reach_state             false
% 2.90/0.99  --bmc1_out_unsat_core                   false
% 2.90/0.99  --bmc1_aig_witness_out                  false
% 2.90/0.99  --bmc1_verbose                          false
% 2.90/0.99  --bmc1_dump_clauses_tptp                false
% 2.90/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.90/0.99  --bmc1_dump_file                        -
% 2.90/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.90/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.90/0.99  --bmc1_ucm_extend_mode                  1
% 2.90/0.99  --bmc1_ucm_init_mode                    2
% 2.90/0.99  --bmc1_ucm_cone_mode                    none
% 2.90/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.90/0.99  --bmc1_ucm_relax_model                  4
% 2.90/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.90/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.90/0.99  --bmc1_ucm_layered_model                none
% 2.90/0.99  --bmc1_ucm_max_lemma_size               10
% 2.90/0.99  
% 2.90/0.99  ------ AIG Options
% 2.90/0.99  
% 2.90/0.99  --aig_mode                              false
% 2.90/0.99  
% 2.90/0.99  ------ Instantiation Options
% 2.90/0.99  
% 2.90/0.99  --instantiation_flag                    true
% 2.90/0.99  --inst_sos_flag                         false
% 2.90/0.99  --inst_sos_phase                        true
% 2.90/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.90/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.90/0.99  --inst_lit_sel_side                     none
% 2.90/0.99  --inst_solver_per_active                1400
% 2.90/0.99  --inst_solver_calls_frac                1.
% 2.90/0.99  --inst_passive_queue_type               priority_queues
% 2.90/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.90/0.99  --inst_passive_queues_freq              [25;2]
% 2.90/0.99  --inst_dismatching                      true
% 2.90/0.99  --inst_eager_unprocessed_to_passive     true
% 2.90/0.99  --inst_prop_sim_given                   true
% 2.90/0.99  --inst_prop_sim_new                     false
% 2.90/0.99  --inst_subs_new                         false
% 2.90/0.99  --inst_eq_res_simp                      false
% 2.90/0.99  --inst_subs_given                       false
% 2.90/0.99  --inst_orphan_elimination               true
% 2.90/0.99  --inst_learning_loop_flag               true
% 2.90/0.99  --inst_learning_start                   3000
% 2.90/0.99  --inst_learning_factor                  2
% 2.90/0.99  --inst_start_prop_sim_after_learn       3
% 2.90/0.99  --inst_sel_renew                        solver
% 2.90/0.99  --inst_lit_activity_flag                true
% 2.90/0.99  --inst_restr_to_given                   false
% 2.90/0.99  --inst_activity_threshold               500
% 2.90/0.99  --inst_out_proof                        true
% 2.90/0.99  
% 2.90/0.99  ------ Resolution Options
% 2.90/0.99  
% 2.90/0.99  --resolution_flag                       false
% 2.90/0.99  --res_lit_sel                           adaptive
% 2.90/0.99  --res_lit_sel_side                      none
% 2.90/0.99  --res_ordering                          kbo
% 2.90/0.99  --res_to_prop_solver                    active
% 2.90/0.99  --res_prop_simpl_new                    false
% 2.90/0.99  --res_prop_simpl_given                  true
% 2.90/0.99  --res_passive_queue_type                priority_queues
% 2.90/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.90/0.99  --res_passive_queues_freq               [15;5]
% 2.90/0.99  --res_forward_subs                      full
% 2.90/0.99  --res_backward_subs                     full
% 2.90/0.99  --res_forward_subs_resolution           true
% 2.90/0.99  --res_backward_subs_resolution          true
% 2.90/0.99  --res_orphan_elimination                true
% 2.90/0.99  --res_time_limit                        2.
% 2.90/0.99  --res_out_proof                         true
% 2.90/0.99  
% 2.90/0.99  ------ Superposition Options
% 2.90/0.99  
% 2.90/0.99  --superposition_flag                    true
% 2.90/0.99  --sup_passive_queue_type                priority_queues
% 2.90/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.90/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.90/0.99  --demod_completeness_check              fast
% 2.90/0.99  --demod_use_ground                      true
% 2.90/0.99  --sup_to_prop_solver                    passive
% 2.90/0.99  --sup_prop_simpl_new                    true
% 2.90/0.99  --sup_prop_simpl_given                  true
% 2.90/0.99  --sup_fun_splitting                     false
% 2.90/0.99  --sup_smt_interval                      50000
% 2.90/0.99  
% 2.90/0.99  ------ Superposition Simplification Setup
% 2.90/0.99  
% 2.90/0.99  --sup_indices_passive                   []
% 2.90/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.90/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.90/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.90/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.90/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.90/0.99  --sup_full_bw                           [BwDemod]
% 2.90/0.99  --sup_immed_triv                        [TrivRules]
% 2.90/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.90/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.90/0.99  --sup_immed_bw_main                     []
% 2.90/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.90/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.90/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.90/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.90/0.99  
% 2.90/0.99  ------ Combination Options
% 2.90/0.99  
% 2.90/0.99  --comb_res_mult                         3
% 2.90/0.99  --comb_sup_mult                         2
% 2.90/0.99  --comb_inst_mult                        10
% 2.90/0.99  
% 2.90/0.99  ------ Debug Options
% 2.90/0.99  
% 2.90/0.99  --dbg_backtrace                         false
% 2.90/0.99  --dbg_dump_prop_clauses                 false
% 2.90/0.99  --dbg_dump_prop_clauses_file            -
% 2.90/0.99  --dbg_out_stat                          false
% 2.90/0.99  
% 2.90/0.99  
% 2.90/0.99  
% 2.90/0.99  
% 2.90/0.99  ------ Proving...
% 2.90/0.99  
% 2.90/0.99  
% 2.90/0.99  % SZS status Theorem for theBenchmark.p
% 2.90/0.99  
% 2.90/0.99   Resolution empty clause
% 2.90/0.99  
% 2.90/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.90/0.99  
% 2.90/0.99  fof(f18,axiom,(
% 2.90/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.90/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.90/0.99  
% 2.90/0.99  fof(f42,plain,(
% 2.90/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.90/0.99    inference(ennf_transformation,[],[f18])).
% 2.90/0.99  
% 2.90/0.99  fof(f43,plain,(
% 2.90/0.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.90/0.99    inference(flattening,[],[f42])).
% 2.90/0.99  
% 2.90/0.99  fof(f52,plain,(
% 2.90/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.90/0.99    inference(nnf_transformation,[],[f43])).
% 2.90/0.99  
% 2.90/0.99  fof(f80,plain,(
% 2.90/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.90/0.99    inference(cnf_transformation,[],[f52])).
% 2.90/0.99  
% 2.90/0.99  fof(f21,conjecture,(
% 2.90/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 2.90/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.90/0.99  
% 2.90/0.99  fof(f22,negated_conjecture,(
% 2.90/0.99    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 2.90/0.99    inference(negated_conjecture,[],[f21])).
% 2.90/0.99  
% 2.90/0.99  fof(f48,plain,(
% 2.90/0.99    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.90/0.99    inference(ennf_transformation,[],[f22])).
% 2.90/0.99  
% 2.90/0.99  fof(f49,plain,(
% 2.90/0.99    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.90/0.99    inference(flattening,[],[f48])).
% 2.90/0.99  
% 2.90/0.99  fof(f53,plain,(
% 2.90/0.99    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & k2_relset_1(sK0,sK1,sK2) = sK1 & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 2.90/0.99    introduced(choice_axiom,[])).
% 2.90/0.99  
% 2.90/0.99  fof(f54,plain,(
% 2.90/0.99    (~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & k2_relset_1(sK0,sK1,sK2) = sK1 & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 2.90/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f49,f53])).
% 2.90/0.99  
% 2.90/0.99  fof(f93,plain,(
% 2.90/0.99    v1_funct_2(sK2,sK0,sK1)),
% 2.90/0.99    inference(cnf_transformation,[],[f54])).
% 2.90/0.99  
% 2.90/0.99  fof(f94,plain,(
% 2.90/0.99    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.90/0.99    inference(cnf_transformation,[],[f54])).
% 2.90/0.99  
% 2.90/0.99  fof(f16,axiom,(
% 2.90/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.90/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.90/0.99  
% 2.90/0.99  fof(f40,plain,(
% 2.90/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.90/0.99    inference(ennf_transformation,[],[f16])).
% 2.90/0.99  
% 2.90/0.99  fof(f78,plain,(
% 2.90/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.90/0.99    inference(cnf_transformation,[],[f40])).
% 2.90/0.99  
% 2.90/0.99  fof(f15,axiom,(
% 2.90/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.90/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.90/0.99  
% 2.90/0.99  fof(f39,plain,(
% 2.90/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.90/0.99    inference(ennf_transformation,[],[f15])).
% 2.90/0.99  
% 2.90/0.99  fof(f77,plain,(
% 2.90/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.90/0.99    inference(cnf_transformation,[],[f39])).
% 2.90/0.99  
% 2.90/0.99  fof(f13,axiom,(
% 2.90/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 2.90/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.90/0.99  
% 2.90/0.99  fof(f37,plain,(
% 2.90/0.99    ! [X0] : (((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.90/0.99    inference(ennf_transformation,[],[f13])).
% 2.90/0.99  
% 2.90/0.99  fof(f38,plain,(
% 2.90/0.99    ! [X0] : ((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.90/0.99    inference(flattening,[],[f37])).
% 2.90/0.99  
% 2.90/0.99  fof(f74,plain,(
% 2.90/0.99    ( ! [X0] : (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.90/0.99    inference(cnf_transformation,[],[f38])).
% 2.90/0.99  
% 2.90/0.99  fof(f95,plain,(
% 2.90/0.99    v2_funct_1(sK2)),
% 2.90/0.99    inference(cnf_transformation,[],[f54])).
% 2.90/0.99  
% 2.90/0.99  fof(f92,plain,(
% 2.90/0.99    v1_funct_1(sK2)),
% 2.90/0.99    inference(cnf_transformation,[],[f54])).
% 2.90/0.99  
% 2.90/0.99  fof(f11,axiom,(
% 2.90/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 2.90/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.90/0.99  
% 2.90/0.99  fof(f33,plain,(
% 2.90/0.99    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.90/0.99    inference(ennf_transformation,[],[f11])).
% 2.90/0.99  
% 2.90/0.99  fof(f34,plain,(
% 2.90/0.99    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.90/0.99    inference(flattening,[],[f33])).
% 2.90/0.99  
% 2.90/0.99  fof(f70,plain,(
% 2.90/0.99    ( ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.90/0.99    inference(cnf_transformation,[],[f34])).
% 2.90/0.99  
% 2.90/0.99  fof(f84,plain,(
% 2.90/0.99    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.90/0.99    inference(cnf_transformation,[],[f52])).
% 2.90/0.99  
% 2.90/0.99  fof(f100,plain,(
% 2.90/0.99    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 2.90/0.99    inference(equality_resolution,[],[f84])).
% 2.90/0.99  
% 2.90/0.99  fof(f19,axiom,(
% 2.90/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 2.90/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.90/0.99  
% 2.90/0.99  fof(f44,plain,(
% 2.90/0.99    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.90/0.99    inference(ennf_transformation,[],[f19])).
% 2.90/0.99  
% 2.90/0.99  fof(f45,plain,(
% 2.90/0.99    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.90/0.99    inference(flattening,[],[f44])).
% 2.90/0.99  
% 2.90/0.99  fof(f87,plain,(
% 2.90/0.99    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.90/0.99    inference(cnf_transformation,[],[f45])).
% 2.90/0.99  
% 2.90/0.99  fof(f73,plain,(
% 2.90/0.99    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.90/0.99    inference(cnf_transformation,[],[f38])).
% 2.90/0.99  
% 2.90/0.99  fof(f17,axiom,(
% 2.90/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.90/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.90/0.99  
% 2.90/0.99  fof(f41,plain,(
% 2.90/0.99    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.90/0.99    inference(ennf_transformation,[],[f17])).
% 2.90/0.99  
% 2.90/0.99  fof(f79,plain,(
% 2.90/0.99    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.90/0.99    inference(cnf_transformation,[],[f41])).
% 2.90/0.99  
% 2.90/0.99  fof(f96,plain,(
% 2.90/0.99    k2_relset_1(sK0,sK1,sK2) = sK1),
% 2.90/0.99    inference(cnf_transformation,[],[f54])).
% 2.90/0.99  
% 2.90/0.99  fof(f2,axiom,(
% 2.90/0.99    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 2.90/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.90/0.99  
% 2.90/0.99  fof(f25,plain,(
% 2.90/0.99    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 2.90/0.99    inference(ennf_transformation,[],[f2])).
% 2.90/0.99  
% 2.90/0.99  fof(f56,plain,(
% 2.90/0.99    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 2.90/0.99    inference(cnf_transformation,[],[f25])).
% 2.90/0.99  
% 2.90/0.99  fof(f1,axiom,(
% 2.90/0.99    v1_xboole_0(k1_xboole_0)),
% 2.90/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.90/0.99  
% 2.90/0.99  fof(f55,plain,(
% 2.90/0.99    v1_xboole_0(k1_xboole_0)),
% 2.90/0.99    inference(cnf_transformation,[],[f1])).
% 2.90/0.99  
% 2.90/0.99  fof(f3,axiom,(
% 2.90/0.99    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.90/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.90/0.99  
% 2.90/0.99  fof(f57,plain,(
% 2.90/0.99    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.90/0.99    inference(cnf_transformation,[],[f3])).
% 2.90/0.99  
% 2.90/0.99  fof(f20,axiom,(
% 2.90/0.99    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 2.90/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.90/0.99  
% 2.90/0.99  fof(f46,plain,(
% 2.90/0.99    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.90/0.99    inference(ennf_transformation,[],[f20])).
% 2.90/0.99  
% 2.90/0.99  fof(f47,plain,(
% 2.90/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.90/0.99    inference(flattening,[],[f46])).
% 2.90/0.99  
% 2.90/0.99  fof(f90,plain,(
% 2.90/0.99    ( ! [X0,X1] : (v1_funct_2(X1,k1_relat_1(X1),X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.90/0.99    inference(cnf_transformation,[],[f47])).
% 2.90/0.99  
% 2.90/0.99  fof(f97,plain,(
% 2.90/0.99    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))),
% 2.90/0.99    inference(cnf_transformation,[],[f54])).
% 2.90/0.99  
% 2.90/0.99  fof(f12,axiom,(
% 2.90/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 2.90/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.90/0.99  
% 2.90/0.99  fof(f35,plain,(
% 2.90/0.99    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.90/0.99    inference(ennf_transformation,[],[f12])).
% 2.90/0.99  
% 2.90/0.99  fof(f36,plain,(
% 2.90/0.99    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.90/0.99    inference(flattening,[],[f35])).
% 2.90/0.99  
% 2.90/0.99  fof(f72,plain,(
% 2.90/0.99    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.90/0.99    inference(cnf_transformation,[],[f36])).
% 2.90/0.99  
% 2.90/0.99  fof(f71,plain,(
% 2.90/0.99    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.90/0.99    inference(cnf_transformation,[],[f36])).
% 2.90/0.99  
% 2.90/0.99  fof(f7,axiom,(
% 2.90/0.99    ! [X0] : ((v1_relat_1(X0) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k2_relat_1(X0)))),
% 2.90/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.90/0.99  
% 2.90/0.99  fof(f28,plain,(
% 2.90/0.99    ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | (~v1_relat_1(X0) | v1_xboole_0(X0)))),
% 2.90/0.99    inference(ennf_transformation,[],[f7])).
% 2.90/0.99  
% 2.90/0.99  fof(f29,plain,(
% 2.90/0.99    ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0))),
% 2.90/0.99    inference(flattening,[],[f28])).
% 2.90/0.99  
% 2.90/0.99  fof(f63,plain,(
% 2.90/0.99    ( ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0)) )),
% 2.90/0.99    inference(cnf_transformation,[],[f29])).
% 2.90/0.99  
% 2.90/0.99  fof(f4,axiom,(
% 2.90/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.90/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.90/0.99  
% 2.90/0.99  fof(f50,plain,(
% 2.90/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.90/0.99    inference(nnf_transformation,[],[f4])).
% 2.90/0.99  
% 2.90/0.99  fof(f59,plain,(
% 2.90/0.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.90/0.99    inference(cnf_transformation,[],[f50])).
% 2.90/0.99  
% 2.90/0.99  fof(f88,plain,(
% 2.90/0.99    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.90/0.99    inference(cnf_transformation,[],[f45])).
% 2.90/0.99  
% 2.90/0.99  fof(f82,plain,(
% 2.90/0.99    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.90/0.99    inference(cnf_transformation,[],[f52])).
% 2.90/0.99  
% 2.90/0.99  fof(f8,axiom,(
% 2.90/0.99    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.90/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.90/0.99  
% 2.90/0.99  fof(f64,plain,(
% 2.90/0.99    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.90/0.99    inference(cnf_transformation,[],[f8])).
% 2.90/0.99  
% 2.90/0.99  cnf(c_30,plain,
% 2.90/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.90/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.90/0.99      | k1_relset_1(X1,X2,X0) = X1
% 2.90/0.99      | k1_xboole_0 = X2 ),
% 2.90/0.99      inference(cnf_transformation,[],[f80]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_41,negated_conjecture,
% 2.90/0.99      ( v1_funct_2(sK2,sK0,sK1) ),
% 2.90/0.99      inference(cnf_transformation,[],[f93]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_958,plain,
% 2.90/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.90/0.99      | k1_relset_1(X1,X2,X0) = X1
% 2.90/0.99      | sK0 != X1
% 2.90/0.99      | sK1 != X2
% 2.90/0.99      | sK2 != X0
% 2.90/0.99      | k1_xboole_0 = X2 ),
% 2.90/0.99      inference(resolution_lifted,[status(thm)],[c_30,c_41]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_959,plain,
% 2.90/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 2.90/0.99      | k1_relset_1(sK0,sK1,sK2) = sK0
% 2.90/0.99      | k1_xboole_0 = sK1 ),
% 2.90/0.99      inference(unflattening,[status(thm)],[c_958]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_40,negated_conjecture,
% 2.90/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 2.90/0.99      inference(cnf_transformation,[],[f94]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_961,plain,
% 2.90/0.99      ( k1_relset_1(sK0,sK1,sK2) = sK0 | k1_xboole_0 = sK1 ),
% 2.90/0.99      inference(global_propositional_subsumption,[status(thm)],[c_959,c_40]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_2264,plain,
% 2.90/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 2.90/0.99      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_23,plain,
% 2.90/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.90/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.90/0.99      inference(cnf_transformation,[],[f78]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_2268,plain,
% 2.90/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.90/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.90/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_4372,plain,
% 2.90/0.99      ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
% 2.90/0.99      inference(superposition,[status(thm)],[c_2264,c_2268]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_4457,plain,
% 2.90/0.99      ( k1_relat_1(sK2) = sK0 | sK1 = k1_xboole_0 ),
% 2.90/0.99      inference(superposition,[status(thm)],[c_961,c_4372]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_22,plain,
% 2.90/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 2.90/0.99      inference(cnf_transformation,[],[f77]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_2269,plain,
% 2.90/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.90/0.99      | v1_relat_1(X0) = iProver_top ),
% 2.90/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_3764,plain,
% 2.90/0.99      ( v1_relat_1(sK2) = iProver_top ),
% 2.90/0.99      inference(superposition,[status(thm)],[c_2264,c_2269]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_18,plain,
% 2.90/0.99      ( ~ v2_funct_1(X0)
% 2.90/0.99      | ~ v1_funct_1(X0)
% 2.90/0.99      | ~ v1_relat_1(X0)
% 2.90/0.99      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 2.90/0.99      inference(cnf_transformation,[],[f74]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_39,negated_conjecture,
% 2.90/0.99      ( v2_funct_1(sK2) ),
% 2.90/0.99      inference(cnf_transformation,[],[f95]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_661,plain,
% 2.90/0.99      ( ~ v1_funct_1(X0)
% 2.90/0.99      | ~ v1_relat_1(X0)
% 2.90/0.99      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 2.90/0.99      | sK2 != X0 ),
% 2.90/0.99      inference(resolution_lifted,[status(thm)],[c_18,c_39]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_662,plain,
% 2.90/0.99      ( ~ v1_funct_1(sK2)
% 2.90/0.99      | ~ v1_relat_1(sK2)
% 2.90/0.99      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.90/0.99      inference(unflattening,[status(thm)],[c_661]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_42,negated_conjecture,
% 2.90/0.99      ( v1_funct_1(sK2) ),
% 2.90/0.99      inference(cnf_transformation,[],[f92]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_664,plain,
% 2.90/0.99      ( ~ v1_relat_1(sK2) | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.90/0.99      inference(global_propositional_subsumption,[status(thm)],[c_662,c_42]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_2258,plain,
% 2.90/0.99      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 2.90/0.99      | v1_relat_1(sK2) != iProver_top ),
% 2.90/0.99      inference(predicate_to_equality,[status(thm)],[c_664]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_3824,plain,
% 2.90/0.99      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.90/0.99      inference(superposition,[status(thm)],[c_3764,c_2258]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_15,plain,
% 2.90/0.99      ( ~ v2_funct_1(X0)
% 2.90/0.99      | ~ v1_funct_1(X0)
% 2.90/0.99      | ~ v1_relat_1(X0)
% 2.90/0.99      | k2_funct_1(X0) = k4_relat_1(X0) ),
% 2.90/0.99      inference(cnf_transformation,[],[f70]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_675,plain,
% 2.90/0.99      ( ~ v1_funct_1(X0)
% 2.90/0.99      | ~ v1_relat_1(X0)
% 2.90/0.99      | k2_funct_1(X0) = k4_relat_1(X0)
% 2.90/0.99      | sK2 != X0 ),
% 2.90/0.99      inference(resolution_lifted,[status(thm)],[c_15,c_39]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_676,plain,
% 2.90/0.99      ( ~ v1_funct_1(sK2)
% 2.90/0.99      | ~ v1_relat_1(sK2)
% 2.90/0.99      | k2_funct_1(sK2) = k4_relat_1(sK2) ),
% 2.90/0.99      inference(unflattening,[status(thm)],[c_675]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_678,plain,
% 2.90/0.99      ( ~ v1_relat_1(sK2) | k2_funct_1(sK2) = k4_relat_1(sK2) ),
% 2.90/0.99      inference(global_propositional_subsumption,[status(thm)],[c_676,c_42]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_2257,plain,
% 2.90/0.99      ( k2_funct_1(sK2) = k4_relat_1(sK2) | v1_relat_1(sK2) != iProver_top ),
% 2.90/0.99      inference(predicate_to_equality,[status(thm)],[c_678]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_3825,plain,
% 2.90/0.99      ( k2_funct_1(sK2) = k4_relat_1(sK2) ),
% 2.90/0.99      inference(superposition,[status(thm)],[c_3764,c_2257]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_3828,plain,
% 2.90/0.99      ( k2_relat_1(k4_relat_1(sK2)) = k1_relat_1(sK2) ),
% 2.90/0.99      inference(light_normalisation,[status(thm)],[c_3824,c_3825]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_26,plain,
% 2.90/0.99      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 2.90/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 2.90/0.99      | k1_xboole_0 = X1
% 2.90/0.99      | k1_xboole_0 = X0 ),
% 2.90/0.99      inference(cnf_transformation,[],[f100]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_32,plain,
% 2.90/0.99      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
% 2.90/0.99      | ~ v1_funct_1(X0)
% 2.90/0.99      | ~ v1_relat_1(X0) ),
% 2.90/0.99      inference(cnf_transformation,[],[f87]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_738,plain,
% 2.90/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 2.90/0.99      | ~ v1_funct_1(X2)
% 2.90/0.99      | ~ v1_relat_1(X2)
% 2.90/0.99      | X2 != X0
% 2.90/0.99      | k1_relat_1(X2) != X1
% 2.90/0.99      | k2_relat_1(X2) != k1_xboole_0
% 2.90/0.99      | k1_xboole_0 = X0
% 2.90/0.99      | k1_xboole_0 = X1 ),
% 2.90/0.99      inference(resolution_lifted,[status(thm)],[c_26,c_32]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_739,plain,
% 2.90/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k1_xboole_0)))
% 2.90/0.99      | ~ v1_funct_1(X0)
% 2.90/0.99      | ~ v1_relat_1(X0)
% 2.90/0.99      | k2_relat_1(X0) != k1_xboole_0
% 2.90/0.99      | k1_xboole_0 = X0
% 2.90/0.99      | k1_xboole_0 = k1_relat_1(X0) ),
% 2.90/0.99      inference(unflattening,[status(thm)],[c_738]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_755,plain,
% 2.90/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k1_xboole_0)))
% 2.90/0.99      | ~ v1_funct_1(X0)
% 2.90/0.99      | k2_relat_1(X0) != k1_xboole_0
% 2.90/0.99      | k1_xboole_0 = X0
% 2.90/0.99      | k1_xboole_0 = k1_relat_1(X0) ),
% 2.90/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_739,c_22]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_2255,plain,
% 2.90/0.99      ( k2_relat_1(X0) != k1_xboole_0
% 2.90/0.99      | k1_xboole_0 = X0
% 2.90/0.99      | k1_xboole_0 = k1_relat_1(X0)
% 2.90/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k1_xboole_0))) != iProver_top
% 2.90/0.99      | v1_funct_1(X0) != iProver_top ),
% 2.90/0.99      inference(predicate_to_equality,[status(thm)],[c_755]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_6415,plain,
% 2.90/0.99      ( k1_relat_1(k4_relat_1(sK2)) = k1_xboole_0
% 2.90/0.99      | k1_relat_1(sK2) != k1_xboole_0
% 2.90/0.99      | k4_relat_1(sK2) = k1_xboole_0
% 2.90/0.99      | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k4_relat_1(sK2)),k1_xboole_0))) != iProver_top
% 2.90/0.99      | v1_funct_1(k4_relat_1(sK2)) != iProver_top ),
% 2.90/0.99      inference(superposition,[status(thm)],[c_3828,c_2255]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_19,plain,
% 2.90/0.99      ( ~ v2_funct_1(X0)
% 2.90/0.99      | ~ v1_funct_1(X0)
% 2.90/0.99      | ~ v1_relat_1(X0)
% 2.90/0.99      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 2.90/0.99      inference(cnf_transformation,[],[f73]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_647,plain,
% 2.90/0.99      ( ~ v1_funct_1(X0)
% 2.90/0.99      | ~ v1_relat_1(X0)
% 2.90/0.99      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 2.90/0.99      | sK2 != X0 ),
% 2.90/0.99      inference(resolution_lifted,[status(thm)],[c_19,c_39]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_648,plain,
% 2.90/0.99      ( ~ v1_funct_1(sK2)
% 2.90/0.99      | ~ v1_relat_1(sK2)
% 2.90/0.99      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 2.90/0.99      inference(unflattening,[status(thm)],[c_647]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_650,plain,
% 2.90/0.99      ( ~ v1_relat_1(sK2) | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 2.90/0.99      inference(global_propositional_subsumption,[status(thm)],[c_648,c_42]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_2259,plain,
% 2.90/0.99      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
% 2.90/0.99      | v1_relat_1(sK2) != iProver_top ),
% 2.90/0.99      inference(predicate_to_equality,[status(thm)],[c_650]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_3823,plain,
% 2.90/0.99      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 2.90/0.99      inference(superposition,[status(thm)],[c_3764,c_2259]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_3831,plain,
% 2.90/0.99      ( k1_relat_1(k4_relat_1(sK2)) = k2_relat_1(sK2) ),
% 2.90/0.99      inference(light_normalisation,[status(thm)],[c_3823,c_3825]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_24,plain,
% 2.90/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.90/0.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.90/0.99      inference(cnf_transformation,[],[f79]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_2267,plain,
% 2.90/0.99      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 2.90/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.90/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_4275,plain,
% 2.90/0.99      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 2.90/0.99      inference(superposition,[status(thm)],[c_2264,c_2267]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_38,negated_conjecture,
% 2.90/0.99      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 2.90/0.99      inference(cnf_transformation,[],[f96]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_4277,plain,
% 2.90/0.99      ( k2_relat_1(sK2) = sK1 ),
% 2.90/0.99      inference(light_normalisation,[status(thm)],[c_4275,c_38]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_4753,plain,
% 2.90/0.99      ( k1_relat_1(k4_relat_1(sK2)) = sK1 ),
% 2.90/0.99      inference(light_normalisation,[status(thm)],[c_3831,c_4277]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_6421,plain,
% 2.90/0.99      ( k1_relat_1(k4_relat_1(sK2)) = k1_xboole_0
% 2.90/0.99      | k1_relat_1(sK2) != k1_xboole_0
% 2.90/0.99      | k4_relat_1(sK2) = k1_xboole_0
% 2.90/0.99      | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) != iProver_top
% 2.90/0.99      | v1_funct_1(k4_relat_1(sK2)) != iProver_top ),
% 2.90/0.99      inference(light_normalisation,[status(thm)],[c_6415,c_4753]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_6422,plain,
% 2.90/0.99      ( k1_relat_1(sK2) != k1_xboole_0
% 2.90/0.99      | k4_relat_1(sK2) = k1_xboole_0
% 2.90/0.99      | sK1 = k1_xboole_0
% 2.90/0.99      | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) != iProver_top
% 2.90/0.99      | v1_funct_1(k4_relat_1(sK2)) != iProver_top ),
% 2.90/0.99      inference(demodulation,[status(thm)],[c_6421,c_4753]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_1,plain,
% 2.90/0.99      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 2.90/0.99      inference(cnf_transformation,[],[f56]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_132,plain,
% 2.90/0.99      ( ~ v1_xboole_0(k1_xboole_0) | k1_xboole_0 = k1_xboole_0 ),
% 2.90/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_0,plain,
% 2.90/0.99      ( v1_xboole_0(k1_xboole_0) ),
% 2.90/0.99      inference(cnf_transformation,[],[f55]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_2,plain,
% 2.90/0.99      ( r1_tarski(k1_xboole_0,X0) ),
% 2.90/0.99      inference(cnf_transformation,[],[f57]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_35,plain,
% 2.90/0.99      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 2.90/0.99      | ~ r1_tarski(k2_relat_1(X0),X1)
% 2.90/0.99      | ~ v1_funct_1(X0)
% 2.90/0.99      | ~ v1_relat_1(X0) ),
% 2.90/0.99      inference(cnf_transformation,[],[f90]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_37,negated_conjecture,
% 2.90/0.99      ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
% 2.90/0.99      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.90/0.99      | ~ v1_funct_1(k2_funct_1(sK2)) ),
% 2.90/0.99      inference(cnf_transformation,[],[f97]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_988,plain,
% 2.90/0.99      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.90/0.99      | ~ r1_tarski(k2_relat_1(X0),X1)
% 2.90/0.99      | ~ v1_funct_1(X0)
% 2.90/0.99      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.90/0.99      | ~ v1_relat_1(X0)
% 2.90/0.99      | k2_funct_1(sK2) != X0
% 2.90/0.99      | k1_relat_1(X0) != sK1
% 2.90/0.99      | sK0 != X1 ),
% 2.90/0.99      inference(resolution_lifted,[status(thm)],[c_35,c_37]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_989,plain,
% 2.90/0.99      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.90/0.99      | ~ r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0)
% 2.90/0.99      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.90/0.99      | ~ v1_relat_1(k2_funct_1(sK2))
% 2.90/0.99      | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
% 2.90/0.99      inference(unflattening,[status(thm)],[c_988]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_1001,plain,
% 2.90/0.99      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.90/0.99      | ~ r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0)
% 2.90/0.99      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.90/0.99      | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
% 2.90/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_989,c_22]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_1184,plain,
% 2.90/0.99      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.90/0.99      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.90/0.99      | k1_relat_1(k2_funct_1(sK2)) != sK1
% 2.90/0.99      | k2_relat_1(k2_funct_1(sK2)) != k1_xboole_0
% 2.90/0.99      | sK0 != X0 ),
% 2.90/0.99      inference(resolution_lifted,[status(thm)],[c_2,c_1001]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_1185,plain,
% 2.90/0.99      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.90/0.99      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.90/0.99      | k1_relat_1(k2_funct_1(sK2)) != sK1
% 2.90/0.99      | k2_relat_1(k2_funct_1(sK2)) != k1_xboole_0 ),
% 2.90/0.99      inference(unflattening,[status(thm)],[c_1184]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_16,plain,
% 2.90/0.99      ( ~ v1_funct_1(X0) | v1_funct_1(k2_funct_1(X0)) | ~ v1_relat_1(X0) ),
% 2.90/0.99      inference(cnf_transformation,[],[f72]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_2621,plain,
% 2.90/0.99      ( v1_funct_1(k2_funct_1(sK2)) | ~ v1_funct_1(sK2) | ~ v1_relat_1(sK2) ),
% 2.90/0.99      inference(instantiation,[status(thm)],[c_16]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_2630,plain,
% 2.90/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(sK2) ),
% 2.90/0.99      inference(instantiation,[status(thm)],[c_22]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_2757,plain,
% 2.90/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 2.90/0.99      | v1_relat_1(sK2) ),
% 2.90/0.99      inference(instantiation,[status(thm)],[c_2630]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_1341,plain,( X0 = X0 ),theory(equality) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_2791,plain,
% 2.90/0.99      ( sK1 = sK1 ),
% 2.90/0.99      inference(instantiation,[status(thm)],[c_1341]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_1342,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_2908,plain,
% 2.90/0.99      ( k1_relat_1(k2_funct_1(sK2)) != X0
% 2.90/0.99      | k1_relat_1(k2_funct_1(sK2)) = sK1
% 2.90/0.99      | sK1 != X0 ),
% 2.90/0.99      inference(instantiation,[status(thm)],[c_1342]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_3024,plain,
% 2.90/0.99      ( k1_relat_1(k2_funct_1(sK2)) != k2_relat_1(sK2)
% 2.90/0.99      | k1_relat_1(k2_funct_1(sK2)) = sK1
% 2.90/0.99      | sK1 != k2_relat_1(sK2) ),
% 2.90/0.99      inference(instantiation,[status(thm)],[c_2908]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_2769,plain,
% 2.90/0.99      ( X0 != X1 | k2_funct_1(sK2) != X1 | k2_funct_1(sK2) = X0 ),
% 2.90/0.99      inference(instantiation,[status(thm)],[c_1342]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_3047,plain,
% 2.90/0.99      ( X0 != k4_relat_1(sK2)
% 2.90/0.99      | k2_funct_1(sK2) = X0
% 2.90/0.99      | k2_funct_1(sK2) != k4_relat_1(sK2) ),
% 2.90/0.99      inference(instantiation,[status(thm)],[c_2769]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_3048,plain,
% 2.90/0.99      ( k2_funct_1(sK2) != k4_relat_1(sK2)
% 2.90/0.99      | k2_funct_1(sK2) = k1_xboole_0
% 2.90/0.99      | k1_xboole_0 != k4_relat_1(sK2) ),
% 2.90/0.99      inference(instantiation,[status(thm)],[c_3047]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_1346,plain,
% 2.90/0.99      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.90/0.99      theory(equality) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_2707,plain,
% 2.90/0.99      ( m1_subset_1(X0,X1)
% 2.90/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
% 2.90/0.99      | X0 != X2
% 2.90/0.99      | X1 != k1_zfmisc_1(X3) ),
% 2.90/0.99      inference(instantiation,[status(thm)],[c_1346]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_2881,plain,
% 2.90/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.90/0.99      | m1_subset_1(X2,k1_zfmisc_1(X1))
% 2.90/0.99      | X2 != X0
% 2.90/0.99      | k1_zfmisc_1(X1) != k1_zfmisc_1(X1) ),
% 2.90/0.99      inference(instantiation,[status(thm)],[c_2707]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_3239,plain,
% 2.90/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.90/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.90/0.99      | k2_funct_1(sK2) != X0
% 2.90/0.99      | k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
% 2.90/0.99      inference(instantiation,[status(thm)],[c_2881]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_3241,plain,
% 2.90/0.99      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.90/0.99      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.90/0.99      | k2_funct_1(sK2) != k1_xboole_0
% 2.90/0.99      | k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
% 2.90/0.99      inference(instantiation,[status(thm)],[c_3239]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_3339,plain,
% 2.90/0.99      ( ~ v1_xboole_0(k4_relat_1(sK2)) | k1_xboole_0 = k4_relat_1(sK2) ),
% 2.90/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_2882,plain,
% 2.90/0.99      ( k1_zfmisc_1(X0) = k1_zfmisc_1(X0) ),
% 2.90/0.99      inference(instantiation,[status(thm)],[c_1341]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_3362,plain,
% 2.90/0.99      ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) = k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
% 2.90/0.99      inference(instantiation,[status(thm)],[c_2882]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_2792,plain,
% 2.90/0.99      ( X0 != X1 | sK1 != X1 | sK1 = X0 ),
% 2.90/0.99      inference(instantiation,[status(thm)],[c_1342]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_3500,plain,
% 2.90/0.99      ( k2_relat_1(sK2) != X0 | sK1 != X0 | sK1 = k2_relat_1(sK2) ),
% 2.90/0.99      inference(instantiation,[status(thm)],[c_2792]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_4146,plain,
% 2.90/0.99      ( k2_relat_1(sK2) != sK1 | sK1 = k2_relat_1(sK2) | sK1 != sK1 ),
% 2.90/0.99      inference(instantiation,[status(thm)],[c_3500]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_17,plain,
% 2.90/0.99      ( ~ v1_funct_1(X0) | ~ v1_relat_1(X0) | v1_relat_1(k2_funct_1(X0)) ),
% 2.90/0.99      inference(cnf_transformation,[],[f71]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_2272,plain,
% 2.90/0.99      ( v1_funct_1(X0) != iProver_top
% 2.90/0.99      | v1_relat_1(X0) != iProver_top
% 2.90/0.99      | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
% 2.90/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_4447,plain,
% 2.90/0.99      ( v1_funct_1(sK2) != iProver_top
% 2.90/0.99      | v1_relat_1(k4_relat_1(sK2)) = iProver_top
% 2.90/0.99      | v1_relat_1(sK2) != iProver_top ),
% 2.90/0.99      inference(superposition,[status(thm)],[c_3825,c_2272]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_4455,plain,
% 2.90/0.99      ( ~ v1_funct_1(sK2) | v1_relat_1(k4_relat_1(sK2)) | ~ v1_relat_1(sK2) ),
% 2.90/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_4447]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_8,plain,
% 2.90/0.99      ( ~ v1_relat_1(X0) | v1_xboole_0(X0) | ~ v1_xboole_0(k2_relat_1(X0)) ),
% 2.90/0.99      inference(cnf_transformation,[],[f63]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_2275,plain,
% 2.90/0.99      ( v1_relat_1(X0) != iProver_top
% 2.90/0.99      | v1_xboole_0(X0) = iProver_top
% 2.90/0.99      | v1_xboole_0(k2_relat_1(X0)) != iProver_top ),
% 2.90/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_4943,plain,
% 2.90/0.99      ( v1_relat_1(k4_relat_1(sK2)) != iProver_top
% 2.90/0.99      | v1_xboole_0(k1_relat_1(sK2)) != iProver_top
% 2.90/0.99      | v1_xboole_0(k4_relat_1(sK2)) = iProver_top ),
% 2.90/0.99      inference(superposition,[status(thm)],[c_3828,c_2275]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_4957,plain,
% 2.90/0.99      ( ~ v1_relat_1(k4_relat_1(sK2))
% 2.90/0.99      | ~ v1_xboole_0(k1_relat_1(sK2))
% 2.90/0.99      | v1_xboole_0(k4_relat_1(sK2)) ),
% 2.90/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_4943]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_3,plain,
% 2.90/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.90/0.99      inference(cnf_transformation,[],[f59]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_2659,plain,
% 2.90/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.90/0.99      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ),
% 2.90/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_5288,plain,
% 2.90/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.90/0.99      | ~ r1_tarski(X0,k2_zfmisc_1(sK1,sK0)) ),
% 2.90/0.99      inference(instantiation,[status(thm)],[c_2659]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_5290,plain,
% 2.90/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.90/0.99      | ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(sK1,sK0)) ),
% 2.90/0.99      inference(instantiation,[status(thm)],[c_5288]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_1343,plain,
% 2.90/0.99      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 2.90/0.99      theory(equality) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_5445,plain,
% 2.90/0.99      ( ~ v1_xboole_0(X0)
% 2.90/0.99      | v1_xboole_0(k1_relat_1(sK2))
% 2.90/0.99      | k1_relat_1(sK2) != X0 ),
% 2.90/0.99      inference(instantiation,[status(thm)],[c_1343]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_5447,plain,
% 2.90/0.99      ( v1_xboole_0(k1_relat_1(sK2))
% 2.90/0.99      | ~ v1_xboole_0(k1_xboole_0)
% 2.90/0.99      | k1_relat_1(sK2) != k1_xboole_0 ),
% 2.90/0.99      inference(instantiation,[status(thm)],[c_5445]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_4121,plain,
% 2.90/0.99      ( X0 != X1
% 2.90/0.99      | k2_relat_1(k2_funct_1(sK2)) != X1
% 2.90/0.99      | k2_relat_1(k2_funct_1(sK2)) = X0 ),
% 2.90/0.99      inference(instantiation,[status(thm)],[c_1342]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_5685,plain,
% 2.90/0.99      ( X0 != k1_relat_1(sK2)
% 2.90/0.99      | k2_relat_1(k2_funct_1(sK2)) = X0
% 2.90/0.99      | k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2) ),
% 2.90/0.99      inference(instantiation,[status(thm)],[c_4121]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_5686,plain,
% 2.90/0.99      ( k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2)
% 2.90/0.99      | k2_relat_1(k2_funct_1(sK2)) = k1_xboole_0
% 2.90/0.99      | k1_xboole_0 != k1_relat_1(sK2) ),
% 2.90/0.99      inference(instantiation,[status(thm)],[c_5685]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_5938,plain,
% 2.90/0.99      ( X0 != X1 | X0 = k1_relat_1(sK2) | k1_relat_1(sK2) != X1 ),
% 2.90/0.99      inference(instantiation,[status(thm)],[c_1342]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_5939,plain,
% 2.90/0.99      ( k1_relat_1(sK2) != k1_xboole_0
% 2.90/0.99      | k1_xboole_0 = k1_relat_1(sK2)
% 2.90/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 2.90/0.99      inference(instantiation,[status(thm)],[c_5938]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_2816,plain,
% 2.90/0.99      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,X1)) ),
% 2.90/0.99      inference(instantiation,[status(thm)],[c_2]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_6629,plain,
% 2.90/0.99      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(sK1,sK0)) ),
% 2.90/0.99      inference(instantiation,[status(thm)],[c_2816]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_6655,plain,
% 2.90/0.99      ( k1_relat_1(sK2) != k1_xboole_0 ),
% 2.90/0.99      inference(global_propositional_subsumption,
% 2.90/0.99                [status(thm)],
% 2.90/0.99                [c_6422,c_42,c_40,c_132,c_0,c_648,c_662,c_676,c_1185,c_2621,
% 2.90/0.99                 c_2757,c_2791,c_3024,c_3048,c_3241,c_3339,c_3362,c_4146,
% 2.90/0.99                 c_4277,c_4455,c_4957,c_5290,c_5447,c_5686,c_5939,c_6629]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_6658,plain,
% 2.90/0.99      ( sK0 != k1_xboole_0 | sK1 = k1_xboole_0 ),
% 2.90/0.99      inference(superposition,[status(thm)],[c_4457,c_6655]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_31,plain,
% 2.90/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 2.90/0.99      | ~ v1_funct_1(X0)
% 2.90/0.99      | ~ v1_relat_1(X0) ),
% 2.90/0.99      inference(cnf_transformation,[],[f88]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_2266,plain,
% 2.90/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
% 2.90/0.99      | v1_funct_1(X0) != iProver_top
% 2.90/0.99      | v1_relat_1(X0) != iProver_top ),
% 2.90/0.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_4982,plain,
% 2.90/0.99      ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k4_relat_1(sK2)),k1_relat_1(sK2)))) = iProver_top
% 2.90/0.99      | v1_funct_1(k4_relat_1(sK2)) != iProver_top
% 2.90/0.99      | v1_relat_1(k4_relat_1(sK2)) != iProver_top ),
% 2.90/0.99      inference(superposition,[status(thm)],[c_3828,c_2266]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_5002,plain,
% 2.90/0.99      ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) = iProver_top
% 2.90/0.99      | v1_funct_1(k4_relat_1(sK2)) != iProver_top
% 2.90/0.99      | v1_relat_1(k4_relat_1(sK2)) != iProver_top ),
% 2.90/0.99      inference(light_normalisation,[status(thm)],[c_4982,c_4753]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_43,plain,
% 2.90/0.99      ( v1_funct_1(sK2) = iProver_top ),
% 2.90/0.99      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_45,plain,
% 2.90/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 2.90/0.99      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_2758,plain,
% 2.90/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 2.90/0.99      | v1_relat_1(sK2) = iProver_top ),
% 2.90/0.99      inference(predicate_to_equality,[status(thm)],[c_2757]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_2273,plain,
% 2.90/0.99      ( v1_funct_1(X0) != iProver_top
% 2.90/0.99      | v1_funct_1(k2_funct_1(X0)) = iProver_top
% 2.90/0.99      | v1_relat_1(X0) != iProver_top ),
% 2.90/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_4916,plain,
% 2.90/0.99      ( v1_funct_1(k4_relat_1(sK2)) = iProver_top
% 2.90/0.99      | v1_funct_1(sK2) != iProver_top
% 2.90/0.99      | v1_relat_1(sK2) != iProver_top ),
% 2.90/0.99      inference(superposition,[status(thm)],[c_3825,c_2273]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_5364,plain,
% 2.90/0.99      ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) = iProver_top ),
% 2.90/0.99      inference(global_propositional_subsumption,
% 2.90/0.99                [status(thm)],
% 2.90/0.99                [c_5002,c_43,c_45,c_2758,c_4447,c_4916]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_5369,plain,
% 2.90/0.99      ( sK1 = k1_xboole_0
% 2.90/0.99      | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 2.90/0.99      inference(superposition,[status(thm)],[c_4457,c_5364]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_5371,plain,
% 2.90/0.99      ( k1_relset_1(sK1,k1_relat_1(sK2),k4_relat_1(sK2)) = k1_relat_1(k4_relat_1(sK2)) ),
% 2.90/0.99      inference(superposition,[status(thm)],[c_5364,c_2268]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_5378,plain,
% 2.90/0.99      ( k1_relset_1(sK1,k1_relat_1(sK2),k4_relat_1(sK2)) = sK1 ),
% 2.90/0.99      inference(light_normalisation,[status(thm)],[c_5371,c_4753]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_5389,plain,
% 2.90/0.99      ( k1_relset_1(sK1,sK0,k4_relat_1(sK2)) = sK1 | sK1 = k1_xboole_0 ),
% 2.90/0.99      inference(superposition,[status(thm)],[c_4457,c_5378]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_28,plain,
% 2.90/0.99      ( v1_funct_2(X0,X1,X2)
% 2.90/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.90/0.99      | k1_relset_1(X1,X2,X0) != X1
% 2.90/0.99      | k1_xboole_0 = X2 ),
% 2.90/0.99      inference(cnf_transformation,[],[f82]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_942,plain,
% 2.90/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.90/0.99      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.90/0.99      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.90/0.99      | k1_relset_1(X1,X2,X0) != X1
% 2.90/0.99      | k2_funct_1(sK2) != X0
% 2.90/0.99      | sK0 != X2
% 2.90/0.99      | sK1 != X1
% 2.90/0.99      | k1_xboole_0 = X2 ),
% 2.90/0.99      inference(resolution_lifted,[status(thm)],[c_28,c_37]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_943,plain,
% 2.90/0.99      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.90/0.99      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.90/0.99      | k1_relset_1(sK1,sK0,k2_funct_1(sK2)) != sK1
% 2.90/0.99      | k1_xboole_0 = sK0 ),
% 2.90/0.99      inference(unflattening,[status(thm)],[c_942]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_2246,plain,
% 2.90/0.99      ( k1_relset_1(sK1,sK0,k2_funct_1(sK2)) != sK1
% 2.90/0.99      | k1_xboole_0 = sK0
% 2.90/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.90/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.90/0.99      inference(predicate_to_equality,[status(thm)],[c_943]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_944,plain,
% 2.90/0.99      ( k1_relset_1(sK1,sK0,k2_funct_1(sK2)) != sK1
% 2.90/0.99      | k1_xboole_0 = sK0
% 2.90/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.90/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.90/0.99      inference(predicate_to_equality,[status(thm)],[c_943]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_2622,plain,
% 2.90/0.99      ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
% 2.90/0.99      | v1_funct_1(sK2) != iProver_top
% 2.90/0.99      | v1_relat_1(sK2) != iProver_top ),
% 2.90/0.99      inference(predicate_to_equality,[status(thm)],[c_2621]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_2783,plain,
% 2.90/0.99      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.90/0.99      | k1_xboole_0 = sK0
% 2.90/0.99      | k1_relset_1(sK1,sK0,k2_funct_1(sK2)) != sK1 ),
% 2.90/0.99      inference(global_propositional_subsumption,
% 2.90/0.99                [status(thm)],
% 2.90/0.99                [c_2246,c_43,c_45,c_944,c_2622,c_2758]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_2784,plain,
% 2.90/0.99      ( k1_relset_1(sK1,sK0,k2_funct_1(sK2)) != sK1
% 2.90/0.99      | k1_xboole_0 = sK0
% 2.90/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 2.90/0.99      inference(renaming,[status(thm)],[c_2783]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_3904,plain,
% 2.90/0.99      ( k1_relset_1(sK1,sK0,k4_relat_1(sK2)) != sK1
% 2.90/0.99      | sK0 = k1_xboole_0
% 2.90/0.99      | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 2.90/0.99      inference(demodulation,[status(thm)],[c_3825,c_2784]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_5452,plain,
% 2.90/0.99      ( sK0 = k1_xboole_0
% 2.90/0.99      | sK1 = k1_xboole_0
% 2.90/0.99      | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 2.90/0.99      inference(superposition,[status(thm)],[c_5389,c_3904]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_6741,plain,
% 2.90/0.99      ( sK1 = k1_xboole_0 ),
% 2.90/0.99      inference(global_propositional_subsumption,
% 2.90/0.99                [status(thm)],
% 2.90/0.99                [c_6658,c_5369,c_5452]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_6414,plain,
% 2.90/0.99      ( k1_relat_1(sK2) = k1_xboole_0
% 2.90/0.99      | sK1 != k1_xboole_0
% 2.90/0.99      | sK2 = k1_xboole_0
% 2.90/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0))) != iProver_top
% 2.90/0.99      | v1_funct_1(sK2) != iProver_top ),
% 2.90/0.99      inference(superposition,[status(thm)],[c_4277,c_2255]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_6647,plain,
% 2.90/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0))) != iProver_top
% 2.90/0.99      | sK2 = k1_xboole_0
% 2.90/0.99      | sK1 != k1_xboole_0 ),
% 2.90/0.99      inference(global_propositional_subsumption,
% 2.90/0.99                [status(thm)],
% 2.90/0.99                [c_6414,c_42,c_43,c_40,c_132,c_0,c_648,c_662,c_676,c_1185,
% 2.90/0.99                 c_2621,c_2757,c_2791,c_3024,c_3048,c_3241,c_3339,c_3362,
% 2.90/0.99                 c_4146,c_4277,c_4455,c_4957,c_5290,c_5447,c_5686,c_5939,
% 2.90/0.99                 c_6629]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_6648,plain,
% 2.90/0.99      ( sK1 != k1_xboole_0
% 2.90/0.99      | sK2 = k1_xboole_0
% 2.90/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0))) != iProver_top ),
% 2.90/0.99      inference(renaming,[status(thm)],[c_6647]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_6744,plain,
% 2.90/0.99      ( sK2 = k1_xboole_0
% 2.90/0.99      | k1_xboole_0 != k1_xboole_0
% 2.90/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0))) != iProver_top ),
% 2.90/0.99      inference(demodulation,[status(thm)],[c_6741,c_6648]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_6844,plain,
% 2.90/0.99      ( sK2 = k1_xboole_0
% 2.90/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0))) != iProver_top ),
% 2.90/0.99      inference(equality_resolution_simp,[status(thm)],[c_6744]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_4981,plain,
% 2.90/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) = iProver_top
% 2.90/0.99      | v1_funct_1(sK2) != iProver_top
% 2.90/0.99      | v1_relat_1(sK2) != iProver_top ),
% 2.90/0.99      inference(superposition,[status(thm)],[c_4277,c_2266]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_5147,plain,
% 2.90/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) = iProver_top ),
% 2.90/0.99      inference(global_propositional_subsumption,
% 2.90/0.99                [status(thm)],
% 2.90/0.99                [c_4981,c_43,c_45,c_2758]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_6754,plain,
% 2.90/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0))) = iProver_top ),
% 2.90/0.99      inference(demodulation,[status(thm)],[c_6741,c_5147]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_6847,plain,
% 2.90/0.99      ( sK2 = k1_xboole_0 ),
% 2.90/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_6844,c_6754]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_7078,plain,
% 2.90/0.99      ( k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
% 2.90/0.99      inference(demodulation,[status(thm)],[c_6847,c_6655]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_10,plain,
% 2.90/0.99      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 2.90/0.99      inference(cnf_transformation,[],[f64]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_7090,plain,
% 2.90/0.99      ( k1_xboole_0 != k1_xboole_0 ),
% 2.90/0.99      inference(light_normalisation,[status(thm)],[c_7078,c_10]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_7091,plain,
% 2.90/0.99      ( $false ),
% 2.90/0.99      inference(equality_resolution_simp,[status(thm)],[c_7090]) ).
% 2.90/0.99  
% 2.90/0.99  
% 2.90/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.90/0.99  
% 2.90/0.99  ------                               Statistics
% 2.90/0.99  
% 2.90/0.99  ------ General
% 2.90/0.99  
% 2.90/0.99  abstr_ref_over_cycles:                  0
% 2.90/0.99  abstr_ref_under_cycles:                 0
% 2.90/0.99  gc_basic_clause_elim:                   0
% 2.90/0.99  forced_gc_time:                         0
% 2.90/0.99  parsing_time:                           0.009
% 2.90/0.99  unif_index_cands_time:                  0.
% 2.90/0.99  unif_index_add_time:                    0.
% 2.90/0.99  orderings_time:                         0.
% 2.90/0.99  out_proof_time:                         0.012
% 2.90/0.99  total_time:                             0.214
% 2.90/0.99  num_of_symbols:                         50
% 2.90/0.99  num_of_terms:                           4062
% 2.90/0.99  
% 2.90/0.99  ------ Preprocessing
% 2.90/0.99  
% 2.90/0.99  num_of_splits:                          0
% 2.90/0.99  num_of_split_atoms:                     0
% 2.90/0.99  num_of_reused_defs:                     0
% 2.90/0.99  num_eq_ax_congr_red:                    4
% 2.90/0.99  num_of_sem_filtered_clauses:            1
% 2.90/0.99  num_of_subtypes:                        0
% 2.90/0.99  monotx_restored_types:                  0
% 2.90/0.99  sat_num_of_epr_types:                   0
% 2.90/0.99  sat_num_of_non_cyclic_types:            0
% 2.90/0.99  sat_guarded_non_collapsed_types:        0
% 2.90/0.99  num_pure_diseq_elim:                    0
% 2.90/0.99  simp_replaced_by:                       0
% 2.90/0.99  res_preprocessed:                       160
% 2.90/0.99  prep_upred:                             0
% 2.90/0.99  prep_unflattend:                        79
% 2.90/0.99  smt_new_axioms:                         0
% 2.90/0.99  pred_elim_cands:                        7
% 2.90/0.99  pred_elim:                              2
% 2.90/0.99  pred_elim_cl:                           -6
% 2.90/0.99  pred_elim_cycles:                       4
% 2.90/0.99  merged_defs:                            6
% 2.90/0.99  merged_defs_ncl:                        0
% 2.90/0.99  bin_hyper_res:                          6
% 2.90/0.99  prep_cycles:                            3
% 2.90/0.99  pred_elim_time:                         0.017
% 2.90/0.99  splitting_time:                         0.
% 2.90/0.99  sem_filter_time:                        0.
% 2.90/0.99  monotx_time:                            0.
% 2.90/0.99  subtype_inf_time:                       0.
% 2.90/0.99  
% 2.90/0.99  ------ Problem properties
% 2.90/0.99  
% 2.90/0.99  clauses:                                45
% 2.90/0.99  conjectures:                            3
% 2.90/0.99  epr:                                    8
% 2.90/0.99  horn:                                   39
% 2.90/0.99  ground:                                 20
% 2.90/0.99  unary:                                  9
% 2.90/0.99  binary:                                 17
% 2.90/0.99  lits:                                   120
% 2.90/0.99  lits_eq:                                44
% 2.90/0.99  fd_pure:                                0
% 2.90/0.99  fd_pseudo:                              0
% 2.90/0.99  fd_cond:                                4
% 2.90/0.99  fd_pseudo_cond:                         0
% 2.90/0.99  ac_symbols:                             0
% 2.90/0.99  
% 2.90/0.99  ------ Propositional Solver
% 2.90/0.99  
% 2.90/0.99  prop_solver_calls:                      25
% 2.90/0.99  prop_fast_solver_calls:                 1312
% 2.90/0.99  smt_solver_calls:                       0
% 2.90/0.99  smt_fast_solver_calls:                  0
% 2.90/0.99  prop_num_of_clauses:                    2013
% 2.90/0.99  prop_preprocess_simplified:             6663
% 2.90/0.99  prop_fo_subsumed:                       55
% 2.90/0.99  prop_solver_time:                       0.
% 2.90/0.99  smt_solver_time:                        0.
% 2.90/0.99  smt_fast_solver_time:                   0.
% 2.90/0.99  prop_fast_solver_time:                  0.
% 2.90/0.99  prop_unsat_core_time:                   0.
% 2.90/0.99  
% 2.90/0.99  ------ QBF
% 2.90/0.99  
% 2.90/0.99  qbf_q_res:                              0
% 2.90/0.99  qbf_num_tautologies:                    0
% 2.90/0.99  qbf_prep_cycles:                        0
% 2.90/0.99  
% 2.90/0.99  ------ BMC1
% 2.90/0.99  
% 2.90/0.99  bmc1_current_bound:                     -1
% 2.90/0.99  bmc1_last_solved_bound:                 -1
% 2.90/0.99  bmc1_unsat_core_size:                   -1
% 2.90/0.99  bmc1_unsat_core_parents_size:           -1
% 2.90/0.99  bmc1_merge_next_fun:                    0
% 2.90/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.90/0.99  
% 2.90/0.99  ------ Instantiation
% 2.90/0.99  
% 2.90/0.99  inst_num_of_clauses:                    631
% 2.90/0.99  inst_num_in_passive:                    79
% 2.90/0.99  inst_num_in_active:                     416
% 2.90/0.99  inst_num_in_unprocessed:                136
% 2.90/0.99  inst_num_of_loops:                      470
% 2.90/0.99  inst_num_of_learning_restarts:          0
% 2.90/0.99  inst_num_moves_active_passive:          50
% 2.90/0.99  inst_lit_activity:                      0
% 2.90/0.99  inst_lit_activity_moves:                0
% 2.90/0.99  inst_num_tautologies:                   0
% 2.90/0.99  inst_num_prop_implied:                  0
% 2.90/0.99  inst_num_existing_simplified:           0
% 2.90/0.99  inst_num_eq_res_simplified:             0
% 2.90/0.99  inst_num_child_elim:                    0
% 2.90/0.99  inst_num_of_dismatching_blockings:      304
% 2.90/0.99  inst_num_of_non_proper_insts:           868
% 2.90/0.99  inst_num_of_duplicates:                 0
% 2.90/0.99  inst_inst_num_from_inst_to_res:         0
% 2.90/0.99  inst_dismatching_checking_time:         0.
% 2.90/0.99  
% 2.90/0.99  ------ Resolution
% 2.90/0.99  
% 2.90/0.99  res_num_of_clauses:                     0
% 2.90/0.99  res_num_in_passive:                     0
% 2.90/0.99  res_num_in_active:                      0
% 2.90/0.99  res_num_of_loops:                       163
% 2.90/0.99  res_forward_subset_subsumed:            40
% 2.90/0.99  res_backward_subset_subsumed:           6
% 2.90/0.99  res_forward_subsumed:                   0
% 2.90/0.99  res_backward_subsumed:                  0
% 2.90/0.99  res_forward_subsumption_resolution:     6
% 2.90/0.99  res_backward_subsumption_resolution:    1
% 2.90/0.99  res_clause_to_clause_subsumption:       339
% 2.90/0.99  res_orphan_elimination:                 0
% 2.90/0.99  res_tautology_del:                      148
% 2.90/0.99  res_num_eq_res_simplified:              0
% 2.90/0.99  res_num_sel_changes:                    0
% 2.90/0.99  res_moves_from_active_to_pass:          0
% 2.90/0.99  
% 2.90/0.99  ------ Superposition
% 2.90/0.99  
% 2.90/0.99  sup_time_total:                         0.
% 2.90/0.99  sup_time_generating:                    0.
% 2.90/0.99  sup_time_sim_full:                      0.
% 2.90/0.99  sup_time_sim_immed:                     0.
% 2.90/0.99  
% 2.90/0.99  sup_num_of_clauses:                     72
% 2.90/0.99  sup_num_in_active:                      43
% 2.90/0.99  sup_num_in_passive:                     29
% 2.90/0.99  sup_num_of_loops:                       93
% 2.90/0.99  sup_fw_superposition:                   59
% 2.90/0.99  sup_bw_superposition:                   52
% 2.90/0.99  sup_immediate_simplified:               86
% 2.90/0.99  sup_given_eliminated:                   0
% 2.90/0.99  comparisons_done:                       0
% 2.90/0.99  comparisons_avoided:                    8
% 2.90/0.99  
% 2.90/0.99  ------ Simplifications
% 2.90/0.99  
% 2.90/0.99  
% 2.90/0.99  sim_fw_subset_subsumed:                 13
% 2.90/0.99  sim_bw_subset_subsumed:                 8
% 2.90/0.99  sim_fw_subsumed:                        5
% 2.90/0.99  sim_bw_subsumed:                        3
% 2.90/0.99  sim_fw_subsumption_res:                 2
% 2.90/0.99  sim_bw_subsumption_res:                 0
% 2.90/0.99  sim_tautology_del:                      6
% 2.90/0.99  sim_eq_tautology_del:                   22
% 2.90/0.99  sim_eq_res_simp:                        5
% 2.90/0.99  sim_fw_demodulated:                     3
% 2.90/0.99  sim_bw_demodulated:                     63
% 2.90/0.99  sim_light_normalised:                   50
% 2.90/0.99  sim_joinable_taut:                      0
% 2.90/0.99  sim_joinable_simp:                      0
% 2.90/0.99  sim_ac_normalised:                      0
% 2.90/0.99  sim_smt_subsumption:                    0
% 2.90/0.99  
%------------------------------------------------------------------------------
