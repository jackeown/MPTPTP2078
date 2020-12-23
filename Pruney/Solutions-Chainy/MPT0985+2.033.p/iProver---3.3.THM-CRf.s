%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:02:26 EST 2020

% Result     : Theorem 7.67s
% Output     : CNFRefutation 7.67s
% Verified   : 
% Statistics : Number of formulae       :  229 (10847 expanded)
%              Number of clauses        :  150 (3332 expanded)
%              Number of leaves         :   22 (2133 expanded)
%              Depth                    :   31
%              Number of atoms          :  711 (58587 expanded)
%              Number of equality atoms :  337 (10685 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f72,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f53])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f54])).

fof(f118,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f68])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_partfun1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v1_partfun1(X2,X0)
          & v1_funct_1(X2) )
       => ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f42])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f21,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( v5_relat_1(X2,X1)
      & v4_relat_1(X2,X0)
      & v1_relat_1(X2)
      & v1_xboole_0(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( v5_relat_1(X2,X1)
          & v4_relat_1(X2,X0)
          & v1_relat_1(X2)
          & v1_xboole_0(X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( v5_relat_1(sK0(X0,X1),X1)
        & v4_relat_1(sK0(X0,X1),X0)
        & v1_relat_1(sK0(X0,X1))
        & v1_xboole_0(sK0(X0,X1))
        & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X0,X1] :
      ( v5_relat_1(sK0(X0,X1),X1)
      & v4_relat_1(sK0(X0,X1),X0)
      & v1_relat_1(sK0(X0,X1))
      & v1_xboole_0(sK0(X0,X1))
      & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f59])).

fof(f96,plain,(
    ! [X0,X1] : v1_xboole_0(sK0(X0,X1)) ),
    inference(cnf_transformation,[],[f60])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f14,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f37,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f36])).

fof(f86,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f25])).

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
    inference(flattening,[],[f49])).

fof(f61,plain,
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

fof(f62,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
      | ~ v1_funct_1(k2_funct_1(sK3)) )
    & k2_relset_1(sK1,sK2,sK3) = sK2
    & v2_funct_1(sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK3,sK1,sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f50,f61])).

fof(f112,plain,(
    v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f62])).

fof(f109,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f62])).

fof(f111,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f62])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f22,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f46,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f45])).

fof(f102,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f113,plain,(
    k2_relset_1(sK1,sK2,sK3) = sK2 ),
    inference(cnf_transformation,[],[f62])).

fof(f85,plain,(
    ! [X0] :
      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f13,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f35,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f34])).

fof(f84,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f83,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f23,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(X1,X2)
       => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
            & v1_funct_2(X3,X0,X2)
            & v1_funct_1(X3) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(X3,X0,X2)
        & v1_funct_1(X3) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f48,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(X3,X0,X2)
        & v1_funct_1(X3) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f47])).

fof(f105,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(X3,X0,X2)
      | k1_xboole_0 = X1
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f101,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f107,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
      | k1_xboole_0 = X1
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f114,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
    | ~ v1_funct_1(k2_funct_1(sK3)) ),
    inference(cnf_transformation,[],[f62])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f12,axiom,(
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
    inference(ennf_transformation,[],[f12])).

fof(f58,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f82,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_relat_1(X0)
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f81,plain,(
    ! [X0] :
      ( k1_xboole_0 = k2_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f32,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f80,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f79,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_8,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1913,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_5,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f118])).

cnf(c_31,plain,
    ( v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_29,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_576,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ v1_xboole_0(X1)
    | ~ v1_funct_1(X0) ),
    inference(resolution,[status(thm)],[c_31,c_29])).

cnf(c_580,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_funct_2(X0,X1,X2)
    | ~ v1_xboole_0(X1)
    | ~ v1_funct_1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_576,c_31,c_29])).

cnf(c_581,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X1)
    | ~ v1_funct_1(X0) ),
    inference(renaming,[status(thm)],[c_580])).

cnf(c_1883,plain,
    ( v1_funct_2(X0,X1,X2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_581])).

cnf(c_2844,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5,c_1883])).

cnf(c_35,plain,
    ( v1_xboole_0(sK0(X0,X1)) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_73,plain,
    ( v1_xboole_0(sK0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_2348,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0(X1,X2),X3)))
    | v1_xboole_0(X0)
    | ~ v1_xboole_0(sK0(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_2969,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0(X0,X1),X2)))
    | ~ v1_xboole_0(sK0(X0,X1))
    | v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2348])).

cnf(c_2971,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0(X0,X1),X2))) != iProver_top
    | v1_xboole_0(sK0(X0,X1)) != iProver_top
    | v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2969])).

cnf(c_7,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_2224,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_2970,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0(X0,X1),X2))) ),
    inference(instantiation,[status(thm)],[c_2224])).

cnf(c_2973,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0(X0,X1),X2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2970])).

cnf(c_9131,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_2(X0,k1_xboole_0,X1) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2844,c_73,c_2971,c_2973])).

cnf(c_9132,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_9131])).

cnf(c_9141,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1) = iProver_top
    | r1_tarski(X0,k1_xboole_0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1913,c_9132])).

cnf(c_22,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_48,negated_conjecture,
    ( v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_616,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_48])).

cnf(c_617,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_616])).

cnf(c_51,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_619,plain,
    ( ~ v1_relat_1(sK3)
    | k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_617,c_51])).

cnf(c_1881,plain,
    ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_619])).

cnf(c_49,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_2234,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_2251,plain,
    ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1881,c_51,c_49,c_617,c_2234])).

cnf(c_37,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_1893,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_6255,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK3)),k1_relat_1(sK3)))) = iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2251,c_1893])).

cnf(c_1886,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_49])).

cnf(c_28,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1898,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_5863,plain,
    ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1886,c_1898])).

cnf(c_47,negated_conjecture,
    ( k2_relset_1(sK1,sK2,sK3) = sK2 ),
    inference(cnf_transformation,[],[f113])).

cnf(c_5882,plain,
    ( k2_relat_1(sK3) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_5863,c_47])).

cnf(c_23,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_602,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_48])).

cnf(c_603,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_602])).

cnf(c_605,plain,
    ( ~ v1_relat_1(sK3)
    | k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_603,c_51])).

cnf(c_1882,plain,
    ( k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_605])).

cnf(c_2278,plain,
    ( k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1882,c_51,c_49,c_603,c_2234])).

cnf(c_5976,plain,
    ( k1_relat_1(k2_funct_1(sK3)) = sK2 ),
    inference(demodulation,[status(thm)],[c_5882,c_2278])).

cnf(c_6316,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3)))) = iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6255,c_5976])).

cnf(c_52,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_51])).

cnf(c_54,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_49])).

cnf(c_20,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_2213,plain,
    ( v1_funct_1(k2_funct_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_2214,plain,
    ( v1_funct_1(k2_funct_1(sK3)) = iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2213])).

cnf(c_21,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_2216,plain,
    ( ~ v1_funct_1(sK3)
    | v1_relat_1(k2_funct_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_2217,plain,
    ( v1_funct_1(sK3) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2216])).

cnf(c_2235,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2234])).

cnf(c_7179,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6316,c_52,c_54,c_2214,c_2217,c_2235])).

cnf(c_43,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(X0,X1,X3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(X2,X3)
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f105])).

cnf(c_1888,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,X2,X0) != iProver_top
    | v1_funct_2(X1,X2,X3) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | r1_tarski(X0,X3) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_7191,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | v1_funct_2(k2_funct_1(sK3),sK2,X0) = iProver_top
    | v1_funct_2(k2_funct_1(sK3),sK2,k1_relat_1(sK3)) != iProver_top
    | r1_tarski(k1_relat_1(sK3),X0) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7179,c_1888])).

cnf(c_38,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_1892,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_6009,plain,
    ( v1_funct_2(k2_funct_1(sK3),sK2,k2_relat_1(k2_funct_1(sK3))) = iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5976,c_1892])).

cnf(c_6014,plain,
    ( v1_funct_2(k2_funct_1(sK3),sK2,k1_relat_1(sK3)) = iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6009,c_2251])).

cnf(c_24074,plain,
    ( r1_tarski(k1_relat_1(sK3),X0) != iProver_top
    | k1_relat_1(sK3) = k1_xboole_0
    | v1_funct_2(k2_funct_1(sK3),sK2,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7191,c_52,c_54,c_2214,c_2217,c_2235,c_6014])).

cnf(c_24075,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | v1_funct_2(k2_funct_1(sK3),sK2,X0) = iProver_top
    | r1_tarski(k1_relat_1(sK3),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_24074])).

cnf(c_41,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ r1_tarski(X2,X3)
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f107])).

cnf(c_1890,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,X2,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) = iProver_top
    | r1_tarski(X0,X3) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_6262,plain,
    ( k2_relat_1(X0) = k1_xboole_0
    | v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1893,c_1890])).

cnf(c_64,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_29021,plain,
    ( k2_relat_1(X0) = k1_xboole_0
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6262,c_64])).

cnf(c_29033,plain,
    ( k2_relat_1(k2_funct_1(sK3)) = k1_xboole_0
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
    | r1_tarski(k2_relat_1(k2_funct_1(sK3)),X0) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5976,c_29021])).

cnf(c_29138,plain,
    ( k2_relat_1(k2_funct_1(sK3)) = k1_xboole_0
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
    | r1_tarski(k1_relat_1(sK3),X0) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_29033,c_2251])).

cnf(c_29139,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
    | r1_tarski(k1_relat_1(sK3),X0) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_29138,c_2251])).

cnf(c_7190,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | v1_funct_2(k2_funct_1(sK3),sK2,k1_relat_1(sK3)) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
    | r1_tarski(k1_relat_1(sK3),X0) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7179,c_1890])).

cnf(c_29901,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
    | r1_tarski(k1_relat_1(sK3),X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_29139,c_52,c_54,c_2214,c_2217,c_2235,c_6014,c_7190])).

cnf(c_46,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
    | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK3)) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_1887,plain,
    ( v1_funct_2(k2_funct_1(sK3),sK2,sK1) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_56,plain,
    ( v1_funct_2(k2_funct_1(sK3),sK2,sK1) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_2244,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_2(k2_funct_1(sK3),sK2,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1887,c_52,c_54,c_56,c_2214,c_2235])).

cnf(c_2245,plain,
    ( v1_funct_2(k2_funct_1(sK3),sK2,sK1) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2244])).

cnf(c_29917,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | v1_funct_2(k2_funct_1(sK3),sK2,sK1) != iProver_top
    | r1_tarski(k1_relat_1(sK3),sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_29901,c_2245])).

cnf(c_26,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_12,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_636,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_26,c_12])).

cnf(c_640,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_636,c_24])).

cnf(c_641,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1) ),
    inference(renaming,[status(thm)],[c_640])).

cnf(c_2271,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | r1_tarski(k1_relat_1(sK3),sK1) ),
    inference(instantiation,[status(thm)],[c_641])).

cnf(c_2272,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | r1_tarski(k1_relat_1(sK3),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2271])).

cnf(c_29991,plain,
    ( v1_funct_2(k2_funct_1(sK3),sK2,sK1) != iProver_top
    | k1_relat_1(sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_29917,c_54,c_2272])).

cnf(c_29992,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | v1_funct_2(k2_funct_1(sK3),sK2,sK1) != iProver_top ),
    inference(renaming,[status(thm)],[c_29991])).

cnf(c_29997,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | r1_tarski(k1_relat_1(sK3),sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_24075,c_29992])).

cnf(c_30420,plain,
    ( k1_relat_1(sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_29997,c_54,c_2272])).

cnf(c_18,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_relat_1(X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1905,plain,
    ( k2_relat_1(X0) != k1_xboole_0
    | k1_relat_1(X0) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_5854,plain,
    ( k1_relat_1(k2_funct_1(sK3)) = k1_xboole_0
    | k1_relat_1(sK3) != k1_xboole_0
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2251,c_1905])).

cnf(c_5855,plain,
    ( k2_relat_1(sK3) = k1_xboole_0
    | k1_relat_1(sK3) != k1_xboole_0
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5854,c_2278])).

cnf(c_19,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) = k1_xboole_0
    | k1_relat_1(X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_3347,plain,
    ( ~ v1_relat_1(sK3)
    | k2_relat_1(sK3) = k1_xboole_0
    | k1_relat_1(sK3) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_6987,plain,
    ( k1_relat_1(sK3) != k1_xboole_0
    | k2_relat_1(sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5855,c_49,c_2234,c_3347])).

cnf(c_6988,plain,
    ( k2_relat_1(sK3) = k1_xboole_0
    | k1_relat_1(sK3) != k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_6987])).

cnf(c_6989,plain,
    ( k1_relat_1(sK3) != k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6988,c_5882])).

cnf(c_30471,plain,
    ( sK2 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_30420,c_6989])).

cnf(c_30498,plain,
    ( sK2 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_30471])).

cnf(c_16,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1907,plain,
    ( k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_5985,plain,
    ( sK2 != k1_xboole_0
    | sK3 = k1_xboole_0
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5882,c_1907])).

cnf(c_6081,plain,
    ( sK3 = k1_xboole_0
    | sK2 != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5985,c_54,c_2235])).

cnf(c_6082,plain,
    ( sK2 != k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_6081])).

cnf(c_30696,plain,
    ( sK3 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_30498,c_6082])).

cnf(c_30730,plain,
    ( sK3 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_30696])).

cnf(c_30702,plain,
    ( v1_funct_2(k2_funct_1(sK3),k1_xboole_0,sK1) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_30498,c_2245])).

cnf(c_30714,plain,
    ( v1_funct_2(k2_funct_1(sK3),k1_xboole_0,sK1) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_30702,c_5])).

cnf(c_30736,plain,
    ( v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK1) != iProver_top
    | m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_30730,c_30714])).

cnf(c_111,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_113,plain,
    ( v1_funct_1(k1_xboole_0) != iProver_top
    | v1_relat_1(k2_funct_1(k1_xboole_0)) = iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_111])).

cnf(c_2223,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_2225,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2223])).

cnf(c_2227,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2224])).

cnf(c_1014,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2238,plain,
    ( v1_funct_1(X0)
    | ~ v1_funct_1(sK3)
    | X0 != sK3 ),
    inference(instantiation,[status(thm)],[c_1014])).

cnf(c_2239,plain,
    ( X0 != sK3
    | v1_funct_1(X0) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2238])).

cnf(c_2241,plain,
    ( k1_xboole_0 != sK3
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2239])).

cnf(c_17,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_2562,plain,
    ( ~ v1_relat_1(sK3)
    | k1_relat_1(sK3) != k1_xboole_0
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_2432,plain,
    ( v1_funct_1(X0)
    | ~ v1_funct_1(k2_funct_1(sK3))
    | X0 != k2_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1014])).

cnf(c_2620,plain,
    ( v1_funct_1(k2_funct_1(X0))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | k2_funct_1(X0) != k2_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2432])).

cnf(c_2622,plain,
    ( k2_funct_1(X0) != k2_funct_1(sK3)
    | v1_funct_1(k2_funct_1(X0)) = iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2620])).

cnf(c_2624,plain,
    ( k2_funct_1(k1_xboole_0) != k2_funct_1(sK3)
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_funct_1(k2_funct_1(k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2622])).

cnf(c_1013,plain,
    ( X0 != X1
    | k2_funct_1(X0) = k2_funct_1(X1) ),
    theory(equality)).

cnf(c_2621,plain,
    ( X0 != sK3
    | k2_funct_1(X0) = k2_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1013])).

cnf(c_2626,plain,
    ( k2_funct_1(k1_xboole_0) = k2_funct_1(sK3)
    | k1_xboole_0 != sK3 ),
    inference(instantiation,[status(thm)],[c_2621])).

cnf(c_30697,plain,
    ( k1_relat_1(k2_funct_1(sK3)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_30498,c_5976])).

cnf(c_30732,plain,
    ( k1_relat_1(k2_funct_1(k1_xboole_0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_30730,c_30697])).

cnf(c_31777,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(k2_funct_1(k1_xboole_0))))) = iProver_top
    | v1_funct_1(k2_funct_1(k1_xboole_0)) != iProver_top
    | v1_relat_1(k2_funct_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_30732,c_1893])).

cnf(c_31798,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | v1_funct_1(k2_funct_1(k1_xboole_0)) != iProver_top
    | v1_relat_1(k2_funct_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_31777,c_5])).

cnf(c_32557,plain,
    ( v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_30736,c_52,c_49,c_54,c_113,c_2214,c_2225,c_2227,c_2234,c_2235,c_2241,c_2272,c_2562,c_2624,c_2626,c_29997,c_31798])).

cnf(c_37441,plain,
    ( r1_tarski(k2_funct_1(k1_xboole_0),k1_xboole_0) != iProver_top
    | v1_funct_1(k2_funct_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9141,c_32557])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1912,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_6256,plain,
    ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1893,c_1912])).

cnf(c_31772,plain,
    ( r1_tarski(k2_funct_1(k1_xboole_0),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k2_funct_1(k1_xboole_0)))) = iProver_top
    | v1_funct_1(k2_funct_1(k1_xboole_0)) != iProver_top
    | v1_relat_1(k2_funct_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_30732,c_6256])).

cnf(c_31805,plain,
    ( r1_tarski(k2_funct_1(k1_xboole_0),k1_xboole_0) = iProver_top
    | v1_funct_1(k2_funct_1(k1_xboole_0)) != iProver_top
    | v1_relat_1(k2_funct_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_31772,c_5])).

cnf(c_37453,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(grounding,[status(thm)],[c_2227:[bind(X1,$fot(k1_xboole_0)),bind(X0,$fot(k1_xboole_0))]])).

cnf(c_37454,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(grounding,[status(thm)],[c_2225:[bind(X1,$fot(k1_xboole_0)),bind(X0,$fot(k1_xboole_0))]])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_37441,c_31805,c_29997,c_2626,c_2624,c_2562,c_2272,c_2241,c_2235,c_2234,c_37453,c_37454,c_2214,c_113,c_54,c_49,c_52])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 20:39:52 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 7.67/1.48  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.67/1.48  
% 7.67/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.67/1.48  
% 7.67/1.48  ------  iProver source info
% 7.67/1.48  
% 7.67/1.48  git: date: 2020-06-30 10:37:57 +0100
% 7.67/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.67/1.48  git: non_committed_changes: false
% 7.67/1.48  git: last_make_outside_of_git: false
% 7.67/1.48  
% 7.67/1.48  ------ 
% 7.67/1.48  
% 7.67/1.48  ------ Input Options
% 7.67/1.48  
% 7.67/1.48  --out_options                           all
% 7.67/1.48  --tptp_safe_out                         true
% 7.67/1.48  --problem_path                          ""
% 7.67/1.48  --include_path                          ""
% 7.67/1.48  --clausifier                            res/vclausify_rel
% 7.67/1.48  --clausifier_options                    --mode clausify
% 7.67/1.48  --stdin                                 false
% 7.67/1.48  --stats_out                             all
% 7.67/1.48  
% 7.67/1.48  ------ General Options
% 7.67/1.48  
% 7.67/1.48  --fof                                   false
% 7.67/1.48  --time_out_real                         305.
% 7.67/1.48  --time_out_virtual                      -1.
% 7.67/1.48  --symbol_type_check                     false
% 7.67/1.48  --clausify_out                          false
% 7.67/1.48  --sig_cnt_out                           false
% 7.67/1.48  --trig_cnt_out                          false
% 7.67/1.48  --trig_cnt_out_tolerance                1.
% 7.67/1.48  --trig_cnt_out_sk_spl                   false
% 7.67/1.48  --abstr_cl_out                          false
% 7.67/1.48  
% 7.67/1.48  ------ Global Options
% 7.67/1.48  
% 7.67/1.48  --schedule                              default
% 7.67/1.48  --add_important_lit                     false
% 7.67/1.48  --prop_solver_per_cl                    1000
% 7.67/1.48  --min_unsat_core                        false
% 7.67/1.48  --soft_assumptions                      false
% 7.67/1.48  --soft_lemma_size                       3
% 7.67/1.48  --prop_impl_unit_size                   0
% 7.67/1.48  --prop_impl_unit                        []
% 7.67/1.48  --share_sel_clauses                     true
% 7.67/1.48  --reset_solvers                         false
% 7.67/1.48  --bc_imp_inh                            [conj_cone]
% 7.67/1.48  --conj_cone_tolerance                   3.
% 7.67/1.48  --extra_neg_conj                        none
% 7.67/1.48  --large_theory_mode                     true
% 7.67/1.48  --prolific_symb_bound                   200
% 7.67/1.48  --lt_threshold                          2000
% 7.67/1.48  --clause_weak_htbl                      true
% 7.67/1.48  --gc_record_bc_elim                     false
% 7.67/1.48  
% 7.67/1.48  ------ Preprocessing Options
% 7.67/1.48  
% 7.67/1.48  --preprocessing_flag                    true
% 7.67/1.48  --time_out_prep_mult                    0.1
% 7.67/1.48  --splitting_mode                        input
% 7.67/1.48  --splitting_grd                         true
% 7.67/1.48  --splitting_cvd                         false
% 7.67/1.48  --splitting_cvd_svl                     false
% 7.67/1.48  --splitting_nvd                         32
% 7.67/1.48  --sub_typing                            true
% 7.67/1.48  --prep_gs_sim                           true
% 7.67/1.48  --prep_unflatten                        true
% 7.67/1.48  --prep_res_sim                          true
% 7.67/1.48  --prep_upred                            true
% 7.67/1.48  --prep_sem_filter                       exhaustive
% 7.67/1.48  --prep_sem_filter_out                   false
% 7.67/1.48  --pred_elim                             true
% 7.67/1.48  --res_sim_input                         true
% 7.67/1.48  --eq_ax_congr_red                       true
% 7.67/1.48  --pure_diseq_elim                       true
% 7.67/1.48  --brand_transform                       false
% 7.67/1.48  --non_eq_to_eq                          false
% 7.67/1.48  --prep_def_merge                        true
% 7.67/1.48  --prep_def_merge_prop_impl              false
% 7.67/1.48  --prep_def_merge_mbd                    true
% 7.67/1.48  --prep_def_merge_tr_red                 false
% 7.67/1.48  --prep_def_merge_tr_cl                  false
% 7.67/1.48  --smt_preprocessing                     true
% 7.67/1.48  --smt_ac_axioms                         fast
% 7.67/1.48  --preprocessed_out                      false
% 7.67/1.48  --preprocessed_stats                    false
% 7.67/1.48  
% 7.67/1.48  ------ Abstraction refinement Options
% 7.67/1.48  
% 7.67/1.48  --abstr_ref                             []
% 7.67/1.48  --abstr_ref_prep                        false
% 7.67/1.48  --abstr_ref_until_sat                   false
% 7.67/1.48  --abstr_ref_sig_restrict                funpre
% 7.67/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.67/1.48  --abstr_ref_under                       []
% 7.67/1.48  
% 7.67/1.48  ------ SAT Options
% 7.67/1.48  
% 7.67/1.48  --sat_mode                              false
% 7.67/1.48  --sat_fm_restart_options                ""
% 7.67/1.48  --sat_gr_def                            false
% 7.67/1.48  --sat_epr_types                         true
% 7.67/1.48  --sat_non_cyclic_types                  false
% 7.67/1.48  --sat_finite_models                     false
% 7.67/1.48  --sat_fm_lemmas                         false
% 7.67/1.48  --sat_fm_prep                           false
% 7.67/1.48  --sat_fm_uc_incr                        true
% 7.67/1.48  --sat_out_model                         small
% 7.67/1.48  --sat_out_clauses                       false
% 7.67/1.48  
% 7.67/1.48  ------ QBF Options
% 7.67/1.48  
% 7.67/1.48  --qbf_mode                              false
% 7.67/1.48  --qbf_elim_univ                         false
% 7.67/1.48  --qbf_dom_inst                          none
% 7.67/1.48  --qbf_dom_pre_inst                      false
% 7.67/1.48  --qbf_sk_in                             false
% 7.67/1.48  --qbf_pred_elim                         true
% 7.67/1.48  --qbf_split                             512
% 7.67/1.48  
% 7.67/1.48  ------ BMC1 Options
% 7.67/1.48  
% 7.67/1.48  --bmc1_incremental                      false
% 7.67/1.48  --bmc1_axioms                           reachable_all
% 7.67/1.48  --bmc1_min_bound                        0
% 7.67/1.48  --bmc1_max_bound                        -1
% 7.67/1.48  --bmc1_max_bound_default                -1
% 7.67/1.48  --bmc1_symbol_reachability              true
% 7.67/1.48  --bmc1_property_lemmas                  false
% 7.67/1.48  --bmc1_k_induction                      false
% 7.67/1.48  --bmc1_non_equiv_states                 false
% 7.67/1.48  --bmc1_deadlock                         false
% 7.67/1.48  --bmc1_ucm                              false
% 7.67/1.48  --bmc1_add_unsat_core                   none
% 7.67/1.48  --bmc1_unsat_core_children              false
% 7.67/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.67/1.48  --bmc1_out_stat                         full
% 7.67/1.48  --bmc1_ground_init                      false
% 7.67/1.48  --bmc1_pre_inst_next_state              false
% 7.67/1.48  --bmc1_pre_inst_state                   false
% 7.67/1.48  --bmc1_pre_inst_reach_state             false
% 7.67/1.48  --bmc1_out_unsat_core                   false
% 7.67/1.48  --bmc1_aig_witness_out                  false
% 7.67/1.48  --bmc1_verbose                          false
% 7.67/1.48  --bmc1_dump_clauses_tptp                false
% 7.67/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.67/1.48  --bmc1_dump_file                        -
% 7.67/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.67/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.67/1.48  --bmc1_ucm_extend_mode                  1
% 7.67/1.48  --bmc1_ucm_init_mode                    2
% 7.67/1.48  --bmc1_ucm_cone_mode                    none
% 7.67/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.67/1.48  --bmc1_ucm_relax_model                  4
% 7.67/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.67/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.67/1.48  --bmc1_ucm_layered_model                none
% 7.67/1.48  --bmc1_ucm_max_lemma_size               10
% 7.67/1.48  
% 7.67/1.48  ------ AIG Options
% 7.67/1.48  
% 7.67/1.48  --aig_mode                              false
% 7.67/1.48  
% 7.67/1.48  ------ Instantiation Options
% 7.67/1.48  
% 7.67/1.48  --instantiation_flag                    true
% 7.67/1.48  --inst_sos_flag                         false
% 7.67/1.48  --inst_sos_phase                        true
% 7.67/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.67/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.67/1.48  --inst_lit_sel_side                     num_symb
% 7.67/1.48  --inst_solver_per_active                1400
% 7.67/1.48  --inst_solver_calls_frac                1.
% 7.67/1.48  --inst_passive_queue_type               priority_queues
% 7.67/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.67/1.48  --inst_passive_queues_freq              [25;2]
% 7.67/1.48  --inst_dismatching                      true
% 7.67/1.48  --inst_eager_unprocessed_to_passive     true
% 7.67/1.48  --inst_prop_sim_given                   true
% 7.67/1.48  --inst_prop_sim_new                     false
% 7.67/1.48  --inst_subs_new                         false
% 7.67/1.48  --inst_eq_res_simp                      false
% 7.67/1.48  --inst_subs_given                       false
% 7.67/1.48  --inst_orphan_elimination               true
% 7.67/1.48  --inst_learning_loop_flag               true
% 7.67/1.48  --inst_learning_start                   3000
% 7.67/1.48  --inst_learning_factor                  2
% 7.67/1.48  --inst_start_prop_sim_after_learn       3
% 7.67/1.48  --inst_sel_renew                        solver
% 7.67/1.48  --inst_lit_activity_flag                true
% 7.67/1.48  --inst_restr_to_given                   false
% 7.67/1.48  --inst_activity_threshold               500
% 7.67/1.48  --inst_out_proof                        true
% 7.67/1.48  
% 7.67/1.48  ------ Resolution Options
% 7.67/1.48  
% 7.67/1.48  --resolution_flag                       true
% 7.67/1.48  --res_lit_sel                           adaptive
% 7.67/1.48  --res_lit_sel_side                      none
% 7.67/1.48  --res_ordering                          kbo
% 7.67/1.48  --res_to_prop_solver                    active
% 7.67/1.48  --res_prop_simpl_new                    false
% 7.67/1.48  --res_prop_simpl_given                  true
% 7.67/1.48  --res_passive_queue_type                priority_queues
% 7.67/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.67/1.48  --res_passive_queues_freq               [15;5]
% 7.67/1.48  --res_forward_subs                      full
% 7.67/1.48  --res_backward_subs                     full
% 7.67/1.48  --res_forward_subs_resolution           true
% 7.67/1.48  --res_backward_subs_resolution          true
% 7.67/1.48  --res_orphan_elimination                true
% 7.67/1.48  --res_time_limit                        2.
% 7.67/1.48  --res_out_proof                         true
% 7.67/1.48  
% 7.67/1.48  ------ Superposition Options
% 7.67/1.48  
% 7.67/1.48  --superposition_flag                    true
% 7.67/1.48  --sup_passive_queue_type                priority_queues
% 7.67/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.67/1.48  --sup_passive_queues_freq               [8;1;4]
% 7.67/1.48  --demod_completeness_check              fast
% 7.67/1.48  --demod_use_ground                      true
% 7.67/1.48  --sup_to_prop_solver                    passive
% 7.67/1.48  --sup_prop_simpl_new                    true
% 7.67/1.48  --sup_prop_simpl_given                  true
% 7.67/1.48  --sup_fun_splitting                     false
% 7.67/1.48  --sup_smt_interval                      50000
% 7.67/1.48  
% 7.67/1.48  ------ Superposition Simplification Setup
% 7.67/1.48  
% 7.67/1.48  --sup_indices_passive                   []
% 7.67/1.48  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.67/1.48  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.67/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.67/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.67/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.67/1.48  --sup_full_bw                           [BwDemod]
% 7.67/1.48  --sup_immed_triv                        [TrivRules]
% 7.67/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.67/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.67/1.48  --sup_immed_bw_main                     []
% 7.67/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.67/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.67/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.67/1.48  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.67/1.48  
% 7.67/1.48  ------ Combination Options
% 7.67/1.48  
% 7.67/1.48  --comb_res_mult                         3
% 7.67/1.48  --comb_sup_mult                         2
% 7.67/1.48  --comb_inst_mult                        10
% 7.67/1.48  
% 7.67/1.48  ------ Debug Options
% 7.67/1.48  
% 7.67/1.48  --dbg_backtrace                         false
% 7.67/1.48  --dbg_dump_prop_clauses                 false
% 7.67/1.48  --dbg_dump_prop_clauses_file            -
% 7.67/1.48  --dbg_out_stat                          false
% 7.67/1.48  ------ Parsing...
% 7.67/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.67/1.48  
% 7.67/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 7.67/1.48  
% 7.67/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.67/1.48  
% 7.67/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.67/1.48  ------ Proving...
% 7.67/1.48  ------ Problem Properties 
% 7.67/1.48  
% 7.67/1.48  
% 7.67/1.48  clauses                                 43
% 7.67/1.48  conjectures                             5
% 7.67/1.48  EPR                                     5
% 7.67/1.48  Horn                                    40
% 7.67/1.48  unary                                   15
% 7.67/1.48  binary                                  8
% 7.67/1.48  lits                                    103
% 7.67/1.48  lits eq                                 20
% 7.67/1.48  fd_pure                                 0
% 7.67/1.48  fd_pseudo                               0
% 7.67/1.48  fd_cond                                 5
% 7.67/1.48  fd_pseudo_cond                          1
% 7.67/1.48  AC symbols                              0
% 7.67/1.48  
% 7.67/1.48  ------ Schedule dynamic 5 is on 
% 7.67/1.48  
% 7.67/1.48  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.67/1.48  
% 7.67/1.48  
% 7.67/1.48  ------ 
% 7.67/1.48  Current options:
% 7.67/1.48  ------ 
% 7.67/1.48  
% 7.67/1.48  ------ Input Options
% 7.67/1.48  
% 7.67/1.48  --out_options                           all
% 7.67/1.48  --tptp_safe_out                         true
% 7.67/1.48  --problem_path                          ""
% 7.67/1.48  --include_path                          ""
% 7.67/1.48  --clausifier                            res/vclausify_rel
% 7.67/1.48  --clausifier_options                    --mode clausify
% 7.67/1.48  --stdin                                 false
% 7.67/1.48  --stats_out                             all
% 7.67/1.48  
% 7.67/1.48  ------ General Options
% 7.67/1.48  
% 7.67/1.48  --fof                                   false
% 7.67/1.48  --time_out_real                         305.
% 7.67/1.48  --time_out_virtual                      -1.
% 7.67/1.48  --symbol_type_check                     false
% 7.67/1.48  --clausify_out                          false
% 7.67/1.48  --sig_cnt_out                           false
% 7.67/1.48  --trig_cnt_out                          false
% 7.67/1.48  --trig_cnt_out_tolerance                1.
% 7.67/1.48  --trig_cnt_out_sk_spl                   false
% 7.67/1.48  --abstr_cl_out                          false
% 7.67/1.48  
% 7.67/1.48  ------ Global Options
% 7.67/1.48  
% 7.67/1.48  --schedule                              default
% 7.67/1.48  --add_important_lit                     false
% 7.67/1.48  --prop_solver_per_cl                    1000
% 7.67/1.48  --min_unsat_core                        false
% 7.67/1.48  --soft_assumptions                      false
% 7.67/1.48  --soft_lemma_size                       3
% 7.67/1.48  --prop_impl_unit_size                   0
% 7.67/1.48  --prop_impl_unit                        []
% 7.67/1.48  --share_sel_clauses                     true
% 7.67/1.48  --reset_solvers                         false
% 7.67/1.48  --bc_imp_inh                            [conj_cone]
% 7.67/1.48  --conj_cone_tolerance                   3.
% 7.67/1.48  --extra_neg_conj                        none
% 7.67/1.48  --large_theory_mode                     true
% 7.67/1.48  --prolific_symb_bound                   200
% 7.67/1.48  --lt_threshold                          2000
% 7.67/1.48  --clause_weak_htbl                      true
% 7.67/1.48  --gc_record_bc_elim                     false
% 7.67/1.48  
% 7.67/1.48  ------ Preprocessing Options
% 7.67/1.48  
% 7.67/1.48  --preprocessing_flag                    true
% 7.67/1.48  --time_out_prep_mult                    0.1
% 7.67/1.48  --splitting_mode                        input
% 7.67/1.48  --splitting_grd                         true
% 7.67/1.48  --splitting_cvd                         false
% 7.67/1.48  --splitting_cvd_svl                     false
% 7.67/1.48  --splitting_nvd                         32
% 7.67/1.48  --sub_typing                            true
% 7.67/1.48  --prep_gs_sim                           true
% 7.67/1.48  --prep_unflatten                        true
% 7.67/1.48  --prep_res_sim                          true
% 7.67/1.48  --prep_upred                            true
% 7.67/1.48  --prep_sem_filter                       exhaustive
% 7.67/1.48  --prep_sem_filter_out                   false
% 7.67/1.48  --pred_elim                             true
% 7.67/1.48  --res_sim_input                         true
% 7.67/1.48  --eq_ax_congr_red                       true
% 7.67/1.48  --pure_diseq_elim                       true
% 7.67/1.48  --brand_transform                       false
% 7.67/1.48  --non_eq_to_eq                          false
% 7.67/1.48  --prep_def_merge                        true
% 7.67/1.48  --prep_def_merge_prop_impl              false
% 7.67/1.48  --prep_def_merge_mbd                    true
% 7.67/1.48  --prep_def_merge_tr_red                 false
% 7.67/1.48  --prep_def_merge_tr_cl                  false
% 7.67/1.48  --smt_preprocessing                     true
% 7.67/1.48  --smt_ac_axioms                         fast
% 7.67/1.48  --preprocessed_out                      false
% 7.67/1.48  --preprocessed_stats                    false
% 7.67/1.48  
% 7.67/1.48  ------ Abstraction refinement Options
% 7.67/1.48  
% 7.67/1.48  --abstr_ref                             []
% 7.67/1.48  --abstr_ref_prep                        false
% 7.67/1.48  --abstr_ref_until_sat                   false
% 7.67/1.48  --abstr_ref_sig_restrict                funpre
% 7.67/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.67/1.48  --abstr_ref_under                       []
% 7.67/1.48  
% 7.67/1.48  ------ SAT Options
% 7.67/1.48  
% 7.67/1.48  --sat_mode                              false
% 7.67/1.48  --sat_fm_restart_options                ""
% 7.67/1.48  --sat_gr_def                            false
% 7.67/1.48  --sat_epr_types                         true
% 7.67/1.48  --sat_non_cyclic_types                  false
% 7.67/1.48  --sat_finite_models                     false
% 7.67/1.48  --sat_fm_lemmas                         false
% 7.67/1.48  --sat_fm_prep                           false
% 7.67/1.48  --sat_fm_uc_incr                        true
% 7.67/1.48  --sat_out_model                         small
% 7.67/1.48  --sat_out_clauses                       false
% 7.67/1.48  
% 7.67/1.48  ------ QBF Options
% 7.67/1.48  
% 7.67/1.48  --qbf_mode                              false
% 7.67/1.48  --qbf_elim_univ                         false
% 7.67/1.48  --qbf_dom_inst                          none
% 7.67/1.48  --qbf_dom_pre_inst                      false
% 7.67/1.48  --qbf_sk_in                             false
% 7.67/1.48  --qbf_pred_elim                         true
% 7.67/1.48  --qbf_split                             512
% 7.67/1.48  
% 7.67/1.48  ------ BMC1 Options
% 7.67/1.48  
% 7.67/1.48  --bmc1_incremental                      false
% 7.67/1.48  --bmc1_axioms                           reachable_all
% 7.67/1.48  --bmc1_min_bound                        0
% 7.67/1.48  --bmc1_max_bound                        -1
% 7.67/1.48  --bmc1_max_bound_default                -1
% 7.67/1.48  --bmc1_symbol_reachability              true
% 7.67/1.48  --bmc1_property_lemmas                  false
% 7.67/1.48  --bmc1_k_induction                      false
% 7.67/1.48  --bmc1_non_equiv_states                 false
% 7.67/1.48  --bmc1_deadlock                         false
% 7.67/1.48  --bmc1_ucm                              false
% 7.67/1.48  --bmc1_add_unsat_core                   none
% 7.67/1.48  --bmc1_unsat_core_children              false
% 7.67/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.67/1.48  --bmc1_out_stat                         full
% 7.67/1.48  --bmc1_ground_init                      false
% 7.67/1.48  --bmc1_pre_inst_next_state              false
% 7.67/1.48  --bmc1_pre_inst_state                   false
% 7.67/1.48  --bmc1_pre_inst_reach_state             false
% 7.67/1.48  --bmc1_out_unsat_core                   false
% 7.67/1.48  --bmc1_aig_witness_out                  false
% 7.67/1.48  --bmc1_verbose                          false
% 7.67/1.48  --bmc1_dump_clauses_tptp                false
% 7.67/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.67/1.48  --bmc1_dump_file                        -
% 7.67/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.67/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.67/1.48  --bmc1_ucm_extend_mode                  1
% 7.67/1.48  --bmc1_ucm_init_mode                    2
% 7.67/1.48  --bmc1_ucm_cone_mode                    none
% 7.67/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.67/1.48  --bmc1_ucm_relax_model                  4
% 7.67/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.67/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.67/1.48  --bmc1_ucm_layered_model                none
% 7.67/1.48  --bmc1_ucm_max_lemma_size               10
% 7.67/1.48  
% 7.67/1.48  ------ AIG Options
% 7.67/1.48  
% 7.67/1.48  --aig_mode                              false
% 7.67/1.48  
% 7.67/1.48  ------ Instantiation Options
% 7.67/1.48  
% 7.67/1.48  --instantiation_flag                    true
% 7.67/1.48  --inst_sos_flag                         false
% 7.67/1.48  --inst_sos_phase                        true
% 7.67/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.67/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.67/1.48  --inst_lit_sel_side                     none
% 7.67/1.48  --inst_solver_per_active                1400
% 7.67/1.48  --inst_solver_calls_frac                1.
% 7.67/1.48  --inst_passive_queue_type               priority_queues
% 7.67/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.67/1.48  --inst_passive_queues_freq              [25;2]
% 7.67/1.48  --inst_dismatching                      true
% 7.67/1.48  --inst_eager_unprocessed_to_passive     true
% 7.67/1.48  --inst_prop_sim_given                   true
% 7.67/1.48  --inst_prop_sim_new                     false
% 7.67/1.48  --inst_subs_new                         false
% 7.67/1.48  --inst_eq_res_simp                      false
% 7.67/1.48  --inst_subs_given                       false
% 7.67/1.48  --inst_orphan_elimination               true
% 7.67/1.48  --inst_learning_loop_flag               true
% 7.67/1.48  --inst_learning_start                   3000
% 7.67/1.48  --inst_learning_factor                  2
% 7.67/1.48  --inst_start_prop_sim_after_learn       3
% 7.67/1.48  --inst_sel_renew                        solver
% 7.67/1.48  --inst_lit_activity_flag                true
% 7.67/1.48  --inst_restr_to_given                   false
% 7.67/1.48  --inst_activity_threshold               500
% 7.67/1.48  --inst_out_proof                        true
% 7.67/1.48  
% 7.67/1.48  ------ Resolution Options
% 7.67/1.48  
% 7.67/1.48  --resolution_flag                       false
% 7.67/1.48  --res_lit_sel                           adaptive
% 7.67/1.48  --res_lit_sel_side                      none
% 7.67/1.48  --res_ordering                          kbo
% 7.67/1.48  --res_to_prop_solver                    active
% 7.67/1.48  --res_prop_simpl_new                    false
% 7.67/1.48  --res_prop_simpl_given                  true
% 7.67/1.48  --res_passive_queue_type                priority_queues
% 7.67/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.67/1.48  --res_passive_queues_freq               [15;5]
% 7.67/1.48  --res_forward_subs                      full
% 7.67/1.48  --res_backward_subs                     full
% 7.67/1.48  --res_forward_subs_resolution           true
% 7.67/1.48  --res_backward_subs_resolution          true
% 7.67/1.48  --res_orphan_elimination                true
% 7.67/1.48  --res_time_limit                        2.
% 7.67/1.48  --res_out_proof                         true
% 7.67/1.48  
% 7.67/1.48  ------ Superposition Options
% 7.67/1.48  
% 7.67/1.48  --superposition_flag                    true
% 7.67/1.48  --sup_passive_queue_type                priority_queues
% 7.67/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.67/1.48  --sup_passive_queues_freq               [8;1;4]
% 7.67/1.48  --demod_completeness_check              fast
% 7.67/1.48  --demod_use_ground                      true
% 7.67/1.48  --sup_to_prop_solver                    passive
% 7.67/1.48  --sup_prop_simpl_new                    true
% 7.67/1.48  --sup_prop_simpl_given                  true
% 7.67/1.48  --sup_fun_splitting                     false
% 7.67/1.48  --sup_smt_interval                      50000
% 7.67/1.48  
% 7.67/1.48  ------ Superposition Simplification Setup
% 7.67/1.48  
% 7.67/1.48  --sup_indices_passive                   []
% 7.67/1.48  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.67/1.48  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.67/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.67/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.67/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.67/1.48  --sup_full_bw                           [BwDemod]
% 7.67/1.48  --sup_immed_triv                        [TrivRules]
% 7.67/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.67/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.67/1.48  --sup_immed_bw_main                     []
% 7.67/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.67/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.67/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.67/1.48  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.67/1.48  
% 7.67/1.48  ------ Combination Options
% 7.67/1.48  
% 7.67/1.48  --comb_res_mult                         3
% 7.67/1.48  --comb_sup_mult                         2
% 7.67/1.48  --comb_inst_mult                        10
% 7.67/1.48  
% 7.67/1.48  ------ Debug Options
% 7.67/1.48  
% 7.67/1.48  --dbg_backtrace                         false
% 7.67/1.48  --dbg_dump_prop_clauses                 false
% 7.67/1.48  --dbg_dump_prop_clauses_file            -
% 7.67/1.48  --dbg_out_stat                          false
% 7.67/1.48  
% 7.67/1.48  
% 7.67/1.48  
% 7.67/1.48  
% 7.67/1.48  ------ Proving...
% 7.67/1.48  
% 7.67/1.48  
% 7.67/1.48  % SZS status Theorem for theBenchmark.p
% 7.67/1.48  
% 7.67/1.48  % SZS output start CNFRefutation for theBenchmark.p
% 7.67/1.48  
% 7.67/1.48  fof(f5,axiom,(
% 7.67/1.48    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.67/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.67/1.48  
% 7.67/1.48  fof(f55,plain,(
% 7.67/1.48    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 7.67/1.48    inference(nnf_transformation,[],[f5])).
% 7.67/1.48  
% 7.67/1.48  fof(f72,plain,(
% 7.67/1.48    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 7.67/1.48    inference(cnf_transformation,[],[f55])).
% 7.67/1.48  
% 7.67/1.48  fof(f3,axiom,(
% 7.67/1.48    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 7.67/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.67/1.48  
% 7.67/1.48  fof(f53,plain,(
% 7.67/1.48    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 7.67/1.48    inference(nnf_transformation,[],[f3])).
% 7.67/1.48  
% 7.67/1.48  fof(f54,plain,(
% 7.67/1.48    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 7.67/1.48    inference(flattening,[],[f53])).
% 7.67/1.48  
% 7.67/1.48  fof(f68,plain,(
% 7.67/1.48    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 7.67/1.48    inference(cnf_transformation,[],[f54])).
% 7.67/1.48  
% 7.67/1.48  fof(f118,plain,(
% 7.67/1.48    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 7.67/1.48    inference(equality_resolution,[],[f68])).
% 7.67/1.48  
% 7.67/1.48  fof(f20,axiom,(
% 7.67/1.48    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_partfun1(X2,X0)))),
% 7.67/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.67/1.48  
% 7.67/1.48  fof(f44,plain,(
% 7.67/1.48    ! [X0,X1] : (! [X2] : (v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 7.67/1.48    inference(ennf_transformation,[],[f20])).
% 7.67/1.48  
% 7.67/1.48  fof(f94,plain,(
% 7.67/1.48    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0)) )),
% 7.67/1.48    inference(cnf_transformation,[],[f44])).
% 7.67/1.48  
% 7.67/1.48  fof(f19,axiom,(
% 7.67/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_partfun1(X2,X0) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 7.67/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.67/1.48  
% 7.67/1.48  fof(f42,plain,(
% 7.67/1.48    ! [X0,X1,X2] : (((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~v1_partfun1(X2,X0) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.67/1.48    inference(ennf_transformation,[],[f19])).
% 7.67/1.48  
% 7.67/1.48  fof(f43,plain,(
% 7.67/1.48    ! [X0,X1,X2] : ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.67/1.48    inference(flattening,[],[f42])).
% 7.67/1.48  
% 7.67/1.48  fof(f93,plain,(
% 7.67/1.48    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.67/1.48    inference(cnf_transformation,[],[f43])).
% 7.67/1.48  
% 7.67/1.48  fof(f21,axiom,(
% 7.67/1.48    ! [X0,X1] : ? [X2] : (v5_relat_1(X2,X1) & v4_relat_1(X2,X0) & v1_relat_1(X2) & v1_xboole_0(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.67/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.67/1.48  
% 7.67/1.48  fof(f59,plain,(
% 7.67/1.48    ! [X1,X0] : (? [X2] : (v5_relat_1(X2,X1) & v4_relat_1(X2,X0) & v1_relat_1(X2) & v1_xboole_0(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (v5_relat_1(sK0(X0,X1),X1) & v4_relat_1(sK0(X0,X1),X0) & v1_relat_1(sK0(X0,X1)) & v1_xboole_0(sK0(X0,X1)) & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 7.67/1.48    introduced(choice_axiom,[])).
% 7.67/1.48  
% 7.67/1.48  fof(f60,plain,(
% 7.67/1.48    ! [X0,X1] : (v5_relat_1(sK0(X0,X1),X1) & v4_relat_1(sK0(X0,X1),X0) & v1_relat_1(sK0(X0,X1)) & v1_xboole_0(sK0(X0,X1)) & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.67/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f59])).
% 7.67/1.48  
% 7.67/1.48  fof(f96,plain,(
% 7.67/1.48    ( ! [X0,X1] : (v1_xboole_0(sK0(X0,X1))) )),
% 7.67/1.48    inference(cnf_transformation,[],[f60])).
% 7.67/1.48  
% 7.67/1.48  fof(f17,axiom,(
% 7.67/1.48    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_xboole_0(X2)))),
% 7.67/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.67/1.48  
% 7.67/1.48  fof(f40,plain,(
% 7.67/1.48    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 7.67/1.48    inference(ennf_transformation,[],[f17])).
% 7.67/1.48  
% 7.67/1.48  fof(f90,plain,(
% 7.67/1.48    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0)) )),
% 7.67/1.48    inference(cnf_transformation,[],[f40])).
% 7.67/1.48  
% 7.67/1.48  fof(f4,axiom,(
% 7.67/1.48    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 7.67/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.67/1.48  
% 7.67/1.48  fof(f70,plain,(
% 7.67/1.48    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 7.67/1.48    inference(cnf_transformation,[],[f4])).
% 7.67/1.48  
% 7.67/1.48  fof(f14,axiom,(
% 7.67/1.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0))))),
% 7.67/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.67/1.48  
% 7.67/1.48  fof(f36,plain,(
% 7.67/1.48    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.67/1.48    inference(ennf_transformation,[],[f14])).
% 7.67/1.48  
% 7.67/1.48  fof(f37,plain,(
% 7.67/1.48    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.67/1.48    inference(flattening,[],[f36])).
% 7.67/1.48  
% 7.67/1.48  fof(f86,plain,(
% 7.67/1.48    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.67/1.48    inference(cnf_transformation,[],[f37])).
% 7.67/1.48  
% 7.67/1.48  fof(f24,conjecture,(
% 7.67/1.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 7.67/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.67/1.48  
% 7.67/1.48  fof(f25,negated_conjecture,(
% 7.67/1.48    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 7.67/1.48    inference(negated_conjecture,[],[f24])).
% 7.67/1.48  
% 7.67/1.48  fof(f49,plain,(
% 7.67/1.48    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 7.67/1.48    inference(ennf_transformation,[],[f25])).
% 7.67/1.48  
% 7.67/1.48  fof(f50,plain,(
% 7.67/1.48    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 7.67/1.48    inference(flattening,[],[f49])).
% 7.67/1.48  
% 7.67/1.48  fof(f61,plain,(
% 7.67/1.48    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))) & k2_relset_1(sK1,sK2,sK3) = sK2 & v2_funct_1(sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3))),
% 7.67/1.48    introduced(choice_axiom,[])).
% 7.67/1.48  
% 7.67/1.48  fof(f62,plain,(
% 7.67/1.48    (~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))) & k2_relset_1(sK1,sK2,sK3) = sK2 & v2_funct_1(sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)),
% 7.67/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f50,f61])).
% 7.67/1.48  
% 7.67/1.48  fof(f112,plain,(
% 7.67/1.48    v2_funct_1(sK3)),
% 7.67/1.48    inference(cnf_transformation,[],[f62])).
% 7.67/1.48  
% 7.67/1.48  fof(f109,plain,(
% 7.67/1.48    v1_funct_1(sK3)),
% 7.67/1.48    inference(cnf_transformation,[],[f62])).
% 7.67/1.48  
% 7.67/1.48  fof(f111,plain,(
% 7.67/1.48    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 7.67/1.48    inference(cnf_transformation,[],[f62])).
% 7.67/1.48  
% 7.67/1.48  fof(f15,axiom,(
% 7.67/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 7.67/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.67/1.48  
% 7.67/1.48  fof(f38,plain,(
% 7.67/1.48    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.67/1.48    inference(ennf_transformation,[],[f15])).
% 7.67/1.48  
% 7.67/1.48  fof(f87,plain,(
% 7.67/1.48    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.67/1.48    inference(cnf_transformation,[],[f38])).
% 7.67/1.48  
% 7.67/1.48  fof(f22,axiom,(
% 7.67/1.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 7.67/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.67/1.48  
% 7.67/1.48  fof(f45,plain,(
% 7.67/1.48    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.67/1.48    inference(ennf_transformation,[],[f22])).
% 7.67/1.48  
% 7.67/1.48  fof(f46,plain,(
% 7.67/1.48    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.67/1.48    inference(flattening,[],[f45])).
% 7.67/1.48  
% 7.67/1.48  fof(f102,plain,(
% 7.67/1.48    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.67/1.48    inference(cnf_transformation,[],[f46])).
% 7.67/1.48  
% 7.67/1.48  fof(f18,axiom,(
% 7.67/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 7.67/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.67/1.48  
% 7.67/1.48  fof(f41,plain,(
% 7.67/1.48    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.67/1.48    inference(ennf_transformation,[],[f18])).
% 7.67/1.48  
% 7.67/1.48  fof(f91,plain,(
% 7.67/1.48    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.67/1.48    inference(cnf_transformation,[],[f41])).
% 7.67/1.48  
% 7.67/1.48  fof(f113,plain,(
% 7.67/1.48    k2_relset_1(sK1,sK2,sK3) = sK2),
% 7.67/1.48    inference(cnf_transformation,[],[f62])).
% 7.67/1.48  
% 7.67/1.48  fof(f85,plain,(
% 7.67/1.48    ( ! [X0] : (k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.67/1.48    inference(cnf_transformation,[],[f37])).
% 7.67/1.48  
% 7.67/1.48  fof(f13,axiom,(
% 7.67/1.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 7.67/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.67/1.48  
% 7.67/1.48  fof(f34,plain,(
% 7.67/1.48    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.67/1.48    inference(ennf_transformation,[],[f13])).
% 7.67/1.48  
% 7.67/1.48  fof(f35,plain,(
% 7.67/1.48    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.67/1.48    inference(flattening,[],[f34])).
% 7.67/1.48  
% 7.67/1.48  fof(f84,plain,(
% 7.67/1.48    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.67/1.48    inference(cnf_transformation,[],[f35])).
% 7.67/1.48  
% 7.67/1.48  fof(f83,plain,(
% 7.67/1.48    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.67/1.48    inference(cnf_transformation,[],[f35])).
% 7.67/1.48  
% 7.67/1.48  fof(f23,axiom,(
% 7.67/1.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X1,X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 7.67/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.67/1.48  
% 7.67/1.48  fof(f47,plain,(
% 7.67/1.48    ! [X0,X1,X2,X3] : ((((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | ~r1_tarski(X1,X2)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 7.67/1.48    inference(ennf_transformation,[],[f23])).
% 7.67/1.48  
% 7.67/1.48  fof(f48,plain,(
% 7.67/1.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~r1_tarski(X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 7.67/1.48    inference(flattening,[],[f47])).
% 7.67/1.48  
% 7.67/1.48  fof(f105,plain,(
% 7.67/1.48    ( ! [X2,X0,X3,X1] : (v1_funct_2(X3,X0,X2) | k1_xboole_0 = X1 | ~r1_tarski(X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 7.67/1.48    inference(cnf_transformation,[],[f48])).
% 7.67/1.48  
% 7.67/1.48  fof(f101,plain,(
% 7.67/1.48    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.67/1.48    inference(cnf_transformation,[],[f46])).
% 7.67/1.48  
% 7.67/1.48  fof(f107,plain,(
% 7.67/1.48    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | k1_xboole_0 = X1 | ~r1_tarski(X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 7.67/1.48    inference(cnf_transformation,[],[f48])).
% 7.67/1.48  
% 7.67/1.48  fof(f114,plain,(
% 7.67/1.48    ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))),
% 7.67/1.48    inference(cnf_transformation,[],[f62])).
% 7.67/1.48  
% 7.67/1.48  fof(f16,axiom,(
% 7.67/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 7.67/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.67/1.48  
% 7.67/1.48  fof(f39,plain,(
% 7.67/1.48    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.67/1.48    inference(ennf_transformation,[],[f16])).
% 7.67/1.48  
% 7.67/1.48  fof(f88,plain,(
% 7.67/1.48    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.67/1.48    inference(cnf_transformation,[],[f39])).
% 7.67/1.48  
% 7.67/1.48  fof(f8,axiom,(
% 7.67/1.48    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 7.67/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.67/1.48  
% 7.67/1.48  fof(f29,plain,(
% 7.67/1.48    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.67/1.48    inference(ennf_transformation,[],[f8])).
% 7.67/1.48  
% 7.67/1.48  fof(f56,plain,(
% 7.67/1.48    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 7.67/1.48    inference(nnf_transformation,[],[f29])).
% 7.67/1.48  
% 7.67/1.48  fof(f74,plain,(
% 7.67/1.48    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.67/1.48    inference(cnf_transformation,[],[f56])).
% 7.67/1.48  
% 7.67/1.48  fof(f12,axiom,(
% 7.67/1.48    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 7.67/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.67/1.48  
% 7.67/1.48  fof(f33,plain,(
% 7.67/1.48    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 7.67/1.48    inference(ennf_transformation,[],[f12])).
% 7.67/1.48  
% 7.67/1.48  fof(f58,plain,(
% 7.67/1.48    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 7.67/1.48    inference(nnf_transformation,[],[f33])).
% 7.67/1.48  
% 7.67/1.48  fof(f82,plain,(
% 7.67/1.48    ( ! [X0] : (k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 7.67/1.48    inference(cnf_transformation,[],[f58])).
% 7.67/1.48  
% 7.67/1.48  fof(f81,plain,(
% 7.67/1.48    ( ! [X0] : (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 7.67/1.48    inference(cnf_transformation,[],[f58])).
% 7.67/1.48  
% 7.67/1.48  fof(f11,axiom,(
% 7.67/1.48    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 7.67/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.67/1.48  
% 7.67/1.48  fof(f31,plain,(
% 7.67/1.48    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 7.67/1.48    inference(ennf_transformation,[],[f11])).
% 7.67/1.48  
% 7.67/1.48  fof(f32,plain,(
% 7.67/1.48    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 7.67/1.48    inference(flattening,[],[f31])).
% 7.67/1.48  
% 7.67/1.48  fof(f80,plain,(
% 7.67/1.48    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 7.67/1.48    inference(cnf_transformation,[],[f32])).
% 7.67/1.48  
% 7.67/1.48  fof(f79,plain,(
% 7.67/1.48    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 7.67/1.48    inference(cnf_transformation,[],[f32])).
% 7.67/1.48  
% 7.67/1.48  fof(f71,plain,(
% 7.67/1.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 7.67/1.48    inference(cnf_transformation,[],[f55])).
% 7.67/1.48  
% 7.67/1.48  cnf(c_8,plain,
% 7.67/1.48      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.67/1.48      inference(cnf_transformation,[],[f72]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_1913,plain,
% 7.67/1.48      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 7.67/1.48      | r1_tarski(X0,X1) != iProver_top ),
% 7.67/1.48      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_5,plain,
% 7.67/1.48      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 7.67/1.48      inference(cnf_transformation,[],[f118]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_31,plain,
% 7.67/1.48      ( v1_partfun1(X0,X1)
% 7.67/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.67/1.48      | ~ v1_xboole_0(X1) ),
% 7.67/1.48      inference(cnf_transformation,[],[f94]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_29,plain,
% 7.67/1.48      ( v1_funct_2(X0,X1,X2)
% 7.67/1.48      | ~ v1_partfun1(X0,X1)
% 7.67/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.67/1.48      | ~ v1_funct_1(X0) ),
% 7.67/1.48      inference(cnf_transformation,[],[f93]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_576,plain,
% 7.67/1.48      ( v1_funct_2(X0,X1,X2)
% 7.67/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.67/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 7.67/1.48      | ~ v1_xboole_0(X1)
% 7.67/1.48      | ~ v1_funct_1(X0) ),
% 7.67/1.48      inference(resolution,[status(thm)],[c_31,c_29]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_580,plain,
% 7.67/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.67/1.48      | v1_funct_2(X0,X1,X2)
% 7.67/1.48      | ~ v1_xboole_0(X1)
% 7.67/1.48      | ~ v1_funct_1(X0) ),
% 7.67/1.48      inference(global_propositional_subsumption,
% 7.67/1.48                [status(thm)],
% 7.67/1.48                [c_576,c_31,c_29]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_581,plain,
% 7.67/1.48      ( v1_funct_2(X0,X1,X2)
% 7.67/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.67/1.48      | ~ v1_xboole_0(X1)
% 7.67/1.48      | ~ v1_funct_1(X0) ),
% 7.67/1.48      inference(renaming,[status(thm)],[c_580]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_1883,plain,
% 7.67/1.48      ( v1_funct_2(X0,X1,X2) = iProver_top
% 7.67/1.48      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.67/1.48      | v1_xboole_0(X1) != iProver_top
% 7.67/1.48      | v1_funct_1(X0) != iProver_top ),
% 7.67/1.48      inference(predicate_to_equality,[status(thm)],[c_581]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_2844,plain,
% 7.67/1.48      ( v1_funct_2(X0,k1_xboole_0,X1) = iProver_top
% 7.67/1.48      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 7.67/1.48      | v1_xboole_0(k1_xboole_0) != iProver_top
% 7.67/1.48      | v1_funct_1(X0) != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_5,c_1883]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_35,plain,
% 7.67/1.48      ( v1_xboole_0(sK0(X0,X1)) ),
% 7.67/1.48      inference(cnf_transformation,[],[f96]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_73,plain,
% 7.67/1.48      ( v1_xboole_0(sK0(X0,X1)) = iProver_top ),
% 7.67/1.48      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_27,plain,
% 7.67/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.67/1.48      | ~ v1_xboole_0(X1)
% 7.67/1.48      | v1_xboole_0(X0) ),
% 7.67/1.48      inference(cnf_transformation,[],[f90]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_2348,plain,
% 7.67/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0(X1,X2),X3)))
% 7.67/1.48      | v1_xboole_0(X0)
% 7.67/1.48      | ~ v1_xboole_0(sK0(X1,X2)) ),
% 7.67/1.48      inference(instantiation,[status(thm)],[c_27]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_2969,plain,
% 7.67/1.48      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0(X0,X1),X2)))
% 7.67/1.48      | ~ v1_xboole_0(sK0(X0,X1))
% 7.67/1.48      | v1_xboole_0(k1_xboole_0) ),
% 7.67/1.48      inference(instantiation,[status(thm)],[c_2348]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_2971,plain,
% 7.67/1.48      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0(X0,X1),X2))) != iProver_top
% 7.67/1.48      | v1_xboole_0(sK0(X0,X1)) != iProver_top
% 7.67/1.48      | v1_xboole_0(k1_xboole_0) = iProver_top ),
% 7.67/1.48      inference(predicate_to_equality,[status(thm)],[c_2969]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_7,plain,
% 7.67/1.48      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 7.67/1.48      inference(cnf_transformation,[],[f70]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_2224,plain,
% 7.67/1.48      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 7.67/1.48      inference(instantiation,[status(thm)],[c_7]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_2970,plain,
% 7.67/1.48      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0(X0,X1),X2))) ),
% 7.67/1.48      inference(instantiation,[status(thm)],[c_2224]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_2973,plain,
% 7.67/1.48      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0(X0,X1),X2))) = iProver_top ),
% 7.67/1.48      inference(predicate_to_equality,[status(thm)],[c_2970]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_9131,plain,
% 7.67/1.48      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 7.67/1.48      | v1_funct_2(X0,k1_xboole_0,X1) = iProver_top
% 7.67/1.48      | v1_funct_1(X0) != iProver_top ),
% 7.67/1.48      inference(global_propositional_subsumption,
% 7.67/1.48                [status(thm)],
% 7.67/1.48                [c_2844,c_73,c_2971,c_2973]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_9132,plain,
% 7.67/1.48      ( v1_funct_2(X0,k1_xboole_0,X1) = iProver_top
% 7.67/1.48      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 7.67/1.48      | v1_funct_1(X0) != iProver_top ),
% 7.67/1.48      inference(renaming,[status(thm)],[c_9131]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_9141,plain,
% 7.67/1.48      ( v1_funct_2(X0,k1_xboole_0,X1) = iProver_top
% 7.67/1.48      | r1_tarski(X0,k1_xboole_0) != iProver_top
% 7.67/1.48      | v1_funct_1(X0) != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_1913,c_9132]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_22,plain,
% 7.67/1.48      ( ~ v2_funct_1(X0)
% 7.67/1.48      | ~ v1_funct_1(X0)
% 7.67/1.48      | ~ v1_relat_1(X0)
% 7.67/1.48      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 7.67/1.48      inference(cnf_transformation,[],[f86]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_48,negated_conjecture,
% 7.67/1.48      ( v2_funct_1(sK3) ),
% 7.67/1.48      inference(cnf_transformation,[],[f112]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_616,plain,
% 7.67/1.48      ( ~ v1_funct_1(X0)
% 7.67/1.48      | ~ v1_relat_1(X0)
% 7.67/1.48      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 7.67/1.48      | sK3 != X0 ),
% 7.67/1.48      inference(resolution_lifted,[status(thm)],[c_22,c_48]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_617,plain,
% 7.67/1.48      ( ~ v1_funct_1(sK3)
% 7.67/1.48      | ~ v1_relat_1(sK3)
% 7.67/1.48      | k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
% 7.67/1.48      inference(unflattening,[status(thm)],[c_616]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_51,negated_conjecture,
% 7.67/1.48      ( v1_funct_1(sK3) ),
% 7.67/1.48      inference(cnf_transformation,[],[f109]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_619,plain,
% 7.67/1.48      ( ~ v1_relat_1(sK3)
% 7.67/1.48      | k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
% 7.67/1.48      inference(global_propositional_subsumption,
% 7.67/1.48                [status(thm)],
% 7.67/1.48                [c_617,c_51]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_1881,plain,
% 7.67/1.48      ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3)
% 7.67/1.48      | v1_relat_1(sK3) != iProver_top ),
% 7.67/1.48      inference(predicate_to_equality,[status(thm)],[c_619]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_49,negated_conjecture,
% 7.67/1.48      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 7.67/1.48      inference(cnf_transformation,[],[f111]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_24,plain,
% 7.67/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.67/1.48      | v1_relat_1(X0) ),
% 7.67/1.48      inference(cnf_transformation,[],[f87]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_2234,plain,
% 7.67/1.48      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 7.67/1.48      | v1_relat_1(sK3) ),
% 7.67/1.48      inference(instantiation,[status(thm)],[c_24]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_2251,plain,
% 7.67/1.48      ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
% 7.67/1.48      inference(global_propositional_subsumption,
% 7.67/1.48                [status(thm)],
% 7.67/1.48                [c_1881,c_51,c_49,c_617,c_2234]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_37,plain,
% 7.67/1.48      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 7.67/1.48      | ~ v1_funct_1(X0)
% 7.67/1.48      | ~ v1_relat_1(X0) ),
% 7.67/1.48      inference(cnf_transformation,[],[f102]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_1893,plain,
% 7.67/1.48      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
% 7.67/1.48      | v1_funct_1(X0) != iProver_top
% 7.67/1.48      | v1_relat_1(X0) != iProver_top ),
% 7.67/1.48      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_6255,plain,
% 7.67/1.48      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK3)),k1_relat_1(sK3)))) = iProver_top
% 7.67/1.48      | v1_funct_1(k2_funct_1(sK3)) != iProver_top
% 7.67/1.48      | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_2251,c_1893]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_1886,plain,
% 7.67/1.48      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 7.67/1.48      inference(predicate_to_equality,[status(thm)],[c_49]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_28,plain,
% 7.67/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.67/1.48      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 7.67/1.48      inference(cnf_transformation,[],[f91]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_1898,plain,
% 7.67/1.48      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 7.67/1.48      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.67/1.48      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_5863,plain,
% 7.67/1.48      ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_1886,c_1898]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_47,negated_conjecture,
% 7.67/1.48      ( k2_relset_1(sK1,sK2,sK3) = sK2 ),
% 7.67/1.48      inference(cnf_transformation,[],[f113]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_5882,plain,
% 7.67/1.48      ( k2_relat_1(sK3) = sK2 ),
% 7.67/1.48      inference(light_normalisation,[status(thm)],[c_5863,c_47]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_23,plain,
% 7.67/1.48      ( ~ v2_funct_1(X0)
% 7.67/1.48      | ~ v1_funct_1(X0)
% 7.67/1.48      | ~ v1_relat_1(X0)
% 7.67/1.48      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 7.67/1.48      inference(cnf_transformation,[],[f85]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_602,plain,
% 7.67/1.48      ( ~ v1_funct_1(X0)
% 7.67/1.48      | ~ v1_relat_1(X0)
% 7.67/1.48      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 7.67/1.48      | sK3 != X0 ),
% 7.67/1.48      inference(resolution_lifted,[status(thm)],[c_23,c_48]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_603,plain,
% 7.67/1.48      ( ~ v1_funct_1(sK3)
% 7.67/1.48      | ~ v1_relat_1(sK3)
% 7.67/1.48      | k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
% 7.67/1.48      inference(unflattening,[status(thm)],[c_602]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_605,plain,
% 7.67/1.48      ( ~ v1_relat_1(sK3)
% 7.67/1.48      | k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
% 7.67/1.48      inference(global_propositional_subsumption,
% 7.67/1.48                [status(thm)],
% 7.67/1.48                [c_603,c_51]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_1882,plain,
% 7.67/1.48      ( k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3)
% 7.67/1.48      | v1_relat_1(sK3) != iProver_top ),
% 7.67/1.48      inference(predicate_to_equality,[status(thm)],[c_605]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_2278,plain,
% 7.67/1.48      ( k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
% 7.67/1.48      inference(global_propositional_subsumption,
% 7.67/1.48                [status(thm)],
% 7.67/1.48                [c_1882,c_51,c_49,c_603,c_2234]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_5976,plain,
% 7.67/1.48      ( k1_relat_1(k2_funct_1(sK3)) = sK2 ),
% 7.67/1.48      inference(demodulation,[status(thm)],[c_5882,c_2278]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_6316,plain,
% 7.67/1.48      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3)))) = iProver_top
% 7.67/1.48      | v1_funct_1(k2_funct_1(sK3)) != iProver_top
% 7.67/1.48      | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
% 7.67/1.48      inference(light_normalisation,[status(thm)],[c_6255,c_5976]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_52,plain,
% 7.67/1.48      ( v1_funct_1(sK3) = iProver_top ),
% 7.67/1.48      inference(predicate_to_equality,[status(thm)],[c_51]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_54,plain,
% 7.67/1.48      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 7.67/1.48      inference(predicate_to_equality,[status(thm)],[c_49]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_20,plain,
% 7.67/1.48      ( ~ v1_funct_1(X0)
% 7.67/1.48      | v1_funct_1(k2_funct_1(X0))
% 7.67/1.48      | ~ v1_relat_1(X0) ),
% 7.67/1.48      inference(cnf_transformation,[],[f84]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_2213,plain,
% 7.67/1.48      ( v1_funct_1(k2_funct_1(sK3))
% 7.67/1.48      | ~ v1_funct_1(sK3)
% 7.67/1.48      | ~ v1_relat_1(sK3) ),
% 7.67/1.48      inference(instantiation,[status(thm)],[c_20]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_2214,plain,
% 7.67/1.48      ( v1_funct_1(k2_funct_1(sK3)) = iProver_top
% 7.67/1.48      | v1_funct_1(sK3) != iProver_top
% 7.67/1.48      | v1_relat_1(sK3) != iProver_top ),
% 7.67/1.48      inference(predicate_to_equality,[status(thm)],[c_2213]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_21,plain,
% 7.67/1.48      ( ~ v1_funct_1(X0)
% 7.67/1.48      | ~ v1_relat_1(X0)
% 7.67/1.48      | v1_relat_1(k2_funct_1(X0)) ),
% 7.67/1.48      inference(cnf_transformation,[],[f83]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_2216,plain,
% 7.67/1.48      ( ~ v1_funct_1(sK3)
% 7.67/1.48      | v1_relat_1(k2_funct_1(sK3))
% 7.67/1.48      | ~ v1_relat_1(sK3) ),
% 7.67/1.48      inference(instantiation,[status(thm)],[c_21]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_2217,plain,
% 7.67/1.48      ( v1_funct_1(sK3) != iProver_top
% 7.67/1.48      | v1_relat_1(k2_funct_1(sK3)) = iProver_top
% 7.67/1.48      | v1_relat_1(sK3) != iProver_top ),
% 7.67/1.48      inference(predicate_to_equality,[status(thm)],[c_2216]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_2235,plain,
% 7.67/1.48      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 7.67/1.48      | v1_relat_1(sK3) = iProver_top ),
% 7.67/1.48      inference(predicate_to_equality,[status(thm)],[c_2234]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_7179,plain,
% 7.67/1.48      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3)))) = iProver_top ),
% 7.67/1.48      inference(global_propositional_subsumption,
% 7.67/1.48                [status(thm)],
% 7.67/1.48                [c_6316,c_52,c_54,c_2214,c_2217,c_2235]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_43,plain,
% 7.67/1.48      ( ~ v1_funct_2(X0,X1,X2)
% 7.67/1.48      | v1_funct_2(X0,X1,X3)
% 7.67/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.67/1.48      | ~ r1_tarski(X2,X3)
% 7.67/1.48      | ~ v1_funct_1(X0)
% 7.67/1.48      | k1_xboole_0 = X2 ),
% 7.67/1.48      inference(cnf_transformation,[],[f105]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_1888,plain,
% 7.67/1.48      ( k1_xboole_0 = X0
% 7.67/1.48      | v1_funct_2(X1,X2,X0) != iProver_top
% 7.67/1.48      | v1_funct_2(X1,X2,X3) = iProver_top
% 7.67/1.48      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 7.67/1.48      | r1_tarski(X0,X3) != iProver_top
% 7.67/1.48      | v1_funct_1(X1) != iProver_top ),
% 7.67/1.48      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_7191,plain,
% 7.67/1.48      ( k1_relat_1(sK3) = k1_xboole_0
% 7.67/1.48      | v1_funct_2(k2_funct_1(sK3),sK2,X0) = iProver_top
% 7.67/1.48      | v1_funct_2(k2_funct_1(sK3),sK2,k1_relat_1(sK3)) != iProver_top
% 7.67/1.48      | r1_tarski(k1_relat_1(sK3),X0) != iProver_top
% 7.67/1.48      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_7179,c_1888]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_38,plain,
% 7.67/1.48      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
% 7.67/1.48      | ~ v1_funct_1(X0)
% 7.67/1.48      | ~ v1_relat_1(X0) ),
% 7.67/1.48      inference(cnf_transformation,[],[f101]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_1892,plain,
% 7.67/1.48      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) = iProver_top
% 7.67/1.48      | v1_funct_1(X0) != iProver_top
% 7.67/1.48      | v1_relat_1(X0) != iProver_top ),
% 7.67/1.48      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_6009,plain,
% 7.67/1.48      ( v1_funct_2(k2_funct_1(sK3),sK2,k2_relat_1(k2_funct_1(sK3))) = iProver_top
% 7.67/1.48      | v1_funct_1(k2_funct_1(sK3)) != iProver_top
% 7.67/1.48      | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_5976,c_1892]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_6014,plain,
% 7.67/1.48      ( v1_funct_2(k2_funct_1(sK3),sK2,k1_relat_1(sK3)) = iProver_top
% 7.67/1.48      | v1_funct_1(k2_funct_1(sK3)) != iProver_top
% 7.67/1.48      | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
% 7.67/1.48      inference(light_normalisation,[status(thm)],[c_6009,c_2251]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_24074,plain,
% 7.67/1.48      ( r1_tarski(k1_relat_1(sK3),X0) != iProver_top
% 7.67/1.48      | k1_relat_1(sK3) = k1_xboole_0
% 7.67/1.48      | v1_funct_2(k2_funct_1(sK3),sK2,X0) = iProver_top ),
% 7.67/1.48      inference(global_propositional_subsumption,
% 7.67/1.48                [status(thm)],
% 7.67/1.48                [c_7191,c_52,c_54,c_2214,c_2217,c_2235,c_6014]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_24075,plain,
% 7.67/1.48      ( k1_relat_1(sK3) = k1_xboole_0
% 7.67/1.48      | v1_funct_2(k2_funct_1(sK3),sK2,X0) = iProver_top
% 7.67/1.48      | r1_tarski(k1_relat_1(sK3),X0) != iProver_top ),
% 7.67/1.48      inference(renaming,[status(thm)],[c_24074]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_41,plain,
% 7.67/1.48      ( ~ v1_funct_2(X0,X1,X2)
% 7.67/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.67/1.48      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 7.67/1.48      | ~ r1_tarski(X2,X3)
% 7.67/1.48      | ~ v1_funct_1(X0)
% 7.67/1.48      | k1_xboole_0 = X2 ),
% 7.67/1.48      inference(cnf_transformation,[],[f107]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_1890,plain,
% 7.67/1.48      ( k1_xboole_0 = X0
% 7.67/1.48      | v1_funct_2(X1,X2,X0) != iProver_top
% 7.67/1.48      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 7.67/1.48      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) = iProver_top
% 7.67/1.48      | r1_tarski(X0,X3) != iProver_top
% 7.67/1.48      | v1_funct_1(X1) != iProver_top ),
% 7.67/1.48      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_6262,plain,
% 7.67/1.48      ( k2_relat_1(X0) = k1_xboole_0
% 7.67/1.48      | v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) != iProver_top
% 7.67/1.48      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
% 7.67/1.48      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 7.67/1.48      | v1_funct_1(X0) != iProver_top
% 7.67/1.48      | v1_relat_1(X0) != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_1893,c_1890]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_64,plain,
% 7.67/1.48      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) = iProver_top
% 7.67/1.48      | v1_funct_1(X0) != iProver_top
% 7.67/1.48      | v1_relat_1(X0) != iProver_top ),
% 7.67/1.48      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_29021,plain,
% 7.67/1.48      ( k2_relat_1(X0) = k1_xboole_0
% 7.67/1.48      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
% 7.67/1.48      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 7.67/1.48      | v1_funct_1(X0) != iProver_top
% 7.67/1.48      | v1_relat_1(X0) != iProver_top ),
% 7.67/1.48      inference(global_propositional_subsumption,
% 7.67/1.48                [status(thm)],
% 7.67/1.48                [c_6262,c_64]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_29033,plain,
% 7.67/1.48      ( k2_relat_1(k2_funct_1(sK3)) = k1_xboole_0
% 7.67/1.48      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
% 7.67/1.48      | r1_tarski(k2_relat_1(k2_funct_1(sK3)),X0) != iProver_top
% 7.67/1.48      | v1_funct_1(k2_funct_1(sK3)) != iProver_top
% 7.67/1.48      | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_5976,c_29021]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_29138,plain,
% 7.67/1.48      ( k2_relat_1(k2_funct_1(sK3)) = k1_xboole_0
% 7.67/1.48      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
% 7.67/1.48      | r1_tarski(k1_relat_1(sK3),X0) != iProver_top
% 7.67/1.48      | v1_funct_1(k2_funct_1(sK3)) != iProver_top
% 7.67/1.48      | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
% 7.67/1.48      inference(light_normalisation,[status(thm)],[c_29033,c_2251]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_29139,plain,
% 7.67/1.48      ( k1_relat_1(sK3) = k1_xboole_0
% 7.67/1.48      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
% 7.67/1.48      | r1_tarski(k1_relat_1(sK3),X0) != iProver_top
% 7.67/1.48      | v1_funct_1(k2_funct_1(sK3)) != iProver_top
% 7.67/1.48      | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
% 7.67/1.48      inference(demodulation,[status(thm)],[c_29138,c_2251]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_7190,plain,
% 7.67/1.48      ( k1_relat_1(sK3) = k1_xboole_0
% 7.67/1.48      | v1_funct_2(k2_funct_1(sK3),sK2,k1_relat_1(sK3)) != iProver_top
% 7.67/1.48      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
% 7.67/1.48      | r1_tarski(k1_relat_1(sK3),X0) != iProver_top
% 7.67/1.48      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_7179,c_1890]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_29901,plain,
% 7.67/1.48      ( k1_relat_1(sK3) = k1_xboole_0
% 7.67/1.48      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
% 7.67/1.48      | r1_tarski(k1_relat_1(sK3),X0) != iProver_top ),
% 7.67/1.48      inference(global_propositional_subsumption,
% 7.67/1.48                [status(thm)],
% 7.67/1.48                [c_29139,c_52,c_54,c_2214,c_2217,c_2235,c_6014,c_7190]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_46,negated_conjecture,
% 7.67/1.48      ( ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
% 7.67/1.48      | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 7.67/1.48      | ~ v1_funct_1(k2_funct_1(sK3)) ),
% 7.67/1.48      inference(cnf_transformation,[],[f114]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_1887,plain,
% 7.67/1.48      ( v1_funct_2(k2_funct_1(sK3),sK2,sK1) != iProver_top
% 7.67/1.48      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.67/1.48      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 7.67/1.48      inference(predicate_to_equality,[status(thm)],[c_46]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_56,plain,
% 7.67/1.48      ( v1_funct_2(k2_funct_1(sK3),sK2,sK1) != iProver_top
% 7.67/1.48      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.67/1.48      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 7.67/1.48      inference(predicate_to_equality,[status(thm)],[c_46]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_2244,plain,
% 7.67/1.48      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.67/1.48      | v1_funct_2(k2_funct_1(sK3),sK2,sK1) != iProver_top ),
% 7.67/1.48      inference(global_propositional_subsumption,
% 7.67/1.48                [status(thm)],
% 7.67/1.48                [c_1887,c_52,c_54,c_56,c_2214,c_2235]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_2245,plain,
% 7.67/1.48      ( v1_funct_2(k2_funct_1(sK3),sK2,sK1) != iProver_top
% 7.67/1.48      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 7.67/1.48      inference(renaming,[status(thm)],[c_2244]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_29917,plain,
% 7.67/1.48      ( k1_relat_1(sK3) = k1_xboole_0
% 7.67/1.48      | v1_funct_2(k2_funct_1(sK3),sK2,sK1) != iProver_top
% 7.67/1.48      | r1_tarski(k1_relat_1(sK3),sK1) != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_29901,c_2245]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_26,plain,
% 7.67/1.48      ( v4_relat_1(X0,X1)
% 7.67/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 7.67/1.48      inference(cnf_transformation,[],[f88]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_12,plain,
% 7.67/1.48      ( ~ v4_relat_1(X0,X1)
% 7.67/1.48      | r1_tarski(k1_relat_1(X0),X1)
% 7.67/1.48      | ~ v1_relat_1(X0) ),
% 7.67/1.48      inference(cnf_transformation,[],[f74]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_636,plain,
% 7.67/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.67/1.48      | r1_tarski(k1_relat_1(X0),X1)
% 7.67/1.48      | ~ v1_relat_1(X0) ),
% 7.67/1.48      inference(resolution,[status(thm)],[c_26,c_12]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_640,plain,
% 7.67/1.48      ( r1_tarski(k1_relat_1(X0),X1)
% 7.67/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 7.67/1.48      inference(global_propositional_subsumption,
% 7.67/1.48                [status(thm)],
% 7.67/1.48                [c_636,c_24]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_641,plain,
% 7.67/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.67/1.48      | r1_tarski(k1_relat_1(X0),X1) ),
% 7.67/1.48      inference(renaming,[status(thm)],[c_640]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_2271,plain,
% 7.67/1.48      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 7.67/1.48      | r1_tarski(k1_relat_1(sK3),sK1) ),
% 7.67/1.48      inference(instantiation,[status(thm)],[c_641]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_2272,plain,
% 7.67/1.48      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 7.67/1.48      | r1_tarski(k1_relat_1(sK3),sK1) = iProver_top ),
% 7.67/1.48      inference(predicate_to_equality,[status(thm)],[c_2271]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_29991,plain,
% 7.67/1.48      ( v1_funct_2(k2_funct_1(sK3),sK2,sK1) != iProver_top
% 7.67/1.48      | k1_relat_1(sK3) = k1_xboole_0 ),
% 7.67/1.48      inference(global_propositional_subsumption,
% 7.67/1.48                [status(thm)],
% 7.67/1.48                [c_29917,c_54,c_2272]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_29992,plain,
% 7.67/1.48      ( k1_relat_1(sK3) = k1_xboole_0
% 7.67/1.48      | v1_funct_2(k2_funct_1(sK3),sK2,sK1) != iProver_top ),
% 7.67/1.48      inference(renaming,[status(thm)],[c_29991]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_29997,plain,
% 7.67/1.48      ( k1_relat_1(sK3) = k1_xboole_0
% 7.67/1.48      | r1_tarski(k1_relat_1(sK3),sK1) != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_24075,c_29992]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_30420,plain,
% 7.67/1.48      ( k1_relat_1(sK3) = k1_xboole_0 ),
% 7.67/1.48      inference(global_propositional_subsumption,
% 7.67/1.48                [status(thm)],
% 7.67/1.48                [c_29997,c_54,c_2272]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_18,plain,
% 7.67/1.48      ( ~ v1_relat_1(X0)
% 7.67/1.48      | k2_relat_1(X0) != k1_xboole_0
% 7.67/1.48      | k1_relat_1(X0) = k1_xboole_0 ),
% 7.67/1.48      inference(cnf_transformation,[],[f82]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_1905,plain,
% 7.67/1.48      ( k2_relat_1(X0) != k1_xboole_0
% 7.67/1.48      | k1_relat_1(X0) = k1_xboole_0
% 7.67/1.48      | v1_relat_1(X0) != iProver_top ),
% 7.67/1.48      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_5854,plain,
% 7.67/1.48      ( k1_relat_1(k2_funct_1(sK3)) = k1_xboole_0
% 7.67/1.48      | k1_relat_1(sK3) != k1_xboole_0
% 7.67/1.48      | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_2251,c_1905]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_5855,plain,
% 7.67/1.48      ( k2_relat_1(sK3) = k1_xboole_0
% 7.67/1.48      | k1_relat_1(sK3) != k1_xboole_0
% 7.67/1.48      | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
% 7.67/1.48      inference(demodulation,[status(thm)],[c_5854,c_2278]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_19,plain,
% 7.67/1.48      ( ~ v1_relat_1(X0)
% 7.67/1.48      | k2_relat_1(X0) = k1_xboole_0
% 7.67/1.48      | k1_relat_1(X0) != k1_xboole_0 ),
% 7.67/1.48      inference(cnf_transformation,[],[f81]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_3347,plain,
% 7.67/1.48      ( ~ v1_relat_1(sK3)
% 7.67/1.48      | k2_relat_1(sK3) = k1_xboole_0
% 7.67/1.48      | k1_relat_1(sK3) != k1_xboole_0 ),
% 7.67/1.48      inference(instantiation,[status(thm)],[c_19]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_6987,plain,
% 7.67/1.48      ( k1_relat_1(sK3) != k1_xboole_0 | k2_relat_1(sK3) = k1_xboole_0 ),
% 7.67/1.48      inference(global_propositional_subsumption,
% 7.67/1.48                [status(thm)],
% 7.67/1.48                [c_5855,c_49,c_2234,c_3347]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_6988,plain,
% 7.67/1.48      ( k2_relat_1(sK3) = k1_xboole_0 | k1_relat_1(sK3) != k1_xboole_0 ),
% 7.67/1.48      inference(renaming,[status(thm)],[c_6987]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_6989,plain,
% 7.67/1.48      ( k1_relat_1(sK3) != k1_xboole_0 | sK2 = k1_xboole_0 ),
% 7.67/1.48      inference(demodulation,[status(thm)],[c_6988,c_5882]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_30471,plain,
% 7.67/1.48      ( sK2 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 7.67/1.48      inference(demodulation,[status(thm)],[c_30420,c_6989]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_30498,plain,
% 7.67/1.48      ( sK2 = k1_xboole_0 ),
% 7.67/1.48      inference(equality_resolution_simp,[status(thm)],[c_30471]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_16,plain,
% 7.67/1.48      ( ~ v1_relat_1(X0)
% 7.67/1.48      | k2_relat_1(X0) != k1_xboole_0
% 7.67/1.48      | k1_xboole_0 = X0 ),
% 7.67/1.48      inference(cnf_transformation,[],[f80]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_1907,plain,
% 7.67/1.48      ( k2_relat_1(X0) != k1_xboole_0
% 7.67/1.48      | k1_xboole_0 = X0
% 7.67/1.48      | v1_relat_1(X0) != iProver_top ),
% 7.67/1.48      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_5985,plain,
% 7.67/1.48      ( sK2 != k1_xboole_0
% 7.67/1.48      | sK3 = k1_xboole_0
% 7.67/1.48      | v1_relat_1(sK3) != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_5882,c_1907]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_6081,plain,
% 7.67/1.48      ( sK3 = k1_xboole_0 | sK2 != k1_xboole_0 ),
% 7.67/1.48      inference(global_propositional_subsumption,
% 7.67/1.48                [status(thm)],
% 7.67/1.48                [c_5985,c_54,c_2235]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_6082,plain,
% 7.67/1.48      ( sK2 != k1_xboole_0 | sK3 = k1_xboole_0 ),
% 7.67/1.48      inference(renaming,[status(thm)],[c_6081]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_30696,plain,
% 7.67/1.48      ( sK3 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 7.67/1.48      inference(demodulation,[status(thm)],[c_30498,c_6082]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_30730,plain,
% 7.67/1.48      ( sK3 = k1_xboole_0 ),
% 7.67/1.48      inference(equality_resolution_simp,[status(thm)],[c_30696]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_30702,plain,
% 7.67/1.48      ( v1_funct_2(k2_funct_1(sK3),k1_xboole_0,sK1) != iProver_top
% 7.67/1.48      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top ),
% 7.67/1.48      inference(demodulation,[status(thm)],[c_30498,c_2245]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_30714,plain,
% 7.67/1.48      ( v1_funct_2(k2_funct_1(sK3),k1_xboole_0,sK1) != iProver_top
% 7.67/1.48      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.67/1.48      inference(demodulation,[status(thm)],[c_30702,c_5]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_30736,plain,
% 7.67/1.48      ( v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK1) != iProver_top
% 7.67/1.48      | m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.67/1.48      inference(demodulation,[status(thm)],[c_30730,c_30714]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_111,plain,
% 7.67/1.48      ( v1_funct_1(X0) != iProver_top
% 7.67/1.48      | v1_relat_1(X0) != iProver_top
% 7.67/1.48      | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
% 7.67/1.48      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_113,plain,
% 7.67/1.48      ( v1_funct_1(k1_xboole_0) != iProver_top
% 7.67/1.48      | v1_relat_1(k2_funct_1(k1_xboole_0)) = iProver_top
% 7.67/1.48      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 7.67/1.48      inference(instantiation,[status(thm)],[c_111]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_2223,plain,
% 7.67/1.48      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.67/1.48      | v1_relat_1(k1_xboole_0) ),
% 7.67/1.48      inference(instantiation,[status(thm)],[c_24]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_2225,plain,
% 7.67/1.48      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.67/1.48      | v1_relat_1(k1_xboole_0) = iProver_top ),
% 7.67/1.48      inference(predicate_to_equality,[status(thm)],[c_2223]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_2227,plain,
% 7.67/1.48      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top ),
% 7.67/1.48      inference(predicate_to_equality,[status(thm)],[c_2224]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_1014,plain,
% 7.67/1.48      ( ~ v1_funct_1(X0) | v1_funct_1(X1) | X1 != X0 ),
% 7.67/1.48      theory(equality) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_2238,plain,
% 7.67/1.48      ( v1_funct_1(X0) | ~ v1_funct_1(sK3) | X0 != sK3 ),
% 7.67/1.48      inference(instantiation,[status(thm)],[c_1014]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_2239,plain,
% 7.67/1.48      ( X0 != sK3
% 7.67/1.48      | v1_funct_1(X0) = iProver_top
% 7.67/1.48      | v1_funct_1(sK3) != iProver_top ),
% 7.67/1.48      inference(predicate_to_equality,[status(thm)],[c_2238]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_2241,plain,
% 7.67/1.48      ( k1_xboole_0 != sK3
% 7.67/1.48      | v1_funct_1(sK3) != iProver_top
% 7.67/1.48      | v1_funct_1(k1_xboole_0) = iProver_top ),
% 7.67/1.48      inference(instantiation,[status(thm)],[c_2239]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_17,plain,
% 7.67/1.48      ( ~ v1_relat_1(X0)
% 7.67/1.48      | k1_relat_1(X0) != k1_xboole_0
% 7.67/1.48      | k1_xboole_0 = X0 ),
% 7.67/1.48      inference(cnf_transformation,[],[f79]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_2562,plain,
% 7.67/1.48      ( ~ v1_relat_1(sK3)
% 7.67/1.48      | k1_relat_1(sK3) != k1_xboole_0
% 7.67/1.48      | k1_xboole_0 = sK3 ),
% 7.67/1.48      inference(instantiation,[status(thm)],[c_17]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_2432,plain,
% 7.67/1.48      ( v1_funct_1(X0)
% 7.67/1.48      | ~ v1_funct_1(k2_funct_1(sK3))
% 7.67/1.48      | X0 != k2_funct_1(sK3) ),
% 7.67/1.48      inference(instantiation,[status(thm)],[c_1014]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_2620,plain,
% 7.67/1.48      ( v1_funct_1(k2_funct_1(X0))
% 7.67/1.48      | ~ v1_funct_1(k2_funct_1(sK3))
% 7.67/1.48      | k2_funct_1(X0) != k2_funct_1(sK3) ),
% 7.67/1.48      inference(instantiation,[status(thm)],[c_2432]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_2622,plain,
% 7.67/1.48      ( k2_funct_1(X0) != k2_funct_1(sK3)
% 7.67/1.48      | v1_funct_1(k2_funct_1(X0)) = iProver_top
% 7.67/1.48      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 7.67/1.48      inference(predicate_to_equality,[status(thm)],[c_2620]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_2624,plain,
% 7.67/1.48      ( k2_funct_1(k1_xboole_0) != k2_funct_1(sK3)
% 7.67/1.48      | v1_funct_1(k2_funct_1(sK3)) != iProver_top
% 7.67/1.48      | v1_funct_1(k2_funct_1(k1_xboole_0)) = iProver_top ),
% 7.67/1.48      inference(instantiation,[status(thm)],[c_2622]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_1013,plain,
% 7.67/1.48      ( X0 != X1 | k2_funct_1(X0) = k2_funct_1(X1) ),
% 7.67/1.48      theory(equality) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_2621,plain,
% 7.67/1.48      ( X0 != sK3 | k2_funct_1(X0) = k2_funct_1(sK3) ),
% 7.67/1.48      inference(instantiation,[status(thm)],[c_1013]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_2626,plain,
% 7.67/1.48      ( k2_funct_1(k1_xboole_0) = k2_funct_1(sK3) | k1_xboole_0 != sK3 ),
% 7.67/1.48      inference(instantiation,[status(thm)],[c_2621]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_30697,plain,
% 7.67/1.48      ( k1_relat_1(k2_funct_1(sK3)) = k1_xboole_0 ),
% 7.67/1.48      inference(demodulation,[status(thm)],[c_30498,c_5976]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_30732,plain,
% 7.67/1.48      ( k1_relat_1(k2_funct_1(k1_xboole_0)) = k1_xboole_0 ),
% 7.67/1.48      inference(demodulation,[status(thm)],[c_30730,c_30697]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_31777,plain,
% 7.67/1.48      ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(k2_funct_1(k1_xboole_0))))) = iProver_top
% 7.67/1.48      | v1_funct_1(k2_funct_1(k1_xboole_0)) != iProver_top
% 7.67/1.48      | v1_relat_1(k2_funct_1(k1_xboole_0)) != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_30732,c_1893]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_31798,plain,
% 7.67/1.48      ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 7.67/1.48      | v1_funct_1(k2_funct_1(k1_xboole_0)) != iProver_top
% 7.67/1.48      | v1_relat_1(k2_funct_1(k1_xboole_0)) != iProver_top ),
% 7.67/1.48      inference(demodulation,[status(thm)],[c_31777,c_5]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_32557,plain,
% 7.67/1.48      ( v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK1) != iProver_top ),
% 7.67/1.48      inference(global_propositional_subsumption,
% 7.67/1.48                [status(thm)],
% 7.67/1.48                [c_30736,c_52,c_49,c_54,c_113,c_2214,c_2225,c_2227,
% 7.67/1.48                 c_2234,c_2235,c_2241,c_2272,c_2562,c_2624,c_2626,
% 7.67/1.48                 c_29997,c_31798]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_37441,plain,
% 7.67/1.48      ( r1_tarski(k2_funct_1(k1_xboole_0),k1_xboole_0) != iProver_top
% 7.67/1.48      | v1_funct_1(k2_funct_1(k1_xboole_0)) != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_9141,c_32557]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_9,plain,
% 7.67/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 7.67/1.48      inference(cnf_transformation,[],[f71]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_1912,plain,
% 7.67/1.48      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.67/1.48      | r1_tarski(X0,X1) = iProver_top ),
% 7.67/1.48      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_6256,plain,
% 7.67/1.48      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = iProver_top
% 7.67/1.48      | v1_funct_1(X0) != iProver_top
% 7.67/1.48      | v1_relat_1(X0) != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_1893,c_1912]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_31772,plain,
% 7.67/1.48      ( r1_tarski(k2_funct_1(k1_xboole_0),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k2_funct_1(k1_xboole_0)))) = iProver_top
% 7.67/1.48      | v1_funct_1(k2_funct_1(k1_xboole_0)) != iProver_top
% 7.67/1.48      | v1_relat_1(k2_funct_1(k1_xboole_0)) != iProver_top ),
% 7.67/1.48      inference(superposition,[status(thm)],[c_30732,c_6256]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_31805,plain,
% 7.67/1.48      ( r1_tarski(k2_funct_1(k1_xboole_0),k1_xboole_0) = iProver_top
% 7.67/1.48      | v1_funct_1(k2_funct_1(k1_xboole_0)) != iProver_top
% 7.67/1.48      | v1_relat_1(k2_funct_1(k1_xboole_0)) != iProver_top ),
% 7.67/1.48      inference(demodulation,[status(thm)],[c_31772,c_5]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_37453,plain,
% 7.67/1.48      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 7.67/1.48      inference(grounding,
% 7.67/1.48                [status(thm)],
% 7.67/1.48                [c_2227:[bind(X1,$fot(k1_xboole_0)),
% 7.67/1.48                 bind(X0,$fot(k1_xboole_0))]]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(c_37454,plain,
% 7.67/1.48      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 7.67/1.48      | v1_relat_1(k1_xboole_0) = iProver_top ),
% 7.67/1.48      inference(grounding,
% 7.67/1.48                [status(thm)],
% 7.67/1.48                [c_2225:[bind(X1,$fot(k1_xboole_0)),
% 7.67/1.48                 bind(X0,$fot(k1_xboole_0))]]) ).
% 7.67/1.48  
% 7.67/1.48  cnf(contradiction,plain,
% 7.67/1.48      ( $false ),
% 7.67/1.48      inference(minisat,
% 7.67/1.48                [status(thm)],
% 7.67/1.48                [c_37441,c_31805,c_29997,c_2626,c_2624,c_2562,c_2272,
% 7.67/1.48                 c_2241,c_2235,c_2234,c_37453,c_37454,c_2214,c_113,c_54,
% 7.67/1.48                 c_49,c_52]) ).
% 7.67/1.48  
% 7.67/1.48  
% 7.67/1.48  % SZS output end CNFRefutation for theBenchmark.p
% 7.67/1.48  
% 7.67/1.48  ------                               Statistics
% 7.67/1.48  
% 7.67/1.48  ------ General
% 7.67/1.48  
% 7.67/1.48  abstr_ref_over_cycles:                  0
% 7.67/1.48  abstr_ref_under_cycles:                 0
% 7.67/1.48  gc_basic_clause_elim:                   0
% 7.67/1.48  forced_gc_time:                         0
% 7.67/1.48  parsing_time:                           0.012
% 7.67/1.48  unif_index_cands_time:                  0.
% 7.67/1.48  unif_index_add_time:                    0.
% 7.67/1.48  orderings_time:                         0.
% 7.67/1.48  out_proof_time:                         0.023
% 7.67/1.48  total_time:                             0.918
% 7.67/1.48  num_of_symbols:                         52
% 7.67/1.48  num_of_terms:                           28044
% 7.67/1.48  
% 7.67/1.48  ------ Preprocessing
% 7.67/1.48  
% 7.67/1.48  num_of_splits:                          0
% 7.67/1.48  num_of_split_atoms:                     0
% 7.67/1.48  num_of_reused_defs:                     0
% 7.67/1.48  num_eq_ax_congr_red:                    15
% 7.67/1.48  num_of_sem_filtered_clauses:            1
% 7.67/1.48  num_of_subtypes:                        0
% 7.67/1.48  monotx_restored_types:                  0
% 7.67/1.48  sat_num_of_epr_types:                   0
% 7.67/1.48  sat_num_of_non_cyclic_types:            0
% 7.67/1.48  sat_guarded_non_collapsed_types:        0
% 7.67/1.48  num_pure_diseq_elim:                    0
% 7.67/1.48  simp_replaced_by:                       0
% 7.67/1.48  res_preprocessed:                       207
% 7.67/1.48  prep_upred:                             0
% 7.67/1.48  prep_unflattend:                        4
% 7.67/1.48  smt_new_axioms:                         0
% 7.67/1.48  pred_elim_cands:                        7
% 7.67/1.48  pred_elim:                              3
% 7.67/1.48  pred_elim_cl:                           4
% 7.67/1.48  pred_elim_cycles:                       5
% 7.67/1.48  merged_defs:                            8
% 7.67/1.48  merged_defs_ncl:                        0
% 7.67/1.48  bin_hyper_res:                          8
% 7.67/1.48  prep_cycles:                            4
% 7.67/1.48  pred_elim_time:                         0.003
% 7.67/1.48  splitting_time:                         0.
% 7.67/1.48  sem_filter_time:                        0.
% 7.67/1.48  monotx_time:                            0.001
% 7.67/1.48  subtype_inf_time:                       0.
% 7.67/1.48  
% 7.67/1.48  ------ Problem properties
% 7.67/1.48  
% 7.67/1.48  clauses:                                43
% 7.67/1.48  conjectures:                            5
% 7.67/1.48  epr:                                    5
% 7.67/1.48  horn:                                   40
% 7.67/1.48  ground:                                 7
% 7.67/1.48  unary:                                  15
% 7.67/1.48  binary:                                 8
% 7.67/1.48  lits:                                   103
% 7.67/1.48  lits_eq:                                20
% 7.67/1.48  fd_pure:                                0
% 7.67/1.48  fd_pseudo:                              0
% 7.67/1.48  fd_cond:                                5
% 7.67/1.48  fd_pseudo_cond:                         1
% 7.67/1.48  ac_symbols:                             0
% 7.67/1.48  
% 7.67/1.48  ------ Propositional Solver
% 7.67/1.48  
% 7.67/1.48  prop_solver_calls:                      30
% 7.67/1.48  prop_fast_solver_calls:                 2486
% 7.67/1.48  smt_solver_calls:                       0
% 7.67/1.48  smt_fast_solver_calls:                  0
% 7.67/1.48  prop_num_of_clauses:                    12929
% 7.67/1.48  prop_preprocess_simplified:             31836
% 7.67/1.48  prop_fo_subsumed:                       236
% 7.67/1.48  prop_solver_time:                       0.
% 7.67/1.48  smt_solver_time:                        0.
% 7.67/1.48  smt_fast_solver_time:                   0.
% 7.67/1.48  prop_fast_solver_time:                  0.
% 7.67/1.48  prop_unsat_core_time:                   0.001
% 7.67/1.48  
% 7.67/1.48  ------ QBF
% 7.67/1.48  
% 7.67/1.48  qbf_q_res:                              0
% 7.67/1.48  qbf_num_tautologies:                    0
% 7.67/1.48  qbf_prep_cycles:                        0
% 7.67/1.48  
% 7.67/1.48  ------ BMC1
% 7.67/1.48  
% 7.67/1.48  bmc1_current_bound:                     -1
% 7.67/1.48  bmc1_last_solved_bound:                 -1
% 7.67/1.48  bmc1_unsat_core_size:                   -1
% 7.67/1.48  bmc1_unsat_core_parents_size:           -1
% 7.67/1.48  bmc1_merge_next_fun:                    0
% 7.67/1.48  bmc1_unsat_core_clauses_time:           0.
% 7.67/1.48  
% 7.67/1.48  ------ Instantiation
% 7.67/1.48  
% 7.67/1.48  inst_num_of_clauses:                    3948
% 7.67/1.48  inst_num_in_passive:                    2516
% 7.67/1.48  inst_num_in_active:                     1355
% 7.67/1.48  inst_num_in_unprocessed:                87
% 7.67/1.48  inst_num_of_loops:                      1680
% 7.67/1.48  inst_num_of_learning_restarts:          0
% 7.67/1.48  inst_num_moves_active_passive:          324
% 7.67/1.48  inst_lit_activity:                      0
% 7.67/1.48  inst_lit_activity_moves:                0
% 7.67/1.48  inst_num_tautologies:                   0
% 7.67/1.48  inst_num_prop_implied:                  0
% 7.67/1.48  inst_num_existing_simplified:           0
% 7.67/1.48  inst_num_eq_res_simplified:             0
% 7.67/1.48  inst_num_child_elim:                    0
% 7.67/1.48  inst_num_of_dismatching_blockings:      1934
% 7.67/1.48  inst_num_of_non_proper_insts:           3673
% 7.67/1.48  inst_num_of_duplicates:                 0
% 7.67/1.48  inst_inst_num_from_inst_to_res:         0
% 7.67/1.48  inst_dismatching_checking_time:         0.
% 7.67/1.48  
% 7.67/1.48  ------ Resolution
% 7.67/1.48  
% 7.67/1.48  res_num_of_clauses:                     0
% 7.67/1.48  res_num_in_passive:                     0
% 7.67/1.48  res_num_in_active:                      0
% 7.67/1.48  res_num_of_loops:                       211
% 7.67/1.48  res_forward_subset_subsumed:            132
% 7.67/1.48  res_backward_subset_subsumed:           32
% 7.67/1.48  res_forward_subsumed:                   0
% 7.67/1.48  res_backward_subsumed:                  0
% 7.67/1.48  res_forward_subsumption_resolution:     0
% 7.67/1.48  res_backward_subsumption_resolution:    0
% 7.67/1.48  res_clause_to_clause_subsumption:       2876
% 7.67/1.48  res_orphan_elimination:                 0
% 7.67/1.48  res_tautology_del:                      513
% 7.67/1.48  res_num_eq_res_simplified:              0
% 7.67/1.48  res_num_sel_changes:                    0
% 7.67/1.48  res_moves_from_active_to_pass:          0
% 7.67/1.48  
% 7.67/1.48  ------ Superposition
% 7.67/1.48  
% 7.67/1.48  sup_time_total:                         0.
% 7.67/1.48  sup_time_generating:                    0.
% 7.67/1.48  sup_time_sim_full:                      0.
% 7.67/1.48  sup_time_sim_immed:                     0.
% 7.67/1.48  
% 7.67/1.48  sup_num_of_clauses:                     401
% 7.67/1.48  sup_num_in_active:                      156
% 7.67/1.48  sup_num_in_passive:                     245
% 7.67/1.48  sup_num_of_loops:                       334
% 7.67/1.48  sup_fw_superposition:                   798
% 7.67/1.48  sup_bw_superposition:                   519
% 7.67/1.48  sup_immediate_simplified:               502
% 7.67/1.48  sup_given_eliminated:                   1
% 7.67/1.48  comparisons_done:                       0
% 7.67/1.48  comparisons_avoided:                    48
% 7.67/1.48  
% 7.67/1.48  ------ Simplifications
% 7.67/1.48  
% 7.67/1.48  
% 7.67/1.48  sim_fw_subset_subsumed:                 204
% 7.67/1.48  sim_bw_subset_subsumed:                 121
% 7.67/1.48  sim_fw_subsumed:                        130
% 7.67/1.48  sim_bw_subsumed:                        7
% 7.67/1.48  sim_fw_subsumption_res:                 11
% 7.67/1.48  sim_bw_subsumption_res:                 0
% 7.67/1.48  sim_tautology_del:                      16
% 7.67/1.48  sim_eq_tautology_del:                   74
% 7.67/1.48  sim_eq_res_simp:                        3
% 7.67/1.48  sim_fw_demodulated:                     64
% 7.67/1.48  sim_bw_demodulated:                     164
% 7.67/1.48  sim_light_normalised:                   161
% 7.67/1.48  sim_joinable_taut:                      0
% 7.67/1.48  sim_joinable_simp:                      0
% 7.67/1.48  sim_ac_normalised:                      0
% 7.67/1.48  sim_smt_subsumption:                    0
% 7.67/1.48  
%------------------------------------------------------------------------------
