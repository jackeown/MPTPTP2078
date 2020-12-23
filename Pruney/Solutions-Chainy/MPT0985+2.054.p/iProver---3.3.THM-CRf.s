%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:02:30 EST 2020

% Result     : Theorem 7.85s
% Output     : CNFRefutation 7.85s
% Verified   : 
% Statistics : Number of formulae       :  244 (4116 expanded)
%              Number of clauses        :  156 (1468 expanded)
%              Number of leaves         :   25 ( 785 expanded)
%              Depth                    :   30
%              Number of atoms          :  669 (18804 expanded)
%              Number of equality atoms :  327 (3819 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f116,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f19])).

fof(f34,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f136,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f34])).

fof(f155,plain,(
    k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    inference(definition_unfolding,[],[f116,f136])).

fof(f33,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f135,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f33])).

fof(f36,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f77,plain,(
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
    inference(ennf_transformation,[],[f36])).

fof(f78,plain,(
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
    inference(flattening,[],[f77])).

fof(f143,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(X3,X0,X2)
      | k1_xboole_0 != X0
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f161,plain,(
    ! [X2,X3,X1] :
      ( v1_funct_2(X3,k1_xboole_0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X3,k1_xboole_0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(equality_resolution,[],[f143])).

fof(f23,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f122,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f23])).

fof(f156,plain,(
    ! [X0] : v1_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f122,f136])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f94,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f93,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f32,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v1_partfun1(X2,X0)
          & v1_funct_1(X2) )
       => ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f74,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f73])).

fof(f133,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f134,plain,(
    ! [X0] : v1_partfun1(k6_partfun1(X0),X0) ),
    inference(cnf_transformation,[],[f33])).

fof(f145,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
      | k1_xboole_0 != X0
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f160,plain,(
    ! [X2,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X3,k1_xboole_0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(equality_resolution,[],[f145])).

fof(f37,conjecture,(
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

fof(f38,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f37])).

fof(f79,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f38])).

fof(f80,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f79])).

fof(f88,plain,
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

fof(f89,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
      | ~ v1_funct_1(k2_funct_1(sK3)) )
    & k2_relset_1(sK1,sK2,sK3) = sK2
    & v2_funct_1(sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK3,sK1,sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f80,f88])).

fof(f148,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f89])).

fof(f29,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f129,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f108,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f35,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f35])).

fof(f76,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f75])).

fof(f139,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f31,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f131,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f150,plain,(
    k2_relset_1(sK1,sK2,sK3) = sK2 ),
    inference(cnf_transformation,[],[f89])).

fof(f107,plain,(
    ! [X0] :
      ( k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f146,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f89])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f102,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f21,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f57,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f56])).

fof(f118,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f149,plain,(
    v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f89])).

fof(f22,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f59,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f58])).

fof(f120,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f142,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(X3,X0,X2)
      | k1_xboole_0 = X1
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f138,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f144,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
      | k1_xboole_0 = X1
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f151,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
    | ~ v1_funct_1(k2_funct_1(sK3)) ),
    inference(cnf_transformation,[],[f89])).

fof(f30,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f30])).

fof(f71,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f39])).

fof(f130,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f100,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f86])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f87,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f53])).

fof(f112,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_relat_1(X0)
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f87])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f52,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f51])).

fof(f110,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f121,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f23])).

fof(f157,plain,(
    ! [X0] : v1_relat_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f121,f136])).

fof(f17,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f114,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f17])).

fof(f152,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f114,f136])).

fof(f109,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_26,plain,
    ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f155])).

cnf(c_44,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f135])).

cnf(c_4153,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_5084,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_26,c_4153])).

cnf(c_51,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | v1_funct_2(X0,k1_xboole_0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ r1_tarski(X1,X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f161])).

cnf(c_4148,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1) != iProver_top
    | v1_funct_2(X0,k1_xboole_0,X2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_51])).

cnf(c_6273,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,X0) = iProver_top
    | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,X0) != iProver_top
    | v1_funct_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5084,c_4148])).

cnf(c_31,plain,
    ( v1_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f156])).

cnf(c_119,plain,
    ( v1_funct_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_121,plain,
    ( v1_funct_1(k6_partfun1(k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_119])).

cnf(c_4,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_192,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_3,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_3106,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_4341,plain,
    ( v1_funct_1(X0)
    | ~ v1_funct_1(k6_partfun1(X1))
    | X0 != k6_partfun1(X1) ),
    inference(instantiation,[status(thm)],[c_3106])).

cnf(c_4342,plain,
    ( X0 != k6_partfun1(X1)
    | v1_funct_1(X0) = iProver_top
    | v1_funct_1(k6_partfun1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4341])).

cnf(c_4344,plain,
    ( k1_xboole_0 != k6_partfun1(k1_xboole_0)
    | v1_funct_1(k6_partfun1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_4342])).

cnf(c_3090,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_4782,plain,
    ( X0 != X1
    | X0 = k6_partfun1(X2)
    | k6_partfun1(X2) != X1 ),
    inference(instantiation,[status(thm)],[c_3090])).

cnf(c_4783,plain,
    ( k6_partfun1(k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k6_partfun1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4782])).

cnf(c_42,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f133])).

cnf(c_45,plain,
    ( v1_partfun1(k6_partfun1(X0),X0) ),
    inference(cnf_transformation,[],[f134])).

cnf(c_712,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | X3 != X1
    | k6_partfun1(X3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_42,c_45])).

cnf(c_713,plain,
    ( v1_funct_2(k6_partfun1(X0),X0,X1)
    | ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(k6_partfun1(X0)) ),
    inference(unflattening,[status(thm)],[c_712])).

cnf(c_717,plain,
    ( ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_funct_2(k6_partfun1(X0),X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_713,c_31])).

cnf(c_718,plain,
    ( v1_funct_2(k6_partfun1(X0),X0,X1)
    | ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(renaming,[status(thm)],[c_717])).

cnf(c_4139,plain,
    ( v1_funct_2(k6_partfun1(X0),X0,X1) = iProver_top
    | m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_718])).

cnf(c_5020,plain,
    ( v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,X0) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_26,c_4139])).

cnf(c_5021,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,X0) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5020,c_26])).

cnf(c_5023,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5021])).

cnf(c_17026,plain,
    ( r1_tarski(k1_xboole_0,X0) != iProver_top
    | v1_funct_2(k1_xboole_0,k1_xboole_0,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6273,c_121,c_26,c_192,c_3,c_4344,c_4783,c_5023,c_5084])).

cnf(c_17027,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,X0) = iProver_top
    | r1_tarski(k1_xboole_0,X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_17026])).

cnf(c_49,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))
    | ~ r1_tarski(X1,X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f160])).

cnf(c_4150,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2))) = iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_49])).

cnf(c_7822,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) = iProver_top
    | r1_tarski(k1_xboole_0,X0) != iProver_top
    | v1_funct_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5084,c_4150])).

cnf(c_21069,plain,
    ( r1_tarski(k1_xboole_0,X0) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7822,c_121,c_26,c_192,c_3,c_4344,c_4783,c_5023,c_5084])).

cnf(c_21070,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) = iProver_top
    | r1_tarski(k1_xboole_0,X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_21069])).

cnf(c_58,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f148])).

cnf(c_4144,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_58])).

cnf(c_39,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f129])).

cnf(c_4155,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_6223,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_4144,c_4155])).

cnf(c_17,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_4173,plain,
    ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_6267,plain,
    ( k2_relat_1(k4_relat_1(sK3)) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_6223,c_4173])).

cnf(c_46,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f139])).

cnf(c_4152,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_9352,plain,
    ( m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k4_relat_1(sK3)),k1_relat_1(sK3)))) = iProver_top
    | v1_funct_1(k4_relat_1(sK3)) != iProver_top
    | v1_relat_1(k4_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6267,c_4152])).

cnf(c_41,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f131])).

cnf(c_4154,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_7866,plain,
    ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_4144,c_4154])).

cnf(c_56,negated_conjecture,
    ( k2_relset_1(sK1,sK2,sK3) = sK2 ),
    inference(cnf_transformation,[],[f150])).

cnf(c_7873,plain,
    ( k2_relat_1(sK3) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_7866,c_56])).

cnf(c_18,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_4172,plain,
    ( k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_6268,plain,
    ( k1_relat_1(k4_relat_1(sK3)) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_6223,c_4172])).

cnf(c_7891,plain,
    ( k1_relat_1(k4_relat_1(sK3)) = sK2 ),
    inference(demodulation,[status(thm)],[c_7873,c_6268])).

cnf(c_9362,plain,
    ( m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3)))) = iProver_top
    | v1_funct_1(k4_relat_1(sK3)) != iProver_top
    | v1_relat_1(k4_relat_1(sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9352,c_7891])).

cnf(c_60,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f146])).

cnf(c_61,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_60])).

cnf(c_63,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_58])).

cnf(c_4257,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_39])).

cnf(c_4308,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_4257])).

cnf(c_4309,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4308])).

cnf(c_12,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k4_relat_1(X0)) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_9053,plain,
    ( v1_relat_1(k4_relat_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_9054,plain,
    ( v1_relat_1(k4_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9053])).

cnf(c_4142,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_60])).

cnf(c_28,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(X0) = k4_relat_1(X0) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_4165,plain,
    ( k2_funct_1(X0) = k4_relat_1(X0)
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_9391,plain,
    ( k2_funct_1(sK3) = k4_relat_1(sK3)
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4142,c_4165])).

cnf(c_57,negated_conjecture,
    ( v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f149])).

cnf(c_878,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(X0) = k4_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_57])).

cnf(c_879,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | k2_funct_1(sK3) = k4_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_878])).

cnf(c_9784,plain,
    ( k2_funct_1(sK3) = k4_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9391,c_60,c_58,c_879,c_4308])).

cnf(c_29,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_4164,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_funct_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_9790,plain,
    ( v1_funct_1(k4_relat_1(sK3)) = iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_9784,c_4164])).

cnf(c_10740,plain,
    ( m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9362,c_61,c_63,c_4309,c_9054,c_9790])).

cnf(c_52,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(X0,X1,X3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(X2,X3)
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f142])).

cnf(c_4147,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,X2,X0) != iProver_top
    | v1_funct_2(X1,X2,X3) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | r1_tarski(X0,X3) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_52])).

cnf(c_10749,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | v1_funct_2(k4_relat_1(sK3),sK2,X0) = iProver_top
    | v1_funct_2(k4_relat_1(sK3),sK2,k1_relat_1(sK3)) != iProver_top
    | r1_tarski(k1_relat_1(sK3),X0) != iProver_top
    | v1_funct_1(k4_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_10740,c_4147])).

cnf(c_47,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f138])).

cnf(c_4151,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_47])).

cnf(c_8377,plain,
    ( v1_funct_2(k4_relat_1(sK3),k1_relat_1(k4_relat_1(sK3)),k1_relat_1(sK3)) = iProver_top
    | v1_funct_1(k4_relat_1(sK3)) != iProver_top
    | v1_relat_1(k4_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6267,c_4151])).

cnf(c_8381,plain,
    ( v1_funct_2(k4_relat_1(sK3),sK2,k1_relat_1(sK3)) = iProver_top
    | v1_funct_1(k4_relat_1(sK3)) != iProver_top
    | v1_relat_1(k4_relat_1(sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8377,c_7891])).

cnf(c_19323,plain,
    ( r1_tarski(k1_relat_1(sK3),X0) != iProver_top
    | k1_relat_1(sK3) = k1_xboole_0
    | v1_funct_2(k4_relat_1(sK3),sK2,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10749,c_61,c_63,c_4309,c_8381,c_9054,c_9790])).

cnf(c_19324,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | v1_funct_2(k4_relat_1(sK3),sK2,X0) = iProver_top
    | r1_tarski(k1_relat_1(sK3),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_19323])).

cnf(c_50,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ r1_tarski(X2,X3)
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f144])).

cnf(c_4149,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,X2,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) = iProver_top
    | r1_tarski(X0,X3) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_50])).

cnf(c_10748,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | v1_funct_2(k4_relat_1(sK3),sK2,k1_relat_1(sK3)) != iProver_top
    | m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
    | r1_tarski(k1_relat_1(sK3),X0) != iProver_top
    | v1_funct_1(k4_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_10740,c_4149])).

cnf(c_19330,plain,
    ( r1_tarski(k1_relat_1(sK3),X0) != iProver_top
    | m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
    | k1_relat_1(sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_10748,c_61,c_63,c_4309,c_8381,c_9054,c_9790])).

cnf(c_19331,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
    | r1_tarski(k1_relat_1(sK3),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_19330])).

cnf(c_55,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
    | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK3)) ),
    inference(cnf_transformation,[],[f151])).

cnf(c_4146,plain,
    ( v1_funct_2(k2_funct_1(sK3),sK2,sK1) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_55])).

cnf(c_65,plain,
    ( v1_funct_2(k2_funct_1(sK3),sK2,sK1) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_55])).

cnf(c_4244,plain,
    ( v1_funct_1(k2_funct_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_4245,plain,
    ( v1_funct_1(k2_funct_1(sK3)) = iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4244])).

cnf(c_4492,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_2(k2_funct_1(sK3),sK2,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4146,c_61,c_63,c_65,c_4245,c_4309])).

cnf(c_4493,plain,
    ( v1_funct_2(k2_funct_1(sK3),sK2,sK1) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(renaming,[status(thm)],[c_4492])).

cnf(c_9787,plain,
    ( v1_funct_2(k4_relat_1(sK3),sK2,sK1) != iProver_top
    | m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9784,c_4493])).

cnf(c_19342,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | v1_funct_2(k4_relat_1(sK3),sK2,sK1) != iProver_top
    | r1_tarski(k1_relat_1(sK3),sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_19331,c_9787])).

cnf(c_40,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f130])).

cnf(c_11,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_733,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_40,c_11])).

cnf(c_737,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_733,c_39])).

cnf(c_738,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1) ),
    inference(renaming,[status(thm)],[c_737])).

cnf(c_4138,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_738])).

cnf(c_4650,plain,
    ( r1_tarski(k1_relat_1(sK3),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_4144,c_4138])).

cnf(c_19475,plain,
    ( v1_funct_2(k4_relat_1(sK3),sK2,sK1) != iProver_top
    | k1_relat_1(sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_19342,c_4650])).

cnf(c_19476,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | v1_funct_2(k4_relat_1(sK3),sK2,sK1) != iProver_top ),
    inference(renaming,[status(thm)],[c_19475])).

cnf(c_19479,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | r1_tarski(k1_relat_1(sK3),sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_19324,c_19476])).

cnf(c_19482,plain,
    ( k1_relat_1(sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_19479,c_4650])).

cnf(c_21,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_relat_1(X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f112])).

cnf(c_4169,plain,
    ( k2_relat_1(X0) != k1_xboole_0
    | k1_relat_1(X0) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_6940,plain,
    ( k1_relat_1(k4_relat_1(sK3)) = k1_xboole_0
    | k1_relat_1(sK3) != k1_xboole_0
    | v1_relat_1(k4_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6267,c_4169])).

cnf(c_6944,plain,
    ( k2_relat_1(sK3) = k1_xboole_0
    | k1_relat_1(sK3) != k1_xboole_0
    | v1_relat_1(k4_relat_1(sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6940,c_6268])).

cnf(c_11971,plain,
    ( k1_relat_1(sK3) != k1_xboole_0
    | k2_relat_1(sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6944,c_63,c_4309,c_9054])).

cnf(c_11972,plain,
    ( k2_relat_1(sK3) = k1_xboole_0
    | k1_relat_1(sK3) != k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_11971])).

cnf(c_11973,plain,
    ( k1_relat_1(sK3) != k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_11972,c_7873])).

cnf(c_19507,plain,
    ( sK2 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_19482,c_11973])).

cnf(c_19538,plain,
    ( sK2 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_19507])).

cnf(c_19804,plain,
    ( v1_funct_2(k4_relat_1(sK3),k1_xboole_0,sK1) != iProver_top
    | m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_19538,c_9787])).

cnf(c_19,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f110])).

cnf(c_4171,plain,
    ( k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_7893,plain,
    ( sK2 != k1_xboole_0
    | sK3 = k1_xboole_0
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_7873,c_4171])).

cnf(c_8237,plain,
    ( sK3 = k1_xboole_0
    | sK2 != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7893,c_63,c_4309])).

cnf(c_8238,plain,
    ( sK2 != k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_8237])).

cnf(c_19809,plain,
    ( sK3 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_19538,c_8238])).

cnf(c_19818,plain,
    ( sK3 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_19809])).

cnf(c_19828,plain,
    ( v1_funct_2(k4_relat_1(k1_xboole_0),k1_xboole_0,sK1) != iProver_top
    | m1_subset_1(k4_relat_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_19804,c_19818])).

cnf(c_32,plain,
    ( v1_relat_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f157])).

cnf(c_4161,plain,
    ( v1_relat_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_4903,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_26,c_4161])).

cnf(c_5368,plain,
    ( k1_relat_1(k4_relat_1(k1_xboole_0)) = k2_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_4903,c_4172])).

cnf(c_23,plain,
    ( k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f152])).

cnf(c_4652,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_26,c_23])).

cnf(c_5369,plain,
    ( k1_relat_1(k4_relat_1(k1_xboole_0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_5368,c_4652])).

cnf(c_20,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f109])).

cnf(c_4170,plain,
    ( k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_6332,plain,
    ( k4_relat_1(k1_xboole_0) = k1_xboole_0
    | v1_relat_1(k4_relat_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5369,c_4170])).

cnf(c_116,plain,
    ( v1_relat_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_118,plain,
    ( v1_relat_1(k6_partfun1(k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_116])).

cnf(c_169,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k4_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_171,plain,
    ( v1_relat_1(k4_relat_1(k1_xboole_0)) = iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_169])).

cnf(c_3097,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_4671,plain,
    ( v1_relat_1(X0)
    | ~ v1_relat_1(k6_partfun1(X1))
    | X0 != k6_partfun1(X1) ),
    inference(instantiation,[status(thm)],[c_3097])).

cnf(c_4672,plain,
    ( X0 != k6_partfun1(X1)
    | v1_relat_1(X0) = iProver_top
    | v1_relat_1(k6_partfun1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4671])).

cnf(c_4674,plain,
    ( k1_xboole_0 != k6_partfun1(k1_xboole_0)
    | v1_relat_1(k6_partfun1(k1_xboole_0)) != iProver_top
    | v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_4672])).

cnf(c_12098,plain,
    ( k4_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6332,c_118,c_26,c_171,c_192,c_3,c_4674,c_4783])).

cnf(c_19829,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,sK1) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_19828,c_12098])).

cnf(c_22373,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,sK1) != iProver_top
    | r1_tarski(k1_xboole_0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_21070,c_19829])).

cnf(c_19535,plain,
    ( r1_tarski(k1_xboole_0,sK1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_19482,c_4650])).

cnf(c_29211,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_22373,c_19535])).

cnf(c_29215,plain,
    ( r1_tarski(k1_xboole_0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_17027,c_29211])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_29215,c_19535])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:34:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.85/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.85/1.49  
% 7.85/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.85/1.49  
% 7.85/1.49  ------  iProver source info
% 7.85/1.49  
% 7.85/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.85/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.85/1.49  git: non_committed_changes: false
% 7.85/1.49  git: last_make_outside_of_git: false
% 7.85/1.49  
% 7.85/1.49  ------ 
% 7.85/1.49  
% 7.85/1.49  ------ Input Options
% 7.85/1.49  
% 7.85/1.49  --out_options                           all
% 7.85/1.49  --tptp_safe_out                         true
% 7.85/1.49  --problem_path                          ""
% 7.85/1.49  --include_path                          ""
% 7.85/1.49  --clausifier                            res/vclausify_rel
% 7.85/1.49  --clausifier_options                    ""
% 7.85/1.49  --stdin                                 false
% 7.85/1.49  --stats_out                             all
% 7.85/1.49  
% 7.85/1.49  ------ General Options
% 7.85/1.49  
% 7.85/1.49  --fof                                   false
% 7.85/1.49  --time_out_real                         305.
% 7.85/1.49  --time_out_virtual                      -1.
% 7.85/1.49  --symbol_type_check                     false
% 7.85/1.49  --clausify_out                          false
% 7.85/1.49  --sig_cnt_out                           false
% 7.85/1.49  --trig_cnt_out                          false
% 7.85/1.49  --trig_cnt_out_tolerance                1.
% 7.85/1.49  --trig_cnt_out_sk_spl                   false
% 7.85/1.49  --abstr_cl_out                          false
% 7.85/1.49  
% 7.85/1.49  ------ Global Options
% 7.85/1.49  
% 7.85/1.49  --schedule                              default
% 7.85/1.49  --add_important_lit                     false
% 7.85/1.49  --prop_solver_per_cl                    1000
% 7.85/1.49  --min_unsat_core                        false
% 7.85/1.49  --soft_assumptions                      false
% 7.85/1.49  --soft_lemma_size                       3
% 7.85/1.49  --prop_impl_unit_size                   0
% 7.85/1.49  --prop_impl_unit                        []
% 7.85/1.49  --share_sel_clauses                     true
% 7.85/1.49  --reset_solvers                         false
% 7.85/1.49  --bc_imp_inh                            [conj_cone]
% 7.85/1.49  --conj_cone_tolerance                   3.
% 7.85/1.49  --extra_neg_conj                        none
% 7.85/1.49  --large_theory_mode                     true
% 7.85/1.49  --prolific_symb_bound                   200
% 7.85/1.49  --lt_threshold                          2000
% 7.85/1.49  --clause_weak_htbl                      true
% 7.85/1.49  --gc_record_bc_elim                     false
% 7.85/1.49  
% 7.85/1.49  ------ Preprocessing Options
% 7.85/1.49  
% 7.85/1.49  --preprocessing_flag                    true
% 7.85/1.49  --time_out_prep_mult                    0.1
% 7.85/1.49  --splitting_mode                        input
% 7.85/1.49  --splitting_grd                         true
% 7.85/1.49  --splitting_cvd                         false
% 7.85/1.49  --splitting_cvd_svl                     false
% 7.85/1.49  --splitting_nvd                         32
% 7.85/1.49  --sub_typing                            true
% 7.85/1.49  --prep_gs_sim                           true
% 7.85/1.49  --prep_unflatten                        true
% 7.85/1.49  --prep_res_sim                          true
% 7.85/1.49  --prep_upred                            true
% 7.85/1.49  --prep_sem_filter                       exhaustive
% 7.85/1.49  --prep_sem_filter_out                   false
% 7.85/1.49  --pred_elim                             true
% 7.85/1.49  --res_sim_input                         true
% 7.85/1.49  --eq_ax_congr_red                       true
% 7.85/1.49  --pure_diseq_elim                       true
% 7.85/1.49  --brand_transform                       false
% 7.85/1.49  --non_eq_to_eq                          false
% 7.85/1.49  --prep_def_merge                        true
% 7.85/1.49  --prep_def_merge_prop_impl              false
% 7.85/1.49  --prep_def_merge_mbd                    true
% 7.85/1.49  --prep_def_merge_tr_red                 false
% 7.85/1.49  --prep_def_merge_tr_cl                  false
% 7.85/1.49  --smt_preprocessing                     true
% 7.85/1.49  --smt_ac_axioms                         fast
% 7.85/1.49  --preprocessed_out                      false
% 7.85/1.49  --preprocessed_stats                    false
% 7.85/1.49  
% 7.85/1.49  ------ Abstraction refinement Options
% 7.85/1.49  
% 7.85/1.49  --abstr_ref                             []
% 7.85/1.49  --abstr_ref_prep                        false
% 7.85/1.49  --abstr_ref_until_sat                   false
% 7.85/1.49  --abstr_ref_sig_restrict                funpre
% 7.85/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.85/1.49  --abstr_ref_under                       []
% 7.85/1.49  
% 7.85/1.49  ------ SAT Options
% 7.85/1.49  
% 7.85/1.49  --sat_mode                              false
% 7.85/1.49  --sat_fm_restart_options                ""
% 7.85/1.49  --sat_gr_def                            false
% 7.85/1.49  --sat_epr_types                         true
% 7.85/1.49  --sat_non_cyclic_types                  false
% 7.85/1.49  --sat_finite_models                     false
% 7.85/1.49  --sat_fm_lemmas                         false
% 7.85/1.49  --sat_fm_prep                           false
% 7.85/1.49  --sat_fm_uc_incr                        true
% 7.85/1.49  --sat_out_model                         small
% 7.85/1.49  --sat_out_clauses                       false
% 7.85/1.49  
% 7.85/1.49  ------ QBF Options
% 7.85/1.49  
% 7.85/1.49  --qbf_mode                              false
% 7.85/1.49  --qbf_elim_univ                         false
% 7.85/1.49  --qbf_dom_inst                          none
% 7.85/1.49  --qbf_dom_pre_inst                      false
% 7.85/1.49  --qbf_sk_in                             false
% 7.85/1.49  --qbf_pred_elim                         true
% 7.85/1.49  --qbf_split                             512
% 7.85/1.49  
% 7.85/1.49  ------ BMC1 Options
% 7.85/1.49  
% 7.85/1.49  --bmc1_incremental                      false
% 7.85/1.49  --bmc1_axioms                           reachable_all
% 7.85/1.49  --bmc1_min_bound                        0
% 7.85/1.49  --bmc1_max_bound                        -1
% 7.85/1.49  --bmc1_max_bound_default                -1
% 7.85/1.49  --bmc1_symbol_reachability              true
% 7.85/1.49  --bmc1_property_lemmas                  false
% 7.85/1.49  --bmc1_k_induction                      false
% 7.85/1.49  --bmc1_non_equiv_states                 false
% 7.85/1.49  --bmc1_deadlock                         false
% 7.85/1.49  --bmc1_ucm                              false
% 7.85/1.49  --bmc1_add_unsat_core                   none
% 7.85/1.49  --bmc1_unsat_core_children              false
% 7.85/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.85/1.49  --bmc1_out_stat                         full
% 7.85/1.49  --bmc1_ground_init                      false
% 7.85/1.49  --bmc1_pre_inst_next_state              false
% 7.85/1.49  --bmc1_pre_inst_state                   false
% 7.85/1.49  --bmc1_pre_inst_reach_state             false
% 7.85/1.49  --bmc1_out_unsat_core                   false
% 7.85/1.49  --bmc1_aig_witness_out                  false
% 7.85/1.49  --bmc1_verbose                          false
% 7.85/1.49  --bmc1_dump_clauses_tptp                false
% 7.85/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.85/1.49  --bmc1_dump_file                        -
% 7.85/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.85/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.85/1.49  --bmc1_ucm_extend_mode                  1
% 7.85/1.49  --bmc1_ucm_init_mode                    2
% 7.85/1.49  --bmc1_ucm_cone_mode                    none
% 7.85/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.85/1.49  --bmc1_ucm_relax_model                  4
% 7.85/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.85/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.85/1.49  --bmc1_ucm_layered_model                none
% 7.85/1.49  --bmc1_ucm_max_lemma_size               10
% 7.85/1.49  
% 7.85/1.49  ------ AIG Options
% 7.85/1.49  
% 7.85/1.49  --aig_mode                              false
% 7.85/1.49  
% 7.85/1.49  ------ Instantiation Options
% 7.85/1.49  
% 7.85/1.49  --instantiation_flag                    true
% 7.85/1.49  --inst_sos_flag                         true
% 7.85/1.49  --inst_sos_phase                        true
% 7.85/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.85/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.85/1.49  --inst_lit_sel_side                     num_symb
% 7.85/1.49  --inst_solver_per_active                1400
% 7.85/1.49  --inst_solver_calls_frac                1.
% 7.85/1.49  --inst_passive_queue_type               priority_queues
% 7.85/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.85/1.49  --inst_passive_queues_freq              [25;2]
% 7.85/1.49  --inst_dismatching                      true
% 7.85/1.49  --inst_eager_unprocessed_to_passive     true
% 7.85/1.49  --inst_prop_sim_given                   true
% 7.85/1.49  --inst_prop_sim_new                     false
% 7.85/1.49  --inst_subs_new                         false
% 7.85/1.49  --inst_eq_res_simp                      false
% 7.85/1.49  --inst_subs_given                       false
% 7.85/1.49  --inst_orphan_elimination               true
% 7.85/1.49  --inst_learning_loop_flag               true
% 7.85/1.49  --inst_learning_start                   3000
% 7.85/1.49  --inst_learning_factor                  2
% 7.85/1.49  --inst_start_prop_sim_after_learn       3
% 7.85/1.49  --inst_sel_renew                        solver
% 7.85/1.49  --inst_lit_activity_flag                true
% 7.85/1.49  --inst_restr_to_given                   false
% 7.85/1.49  --inst_activity_threshold               500
% 7.85/1.49  --inst_out_proof                        true
% 7.85/1.49  
% 7.85/1.49  ------ Resolution Options
% 7.85/1.49  
% 7.85/1.49  --resolution_flag                       true
% 7.85/1.49  --res_lit_sel                           adaptive
% 7.85/1.49  --res_lit_sel_side                      none
% 7.85/1.49  --res_ordering                          kbo
% 7.85/1.49  --res_to_prop_solver                    active
% 7.85/1.49  --res_prop_simpl_new                    false
% 7.85/1.49  --res_prop_simpl_given                  true
% 7.85/1.49  --res_passive_queue_type                priority_queues
% 7.85/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.85/1.49  --res_passive_queues_freq               [15;5]
% 7.85/1.49  --res_forward_subs                      full
% 7.85/1.49  --res_backward_subs                     full
% 7.85/1.49  --res_forward_subs_resolution           true
% 7.85/1.49  --res_backward_subs_resolution          true
% 7.85/1.49  --res_orphan_elimination                true
% 7.85/1.49  --res_time_limit                        2.
% 7.85/1.49  --res_out_proof                         true
% 7.85/1.49  
% 7.85/1.49  ------ Superposition Options
% 7.85/1.49  
% 7.85/1.49  --superposition_flag                    true
% 7.85/1.49  --sup_passive_queue_type                priority_queues
% 7.85/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.85/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.85/1.49  --demod_completeness_check              fast
% 7.85/1.49  --demod_use_ground                      true
% 7.85/1.49  --sup_to_prop_solver                    passive
% 7.85/1.49  --sup_prop_simpl_new                    true
% 7.85/1.49  --sup_prop_simpl_given                  true
% 7.85/1.49  --sup_fun_splitting                     true
% 7.85/1.49  --sup_smt_interval                      50000
% 7.85/1.49  
% 7.85/1.49  ------ Superposition Simplification Setup
% 7.85/1.49  
% 7.85/1.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.85/1.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.85/1.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.85/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.85/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.85/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.85/1.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.85/1.49  --sup_immed_triv                        [TrivRules]
% 7.85/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.85/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.85/1.49  --sup_immed_bw_main                     []
% 7.85/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.85/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.85/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.85/1.49  --sup_input_bw                          []
% 7.85/1.49  
% 7.85/1.49  ------ Combination Options
% 7.85/1.49  
% 7.85/1.49  --comb_res_mult                         3
% 7.85/1.49  --comb_sup_mult                         2
% 7.85/1.49  --comb_inst_mult                        10
% 7.85/1.49  
% 7.85/1.49  ------ Debug Options
% 7.85/1.49  
% 7.85/1.49  --dbg_backtrace                         false
% 7.85/1.49  --dbg_dump_prop_clauses                 false
% 7.85/1.49  --dbg_dump_prop_clauses_file            -
% 7.85/1.49  --dbg_out_stat                          false
% 7.85/1.49  ------ Parsing...
% 7.85/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.85/1.49  
% 7.85/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.85/1.49  
% 7.85/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.85/1.49  
% 7.85/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.85/1.49  ------ Proving...
% 7.85/1.49  ------ Problem Properties 
% 7.85/1.49  
% 7.85/1.49  
% 7.85/1.49  clauses                                 54
% 7.85/1.49  conjectures                             6
% 7.85/1.49  EPR                                     7
% 7.85/1.49  Horn                                    51
% 7.85/1.49  unary                                   14
% 7.85/1.49  binary                                  17
% 7.85/1.49  lits                                    140
% 7.85/1.49  lits eq                                 33
% 7.85/1.49  fd_pure                                 0
% 7.85/1.49  fd_pseudo                               0
% 7.85/1.49  fd_cond                                 5
% 7.85/1.49  fd_pseudo_cond                          1
% 7.85/1.49  AC symbols                              0
% 7.85/1.49  
% 7.85/1.49  ------ Schedule dynamic 5 is on 
% 7.85/1.49  
% 7.85/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.85/1.49  
% 7.85/1.49  
% 7.85/1.49  ------ 
% 7.85/1.49  Current options:
% 7.85/1.49  ------ 
% 7.85/1.49  
% 7.85/1.49  ------ Input Options
% 7.85/1.49  
% 7.85/1.49  --out_options                           all
% 7.85/1.49  --tptp_safe_out                         true
% 7.85/1.49  --problem_path                          ""
% 7.85/1.49  --include_path                          ""
% 7.85/1.49  --clausifier                            res/vclausify_rel
% 7.85/1.49  --clausifier_options                    ""
% 7.85/1.49  --stdin                                 false
% 7.85/1.49  --stats_out                             all
% 7.85/1.49  
% 7.85/1.49  ------ General Options
% 7.85/1.49  
% 7.85/1.49  --fof                                   false
% 7.85/1.49  --time_out_real                         305.
% 7.85/1.49  --time_out_virtual                      -1.
% 7.85/1.49  --symbol_type_check                     false
% 7.85/1.49  --clausify_out                          false
% 7.85/1.49  --sig_cnt_out                           false
% 7.85/1.49  --trig_cnt_out                          false
% 7.85/1.49  --trig_cnt_out_tolerance                1.
% 7.85/1.49  --trig_cnt_out_sk_spl                   false
% 7.85/1.49  --abstr_cl_out                          false
% 7.85/1.49  
% 7.85/1.49  ------ Global Options
% 7.85/1.49  
% 7.85/1.49  --schedule                              default
% 7.85/1.49  --add_important_lit                     false
% 7.85/1.49  --prop_solver_per_cl                    1000
% 7.85/1.49  --min_unsat_core                        false
% 7.85/1.49  --soft_assumptions                      false
% 7.85/1.49  --soft_lemma_size                       3
% 7.85/1.49  --prop_impl_unit_size                   0
% 7.85/1.49  --prop_impl_unit                        []
% 7.85/1.49  --share_sel_clauses                     true
% 7.85/1.49  --reset_solvers                         false
% 7.85/1.49  --bc_imp_inh                            [conj_cone]
% 7.85/1.49  --conj_cone_tolerance                   3.
% 7.85/1.49  --extra_neg_conj                        none
% 7.85/1.49  --large_theory_mode                     true
% 7.85/1.49  --prolific_symb_bound                   200
% 7.85/1.49  --lt_threshold                          2000
% 7.85/1.49  --clause_weak_htbl                      true
% 7.85/1.49  --gc_record_bc_elim                     false
% 7.85/1.49  
% 7.85/1.49  ------ Preprocessing Options
% 7.85/1.49  
% 7.85/1.49  --preprocessing_flag                    true
% 7.85/1.49  --time_out_prep_mult                    0.1
% 7.85/1.49  --splitting_mode                        input
% 7.85/1.49  --splitting_grd                         true
% 7.85/1.49  --splitting_cvd                         false
% 7.85/1.49  --splitting_cvd_svl                     false
% 7.85/1.49  --splitting_nvd                         32
% 7.85/1.49  --sub_typing                            true
% 7.85/1.49  --prep_gs_sim                           true
% 7.85/1.49  --prep_unflatten                        true
% 7.85/1.49  --prep_res_sim                          true
% 7.85/1.49  --prep_upred                            true
% 7.85/1.49  --prep_sem_filter                       exhaustive
% 7.85/1.49  --prep_sem_filter_out                   false
% 7.85/1.49  --pred_elim                             true
% 7.85/1.49  --res_sim_input                         true
% 7.85/1.49  --eq_ax_congr_red                       true
% 7.85/1.49  --pure_diseq_elim                       true
% 7.85/1.49  --brand_transform                       false
% 7.85/1.49  --non_eq_to_eq                          false
% 7.85/1.49  --prep_def_merge                        true
% 7.85/1.49  --prep_def_merge_prop_impl              false
% 7.85/1.49  --prep_def_merge_mbd                    true
% 7.85/1.49  --prep_def_merge_tr_red                 false
% 7.85/1.49  --prep_def_merge_tr_cl                  false
% 7.85/1.49  --smt_preprocessing                     true
% 7.85/1.49  --smt_ac_axioms                         fast
% 7.85/1.49  --preprocessed_out                      false
% 7.85/1.49  --preprocessed_stats                    false
% 7.85/1.49  
% 7.85/1.49  ------ Abstraction refinement Options
% 7.85/1.49  
% 7.85/1.49  --abstr_ref                             []
% 7.85/1.49  --abstr_ref_prep                        false
% 7.85/1.49  --abstr_ref_until_sat                   false
% 7.85/1.49  --abstr_ref_sig_restrict                funpre
% 7.85/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.85/1.49  --abstr_ref_under                       []
% 7.85/1.49  
% 7.85/1.49  ------ SAT Options
% 7.85/1.49  
% 7.85/1.49  --sat_mode                              false
% 7.85/1.49  --sat_fm_restart_options                ""
% 7.85/1.49  --sat_gr_def                            false
% 7.85/1.49  --sat_epr_types                         true
% 7.85/1.49  --sat_non_cyclic_types                  false
% 7.85/1.49  --sat_finite_models                     false
% 7.85/1.49  --sat_fm_lemmas                         false
% 7.85/1.49  --sat_fm_prep                           false
% 7.85/1.49  --sat_fm_uc_incr                        true
% 7.85/1.49  --sat_out_model                         small
% 7.85/1.49  --sat_out_clauses                       false
% 7.85/1.49  
% 7.85/1.49  ------ QBF Options
% 7.85/1.49  
% 7.85/1.49  --qbf_mode                              false
% 7.85/1.49  --qbf_elim_univ                         false
% 7.85/1.49  --qbf_dom_inst                          none
% 7.85/1.49  --qbf_dom_pre_inst                      false
% 7.85/1.49  --qbf_sk_in                             false
% 7.85/1.49  --qbf_pred_elim                         true
% 7.85/1.49  --qbf_split                             512
% 7.85/1.49  
% 7.85/1.49  ------ BMC1 Options
% 7.85/1.49  
% 7.85/1.49  --bmc1_incremental                      false
% 7.85/1.49  --bmc1_axioms                           reachable_all
% 7.85/1.49  --bmc1_min_bound                        0
% 7.85/1.49  --bmc1_max_bound                        -1
% 7.85/1.49  --bmc1_max_bound_default                -1
% 7.85/1.49  --bmc1_symbol_reachability              true
% 7.85/1.49  --bmc1_property_lemmas                  false
% 7.85/1.49  --bmc1_k_induction                      false
% 7.85/1.49  --bmc1_non_equiv_states                 false
% 7.85/1.49  --bmc1_deadlock                         false
% 7.85/1.49  --bmc1_ucm                              false
% 7.85/1.49  --bmc1_add_unsat_core                   none
% 7.85/1.49  --bmc1_unsat_core_children              false
% 7.85/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.85/1.49  --bmc1_out_stat                         full
% 7.85/1.49  --bmc1_ground_init                      false
% 7.85/1.49  --bmc1_pre_inst_next_state              false
% 7.85/1.49  --bmc1_pre_inst_state                   false
% 7.85/1.49  --bmc1_pre_inst_reach_state             false
% 7.85/1.49  --bmc1_out_unsat_core                   false
% 7.85/1.49  --bmc1_aig_witness_out                  false
% 7.85/1.49  --bmc1_verbose                          false
% 7.85/1.49  --bmc1_dump_clauses_tptp                false
% 7.85/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.85/1.49  --bmc1_dump_file                        -
% 7.85/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.85/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.85/1.49  --bmc1_ucm_extend_mode                  1
% 7.85/1.49  --bmc1_ucm_init_mode                    2
% 7.85/1.49  --bmc1_ucm_cone_mode                    none
% 7.85/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.85/1.49  --bmc1_ucm_relax_model                  4
% 7.85/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.85/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.85/1.49  --bmc1_ucm_layered_model                none
% 7.85/1.49  --bmc1_ucm_max_lemma_size               10
% 7.85/1.49  
% 7.85/1.49  ------ AIG Options
% 7.85/1.49  
% 7.85/1.49  --aig_mode                              false
% 7.85/1.49  
% 7.85/1.49  ------ Instantiation Options
% 7.85/1.49  
% 7.85/1.49  --instantiation_flag                    true
% 7.85/1.49  --inst_sos_flag                         true
% 7.85/1.49  --inst_sos_phase                        true
% 7.85/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.85/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.85/1.49  --inst_lit_sel_side                     none
% 7.85/1.49  --inst_solver_per_active                1400
% 7.85/1.49  --inst_solver_calls_frac                1.
% 7.85/1.49  --inst_passive_queue_type               priority_queues
% 7.85/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.85/1.49  --inst_passive_queues_freq              [25;2]
% 7.85/1.49  --inst_dismatching                      true
% 7.85/1.49  --inst_eager_unprocessed_to_passive     true
% 7.85/1.49  --inst_prop_sim_given                   true
% 7.85/1.49  --inst_prop_sim_new                     false
% 7.85/1.49  --inst_subs_new                         false
% 7.85/1.49  --inst_eq_res_simp                      false
% 7.85/1.49  --inst_subs_given                       false
% 7.85/1.49  --inst_orphan_elimination               true
% 7.85/1.49  --inst_learning_loop_flag               true
% 7.85/1.49  --inst_learning_start                   3000
% 7.85/1.49  --inst_learning_factor                  2
% 7.85/1.49  --inst_start_prop_sim_after_learn       3
% 7.85/1.49  --inst_sel_renew                        solver
% 7.85/1.49  --inst_lit_activity_flag                true
% 7.85/1.49  --inst_restr_to_given                   false
% 7.85/1.49  --inst_activity_threshold               500
% 7.85/1.49  --inst_out_proof                        true
% 7.85/1.49  
% 7.85/1.49  ------ Resolution Options
% 7.85/1.49  
% 7.85/1.49  --resolution_flag                       false
% 7.85/1.49  --res_lit_sel                           adaptive
% 7.85/1.49  --res_lit_sel_side                      none
% 7.85/1.49  --res_ordering                          kbo
% 7.85/1.49  --res_to_prop_solver                    active
% 7.85/1.49  --res_prop_simpl_new                    false
% 7.85/1.49  --res_prop_simpl_given                  true
% 7.85/1.49  --res_passive_queue_type                priority_queues
% 7.85/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.85/1.49  --res_passive_queues_freq               [15;5]
% 7.85/1.49  --res_forward_subs                      full
% 7.85/1.49  --res_backward_subs                     full
% 7.85/1.49  --res_forward_subs_resolution           true
% 7.85/1.49  --res_backward_subs_resolution          true
% 7.85/1.49  --res_orphan_elimination                true
% 7.85/1.49  --res_time_limit                        2.
% 7.85/1.49  --res_out_proof                         true
% 7.85/1.49  
% 7.85/1.49  ------ Superposition Options
% 7.85/1.49  
% 7.85/1.49  --superposition_flag                    true
% 7.85/1.49  --sup_passive_queue_type                priority_queues
% 7.85/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.85/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.85/1.49  --demod_completeness_check              fast
% 7.85/1.49  --demod_use_ground                      true
% 7.85/1.49  --sup_to_prop_solver                    passive
% 7.85/1.49  --sup_prop_simpl_new                    true
% 7.85/1.49  --sup_prop_simpl_given                  true
% 7.85/1.49  --sup_fun_splitting                     true
% 7.85/1.49  --sup_smt_interval                      50000
% 7.85/1.49  
% 7.85/1.49  ------ Superposition Simplification Setup
% 7.85/1.49  
% 7.85/1.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.85/1.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.85/1.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.85/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.85/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.85/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.85/1.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.85/1.49  --sup_immed_triv                        [TrivRules]
% 7.85/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.85/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.85/1.49  --sup_immed_bw_main                     []
% 7.85/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.85/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.85/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.85/1.49  --sup_input_bw                          []
% 7.85/1.49  
% 7.85/1.49  ------ Combination Options
% 7.85/1.49  
% 7.85/1.49  --comb_res_mult                         3
% 7.85/1.49  --comb_sup_mult                         2
% 7.85/1.49  --comb_inst_mult                        10
% 7.85/1.49  
% 7.85/1.49  ------ Debug Options
% 7.85/1.49  
% 7.85/1.49  --dbg_backtrace                         false
% 7.85/1.49  --dbg_dump_prop_clauses                 false
% 7.85/1.49  --dbg_dump_prop_clauses_file            -
% 7.85/1.49  --dbg_out_stat                          false
% 7.85/1.49  
% 7.85/1.49  
% 7.85/1.49  
% 7.85/1.49  
% 7.85/1.49  ------ Proving...
% 7.85/1.49  
% 7.85/1.49  
% 7.85/1.49  % SZS status Theorem for theBenchmark.p
% 7.85/1.49  
% 7.85/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.85/1.49  
% 7.85/1.49  fof(f19,axiom,(
% 7.85/1.49    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 7.85/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.85/1.49  
% 7.85/1.49  fof(f116,plain,(
% 7.85/1.49    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 7.85/1.49    inference(cnf_transformation,[],[f19])).
% 7.85/1.49  
% 7.85/1.49  fof(f34,axiom,(
% 7.85/1.49    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 7.85/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.85/1.49  
% 7.85/1.49  fof(f136,plain,(
% 7.85/1.49    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 7.85/1.49    inference(cnf_transformation,[],[f34])).
% 7.85/1.49  
% 7.85/1.49  fof(f155,plain,(
% 7.85/1.49    k1_xboole_0 = k6_partfun1(k1_xboole_0)),
% 7.85/1.49    inference(definition_unfolding,[],[f116,f136])).
% 7.85/1.49  
% 7.85/1.49  fof(f33,axiom,(
% 7.85/1.49    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 7.85/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.85/1.49  
% 7.85/1.49  fof(f135,plain,(
% 7.85/1.49    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 7.85/1.49    inference(cnf_transformation,[],[f33])).
% 7.85/1.49  
% 7.85/1.49  fof(f36,axiom,(
% 7.85/1.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X1,X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 7.85/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.85/1.49  
% 7.85/1.49  fof(f77,plain,(
% 7.85/1.49    ! [X0,X1,X2,X3] : ((((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | ~r1_tarski(X1,X2)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 7.85/1.49    inference(ennf_transformation,[],[f36])).
% 7.85/1.49  
% 7.85/1.49  fof(f78,plain,(
% 7.85/1.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~r1_tarski(X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 7.85/1.49    inference(flattening,[],[f77])).
% 7.85/1.49  
% 7.85/1.49  fof(f143,plain,(
% 7.85/1.49    ( ! [X2,X0,X3,X1] : (v1_funct_2(X3,X0,X2) | k1_xboole_0 != X0 | ~r1_tarski(X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 7.85/1.49    inference(cnf_transformation,[],[f78])).
% 7.85/1.49  
% 7.85/1.49  fof(f161,plain,(
% 7.85/1.49    ( ! [X2,X3,X1] : (v1_funct_2(X3,k1_xboole_0,X2) | ~r1_tarski(X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_2(X3,k1_xboole_0,X1) | ~v1_funct_1(X3)) )),
% 7.85/1.49    inference(equality_resolution,[],[f143])).
% 7.85/1.49  
% 7.85/1.49  fof(f23,axiom,(
% 7.85/1.49    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 7.85/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.85/1.49  
% 7.85/1.49  fof(f122,plain,(
% 7.85/1.49    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 7.85/1.49    inference(cnf_transformation,[],[f23])).
% 7.85/1.49  
% 7.85/1.49  fof(f156,plain,(
% 7.85/1.49    ( ! [X0] : (v1_funct_1(k6_partfun1(X0))) )),
% 7.85/1.49    inference(definition_unfolding,[],[f122,f136])).
% 7.85/1.49  
% 7.85/1.49  fof(f3,axiom,(
% 7.85/1.49    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 7.85/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.85/1.49  
% 7.85/1.49  fof(f41,plain,(
% 7.85/1.49    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 7.85/1.49    inference(ennf_transformation,[],[f3])).
% 7.85/1.49  
% 7.85/1.49  fof(f94,plain,(
% 7.85/1.49    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 7.85/1.49    inference(cnf_transformation,[],[f41])).
% 7.85/1.49  
% 7.85/1.49  fof(f2,axiom,(
% 7.85/1.49    v1_xboole_0(k1_xboole_0)),
% 7.85/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.85/1.49  
% 7.85/1.49  fof(f93,plain,(
% 7.85/1.49    v1_xboole_0(k1_xboole_0)),
% 7.85/1.49    inference(cnf_transformation,[],[f2])).
% 7.85/1.49  
% 7.85/1.49  fof(f32,axiom,(
% 7.85/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_partfun1(X2,X0) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 7.85/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.85/1.49  
% 7.85/1.49  fof(f73,plain,(
% 7.85/1.49    ! [X0,X1,X2] : (((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~v1_partfun1(X2,X0) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.85/1.49    inference(ennf_transformation,[],[f32])).
% 7.85/1.49  
% 7.85/1.49  fof(f74,plain,(
% 7.85/1.49    ! [X0,X1,X2] : ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.85/1.49    inference(flattening,[],[f73])).
% 7.85/1.49  
% 7.85/1.49  fof(f133,plain,(
% 7.85/1.49    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.85/1.49    inference(cnf_transformation,[],[f74])).
% 7.85/1.49  
% 7.85/1.49  fof(f134,plain,(
% 7.85/1.49    ( ! [X0] : (v1_partfun1(k6_partfun1(X0),X0)) )),
% 7.85/1.49    inference(cnf_transformation,[],[f33])).
% 7.85/1.49  
% 7.85/1.49  fof(f145,plain,(
% 7.85/1.49    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | k1_xboole_0 != X0 | ~r1_tarski(X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 7.85/1.49    inference(cnf_transformation,[],[f78])).
% 7.85/1.49  
% 7.85/1.49  fof(f160,plain,(
% 7.85/1.49    ( ! [X2,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2))) | ~r1_tarski(X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_2(X3,k1_xboole_0,X1) | ~v1_funct_1(X3)) )),
% 7.85/1.49    inference(equality_resolution,[],[f145])).
% 7.85/1.49  
% 7.85/1.49  fof(f37,conjecture,(
% 7.85/1.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 7.85/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.85/1.49  
% 7.85/1.49  fof(f38,negated_conjecture,(
% 7.85/1.49    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 7.85/1.49    inference(negated_conjecture,[],[f37])).
% 7.85/1.49  
% 7.85/1.49  fof(f79,plain,(
% 7.85/1.49    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 7.85/1.49    inference(ennf_transformation,[],[f38])).
% 7.85/1.49  
% 7.85/1.49  fof(f80,plain,(
% 7.85/1.49    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 7.85/1.49    inference(flattening,[],[f79])).
% 7.85/1.49  
% 7.85/1.49  fof(f88,plain,(
% 7.85/1.49    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))) & k2_relset_1(sK1,sK2,sK3) = sK2 & v2_funct_1(sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3))),
% 7.85/1.49    introduced(choice_axiom,[])).
% 7.85/1.49  
% 7.85/1.49  fof(f89,plain,(
% 7.85/1.49    (~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))) & k2_relset_1(sK1,sK2,sK3) = sK2 & v2_funct_1(sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)),
% 7.85/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f80,f88])).
% 7.85/1.49  
% 7.85/1.49  fof(f148,plain,(
% 7.85/1.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 7.85/1.49    inference(cnf_transformation,[],[f89])).
% 7.85/1.49  
% 7.85/1.49  fof(f29,axiom,(
% 7.85/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 7.85/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.85/1.49  
% 7.85/1.49  fof(f70,plain,(
% 7.85/1.49    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.85/1.49    inference(ennf_transformation,[],[f29])).
% 7.85/1.49  
% 7.85/1.49  fof(f129,plain,(
% 7.85/1.49    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.85/1.49    inference(cnf_transformation,[],[f70])).
% 7.85/1.49  
% 7.85/1.49  fof(f14,axiom,(
% 7.85/1.49    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0)))),
% 7.85/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.85/1.49  
% 7.85/1.49  fof(f50,plain,(
% 7.85/1.49    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 7.85/1.49    inference(ennf_transformation,[],[f14])).
% 7.85/1.49  
% 7.85/1.49  fof(f108,plain,(
% 7.85/1.49    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 7.85/1.49    inference(cnf_transformation,[],[f50])).
% 7.85/1.49  
% 7.85/1.49  fof(f35,axiom,(
% 7.85/1.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 7.85/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.85/1.49  
% 7.85/1.49  fof(f75,plain,(
% 7.85/1.49    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.85/1.49    inference(ennf_transformation,[],[f35])).
% 7.85/1.49  
% 7.85/1.49  fof(f76,plain,(
% 7.85/1.49    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.85/1.49    inference(flattening,[],[f75])).
% 7.85/1.49  
% 7.85/1.49  fof(f139,plain,(
% 7.85/1.49    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.85/1.49    inference(cnf_transformation,[],[f76])).
% 7.85/1.49  
% 7.85/1.49  fof(f31,axiom,(
% 7.85/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 7.85/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.85/1.49  
% 7.85/1.49  fof(f72,plain,(
% 7.85/1.49    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.85/1.49    inference(ennf_transformation,[],[f31])).
% 7.85/1.49  
% 7.85/1.49  fof(f131,plain,(
% 7.85/1.49    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.85/1.49    inference(cnf_transformation,[],[f72])).
% 7.85/1.49  
% 7.85/1.49  fof(f150,plain,(
% 7.85/1.49    k2_relset_1(sK1,sK2,sK3) = sK2),
% 7.85/1.49    inference(cnf_transformation,[],[f89])).
% 7.85/1.49  
% 7.85/1.49  fof(f107,plain,(
% 7.85/1.49    ( ! [X0] : (k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 7.85/1.49    inference(cnf_transformation,[],[f50])).
% 7.85/1.49  
% 7.85/1.49  fof(f146,plain,(
% 7.85/1.49    v1_funct_1(sK3)),
% 7.85/1.49    inference(cnf_transformation,[],[f89])).
% 7.85/1.49  
% 7.85/1.49  fof(f9,axiom,(
% 7.85/1.49    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 7.85/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.85/1.49  
% 7.85/1.49  fof(f44,plain,(
% 7.85/1.49    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 7.85/1.49    inference(ennf_transformation,[],[f9])).
% 7.85/1.50  
% 7.85/1.50  fof(f102,plain,(
% 7.85/1.50    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 7.85/1.50    inference(cnf_transformation,[],[f44])).
% 7.85/1.50  
% 7.85/1.50  fof(f21,axiom,(
% 7.85/1.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 7.85/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.85/1.50  
% 7.85/1.50  fof(f56,plain,(
% 7.85/1.50    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.85/1.50    inference(ennf_transformation,[],[f21])).
% 7.85/1.50  
% 7.85/1.50  fof(f57,plain,(
% 7.85/1.50    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.85/1.50    inference(flattening,[],[f56])).
% 7.85/1.50  
% 7.85/1.50  fof(f118,plain,(
% 7.85/1.50    ( ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.85/1.50    inference(cnf_transformation,[],[f57])).
% 7.85/1.50  
% 7.85/1.50  fof(f149,plain,(
% 7.85/1.50    v2_funct_1(sK3)),
% 7.85/1.50    inference(cnf_transformation,[],[f89])).
% 7.85/1.50  
% 7.85/1.50  fof(f22,axiom,(
% 7.85/1.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 7.85/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.85/1.50  
% 7.85/1.50  fof(f58,plain,(
% 7.85/1.50    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.85/1.50    inference(ennf_transformation,[],[f22])).
% 7.85/1.50  
% 7.85/1.50  fof(f59,plain,(
% 7.85/1.50    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.85/1.50    inference(flattening,[],[f58])).
% 7.85/1.50  
% 7.85/1.50  fof(f120,plain,(
% 7.85/1.50    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.85/1.50    inference(cnf_transformation,[],[f59])).
% 7.85/1.50  
% 7.85/1.50  fof(f142,plain,(
% 7.85/1.50    ( ! [X2,X0,X3,X1] : (v1_funct_2(X3,X0,X2) | k1_xboole_0 = X1 | ~r1_tarski(X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 7.85/1.50    inference(cnf_transformation,[],[f78])).
% 7.85/1.50  
% 7.85/1.50  fof(f138,plain,(
% 7.85/1.50    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.85/1.50    inference(cnf_transformation,[],[f76])).
% 7.85/1.50  
% 7.85/1.50  fof(f144,plain,(
% 7.85/1.50    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | k1_xboole_0 = X1 | ~r1_tarski(X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 7.85/1.50    inference(cnf_transformation,[],[f78])).
% 7.85/1.50  
% 7.85/1.50  fof(f151,plain,(
% 7.85/1.50    ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))),
% 7.85/1.50    inference(cnf_transformation,[],[f89])).
% 7.85/1.50  
% 7.85/1.50  fof(f30,axiom,(
% 7.85/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 7.85/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.85/1.50  
% 7.85/1.50  fof(f39,plain,(
% 7.85/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 7.85/1.50    inference(pure_predicate_removal,[],[f30])).
% 7.85/1.50  
% 7.85/1.50  fof(f71,plain,(
% 7.85/1.50    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.85/1.50    inference(ennf_transformation,[],[f39])).
% 7.85/1.50  
% 7.85/1.50  fof(f130,plain,(
% 7.85/1.50    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.85/1.50    inference(cnf_transformation,[],[f71])).
% 7.85/1.50  
% 7.85/1.50  fof(f8,axiom,(
% 7.85/1.50    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 7.85/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.85/1.50  
% 7.85/1.50  fof(f43,plain,(
% 7.85/1.50    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.85/1.50    inference(ennf_transformation,[],[f8])).
% 7.85/1.50  
% 7.85/1.50  fof(f86,plain,(
% 7.85/1.50    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 7.85/1.50    inference(nnf_transformation,[],[f43])).
% 7.85/1.50  
% 7.85/1.50  fof(f100,plain,(
% 7.85/1.50    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.85/1.50    inference(cnf_transformation,[],[f86])).
% 7.85/1.50  
% 7.85/1.50  fof(f16,axiom,(
% 7.85/1.50    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 7.85/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.85/1.50  
% 7.85/1.50  fof(f53,plain,(
% 7.85/1.50    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 7.85/1.50    inference(ennf_transformation,[],[f16])).
% 7.85/1.50  
% 7.85/1.50  fof(f87,plain,(
% 7.85/1.50    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 7.85/1.50    inference(nnf_transformation,[],[f53])).
% 7.85/1.50  
% 7.85/1.50  fof(f112,plain,(
% 7.85/1.50    ( ! [X0] : (k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 7.85/1.50    inference(cnf_transformation,[],[f87])).
% 7.85/1.50  
% 7.85/1.50  fof(f15,axiom,(
% 7.85/1.50    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 7.85/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.85/1.50  
% 7.85/1.50  fof(f51,plain,(
% 7.85/1.50    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 7.85/1.50    inference(ennf_transformation,[],[f15])).
% 7.85/1.50  
% 7.85/1.50  fof(f52,plain,(
% 7.85/1.50    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 7.85/1.50    inference(flattening,[],[f51])).
% 7.85/1.50  
% 7.85/1.50  fof(f110,plain,(
% 7.85/1.50    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 7.85/1.50    inference(cnf_transformation,[],[f52])).
% 7.85/1.50  
% 7.85/1.50  fof(f121,plain,(
% 7.85/1.50    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 7.85/1.50    inference(cnf_transformation,[],[f23])).
% 7.85/1.50  
% 7.85/1.50  fof(f157,plain,(
% 7.85/1.50    ( ! [X0] : (v1_relat_1(k6_partfun1(X0))) )),
% 7.85/1.50    inference(definition_unfolding,[],[f121,f136])).
% 7.85/1.50  
% 7.85/1.50  fof(f17,axiom,(
% 7.85/1.50    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 7.85/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.85/1.50  
% 7.85/1.50  fof(f114,plain,(
% 7.85/1.50    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 7.85/1.50    inference(cnf_transformation,[],[f17])).
% 7.85/1.50  
% 7.85/1.50  fof(f152,plain,(
% 7.85/1.50    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 7.85/1.50    inference(definition_unfolding,[],[f114,f136])).
% 7.85/1.50  
% 7.85/1.50  fof(f109,plain,(
% 7.85/1.50    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 7.85/1.50    inference(cnf_transformation,[],[f52])).
% 7.85/1.50  
% 7.85/1.50  cnf(c_26,plain,
% 7.85/1.50      ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
% 7.85/1.50      inference(cnf_transformation,[],[f155]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_44,plain,
% 7.85/1.50      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 7.85/1.50      inference(cnf_transformation,[],[f135]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_4153,plain,
% 7.85/1.50      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
% 7.85/1.50      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_5084,plain,
% 7.85/1.50      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 7.85/1.50      inference(superposition,[status(thm)],[c_26,c_4153]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_51,plain,
% 7.85/1.50      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 7.85/1.50      | v1_funct_2(X0,k1_xboole_0,X2)
% 7.85/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 7.85/1.50      | ~ r1_tarski(X1,X2)
% 7.85/1.50      | ~ v1_funct_1(X0) ),
% 7.85/1.50      inference(cnf_transformation,[],[f161]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_4148,plain,
% 7.85/1.50      ( v1_funct_2(X0,k1_xboole_0,X1) != iProver_top
% 7.85/1.50      | v1_funct_2(X0,k1_xboole_0,X2) = iProver_top
% 7.85/1.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) != iProver_top
% 7.85/1.50      | r1_tarski(X1,X2) != iProver_top
% 7.85/1.50      | v1_funct_1(X0) != iProver_top ),
% 7.85/1.50      inference(predicate_to_equality,[status(thm)],[c_51]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_6273,plain,
% 7.85/1.50      ( v1_funct_2(k1_xboole_0,k1_xboole_0,X0) = iProver_top
% 7.85/1.50      | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top
% 7.85/1.50      | r1_tarski(k1_xboole_0,X0) != iProver_top
% 7.85/1.50      | v1_funct_1(k1_xboole_0) != iProver_top ),
% 7.85/1.50      inference(superposition,[status(thm)],[c_5084,c_4148]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_31,plain,
% 7.85/1.50      ( v1_funct_1(k6_partfun1(X0)) ),
% 7.85/1.50      inference(cnf_transformation,[],[f156]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_119,plain,
% 7.85/1.50      ( v1_funct_1(k6_partfun1(X0)) = iProver_top ),
% 7.85/1.50      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_121,plain,
% 7.85/1.50      ( v1_funct_1(k6_partfun1(k1_xboole_0)) = iProver_top ),
% 7.85/1.50      inference(instantiation,[status(thm)],[c_119]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_4,plain,
% 7.85/1.50      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 7.85/1.50      inference(cnf_transformation,[],[f94]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_192,plain,
% 7.85/1.50      ( ~ v1_xboole_0(k1_xboole_0) | k1_xboole_0 = k1_xboole_0 ),
% 7.85/1.50      inference(instantiation,[status(thm)],[c_4]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_3,plain,
% 7.85/1.50      ( v1_xboole_0(k1_xboole_0) ),
% 7.85/1.50      inference(cnf_transformation,[],[f93]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_3106,plain,
% 7.85/1.50      ( ~ v1_funct_1(X0) | v1_funct_1(X1) | X1 != X0 ),
% 7.85/1.50      theory(equality) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_4341,plain,
% 7.85/1.50      ( v1_funct_1(X0)
% 7.85/1.50      | ~ v1_funct_1(k6_partfun1(X1))
% 7.85/1.50      | X0 != k6_partfun1(X1) ),
% 7.85/1.50      inference(instantiation,[status(thm)],[c_3106]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_4342,plain,
% 7.85/1.50      ( X0 != k6_partfun1(X1)
% 7.85/1.50      | v1_funct_1(X0) = iProver_top
% 7.85/1.50      | v1_funct_1(k6_partfun1(X1)) != iProver_top ),
% 7.85/1.50      inference(predicate_to_equality,[status(thm)],[c_4341]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_4344,plain,
% 7.85/1.50      ( k1_xboole_0 != k6_partfun1(k1_xboole_0)
% 7.85/1.50      | v1_funct_1(k6_partfun1(k1_xboole_0)) != iProver_top
% 7.85/1.50      | v1_funct_1(k1_xboole_0) = iProver_top ),
% 7.85/1.50      inference(instantiation,[status(thm)],[c_4342]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_3090,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_4782,plain,
% 7.85/1.50      ( X0 != X1 | X0 = k6_partfun1(X2) | k6_partfun1(X2) != X1 ),
% 7.85/1.50      inference(instantiation,[status(thm)],[c_3090]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_4783,plain,
% 7.85/1.50      ( k6_partfun1(k1_xboole_0) != k1_xboole_0
% 7.85/1.50      | k1_xboole_0 = k6_partfun1(k1_xboole_0)
% 7.85/1.50      | k1_xboole_0 != k1_xboole_0 ),
% 7.85/1.50      inference(instantiation,[status(thm)],[c_4782]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_42,plain,
% 7.85/1.50      ( v1_funct_2(X0,X1,X2)
% 7.85/1.50      | ~ v1_partfun1(X0,X1)
% 7.85/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.85/1.50      | ~ v1_funct_1(X0) ),
% 7.85/1.50      inference(cnf_transformation,[],[f133]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_45,plain,
% 7.85/1.50      ( v1_partfun1(k6_partfun1(X0),X0) ),
% 7.85/1.50      inference(cnf_transformation,[],[f134]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_712,plain,
% 7.85/1.50      ( v1_funct_2(X0,X1,X2)
% 7.85/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.85/1.50      | ~ v1_funct_1(X0)
% 7.85/1.50      | X3 != X1
% 7.85/1.50      | k6_partfun1(X3) != X0 ),
% 7.85/1.50      inference(resolution_lifted,[status(thm)],[c_42,c_45]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_713,plain,
% 7.85/1.50      ( v1_funct_2(k6_partfun1(X0),X0,X1)
% 7.85/1.50      | ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.85/1.50      | ~ v1_funct_1(k6_partfun1(X0)) ),
% 7.85/1.50      inference(unflattening,[status(thm)],[c_712]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_717,plain,
% 7.85/1.50      ( ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.85/1.50      | v1_funct_2(k6_partfun1(X0),X0,X1) ),
% 7.85/1.50      inference(global_propositional_subsumption,
% 7.85/1.50                [status(thm)],
% 7.85/1.50                [c_713,c_31]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_718,plain,
% 7.85/1.50      ( v1_funct_2(k6_partfun1(X0),X0,X1)
% 7.85/1.50      | ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 7.85/1.50      inference(renaming,[status(thm)],[c_717]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_4139,plain,
% 7.85/1.50      ( v1_funct_2(k6_partfun1(X0),X0,X1) = iProver_top
% 7.85/1.50      | m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.85/1.50      inference(predicate_to_equality,[status(thm)],[c_718]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_5020,plain,
% 7.85/1.50      ( v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,X0) = iProver_top
% 7.85/1.50      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
% 7.85/1.50      inference(superposition,[status(thm)],[c_26,c_4139]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_5021,plain,
% 7.85/1.50      ( v1_funct_2(k1_xboole_0,k1_xboole_0,X0) = iProver_top
% 7.85/1.50      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
% 7.85/1.50      inference(light_normalisation,[status(thm)],[c_5020,c_26]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_5023,plain,
% 7.85/1.50      ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) = iProver_top
% 7.85/1.50      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 7.85/1.50      inference(instantiation,[status(thm)],[c_5021]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_17026,plain,
% 7.85/1.50      ( r1_tarski(k1_xboole_0,X0) != iProver_top
% 7.85/1.50      | v1_funct_2(k1_xboole_0,k1_xboole_0,X0) = iProver_top ),
% 7.85/1.50      inference(global_propositional_subsumption,
% 7.85/1.50                [status(thm)],
% 7.85/1.50                [c_6273,c_121,c_26,c_192,c_3,c_4344,c_4783,c_5023,c_5084]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_17027,plain,
% 7.85/1.50      ( v1_funct_2(k1_xboole_0,k1_xboole_0,X0) = iProver_top
% 7.85/1.50      | r1_tarski(k1_xboole_0,X0) != iProver_top ),
% 7.85/1.50      inference(renaming,[status(thm)],[c_17026]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_49,plain,
% 7.85/1.50      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 7.85/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 7.85/1.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))
% 7.85/1.50      | ~ r1_tarski(X1,X2)
% 7.85/1.50      | ~ v1_funct_1(X0) ),
% 7.85/1.50      inference(cnf_transformation,[],[f160]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_4150,plain,
% 7.85/1.50      ( v1_funct_2(X0,k1_xboole_0,X1) != iProver_top
% 7.85/1.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) != iProver_top
% 7.85/1.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2))) = iProver_top
% 7.85/1.50      | r1_tarski(X1,X2) != iProver_top
% 7.85/1.50      | v1_funct_1(X0) != iProver_top ),
% 7.85/1.50      inference(predicate_to_equality,[status(thm)],[c_49]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_7822,plain,
% 7.85/1.50      ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top
% 7.85/1.50      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) = iProver_top
% 7.85/1.50      | r1_tarski(k1_xboole_0,X0) != iProver_top
% 7.85/1.50      | v1_funct_1(k1_xboole_0) != iProver_top ),
% 7.85/1.50      inference(superposition,[status(thm)],[c_5084,c_4150]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_21069,plain,
% 7.85/1.50      ( r1_tarski(k1_xboole_0,X0) != iProver_top
% 7.85/1.50      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) = iProver_top ),
% 7.85/1.50      inference(global_propositional_subsumption,
% 7.85/1.50                [status(thm)],
% 7.85/1.50                [c_7822,c_121,c_26,c_192,c_3,c_4344,c_4783,c_5023,c_5084]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_21070,plain,
% 7.85/1.50      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) = iProver_top
% 7.85/1.50      | r1_tarski(k1_xboole_0,X0) != iProver_top ),
% 7.85/1.50      inference(renaming,[status(thm)],[c_21069]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_58,negated_conjecture,
% 7.85/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 7.85/1.50      inference(cnf_transformation,[],[f148]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_4144,plain,
% 7.85/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 7.85/1.50      inference(predicate_to_equality,[status(thm)],[c_58]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_39,plain,
% 7.85/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.85/1.50      | v1_relat_1(X0) ),
% 7.85/1.50      inference(cnf_transformation,[],[f129]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_4155,plain,
% 7.85/1.50      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.85/1.50      | v1_relat_1(X0) = iProver_top ),
% 7.85/1.50      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_6223,plain,
% 7.85/1.50      ( v1_relat_1(sK3) = iProver_top ),
% 7.85/1.50      inference(superposition,[status(thm)],[c_4144,c_4155]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_17,plain,
% 7.85/1.50      ( ~ v1_relat_1(X0) | k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) ),
% 7.85/1.50      inference(cnf_transformation,[],[f108]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_4173,plain,
% 7.85/1.50      ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
% 7.85/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.85/1.50      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_6267,plain,
% 7.85/1.50      ( k2_relat_1(k4_relat_1(sK3)) = k1_relat_1(sK3) ),
% 7.85/1.50      inference(superposition,[status(thm)],[c_6223,c_4173]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_46,plain,
% 7.85/1.50      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 7.85/1.50      | ~ v1_funct_1(X0)
% 7.85/1.50      | ~ v1_relat_1(X0) ),
% 7.85/1.50      inference(cnf_transformation,[],[f139]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_4152,plain,
% 7.85/1.50      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
% 7.85/1.50      | v1_funct_1(X0) != iProver_top
% 7.85/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.85/1.50      inference(predicate_to_equality,[status(thm)],[c_46]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_9352,plain,
% 7.85/1.50      ( m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k4_relat_1(sK3)),k1_relat_1(sK3)))) = iProver_top
% 7.85/1.50      | v1_funct_1(k4_relat_1(sK3)) != iProver_top
% 7.85/1.50      | v1_relat_1(k4_relat_1(sK3)) != iProver_top ),
% 7.85/1.50      inference(superposition,[status(thm)],[c_6267,c_4152]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_41,plain,
% 7.85/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.85/1.50      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 7.85/1.50      inference(cnf_transformation,[],[f131]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_4154,plain,
% 7.85/1.50      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 7.85/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.85/1.50      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_7866,plain,
% 7.85/1.50      ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
% 7.85/1.50      inference(superposition,[status(thm)],[c_4144,c_4154]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_56,negated_conjecture,
% 7.85/1.50      ( k2_relset_1(sK1,sK2,sK3) = sK2 ),
% 7.85/1.50      inference(cnf_transformation,[],[f150]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_7873,plain,
% 7.85/1.50      ( k2_relat_1(sK3) = sK2 ),
% 7.85/1.50      inference(light_normalisation,[status(thm)],[c_7866,c_56]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_18,plain,
% 7.85/1.50      ( ~ v1_relat_1(X0) | k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0) ),
% 7.85/1.50      inference(cnf_transformation,[],[f107]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_4172,plain,
% 7.85/1.50      ( k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0)
% 7.85/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.85/1.50      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_6268,plain,
% 7.85/1.50      ( k1_relat_1(k4_relat_1(sK3)) = k2_relat_1(sK3) ),
% 7.85/1.50      inference(superposition,[status(thm)],[c_6223,c_4172]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_7891,plain,
% 7.85/1.50      ( k1_relat_1(k4_relat_1(sK3)) = sK2 ),
% 7.85/1.50      inference(demodulation,[status(thm)],[c_7873,c_6268]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_9362,plain,
% 7.85/1.50      ( m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3)))) = iProver_top
% 7.85/1.50      | v1_funct_1(k4_relat_1(sK3)) != iProver_top
% 7.85/1.50      | v1_relat_1(k4_relat_1(sK3)) != iProver_top ),
% 7.85/1.50      inference(light_normalisation,[status(thm)],[c_9352,c_7891]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_60,negated_conjecture,
% 7.85/1.50      ( v1_funct_1(sK3) ),
% 7.85/1.50      inference(cnf_transformation,[],[f146]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_61,plain,
% 7.85/1.50      ( v1_funct_1(sK3) = iProver_top ),
% 7.85/1.50      inference(predicate_to_equality,[status(thm)],[c_60]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_63,plain,
% 7.85/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 7.85/1.50      inference(predicate_to_equality,[status(thm)],[c_58]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_4257,plain,
% 7.85/1.50      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.85/1.50      | v1_relat_1(sK3) ),
% 7.85/1.50      inference(instantiation,[status(thm)],[c_39]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_4308,plain,
% 7.85/1.50      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 7.85/1.50      | v1_relat_1(sK3) ),
% 7.85/1.50      inference(instantiation,[status(thm)],[c_4257]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_4309,plain,
% 7.85/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 7.85/1.50      | v1_relat_1(sK3) = iProver_top ),
% 7.85/1.50      inference(predicate_to_equality,[status(thm)],[c_4308]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_12,plain,
% 7.85/1.50      ( ~ v1_relat_1(X0) | v1_relat_1(k4_relat_1(X0)) ),
% 7.85/1.50      inference(cnf_transformation,[],[f102]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_9053,plain,
% 7.85/1.50      ( v1_relat_1(k4_relat_1(sK3)) | ~ v1_relat_1(sK3) ),
% 7.85/1.50      inference(instantiation,[status(thm)],[c_12]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_9054,plain,
% 7.85/1.50      ( v1_relat_1(k4_relat_1(sK3)) = iProver_top
% 7.85/1.50      | v1_relat_1(sK3) != iProver_top ),
% 7.85/1.50      inference(predicate_to_equality,[status(thm)],[c_9053]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_4142,plain,
% 7.85/1.50      ( v1_funct_1(sK3) = iProver_top ),
% 7.85/1.50      inference(predicate_to_equality,[status(thm)],[c_60]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_28,plain,
% 7.85/1.50      ( ~ v1_funct_1(X0)
% 7.85/1.50      | ~ v2_funct_1(X0)
% 7.85/1.50      | ~ v1_relat_1(X0)
% 7.85/1.50      | k2_funct_1(X0) = k4_relat_1(X0) ),
% 7.85/1.50      inference(cnf_transformation,[],[f118]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_4165,plain,
% 7.85/1.50      ( k2_funct_1(X0) = k4_relat_1(X0)
% 7.85/1.50      | v1_funct_1(X0) != iProver_top
% 7.85/1.50      | v2_funct_1(X0) != iProver_top
% 7.85/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.85/1.50      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_9391,plain,
% 7.85/1.50      ( k2_funct_1(sK3) = k4_relat_1(sK3)
% 7.85/1.50      | v2_funct_1(sK3) != iProver_top
% 7.85/1.50      | v1_relat_1(sK3) != iProver_top ),
% 7.85/1.50      inference(superposition,[status(thm)],[c_4142,c_4165]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_57,negated_conjecture,
% 7.85/1.50      ( v2_funct_1(sK3) ),
% 7.85/1.50      inference(cnf_transformation,[],[f149]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_878,plain,
% 7.85/1.50      ( ~ v1_funct_1(X0)
% 7.85/1.50      | ~ v1_relat_1(X0)
% 7.85/1.50      | k2_funct_1(X0) = k4_relat_1(X0)
% 7.85/1.50      | sK3 != X0 ),
% 7.85/1.50      inference(resolution_lifted,[status(thm)],[c_28,c_57]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_879,plain,
% 7.85/1.50      ( ~ v1_funct_1(sK3)
% 7.85/1.50      | ~ v1_relat_1(sK3)
% 7.85/1.50      | k2_funct_1(sK3) = k4_relat_1(sK3) ),
% 7.85/1.50      inference(unflattening,[status(thm)],[c_878]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_9784,plain,
% 7.85/1.50      ( k2_funct_1(sK3) = k4_relat_1(sK3) ),
% 7.85/1.50      inference(global_propositional_subsumption,
% 7.85/1.50                [status(thm)],
% 7.85/1.50                [c_9391,c_60,c_58,c_879,c_4308]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_29,plain,
% 7.85/1.50      ( ~ v1_funct_1(X0)
% 7.85/1.50      | v1_funct_1(k2_funct_1(X0))
% 7.85/1.50      | ~ v1_relat_1(X0) ),
% 7.85/1.50      inference(cnf_transformation,[],[f120]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_4164,plain,
% 7.85/1.50      ( v1_funct_1(X0) != iProver_top
% 7.85/1.50      | v1_funct_1(k2_funct_1(X0)) = iProver_top
% 7.85/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.85/1.50      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_9790,plain,
% 7.85/1.50      ( v1_funct_1(k4_relat_1(sK3)) = iProver_top
% 7.85/1.50      | v1_funct_1(sK3) != iProver_top
% 7.85/1.50      | v1_relat_1(sK3) != iProver_top ),
% 7.85/1.50      inference(superposition,[status(thm)],[c_9784,c_4164]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_10740,plain,
% 7.85/1.50      ( m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3)))) = iProver_top ),
% 7.85/1.50      inference(global_propositional_subsumption,
% 7.85/1.50                [status(thm)],
% 7.85/1.50                [c_9362,c_61,c_63,c_4309,c_9054,c_9790]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_52,plain,
% 7.85/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.85/1.50      | v1_funct_2(X0,X1,X3)
% 7.85/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.85/1.50      | ~ r1_tarski(X2,X3)
% 7.85/1.50      | ~ v1_funct_1(X0)
% 7.85/1.50      | k1_xboole_0 = X2 ),
% 7.85/1.50      inference(cnf_transformation,[],[f142]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_4147,plain,
% 7.85/1.50      ( k1_xboole_0 = X0
% 7.85/1.50      | v1_funct_2(X1,X2,X0) != iProver_top
% 7.85/1.50      | v1_funct_2(X1,X2,X3) = iProver_top
% 7.85/1.50      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 7.85/1.50      | r1_tarski(X0,X3) != iProver_top
% 7.85/1.50      | v1_funct_1(X1) != iProver_top ),
% 7.85/1.50      inference(predicate_to_equality,[status(thm)],[c_52]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_10749,plain,
% 7.85/1.50      ( k1_relat_1(sK3) = k1_xboole_0
% 7.85/1.50      | v1_funct_2(k4_relat_1(sK3),sK2,X0) = iProver_top
% 7.85/1.50      | v1_funct_2(k4_relat_1(sK3),sK2,k1_relat_1(sK3)) != iProver_top
% 7.85/1.50      | r1_tarski(k1_relat_1(sK3),X0) != iProver_top
% 7.85/1.50      | v1_funct_1(k4_relat_1(sK3)) != iProver_top ),
% 7.85/1.50      inference(superposition,[status(thm)],[c_10740,c_4147]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_47,plain,
% 7.85/1.50      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
% 7.85/1.50      | ~ v1_funct_1(X0)
% 7.85/1.50      | ~ v1_relat_1(X0) ),
% 7.85/1.50      inference(cnf_transformation,[],[f138]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_4151,plain,
% 7.85/1.50      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) = iProver_top
% 7.85/1.50      | v1_funct_1(X0) != iProver_top
% 7.85/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.85/1.50      inference(predicate_to_equality,[status(thm)],[c_47]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_8377,plain,
% 7.85/1.50      ( v1_funct_2(k4_relat_1(sK3),k1_relat_1(k4_relat_1(sK3)),k1_relat_1(sK3)) = iProver_top
% 7.85/1.50      | v1_funct_1(k4_relat_1(sK3)) != iProver_top
% 7.85/1.50      | v1_relat_1(k4_relat_1(sK3)) != iProver_top ),
% 7.85/1.50      inference(superposition,[status(thm)],[c_6267,c_4151]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_8381,plain,
% 7.85/1.50      ( v1_funct_2(k4_relat_1(sK3),sK2,k1_relat_1(sK3)) = iProver_top
% 7.85/1.50      | v1_funct_1(k4_relat_1(sK3)) != iProver_top
% 7.85/1.50      | v1_relat_1(k4_relat_1(sK3)) != iProver_top ),
% 7.85/1.50      inference(light_normalisation,[status(thm)],[c_8377,c_7891]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_19323,plain,
% 7.85/1.50      ( r1_tarski(k1_relat_1(sK3),X0) != iProver_top
% 7.85/1.50      | k1_relat_1(sK3) = k1_xboole_0
% 7.85/1.50      | v1_funct_2(k4_relat_1(sK3),sK2,X0) = iProver_top ),
% 7.85/1.50      inference(global_propositional_subsumption,
% 7.85/1.50                [status(thm)],
% 7.85/1.50                [c_10749,c_61,c_63,c_4309,c_8381,c_9054,c_9790]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_19324,plain,
% 7.85/1.50      ( k1_relat_1(sK3) = k1_xboole_0
% 7.85/1.50      | v1_funct_2(k4_relat_1(sK3),sK2,X0) = iProver_top
% 7.85/1.50      | r1_tarski(k1_relat_1(sK3),X0) != iProver_top ),
% 7.85/1.50      inference(renaming,[status(thm)],[c_19323]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_50,plain,
% 7.85/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.85/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.85/1.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 7.85/1.50      | ~ r1_tarski(X2,X3)
% 7.85/1.50      | ~ v1_funct_1(X0)
% 7.85/1.50      | k1_xboole_0 = X2 ),
% 7.85/1.50      inference(cnf_transformation,[],[f144]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_4149,plain,
% 7.85/1.50      ( k1_xboole_0 = X0
% 7.85/1.50      | v1_funct_2(X1,X2,X0) != iProver_top
% 7.85/1.50      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 7.85/1.50      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) = iProver_top
% 7.85/1.50      | r1_tarski(X0,X3) != iProver_top
% 7.85/1.50      | v1_funct_1(X1) != iProver_top ),
% 7.85/1.50      inference(predicate_to_equality,[status(thm)],[c_50]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_10748,plain,
% 7.85/1.50      ( k1_relat_1(sK3) = k1_xboole_0
% 7.85/1.50      | v1_funct_2(k4_relat_1(sK3),sK2,k1_relat_1(sK3)) != iProver_top
% 7.85/1.50      | m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
% 7.85/1.50      | r1_tarski(k1_relat_1(sK3),X0) != iProver_top
% 7.85/1.50      | v1_funct_1(k4_relat_1(sK3)) != iProver_top ),
% 7.85/1.50      inference(superposition,[status(thm)],[c_10740,c_4149]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_19330,plain,
% 7.85/1.50      ( r1_tarski(k1_relat_1(sK3),X0) != iProver_top
% 7.85/1.50      | m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
% 7.85/1.50      | k1_relat_1(sK3) = k1_xboole_0 ),
% 7.85/1.50      inference(global_propositional_subsumption,
% 7.85/1.50                [status(thm)],
% 7.85/1.50                [c_10748,c_61,c_63,c_4309,c_8381,c_9054,c_9790]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_19331,plain,
% 7.85/1.50      ( k1_relat_1(sK3) = k1_xboole_0
% 7.85/1.50      | m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
% 7.85/1.50      | r1_tarski(k1_relat_1(sK3),X0) != iProver_top ),
% 7.85/1.50      inference(renaming,[status(thm)],[c_19330]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_55,negated_conjecture,
% 7.85/1.50      ( ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
% 7.85/1.50      | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 7.85/1.50      | ~ v1_funct_1(k2_funct_1(sK3)) ),
% 7.85/1.50      inference(cnf_transformation,[],[f151]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_4146,plain,
% 7.85/1.50      ( v1_funct_2(k2_funct_1(sK3),sK2,sK1) != iProver_top
% 7.85/1.50      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.85/1.50      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 7.85/1.50      inference(predicate_to_equality,[status(thm)],[c_55]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_65,plain,
% 7.85/1.50      ( v1_funct_2(k2_funct_1(sK3),sK2,sK1) != iProver_top
% 7.85/1.50      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.85/1.50      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 7.85/1.50      inference(predicate_to_equality,[status(thm)],[c_55]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_4244,plain,
% 7.85/1.50      ( v1_funct_1(k2_funct_1(sK3))
% 7.85/1.50      | ~ v1_funct_1(sK3)
% 7.85/1.50      | ~ v1_relat_1(sK3) ),
% 7.85/1.50      inference(instantiation,[status(thm)],[c_29]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_4245,plain,
% 7.85/1.50      ( v1_funct_1(k2_funct_1(sK3)) = iProver_top
% 7.85/1.50      | v1_funct_1(sK3) != iProver_top
% 7.85/1.50      | v1_relat_1(sK3) != iProver_top ),
% 7.85/1.50      inference(predicate_to_equality,[status(thm)],[c_4244]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_4492,plain,
% 7.85/1.50      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.85/1.50      | v1_funct_2(k2_funct_1(sK3),sK2,sK1) != iProver_top ),
% 7.85/1.50      inference(global_propositional_subsumption,
% 7.85/1.50                [status(thm)],
% 7.85/1.50                [c_4146,c_61,c_63,c_65,c_4245,c_4309]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_4493,plain,
% 7.85/1.50      ( v1_funct_2(k2_funct_1(sK3),sK2,sK1) != iProver_top
% 7.85/1.50      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 7.85/1.50      inference(renaming,[status(thm)],[c_4492]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_9787,plain,
% 7.85/1.50      ( v1_funct_2(k4_relat_1(sK3),sK2,sK1) != iProver_top
% 7.85/1.50      | m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 7.85/1.50      inference(demodulation,[status(thm)],[c_9784,c_4493]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_19342,plain,
% 7.85/1.50      ( k1_relat_1(sK3) = k1_xboole_0
% 7.85/1.50      | v1_funct_2(k4_relat_1(sK3),sK2,sK1) != iProver_top
% 7.85/1.50      | r1_tarski(k1_relat_1(sK3),sK1) != iProver_top ),
% 7.85/1.50      inference(superposition,[status(thm)],[c_19331,c_9787]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_40,plain,
% 7.85/1.50      ( v4_relat_1(X0,X1)
% 7.85/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 7.85/1.50      inference(cnf_transformation,[],[f130]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_11,plain,
% 7.85/1.50      ( ~ v4_relat_1(X0,X1)
% 7.85/1.50      | r1_tarski(k1_relat_1(X0),X1)
% 7.85/1.50      | ~ v1_relat_1(X0) ),
% 7.85/1.50      inference(cnf_transformation,[],[f100]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_733,plain,
% 7.85/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.85/1.50      | r1_tarski(k1_relat_1(X0),X1)
% 7.85/1.50      | ~ v1_relat_1(X0) ),
% 7.85/1.50      inference(resolution,[status(thm)],[c_40,c_11]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_737,plain,
% 7.85/1.50      ( r1_tarski(k1_relat_1(X0),X1)
% 7.85/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 7.85/1.50      inference(global_propositional_subsumption,
% 7.85/1.50                [status(thm)],
% 7.85/1.50                [c_733,c_39]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_738,plain,
% 7.85/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.85/1.50      | r1_tarski(k1_relat_1(X0),X1) ),
% 7.85/1.50      inference(renaming,[status(thm)],[c_737]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_4138,plain,
% 7.85/1.50      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.85/1.50      | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
% 7.85/1.50      inference(predicate_to_equality,[status(thm)],[c_738]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_4650,plain,
% 7.85/1.50      ( r1_tarski(k1_relat_1(sK3),sK1) = iProver_top ),
% 7.85/1.50      inference(superposition,[status(thm)],[c_4144,c_4138]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_19475,plain,
% 7.85/1.50      ( v1_funct_2(k4_relat_1(sK3),sK2,sK1) != iProver_top
% 7.85/1.50      | k1_relat_1(sK3) = k1_xboole_0 ),
% 7.85/1.50      inference(global_propositional_subsumption,
% 7.85/1.50                [status(thm)],
% 7.85/1.50                [c_19342,c_4650]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_19476,plain,
% 7.85/1.50      ( k1_relat_1(sK3) = k1_xboole_0
% 7.85/1.50      | v1_funct_2(k4_relat_1(sK3),sK2,sK1) != iProver_top ),
% 7.85/1.50      inference(renaming,[status(thm)],[c_19475]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_19479,plain,
% 7.85/1.50      ( k1_relat_1(sK3) = k1_xboole_0
% 7.85/1.50      | r1_tarski(k1_relat_1(sK3),sK1) != iProver_top ),
% 7.85/1.50      inference(superposition,[status(thm)],[c_19324,c_19476]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_19482,plain,
% 7.85/1.50      ( k1_relat_1(sK3) = k1_xboole_0 ),
% 7.85/1.50      inference(global_propositional_subsumption,
% 7.85/1.50                [status(thm)],
% 7.85/1.50                [c_19479,c_4650]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_21,plain,
% 7.85/1.50      ( ~ v1_relat_1(X0)
% 7.85/1.50      | k2_relat_1(X0) != k1_xboole_0
% 7.85/1.50      | k1_relat_1(X0) = k1_xboole_0 ),
% 7.85/1.50      inference(cnf_transformation,[],[f112]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_4169,plain,
% 7.85/1.50      ( k2_relat_1(X0) != k1_xboole_0
% 7.85/1.50      | k1_relat_1(X0) = k1_xboole_0
% 7.85/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.85/1.50      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_6940,plain,
% 7.85/1.50      ( k1_relat_1(k4_relat_1(sK3)) = k1_xboole_0
% 7.85/1.50      | k1_relat_1(sK3) != k1_xboole_0
% 7.85/1.50      | v1_relat_1(k4_relat_1(sK3)) != iProver_top ),
% 7.85/1.50      inference(superposition,[status(thm)],[c_6267,c_4169]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_6944,plain,
% 7.85/1.50      ( k2_relat_1(sK3) = k1_xboole_0
% 7.85/1.50      | k1_relat_1(sK3) != k1_xboole_0
% 7.85/1.50      | v1_relat_1(k4_relat_1(sK3)) != iProver_top ),
% 7.85/1.50      inference(demodulation,[status(thm)],[c_6940,c_6268]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_11971,plain,
% 7.85/1.50      ( k1_relat_1(sK3) != k1_xboole_0 | k2_relat_1(sK3) = k1_xboole_0 ),
% 7.85/1.50      inference(global_propositional_subsumption,
% 7.85/1.50                [status(thm)],
% 7.85/1.50                [c_6944,c_63,c_4309,c_9054]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_11972,plain,
% 7.85/1.50      ( k2_relat_1(sK3) = k1_xboole_0 | k1_relat_1(sK3) != k1_xboole_0 ),
% 7.85/1.50      inference(renaming,[status(thm)],[c_11971]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_11973,plain,
% 7.85/1.50      ( k1_relat_1(sK3) != k1_xboole_0 | sK2 = k1_xboole_0 ),
% 7.85/1.50      inference(demodulation,[status(thm)],[c_11972,c_7873]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_19507,plain,
% 7.85/1.50      ( sK2 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 7.85/1.50      inference(demodulation,[status(thm)],[c_19482,c_11973]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_19538,plain,
% 7.85/1.50      ( sK2 = k1_xboole_0 ),
% 7.85/1.50      inference(equality_resolution_simp,[status(thm)],[c_19507]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_19804,plain,
% 7.85/1.50      ( v1_funct_2(k4_relat_1(sK3),k1_xboole_0,sK1) != iProver_top
% 7.85/1.50      | m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top ),
% 7.85/1.50      inference(demodulation,[status(thm)],[c_19538,c_9787]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_19,plain,
% 7.85/1.50      ( ~ v1_relat_1(X0)
% 7.85/1.50      | k2_relat_1(X0) != k1_xboole_0
% 7.85/1.50      | k1_xboole_0 = X0 ),
% 7.85/1.50      inference(cnf_transformation,[],[f110]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_4171,plain,
% 7.85/1.50      ( k2_relat_1(X0) != k1_xboole_0
% 7.85/1.50      | k1_xboole_0 = X0
% 7.85/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.85/1.50      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_7893,plain,
% 7.85/1.50      ( sK2 != k1_xboole_0
% 7.85/1.50      | sK3 = k1_xboole_0
% 7.85/1.50      | v1_relat_1(sK3) != iProver_top ),
% 7.85/1.50      inference(superposition,[status(thm)],[c_7873,c_4171]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_8237,plain,
% 7.85/1.50      ( sK3 = k1_xboole_0 | sK2 != k1_xboole_0 ),
% 7.85/1.50      inference(global_propositional_subsumption,
% 7.85/1.50                [status(thm)],
% 7.85/1.50                [c_7893,c_63,c_4309]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_8238,plain,
% 7.85/1.50      ( sK2 != k1_xboole_0 | sK3 = k1_xboole_0 ),
% 7.85/1.50      inference(renaming,[status(thm)],[c_8237]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_19809,plain,
% 7.85/1.50      ( sK3 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 7.85/1.50      inference(demodulation,[status(thm)],[c_19538,c_8238]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_19818,plain,
% 7.85/1.50      ( sK3 = k1_xboole_0 ),
% 7.85/1.50      inference(equality_resolution_simp,[status(thm)],[c_19809]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_19828,plain,
% 7.85/1.50      ( v1_funct_2(k4_relat_1(k1_xboole_0),k1_xboole_0,sK1) != iProver_top
% 7.85/1.50      | m1_subset_1(k4_relat_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top ),
% 7.85/1.50      inference(demodulation,[status(thm)],[c_19804,c_19818]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_32,plain,
% 7.85/1.50      ( v1_relat_1(k6_partfun1(X0)) ),
% 7.85/1.50      inference(cnf_transformation,[],[f157]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_4161,plain,
% 7.85/1.50      ( v1_relat_1(k6_partfun1(X0)) = iProver_top ),
% 7.85/1.50      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_4903,plain,
% 7.85/1.50      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 7.85/1.50      inference(superposition,[status(thm)],[c_26,c_4161]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_5368,plain,
% 7.85/1.50      ( k1_relat_1(k4_relat_1(k1_xboole_0)) = k2_relat_1(k1_xboole_0) ),
% 7.85/1.50      inference(superposition,[status(thm)],[c_4903,c_4172]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_23,plain,
% 7.85/1.50      ( k2_relat_1(k6_partfun1(X0)) = X0 ),
% 7.85/1.50      inference(cnf_transformation,[],[f152]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_4652,plain,
% 7.85/1.50      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 7.85/1.50      inference(superposition,[status(thm)],[c_26,c_23]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_5369,plain,
% 7.85/1.50      ( k1_relat_1(k4_relat_1(k1_xboole_0)) = k1_xboole_0 ),
% 7.85/1.50      inference(light_normalisation,[status(thm)],[c_5368,c_4652]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_20,plain,
% 7.85/1.50      ( ~ v1_relat_1(X0)
% 7.85/1.50      | k1_relat_1(X0) != k1_xboole_0
% 7.85/1.50      | k1_xboole_0 = X0 ),
% 7.85/1.50      inference(cnf_transformation,[],[f109]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_4170,plain,
% 7.85/1.50      ( k1_relat_1(X0) != k1_xboole_0
% 7.85/1.50      | k1_xboole_0 = X0
% 7.85/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.85/1.50      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_6332,plain,
% 7.85/1.50      ( k4_relat_1(k1_xboole_0) = k1_xboole_0
% 7.85/1.50      | v1_relat_1(k4_relat_1(k1_xboole_0)) != iProver_top ),
% 7.85/1.50      inference(superposition,[status(thm)],[c_5369,c_4170]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_116,plain,
% 7.85/1.50      ( v1_relat_1(k6_partfun1(X0)) = iProver_top ),
% 7.85/1.50      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_118,plain,
% 7.85/1.50      ( v1_relat_1(k6_partfun1(k1_xboole_0)) = iProver_top ),
% 7.85/1.50      inference(instantiation,[status(thm)],[c_116]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_169,plain,
% 7.85/1.50      ( v1_relat_1(X0) != iProver_top
% 7.85/1.50      | v1_relat_1(k4_relat_1(X0)) = iProver_top ),
% 7.85/1.50      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_171,plain,
% 7.85/1.50      ( v1_relat_1(k4_relat_1(k1_xboole_0)) = iProver_top
% 7.85/1.50      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 7.85/1.50      inference(instantiation,[status(thm)],[c_169]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_3097,plain,
% 7.85/1.50      ( ~ v1_relat_1(X0) | v1_relat_1(X1) | X1 != X0 ),
% 7.85/1.50      theory(equality) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_4671,plain,
% 7.85/1.50      ( v1_relat_1(X0)
% 7.85/1.50      | ~ v1_relat_1(k6_partfun1(X1))
% 7.85/1.50      | X0 != k6_partfun1(X1) ),
% 7.85/1.50      inference(instantiation,[status(thm)],[c_3097]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_4672,plain,
% 7.85/1.50      ( X0 != k6_partfun1(X1)
% 7.85/1.50      | v1_relat_1(X0) = iProver_top
% 7.85/1.50      | v1_relat_1(k6_partfun1(X1)) != iProver_top ),
% 7.85/1.50      inference(predicate_to_equality,[status(thm)],[c_4671]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_4674,plain,
% 7.85/1.50      ( k1_xboole_0 != k6_partfun1(k1_xboole_0)
% 7.85/1.50      | v1_relat_1(k6_partfun1(k1_xboole_0)) != iProver_top
% 7.85/1.50      | v1_relat_1(k1_xboole_0) = iProver_top ),
% 7.85/1.50      inference(instantiation,[status(thm)],[c_4672]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_12098,plain,
% 7.85/1.50      ( k4_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 7.85/1.50      inference(global_propositional_subsumption,
% 7.85/1.50                [status(thm)],
% 7.85/1.50                [c_6332,c_118,c_26,c_171,c_192,c_3,c_4674,c_4783]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_19829,plain,
% 7.85/1.50      ( v1_funct_2(k1_xboole_0,k1_xboole_0,sK1) != iProver_top
% 7.85/1.50      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top ),
% 7.85/1.50      inference(light_normalisation,[status(thm)],[c_19828,c_12098]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_22373,plain,
% 7.85/1.50      ( v1_funct_2(k1_xboole_0,k1_xboole_0,sK1) != iProver_top
% 7.85/1.50      | r1_tarski(k1_xboole_0,sK1) != iProver_top ),
% 7.85/1.50      inference(superposition,[status(thm)],[c_21070,c_19829]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_19535,plain,
% 7.85/1.50      ( r1_tarski(k1_xboole_0,sK1) = iProver_top ),
% 7.85/1.50      inference(demodulation,[status(thm)],[c_19482,c_4650]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_29211,plain,
% 7.85/1.50      ( v1_funct_2(k1_xboole_0,k1_xboole_0,sK1) != iProver_top ),
% 7.85/1.50      inference(global_propositional_subsumption,
% 7.85/1.50                [status(thm)],
% 7.85/1.50                [c_22373,c_19535]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_29215,plain,
% 7.85/1.50      ( r1_tarski(k1_xboole_0,sK1) != iProver_top ),
% 7.85/1.50      inference(superposition,[status(thm)],[c_17027,c_29211]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(contradiction,plain,
% 7.85/1.50      ( $false ),
% 7.85/1.50      inference(minisat,[status(thm)],[c_29215,c_19535]) ).
% 7.85/1.50  
% 7.85/1.50  
% 7.85/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.85/1.50  
% 7.85/1.50  ------                               Statistics
% 7.85/1.50  
% 7.85/1.50  ------ General
% 7.85/1.50  
% 7.85/1.50  abstr_ref_over_cycles:                  0
% 7.85/1.50  abstr_ref_under_cycles:                 0
% 7.85/1.50  gc_basic_clause_elim:                   0
% 7.85/1.50  forced_gc_time:                         0
% 7.85/1.50  parsing_time:                           0.011
% 7.85/1.50  unif_index_cands_time:                  0.
% 7.85/1.50  unif_index_add_time:                    0.
% 7.85/1.50  orderings_time:                         0.
% 7.85/1.50  out_proof_time:                         0.022
% 7.85/1.50  total_time:                             0.808
% 7.85/1.50  num_of_symbols:                         59
% 7.85/1.50  num_of_terms:                           28594
% 7.85/1.50  
% 7.85/1.50  ------ Preprocessing
% 7.85/1.50  
% 7.85/1.50  num_of_splits:                          0
% 7.85/1.50  num_of_split_atoms:                     0
% 7.85/1.50  num_of_reused_defs:                     0
% 7.85/1.50  num_eq_ax_congr_red:                    27
% 7.85/1.50  num_of_sem_filtered_clauses:            1
% 7.85/1.50  num_of_subtypes:                        0
% 7.85/1.50  monotx_restored_types:                  0
% 7.85/1.50  sat_num_of_epr_types:                   0
% 7.85/1.50  sat_num_of_non_cyclic_types:            0
% 7.85/1.50  sat_guarded_non_collapsed_types:        0
% 7.85/1.50  num_pure_diseq_elim:                    0
% 7.85/1.50  simp_replaced_by:                       0
% 7.85/1.50  res_preprocessed:                       262
% 7.85/1.50  prep_upred:                             0
% 7.85/1.50  prep_unflattend:                        144
% 7.85/1.50  smt_new_axioms:                         0
% 7.85/1.50  pred_elim_cands:                        8
% 7.85/1.50  pred_elim:                              2
% 7.85/1.50  pred_elim_cl:                           3
% 7.85/1.50  pred_elim_cycles:                       6
% 7.85/1.50  merged_defs:                            8
% 7.85/1.50  merged_defs_ncl:                        0
% 7.85/1.50  bin_hyper_res:                          9
% 7.85/1.50  prep_cycles:                            4
% 7.85/1.50  pred_elim_time:                         0.035
% 7.85/1.50  splitting_time:                         0.
% 7.85/1.50  sem_filter_time:                        0.
% 7.85/1.50  monotx_time:                            0.001
% 7.85/1.50  subtype_inf_time:                       0.
% 7.85/1.50  
% 7.85/1.50  ------ Problem properties
% 7.85/1.50  
% 7.85/1.50  clauses:                                54
% 7.85/1.50  conjectures:                            6
% 7.85/1.50  epr:                                    7
% 7.85/1.50  horn:                                   51
% 7.85/1.50  ground:                                 8
% 7.85/1.50  unary:                                  14
% 7.85/1.50  binary:                                 17
% 7.85/1.50  lits:                                   140
% 7.85/1.50  lits_eq:                                33
% 7.85/1.50  fd_pure:                                0
% 7.85/1.50  fd_pseudo:                              0
% 7.85/1.50  fd_cond:                                5
% 7.85/1.50  fd_pseudo_cond:                         1
% 7.85/1.50  ac_symbols:                             0
% 7.85/1.50  
% 7.85/1.50  ------ Propositional Solver
% 7.85/1.50  
% 7.85/1.50  prop_solver_calls:                      34
% 7.85/1.50  prop_fast_solver_calls:                 3367
% 7.85/1.50  smt_solver_calls:                       0
% 7.85/1.50  smt_fast_solver_calls:                  0
% 7.85/1.50  prop_num_of_clauses:                    13412
% 7.85/1.50  prop_preprocess_simplified:             30949
% 7.85/1.50  prop_fo_subsumed:                       291
% 7.85/1.50  prop_solver_time:                       0.
% 7.85/1.50  smt_solver_time:                        0.
% 7.85/1.50  smt_fast_solver_time:                   0.
% 7.85/1.50  prop_fast_solver_time:                  0.
% 7.85/1.50  prop_unsat_core_time:                   0.001
% 7.85/1.50  
% 7.85/1.50  ------ QBF
% 7.85/1.50  
% 7.85/1.50  qbf_q_res:                              0
% 7.85/1.50  qbf_num_tautologies:                    0
% 7.85/1.50  qbf_prep_cycles:                        0
% 7.85/1.50  
% 7.85/1.50  ------ BMC1
% 7.85/1.50  
% 7.85/1.50  bmc1_current_bound:                     -1
% 7.85/1.50  bmc1_last_solved_bound:                 -1
% 7.85/1.50  bmc1_unsat_core_size:                   -1
% 7.85/1.50  bmc1_unsat_core_parents_size:           -1
% 7.85/1.50  bmc1_merge_next_fun:                    0
% 7.85/1.50  bmc1_unsat_core_clauses_time:           0.
% 7.85/1.50  
% 7.85/1.50  ------ Instantiation
% 7.85/1.50  
% 7.85/1.50  inst_num_of_clauses:                    4623
% 7.85/1.50  inst_num_in_passive:                    3025
% 7.85/1.50  inst_num_in_active:                     1412
% 7.85/1.50  inst_num_in_unprocessed:                188
% 7.85/1.50  inst_num_of_loops:                      1960
% 7.85/1.50  inst_num_of_learning_restarts:          0
% 7.85/1.50  inst_num_moves_active_passive:          545
% 7.85/1.50  inst_lit_activity:                      0
% 7.85/1.50  inst_lit_activity_moves:                1
% 7.85/1.50  inst_num_tautologies:                   0
% 7.85/1.50  inst_num_prop_implied:                  0
% 7.85/1.50  inst_num_existing_simplified:           0
% 7.85/1.50  inst_num_eq_res_simplified:             0
% 7.85/1.50  inst_num_child_elim:                    0
% 7.85/1.50  inst_num_of_dismatching_blockings:      1033
% 7.85/1.50  inst_num_of_non_proper_insts:           3759
% 7.85/1.50  inst_num_of_duplicates:                 0
% 7.85/1.50  inst_inst_num_from_inst_to_res:         0
% 7.85/1.50  inst_dismatching_checking_time:         0.
% 7.85/1.50  
% 7.85/1.50  ------ Resolution
% 7.85/1.50  
% 7.85/1.50  res_num_of_clauses:                     0
% 7.85/1.50  res_num_in_passive:                     0
% 7.85/1.50  res_num_in_active:                      0
% 7.85/1.50  res_num_of_loops:                       266
% 7.85/1.50  res_forward_subset_subsumed:            387
% 7.85/1.50  res_backward_subset_subsumed:           10
% 7.85/1.50  res_forward_subsumed:                   0
% 7.85/1.50  res_backward_subsumed:                  0
% 7.85/1.50  res_forward_subsumption_resolution:     0
% 7.85/1.50  res_backward_subsumption_resolution:    0
% 7.85/1.50  res_clause_to_clause_subsumption:       2637
% 7.85/1.50  res_orphan_elimination:                 0
% 7.85/1.50  res_tautology_del:                      229
% 7.85/1.50  res_num_eq_res_simplified:              0
% 7.85/1.50  res_num_sel_changes:                    0
% 7.85/1.50  res_moves_from_active_to_pass:          0
% 7.85/1.50  
% 7.85/1.50  ------ Superposition
% 7.85/1.50  
% 7.85/1.50  sup_time_total:                         0.
% 7.85/1.50  sup_time_generating:                    0.
% 7.85/1.50  sup_time_sim_full:                      0.
% 7.85/1.50  sup_time_sim_immed:                     0.
% 7.85/1.50  
% 7.85/1.50  sup_num_of_clauses:                     533
% 7.85/1.50  sup_num_in_active:                      217
% 7.85/1.50  sup_num_in_passive:                     316
% 7.85/1.50  sup_num_of_loops:                       391
% 7.85/1.50  sup_fw_superposition:                   599
% 7.85/1.50  sup_bw_superposition:                   467
% 7.85/1.50  sup_immediate_simplified:               474
% 7.85/1.50  sup_given_eliminated:                   0
% 7.85/1.50  comparisons_done:                       0
% 7.85/1.50  comparisons_avoided:                    33
% 7.85/1.50  
% 7.85/1.50  ------ Simplifications
% 7.85/1.50  
% 7.85/1.50  
% 7.85/1.50  sim_fw_subset_subsumed:                 64
% 7.85/1.50  sim_bw_subset_subsumed:                 50
% 7.85/1.50  sim_fw_subsumed:                        49
% 7.85/1.50  sim_bw_subsumed:                        7
% 7.85/1.50  sim_fw_subsumption_res:                 0
% 7.85/1.50  sim_bw_subsumption_res:                 0
% 7.85/1.50  sim_tautology_del:                      31
% 7.85/1.50  sim_eq_tautology_del:                   165
% 7.85/1.50  sim_eq_res_simp:                        17
% 7.85/1.50  sim_fw_demodulated:                     75
% 7.85/1.50  sim_bw_demodulated:                     180
% 7.85/1.50  sim_light_normalised:                   368
% 7.85/1.50  sim_joinable_taut:                      0
% 7.85/1.50  sim_joinable_simp:                      0
% 7.85/1.50  sim_ac_normalised:                      0
% 7.85/1.50  sim_smt_subsumption:                    0
% 7.85/1.50  
%------------------------------------------------------------------------------
