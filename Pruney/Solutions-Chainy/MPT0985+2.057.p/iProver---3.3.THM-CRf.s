%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:02:31 EST 2020

% Result     : Theorem 3.32s
% Output     : CNFRefutation 3.32s
% Verified   : 
% Statistics : Number of formulae       :  174 (8145 expanded)
%              Number of clauses        :  114 (2735 expanded)
%              Number of leaves         :   13 (1531 expanded)
%              Depth                    :   27
%              Number of atoms          :  511 (42506 expanded)
%              Number of equality atoms :  268 (8920 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,axiom,(
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

fof(f33,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f48,plain,(
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
    inference(nnf_transformation,[],[f34])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f19,conjecture,(
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

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f39,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f40,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f39])).

fof(f49,plain,
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

fof(f50,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
      | ~ v1_funct_1(k2_funct_1(sK3)) )
    & k2_relset_1(sK1,sK2,sK3) = sK2
    & v2_funct_1(sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK3,sK1,sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f40,f49])).

fof(f89,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f50])).

fof(f90,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f50])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f27,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f68,plain,(
    ! [X0] :
      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f91,plain,(
    v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f50])).

fof(f88,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f50])).

fof(f17,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f36,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f35])).

fof(f84,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f92,plain,(
    k2_relset_1(sK1,sK2,sK3) = sK2 ),
    inference(cnf_transformation,[],[f50])).

fof(f67,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f25,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f63,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f62,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f83,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f93,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
    | ~ v1_funct_1(k2_funct_1(sK3)) ),
    inference(cnf_transformation,[],[f50])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f41])).

fof(f53,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f43])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f96,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f57])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f97,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f56])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f101,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f77])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_28,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_41,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_626,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK1 != X1
    | sK2 != X2
    | sK3 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_41])).

cnf(c_627,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k1_relset_1(sK1,sK2,sK3) = sK1
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_626])).

cnf(c_40,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_629,plain,
    ( k1_relset_1(sK1,sK2,sK3) = sK1
    | k1_xboole_0 = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_627,c_40])).

cnf(c_1918,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1923,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_4169,plain,
    ( k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1918,c_1923])).

cnf(c_4318,plain,
    ( k1_relat_1(sK3) = sK1
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_629,c_4169])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1924,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3351,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1918,c_1924])).

cnf(c_16,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_39,negated_conjecture,
    ( v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_527,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_39])).

cnf(c_528,plain,
    ( ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_527])).

cnf(c_42,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_530,plain,
    ( ~ v1_relat_1(sK3)
    | k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_528,c_42])).

cnf(c_1914,plain,
    ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_530])).

cnf(c_3583,plain,
    ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_3351,c_1914])).

cnf(c_31,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1920,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_5480,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK3)),k1_relat_1(sK3)))) = iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3583,c_1920])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1922,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_3487,plain,
    ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1918,c_1922])).

cnf(c_38,negated_conjecture,
    ( k2_relset_1(sK1,sK2,sK3) = sK2 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_3499,plain,
    ( k2_relat_1(sK3) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_3487,c_38])).

cnf(c_17,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_513,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_39])).

cnf(c_514,plain,
    ( ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_513])).

cnf(c_516,plain,
    ( ~ v1_relat_1(sK3)
    | k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_514,c_42])).

cnf(c_1915,plain,
    ( k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_516])).

cnf(c_3577,plain,
    ( k1_relat_1(k2_funct_1(sK3)) = sK2
    | v1_relat_1(sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3499,c_1915])).

cnf(c_45,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_2324,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_2325,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2324])).

cnf(c_3659,plain,
    ( k1_relat_1(k2_funct_1(sK3)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3577,c_45,c_2325])).

cnf(c_5506,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3)))) = iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5480,c_3659])).

cnf(c_43,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_11,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_2526,plain,
    ( ~ v1_relat_1(sK3)
    | v1_funct_1(k2_funct_1(sK3))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_2527,plain,
    ( v1_relat_1(sK3) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2526])).

cnf(c_12,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_2533,plain,
    ( v1_relat_1(k2_funct_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_2534,plain,
    ( v1_relat_1(k2_funct_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2533])).

cnf(c_5840,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5506,c_43,c_45,c_2325,c_2527,c_2534])).

cnf(c_5847,plain,
    ( k1_relset_1(sK2,k1_relat_1(sK3),k2_funct_1(sK3)) = k1_relat_1(k2_funct_1(sK3)) ),
    inference(superposition,[status(thm)],[c_5840,c_1923])).

cnf(c_5856,plain,
    ( k1_relset_1(sK2,k1_relat_1(sK3),k2_funct_1(sK3)) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_5847,c_3659])).

cnf(c_5998,plain,
    ( k1_relset_1(sK2,sK1,k2_funct_1(sK3)) = sK2
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4318,c_5856])).

cnf(c_32,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_37,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
    | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK3)) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_865,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_funct_1(sK3))
    | k1_relat_1(X0) != sK2
    | k2_relat_1(X0) != sK1
    | k2_funct_1(sK3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_32,c_37])).

cnf(c_866,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | k1_relat_1(k2_funct_1(sK3)) != sK2
    | k2_relat_1(k2_funct_1(sK3)) != sK1 ),
    inference(unflattening,[status(thm)],[c_865])).

cnf(c_878,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | k1_relat_1(k2_funct_1(sK3)) != sK2
    | k2_relat_1(k2_funct_1(sK3)) != sK1 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_866,c_18])).

cnf(c_1899,plain,
    ( k1_relat_1(k2_funct_1(sK3)) != sK2
    | k2_relat_1(k2_funct_1(sK3)) != sK1
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_878])).

cnf(c_3663,plain,
    ( k2_relat_1(k2_funct_1(sK3)) != sK1
    | sK2 != sK2
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3659,c_1899])).

cnf(c_3664,plain,
    ( k2_relat_1(k2_funct_1(sK3)) != sK1
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_3663])).

cnf(c_867,plain,
    ( k1_relat_1(k2_funct_1(sK3)) != sK2
    | k2_relat_1(k2_funct_1(sK3)) != sK1
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_866])).

cnf(c_3896,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | k2_relat_1(k2_funct_1(sK3)) != sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3664,c_43,c_45,c_867,c_2325,c_2527,c_2534,c_3577])).

cnf(c_3897,plain,
    ( k2_relat_1(k2_funct_1(sK3)) != sK1
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(renaming,[status(thm)],[c_3896])).

cnf(c_3900,plain,
    ( k1_relat_1(sK3) != sK1
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3897,c_3583])).

cnf(c_4322,plain,
    ( sK2 = k1_xboole_0
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4318,c_3900])).

cnf(c_5845,plain,
    ( sK2 = k1_xboole_0
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4318,c_5840])).

cnf(c_5999,plain,
    ( sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5998,c_4322,c_5845])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1929,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3193,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK1,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1918,c_1929])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1934,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_4908,plain,
    ( k2_zfmisc_1(sK1,sK2) = sK3
    | r1_tarski(k2_zfmisc_1(sK1,sK2),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3193,c_1934])).

cnf(c_6012,plain,
    ( k2_zfmisc_1(sK1,k1_xboole_0) = sK3
    | r1_tarski(k2_zfmisc_1(sK1,k1_xboole_0),sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5999,c_4908])).

cnf(c_4,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f96])).

cnf(c_6126,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(k1_xboole_0,sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6012,c_4])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_2690,plain,
    ( r1_tarski(k1_xboole_0,sK3) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2693,plain,
    ( r1_tarski(k1_xboole_0,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2690])).

cnf(c_2698,plain,
    ( ~ r1_tarski(X0,sK3)
    | ~ r1_tarski(sK3,X0)
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2699,plain,
    ( sK3 = X0
    | r1_tarski(X0,sK3) != iProver_top
    | r1_tarski(sK3,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2698])).

cnf(c_2701,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(sK3,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2699])).

cnf(c_3318,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
    | r1_tarski(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_3319,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
    | r1_tarski(sK3,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3318])).

cnf(c_3321,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(sK3,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3319])).

cnf(c_6032,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5999,c_1918])).

cnf(c_6037,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6032,c_4])).

cnf(c_6524,plain,
    ( sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6126,c_2693,c_2701,c_3321,c_6037])).

cnf(c_6003,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK3)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5999,c_5840])).

cnf(c_5,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f97])).

cnf(c_6144,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6003,c_5])).

cnf(c_6527,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6524,c_6144])).

cnf(c_4171,plain,
    ( k1_relset_1(k1_xboole_0,X0,X1) = k1_relat_1(X1)
    | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5,c_1923])).

cnf(c_9245,plain,
    ( k1_relset_1(k1_xboole_0,X0,k2_funct_1(k1_xboole_0)) = k1_relat_1(k2_funct_1(k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_6527,c_4171])).

cnf(c_6021,plain,
    ( k1_relat_1(k2_funct_1(sK3)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5999,c_3659])).

cnf(c_6938,plain,
    ( k1_relat_1(k2_funct_1(k1_xboole_0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_6021,c_6524])).

cnf(c_9257,plain,
    ( k1_relset_1(k1_xboole_0,X0,k2_funct_1(k1_xboole_0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_9245,c_6938])).

cnf(c_25,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f101])).

cnf(c_818,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
    | k2_funct_1(sK3) != X0
    | sK1 != X1
    | sK2 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_37])).

cnf(c_819,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
    | sK2 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_818])).

cnf(c_1902,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_819])).

cnf(c_2190,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1902,c_5])).

cnf(c_2721,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | sK2 != k1_xboole_0
    | k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2190,c_43,c_45,c_2325,c_2527])).

cnf(c_2722,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2721])).

cnf(c_6025,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5999,c_2722])).

cnf(c_6074,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_6025])).

cnf(c_6078,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6074,c_5])).

cnf(c_6146,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_6144,c_6078])).

cnf(c_9260,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(k1_xboole_0)) != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_6146,c_6524])).

cnf(c_9357,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_9257,c_9260])).

cnf(c_125,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_6,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_124,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9357,c_125,c_124])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:51:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.32/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.32/1.00  
% 3.32/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.32/1.00  
% 3.32/1.00  ------  iProver source info
% 3.32/1.00  
% 3.32/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.32/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.32/1.00  git: non_committed_changes: false
% 3.32/1.00  git: last_make_outside_of_git: false
% 3.32/1.00  
% 3.32/1.00  ------ 
% 3.32/1.00  
% 3.32/1.00  ------ Input Options
% 3.32/1.00  
% 3.32/1.00  --out_options                           all
% 3.32/1.00  --tptp_safe_out                         true
% 3.32/1.00  --problem_path                          ""
% 3.32/1.00  --include_path                          ""
% 3.32/1.00  --clausifier                            res/vclausify_rel
% 3.32/1.00  --clausifier_options                    --mode clausify
% 3.32/1.00  --stdin                                 false
% 3.32/1.00  --stats_out                             all
% 3.32/1.00  
% 3.32/1.00  ------ General Options
% 3.32/1.00  
% 3.32/1.00  --fof                                   false
% 3.32/1.00  --time_out_real                         305.
% 3.32/1.00  --time_out_virtual                      -1.
% 3.32/1.00  --symbol_type_check                     false
% 3.32/1.00  --clausify_out                          false
% 3.32/1.00  --sig_cnt_out                           false
% 3.32/1.00  --trig_cnt_out                          false
% 3.32/1.00  --trig_cnt_out_tolerance                1.
% 3.32/1.00  --trig_cnt_out_sk_spl                   false
% 3.32/1.00  --abstr_cl_out                          false
% 3.32/1.00  
% 3.32/1.00  ------ Global Options
% 3.32/1.00  
% 3.32/1.00  --schedule                              default
% 3.32/1.00  --add_important_lit                     false
% 3.32/1.00  --prop_solver_per_cl                    1000
% 3.32/1.00  --min_unsat_core                        false
% 3.32/1.00  --soft_assumptions                      false
% 3.32/1.00  --soft_lemma_size                       3
% 3.32/1.00  --prop_impl_unit_size                   0
% 3.32/1.00  --prop_impl_unit                        []
% 3.32/1.00  --share_sel_clauses                     true
% 3.32/1.00  --reset_solvers                         false
% 3.32/1.00  --bc_imp_inh                            [conj_cone]
% 3.32/1.00  --conj_cone_tolerance                   3.
% 3.32/1.00  --extra_neg_conj                        none
% 3.32/1.00  --large_theory_mode                     true
% 3.32/1.00  --prolific_symb_bound                   200
% 3.32/1.00  --lt_threshold                          2000
% 3.32/1.00  --clause_weak_htbl                      true
% 3.32/1.00  --gc_record_bc_elim                     false
% 3.32/1.00  
% 3.32/1.00  ------ Preprocessing Options
% 3.32/1.00  
% 3.32/1.00  --preprocessing_flag                    true
% 3.32/1.00  --time_out_prep_mult                    0.1
% 3.32/1.00  --splitting_mode                        input
% 3.32/1.00  --splitting_grd                         true
% 3.32/1.00  --splitting_cvd                         false
% 3.32/1.00  --splitting_cvd_svl                     false
% 3.32/1.00  --splitting_nvd                         32
% 3.32/1.00  --sub_typing                            true
% 3.32/1.00  --prep_gs_sim                           true
% 3.32/1.00  --prep_unflatten                        true
% 3.32/1.00  --prep_res_sim                          true
% 3.32/1.00  --prep_upred                            true
% 3.32/1.00  --prep_sem_filter                       exhaustive
% 3.32/1.00  --prep_sem_filter_out                   false
% 3.32/1.00  --pred_elim                             true
% 3.32/1.00  --res_sim_input                         true
% 3.32/1.00  --eq_ax_congr_red                       true
% 3.32/1.00  --pure_diseq_elim                       true
% 3.32/1.00  --brand_transform                       false
% 3.32/1.00  --non_eq_to_eq                          false
% 3.32/1.00  --prep_def_merge                        true
% 3.32/1.00  --prep_def_merge_prop_impl              false
% 3.32/1.00  --prep_def_merge_mbd                    true
% 3.32/1.00  --prep_def_merge_tr_red                 false
% 3.32/1.00  --prep_def_merge_tr_cl                  false
% 3.32/1.00  --smt_preprocessing                     true
% 3.32/1.00  --smt_ac_axioms                         fast
% 3.32/1.00  --preprocessed_out                      false
% 3.32/1.00  --preprocessed_stats                    false
% 3.32/1.00  
% 3.32/1.00  ------ Abstraction refinement Options
% 3.32/1.00  
% 3.32/1.00  --abstr_ref                             []
% 3.32/1.00  --abstr_ref_prep                        false
% 3.32/1.00  --abstr_ref_until_sat                   false
% 3.32/1.00  --abstr_ref_sig_restrict                funpre
% 3.32/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.32/1.00  --abstr_ref_under                       []
% 3.32/1.00  
% 3.32/1.00  ------ SAT Options
% 3.32/1.00  
% 3.32/1.00  --sat_mode                              false
% 3.32/1.00  --sat_fm_restart_options                ""
% 3.32/1.00  --sat_gr_def                            false
% 3.32/1.00  --sat_epr_types                         true
% 3.32/1.00  --sat_non_cyclic_types                  false
% 3.32/1.00  --sat_finite_models                     false
% 3.32/1.00  --sat_fm_lemmas                         false
% 3.32/1.00  --sat_fm_prep                           false
% 3.32/1.00  --sat_fm_uc_incr                        true
% 3.32/1.00  --sat_out_model                         small
% 3.32/1.00  --sat_out_clauses                       false
% 3.32/1.00  
% 3.32/1.00  ------ QBF Options
% 3.32/1.00  
% 3.32/1.00  --qbf_mode                              false
% 3.32/1.00  --qbf_elim_univ                         false
% 3.32/1.00  --qbf_dom_inst                          none
% 3.32/1.00  --qbf_dom_pre_inst                      false
% 3.32/1.00  --qbf_sk_in                             false
% 3.32/1.00  --qbf_pred_elim                         true
% 3.32/1.00  --qbf_split                             512
% 3.32/1.00  
% 3.32/1.00  ------ BMC1 Options
% 3.32/1.00  
% 3.32/1.00  --bmc1_incremental                      false
% 3.32/1.00  --bmc1_axioms                           reachable_all
% 3.32/1.00  --bmc1_min_bound                        0
% 3.32/1.00  --bmc1_max_bound                        -1
% 3.32/1.00  --bmc1_max_bound_default                -1
% 3.32/1.00  --bmc1_symbol_reachability              true
% 3.32/1.00  --bmc1_property_lemmas                  false
% 3.32/1.00  --bmc1_k_induction                      false
% 3.32/1.00  --bmc1_non_equiv_states                 false
% 3.32/1.00  --bmc1_deadlock                         false
% 3.32/1.00  --bmc1_ucm                              false
% 3.32/1.00  --bmc1_add_unsat_core                   none
% 3.32/1.00  --bmc1_unsat_core_children              false
% 3.32/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.32/1.00  --bmc1_out_stat                         full
% 3.32/1.00  --bmc1_ground_init                      false
% 3.32/1.00  --bmc1_pre_inst_next_state              false
% 3.32/1.00  --bmc1_pre_inst_state                   false
% 3.32/1.00  --bmc1_pre_inst_reach_state             false
% 3.32/1.00  --bmc1_out_unsat_core                   false
% 3.32/1.00  --bmc1_aig_witness_out                  false
% 3.32/1.00  --bmc1_verbose                          false
% 3.32/1.00  --bmc1_dump_clauses_tptp                false
% 3.32/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.32/1.00  --bmc1_dump_file                        -
% 3.32/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.32/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.32/1.00  --bmc1_ucm_extend_mode                  1
% 3.32/1.00  --bmc1_ucm_init_mode                    2
% 3.32/1.00  --bmc1_ucm_cone_mode                    none
% 3.32/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.32/1.00  --bmc1_ucm_relax_model                  4
% 3.32/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.32/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.32/1.00  --bmc1_ucm_layered_model                none
% 3.32/1.00  --bmc1_ucm_max_lemma_size               10
% 3.32/1.00  
% 3.32/1.00  ------ AIG Options
% 3.32/1.00  
% 3.32/1.00  --aig_mode                              false
% 3.32/1.00  
% 3.32/1.00  ------ Instantiation Options
% 3.32/1.00  
% 3.32/1.00  --instantiation_flag                    true
% 3.32/1.00  --inst_sos_flag                         false
% 3.32/1.00  --inst_sos_phase                        true
% 3.32/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.32/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.32/1.00  --inst_lit_sel_side                     num_symb
% 3.32/1.00  --inst_solver_per_active                1400
% 3.32/1.00  --inst_solver_calls_frac                1.
% 3.32/1.00  --inst_passive_queue_type               priority_queues
% 3.32/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.32/1.00  --inst_passive_queues_freq              [25;2]
% 3.32/1.00  --inst_dismatching                      true
% 3.32/1.00  --inst_eager_unprocessed_to_passive     true
% 3.32/1.00  --inst_prop_sim_given                   true
% 3.32/1.00  --inst_prop_sim_new                     false
% 3.32/1.00  --inst_subs_new                         false
% 3.32/1.00  --inst_eq_res_simp                      false
% 3.32/1.00  --inst_subs_given                       false
% 3.32/1.00  --inst_orphan_elimination               true
% 3.32/1.00  --inst_learning_loop_flag               true
% 3.32/1.00  --inst_learning_start                   3000
% 3.32/1.00  --inst_learning_factor                  2
% 3.32/1.00  --inst_start_prop_sim_after_learn       3
% 3.32/1.00  --inst_sel_renew                        solver
% 3.32/1.00  --inst_lit_activity_flag                true
% 3.32/1.00  --inst_restr_to_given                   false
% 3.32/1.00  --inst_activity_threshold               500
% 3.32/1.00  --inst_out_proof                        true
% 3.32/1.00  
% 3.32/1.00  ------ Resolution Options
% 3.32/1.00  
% 3.32/1.00  --resolution_flag                       true
% 3.32/1.00  --res_lit_sel                           adaptive
% 3.32/1.00  --res_lit_sel_side                      none
% 3.32/1.00  --res_ordering                          kbo
% 3.32/1.00  --res_to_prop_solver                    active
% 3.32/1.00  --res_prop_simpl_new                    false
% 3.32/1.00  --res_prop_simpl_given                  true
% 3.32/1.00  --res_passive_queue_type                priority_queues
% 3.32/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.32/1.00  --res_passive_queues_freq               [15;5]
% 3.32/1.00  --res_forward_subs                      full
% 3.32/1.00  --res_backward_subs                     full
% 3.32/1.00  --res_forward_subs_resolution           true
% 3.32/1.00  --res_backward_subs_resolution          true
% 3.32/1.00  --res_orphan_elimination                true
% 3.32/1.00  --res_time_limit                        2.
% 3.32/1.00  --res_out_proof                         true
% 3.32/1.00  
% 3.32/1.00  ------ Superposition Options
% 3.32/1.00  
% 3.32/1.00  --superposition_flag                    true
% 3.32/1.00  --sup_passive_queue_type                priority_queues
% 3.32/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.32/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.32/1.00  --demod_completeness_check              fast
% 3.32/1.00  --demod_use_ground                      true
% 3.32/1.00  --sup_to_prop_solver                    passive
% 3.32/1.00  --sup_prop_simpl_new                    true
% 3.32/1.00  --sup_prop_simpl_given                  true
% 3.32/1.00  --sup_fun_splitting                     false
% 3.32/1.00  --sup_smt_interval                      50000
% 3.32/1.00  
% 3.32/1.00  ------ Superposition Simplification Setup
% 3.32/1.00  
% 3.32/1.00  --sup_indices_passive                   []
% 3.32/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.32/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.32/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.32/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.32/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.32/1.00  --sup_full_bw                           [BwDemod]
% 3.32/1.00  --sup_immed_triv                        [TrivRules]
% 3.32/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.32/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.32/1.00  --sup_immed_bw_main                     []
% 3.32/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.32/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.32/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.32/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.32/1.00  
% 3.32/1.00  ------ Combination Options
% 3.32/1.00  
% 3.32/1.00  --comb_res_mult                         3
% 3.32/1.00  --comb_sup_mult                         2
% 3.32/1.00  --comb_inst_mult                        10
% 3.32/1.00  
% 3.32/1.00  ------ Debug Options
% 3.32/1.00  
% 3.32/1.00  --dbg_backtrace                         false
% 3.32/1.00  --dbg_dump_prop_clauses                 false
% 3.32/1.00  --dbg_dump_prop_clauses_file            -
% 3.32/1.00  --dbg_out_stat                          false
% 3.32/1.00  ------ Parsing...
% 3.32/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.32/1.00  
% 3.32/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e 
% 3.32/1.00  
% 3.32/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.32/1.00  
% 3.32/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.32/1.00  ------ Proving...
% 3.32/1.00  ------ Problem Properties 
% 3.32/1.00  
% 3.32/1.00  
% 3.32/1.00  clauses                                 46
% 3.32/1.00  conjectures                             3
% 3.32/1.00  EPR                                     7
% 3.32/1.00  Horn                                    37
% 3.32/1.00  unary                                   13
% 3.32/1.00  binary                                  8
% 3.32/1.00  lits                                    129
% 3.32/1.00  lits eq                                 51
% 3.32/1.00  fd_pure                                 0
% 3.32/1.00  fd_pseudo                               0
% 3.32/1.00  fd_cond                                 5
% 3.32/1.00  fd_pseudo_cond                          1
% 3.32/1.00  AC symbols                              0
% 3.32/1.00  
% 3.32/1.00  ------ Schedule dynamic 5 is on 
% 3.32/1.00  
% 3.32/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.32/1.00  
% 3.32/1.00  
% 3.32/1.00  ------ 
% 3.32/1.00  Current options:
% 3.32/1.00  ------ 
% 3.32/1.00  
% 3.32/1.00  ------ Input Options
% 3.32/1.00  
% 3.32/1.00  --out_options                           all
% 3.32/1.00  --tptp_safe_out                         true
% 3.32/1.00  --problem_path                          ""
% 3.32/1.00  --include_path                          ""
% 3.32/1.00  --clausifier                            res/vclausify_rel
% 3.32/1.00  --clausifier_options                    --mode clausify
% 3.32/1.00  --stdin                                 false
% 3.32/1.00  --stats_out                             all
% 3.32/1.00  
% 3.32/1.00  ------ General Options
% 3.32/1.00  
% 3.32/1.00  --fof                                   false
% 3.32/1.00  --time_out_real                         305.
% 3.32/1.00  --time_out_virtual                      -1.
% 3.32/1.00  --symbol_type_check                     false
% 3.32/1.00  --clausify_out                          false
% 3.32/1.00  --sig_cnt_out                           false
% 3.32/1.00  --trig_cnt_out                          false
% 3.32/1.00  --trig_cnt_out_tolerance                1.
% 3.32/1.00  --trig_cnt_out_sk_spl                   false
% 3.32/1.00  --abstr_cl_out                          false
% 3.32/1.00  
% 3.32/1.00  ------ Global Options
% 3.32/1.00  
% 3.32/1.00  --schedule                              default
% 3.32/1.00  --add_important_lit                     false
% 3.32/1.00  --prop_solver_per_cl                    1000
% 3.32/1.00  --min_unsat_core                        false
% 3.32/1.00  --soft_assumptions                      false
% 3.32/1.00  --soft_lemma_size                       3
% 3.32/1.00  --prop_impl_unit_size                   0
% 3.32/1.00  --prop_impl_unit                        []
% 3.32/1.00  --share_sel_clauses                     true
% 3.32/1.00  --reset_solvers                         false
% 3.32/1.00  --bc_imp_inh                            [conj_cone]
% 3.32/1.00  --conj_cone_tolerance                   3.
% 3.32/1.00  --extra_neg_conj                        none
% 3.32/1.00  --large_theory_mode                     true
% 3.32/1.00  --prolific_symb_bound                   200
% 3.32/1.00  --lt_threshold                          2000
% 3.32/1.00  --clause_weak_htbl                      true
% 3.32/1.00  --gc_record_bc_elim                     false
% 3.32/1.00  
% 3.32/1.00  ------ Preprocessing Options
% 3.32/1.00  
% 3.32/1.00  --preprocessing_flag                    true
% 3.32/1.00  --time_out_prep_mult                    0.1
% 3.32/1.00  --splitting_mode                        input
% 3.32/1.00  --splitting_grd                         true
% 3.32/1.00  --splitting_cvd                         false
% 3.32/1.00  --splitting_cvd_svl                     false
% 3.32/1.00  --splitting_nvd                         32
% 3.32/1.00  --sub_typing                            true
% 3.32/1.00  --prep_gs_sim                           true
% 3.32/1.00  --prep_unflatten                        true
% 3.32/1.00  --prep_res_sim                          true
% 3.32/1.00  --prep_upred                            true
% 3.32/1.00  --prep_sem_filter                       exhaustive
% 3.32/1.00  --prep_sem_filter_out                   false
% 3.32/1.00  --pred_elim                             true
% 3.32/1.00  --res_sim_input                         true
% 3.32/1.00  --eq_ax_congr_red                       true
% 3.32/1.00  --pure_diseq_elim                       true
% 3.32/1.00  --brand_transform                       false
% 3.32/1.00  --non_eq_to_eq                          false
% 3.32/1.00  --prep_def_merge                        true
% 3.32/1.00  --prep_def_merge_prop_impl              false
% 3.32/1.00  --prep_def_merge_mbd                    true
% 3.32/1.00  --prep_def_merge_tr_red                 false
% 3.32/1.00  --prep_def_merge_tr_cl                  false
% 3.32/1.00  --smt_preprocessing                     true
% 3.32/1.00  --smt_ac_axioms                         fast
% 3.32/1.00  --preprocessed_out                      false
% 3.32/1.00  --preprocessed_stats                    false
% 3.32/1.00  
% 3.32/1.00  ------ Abstraction refinement Options
% 3.32/1.00  
% 3.32/1.00  --abstr_ref                             []
% 3.32/1.00  --abstr_ref_prep                        false
% 3.32/1.00  --abstr_ref_until_sat                   false
% 3.32/1.00  --abstr_ref_sig_restrict                funpre
% 3.32/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.32/1.00  --abstr_ref_under                       []
% 3.32/1.00  
% 3.32/1.00  ------ SAT Options
% 3.32/1.00  
% 3.32/1.00  --sat_mode                              false
% 3.32/1.00  --sat_fm_restart_options                ""
% 3.32/1.00  --sat_gr_def                            false
% 3.32/1.00  --sat_epr_types                         true
% 3.32/1.00  --sat_non_cyclic_types                  false
% 3.32/1.00  --sat_finite_models                     false
% 3.32/1.00  --sat_fm_lemmas                         false
% 3.32/1.00  --sat_fm_prep                           false
% 3.32/1.00  --sat_fm_uc_incr                        true
% 3.32/1.00  --sat_out_model                         small
% 3.32/1.00  --sat_out_clauses                       false
% 3.32/1.00  
% 3.32/1.00  ------ QBF Options
% 3.32/1.00  
% 3.32/1.00  --qbf_mode                              false
% 3.32/1.00  --qbf_elim_univ                         false
% 3.32/1.00  --qbf_dom_inst                          none
% 3.32/1.00  --qbf_dom_pre_inst                      false
% 3.32/1.00  --qbf_sk_in                             false
% 3.32/1.00  --qbf_pred_elim                         true
% 3.32/1.00  --qbf_split                             512
% 3.32/1.00  
% 3.32/1.00  ------ BMC1 Options
% 3.32/1.00  
% 3.32/1.00  --bmc1_incremental                      false
% 3.32/1.00  --bmc1_axioms                           reachable_all
% 3.32/1.00  --bmc1_min_bound                        0
% 3.32/1.00  --bmc1_max_bound                        -1
% 3.32/1.00  --bmc1_max_bound_default                -1
% 3.32/1.00  --bmc1_symbol_reachability              true
% 3.32/1.00  --bmc1_property_lemmas                  false
% 3.32/1.00  --bmc1_k_induction                      false
% 3.32/1.00  --bmc1_non_equiv_states                 false
% 3.32/1.00  --bmc1_deadlock                         false
% 3.32/1.00  --bmc1_ucm                              false
% 3.32/1.00  --bmc1_add_unsat_core                   none
% 3.32/1.00  --bmc1_unsat_core_children              false
% 3.32/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.32/1.00  --bmc1_out_stat                         full
% 3.32/1.00  --bmc1_ground_init                      false
% 3.32/1.00  --bmc1_pre_inst_next_state              false
% 3.32/1.00  --bmc1_pre_inst_state                   false
% 3.32/1.00  --bmc1_pre_inst_reach_state             false
% 3.32/1.00  --bmc1_out_unsat_core                   false
% 3.32/1.00  --bmc1_aig_witness_out                  false
% 3.32/1.00  --bmc1_verbose                          false
% 3.32/1.00  --bmc1_dump_clauses_tptp                false
% 3.32/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.32/1.00  --bmc1_dump_file                        -
% 3.32/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.32/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.32/1.00  --bmc1_ucm_extend_mode                  1
% 3.32/1.00  --bmc1_ucm_init_mode                    2
% 3.32/1.00  --bmc1_ucm_cone_mode                    none
% 3.32/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.32/1.00  --bmc1_ucm_relax_model                  4
% 3.32/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.32/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.32/1.00  --bmc1_ucm_layered_model                none
% 3.32/1.00  --bmc1_ucm_max_lemma_size               10
% 3.32/1.00  
% 3.32/1.00  ------ AIG Options
% 3.32/1.00  
% 3.32/1.00  --aig_mode                              false
% 3.32/1.00  
% 3.32/1.00  ------ Instantiation Options
% 3.32/1.00  
% 3.32/1.00  --instantiation_flag                    true
% 3.32/1.00  --inst_sos_flag                         false
% 3.32/1.00  --inst_sos_phase                        true
% 3.32/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.32/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.32/1.00  --inst_lit_sel_side                     none
% 3.32/1.00  --inst_solver_per_active                1400
% 3.32/1.00  --inst_solver_calls_frac                1.
% 3.32/1.00  --inst_passive_queue_type               priority_queues
% 3.32/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.32/1.00  --inst_passive_queues_freq              [25;2]
% 3.32/1.00  --inst_dismatching                      true
% 3.32/1.00  --inst_eager_unprocessed_to_passive     true
% 3.32/1.00  --inst_prop_sim_given                   true
% 3.32/1.00  --inst_prop_sim_new                     false
% 3.32/1.00  --inst_subs_new                         false
% 3.32/1.00  --inst_eq_res_simp                      false
% 3.32/1.00  --inst_subs_given                       false
% 3.32/1.00  --inst_orphan_elimination               true
% 3.32/1.00  --inst_learning_loop_flag               true
% 3.32/1.00  --inst_learning_start                   3000
% 3.32/1.00  --inst_learning_factor                  2
% 3.32/1.00  --inst_start_prop_sim_after_learn       3
% 3.32/1.00  --inst_sel_renew                        solver
% 3.32/1.00  --inst_lit_activity_flag                true
% 3.32/1.00  --inst_restr_to_given                   false
% 3.32/1.00  --inst_activity_threshold               500
% 3.32/1.00  --inst_out_proof                        true
% 3.32/1.00  
% 3.32/1.00  ------ Resolution Options
% 3.32/1.00  
% 3.32/1.00  --resolution_flag                       false
% 3.32/1.00  --res_lit_sel                           adaptive
% 3.32/1.00  --res_lit_sel_side                      none
% 3.32/1.00  --res_ordering                          kbo
% 3.32/1.00  --res_to_prop_solver                    active
% 3.32/1.00  --res_prop_simpl_new                    false
% 3.32/1.00  --res_prop_simpl_given                  true
% 3.32/1.00  --res_passive_queue_type                priority_queues
% 3.32/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.32/1.00  --res_passive_queues_freq               [15;5]
% 3.32/1.00  --res_forward_subs                      full
% 3.32/1.00  --res_backward_subs                     full
% 3.32/1.00  --res_forward_subs_resolution           true
% 3.32/1.00  --res_backward_subs_resolution          true
% 3.32/1.00  --res_orphan_elimination                true
% 3.32/1.00  --res_time_limit                        2.
% 3.32/1.00  --res_out_proof                         true
% 3.32/1.00  
% 3.32/1.00  ------ Superposition Options
% 3.32/1.00  
% 3.32/1.00  --superposition_flag                    true
% 3.32/1.00  --sup_passive_queue_type                priority_queues
% 3.32/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.32/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.32/1.00  --demod_completeness_check              fast
% 3.32/1.00  --demod_use_ground                      true
% 3.32/1.00  --sup_to_prop_solver                    passive
% 3.32/1.00  --sup_prop_simpl_new                    true
% 3.32/1.00  --sup_prop_simpl_given                  true
% 3.32/1.00  --sup_fun_splitting                     false
% 3.32/1.00  --sup_smt_interval                      50000
% 3.32/1.00  
% 3.32/1.00  ------ Superposition Simplification Setup
% 3.32/1.00  
% 3.32/1.00  --sup_indices_passive                   []
% 3.32/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.32/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.32/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.32/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.32/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.32/1.00  --sup_full_bw                           [BwDemod]
% 3.32/1.00  --sup_immed_triv                        [TrivRules]
% 3.32/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.32/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.32/1.00  --sup_immed_bw_main                     []
% 3.32/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.32/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.32/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.32/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.32/1.00  
% 3.32/1.00  ------ Combination Options
% 3.32/1.00  
% 3.32/1.00  --comb_res_mult                         3
% 3.32/1.00  --comb_sup_mult                         2
% 3.32/1.00  --comb_inst_mult                        10
% 3.32/1.00  
% 3.32/1.00  ------ Debug Options
% 3.32/1.00  
% 3.32/1.00  --dbg_backtrace                         false
% 3.32/1.00  --dbg_dump_prop_clauses                 false
% 3.32/1.00  --dbg_dump_prop_clauses_file            -
% 3.32/1.00  --dbg_out_stat                          false
% 3.32/1.00  
% 3.32/1.00  
% 3.32/1.00  
% 3.32/1.00  
% 3.32/1.00  ------ Proving...
% 3.32/1.00  
% 3.32/1.00  
% 3.32/1.00  % SZS status Theorem for theBenchmark.p
% 3.32/1.00  
% 3.32/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.32/1.00  
% 3.32/1.00  fof(f15,axiom,(
% 3.32/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.32/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/1.00  
% 3.32/1.00  fof(f33,plain,(
% 3.32/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.32/1.00    inference(ennf_transformation,[],[f15])).
% 3.32/1.00  
% 3.32/1.00  fof(f34,plain,(
% 3.32/1.00    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.32/1.00    inference(flattening,[],[f33])).
% 3.32/1.00  
% 3.32/1.00  fof(f48,plain,(
% 3.32/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.32/1.00    inference(nnf_transformation,[],[f34])).
% 3.32/1.00  
% 3.32/1.00  fof(f74,plain,(
% 3.32/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.32/1.00    inference(cnf_transformation,[],[f48])).
% 3.32/1.00  
% 3.32/1.00  fof(f19,conjecture,(
% 3.32/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 3.32/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/1.00  
% 3.32/1.00  fof(f20,negated_conjecture,(
% 3.32/1.00    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 3.32/1.00    inference(negated_conjecture,[],[f19])).
% 3.32/1.00  
% 3.32/1.00  fof(f39,plain,(
% 3.32/1.00    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.32/1.00    inference(ennf_transformation,[],[f20])).
% 3.32/1.00  
% 3.32/1.00  fof(f40,plain,(
% 3.32/1.00    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 3.32/1.00    inference(flattening,[],[f39])).
% 3.32/1.00  
% 3.32/1.00  fof(f49,plain,(
% 3.32/1.00    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))) & k2_relset_1(sK1,sK2,sK3) = sK2 & v2_funct_1(sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3))),
% 3.32/1.00    introduced(choice_axiom,[])).
% 3.32/1.00  
% 3.32/1.00  fof(f50,plain,(
% 3.32/1.00    (~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))) & k2_relset_1(sK1,sK2,sK3) = sK2 & v2_funct_1(sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)),
% 3.32/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f40,f49])).
% 3.32/1.00  
% 3.32/1.00  fof(f89,plain,(
% 3.32/1.00    v1_funct_2(sK3,sK1,sK2)),
% 3.32/1.00    inference(cnf_transformation,[],[f50])).
% 3.32/1.00  
% 3.32/1.00  fof(f90,plain,(
% 3.32/1.00    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 3.32/1.00    inference(cnf_transformation,[],[f50])).
% 3.32/1.00  
% 3.32/1.00  fof(f12,axiom,(
% 3.32/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.32/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/1.00  
% 3.32/1.00  fof(f29,plain,(
% 3.32/1.00    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.32/1.00    inference(ennf_transformation,[],[f12])).
% 3.32/1.00  
% 3.32/1.00  fof(f70,plain,(
% 3.32/1.00    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.32/1.00    inference(cnf_transformation,[],[f29])).
% 3.32/1.00  
% 3.32/1.00  fof(f11,axiom,(
% 3.32/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.32/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/1.00  
% 3.32/1.00  fof(f28,plain,(
% 3.32/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.32/1.00    inference(ennf_transformation,[],[f11])).
% 3.32/1.00  
% 3.32/1.00  fof(f69,plain,(
% 3.32/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.32/1.00    inference(cnf_transformation,[],[f28])).
% 3.32/1.00  
% 3.32/1.00  fof(f10,axiom,(
% 3.32/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 3.32/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/1.00  
% 3.32/1.00  fof(f26,plain,(
% 3.32/1.00    ! [X0] : (((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.32/1.00    inference(ennf_transformation,[],[f10])).
% 3.32/1.00  
% 3.32/1.00  fof(f27,plain,(
% 3.32/1.00    ! [X0] : ((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.32/1.00    inference(flattening,[],[f26])).
% 3.32/1.00  
% 3.32/1.00  fof(f68,plain,(
% 3.32/1.00    ( ! [X0] : (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.32/1.00    inference(cnf_transformation,[],[f27])).
% 3.32/1.00  
% 3.32/1.00  fof(f91,plain,(
% 3.32/1.00    v2_funct_1(sK3)),
% 3.32/1.00    inference(cnf_transformation,[],[f50])).
% 3.32/1.00  
% 3.32/1.00  fof(f88,plain,(
% 3.32/1.00    v1_funct_1(sK3)),
% 3.32/1.00    inference(cnf_transformation,[],[f50])).
% 3.32/1.00  
% 3.32/1.00  fof(f17,axiom,(
% 3.32/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 3.32/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/1.00  
% 3.32/1.00  fof(f35,plain,(
% 3.32/1.00    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.32/1.00    inference(ennf_transformation,[],[f17])).
% 3.32/1.00  
% 3.32/1.00  fof(f36,plain,(
% 3.32/1.00    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.32/1.00    inference(flattening,[],[f35])).
% 3.32/1.00  
% 3.32/1.00  fof(f84,plain,(
% 3.32/1.00    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.32/1.00    inference(cnf_transformation,[],[f36])).
% 3.32/1.00  
% 3.32/1.00  fof(f13,axiom,(
% 3.32/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.32/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/1.00  
% 3.32/1.00  fof(f30,plain,(
% 3.32/1.00    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.32/1.00    inference(ennf_transformation,[],[f13])).
% 3.32/1.00  
% 3.32/1.00  fof(f71,plain,(
% 3.32/1.00    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.32/1.00    inference(cnf_transformation,[],[f30])).
% 3.32/1.00  
% 3.32/1.00  fof(f92,plain,(
% 3.32/1.00    k2_relset_1(sK1,sK2,sK3) = sK2),
% 3.32/1.00    inference(cnf_transformation,[],[f50])).
% 3.32/1.00  
% 3.32/1.00  fof(f67,plain,(
% 3.32/1.00    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.32/1.00    inference(cnf_transformation,[],[f27])).
% 3.32/1.00  
% 3.32/1.00  fof(f8,axiom,(
% 3.32/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 3.32/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/1.00  
% 3.32/1.00  fof(f24,plain,(
% 3.32/1.00    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.32/1.00    inference(ennf_transformation,[],[f8])).
% 3.32/1.00  
% 3.32/1.00  fof(f25,plain,(
% 3.32/1.00    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.32/1.00    inference(flattening,[],[f24])).
% 3.32/1.00  
% 3.32/1.00  fof(f63,plain,(
% 3.32/1.00    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.32/1.00    inference(cnf_transformation,[],[f25])).
% 3.32/1.00  
% 3.32/1.00  fof(f62,plain,(
% 3.32/1.00    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.32/1.00    inference(cnf_transformation,[],[f25])).
% 3.32/1.00  
% 3.32/1.00  fof(f83,plain,(
% 3.32/1.00    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.32/1.00    inference(cnf_transformation,[],[f36])).
% 3.32/1.00  
% 3.32/1.00  fof(f93,plain,(
% 3.32/1.00    ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))),
% 3.32/1.00    inference(cnf_transformation,[],[f50])).
% 3.32/1.00  
% 3.32/1.00  fof(f5,axiom,(
% 3.32/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.32/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/1.00  
% 3.32/1.00  fof(f45,plain,(
% 3.32/1.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.32/1.00    inference(nnf_transformation,[],[f5])).
% 3.32/1.00  
% 3.32/1.00  fof(f59,plain,(
% 3.32/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.32/1.00    inference(cnf_transformation,[],[f45])).
% 3.32/1.00  
% 3.32/1.00  fof(f1,axiom,(
% 3.32/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.32/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/1.00  
% 3.32/1.00  fof(f41,plain,(
% 3.32/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.32/1.00    inference(nnf_transformation,[],[f1])).
% 3.32/1.00  
% 3.32/1.00  fof(f42,plain,(
% 3.32/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.32/1.00    inference(flattening,[],[f41])).
% 3.32/1.00  
% 3.32/1.00  fof(f53,plain,(
% 3.32/1.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.32/1.00    inference(cnf_transformation,[],[f42])).
% 3.32/1.00  
% 3.32/1.00  fof(f3,axiom,(
% 3.32/1.00    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.32/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/1.00  
% 3.32/1.00  fof(f43,plain,(
% 3.32/1.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.32/1.00    inference(nnf_transformation,[],[f3])).
% 3.32/1.00  
% 3.32/1.00  fof(f44,plain,(
% 3.32/1.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.32/1.00    inference(flattening,[],[f43])).
% 3.32/1.00  
% 3.32/1.00  fof(f57,plain,(
% 3.32/1.00    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 3.32/1.00    inference(cnf_transformation,[],[f44])).
% 3.32/1.00  
% 3.32/1.00  fof(f96,plain,(
% 3.32/1.00    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 3.32/1.00    inference(equality_resolution,[],[f57])).
% 3.32/1.00  
% 3.32/1.00  fof(f2,axiom,(
% 3.32/1.00    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.32/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/1.00  
% 3.32/1.00  fof(f54,plain,(
% 3.32/1.00    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.32/1.00    inference(cnf_transformation,[],[f2])).
% 3.32/1.00  
% 3.32/1.00  fof(f56,plain,(
% 3.32/1.00    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 3.32/1.00    inference(cnf_transformation,[],[f44])).
% 3.32/1.00  
% 3.32/1.00  fof(f97,plain,(
% 3.32/1.00    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.32/1.00    inference(equality_resolution,[],[f56])).
% 3.32/1.00  
% 3.32/1.00  fof(f77,plain,(
% 3.32/1.00    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.32/1.00    inference(cnf_transformation,[],[f48])).
% 3.32/1.00  
% 3.32/1.00  fof(f101,plain,(
% 3.32/1.00    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 3.32/1.00    inference(equality_resolution,[],[f77])).
% 3.32/1.00  
% 3.32/1.00  fof(f55,plain,(
% 3.32/1.00    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 3.32/1.00    inference(cnf_transformation,[],[f44])).
% 3.32/1.00  
% 3.32/1.00  cnf(c_28,plain,
% 3.32/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.32/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.32/1.00      | k1_relset_1(X1,X2,X0) = X1
% 3.32/1.00      | k1_xboole_0 = X2 ),
% 3.32/1.00      inference(cnf_transformation,[],[f74]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_41,negated_conjecture,
% 3.32/1.00      ( v1_funct_2(sK3,sK1,sK2) ),
% 3.32/1.00      inference(cnf_transformation,[],[f89]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_626,plain,
% 3.32/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.32/1.00      | k1_relset_1(X1,X2,X0) = X1
% 3.32/1.00      | sK1 != X1
% 3.32/1.00      | sK2 != X2
% 3.32/1.00      | sK3 != X0
% 3.32/1.00      | k1_xboole_0 = X2 ),
% 3.32/1.00      inference(resolution_lifted,[status(thm)],[c_28,c_41]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_627,plain,
% 3.32/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 3.32/1.00      | k1_relset_1(sK1,sK2,sK3) = sK1
% 3.32/1.00      | k1_xboole_0 = sK2 ),
% 3.32/1.00      inference(unflattening,[status(thm)],[c_626]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_40,negated_conjecture,
% 3.32/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 3.32/1.00      inference(cnf_transformation,[],[f90]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_629,plain,
% 3.32/1.00      ( k1_relset_1(sK1,sK2,sK3) = sK1 | k1_xboole_0 = sK2 ),
% 3.32/1.00      inference(global_propositional_subsumption,
% 3.32/1.00                [status(thm)],
% 3.32/1.00                [c_627,c_40]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_1918,plain,
% 3.32/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 3.32/1.00      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_19,plain,
% 3.32/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.32/1.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.32/1.00      inference(cnf_transformation,[],[f70]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_1923,plain,
% 3.32/1.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.32/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.32/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_4169,plain,
% 3.32/1.00      ( k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
% 3.32/1.00      inference(superposition,[status(thm)],[c_1918,c_1923]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_4318,plain,
% 3.32/1.00      ( k1_relat_1(sK3) = sK1 | sK2 = k1_xboole_0 ),
% 3.32/1.00      inference(superposition,[status(thm)],[c_629,c_4169]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_18,plain,
% 3.32/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.32/1.00      | v1_relat_1(X0) ),
% 3.32/1.00      inference(cnf_transformation,[],[f69]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_1924,plain,
% 3.32/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.32/1.00      | v1_relat_1(X0) = iProver_top ),
% 3.32/1.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_3351,plain,
% 3.32/1.00      ( v1_relat_1(sK3) = iProver_top ),
% 3.32/1.00      inference(superposition,[status(thm)],[c_1918,c_1924]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_16,plain,
% 3.32/1.00      ( ~ v2_funct_1(X0)
% 3.32/1.00      | ~ v1_relat_1(X0)
% 3.32/1.00      | ~ v1_funct_1(X0)
% 3.32/1.00      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 3.32/1.00      inference(cnf_transformation,[],[f68]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_39,negated_conjecture,
% 3.32/1.00      ( v2_funct_1(sK3) ),
% 3.32/1.00      inference(cnf_transformation,[],[f91]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_527,plain,
% 3.32/1.00      ( ~ v1_relat_1(X0)
% 3.32/1.00      | ~ v1_funct_1(X0)
% 3.32/1.00      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 3.32/1.00      | sK3 != X0 ),
% 3.32/1.00      inference(resolution_lifted,[status(thm)],[c_16,c_39]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_528,plain,
% 3.32/1.00      ( ~ v1_relat_1(sK3)
% 3.32/1.00      | ~ v1_funct_1(sK3)
% 3.32/1.00      | k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
% 3.32/1.00      inference(unflattening,[status(thm)],[c_527]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_42,negated_conjecture,
% 3.32/1.00      ( v1_funct_1(sK3) ),
% 3.32/1.00      inference(cnf_transformation,[],[f88]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_530,plain,
% 3.32/1.00      ( ~ v1_relat_1(sK3)
% 3.32/1.00      | k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
% 3.32/1.00      inference(global_propositional_subsumption,
% 3.32/1.00                [status(thm)],
% 3.32/1.00                [c_528,c_42]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_1914,plain,
% 3.32/1.00      ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3)
% 3.32/1.00      | v1_relat_1(sK3) != iProver_top ),
% 3.32/1.00      inference(predicate_to_equality,[status(thm)],[c_530]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_3583,plain,
% 3.32/1.00      ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
% 3.32/1.00      inference(superposition,[status(thm)],[c_3351,c_1914]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_31,plain,
% 3.32/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 3.32/1.00      | ~ v1_relat_1(X0)
% 3.32/1.00      | ~ v1_funct_1(X0) ),
% 3.32/1.00      inference(cnf_transformation,[],[f84]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_1920,plain,
% 3.32/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
% 3.32/1.00      | v1_relat_1(X0) != iProver_top
% 3.32/1.00      | v1_funct_1(X0) != iProver_top ),
% 3.32/1.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_5480,plain,
% 3.32/1.00      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK3)),k1_relat_1(sK3)))) = iProver_top
% 3.32/1.00      | v1_relat_1(k2_funct_1(sK3)) != iProver_top
% 3.32/1.00      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 3.32/1.00      inference(superposition,[status(thm)],[c_3583,c_1920]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_20,plain,
% 3.32/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.32/1.00      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.32/1.00      inference(cnf_transformation,[],[f71]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_1922,plain,
% 3.32/1.00      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.32/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.32/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_3487,plain,
% 3.32/1.00      ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
% 3.32/1.00      inference(superposition,[status(thm)],[c_1918,c_1922]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_38,negated_conjecture,
% 3.32/1.00      ( k2_relset_1(sK1,sK2,sK3) = sK2 ),
% 3.32/1.00      inference(cnf_transformation,[],[f92]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_3499,plain,
% 3.32/1.00      ( k2_relat_1(sK3) = sK2 ),
% 3.32/1.00      inference(light_normalisation,[status(thm)],[c_3487,c_38]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_17,plain,
% 3.32/1.00      ( ~ v2_funct_1(X0)
% 3.32/1.00      | ~ v1_relat_1(X0)
% 3.32/1.00      | ~ v1_funct_1(X0)
% 3.32/1.00      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 3.32/1.00      inference(cnf_transformation,[],[f67]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_513,plain,
% 3.32/1.00      ( ~ v1_relat_1(X0)
% 3.32/1.00      | ~ v1_funct_1(X0)
% 3.32/1.00      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 3.32/1.00      | sK3 != X0 ),
% 3.32/1.00      inference(resolution_lifted,[status(thm)],[c_17,c_39]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_514,plain,
% 3.32/1.00      ( ~ v1_relat_1(sK3)
% 3.32/1.00      | ~ v1_funct_1(sK3)
% 3.32/1.00      | k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
% 3.32/1.00      inference(unflattening,[status(thm)],[c_513]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_516,plain,
% 3.32/1.00      ( ~ v1_relat_1(sK3)
% 3.32/1.00      | k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
% 3.32/1.00      inference(global_propositional_subsumption,
% 3.32/1.00                [status(thm)],
% 3.32/1.00                [c_514,c_42]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_1915,plain,
% 3.32/1.00      ( k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3)
% 3.32/1.00      | v1_relat_1(sK3) != iProver_top ),
% 3.32/1.00      inference(predicate_to_equality,[status(thm)],[c_516]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_3577,plain,
% 3.32/1.00      ( k1_relat_1(k2_funct_1(sK3)) = sK2
% 3.32/1.00      | v1_relat_1(sK3) != iProver_top ),
% 3.32/1.00      inference(demodulation,[status(thm)],[c_3499,c_1915]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_45,plain,
% 3.32/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 3.32/1.00      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_2324,plain,
% 3.32/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 3.32/1.00      | v1_relat_1(sK3) ),
% 3.32/1.00      inference(instantiation,[status(thm)],[c_18]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_2325,plain,
% 3.32/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 3.32/1.00      | v1_relat_1(sK3) = iProver_top ),
% 3.32/1.00      inference(predicate_to_equality,[status(thm)],[c_2324]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_3659,plain,
% 3.32/1.00      ( k1_relat_1(k2_funct_1(sK3)) = sK2 ),
% 3.32/1.00      inference(global_propositional_subsumption,
% 3.32/1.00                [status(thm)],
% 3.32/1.00                [c_3577,c_45,c_2325]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_5506,plain,
% 3.32/1.00      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3)))) = iProver_top
% 3.32/1.00      | v1_relat_1(k2_funct_1(sK3)) != iProver_top
% 3.32/1.00      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 3.32/1.00      inference(light_normalisation,[status(thm)],[c_5480,c_3659]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_43,plain,
% 3.32/1.00      ( v1_funct_1(sK3) = iProver_top ),
% 3.32/1.00      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_11,plain,
% 3.32/1.00      ( ~ v1_relat_1(X0)
% 3.32/1.00      | ~ v1_funct_1(X0)
% 3.32/1.00      | v1_funct_1(k2_funct_1(X0)) ),
% 3.32/1.00      inference(cnf_transformation,[],[f63]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_2526,plain,
% 3.32/1.00      ( ~ v1_relat_1(sK3)
% 3.32/1.00      | v1_funct_1(k2_funct_1(sK3))
% 3.32/1.00      | ~ v1_funct_1(sK3) ),
% 3.32/1.00      inference(instantiation,[status(thm)],[c_11]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_2527,plain,
% 3.32/1.00      ( v1_relat_1(sK3) != iProver_top
% 3.32/1.00      | v1_funct_1(k2_funct_1(sK3)) = iProver_top
% 3.32/1.00      | v1_funct_1(sK3) != iProver_top ),
% 3.32/1.00      inference(predicate_to_equality,[status(thm)],[c_2526]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_12,plain,
% 3.32/1.00      ( ~ v1_relat_1(X0)
% 3.32/1.00      | v1_relat_1(k2_funct_1(X0))
% 3.32/1.00      | ~ v1_funct_1(X0) ),
% 3.32/1.00      inference(cnf_transformation,[],[f62]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_2533,plain,
% 3.32/1.00      ( v1_relat_1(k2_funct_1(sK3))
% 3.32/1.00      | ~ v1_relat_1(sK3)
% 3.32/1.00      | ~ v1_funct_1(sK3) ),
% 3.32/1.00      inference(instantiation,[status(thm)],[c_12]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_2534,plain,
% 3.32/1.00      ( v1_relat_1(k2_funct_1(sK3)) = iProver_top
% 3.32/1.00      | v1_relat_1(sK3) != iProver_top
% 3.32/1.00      | v1_funct_1(sK3) != iProver_top ),
% 3.32/1.00      inference(predicate_to_equality,[status(thm)],[c_2533]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_5840,plain,
% 3.32/1.00      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3)))) = iProver_top ),
% 3.32/1.00      inference(global_propositional_subsumption,
% 3.32/1.00                [status(thm)],
% 3.32/1.00                [c_5506,c_43,c_45,c_2325,c_2527,c_2534]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_5847,plain,
% 3.32/1.00      ( k1_relset_1(sK2,k1_relat_1(sK3),k2_funct_1(sK3)) = k1_relat_1(k2_funct_1(sK3)) ),
% 3.32/1.00      inference(superposition,[status(thm)],[c_5840,c_1923]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_5856,plain,
% 3.32/1.00      ( k1_relset_1(sK2,k1_relat_1(sK3),k2_funct_1(sK3)) = sK2 ),
% 3.32/1.00      inference(light_normalisation,[status(thm)],[c_5847,c_3659]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_5998,plain,
% 3.32/1.00      ( k1_relset_1(sK2,sK1,k2_funct_1(sK3)) = sK2 | sK2 = k1_xboole_0 ),
% 3.32/1.00      inference(superposition,[status(thm)],[c_4318,c_5856]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_32,plain,
% 3.32/1.00      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
% 3.32/1.00      | ~ v1_relat_1(X0)
% 3.32/1.00      | ~ v1_funct_1(X0) ),
% 3.32/1.00      inference(cnf_transformation,[],[f83]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_37,negated_conjecture,
% 3.32/1.00      ( ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
% 3.32/1.00      | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.32/1.00      | ~ v1_funct_1(k2_funct_1(sK3)) ),
% 3.32/1.00      inference(cnf_transformation,[],[f93]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_865,plain,
% 3.32/1.00      ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.32/1.00      | ~ v1_relat_1(X0)
% 3.32/1.00      | ~ v1_funct_1(X0)
% 3.32/1.00      | ~ v1_funct_1(k2_funct_1(sK3))
% 3.32/1.00      | k1_relat_1(X0) != sK2
% 3.32/1.00      | k2_relat_1(X0) != sK1
% 3.32/1.00      | k2_funct_1(sK3) != X0 ),
% 3.32/1.00      inference(resolution_lifted,[status(thm)],[c_32,c_37]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_866,plain,
% 3.32/1.00      ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.32/1.00      | ~ v1_relat_1(k2_funct_1(sK3))
% 3.32/1.00      | ~ v1_funct_1(k2_funct_1(sK3))
% 3.32/1.00      | k1_relat_1(k2_funct_1(sK3)) != sK2
% 3.32/1.00      | k2_relat_1(k2_funct_1(sK3)) != sK1 ),
% 3.32/1.00      inference(unflattening,[status(thm)],[c_865]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_878,plain,
% 3.32/1.00      ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.32/1.00      | ~ v1_funct_1(k2_funct_1(sK3))
% 3.32/1.00      | k1_relat_1(k2_funct_1(sK3)) != sK2
% 3.32/1.00      | k2_relat_1(k2_funct_1(sK3)) != sK1 ),
% 3.32/1.00      inference(forward_subsumption_resolution,
% 3.32/1.00                [status(thm)],
% 3.32/1.00                [c_866,c_18]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_1899,plain,
% 3.32/1.00      ( k1_relat_1(k2_funct_1(sK3)) != sK2
% 3.32/1.00      | k2_relat_1(k2_funct_1(sK3)) != sK1
% 3.32/1.00      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.32/1.00      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 3.32/1.00      inference(predicate_to_equality,[status(thm)],[c_878]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_3663,plain,
% 3.32/1.00      ( k2_relat_1(k2_funct_1(sK3)) != sK1
% 3.32/1.00      | sK2 != sK2
% 3.32/1.00      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.32/1.00      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 3.32/1.00      inference(demodulation,[status(thm)],[c_3659,c_1899]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_3664,plain,
% 3.32/1.00      ( k2_relat_1(k2_funct_1(sK3)) != sK1
% 3.32/1.00      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.32/1.00      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 3.32/1.00      inference(equality_resolution_simp,[status(thm)],[c_3663]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_867,plain,
% 3.32/1.00      ( k1_relat_1(k2_funct_1(sK3)) != sK2
% 3.32/1.00      | k2_relat_1(k2_funct_1(sK3)) != sK1
% 3.32/1.00      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.32/1.00      | v1_relat_1(k2_funct_1(sK3)) != iProver_top
% 3.32/1.00      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 3.32/1.00      inference(predicate_to_equality,[status(thm)],[c_866]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_3896,plain,
% 3.32/1.00      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.32/1.00      | k2_relat_1(k2_funct_1(sK3)) != sK1 ),
% 3.32/1.00      inference(global_propositional_subsumption,
% 3.32/1.00                [status(thm)],
% 3.32/1.00                [c_3664,c_43,c_45,c_867,c_2325,c_2527,c_2534,c_3577]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_3897,plain,
% 3.32/1.00      ( k2_relat_1(k2_funct_1(sK3)) != sK1
% 3.32/1.00      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.32/1.00      inference(renaming,[status(thm)],[c_3896]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_3900,plain,
% 3.32/1.00      ( k1_relat_1(sK3) != sK1
% 3.32/1.00      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.32/1.00      inference(light_normalisation,[status(thm)],[c_3897,c_3583]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_4322,plain,
% 3.32/1.00      ( sK2 = k1_xboole_0
% 3.32/1.00      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.32/1.00      inference(superposition,[status(thm)],[c_4318,c_3900]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_5845,plain,
% 3.32/1.00      ( sK2 = k1_xboole_0
% 3.32/1.00      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 3.32/1.00      inference(superposition,[status(thm)],[c_4318,c_5840]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_5999,plain,
% 3.32/1.00      ( sK2 = k1_xboole_0 ),
% 3.32/1.00      inference(global_propositional_subsumption,
% 3.32/1.00                [status(thm)],
% 3.32/1.00                [c_5998,c_4322,c_5845]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_9,plain,
% 3.32/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.32/1.00      inference(cnf_transformation,[],[f59]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_1929,plain,
% 3.32/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.32/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 3.32/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_3193,plain,
% 3.32/1.00      ( r1_tarski(sK3,k2_zfmisc_1(sK1,sK2)) = iProver_top ),
% 3.32/1.00      inference(superposition,[status(thm)],[c_1918,c_1929]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_0,plain,
% 3.32/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.32/1.00      inference(cnf_transformation,[],[f53]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_1934,plain,
% 3.32/1.00      ( X0 = X1
% 3.32/1.00      | r1_tarski(X0,X1) != iProver_top
% 3.32/1.00      | r1_tarski(X1,X0) != iProver_top ),
% 3.32/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_4908,plain,
% 3.32/1.00      ( k2_zfmisc_1(sK1,sK2) = sK3
% 3.32/1.00      | r1_tarski(k2_zfmisc_1(sK1,sK2),sK3) != iProver_top ),
% 3.32/1.00      inference(superposition,[status(thm)],[c_3193,c_1934]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_6012,plain,
% 3.32/1.00      ( k2_zfmisc_1(sK1,k1_xboole_0) = sK3
% 3.32/1.00      | r1_tarski(k2_zfmisc_1(sK1,k1_xboole_0),sK3) != iProver_top ),
% 3.32/1.00      inference(demodulation,[status(thm)],[c_5999,c_4908]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_4,plain,
% 3.32/1.00      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.32/1.00      inference(cnf_transformation,[],[f96]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_6126,plain,
% 3.32/1.00      ( sK3 = k1_xboole_0 | r1_tarski(k1_xboole_0,sK3) != iProver_top ),
% 3.32/1.00      inference(demodulation,[status(thm)],[c_6012,c_4]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_3,plain,
% 3.32/1.00      ( r1_tarski(k1_xboole_0,X0) ),
% 3.32/1.00      inference(cnf_transformation,[],[f54]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_2690,plain,
% 3.32/1.00      ( r1_tarski(k1_xboole_0,sK3) ),
% 3.32/1.00      inference(instantiation,[status(thm)],[c_3]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_2693,plain,
% 3.32/1.00      ( r1_tarski(k1_xboole_0,sK3) = iProver_top ),
% 3.32/1.00      inference(predicate_to_equality,[status(thm)],[c_2690]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_2698,plain,
% 3.32/1.00      ( ~ r1_tarski(X0,sK3) | ~ r1_tarski(sK3,X0) | sK3 = X0 ),
% 3.32/1.00      inference(instantiation,[status(thm)],[c_0]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_2699,plain,
% 3.32/1.00      ( sK3 = X0
% 3.32/1.00      | r1_tarski(X0,sK3) != iProver_top
% 3.32/1.00      | r1_tarski(sK3,X0) != iProver_top ),
% 3.32/1.00      inference(predicate_to_equality,[status(thm)],[c_2698]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_2701,plain,
% 3.32/1.00      ( sK3 = k1_xboole_0
% 3.32/1.00      | r1_tarski(sK3,k1_xboole_0) != iProver_top
% 3.32/1.00      | r1_tarski(k1_xboole_0,sK3) != iProver_top ),
% 3.32/1.00      inference(instantiation,[status(thm)],[c_2699]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_3318,plain,
% 3.32/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0)) | r1_tarski(sK3,X0) ),
% 3.32/1.00      inference(instantiation,[status(thm)],[c_9]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_3319,plain,
% 3.32/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
% 3.32/1.00      | r1_tarski(sK3,X0) = iProver_top ),
% 3.32/1.00      inference(predicate_to_equality,[status(thm)],[c_3318]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_3321,plain,
% 3.32/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.32/1.00      | r1_tarski(sK3,k1_xboole_0) = iProver_top ),
% 3.32/1.00      inference(instantiation,[status(thm)],[c_3319]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_6032,plain,
% 3.32/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) = iProver_top ),
% 3.32/1.00      inference(demodulation,[status(thm)],[c_5999,c_1918]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_6037,plain,
% 3.32/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.32/1.00      inference(demodulation,[status(thm)],[c_6032,c_4]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_6524,plain,
% 3.32/1.00      ( sK3 = k1_xboole_0 ),
% 3.32/1.00      inference(global_propositional_subsumption,
% 3.32/1.00                [status(thm)],
% 3.32/1.00                [c_6126,c_2693,c_2701,c_3321,c_6037]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_6003,plain,
% 3.32/1.00      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK3)))) = iProver_top ),
% 3.32/1.00      inference(demodulation,[status(thm)],[c_5999,c_5840]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_5,plain,
% 3.32/1.00      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.32/1.00      inference(cnf_transformation,[],[f97]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_6144,plain,
% 3.32/1.00      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.32/1.00      inference(demodulation,[status(thm)],[c_6003,c_5]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_6527,plain,
% 3.32/1.00      ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.32/1.00      inference(demodulation,[status(thm)],[c_6524,c_6144]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_4171,plain,
% 3.32/1.00      ( k1_relset_1(k1_xboole_0,X0,X1) = k1_relat_1(X1)
% 3.32/1.00      | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.32/1.00      inference(superposition,[status(thm)],[c_5,c_1923]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_9245,plain,
% 3.32/1.00      ( k1_relset_1(k1_xboole_0,X0,k2_funct_1(k1_xboole_0)) = k1_relat_1(k2_funct_1(k1_xboole_0)) ),
% 3.32/1.00      inference(superposition,[status(thm)],[c_6527,c_4171]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_6021,plain,
% 3.32/1.00      ( k1_relat_1(k2_funct_1(sK3)) = k1_xboole_0 ),
% 3.32/1.00      inference(demodulation,[status(thm)],[c_5999,c_3659]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_6938,plain,
% 3.32/1.00      ( k1_relat_1(k2_funct_1(k1_xboole_0)) = k1_xboole_0 ),
% 3.32/1.00      inference(light_normalisation,[status(thm)],[c_6021,c_6524]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_9257,plain,
% 3.32/1.00      ( k1_relset_1(k1_xboole_0,X0,k2_funct_1(k1_xboole_0)) = k1_xboole_0 ),
% 3.32/1.00      inference(light_normalisation,[status(thm)],[c_9245,c_6938]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_25,plain,
% 3.32/1.00      ( v1_funct_2(X0,k1_xboole_0,X1)
% 3.32/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.32/1.00      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 3.32/1.00      inference(cnf_transformation,[],[f101]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_818,plain,
% 3.32/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.32/1.00      | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.32/1.00      | ~ v1_funct_1(k2_funct_1(sK3))
% 3.32/1.00      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
% 3.32/1.00      | k2_funct_1(sK3) != X0
% 3.32/1.00      | sK1 != X1
% 3.32/1.00      | sK2 != k1_xboole_0 ),
% 3.32/1.00      inference(resolution_lifted,[status(thm)],[c_25,c_37]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_819,plain,
% 3.32/1.00      ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.32/1.00      | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
% 3.32/1.00      | ~ v1_funct_1(k2_funct_1(sK3))
% 3.32/1.00      | k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
% 3.32/1.00      | sK2 != k1_xboole_0 ),
% 3.32/1.00      inference(unflattening,[status(thm)],[c_818]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_1902,plain,
% 3.32/1.00      ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
% 3.32/1.00      | sK2 != k1_xboole_0
% 3.32/1.00      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.32/1.00      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top
% 3.32/1.00      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 3.32/1.00      inference(predicate_to_equality,[status(thm)],[c_819]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_2190,plain,
% 3.32/1.00      ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
% 3.32/1.00      | sK2 != k1_xboole_0
% 3.32/1.00      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.32/1.00      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.32/1.00      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 3.32/1.00      inference(demodulation,[status(thm)],[c_1902,c_5]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_2721,plain,
% 3.32/1.00      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.32/1.00      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.32/1.00      | sK2 != k1_xboole_0
% 3.32/1.00      | k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0 ),
% 3.32/1.00      inference(global_propositional_subsumption,
% 3.32/1.00                [status(thm)],
% 3.32/1.00                [c_2190,c_43,c_45,c_2325,c_2527]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_2722,plain,
% 3.32/1.00      ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
% 3.32/1.00      | sK2 != k1_xboole_0
% 3.32/1.00      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.32/1.00      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.32/1.00      inference(renaming,[status(thm)],[c_2721]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_6025,plain,
% 3.32/1.00      ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
% 3.32/1.00      | k1_xboole_0 != k1_xboole_0
% 3.32/1.00      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top
% 3.32/1.00      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.32/1.00      inference(demodulation,[status(thm)],[c_5999,c_2722]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_6074,plain,
% 3.32/1.00      ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
% 3.32/1.00      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top
% 3.32/1.00      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.32/1.00      inference(equality_resolution_simp,[status(thm)],[c_6025]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_6078,plain,
% 3.32/1.00      ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
% 3.32/1.00      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.32/1.00      inference(demodulation,[status(thm)],[c_6074,c_5]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_6146,plain,
% 3.32/1.00      ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0 ),
% 3.32/1.00      inference(backward_subsumption_resolution,
% 3.32/1.00                [status(thm)],
% 3.32/1.00                [c_6144,c_6078]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_9260,plain,
% 3.32/1.00      ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(k1_xboole_0)) != k1_xboole_0 ),
% 3.32/1.00      inference(light_normalisation,[status(thm)],[c_6146,c_6524]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_9357,plain,
% 3.32/1.00      ( k1_xboole_0 != k1_xboole_0 ),
% 3.32/1.00      inference(demodulation,[status(thm)],[c_9257,c_9260]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_125,plain,
% 3.32/1.00      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 3.32/1.00      inference(instantiation,[status(thm)],[c_5]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_6,plain,
% 3.32/1.00      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 3.32/1.00      | k1_xboole_0 = X1
% 3.32/1.00      | k1_xboole_0 = X0 ),
% 3.32/1.00      inference(cnf_transformation,[],[f55]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_124,plain,
% 3.32/1.00      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 3.32/1.00      | k1_xboole_0 = k1_xboole_0 ),
% 3.32/1.00      inference(instantiation,[status(thm)],[c_6]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(contradiction,plain,
% 3.32/1.00      ( $false ),
% 3.32/1.00      inference(minisat,[status(thm)],[c_9357,c_125,c_124]) ).
% 3.32/1.00  
% 3.32/1.00  
% 3.32/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.32/1.00  
% 3.32/1.00  ------                               Statistics
% 3.32/1.00  
% 3.32/1.00  ------ General
% 3.32/1.00  
% 3.32/1.00  abstr_ref_over_cycles:                  0
% 3.32/1.00  abstr_ref_under_cycles:                 0
% 3.32/1.00  gc_basic_clause_elim:                   0
% 3.32/1.00  forced_gc_time:                         0
% 3.32/1.00  parsing_time:                           0.011
% 3.32/1.00  unif_index_cands_time:                  0.
% 3.32/1.00  unif_index_add_time:                    0.
% 3.32/1.00  orderings_time:                         0.
% 3.32/1.00  out_proof_time:                         0.013
% 3.32/1.00  total_time:                             0.25
% 3.32/1.00  num_of_symbols:                         51
% 3.32/1.00  num_of_terms:                           6821
% 3.32/1.00  
% 3.32/1.00  ------ Preprocessing
% 3.32/1.00  
% 3.32/1.00  num_of_splits:                          0
% 3.32/1.00  num_of_split_atoms:                     0
% 3.32/1.00  num_of_reused_defs:                     0
% 3.32/1.00  num_eq_ax_congr_red:                    5
% 3.32/1.00  num_of_sem_filtered_clauses:            1
% 3.32/1.00  num_of_subtypes:                        0
% 3.32/1.00  monotx_restored_types:                  0
% 3.32/1.00  sat_num_of_epr_types:                   0
% 3.32/1.00  sat_num_of_non_cyclic_types:            0
% 3.32/1.00  sat_guarded_non_collapsed_types:        0
% 3.32/1.00  num_pure_diseq_elim:                    0
% 3.32/1.00  simp_replaced_by:                       0
% 3.32/1.00  res_preprocessed:                       160
% 3.32/1.00  prep_upred:                             0
% 3.32/1.00  prep_unflattend:                        68
% 3.32/1.00  smt_new_axioms:                         0
% 3.32/1.00  pred_elim_cands:                        7
% 3.32/1.00  pred_elim:                              3
% 3.32/1.00  pred_elim_cl:                           -7
% 3.32/1.00  pred_elim_cycles:                       4
% 3.32/1.00  merged_defs:                            6
% 3.32/1.00  merged_defs_ncl:                        0
% 3.32/1.00  bin_hyper_res:                          7
% 3.32/1.00  prep_cycles:                            3
% 3.32/1.00  pred_elim_time:                         0.013
% 3.32/1.00  splitting_time:                         0.
% 3.32/1.00  sem_filter_time:                        0.
% 3.32/1.00  monotx_time:                            0.001
% 3.32/1.00  subtype_inf_time:                       0.
% 3.32/1.00  
% 3.32/1.00  ------ Problem properties
% 3.32/1.00  
% 3.32/1.00  clauses:                                46
% 3.32/1.00  conjectures:                            3
% 3.32/1.00  epr:                                    7
% 3.32/1.00  horn:                                   37
% 3.32/1.00  ground:                                 19
% 3.32/1.00  unary:                                  13
% 3.32/1.00  binary:                                 8
% 3.32/1.00  lits:                                   129
% 3.32/1.00  lits_eq:                                51
% 3.32/1.00  fd_pure:                                0
% 3.32/1.00  fd_pseudo:                              0
% 3.32/1.00  fd_cond:                                5
% 3.32/1.00  fd_pseudo_cond:                         1
% 3.32/1.00  ac_symbols:                             0
% 3.32/1.00  
% 3.32/1.00  ------ Propositional Solver
% 3.32/1.00  
% 3.32/1.00  prop_solver_calls:                      24
% 3.32/1.00  prop_fast_solver_calls:                 1349
% 3.32/1.00  smt_solver_calls:                       0
% 3.32/1.00  smt_fast_solver_calls:                  0
% 3.32/1.00  prop_num_of_clauses:                    3322
% 3.32/1.00  prop_preprocess_simplified:             9493
% 3.32/1.00  prop_fo_subsumed:                       49
% 3.32/1.00  prop_solver_time:                       0.
% 3.32/1.00  smt_solver_time:                        0.
% 3.32/1.00  smt_fast_solver_time:                   0.
% 3.32/1.00  prop_fast_solver_time:                  0.
% 3.32/1.00  prop_unsat_core_time:                   0.
% 3.32/1.00  
% 3.32/1.00  ------ QBF
% 3.32/1.00  
% 3.32/1.00  qbf_q_res:                              0
% 3.32/1.00  qbf_num_tautologies:                    0
% 3.32/1.00  qbf_prep_cycles:                        0
% 3.32/1.00  
% 3.32/1.00  ------ BMC1
% 3.32/1.00  
% 3.32/1.00  bmc1_current_bound:                     -1
% 3.32/1.00  bmc1_last_solved_bound:                 -1
% 3.32/1.00  bmc1_unsat_core_size:                   -1
% 3.32/1.00  bmc1_unsat_core_parents_size:           -1
% 3.32/1.00  bmc1_merge_next_fun:                    0
% 3.32/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.32/1.00  
% 3.32/1.00  ------ Instantiation
% 3.32/1.00  
% 3.32/1.00  inst_num_of_clauses:                    1184
% 3.32/1.00  inst_num_in_passive:                    520
% 3.32/1.00  inst_num_in_active:                     502
% 3.32/1.00  inst_num_in_unprocessed:                163
% 3.32/1.00  inst_num_of_loops:                      620
% 3.32/1.00  inst_num_of_learning_restarts:          0
% 3.32/1.00  inst_num_moves_active_passive:          116
% 3.32/1.00  inst_lit_activity:                      0
% 3.32/1.00  inst_lit_activity_moves:                0
% 3.32/1.00  inst_num_tautologies:                   0
% 3.32/1.00  inst_num_prop_implied:                  0
% 3.32/1.00  inst_num_existing_simplified:           0
% 3.32/1.00  inst_num_eq_res_simplified:             0
% 3.32/1.00  inst_num_child_elim:                    0
% 3.32/1.00  inst_num_of_dismatching_blockings:      407
% 3.32/1.00  inst_num_of_non_proper_insts:           1073
% 3.32/1.00  inst_num_of_duplicates:                 0
% 3.32/1.00  inst_inst_num_from_inst_to_res:         0
% 3.32/1.00  inst_dismatching_checking_time:         0.
% 3.32/1.00  
% 3.32/1.00  ------ Resolution
% 3.32/1.00  
% 3.32/1.00  res_num_of_clauses:                     0
% 3.32/1.00  res_num_in_passive:                     0
% 3.32/1.00  res_num_in_active:                      0
% 3.32/1.00  res_num_of_loops:                       163
% 3.32/1.00  res_forward_subset_subsumed:            48
% 3.32/1.00  res_backward_subset_subsumed:           2
% 3.32/1.00  res_forward_subsumed:                   0
% 3.32/1.00  res_backward_subsumed:                  0
% 3.32/1.00  res_forward_subsumption_resolution:     7
% 3.32/1.00  res_backward_subsumption_resolution:    0
% 3.32/1.00  res_clause_to_clause_subsumption:       455
% 3.32/1.00  res_orphan_elimination:                 0
% 3.32/1.00  res_tautology_del:                      68
% 3.32/1.00  res_num_eq_res_simplified:              0
% 3.32/1.00  res_num_sel_changes:                    0
% 3.32/1.00  res_moves_from_active_to_pass:          0
% 3.32/1.00  
% 3.32/1.00  ------ Superposition
% 3.32/1.00  
% 3.32/1.00  sup_time_total:                         0.
% 3.32/1.00  sup_time_generating:                    0.
% 3.32/1.00  sup_time_sim_full:                      0.
% 3.32/1.00  sup_time_sim_immed:                     0.
% 3.32/1.00  
% 3.32/1.00  sup_num_of_clauses:                     131
% 3.32/1.00  sup_num_in_active:                      72
% 3.32/1.00  sup_num_in_passive:                     59
% 3.32/1.00  sup_num_of_loops:                       123
% 3.32/1.00  sup_fw_superposition:                   114
% 3.32/1.00  sup_bw_superposition:                   60
% 3.32/1.00  sup_immediate_simplified:               71
% 3.32/1.00  sup_given_eliminated:                   0
% 3.32/1.00  comparisons_done:                       0
% 3.32/1.00  comparisons_avoided:                    24
% 3.32/1.00  
% 3.32/1.00  ------ Simplifications
% 3.32/1.00  
% 3.32/1.00  
% 3.32/1.00  sim_fw_subset_subsumed:                 13
% 3.32/1.00  sim_bw_subset_subsumed:                 12
% 3.32/1.00  sim_fw_subsumed:                        12
% 3.32/1.00  sim_bw_subsumed:                        1
% 3.32/1.00  sim_fw_subsumption_res:                 2
% 3.32/1.00  sim_bw_subsumption_res:                 5
% 3.32/1.00  sim_tautology_del:                      4
% 3.32/1.00  sim_eq_tautology_del:                   19
% 3.32/1.00  sim_eq_res_simp:                        4
% 3.32/1.00  sim_fw_demodulated:                     27
% 3.32/1.00  sim_bw_demodulated:                     45
% 3.32/1.00  sim_light_normalised:                   61
% 3.32/1.00  sim_joinable_taut:                      0
% 3.32/1.00  sim_joinable_simp:                      0
% 3.32/1.00  sim_ac_normalised:                      0
% 3.32/1.00  sim_smt_subsumption:                    0
% 3.32/1.00  
%------------------------------------------------------------------------------
