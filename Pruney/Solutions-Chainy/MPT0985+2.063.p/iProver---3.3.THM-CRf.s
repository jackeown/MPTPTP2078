%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:02:32 EST 2020

% Result     : Theorem 3.19s
% Output     : CNFRefutation 3.19s
% Verified   : 
% Statistics : Number of formulae       :  180 (9105 expanded)
%              Number of clauses        :  115 (2747 expanded)
%              Number of leaves         :   16 (1801 expanded)
%              Depth                    :   26
%              Number of atoms          :  576 (50143 expanded)
%              Number of equality atoms :  272 (9850 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,axiom,(
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

fof(f40,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

fof(f50,plain,(
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
    inference(nnf_transformation,[],[f41])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f22,conjecture,(
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

fof(f23,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f46,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f47,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f46])).

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
   => ( ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
        | ~ v1_funct_1(k2_funct_1(sK3)) )
      & k2_relset_1(sK1,sK2,sK3) = sK2
      & v2_funct_1(sK3)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_2(sK3,sK1,sK2)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
      | ~ v1_funct_1(k2_funct_1(sK3)) )
    & k2_relset_1(sK1,sK2,sK3) = sK2
    & v2_funct_1(sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK3,sK1,sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f47,f53])).

fof(f92,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f54])).

fof(f93,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f54])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f11,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f35,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f34])).

fof(f69,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f94,plain,(
    v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f54])).

fof(f91,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f54])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f20,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f43,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f42])).

fof(f87,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f95,plain,(
    k2_relset_1(sK1,sK2,sK3) = sK2 ),
    inference(cnf_transformation,[],[f54])).

fof(f68,plain,(
    ! [X0] :
      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f33,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f67,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f66,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f86,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f96,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
    | ~ v1_funct_1(k2_funct_1(sK3)) ),
    inference(cnf_transformation,[],[f54])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f103,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f78])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f44])).

fof(f90,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f48])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f100,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f59])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f104,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f77])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_24,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_39,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_693,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK1 != X1
    | sK2 != X2
    | sK3 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_39])).

cnf(c_694,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k1_relset_1(sK1,sK2,sK3) = sK1
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_693])).

cnf(c_38,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_696,plain,
    ( k1_relset_1(sK1,sK2,sK3) = sK1
    | k1_xboole_0 = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_694,c_38])).

cnf(c_1410,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1417,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_4229,plain,
    ( k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1410,c_1417])).

cnf(c_4346,plain,
    ( k1_relat_1(sK3) = sK1
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_696,c_4229])).

cnf(c_13,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_37,negated_conjecture,
    ( v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_443,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_37])).

cnf(c_444,plain,
    ( ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_443])).

cnf(c_40,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_446,plain,
    ( ~ v1_relat_1(sK3)
    | k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_444,c_40])).

cnf(c_1406,plain,
    ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_446])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1764,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_1768,plain,
    ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1406,c_40,c_38,c_444,c_1764])).

cnf(c_29,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1411,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_4930,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK3)),k1_relat_1(sK3)))) = iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1768,c_1411])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1416,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3116,plain,
    ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1410,c_1416])).

cnf(c_36,negated_conjecture,
    ( k2_relset_1(sK1,sK2,sK3) = sK2 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_3128,plain,
    ( k2_relat_1(sK3) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_3116,c_36])).

cnf(c_14,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_429,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_37])).

cnf(c_430,plain,
    ( ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_429])).

cnf(c_432,plain,
    ( ~ v1_relat_1(sK3)
    | k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_430,c_40])).

cnf(c_1407,plain,
    ( k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_432])).

cnf(c_1772,plain,
    ( k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1407,c_40,c_38,c_430,c_1764])).

cnf(c_3146,plain,
    ( k1_relat_1(k2_funct_1(sK3)) = sK2 ),
    inference(demodulation,[status(thm)],[c_3128,c_1772])).

cnf(c_4949,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3)))) = iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4930,c_3146])).

cnf(c_41,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_43,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_1765,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1764])).

cnf(c_11,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_2130,plain,
    ( ~ v1_relat_1(sK3)
    | v1_funct_1(k2_funct_1(sK3))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_2131,plain,
    ( v1_relat_1(sK3) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2130])).

cnf(c_12,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_2140,plain,
    ( v1_relat_1(k2_funct_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_2141,plain,
    ( v1_relat_1(k2_funct_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2140])).

cnf(c_5555,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4949,c_41,c_43,c_1765,c_2131,c_2141])).

cnf(c_5561,plain,
    ( k1_relset_1(sK2,k1_relat_1(sK3),k2_funct_1(sK3)) = k1_relat_1(k2_funct_1(sK3)) ),
    inference(superposition,[status(thm)],[c_5555,c_1417])).

cnf(c_5570,plain,
    ( k1_relset_1(sK2,k1_relat_1(sK3),k2_funct_1(sK3)) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_5561,c_3146])).

cnf(c_5579,plain,
    ( k1_relset_1(sK2,sK1,k2_funct_1(sK3)) = sK2
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4346,c_5570])).

cnf(c_30,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_35,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
    | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK3)) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_704,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_funct_1(sK3))
    | k2_funct_1(sK3) != X0
    | k1_relat_1(X0) != sK2
    | k2_relat_1(X0) != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_35])).

cnf(c_705,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | k1_relat_1(k2_funct_1(sK3)) != sK2
    | k2_relat_1(k2_funct_1(sK3)) != sK1 ),
    inference(unflattening,[status(thm)],[c_704])).

cnf(c_717,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | k1_relat_1(k2_funct_1(sK3)) != sK2
    | k2_relat_1(k2_funct_1(sK3)) != sK1 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_705,c_15])).

cnf(c_1395,plain,
    ( k1_relat_1(k2_funct_1(sK3)) != sK2
    | k2_relat_1(k2_funct_1(sK3)) != sK1
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_717])).

cnf(c_2117,plain,
    ( k1_relat_1(sK3) != sK1
    | k2_relat_1(sK3) != sK2
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1395,c_1768,c_1772])).

cnf(c_3144,plain,
    ( k1_relat_1(sK3) != sK1
    | sK2 != sK2
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3128,c_2117])).

cnf(c_3156,plain,
    ( k1_relat_1(sK3) != sK1
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_3144])).

cnf(c_3456,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | k1_relat_1(sK3) != sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3156,c_41,c_43,c_1765,c_2117,c_2131,c_3128])).

cnf(c_3457,plain,
    ( k1_relat_1(sK3) != sK1
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(renaming,[status(thm)],[c_3456])).

cnf(c_4472,plain,
    ( sK2 = k1_xboole_0
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4346,c_3457])).

cnf(c_5560,plain,
    ( sK2 = k1_xboole_0
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4346,c_5555])).

cnf(c_5774,plain,
    ( sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5579,c_4472,c_5560])).

cnf(c_5779,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK3)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5774,c_5555])).

cnf(c_20,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f103])).

cnf(c_497,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | X2 != X0
    | k1_relat_1(X2) != X1
    | k2_relat_1(X2) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_30])).

cnf(c_498,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k1_xboole_0)))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = k1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_497])).

cnf(c_1,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_32,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_401,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | X1 != X2
    | k2_relat_1(X0) != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_32])).

cnf(c_402,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relat_1(X0) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_401])).

cnf(c_514,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = k1_relat_1(X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_498,c_402])).

cnf(c_1404,plain,
    ( k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = k1_relat_1(X0)
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_514])).

cnf(c_3632,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | sK2 != k1_xboole_0
    | sK3 = k1_xboole_0
    | v1_relat_1(sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3128,c_1404])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_831,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2006,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k1_relat_1(sK3))
    | k1_relat_1(sK3) != X0 ),
    inference(instantiation,[status(thm)],[c_831])).

cnf(c_2008,plain,
    ( v1_xboole_0(k1_relat_1(sK3))
    | ~ v1_xboole_0(k1_xboole_0)
    | k1_relat_1(sK3) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2006])).

cnf(c_2,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_2182,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(sK3)
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_2184,plain,
    ( ~ v1_xboole_0(sK3)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK3 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2182])).

cnf(c_2273,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))))
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_2096,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(sK3) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_3064,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))))
    | ~ v1_xboole_0(k1_relat_1(sK3))
    | v1_xboole_0(sK3) ),
    inference(instantiation,[status(thm)],[c_2096])).

cnf(c_3661,plain,
    ( ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | k1_relat_1(sK3) = k1_xboole_0
    | sK2 != k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3632])).

cnf(c_3893,plain,
    ( sK2 != k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3632,c_40,c_38,c_0,c_1764,c_2008,c_2184,c_2273,c_3064,c_3661])).

cnf(c_5790,plain,
    ( sK3 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5774,c_3893])).

cnf(c_5866,plain,
    ( sK3 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_5790])).

cnf(c_5945,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(k1_xboole_0)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5779,c_5866])).

cnf(c_4,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f100])).

cnf(c_5947,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5945,c_4])).

cnf(c_4231,plain,
    ( k1_relset_1(k1_xboole_0,X0,X1) = k1_relat_1(X1)
    | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4,c_1417])).

cnf(c_6418,plain,
    ( k1_relset_1(k1_xboole_0,X0,k2_funct_1(k1_xboole_0)) = k1_relat_1(k2_funct_1(k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_5947,c_4231])).

cnf(c_5795,plain,
    ( k1_relat_1(k2_funct_1(sK3)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5774,c_3146])).

cnf(c_5872,plain,
    ( k1_relat_1(k2_funct_1(k1_xboole_0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5866,c_5795])).

cnf(c_7935,plain,
    ( k1_relset_1(k1_xboole_0,X0,k2_funct_1(k1_xboole_0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_6418,c_5872])).

cnf(c_21,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f104])).

cnf(c_594,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
    | k2_funct_1(sK3) != X0
    | sK1 != X1
    | sK2 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_35])).

cnf(c_595,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
    | sK2 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_594])).

cnf(c_1400,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_595])).

cnf(c_1641,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1400,c_4])).

cnf(c_2228,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | sK2 != k1_xboole_0
    | k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1641,c_41,c_43,c_1765,c_2131])).

cnf(c_2229,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2228])).

cnf(c_5797,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5774,c_2229])).

cnf(c_5834,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_5797])).

cnf(c_5838,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5834,c_4])).

cnf(c_5874,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(k1_xboole_0)) != k1_xboole_0
    | m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5866,c_5838])).

cnf(c_5950,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(k1_xboole_0)) != k1_xboole_0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_5947,c_5874])).

cnf(c_7938,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7935,c_5950])).

cnf(c_120,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_5,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_119,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7938,c_120,c_119])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:17:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.19/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.19/0.99  
% 3.19/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.19/0.99  
% 3.19/0.99  ------  iProver source info
% 3.19/0.99  
% 3.19/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.19/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.19/0.99  git: non_committed_changes: false
% 3.19/0.99  git: last_make_outside_of_git: false
% 3.19/0.99  
% 3.19/0.99  ------ 
% 3.19/0.99  
% 3.19/0.99  ------ Input Options
% 3.19/0.99  
% 3.19/0.99  --out_options                           all
% 3.19/0.99  --tptp_safe_out                         true
% 3.19/0.99  --problem_path                          ""
% 3.19/0.99  --include_path                          ""
% 3.19/0.99  --clausifier                            res/vclausify_rel
% 3.19/0.99  --clausifier_options                    --mode clausify
% 3.19/0.99  --stdin                                 false
% 3.19/0.99  --stats_out                             all
% 3.19/0.99  
% 3.19/0.99  ------ General Options
% 3.19/0.99  
% 3.19/0.99  --fof                                   false
% 3.19/0.99  --time_out_real                         305.
% 3.19/0.99  --time_out_virtual                      -1.
% 3.19/0.99  --symbol_type_check                     false
% 3.19/0.99  --clausify_out                          false
% 3.19/0.99  --sig_cnt_out                           false
% 3.19/0.99  --trig_cnt_out                          false
% 3.19/0.99  --trig_cnt_out_tolerance                1.
% 3.19/0.99  --trig_cnt_out_sk_spl                   false
% 3.19/0.99  --abstr_cl_out                          false
% 3.19/0.99  
% 3.19/0.99  ------ Global Options
% 3.19/0.99  
% 3.19/0.99  --schedule                              default
% 3.19/0.99  --add_important_lit                     false
% 3.19/0.99  --prop_solver_per_cl                    1000
% 3.19/0.99  --min_unsat_core                        false
% 3.19/0.99  --soft_assumptions                      false
% 3.19/0.99  --soft_lemma_size                       3
% 3.19/0.99  --prop_impl_unit_size                   0
% 3.19/0.99  --prop_impl_unit                        []
% 3.19/0.99  --share_sel_clauses                     true
% 3.19/0.99  --reset_solvers                         false
% 3.19/0.99  --bc_imp_inh                            [conj_cone]
% 3.19/0.99  --conj_cone_tolerance                   3.
% 3.19/0.99  --extra_neg_conj                        none
% 3.19/0.99  --large_theory_mode                     true
% 3.19/0.99  --prolific_symb_bound                   200
% 3.19/0.99  --lt_threshold                          2000
% 3.19/0.99  --clause_weak_htbl                      true
% 3.19/0.99  --gc_record_bc_elim                     false
% 3.19/0.99  
% 3.19/0.99  ------ Preprocessing Options
% 3.19/0.99  
% 3.19/0.99  --preprocessing_flag                    true
% 3.19/0.99  --time_out_prep_mult                    0.1
% 3.19/0.99  --splitting_mode                        input
% 3.19/0.99  --splitting_grd                         true
% 3.19/0.99  --splitting_cvd                         false
% 3.19/0.99  --splitting_cvd_svl                     false
% 3.19/0.99  --splitting_nvd                         32
% 3.19/0.99  --sub_typing                            true
% 3.19/0.99  --prep_gs_sim                           true
% 3.19/0.99  --prep_unflatten                        true
% 3.19/0.99  --prep_res_sim                          true
% 3.19/0.99  --prep_upred                            true
% 3.19/0.99  --prep_sem_filter                       exhaustive
% 3.19/0.99  --prep_sem_filter_out                   false
% 3.19/0.99  --pred_elim                             true
% 3.19/0.99  --res_sim_input                         true
% 3.19/0.99  --eq_ax_congr_red                       true
% 3.19/0.99  --pure_diseq_elim                       true
% 3.19/0.99  --brand_transform                       false
% 3.19/0.99  --non_eq_to_eq                          false
% 3.19/0.99  --prep_def_merge                        true
% 3.19/0.99  --prep_def_merge_prop_impl              false
% 3.19/0.99  --prep_def_merge_mbd                    true
% 3.19/0.99  --prep_def_merge_tr_red                 false
% 3.19/0.99  --prep_def_merge_tr_cl                  false
% 3.19/0.99  --smt_preprocessing                     true
% 3.19/0.99  --smt_ac_axioms                         fast
% 3.19/0.99  --preprocessed_out                      false
% 3.19/0.99  --preprocessed_stats                    false
% 3.19/0.99  
% 3.19/0.99  ------ Abstraction refinement Options
% 3.19/0.99  
% 3.19/0.99  --abstr_ref                             []
% 3.19/0.99  --abstr_ref_prep                        false
% 3.19/0.99  --abstr_ref_until_sat                   false
% 3.19/0.99  --abstr_ref_sig_restrict                funpre
% 3.19/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.19/0.99  --abstr_ref_under                       []
% 3.19/0.99  
% 3.19/0.99  ------ SAT Options
% 3.19/0.99  
% 3.19/0.99  --sat_mode                              false
% 3.19/0.99  --sat_fm_restart_options                ""
% 3.19/0.99  --sat_gr_def                            false
% 3.19/0.99  --sat_epr_types                         true
% 3.19/0.99  --sat_non_cyclic_types                  false
% 3.19/0.99  --sat_finite_models                     false
% 3.19/0.99  --sat_fm_lemmas                         false
% 3.19/0.99  --sat_fm_prep                           false
% 3.19/0.99  --sat_fm_uc_incr                        true
% 3.19/0.99  --sat_out_model                         small
% 3.19/0.99  --sat_out_clauses                       false
% 3.19/0.99  
% 3.19/0.99  ------ QBF Options
% 3.19/0.99  
% 3.19/0.99  --qbf_mode                              false
% 3.19/0.99  --qbf_elim_univ                         false
% 3.19/0.99  --qbf_dom_inst                          none
% 3.19/0.99  --qbf_dom_pre_inst                      false
% 3.19/0.99  --qbf_sk_in                             false
% 3.19/0.99  --qbf_pred_elim                         true
% 3.19/0.99  --qbf_split                             512
% 3.19/0.99  
% 3.19/0.99  ------ BMC1 Options
% 3.19/0.99  
% 3.19/0.99  --bmc1_incremental                      false
% 3.19/0.99  --bmc1_axioms                           reachable_all
% 3.19/0.99  --bmc1_min_bound                        0
% 3.19/0.99  --bmc1_max_bound                        -1
% 3.19/0.99  --bmc1_max_bound_default                -1
% 3.19/0.99  --bmc1_symbol_reachability              true
% 3.19/0.99  --bmc1_property_lemmas                  false
% 3.19/0.99  --bmc1_k_induction                      false
% 3.19/0.99  --bmc1_non_equiv_states                 false
% 3.19/0.99  --bmc1_deadlock                         false
% 3.19/0.99  --bmc1_ucm                              false
% 3.19/0.99  --bmc1_add_unsat_core                   none
% 3.19/0.99  --bmc1_unsat_core_children              false
% 3.19/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.19/0.99  --bmc1_out_stat                         full
% 3.19/0.99  --bmc1_ground_init                      false
% 3.19/0.99  --bmc1_pre_inst_next_state              false
% 3.19/0.99  --bmc1_pre_inst_state                   false
% 3.19/0.99  --bmc1_pre_inst_reach_state             false
% 3.19/0.99  --bmc1_out_unsat_core                   false
% 3.19/0.99  --bmc1_aig_witness_out                  false
% 3.19/0.99  --bmc1_verbose                          false
% 3.19/0.99  --bmc1_dump_clauses_tptp                false
% 3.19/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.19/0.99  --bmc1_dump_file                        -
% 3.19/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.19/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.19/0.99  --bmc1_ucm_extend_mode                  1
% 3.19/0.99  --bmc1_ucm_init_mode                    2
% 3.19/0.99  --bmc1_ucm_cone_mode                    none
% 3.19/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.19/0.99  --bmc1_ucm_relax_model                  4
% 3.19/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.19/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.19/0.99  --bmc1_ucm_layered_model                none
% 3.19/0.99  --bmc1_ucm_max_lemma_size               10
% 3.19/0.99  
% 3.19/0.99  ------ AIG Options
% 3.19/0.99  
% 3.19/0.99  --aig_mode                              false
% 3.19/0.99  
% 3.19/0.99  ------ Instantiation Options
% 3.19/0.99  
% 3.19/0.99  --instantiation_flag                    true
% 3.19/0.99  --inst_sos_flag                         false
% 3.19/0.99  --inst_sos_phase                        true
% 3.19/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.19/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.19/0.99  --inst_lit_sel_side                     num_symb
% 3.19/0.99  --inst_solver_per_active                1400
% 3.19/0.99  --inst_solver_calls_frac                1.
% 3.19/0.99  --inst_passive_queue_type               priority_queues
% 3.19/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.19/0.99  --inst_passive_queues_freq              [25;2]
% 3.19/0.99  --inst_dismatching                      true
% 3.19/0.99  --inst_eager_unprocessed_to_passive     true
% 3.19/0.99  --inst_prop_sim_given                   true
% 3.19/0.99  --inst_prop_sim_new                     false
% 3.19/0.99  --inst_subs_new                         false
% 3.19/0.99  --inst_eq_res_simp                      false
% 3.19/0.99  --inst_subs_given                       false
% 3.19/0.99  --inst_orphan_elimination               true
% 3.19/0.99  --inst_learning_loop_flag               true
% 3.19/0.99  --inst_learning_start                   3000
% 3.19/0.99  --inst_learning_factor                  2
% 3.19/0.99  --inst_start_prop_sim_after_learn       3
% 3.19/0.99  --inst_sel_renew                        solver
% 3.19/0.99  --inst_lit_activity_flag                true
% 3.19/0.99  --inst_restr_to_given                   false
% 3.19/0.99  --inst_activity_threshold               500
% 3.19/0.99  --inst_out_proof                        true
% 3.19/0.99  
% 3.19/0.99  ------ Resolution Options
% 3.19/0.99  
% 3.19/0.99  --resolution_flag                       true
% 3.19/0.99  --res_lit_sel                           adaptive
% 3.19/0.99  --res_lit_sel_side                      none
% 3.19/0.99  --res_ordering                          kbo
% 3.19/0.99  --res_to_prop_solver                    active
% 3.19/0.99  --res_prop_simpl_new                    false
% 3.19/0.99  --res_prop_simpl_given                  true
% 3.19/0.99  --res_passive_queue_type                priority_queues
% 3.19/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.19/0.99  --res_passive_queues_freq               [15;5]
% 3.19/0.99  --res_forward_subs                      full
% 3.19/0.99  --res_backward_subs                     full
% 3.19/0.99  --res_forward_subs_resolution           true
% 3.19/0.99  --res_backward_subs_resolution          true
% 3.19/0.99  --res_orphan_elimination                true
% 3.19/0.99  --res_time_limit                        2.
% 3.19/0.99  --res_out_proof                         true
% 3.19/0.99  
% 3.19/0.99  ------ Superposition Options
% 3.19/0.99  
% 3.19/0.99  --superposition_flag                    true
% 3.19/0.99  --sup_passive_queue_type                priority_queues
% 3.19/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.19/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.19/0.99  --demod_completeness_check              fast
% 3.19/0.99  --demod_use_ground                      true
% 3.19/0.99  --sup_to_prop_solver                    passive
% 3.19/0.99  --sup_prop_simpl_new                    true
% 3.19/0.99  --sup_prop_simpl_given                  true
% 3.19/0.99  --sup_fun_splitting                     false
% 3.19/0.99  --sup_smt_interval                      50000
% 3.19/0.99  
% 3.19/0.99  ------ Superposition Simplification Setup
% 3.19/0.99  
% 3.19/0.99  --sup_indices_passive                   []
% 3.19/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.19/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.19/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.19/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.19/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.19/0.99  --sup_full_bw                           [BwDemod]
% 3.19/0.99  --sup_immed_triv                        [TrivRules]
% 3.19/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.19/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.19/0.99  --sup_immed_bw_main                     []
% 3.19/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.19/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.19/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.19/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.19/0.99  
% 3.19/0.99  ------ Combination Options
% 3.19/0.99  
% 3.19/0.99  --comb_res_mult                         3
% 3.19/0.99  --comb_sup_mult                         2
% 3.19/0.99  --comb_inst_mult                        10
% 3.19/0.99  
% 3.19/0.99  ------ Debug Options
% 3.19/0.99  
% 3.19/0.99  --dbg_backtrace                         false
% 3.19/0.99  --dbg_dump_prop_clauses                 false
% 3.19/0.99  --dbg_dump_prop_clauses_file            -
% 3.19/0.99  --dbg_out_stat                          false
% 3.19/0.99  ------ Parsing...
% 3.19/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.19/0.99  
% 3.19/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e 
% 3.19/0.99  
% 3.19/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.19/0.99  
% 3.19/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.19/0.99  ------ Proving...
% 3.19/0.99  ------ Problem Properties 
% 3.19/0.99  
% 3.19/0.99  
% 3.19/0.99  clauses                                 41
% 3.19/0.99  conjectures                             3
% 3.19/0.99  EPR                                     3
% 3.19/0.99  Horn                                    35
% 3.19/0.99  unary                                   13
% 3.19/0.99  binary                                  6
% 3.19/0.99  lits                                    110
% 3.19/0.99  lits eq                                 47
% 3.19/0.99  fd_pure                                 0
% 3.19/0.99  fd_pseudo                               0
% 3.19/0.99  fd_cond                                 3
% 3.19/0.99  fd_pseudo_cond                          1
% 3.19/0.99  AC symbols                              0
% 3.19/0.99  
% 3.19/0.99  ------ Schedule dynamic 5 is on 
% 3.19/0.99  
% 3.19/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.19/0.99  
% 3.19/0.99  
% 3.19/0.99  ------ 
% 3.19/0.99  Current options:
% 3.19/0.99  ------ 
% 3.19/0.99  
% 3.19/0.99  ------ Input Options
% 3.19/0.99  
% 3.19/0.99  --out_options                           all
% 3.19/0.99  --tptp_safe_out                         true
% 3.19/0.99  --problem_path                          ""
% 3.19/0.99  --include_path                          ""
% 3.19/0.99  --clausifier                            res/vclausify_rel
% 3.19/0.99  --clausifier_options                    --mode clausify
% 3.19/0.99  --stdin                                 false
% 3.19/0.99  --stats_out                             all
% 3.19/0.99  
% 3.19/0.99  ------ General Options
% 3.19/0.99  
% 3.19/0.99  --fof                                   false
% 3.19/0.99  --time_out_real                         305.
% 3.19/0.99  --time_out_virtual                      -1.
% 3.19/0.99  --symbol_type_check                     false
% 3.19/0.99  --clausify_out                          false
% 3.19/0.99  --sig_cnt_out                           false
% 3.19/0.99  --trig_cnt_out                          false
% 3.19/0.99  --trig_cnt_out_tolerance                1.
% 3.19/0.99  --trig_cnt_out_sk_spl                   false
% 3.19/0.99  --abstr_cl_out                          false
% 3.19/0.99  
% 3.19/0.99  ------ Global Options
% 3.19/0.99  
% 3.19/0.99  --schedule                              default
% 3.19/0.99  --add_important_lit                     false
% 3.19/0.99  --prop_solver_per_cl                    1000
% 3.19/0.99  --min_unsat_core                        false
% 3.19/0.99  --soft_assumptions                      false
% 3.19/0.99  --soft_lemma_size                       3
% 3.19/0.99  --prop_impl_unit_size                   0
% 3.19/0.99  --prop_impl_unit                        []
% 3.19/0.99  --share_sel_clauses                     true
% 3.19/0.99  --reset_solvers                         false
% 3.19/0.99  --bc_imp_inh                            [conj_cone]
% 3.19/0.99  --conj_cone_tolerance                   3.
% 3.19/0.99  --extra_neg_conj                        none
% 3.19/0.99  --large_theory_mode                     true
% 3.19/0.99  --prolific_symb_bound                   200
% 3.19/0.99  --lt_threshold                          2000
% 3.19/0.99  --clause_weak_htbl                      true
% 3.19/0.99  --gc_record_bc_elim                     false
% 3.19/0.99  
% 3.19/0.99  ------ Preprocessing Options
% 3.19/0.99  
% 3.19/0.99  --preprocessing_flag                    true
% 3.19/0.99  --time_out_prep_mult                    0.1
% 3.19/0.99  --splitting_mode                        input
% 3.19/0.99  --splitting_grd                         true
% 3.19/0.99  --splitting_cvd                         false
% 3.19/0.99  --splitting_cvd_svl                     false
% 3.19/0.99  --splitting_nvd                         32
% 3.19/0.99  --sub_typing                            true
% 3.19/0.99  --prep_gs_sim                           true
% 3.19/0.99  --prep_unflatten                        true
% 3.19/0.99  --prep_res_sim                          true
% 3.19/0.99  --prep_upred                            true
% 3.19/0.99  --prep_sem_filter                       exhaustive
% 3.19/0.99  --prep_sem_filter_out                   false
% 3.19/0.99  --pred_elim                             true
% 3.19/0.99  --res_sim_input                         true
% 3.19/0.99  --eq_ax_congr_red                       true
% 3.19/0.99  --pure_diseq_elim                       true
% 3.19/0.99  --brand_transform                       false
% 3.19/0.99  --non_eq_to_eq                          false
% 3.19/0.99  --prep_def_merge                        true
% 3.19/0.99  --prep_def_merge_prop_impl              false
% 3.19/0.99  --prep_def_merge_mbd                    true
% 3.19/0.99  --prep_def_merge_tr_red                 false
% 3.19/0.99  --prep_def_merge_tr_cl                  false
% 3.19/0.99  --smt_preprocessing                     true
% 3.19/0.99  --smt_ac_axioms                         fast
% 3.19/0.99  --preprocessed_out                      false
% 3.19/0.99  --preprocessed_stats                    false
% 3.19/0.99  
% 3.19/0.99  ------ Abstraction refinement Options
% 3.19/0.99  
% 3.19/0.99  --abstr_ref                             []
% 3.19/0.99  --abstr_ref_prep                        false
% 3.19/0.99  --abstr_ref_until_sat                   false
% 3.19/0.99  --abstr_ref_sig_restrict                funpre
% 3.19/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.19/0.99  --abstr_ref_under                       []
% 3.19/0.99  
% 3.19/0.99  ------ SAT Options
% 3.19/0.99  
% 3.19/0.99  --sat_mode                              false
% 3.19/0.99  --sat_fm_restart_options                ""
% 3.19/0.99  --sat_gr_def                            false
% 3.19/0.99  --sat_epr_types                         true
% 3.19/0.99  --sat_non_cyclic_types                  false
% 3.19/0.99  --sat_finite_models                     false
% 3.19/0.99  --sat_fm_lemmas                         false
% 3.19/0.99  --sat_fm_prep                           false
% 3.19/0.99  --sat_fm_uc_incr                        true
% 3.19/0.99  --sat_out_model                         small
% 3.19/0.99  --sat_out_clauses                       false
% 3.19/0.99  
% 3.19/0.99  ------ QBF Options
% 3.19/0.99  
% 3.19/0.99  --qbf_mode                              false
% 3.19/0.99  --qbf_elim_univ                         false
% 3.19/0.99  --qbf_dom_inst                          none
% 3.19/0.99  --qbf_dom_pre_inst                      false
% 3.19/0.99  --qbf_sk_in                             false
% 3.19/0.99  --qbf_pred_elim                         true
% 3.19/0.99  --qbf_split                             512
% 3.19/0.99  
% 3.19/0.99  ------ BMC1 Options
% 3.19/0.99  
% 3.19/0.99  --bmc1_incremental                      false
% 3.19/0.99  --bmc1_axioms                           reachable_all
% 3.19/0.99  --bmc1_min_bound                        0
% 3.19/0.99  --bmc1_max_bound                        -1
% 3.19/0.99  --bmc1_max_bound_default                -1
% 3.19/0.99  --bmc1_symbol_reachability              true
% 3.19/0.99  --bmc1_property_lemmas                  false
% 3.19/0.99  --bmc1_k_induction                      false
% 3.19/0.99  --bmc1_non_equiv_states                 false
% 3.19/0.99  --bmc1_deadlock                         false
% 3.19/0.99  --bmc1_ucm                              false
% 3.19/0.99  --bmc1_add_unsat_core                   none
% 3.19/0.99  --bmc1_unsat_core_children              false
% 3.19/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.19/0.99  --bmc1_out_stat                         full
% 3.19/0.99  --bmc1_ground_init                      false
% 3.19/0.99  --bmc1_pre_inst_next_state              false
% 3.19/0.99  --bmc1_pre_inst_state                   false
% 3.19/0.99  --bmc1_pre_inst_reach_state             false
% 3.19/0.99  --bmc1_out_unsat_core                   false
% 3.19/0.99  --bmc1_aig_witness_out                  false
% 3.19/0.99  --bmc1_verbose                          false
% 3.19/0.99  --bmc1_dump_clauses_tptp                false
% 3.19/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.19/0.99  --bmc1_dump_file                        -
% 3.19/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.19/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.19/0.99  --bmc1_ucm_extend_mode                  1
% 3.19/0.99  --bmc1_ucm_init_mode                    2
% 3.19/0.99  --bmc1_ucm_cone_mode                    none
% 3.19/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.19/0.99  --bmc1_ucm_relax_model                  4
% 3.19/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.19/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.19/0.99  --bmc1_ucm_layered_model                none
% 3.19/0.99  --bmc1_ucm_max_lemma_size               10
% 3.19/0.99  
% 3.19/0.99  ------ AIG Options
% 3.19/0.99  
% 3.19/0.99  --aig_mode                              false
% 3.19/0.99  
% 3.19/0.99  ------ Instantiation Options
% 3.19/0.99  
% 3.19/0.99  --instantiation_flag                    true
% 3.19/0.99  --inst_sos_flag                         false
% 3.19/0.99  --inst_sos_phase                        true
% 3.19/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.19/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.19/0.99  --inst_lit_sel_side                     none
% 3.19/0.99  --inst_solver_per_active                1400
% 3.19/0.99  --inst_solver_calls_frac                1.
% 3.19/0.99  --inst_passive_queue_type               priority_queues
% 3.19/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.19/0.99  --inst_passive_queues_freq              [25;2]
% 3.19/0.99  --inst_dismatching                      true
% 3.19/0.99  --inst_eager_unprocessed_to_passive     true
% 3.19/0.99  --inst_prop_sim_given                   true
% 3.19/0.99  --inst_prop_sim_new                     false
% 3.19/0.99  --inst_subs_new                         false
% 3.19/0.99  --inst_eq_res_simp                      false
% 3.19/0.99  --inst_subs_given                       false
% 3.19/0.99  --inst_orphan_elimination               true
% 3.19/0.99  --inst_learning_loop_flag               true
% 3.19/0.99  --inst_learning_start                   3000
% 3.19/0.99  --inst_learning_factor                  2
% 3.19/0.99  --inst_start_prop_sim_after_learn       3
% 3.19/0.99  --inst_sel_renew                        solver
% 3.19/0.99  --inst_lit_activity_flag                true
% 3.19/0.99  --inst_restr_to_given                   false
% 3.19/0.99  --inst_activity_threshold               500
% 3.19/0.99  --inst_out_proof                        true
% 3.19/0.99  
% 3.19/0.99  ------ Resolution Options
% 3.19/0.99  
% 3.19/0.99  --resolution_flag                       false
% 3.19/0.99  --res_lit_sel                           adaptive
% 3.19/0.99  --res_lit_sel_side                      none
% 3.19/0.99  --res_ordering                          kbo
% 3.19/0.99  --res_to_prop_solver                    active
% 3.19/0.99  --res_prop_simpl_new                    false
% 3.19/0.99  --res_prop_simpl_given                  true
% 3.19/0.99  --res_passive_queue_type                priority_queues
% 3.19/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.19/0.99  --res_passive_queues_freq               [15;5]
% 3.19/0.99  --res_forward_subs                      full
% 3.19/0.99  --res_backward_subs                     full
% 3.19/0.99  --res_forward_subs_resolution           true
% 3.19/0.99  --res_backward_subs_resolution          true
% 3.19/0.99  --res_orphan_elimination                true
% 3.19/0.99  --res_time_limit                        2.
% 3.19/0.99  --res_out_proof                         true
% 3.19/0.99  
% 3.19/0.99  ------ Superposition Options
% 3.19/0.99  
% 3.19/0.99  --superposition_flag                    true
% 3.19/0.99  --sup_passive_queue_type                priority_queues
% 3.19/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.19/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.19/0.99  --demod_completeness_check              fast
% 3.19/0.99  --demod_use_ground                      true
% 3.19/0.99  --sup_to_prop_solver                    passive
% 3.19/0.99  --sup_prop_simpl_new                    true
% 3.19/0.99  --sup_prop_simpl_given                  true
% 3.19/0.99  --sup_fun_splitting                     false
% 3.19/0.99  --sup_smt_interval                      50000
% 3.19/0.99  
% 3.19/0.99  ------ Superposition Simplification Setup
% 3.19/0.99  
% 3.19/0.99  --sup_indices_passive                   []
% 3.19/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.19/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.19/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.19/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.19/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.19/0.99  --sup_full_bw                           [BwDemod]
% 3.19/0.99  --sup_immed_triv                        [TrivRules]
% 3.19/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.19/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.19/0.99  --sup_immed_bw_main                     []
% 3.19/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.19/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.19/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.19/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.19/0.99  
% 3.19/0.99  ------ Combination Options
% 3.19/0.99  
% 3.19/0.99  --comb_res_mult                         3
% 3.19/0.99  --comb_sup_mult                         2
% 3.19/0.99  --comb_inst_mult                        10
% 3.19/0.99  
% 3.19/0.99  ------ Debug Options
% 3.19/0.99  
% 3.19/0.99  --dbg_backtrace                         false
% 3.19/0.99  --dbg_dump_prop_clauses                 false
% 3.19/0.99  --dbg_dump_prop_clauses_file            -
% 3.19/0.99  --dbg_out_stat                          false
% 3.19/0.99  
% 3.19/0.99  
% 3.19/0.99  
% 3.19/0.99  
% 3.19/0.99  ------ Proving...
% 3.19/0.99  
% 3.19/0.99  
% 3.19/0.99  % SZS status Theorem for theBenchmark.p
% 3.19/0.99  
% 3.19/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.19/0.99  
% 3.19/0.99  fof(f16,axiom,(
% 3.19/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.19/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.19/0.99  
% 3.19/0.99  fof(f40,plain,(
% 3.19/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.19/0.99    inference(ennf_transformation,[],[f16])).
% 3.19/0.99  
% 3.19/0.99  fof(f41,plain,(
% 3.19/0.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.19/0.99    inference(flattening,[],[f40])).
% 3.19/0.99  
% 3.19/0.99  fof(f50,plain,(
% 3.19/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.19/0.99    inference(nnf_transformation,[],[f41])).
% 3.19/0.99  
% 3.19/0.99  fof(f74,plain,(
% 3.19/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.19/0.99    inference(cnf_transformation,[],[f50])).
% 3.19/0.99  
% 3.19/0.99  fof(f22,conjecture,(
% 3.19/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 3.19/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.19/0.99  
% 3.19/0.99  fof(f23,negated_conjecture,(
% 3.19/0.99    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 3.19/0.99    inference(negated_conjecture,[],[f22])).
% 3.19/0.99  
% 3.19/0.99  fof(f46,plain,(
% 3.19/0.99    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.19/0.99    inference(ennf_transformation,[],[f23])).
% 3.19/0.99  
% 3.19/0.99  fof(f47,plain,(
% 3.19/0.99    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 3.19/0.99    inference(flattening,[],[f46])).
% 3.19/0.99  
% 3.19/0.99  fof(f53,plain,(
% 3.19/0.99    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))) & k2_relset_1(sK1,sK2,sK3) = sK2 & v2_funct_1(sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3))),
% 3.19/0.99    introduced(choice_axiom,[])).
% 3.19/0.99  
% 3.19/0.99  fof(f54,plain,(
% 3.19/0.99    (~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))) & k2_relset_1(sK1,sK2,sK3) = sK2 & v2_funct_1(sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)),
% 3.19/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f47,f53])).
% 3.19/0.99  
% 3.19/0.99  fof(f92,plain,(
% 3.19/0.99    v1_funct_2(sK3,sK1,sK2)),
% 3.19/0.99    inference(cnf_transformation,[],[f54])).
% 3.19/0.99  
% 3.19/0.99  fof(f93,plain,(
% 3.19/0.99    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 3.19/0.99    inference(cnf_transformation,[],[f54])).
% 3.19/0.99  
% 3.19/0.99  fof(f14,axiom,(
% 3.19/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.19/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.19/0.99  
% 3.19/0.99  fof(f38,plain,(
% 3.19/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.19/0.99    inference(ennf_transformation,[],[f14])).
% 3.19/0.99  
% 3.19/0.99  fof(f72,plain,(
% 3.19/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.19/0.99    inference(cnf_transformation,[],[f38])).
% 3.19/0.99  
% 3.19/0.99  fof(f11,axiom,(
% 3.19/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0))))),
% 3.19/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.19/0.99  
% 3.19/0.99  fof(f34,plain,(
% 3.19/0.99    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.19/0.99    inference(ennf_transformation,[],[f11])).
% 3.19/0.99  
% 3.19/0.99  fof(f35,plain,(
% 3.19/0.99    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.19/0.99    inference(flattening,[],[f34])).
% 3.19/0.99  
% 3.19/0.99  fof(f69,plain,(
% 3.19/0.99    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.19/0.99    inference(cnf_transformation,[],[f35])).
% 3.19/0.99  
% 3.19/0.99  fof(f94,plain,(
% 3.19/0.99    v2_funct_1(sK3)),
% 3.19/0.99    inference(cnf_transformation,[],[f54])).
% 3.19/0.99  
% 3.19/0.99  fof(f91,plain,(
% 3.19/0.99    v1_funct_1(sK3)),
% 3.19/0.99    inference(cnf_transformation,[],[f54])).
% 3.19/0.99  
% 3.19/0.99  fof(f12,axiom,(
% 3.19/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.19/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.19/0.99  
% 3.19/0.99  fof(f36,plain,(
% 3.19/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.19/0.99    inference(ennf_transformation,[],[f12])).
% 3.19/0.99  
% 3.19/0.99  fof(f70,plain,(
% 3.19/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.19/0.99    inference(cnf_transformation,[],[f36])).
% 3.19/0.99  
% 3.19/0.99  fof(f20,axiom,(
% 3.19/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 3.19/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.19/0.99  
% 3.19/0.99  fof(f42,plain,(
% 3.19/0.99    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.19/0.99    inference(ennf_transformation,[],[f20])).
% 3.19/0.99  
% 3.19/0.99  fof(f43,plain,(
% 3.19/0.99    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.19/0.99    inference(flattening,[],[f42])).
% 3.19/0.99  
% 3.19/0.99  fof(f87,plain,(
% 3.19/0.99    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.19/0.99    inference(cnf_transformation,[],[f43])).
% 3.19/0.99  
% 3.19/0.99  fof(f15,axiom,(
% 3.19/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.19/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.19/0.99  
% 3.19/0.99  fof(f39,plain,(
% 3.19/0.99    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.19/0.99    inference(ennf_transformation,[],[f15])).
% 3.19/0.99  
% 3.19/0.99  fof(f73,plain,(
% 3.19/0.99    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.19/0.99    inference(cnf_transformation,[],[f39])).
% 3.19/0.99  
% 3.19/0.99  fof(f95,plain,(
% 3.19/0.99    k2_relset_1(sK1,sK2,sK3) = sK2),
% 3.19/0.99    inference(cnf_transformation,[],[f54])).
% 3.19/0.99  
% 3.19/0.99  fof(f68,plain,(
% 3.19/0.99    ( ! [X0] : (k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.19/0.99    inference(cnf_transformation,[],[f35])).
% 3.19/0.99  
% 3.19/0.99  fof(f10,axiom,(
% 3.19/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 3.19/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.19/0.99  
% 3.19/0.99  fof(f32,plain,(
% 3.19/0.99    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.19/0.99    inference(ennf_transformation,[],[f10])).
% 3.19/0.99  
% 3.19/0.99  fof(f33,plain,(
% 3.19/0.99    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.19/0.99    inference(flattening,[],[f32])).
% 3.19/0.99  
% 3.19/0.99  fof(f67,plain,(
% 3.19/0.99    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.19/0.99    inference(cnf_transformation,[],[f33])).
% 3.19/0.99  
% 3.19/0.99  fof(f66,plain,(
% 3.19/0.99    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.19/0.99    inference(cnf_transformation,[],[f33])).
% 3.19/0.99  
% 3.19/0.99  fof(f86,plain,(
% 3.19/0.99    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.19/0.99    inference(cnf_transformation,[],[f43])).
% 3.19/0.99  
% 3.19/0.99  fof(f96,plain,(
% 3.19/0.99    ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))),
% 3.19/0.99    inference(cnf_transformation,[],[f54])).
% 3.19/0.99  
% 3.19/0.99  fof(f78,plain,(
% 3.19/0.99    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.19/0.99    inference(cnf_transformation,[],[f50])).
% 3.19/0.99  
% 3.19/0.99  fof(f103,plain,(
% 3.19/0.99    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 3.19/0.99    inference(equality_resolution,[],[f78])).
% 3.19/0.99  
% 3.19/0.99  fof(f2,axiom,(
% 3.19/0.99    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.19/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.19/0.99  
% 3.19/0.99  fof(f56,plain,(
% 3.19/0.99    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.19/0.99    inference(cnf_transformation,[],[f2])).
% 3.19/0.99  
% 3.19/0.99  fof(f21,axiom,(
% 3.19/0.99    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 3.19/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.19/0.99  
% 3.19/0.99  fof(f44,plain,(
% 3.19/0.99    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.19/0.99    inference(ennf_transformation,[],[f21])).
% 3.19/0.99  
% 3.19/0.99  fof(f45,plain,(
% 3.19/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.19/0.99    inference(flattening,[],[f44])).
% 3.19/0.99  
% 3.19/0.99  fof(f90,plain,(
% 3.19/0.99    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.19/0.99    inference(cnf_transformation,[],[f45])).
% 3.19/0.99  
% 3.19/0.99  fof(f1,axiom,(
% 3.19/0.99    v1_xboole_0(k1_xboole_0)),
% 3.19/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.19/0.99  
% 3.19/0.99  fof(f55,plain,(
% 3.19/0.99    v1_xboole_0(k1_xboole_0)),
% 3.19/0.99    inference(cnf_transformation,[],[f1])).
% 3.19/0.99  
% 3.19/0.99  fof(f3,axiom,(
% 3.19/0.99    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 3.19/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.19/0.99  
% 3.19/0.99  fof(f28,plain,(
% 3.19/0.99    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 3.19/0.99    inference(ennf_transformation,[],[f3])).
% 3.19/0.99  
% 3.19/0.99  fof(f57,plain,(
% 3.19/0.99    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 3.19/0.99    inference(cnf_transformation,[],[f28])).
% 3.19/0.99  
% 3.19/0.99  fof(f13,axiom,(
% 3.19/0.99    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_xboole_0(X2)))),
% 3.19/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.19/0.99  
% 3.19/0.99  fof(f37,plain,(
% 3.19/0.99    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 3.19/0.99    inference(ennf_transformation,[],[f13])).
% 3.19/0.99  
% 3.19/0.99  fof(f71,plain,(
% 3.19/0.99    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0)) )),
% 3.19/0.99    inference(cnf_transformation,[],[f37])).
% 3.19/0.99  
% 3.19/0.99  fof(f4,axiom,(
% 3.19/0.99    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.19/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.19/0.99  
% 3.19/0.99  fof(f48,plain,(
% 3.19/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.19/0.99    inference(nnf_transformation,[],[f4])).
% 3.19/0.99  
% 3.19/0.99  fof(f49,plain,(
% 3.19/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.19/0.99    inference(flattening,[],[f48])).
% 3.19/0.99  
% 3.19/0.99  fof(f59,plain,(
% 3.19/0.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 3.19/0.99    inference(cnf_transformation,[],[f49])).
% 3.19/0.99  
% 3.19/0.99  fof(f100,plain,(
% 3.19/0.99    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.19/0.99    inference(equality_resolution,[],[f59])).
% 3.19/0.99  
% 3.19/0.99  fof(f77,plain,(
% 3.19/0.99    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.19/0.99    inference(cnf_transformation,[],[f50])).
% 3.19/0.99  
% 3.19/0.99  fof(f104,plain,(
% 3.19/0.99    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 3.19/0.99    inference(equality_resolution,[],[f77])).
% 3.19/0.99  
% 3.19/0.99  fof(f58,plain,(
% 3.19/0.99    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 3.19/0.99    inference(cnf_transformation,[],[f49])).
% 3.19/0.99  
% 3.19/0.99  cnf(c_24,plain,
% 3.19/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.19/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.19/0.99      | k1_relset_1(X1,X2,X0) = X1
% 3.19/0.99      | k1_xboole_0 = X2 ),
% 3.19/0.99      inference(cnf_transformation,[],[f74]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_39,negated_conjecture,
% 3.19/0.99      ( v1_funct_2(sK3,sK1,sK2) ),
% 3.19/0.99      inference(cnf_transformation,[],[f92]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_693,plain,
% 3.19/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.19/0.99      | k1_relset_1(X1,X2,X0) = X1
% 3.19/0.99      | sK1 != X1
% 3.19/0.99      | sK2 != X2
% 3.19/0.99      | sK3 != X0
% 3.19/0.99      | k1_xboole_0 = X2 ),
% 3.19/0.99      inference(resolution_lifted,[status(thm)],[c_24,c_39]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_694,plain,
% 3.19/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 3.19/0.99      | k1_relset_1(sK1,sK2,sK3) = sK1
% 3.19/0.99      | k1_xboole_0 = sK2 ),
% 3.19/0.99      inference(unflattening,[status(thm)],[c_693]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_38,negated_conjecture,
% 3.19/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 3.19/0.99      inference(cnf_transformation,[],[f93]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_696,plain,
% 3.19/0.99      ( k1_relset_1(sK1,sK2,sK3) = sK1 | k1_xboole_0 = sK2 ),
% 3.19/0.99      inference(global_propositional_subsumption,
% 3.19/0.99                [status(thm)],
% 3.19/0.99                [c_694,c_38]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_1410,plain,
% 3.19/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 3.19/0.99      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_17,plain,
% 3.19/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.19/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.19/0.99      inference(cnf_transformation,[],[f72]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_1417,plain,
% 3.19/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.19/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.19/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_4229,plain,
% 3.19/0.99      ( k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
% 3.19/0.99      inference(superposition,[status(thm)],[c_1410,c_1417]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_4346,plain,
% 3.19/0.99      ( k1_relat_1(sK3) = sK1 | sK2 = k1_xboole_0 ),
% 3.19/0.99      inference(superposition,[status(thm)],[c_696,c_4229]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_13,plain,
% 3.19/0.99      ( ~ v2_funct_1(X0)
% 3.19/0.99      | ~ v1_relat_1(X0)
% 3.19/0.99      | ~ v1_funct_1(X0)
% 3.19/0.99      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 3.19/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_37,negated_conjecture,
% 3.19/0.99      ( v2_funct_1(sK3) ),
% 3.19/0.99      inference(cnf_transformation,[],[f94]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_443,plain,
% 3.19/0.99      ( ~ v1_relat_1(X0)
% 3.19/0.99      | ~ v1_funct_1(X0)
% 3.19/0.99      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 3.19/0.99      | sK3 != X0 ),
% 3.19/0.99      inference(resolution_lifted,[status(thm)],[c_13,c_37]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_444,plain,
% 3.19/0.99      ( ~ v1_relat_1(sK3)
% 3.19/0.99      | ~ v1_funct_1(sK3)
% 3.19/0.99      | k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
% 3.19/0.99      inference(unflattening,[status(thm)],[c_443]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_40,negated_conjecture,
% 3.19/0.99      ( v1_funct_1(sK3) ),
% 3.19/0.99      inference(cnf_transformation,[],[f91]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_446,plain,
% 3.19/0.99      ( ~ v1_relat_1(sK3)
% 3.19/0.99      | k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
% 3.19/0.99      inference(global_propositional_subsumption,
% 3.19/0.99                [status(thm)],
% 3.19/0.99                [c_444,c_40]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_1406,plain,
% 3.19/0.99      ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3)
% 3.19/0.99      | v1_relat_1(sK3) != iProver_top ),
% 3.19/0.99      inference(predicate_to_equality,[status(thm)],[c_446]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_15,plain,
% 3.19/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.19/0.99      | v1_relat_1(X0) ),
% 3.19/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_1764,plain,
% 3.19/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 3.19/0.99      | v1_relat_1(sK3) ),
% 3.19/0.99      inference(instantiation,[status(thm)],[c_15]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_1768,plain,
% 3.19/0.99      ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
% 3.19/0.99      inference(global_propositional_subsumption,
% 3.19/0.99                [status(thm)],
% 3.19/0.99                [c_1406,c_40,c_38,c_444,c_1764]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_29,plain,
% 3.19/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 3.19/0.99      | ~ v1_relat_1(X0)
% 3.19/0.99      | ~ v1_funct_1(X0) ),
% 3.19/0.99      inference(cnf_transformation,[],[f87]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_1411,plain,
% 3.19/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
% 3.19/0.99      | v1_relat_1(X0) != iProver_top
% 3.19/0.99      | v1_funct_1(X0) != iProver_top ),
% 3.19/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_4930,plain,
% 3.19/0.99      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK3)),k1_relat_1(sK3)))) = iProver_top
% 3.19/0.99      | v1_relat_1(k2_funct_1(sK3)) != iProver_top
% 3.19/0.99      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 3.19/0.99      inference(superposition,[status(thm)],[c_1768,c_1411]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_18,plain,
% 3.19/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.19/0.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.19/0.99      inference(cnf_transformation,[],[f73]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_1416,plain,
% 3.19/0.99      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.19/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.19/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_3116,plain,
% 3.19/0.99      ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
% 3.19/0.99      inference(superposition,[status(thm)],[c_1410,c_1416]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_36,negated_conjecture,
% 3.19/0.99      ( k2_relset_1(sK1,sK2,sK3) = sK2 ),
% 3.19/0.99      inference(cnf_transformation,[],[f95]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_3128,plain,
% 3.19/0.99      ( k2_relat_1(sK3) = sK2 ),
% 3.19/0.99      inference(light_normalisation,[status(thm)],[c_3116,c_36]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_14,plain,
% 3.19/0.99      ( ~ v2_funct_1(X0)
% 3.19/0.99      | ~ v1_relat_1(X0)
% 3.19/0.99      | ~ v1_funct_1(X0)
% 3.19/0.99      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 3.19/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_429,plain,
% 3.19/0.99      ( ~ v1_relat_1(X0)
% 3.19/0.99      | ~ v1_funct_1(X0)
% 3.19/0.99      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 3.19/0.99      | sK3 != X0 ),
% 3.19/0.99      inference(resolution_lifted,[status(thm)],[c_14,c_37]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_430,plain,
% 3.19/0.99      ( ~ v1_relat_1(sK3)
% 3.19/0.99      | ~ v1_funct_1(sK3)
% 3.19/0.99      | k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
% 3.19/0.99      inference(unflattening,[status(thm)],[c_429]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_432,plain,
% 3.19/0.99      ( ~ v1_relat_1(sK3)
% 3.19/0.99      | k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
% 3.19/0.99      inference(global_propositional_subsumption,
% 3.19/0.99                [status(thm)],
% 3.19/0.99                [c_430,c_40]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_1407,plain,
% 3.19/0.99      ( k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3)
% 3.19/0.99      | v1_relat_1(sK3) != iProver_top ),
% 3.19/0.99      inference(predicate_to_equality,[status(thm)],[c_432]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_1772,plain,
% 3.19/0.99      ( k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
% 3.19/0.99      inference(global_propositional_subsumption,
% 3.19/0.99                [status(thm)],
% 3.19/0.99                [c_1407,c_40,c_38,c_430,c_1764]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_3146,plain,
% 3.19/0.99      ( k1_relat_1(k2_funct_1(sK3)) = sK2 ),
% 3.19/0.99      inference(demodulation,[status(thm)],[c_3128,c_1772]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_4949,plain,
% 3.19/0.99      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3)))) = iProver_top
% 3.19/0.99      | v1_relat_1(k2_funct_1(sK3)) != iProver_top
% 3.19/0.99      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 3.19/0.99      inference(light_normalisation,[status(thm)],[c_4930,c_3146]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_41,plain,
% 3.19/0.99      ( v1_funct_1(sK3) = iProver_top ),
% 3.19/0.99      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_43,plain,
% 3.19/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 3.19/0.99      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_1765,plain,
% 3.19/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 3.19/0.99      | v1_relat_1(sK3) = iProver_top ),
% 3.19/0.99      inference(predicate_to_equality,[status(thm)],[c_1764]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_11,plain,
% 3.19/0.99      ( ~ v1_relat_1(X0)
% 3.19/0.99      | ~ v1_funct_1(X0)
% 3.19/0.99      | v1_funct_1(k2_funct_1(X0)) ),
% 3.19/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_2130,plain,
% 3.19/0.99      ( ~ v1_relat_1(sK3)
% 3.19/0.99      | v1_funct_1(k2_funct_1(sK3))
% 3.19/0.99      | ~ v1_funct_1(sK3) ),
% 3.19/0.99      inference(instantiation,[status(thm)],[c_11]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_2131,plain,
% 3.19/0.99      ( v1_relat_1(sK3) != iProver_top
% 3.19/0.99      | v1_funct_1(k2_funct_1(sK3)) = iProver_top
% 3.19/0.99      | v1_funct_1(sK3) != iProver_top ),
% 3.19/0.99      inference(predicate_to_equality,[status(thm)],[c_2130]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_12,plain,
% 3.19/0.99      ( ~ v1_relat_1(X0)
% 3.19/0.99      | v1_relat_1(k2_funct_1(X0))
% 3.19/0.99      | ~ v1_funct_1(X0) ),
% 3.19/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_2140,plain,
% 3.19/0.99      ( v1_relat_1(k2_funct_1(sK3))
% 3.19/0.99      | ~ v1_relat_1(sK3)
% 3.19/0.99      | ~ v1_funct_1(sK3) ),
% 3.19/0.99      inference(instantiation,[status(thm)],[c_12]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_2141,plain,
% 3.19/0.99      ( v1_relat_1(k2_funct_1(sK3)) = iProver_top
% 3.19/0.99      | v1_relat_1(sK3) != iProver_top
% 3.19/0.99      | v1_funct_1(sK3) != iProver_top ),
% 3.19/0.99      inference(predicate_to_equality,[status(thm)],[c_2140]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_5555,plain,
% 3.19/0.99      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3)))) = iProver_top ),
% 3.19/0.99      inference(global_propositional_subsumption,
% 3.19/0.99                [status(thm)],
% 3.19/0.99                [c_4949,c_41,c_43,c_1765,c_2131,c_2141]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_5561,plain,
% 3.19/0.99      ( k1_relset_1(sK2,k1_relat_1(sK3),k2_funct_1(sK3)) = k1_relat_1(k2_funct_1(sK3)) ),
% 3.19/0.99      inference(superposition,[status(thm)],[c_5555,c_1417]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_5570,plain,
% 3.19/0.99      ( k1_relset_1(sK2,k1_relat_1(sK3),k2_funct_1(sK3)) = sK2 ),
% 3.19/0.99      inference(light_normalisation,[status(thm)],[c_5561,c_3146]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_5579,plain,
% 3.19/0.99      ( k1_relset_1(sK2,sK1,k2_funct_1(sK3)) = sK2 | sK2 = k1_xboole_0 ),
% 3.19/0.99      inference(superposition,[status(thm)],[c_4346,c_5570]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_30,plain,
% 3.19/0.99      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
% 3.19/0.99      | ~ v1_relat_1(X0)
% 3.19/0.99      | ~ v1_funct_1(X0) ),
% 3.19/0.99      inference(cnf_transformation,[],[f86]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_35,negated_conjecture,
% 3.19/0.99      ( ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
% 3.19/0.99      | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.19/0.99      | ~ v1_funct_1(k2_funct_1(sK3)) ),
% 3.19/0.99      inference(cnf_transformation,[],[f96]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_704,plain,
% 3.19/0.99      ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.19/0.99      | ~ v1_relat_1(X0)
% 3.19/0.99      | ~ v1_funct_1(X0)
% 3.19/0.99      | ~ v1_funct_1(k2_funct_1(sK3))
% 3.19/0.99      | k2_funct_1(sK3) != X0
% 3.19/0.99      | k1_relat_1(X0) != sK2
% 3.19/0.99      | k2_relat_1(X0) != sK1 ),
% 3.19/0.99      inference(resolution_lifted,[status(thm)],[c_30,c_35]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_705,plain,
% 3.19/0.99      ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.19/0.99      | ~ v1_relat_1(k2_funct_1(sK3))
% 3.19/0.99      | ~ v1_funct_1(k2_funct_1(sK3))
% 3.19/0.99      | k1_relat_1(k2_funct_1(sK3)) != sK2
% 3.19/0.99      | k2_relat_1(k2_funct_1(sK3)) != sK1 ),
% 3.19/0.99      inference(unflattening,[status(thm)],[c_704]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_717,plain,
% 3.19/0.99      ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.19/0.99      | ~ v1_funct_1(k2_funct_1(sK3))
% 3.19/0.99      | k1_relat_1(k2_funct_1(sK3)) != sK2
% 3.19/0.99      | k2_relat_1(k2_funct_1(sK3)) != sK1 ),
% 3.19/0.99      inference(forward_subsumption_resolution,
% 3.19/0.99                [status(thm)],
% 3.19/0.99                [c_705,c_15]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_1395,plain,
% 3.19/0.99      ( k1_relat_1(k2_funct_1(sK3)) != sK2
% 3.19/0.99      | k2_relat_1(k2_funct_1(sK3)) != sK1
% 3.19/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.19/0.99      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 3.19/0.99      inference(predicate_to_equality,[status(thm)],[c_717]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_2117,plain,
% 3.19/0.99      ( k1_relat_1(sK3) != sK1
% 3.19/0.99      | k2_relat_1(sK3) != sK2
% 3.19/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.19/0.99      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 3.19/0.99      inference(light_normalisation,[status(thm)],[c_1395,c_1768,c_1772]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_3144,plain,
% 3.19/0.99      ( k1_relat_1(sK3) != sK1
% 3.19/0.99      | sK2 != sK2
% 3.19/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.19/0.99      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 3.19/0.99      inference(demodulation,[status(thm)],[c_3128,c_2117]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_3156,plain,
% 3.19/0.99      ( k1_relat_1(sK3) != sK1
% 3.19/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.19/0.99      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 3.19/0.99      inference(equality_resolution_simp,[status(thm)],[c_3144]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_3456,plain,
% 3.19/0.99      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.19/0.99      | k1_relat_1(sK3) != sK1 ),
% 3.19/0.99      inference(global_propositional_subsumption,
% 3.19/0.99                [status(thm)],
% 3.19/0.99                [c_3156,c_41,c_43,c_1765,c_2117,c_2131,c_3128]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_3457,plain,
% 3.19/0.99      ( k1_relat_1(sK3) != sK1
% 3.19/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.19/0.99      inference(renaming,[status(thm)],[c_3456]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_4472,plain,
% 3.19/0.99      ( sK2 = k1_xboole_0
% 3.19/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.19/0.99      inference(superposition,[status(thm)],[c_4346,c_3457]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_5560,plain,
% 3.19/0.99      ( sK2 = k1_xboole_0
% 3.19/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 3.19/0.99      inference(superposition,[status(thm)],[c_4346,c_5555]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_5774,plain,
% 3.19/0.99      ( sK2 = k1_xboole_0 ),
% 3.19/0.99      inference(global_propositional_subsumption,
% 3.19/0.99                [status(thm)],
% 3.19/0.99                [c_5579,c_4472,c_5560]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_5779,plain,
% 3.19/0.99      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK3)))) = iProver_top ),
% 3.19/0.99      inference(demodulation,[status(thm)],[c_5774,c_5555]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_20,plain,
% 3.19/0.99      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 3.19/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 3.19/0.99      | k1_xboole_0 = X1
% 3.19/0.99      | k1_xboole_0 = X0 ),
% 3.19/0.99      inference(cnf_transformation,[],[f103]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_497,plain,
% 3.19/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 3.19/0.99      | ~ v1_relat_1(X2)
% 3.19/0.99      | ~ v1_funct_1(X2)
% 3.19/0.99      | X2 != X0
% 3.19/0.99      | k1_relat_1(X2) != X1
% 3.19/0.99      | k2_relat_1(X2) != k1_xboole_0
% 3.19/0.99      | k1_xboole_0 = X1
% 3.19/0.99      | k1_xboole_0 = X0 ),
% 3.19/0.99      inference(resolution_lifted,[status(thm)],[c_20,c_30]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_498,plain,
% 3.19/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k1_xboole_0)))
% 3.19/0.99      | ~ v1_relat_1(X0)
% 3.19/0.99      | ~ v1_funct_1(X0)
% 3.19/0.99      | k2_relat_1(X0) != k1_xboole_0
% 3.19/0.99      | k1_xboole_0 = X0
% 3.19/0.99      | k1_xboole_0 = k1_relat_1(X0) ),
% 3.19/0.99      inference(unflattening,[status(thm)],[c_497]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_1,plain,
% 3.19/0.99      ( r1_tarski(k1_xboole_0,X0) ),
% 3.19/0.99      inference(cnf_transformation,[],[f56]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_32,plain,
% 3.19/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 3.19/0.99      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.19/0.99      | ~ v1_relat_1(X0)
% 3.19/0.99      | ~ v1_funct_1(X0) ),
% 3.19/0.99      inference(cnf_transformation,[],[f90]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_401,plain,
% 3.19/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 3.19/0.99      | ~ v1_relat_1(X0)
% 3.19/0.99      | ~ v1_funct_1(X0)
% 3.19/0.99      | X1 != X2
% 3.19/0.99      | k2_relat_1(X0) != k1_xboole_0 ),
% 3.19/0.99      inference(resolution_lifted,[status(thm)],[c_1,c_32]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_402,plain,
% 3.19/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 3.19/0.99      | ~ v1_relat_1(X0)
% 3.19/0.99      | ~ v1_funct_1(X0)
% 3.19/0.99      | k2_relat_1(X0) != k1_xboole_0 ),
% 3.19/0.99      inference(unflattening,[status(thm)],[c_401]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_514,plain,
% 3.19/0.99      ( ~ v1_relat_1(X0)
% 3.19/0.99      | ~ v1_funct_1(X0)
% 3.19/0.99      | k2_relat_1(X0) != k1_xboole_0
% 3.19/0.99      | k1_xboole_0 = X0
% 3.19/0.99      | k1_xboole_0 = k1_relat_1(X0) ),
% 3.19/0.99      inference(forward_subsumption_resolution,
% 3.19/0.99                [status(thm)],
% 3.19/0.99                [c_498,c_402]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_1404,plain,
% 3.19/0.99      ( k2_relat_1(X0) != k1_xboole_0
% 3.19/0.99      | k1_xboole_0 = X0
% 3.19/0.99      | k1_xboole_0 = k1_relat_1(X0)
% 3.19/0.99      | v1_relat_1(X0) != iProver_top
% 3.19/0.99      | v1_funct_1(X0) != iProver_top ),
% 3.19/0.99      inference(predicate_to_equality,[status(thm)],[c_514]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_3632,plain,
% 3.19/0.99      ( k1_relat_1(sK3) = k1_xboole_0
% 3.19/0.99      | sK2 != k1_xboole_0
% 3.19/0.99      | sK3 = k1_xboole_0
% 3.19/0.99      | v1_relat_1(sK3) != iProver_top
% 3.19/0.99      | v1_funct_1(sK3) != iProver_top ),
% 3.19/0.99      inference(superposition,[status(thm)],[c_3128,c_1404]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_0,plain,
% 3.19/0.99      ( v1_xboole_0(k1_xboole_0) ),
% 3.19/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_831,plain,
% 3.19/0.99      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 3.19/0.99      theory(equality) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_2006,plain,
% 3.19/0.99      ( ~ v1_xboole_0(X0)
% 3.19/0.99      | v1_xboole_0(k1_relat_1(sK3))
% 3.19/0.99      | k1_relat_1(sK3) != X0 ),
% 3.19/0.99      inference(instantiation,[status(thm)],[c_831]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_2008,plain,
% 3.19/0.99      ( v1_xboole_0(k1_relat_1(sK3))
% 3.19/0.99      | ~ v1_xboole_0(k1_xboole_0)
% 3.19/0.99      | k1_relat_1(sK3) != k1_xboole_0 ),
% 3.19/0.99      inference(instantiation,[status(thm)],[c_2006]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_2,plain,
% 3.19/0.99      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(X1) | X0 = X1 ),
% 3.19/0.99      inference(cnf_transformation,[],[f57]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_2182,plain,
% 3.19/0.99      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(sK3) | sK3 = X0 ),
% 3.19/0.99      inference(instantiation,[status(thm)],[c_2]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_2184,plain,
% 3.19/0.99      ( ~ v1_xboole_0(sK3)
% 3.19/0.99      | ~ v1_xboole_0(k1_xboole_0)
% 3.19/0.99      | sK3 = k1_xboole_0 ),
% 3.19/0.99      inference(instantiation,[status(thm)],[c_2182]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_2273,plain,
% 3.19/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))))
% 3.19/0.99      | ~ v1_relat_1(sK3)
% 3.19/0.99      | ~ v1_funct_1(sK3) ),
% 3.19/0.99      inference(instantiation,[status(thm)],[c_29]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_16,plain,
% 3.19/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.19/0.99      | ~ v1_xboole_0(X1)
% 3.19/0.99      | v1_xboole_0(X0) ),
% 3.19/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_2096,plain,
% 3.19/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.19/0.99      | ~ v1_xboole_0(X0)
% 3.19/0.99      | v1_xboole_0(sK3) ),
% 3.19/0.99      inference(instantiation,[status(thm)],[c_16]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_3064,plain,
% 3.19/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))))
% 3.19/0.99      | ~ v1_xboole_0(k1_relat_1(sK3))
% 3.19/0.99      | v1_xboole_0(sK3) ),
% 3.19/0.99      inference(instantiation,[status(thm)],[c_2096]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_3661,plain,
% 3.19/0.99      ( ~ v1_relat_1(sK3)
% 3.19/0.99      | ~ v1_funct_1(sK3)
% 3.19/0.99      | k1_relat_1(sK3) = k1_xboole_0
% 3.19/0.99      | sK2 != k1_xboole_0
% 3.19/0.99      | sK3 = k1_xboole_0 ),
% 3.19/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_3632]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_3893,plain,
% 3.19/0.99      ( sK2 != k1_xboole_0 | sK3 = k1_xboole_0 ),
% 3.19/0.99      inference(global_propositional_subsumption,
% 3.19/0.99                [status(thm)],
% 3.19/0.99                [c_3632,c_40,c_38,c_0,c_1764,c_2008,c_2184,c_2273,c_3064,
% 3.19/0.99                 c_3661]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_5790,plain,
% 3.19/0.99      ( sK3 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 3.19/0.99      inference(demodulation,[status(thm)],[c_5774,c_3893]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_5866,plain,
% 3.19/0.99      ( sK3 = k1_xboole_0 ),
% 3.19/0.99      inference(equality_resolution_simp,[status(thm)],[c_5790]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_5945,plain,
% 3.19/0.99      ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(k1_xboole_0)))) = iProver_top ),
% 3.19/0.99      inference(light_normalisation,[status(thm)],[c_5779,c_5866]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_4,plain,
% 3.19/0.99      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.19/0.99      inference(cnf_transformation,[],[f100]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_5947,plain,
% 3.19/0.99      ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.19/0.99      inference(demodulation,[status(thm)],[c_5945,c_4]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_4231,plain,
% 3.19/0.99      ( k1_relset_1(k1_xboole_0,X0,X1) = k1_relat_1(X1)
% 3.19/0.99      | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.19/0.99      inference(superposition,[status(thm)],[c_4,c_1417]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_6418,plain,
% 3.19/0.99      ( k1_relset_1(k1_xboole_0,X0,k2_funct_1(k1_xboole_0)) = k1_relat_1(k2_funct_1(k1_xboole_0)) ),
% 3.19/0.99      inference(superposition,[status(thm)],[c_5947,c_4231]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_5795,plain,
% 3.19/0.99      ( k1_relat_1(k2_funct_1(sK3)) = k1_xboole_0 ),
% 3.19/0.99      inference(demodulation,[status(thm)],[c_5774,c_3146]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_5872,plain,
% 3.19/0.99      ( k1_relat_1(k2_funct_1(k1_xboole_0)) = k1_xboole_0 ),
% 3.19/0.99      inference(demodulation,[status(thm)],[c_5866,c_5795]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_7935,plain,
% 3.19/0.99      ( k1_relset_1(k1_xboole_0,X0,k2_funct_1(k1_xboole_0)) = k1_xboole_0 ),
% 3.19/0.99      inference(light_normalisation,[status(thm)],[c_6418,c_5872]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_21,plain,
% 3.19/0.99      ( v1_funct_2(X0,k1_xboole_0,X1)
% 3.19/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.19/0.99      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 3.19/0.99      inference(cnf_transformation,[],[f104]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_594,plain,
% 3.19/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.19/0.99      | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.19/0.99      | ~ v1_funct_1(k2_funct_1(sK3))
% 3.19/0.99      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
% 3.19/0.99      | k2_funct_1(sK3) != X0
% 3.19/0.99      | sK1 != X1
% 3.19/0.99      | sK2 != k1_xboole_0 ),
% 3.19/0.99      inference(resolution_lifted,[status(thm)],[c_21,c_35]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_595,plain,
% 3.19/0.99      ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.19/0.99      | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
% 3.19/0.99      | ~ v1_funct_1(k2_funct_1(sK3))
% 3.19/0.99      | k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
% 3.19/0.99      | sK2 != k1_xboole_0 ),
% 3.19/0.99      inference(unflattening,[status(thm)],[c_594]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_1400,plain,
% 3.19/0.99      ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
% 3.19/0.99      | sK2 != k1_xboole_0
% 3.19/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.19/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top
% 3.19/0.99      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 3.19/0.99      inference(predicate_to_equality,[status(thm)],[c_595]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_1641,plain,
% 3.19/0.99      ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
% 3.19/0.99      | sK2 != k1_xboole_0
% 3.19/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.19/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.19/0.99      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 3.19/0.99      inference(demodulation,[status(thm)],[c_1400,c_4]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_2228,plain,
% 3.19/0.99      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.19/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.19/0.99      | sK2 != k1_xboole_0
% 3.19/0.99      | k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0 ),
% 3.19/0.99      inference(global_propositional_subsumption,
% 3.19/0.99                [status(thm)],
% 3.19/0.99                [c_1641,c_41,c_43,c_1765,c_2131]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_2229,plain,
% 3.19/0.99      ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
% 3.19/0.99      | sK2 != k1_xboole_0
% 3.19/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.19/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.19/0.99      inference(renaming,[status(thm)],[c_2228]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_5797,plain,
% 3.19/0.99      ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
% 3.19/0.99      | k1_xboole_0 != k1_xboole_0
% 3.19/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top
% 3.19/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.19/0.99      inference(demodulation,[status(thm)],[c_5774,c_2229]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_5834,plain,
% 3.19/0.99      ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
% 3.19/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top
% 3.19/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.19/0.99      inference(equality_resolution_simp,[status(thm)],[c_5797]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_5838,plain,
% 3.19/0.99      ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
% 3.19/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.19/0.99      inference(demodulation,[status(thm)],[c_5834,c_4]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_5874,plain,
% 3.19/0.99      ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(k1_xboole_0)) != k1_xboole_0
% 3.19/0.99      | m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.19/0.99      inference(demodulation,[status(thm)],[c_5866,c_5838]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_5950,plain,
% 3.19/0.99      ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(k1_xboole_0)) != k1_xboole_0 ),
% 3.19/0.99      inference(backward_subsumption_resolution,
% 3.19/0.99                [status(thm)],
% 3.19/0.99                [c_5947,c_5874]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_7938,plain,
% 3.19/0.99      ( k1_xboole_0 != k1_xboole_0 ),
% 3.19/0.99      inference(demodulation,[status(thm)],[c_7935,c_5950]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_120,plain,
% 3.19/0.99      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 3.19/0.99      inference(instantiation,[status(thm)],[c_4]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_5,plain,
% 3.19/0.99      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 3.19/0.99      | k1_xboole_0 = X1
% 3.19/0.99      | k1_xboole_0 = X0 ),
% 3.19/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_119,plain,
% 3.19/0.99      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 3.19/0.99      | k1_xboole_0 = k1_xboole_0 ),
% 3.19/0.99      inference(instantiation,[status(thm)],[c_5]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(contradiction,plain,
% 3.19/0.99      ( $false ),
% 3.19/0.99      inference(minisat,[status(thm)],[c_7938,c_120,c_119]) ).
% 3.19/0.99  
% 3.19/0.99  
% 3.19/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.19/0.99  
% 3.19/0.99  ------                               Statistics
% 3.19/0.99  
% 3.19/0.99  ------ General
% 3.19/0.99  
% 3.19/0.99  abstr_ref_over_cycles:                  0
% 3.19/0.99  abstr_ref_under_cycles:                 0
% 3.19/0.99  gc_basic_clause_elim:                   0
% 3.19/0.99  forced_gc_time:                         0
% 3.19/0.99  parsing_time:                           0.01
% 3.19/0.99  unif_index_cands_time:                  0.
% 3.19/0.99  unif_index_add_time:                    0.
% 3.19/0.99  orderings_time:                         0.
% 3.19/0.99  out_proof_time:                         0.009
% 3.19/0.99  total_time:                             0.239
% 3.19/0.99  num_of_symbols:                         51
% 3.19/0.99  num_of_terms:                           6239
% 3.19/0.99  
% 3.19/0.99  ------ Preprocessing
% 3.19/0.99  
% 3.19/0.99  num_of_splits:                          0
% 3.19/0.99  num_of_split_atoms:                     0
% 3.19/0.99  num_of_reused_defs:                     0
% 3.19/0.99  num_eq_ax_congr_red:                    9
% 3.19/0.99  num_of_sem_filtered_clauses:            1
% 3.19/0.99  num_of_subtypes:                        0
% 3.19/0.99  monotx_restored_types:                  0
% 3.19/0.99  sat_num_of_epr_types:                   0
% 3.19/0.99  sat_num_of_non_cyclic_types:            0
% 3.19/0.99  sat_guarded_non_collapsed_types:        0
% 3.19/0.99  num_pure_diseq_elim:                    0
% 3.19/0.99  simp_replaced_by:                       0
% 3.19/0.99  res_preprocessed:                       148
% 3.19/0.99  prep_upred:                             0
% 3.19/0.99  prep_unflattend:                        55
% 3.19/0.99  smt_new_axioms:                         0
% 3.19/0.99  pred_elim_cands:                        7
% 3.19/0.99  pred_elim:                              3
% 3.19/0.99  pred_elim_cl:                           -2
% 3.19/0.99  pred_elim_cycles:                       4
% 3.19/0.99  merged_defs:                            0
% 3.19/0.99  merged_defs_ncl:                        0
% 3.19/0.99  bin_hyper_res:                          0
% 3.19/0.99  prep_cycles:                            3
% 3.19/0.99  pred_elim_time:                         0.011
% 3.19/0.99  splitting_time:                         0.
% 3.19/0.99  sem_filter_time:                        0.
% 3.19/0.99  monotx_time:                            0.001
% 3.19/0.99  subtype_inf_time:                       0.
% 3.19/0.99  
% 3.19/0.99  ------ Problem properties
% 3.19/0.99  
% 3.19/0.99  clauses:                                41
% 3.19/0.99  conjectures:                            3
% 3.19/0.99  epr:                                    3
% 3.19/0.99  horn:                                   35
% 3.19/0.99  ground:                                 15
% 3.19/0.99  unary:                                  13
% 3.19/0.99  binary:                                 6
% 3.19/0.99  lits:                                   110
% 3.19/0.99  lits_eq:                                47
% 3.19/0.99  fd_pure:                                0
% 3.19/0.99  fd_pseudo:                              0
% 3.19/0.99  fd_cond:                                3
% 3.19/0.99  fd_pseudo_cond:                         1
% 3.19/0.99  ac_symbols:                             0
% 3.19/0.99  
% 3.19/0.99  ------ Propositional Solver
% 3.19/0.99  
% 3.19/0.99  prop_solver_calls:                      24
% 3.19/0.99  prop_fast_solver_calls:                 1174
% 3.19/0.99  smt_solver_calls:                       0
% 3.19/0.99  smt_fast_solver_calls:                  0
% 3.19/0.99  prop_num_of_clauses:                    2924
% 3.19/0.99  prop_preprocess_simplified:             8352
% 3.19/0.99  prop_fo_subsumed:                       37
% 3.19/0.99  prop_solver_time:                       0.
% 3.19/0.99  smt_solver_time:                        0.
% 3.19/0.99  smt_fast_solver_time:                   0.
% 3.19/0.99  prop_fast_solver_time:                  0.
% 3.19/0.99  prop_unsat_core_time:                   0.
% 3.19/0.99  
% 3.19/0.99  ------ QBF
% 3.19/0.99  
% 3.19/0.99  qbf_q_res:                              0
% 3.19/0.99  qbf_num_tautologies:                    0
% 3.19/0.99  qbf_prep_cycles:                        0
% 3.19/0.99  
% 3.19/0.99  ------ BMC1
% 3.19/0.99  
% 3.19/0.99  bmc1_current_bound:                     -1
% 3.19/0.99  bmc1_last_solved_bound:                 -1
% 3.19/0.99  bmc1_unsat_core_size:                   -1
% 3.19/0.99  bmc1_unsat_core_parents_size:           -1
% 3.19/0.99  bmc1_merge_next_fun:                    0
% 3.19/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.19/0.99  
% 3.19/0.99  ------ Instantiation
% 3.19/0.99  
% 3.19/0.99  inst_num_of_clauses:                    1049
% 3.19/0.99  inst_num_in_passive:                    457
% 3.19/0.99  inst_num_in_active:                     451
% 3.19/0.99  inst_num_in_unprocessed:                141
% 3.19/0.99  inst_num_of_loops:                      550
% 3.19/0.99  inst_num_of_learning_restarts:          0
% 3.19/0.99  inst_num_moves_active_passive:          97
% 3.19/0.99  inst_lit_activity:                      0
% 3.19/0.99  inst_lit_activity_moves:                0
% 3.19/0.99  inst_num_tautologies:                   0
% 3.19/0.99  inst_num_prop_implied:                  0
% 3.19/0.99  inst_num_existing_simplified:           0
% 3.19/0.99  inst_num_eq_res_simplified:             0
% 3.19/0.99  inst_num_child_elim:                    0
% 3.19/0.99  inst_num_of_dismatching_blockings:      443
% 3.19/0.99  inst_num_of_non_proper_insts:           901
% 3.19/0.99  inst_num_of_duplicates:                 0
% 3.19/0.99  inst_inst_num_from_inst_to_res:         0
% 3.19/0.99  inst_dismatching_checking_time:         0.
% 3.19/0.99  
% 3.19/0.99  ------ Resolution
% 3.19/0.99  
% 3.19/0.99  res_num_of_clauses:                     0
% 3.19/0.99  res_num_in_passive:                     0
% 3.19/0.99  res_num_in_active:                      0
% 3.19/0.99  res_num_of_loops:                       151
% 3.19/0.99  res_forward_subset_subsumed:            37
% 3.19/0.99  res_backward_subset_subsumed:           0
% 3.19/0.99  res_forward_subsumed:                   0
% 3.19/0.99  res_backward_subsumed:                  0
% 3.19/0.99  res_forward_subsumption_resolution:     6
% 3.19/0.99  res_backward_subsumption_resolution:    0
% 3.19/0.99  res_clause_to_clause_subsumption:       315
% 3.19/0.99  res_orphan_elimination:                 0
% 3.19/0.99  res_tautology_del:                      70
% 3.19/0.99  res_num_eq_res_simplified:              0
% 3.19/0.99  res_num_sel_changes:                    0
% 3.19/0.99  res_moves_from_active_to_pass:          0
% 3.19/0.99  
% 3.19/0.99  ------ Superposition
% 3.19/0.99  
% 3.19/0.99  sup_time_total:                         0.
% 3.19/0.99  sup_time_generating:                    0.
% 3.19/0.99  sup_time_sim_full:                      0.
% 3.19/0.99  sup_time_sim_immed:                     0.
% 3.19/0.99  
% 3.19/0.99  sup_num_of_clauses:                     114
% 3.19/0.99  sup_num_in_active:                      68
% 3.19/0.99  sup_num_in_passive:                     46
% 3.19/0.99  sup_num_of_loops:                       109
% 3.19/0.99  sup_fw_superposition:                   104
% 3.19/0.99  sup_bw_superposition:                   34
% 3.19/0.99  sup_immediate_simplified:               93
% 3.19/0.99  sup_given_eliminated:                   0
% 3.19/0.99  comparisons_done:                       0
% 3.19/0.99  comparisons_avoided:                    11
% 3.19/0.99  
% 3.19/0.99  ------ Simplifications
% 3.19/0.99  
% 3.19/0.99  
% 3.19/0.99  sim_fw_subset_subsumed:                 16
% 3.19/0.99  sim_bw_subset_subsumed:                 6
% 3.19/0.99  sim_fw_subsumed:                        19
% 3.19/0.99  sim_bw_subsumed:                        4
% 3.19/0.99  sim_fw_subsumption_res:                 1
% 3.19/0.99  sim_bw_subsumption_res:                 4
% 3.19/0.99  sim_tautology_del:                      3
% 3.19/0.99  sim_eq_tautology_del:                   11
% 3.19/0.99  sim_eq_res_simp:                        6
% 3.19/0.99  sim_fw_demodulated:                     24
% 3.19/0.99  sim_bw_demodulated:                     49
% 3.19/0.99  sim_light_normalised:                   38
% 3.19/0.99  sim_joinable_taut:                      0
% 3.19/0.99  sim_joinable_simp:                      0
% 3.19/0.99  sim_ac_normalised:                      0
% 3.19/0.99  sim_smt_subsumption:                    0
% 3.19/0.99  
%------------------------------------------------------------------------------
