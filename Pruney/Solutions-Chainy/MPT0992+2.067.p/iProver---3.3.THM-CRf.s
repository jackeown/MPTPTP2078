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
% DateTime   : Thu Dec  3 12:04:00 EST 2020

% Result     : Theorem 6.57s
% Output     : CNFRefutation 6.57s
% Verified   : 
% Statistics : Number of formulae       :  253 (4808 expanded)
%              Number of clauses        :  169 (1926 expanded)
%              Number of leaves         :   24 ( 870 expanded)
%              Depth                    :   29
%              Number of atoms          :  702 (22390 expanded)
%              Number of equality atoms :  339 (5990 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f23,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(X2,X0)
       => ( ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
            & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
            & v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r1_tarski(X2,X0)
         => ( ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
              & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
              & v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
            | ( k1_xboole_0 != X0
              & k1_xboole_0 = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f49,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        | ~ v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
        | ~ v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f50,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        | ~ v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
        | ~ v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f49])).

fof(f56,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
          | ~ v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
          | ~ v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & r1_tarski(X2,X0)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
        | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) )
      & ( k1_xboole_0 = sK0
        | k1_xboole_0 != sK1 )
      & r1_tarski(sK2,sK0)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,
    ( ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) )
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_tarski(sK2,sK0)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f50,f56])).

fof(f95,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f57])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f67,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f66,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f10,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f19,axiom,(
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
    inference(ennf_transformation,[],[f19])).

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
    inference(flattening,[],[f41])).

fof(f55,plain,(
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
    inference(nnf_transformation,[],[f42])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f94,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f57])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f93,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f57])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f46,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f45])).

fof(f89,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f43])).

fof(f88,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f96,plain,(
    r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f57])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f47])).

fof(f92,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_partfun1(X0,X1,X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f91,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f98,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f57])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f26])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f97,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f57])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f51])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f99,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f63])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f12,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f100,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f62])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => ( r1_tarski(k1_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(flattening,[],[f39])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_38,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1833,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_20,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_13,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_464,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_20,c_13])).

cnf(c_1830,plain,
    ( k7_relat_1(X0,X1) = X0
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_464])).

cnf(c_5214,plain,
    ( k7_relat_1(sK3,sK0) = sK3
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1833,c_1830])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1845,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2656,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1833,c_1845])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_7,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_275,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_7])).

cnf(c_276,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_275])).

cnf(c_346,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_9,c_276])).

cnf(c_1831,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_346])).

cnf(c_3979,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2656,c_1831])).

cnf(c_12,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1844,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_4772,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3979,c_1844])).

cnf(c_4773,plain,
    ( v1_relat_1(sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4772])).

cnf(c_2733,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_relat_1(sK3)
    | k7_relat_1(sK3,X0) = sK3 ),
    inference(instantiation,[status(thm)],[c_464])).

cnf(c_5098,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_relat_1(sK3)
    | k7_relat_1(sK3,sK0) = sK3 ),
    inference(instantiation,[status(thm)],[c_2733])).

cnf(c_5477,plain,
    ( k7_relat_1(sK3,sK0) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5214,c_38,c_4773,c_5098])).

cnf(c_16,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1843,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_5481,plain,
    ( r1_tarski(k1_relat_1(sK3),sK0) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5477,c_1843])).

cnf(c_5672,plain,
    ( r1_tarski(k1_relat_1(sK3),sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5481,c_4772])).

cnf(c_28,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_39,negated_conjecture,
    ( v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_682,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK3 != X0
    | sK1 != X2
    | sK0 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_39])).

cnf(c_683,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_682])).

cnf(c_685,plain,
    ( k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_683,c_38])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1840,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_3377,plain,
    ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1833,c_1840])).

cnf(c_3636,plain,
    ( k1_relat_1(sK3) = sK0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_685,c_3377])).

cnf(c_17,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1842,plain,
    ( k1_relat_1(k7_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_4413,plain,
    ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
    | sK1 = k1_xboole_0
    | r1_tarski(X0,sK0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3636,c_1842])).

cnf(c_5841,plain,
    ( r1_tarski(X0,sK0) != iProver_top
    | sK1 = k1_xboole_0
    | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4413,c_4772])).

cnf(c_5842,plain,
    ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
    | sK1 = k1_xboole_0
    | r1_tarski(X0,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_5841])).

cnf(c_5854,plain,
    ( k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK3))) = k1_relat_1(sK3)
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5672,c_5842])).

cnf(c_40,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_31,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_2273,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK3)
    | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) ),
    inference(instantiation,[status(thm)],[c_31])).

cnf(c_2309,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_2273])).

cnf(c_3354,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | k2_partfun1(sK0,sK1,sK3,sK2) = k7_relat_1(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_2309])).

cnf(c_2368,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(X0,k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_3428,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),k2_zfmisc_1(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_2368])).

cnf(c_7161,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_3428])).

cnf(c_29,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_2268,plain,
    ( m1_subset_1(k2_partfun1(X0,X1,sK3,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_2315,plain,
    ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2268])).

cnf(c_7162,plain,
    ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2315])).

cnf(c_2166,plain,
    ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_346])).

cnf(c_2869,plain,
    ( ~ r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),k2_zfmisc_1(X0,X1))
    | v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | ~ v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_2166])).

cnf(c_9562,plain,
    ( ~ r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_2869])).

cnf(c_1076,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2976,plain,
    ( X0 != X1
    | X0 = k2_partfun1(sK0,sK1,sK3,X2)
    | k2_partfun1(sK0,sK1,sK3,X2) != X1 ),
    inference(instantiation,[status(thm)],[c_1076])).

cnf(c_3597,plain,
    ( X0 = k2_partfun1(sK0,sK1,sK3,X1)
    | X0 != k7_relat_1(sK3,X1)
    | k2_partfun1(sK0,sK1,sK3,X1) != k7_relat_1(sK3,X1) ),
    inference(instantiation,[status(thm)],[c_2976])).

cnf(c_5167,plain,
    ( k2_partfun1(sK0,sK1,sK3,X0) != k7_relat_1(sK3,X0)
    | k7_relat_1(sK3,X0) = k2_partfun1(sK0,sK1,sK3,X0)
    | k7_relat_1(sK3,X0) != k7_relat_1(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_3597])).

cnf(c_11130,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != k7_relat_1(sK3,sK2)
    | k7_relat_1(sK3,sK2) = k2_partfun1(sK0,sK1,sK3,sK2)
    | k7_relat_1(sK3,sK2) != k7_relat_1(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_5167])).

cnf(c_1082,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_4676,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k7_relat_1(sK3,sK2))
    | k7_relat_1(sK3,sK2) != X0 ),
    inference(instantiation,[status(thm)],[c_1082])).

cnf(c_11131,plain,
    ( ~ v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | v1_relat_1(k7_relat_1(sK3,sK2))
    | k7_relat_1(sK3,sK2) != k2_partfun1(sK0,sK1,sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_4676])).

cnf(c_1075,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_5168,plain,
    ( k7_relat_1(sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_1075])).

cnf(c_13785,plain,
    ( k7_relat_1(sK3,sK2) = k7_relat_1(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_5168])).

cnf(c_37,negated_conjecture,
    ( r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1834,plain,
    ( r1_tarski(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_5851,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) = sK2
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1834,c_5842])).

cnf(c_32,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1835,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_6237,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5851,c_1835])).

cnf(c_1836,plain,
    ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_6334,plain,
    ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0)
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1833,c_1836])).

cnf(c_6656,plain,
    ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6334,c_40,c_38,c_2309])).

cnf(c_30,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1837,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_5294,plain,
    ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1833,c_1837])).

cnf(c_41,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_43,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_2249,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_funct_1(k2_partfun1(X0,X1,sK3,X2))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_2301,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2249])).

cnf(c_2302,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2301])).

cnf(c_5493,plain,
    ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5294,c_41,c_43,c_2302])).

cnf(c_6665,plain,
    ( v1_funct_1(k7_relat_1(sK3,X0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6656,c_5493])).

cnf(c_10054,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6237,c_6665])).

cnf(c_33,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_35,negated_conjecture,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_693,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | ~ v1_relat_1(X0)
    | k2_partfun1(sK0,sK1,sK3,sK2) != X0
    | k1_relat_1(X0) != sK2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_33,c_35])).

cnf(c_694,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK1)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | ~ v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2 ),
    inference(unflattening,[status(thm)],[c_693])).

cnf(c_19,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_11,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_482,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_19,c_11])).

cnf(c_706,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | ~ v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_694,c_482])).

cnf(c_1820,plain,
    ( k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top
    | v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_706])).

cnf(c_6662,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6656,c_1820])).

cnf(c_6688,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6662,c_6665])).

cnf(c_18928,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5851,c_6688])).

cnf(c_18936,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_10054,c_18928])).

cnf(c_18,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(X0,X1)),k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1841,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(X0,X1)),k2_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1829,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_482])).

cnf(c_4184,plain,
    ( r1_tarski(k2_relat_1(sK3),sK1) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1833,c_1829])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X0)
    | r1_tarski(X2,X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1849,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,X0) != iProver_top
    | r1_tarski(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_4620,plain,
    ( r1_tarski(X0,k2_relat_1(sK3)) != iProver_top
    | r1_tarski(X0,sK1) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4184,c_1849])).

cnf(c_5182,plain,
    ( r1_tarski(X0,sK1) = iProver_top
    | r1_tarski(X0,k2_relat_1(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4620,c_4772])).

cnf(c_5183,plain,
    ( r1_tarski(X0,k2_relat_1(sK3)) != iProver_top
    | r1_tarski(X0,sK1) = iProver_top ),
    inference(renaming,[status(thm)],[c_5182])).

cnf(c_5191,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1841,c_5183])).

cnf(c_10812,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5191,c_4772])).

cnf(c_20246,plain,
    ( sK1 = k1_xboole_0
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_18936,c_10812])).

cnf(c_20247,plain,
    ( ~ v1_relat_1(k7_relat_1(sK3,sK2))
    | sK1 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_20246])).

cnf(c_21936,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_22406,plain,
    ( sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5854,c_40,c_38,c_3354,c_7161,c_7162,c_9562,c_11130,c_11131,c_13785,c_20247,c_21936])).

cnf(c_712,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != sK3
    | sK2 != sK0
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_35,c_39])).

cnf(c_819,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != sK3
    | sK2 != sK0 ),
    inference(equality_resolution_simp,[status(thm)],[c_712])).

cnf(c_1819,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != sK3
    | sK2 != sK0
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_819])).

cnf(c_6663,plain,
    ( k7_relat_1(sK3,sK2) != sK3
    | sK2 != sK0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6656,c_1819])).

cnf(c_6680,plain,
    ( k7_relat_1(sK3,sK2) != sK3
    | sK2 != sK0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6663,c_6665])).

cnf(c_22442,plain,
    ( k7_relat_1(sK3,sK2) != sK3
    | sK2 != sK0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_22406,c_6680])).

cnf(c_36,negated_conjecture,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f97])).

cnf(c_22492,plain,
    ( sK0 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_22406,c_36])).

cnf(c_22493,plain,
    ( sK0 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_22492])).

cnf(c_22672,plain,
    ( k7_relat_1(sK3,sK2) != sK3
    | sK2 != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_22442,c_22493])).

cnf(c_3,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f99])).

cnf(c_22676,plain,
    ( k7_relat_1(sK3,sK2) != sK3
    | sK2 != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_22672,c_3])).

cnf(c_22926,plain,
    ( r1_tarski(sK2,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_22493,c_1834])).

cnf(c_6,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1847,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_5212,plain,
    ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1847,c_1830])).

cnf(c_102,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_104,plain,
    ( v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_102])).

cnf(c_2167,plain,
    ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | v1_relat_1(X0) = iProver_top
    | v1_relat_1(k2_zfmisc_1(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2166])).

cnf(c_2169,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top
    | v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top
    | v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2167])).

cnf(c_2204,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2207,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2204])).

cnf(c_2209,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2207])).

cnf(c_2369,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(X0,k2_zfmisc_1(X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2368])).

cnf(c_2371,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2369])).

cnf(c_9499,plain,
    ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5212,c_104,c_2169,c_2209,c_2371])).

cnf(c_15,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_4412,plain,
    ( k1_relat_1(k7_relat_1(k1_xboole_0,X0)) = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_15,c_1842])).

cnf(c_4449,plain,
    ( r1_tarski(X0,k1_xboole_0) != iProver_top
    | k1_relat_1(k7_relat_1(k1_xboole_0,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4412,c_104,c_2169,c_2209,c_2371])).

cnf(c_4450,plain,
    ( k1_relat_1(k7_relat_1(k1_xboole_0,X0)) = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4449])).

cnf(c_9503,plain,
    ( k1_relat_1(k1_xboole_0) = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9499,c_4450])).

cnf(c_9515,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9503,c_15])).

cnf(c_23491,plain,
    ( sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_22926,c_9515])).

cnf(c_25731,plain,
    ( k7_relat_1(sK3,sK2) != sK3
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_22676,c_23491])).

cnf(c_22921,plain,
    ( k7_relat_1(sK3,k1_xboole_0) = sK3 ),
    inference(demodulation,[status(thm)],[c_22493,c_5477])).

cnf(c_4,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f100])).

cnf(c_1838,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_7318,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_6656,c_1838])).

cnf(c_8033,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7318,c_41,c_43])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ r1_tarski(k1_relat_1(X0),X3) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1839,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) = iProver_top
    | r1_tarski(k1_relat_1(X0),X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_8042,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) = iProver_top
    | r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_8033,c_1839])).

cnf(c_12457,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4,c_8042])).

cnf(c_13043,plain,
    ( m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1843,c_12457])).

cnf(c_13138,plain,
    ( m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13043,c_4772])).

cnf(c_13143,plain,
    ( r1_tarski(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_13138,c_1845])).

cnf(c_13448,plain,
    ( k7_relat_1(sK3,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_13143,c_9515])).

cnf(c_22942,plain,
    ( sK3 = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_22921,c_13448])).

cnf(c_25735,plain,
    ( k7_relat_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | m1_subset_1(k7_relat_1(k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_25731,c_22942,c_23491])).

cnf(c_25736,plain,
    ( k1_xboole_0 != k1_xboole_0
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_25735,c_9499])).

cnf(c_25737,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_25736])).

cnf(c_25739,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_25737,c_1847])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:08:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 6.57/1.54  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.57/1.54  
% 6.57/1.54  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 6.57/1.54  
% 6.57/1.54  ------  iProver source info
% 6.57/1.54  
% 6.57/1.54  git: date: 2020-06-30 10:37:57 +0100
% 6.57/1.54  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 6.57/1.54  git: non_committed_changes: false
% 6.57/1.54  git: last_make_outside_of_git: false
% 6.57/1.54  
% 6.57/1.54  ------ 
% 6.57/1.54  
% 6.57/1.54  ------ Input Options
% 6.57/1.54  
% 6.57/1.54  --out_options                           all
% 6.57/1.54  --tptp_safe_out                         true
% 6.57/1.54  --problem_path                          ""
% 6.57/1.54  --include_path                          ""
% 6.57/1.54  --clausifier                            res/vclausify_rel
% 6.57/1.54  --clausifier_options                    --mode clausify
% 6.57/1.54  --stdin                                 false
% 6.57/1.54  --stats_out                             all
% 6.57/1.54  
% 6.57/1.54  ------ General Options
% 6.57/1.54  
% 6.57/1.54  --fof                                   false
% 6.57/1.54  --time_out_real                         305.
% 6.57/1.54  --time_out_virtual                      -1.
% 6.57/1.54  --symbol_type_check                     false
% 6.57/1.54  --clausify_out                          false
% 6.57/1.54  --sig_cnt_out                           false
% 6.57/1.54  --trig_cnt_out                          false
% 6.57/1.54  --trig_cnt_out_tolerance                1.
% 6.57/1.54  --trig_cnt_out_sk_spl                   false
% 6.57/1.54  --abstr_cl_out                          false
% 6.57/1.54  
% 6.57/1.54  ------ Global Options
% 6.57/1.54  
% 6.57/1.54  --schedule                              default
% 6.57/1.54  --add_important_lit                     false
% 6.57/1.54  --prop_solver_per_cl                    1000
% 6.57/1.54  --min_unsat_core                        false
% 6.57/1.54  --soft_assumptions                      false
% 6.57/1.54  --soft_lemma_size                       3
% 6.57/1.54  --prop_impl_unit_size                   0
% 6.57/1.54  --prop_impl_unit                        []
% 6.57/1.54  --share_sel_clauses                     true
% 6.57/1.54  --reset_solvers                         false
% 6.57/1.54  --bc_imp_inh                            [conj_cone]
% 6.57/1.54  --conj_cone_tolerance                   3.
% 6.57/1.54  --extra_neg_conj                        none
% 6.57/1.54  --large_theory_mode                     true
% 6.57/1.54  --prolific_symb_bound                   200
% 6.57/1.54  --lt_threshold                          2000
% 6.57/1.54  --clause_weak_htbl                      true
% 6.57/1.54  --gc_record_bc_elim                     false
% 6.57/1.54  
% 6.57/1.54  ------ Preprocessing Options
% 6.57/1.54  
% 6.57/1.54  --preprocessing_flag                    true
% 6.57/1.54  --time_out_prep_mult                    0.1
% 6.57/1.54  --splitting_mode                        input
% 6.57/1.54  --splitting_grd                         true
% 6.57/1.54  --splitting_cvd                         false
% 6.57/1.54  --splitting_cvd_svl                     false
% 6.57/1.54  --splitting_nvd                         32
% 6.57/1.54  --sub_typing                            true
% 6.57/1.54  --prep_gs_sim                           true
% 6.57/1.54  --prep_unflatten                        true
% 6.57/1.54  --prep_res_sim                          true
% 6.57/1.54  --prep_upred                            true
% 6.57/1.54  --prep_sem_filter                       exhaustive
% 6.57/1.54  --prep_sem_filter_out                   false
% 6.57/1.54  --pred_elim                             true
% 6.57/1.54  --res_sim_input                         true
% 6.57/1.54  --eq_ax_congr_red                       true
% 6.57/1.54  --pure_diseq_elim                       true
% 6.57/1.54  --brand_transform                       false
% 6.57/1.54  --non_eq_to_eq                          false
% 6.57/1.54  --prep_def_merge                        true
% 6.57/1.54  --prep_def_merge_prop_impl              false
% 6.57/1.54  --prep_def_merge_mbd                    true
% 6.57/1.54  --prep_def_merge_tr_red                 false
% 6.57/1.54  --prep_def_merge_tr_cl                  false
% 6.57/1.54  --smt_preprocessing                     true
% 6.57/1.54  --smt_ac_axioms                         fast
% 6.57/1.54  --preprocessed_out                      false
% 6.57/1.54  --preprocessed_stats                    false
% 6.57/1.54  
% 6.57/1.54  ------ Abstraction refinement Options
% 6.57/1.54  
% 6.57/1.54  --abstr_ref                             []
% 6.57/1.54  --abstr_ref_prep                        false
% 6.57/1.54  --abstr_ref_until_sat                   false
% 6.57/1.54  --abstr_ref_sig_restrict                funpre
% 6.57/1.54  --abstr_ref_af_restrict_to_split_sk     false
% 6.57/1.54  --abstr_ref_under                       []
% 6.57/1.54  
% 6.57/1.54  ------ SAT Options
% 6.57/1.54  
% 6.57/1.54  --sat_mode                              false
% 6.57/1.54  --sat_fm_restart_options                ""
% 6.57/1.54  --sat_gr_def                            false
% 6.57/1.54  --sat_epr_types                         true
% 6.57/1.54  --sat_non_cyclic_types                  false
% 6.57/1.54  --sat_finite_models                     false
% 6.57/1.54  --sat_fm_lemmas                         false
% 6.57/1.54  --sat_fm_prep                           false
% 6.57/1.54  --sat_fm_uc_incr                        true
% 6.57/1.54  --sat_out_model                         small
% 6.57/1.54  --sat_out_clauses                       false
% 6.57/1.54  
% 6.57/1.54  ------ QBF Options
% 6.57/1.54  
% 6.57/1.54  --qbf_mode                              false
% 6.57/1.54  --qbf_elim_univ                         false
% 6.57/1.54  --qbf_dom_inst                          none
% 6.57/1.54  --qbf_dom_pre_inst                      false
% 6.57/1.54  --qbf_sk_in                             false
% 6.57/1.54  --qbf_pred_elim                         true
% 6.57/1.54  --qbf_split                             512
% 6.57/1.54  
% 6.57/1.54  ------ BMC1 Options
% 6.57/1.54  
% 6.57/1.54  --bmc1_incremental                      false
% 6.57/1.54  --bmc1_axioms                           reachable_all
% 6.57/1.54  --bmc1_min_bound                        0
% 6.57/1.54  --bmc1_max_bound                        -1
% 6.57/1.54  --bmc1_max_bound_default                -1
% 6.57/1.54  --bmc1_symbol_reachability              true
% 6.57/1.54  --bmc1_property_lemmas                  false
% 6.57/1.54  --bmc1_k_induction                      false
% 6.57/1.54  --bmc1_non_equiv_states                 false
% 6.57/1.54  --bmc1_deadlock                         false
% 6.57/1.54  --bmc1_ucm                              false
% 6.57/1.54  --bmc1_add_unsat_core                   none
% 6.57/1.54  --bmc1_unsat_core_children              false
% 6.57/1.54  --bmc1_unsat_core_extrapolate_axioms    false
% 6.57/1.54  --bmc1_out_stat                         full
% 6.57/1.54  --bmc1_ground_init                      false
% 6.57/1.54  --bmc1_pre_inst_next_state              false
% 6.57/1.54  --bmc1_pre_inst_state                   false
% 6.57/1.54  --bmc1_pre_inst_reach_state             false
% 6.57/1.54  --bmc1_out_unsat_core                   false
% 6.57/1.54  --bmc1_aig_witness_out                  false
% 6.57/1.54  --bmc1_verbose                          false
% 6.57/1.54  --bmc1_dump_clauses_tptp                false
% 6.57/1.54  --bmc1_dump_unsat_core_tptp             false
% 6.57/1.54  --bmc1_dump_file                        -
% 6.57/1.54  --bmc1_ucm_expand_uc_limit              128
% 6.57/1.54  --bmc1_ucm_n_expand_iterations          6
% 6.57/1.54  --bmc1_ucm_extend_mode                  1
% 6.57/1.54  --bmc1_ucm_init_mode                    2
% 6.57/1.54  --bmc1_ucm_cone_mode                    none
% 6.57/1.54  --bmc1_ucm_reduced_relation_type        0
% 6.57/1.54  --bmc1_ucm_relax_model                  4
% 6.57/1.54  --bmc1_ucm_full_tr_after_sat            true
% 6.57/1.54  --bmc1_ucm_expand_neg_assumptions       false
% 6.57/1.54  --bmc1_ucm_layered_model                none
% 6.57/1.54  --bmc1_ucm_max_lemma_size               10
% 6.57/1.54  
% 6.57/1.54  ------ AIG Options
% 6.57/1.54  
% 6.57/1.54  --aig_mode                              false
% 6.57/1.54  
% 6.57/1.54  ------ Instantiation Options
% 6.57/1.54  
% 6.57/1.54  --instantiation_flag                    true
% 6.57/1.54  --inst_sos_flag                         false
% 6.57/1.54  --inst_sos_phase                        true
% 6.57/1.54  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.57/1.54  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.57/1.54  --inst_lit_sel_side                     num_symb
% 6.57/1.54  --inst_solver_per_active                1400
% 6.57/1.54  --inst_solver_calls_frac                1.
% 6.57/1.54  --inst_passive_queue_type               priority_queues
% 6.57/1.54  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.57/1.54  --inst_passive_queues_freq              [25;2]
% 6.57/1.54  --inst_dismatching                      true
% 6.57/1.54  --inst_eager_unprocessed_to_passive     true
% 6.57/1.54  --inst_prop_sim_given                   true
% 6.57/1.54  --inst_prop_sim_new                     false
% 6.57/1.54  --inst_subs_new                         false
% 6.57/1.54  --inst_eq_res_simp                      false
% 6.57/1.54  --inst_subs_given                       false
% 6.57/1.54  --inst_orphan_elimination               true
% 6.57/1.54  --inst_learning_loop_flag               true
% 6.57/1.54  --inst_learning_start                   3000
% 6.57/1.54  --inst_learning_factor                  2
% 6.57/1.54  --inst_start_prop_sim_after_learn       3
% 6.57/1.54  --inst_sel_renew                        solver
% 6.57/1.54  --inst_lit_activity_flag                true
% 6.57/1.54  --inst_restr_to_given                   false
% 6.57/1.54  --inst_activity_threshold               500
% 6.57/1.54  --inst_out_proof                        true
% 6.57/1.54  
% 6.57/1.54  ------ Resolution Options
% 6.57/1.54  
% 6.57/1.54  --resolution_flag                       true
% 6.57/1.54  --res_lit_sel                           adaptive
% 6.57/1.54  --res_lit_sel_side                      none
% 6.57/1.54  --res_ordering                          kbo
% 6.57/1.54  --res_to_prop_solver                    active
% 6.57/1.54  --res_prop_simpl_new                    false
% 6.57/1.54  --res_prop_simpl_given                  true
% 6.57/1.54  --res_passive_queue_type                priority_queues
% 6.57/1.54  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.57/1.54  --res_passive_queues_freq               [15;5]
% 6.57/1.54  --res_forward_subs                      full
% 6.57/1.54  --res_backward_subs                     full
% 6.57/1.54  --res_forward_subs_resolution           true
% 6.57/1.54  --res_backward_subs_resolution          true
% 6.57/1.54  --res_orphan_elimination                true
% 6.57/1.54  --res_time_limit                        2.
% 6.57/1.54  --res_out_proof                         true
% 6.57/1.54  
% 6.57/1.54  ------ Superposition Options
% 6.57/1.54  
% 6.57/1.54  --superposition_flag                    true
% 6.57/1.54  --sup_passive_queue_type                priority_queues
% 6.57/1.54  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.57/1.54  --sup_passive_queues_freq               [8;1;4]
% 6.57/1.54  --demod_completeness_check              fast
% 6.57/1.54  --demod_use_ground                      true
% 6.57/1.54  --sup_to_prop_solver                    passive
% 6.57/1.54  --sup_prop_simpl_new                    true
% 6.57/1.54  --sup_prop_simpl_given                  true
% 6.57/1.54  --sup_fun_splitting                     false
% 6.57/1.54  --sup_smt_interval                      50000
% 6.57/1.54  
% 6.57/1.54  ------ Superposition Simplification Setup
% 6.57/1.54  
% 6.57/1.54  --sup_indices_passive                   []
% 6.57/1.54  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.57/1.54  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.57/1.54  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.57/1.54  --sup_full_triv                         [TrivRules;PropSubs]
% 6.57/1.54  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.57/1.54  --sup_full_bw                           [BwDemod]
% 6.57/1.54  --sup_immed_triv                        [TrivRules]
% 6.57/1.54  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.57/1.54  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.57/1.54  --sup_immed_bw_main                     []
% 6.57/1.54  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.57/1.54  --sup_input_triv                        [Unflattening;TrivRules]
% 6.57/1.54  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.57/1.54  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.57/1.54  
% 6.57/1.54  ------ Combination Options
% 6.57/1.54  
% 6.57/1.54  --comb_res_mult                         3
% 6.57/1.54  --comb_sup_mult                         2
% 6.57/1.54  --comb_inst_mult                        10
% 6.57/1.54  
% 6.57/1.54  ------ Debug Options
% 6.57/1.54  
% 6.57/1.54  --dbg_backtrace                         false
% 6.57/1.54  --dbg_dump_prop_clauses                 false
% 6.57/1.54  --dbg_dump_prop_clauses_file            -
% 6.57/1.54  --dbg_out_stat                          false
% 6.57/1.54  ------ Parsing...
% 6.57/1.54  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 6.57/1.54  
% 6.57/1.54  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 6.57/1.54  
% 6.57/1.54  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 6.57/1.54  
% 6.57/1.54  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 6.57/1.54  ------ Proving...
% 6.57/1.54  ------ Problem Properties 
% 6.57/1.54  
% 6.57/1.54  
% 6.57/1.54  clauses                                 39
% 6.57/1.54  conjectures                             4
% 6.57/1.54  EPR                                     7
% 6.57/1.54  Horn                                    34
% 6.57/1.54  unary                                   10
% 6.57/1.54  binary                                  7
% 6.57/1.54  lits                                    105
% 6.57/1.54  lits eq                                 37
% 6.57/1.54  fd_pure                                 0
% 6.57/1.54  fd_pseudo                               0
% 6.57/1.54  fd_cond                                 3
% 6.57/1.54  fd_pseudo_cond                          1
% 6.57/1.54  AC symbols                              0
% 6.57/1.54  
% 6.57/1.54  ------ Schedule dynamic 5 is on 
% 6.57/1.54  
% 6.57/1.54  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 6.57/1.54  
% 6.57/1.54  
% 6.57/1.54  ------ 
% 6.57/1.54  Current options:
% 6.57/1.54  ------ 
% 6.57/1.54  
% 6.57/1.54  ------ Input Options
% 6.57/1.54  
% 6.57/1.54  --out_options                           all
% 6.57/1.54  --tptp_safe_out                         true
% 6.57/1.54  --problem_path                          ""
% 6.57/1.54  --include_path                          ""
% 6.57/1.54  --clausifier                            res/vclausify_rel
% 6.57/1.54  --clausifier_options                    --mode clausify
% 6.57/1.54  --stdin                                 false
% 6.57/1.54  --stats_out                             all
% 6.57/1.54  
% 6.57/1.54  ------ General Options
% 6.57/1.54  
% 6.57/1.54  --fof                                   false
% 6.57/1.54  --time_out_real                         305.
% 6.57/1.54  --time_out_virtual                      -1.
% 6.57/1.54  --symbol_type_check                     false
% 6.57/1.54  --clausify_out                          false
% 6.57/1.54  --sig_cnt_out                           false
% 6.57/1.54  --trig_cnt_out                          false
% 6.57/1.54  --trig_cnt_out_tolerance                1.
% 6.57/1.54  --trig_cnt_out_sk_spl                   false
% 6.57/1.54  --abstr_cl_out                          false
% 6.57/1.54  
% 6.57/1.54  ------ Global Options
% 6.57/1.54  
% 6.57/1.54  --schedule                              default
% 6.57/1.54  --add_important_lit                     false
% 6.57/1.54  --prop_solver_per_cl                    1000
% 6.57/1.54  --min_unsat_core                        false
% 6.57/1.54  --soft_assumptions                      false
% 6.57/1.54  --soft_lemma_size                       3
% 6.57/1.54  --prop_impl_unit_size                   0
% 6.57/1.54  --prop_impl_unit                        []
% 6.57/1.54  --share_sel_clauses                     true
% 6.57/1.54  --reset_solvers                         false
% 6.57/1.54  --bc_imp_inh                            [conj_cone]
% 6.57/1.54  --conj_cone_tolerance                   3.
% 6.57/1.54  --extra_neg_conj                        none
% 6.57/1.54  --large_theory_mode                     true
% 6.57/1.54  --prolific_symb_bound                   200
% 6.57/1.54  --lt_threshold                          2000
% 6.57/1.54  --clause_weak_htbl                      true
% 6.57/1.54  --gc_record_bc_elim                     false
% 6.57/1.54  
% 6.57/1.54  ------ Preprocessing Options
% 6.57/1.54  
% 6.57/1.54  --preprocessing_flag                    true
% 6.57/1.54  --time_out_prep_mult                    0.1
% 6.57/1.54  --splitting_mode                        input
% 6.57/1.54  --splitting_grd                         true
% 6.57/1.54  --splitting_cvd                         false
% 6.57/1.54  --splitting_cvd_svl                     false
% 6.57/1.54  --splitting_nvd                         32
% 6.57/1.54  --sub_typing                            true
% 6.57/1.54  --prep_gs_sim                           true
% 6.57/1.54  --prep_unflatten                        true
% 6.57/1.54  --prep_res_sim                          true
% 6.57/1.54  --prep_upred                            true
% 6.57/1.54  --prep_sem_filter                       exhaustive
% 6.57/1.54  --prep_sem_filter_out                   false
% 6.57/1.54  --pred_elim                             true
% 6.57/1.54  --res_sim_input                         true
% 6.57/1.54  --eq_ax_congr_red                       true
% 6.57/1.54  --pure_diseq_elim                       true
% 6.57/1.54  --brand_transform                       false
% 6.57/1.54  --non_eq_to_eq                          false
% 6.57/1.54  --prep_def_merge                        true
% 6.57/1.54  --prep_def_merge_prop_impl              false
% 6.57/1.54  --prep_def_merge_mbd                    true
% 6.57/1.54  --prep_def_merge_tr_red                 false
% 6.57/1.54  --prep_def_merge_tr_cl                  false
% 6.57/1.54  --smt_preprocessing                     true
% 6.57/1.54  --smt_ac_axioms                         fast
% 6.57/1.54  --preprocessed_out                      false
% 6.57/1.54  --preprocessed_stats                    false
% 6.57/1.54  
% 6.57/1.54  ------ Abstraction refinement Options
% 6.57/1.54  
% 6.57/1.54  --abstr_ref                             []
% 6.57/1.54  --abstr_ref_prep                        false
% 6.57/1.54  --abstr_ref_until_sat                   false
% 6.57/1.54  --abstr_ref_sig_restrict                funpre
% 6.57/1.54  --abstr_ref_af_restrict_to_split_sk     false
% 6.57/1.54  --abstr_ref_under                       []
% 6.57/1.54  
% 6.57/1.54  ------ SAT Options
% 6.57/1.54  
% 6.57/1.54  --sat_mode                              false
% 6.57/1.54  --sat_fm_restart_options                ""
% 6.57/1.54  --sat_gr_def                            false
% 6.57/1.54  --sat_epr_types                         true
% 6.57/1.54  --sat_non_cyclic_types                  false
% 6.57/1.54  --sat_finite_models                     false
% 6.57/1.54  --sat_fm_lemmas                         false
% 6.57/1.54  --sat_fm_prep                           false
% 6.57/1.54  --sat_fm_uc_incr                        true
% 6.57/1.54  --sat_out_model                         small
% 6.57/1.54  --sat_out_clauses                       false
% 6.57/1.54  
% 6.57/1.54  ------ QBF Options
% 6.57/1.54  
% 6.57/1.54  --qbf_mode                              false
% 6.57/1.54  --qbf_elim_univ                         false
% 6.57/1.54  --qbf_dom_inst                          none
% 6.57/1.54  --qbf_dom_pre_inst                      false
% 6.57/1.54  --qbf_sk_in                             false
% 6.57/1.54  --qbf_pred_elim                         true
% 6.57/1.54  --qbf_split                             512
% 6.57/1.54  
% 6.57/1.54  ------ BMC1 Options
% 6.57/1.54  
% 6.57/1.54  --bmc1_incremental                      false
% 6.57/1.54  --bmc1_axioms                           reachable_all
% 6.57/1.54  --bmc1_min_bound                        0
% 6.57/1.54  --bmc1_max_bound                        -1
% 6.57/1.54  --bmc1_max_bound_default                -1
% 6.57/1.54  --bmc1_symbol_reachability              true
% 6.57/1.54  --bmc1_property_lemmas                  false
% 6.57/1.54  --bmc1_k_induction                      false
% 6.57/1.54  --bmc1_non_equiv_states                 false
% 6.57/1.54  --bmc1_deadlock                         false
% 6.57/1.54  --bmc1_ucm                              false
% 6.57/1.54  --bmc1_add_unsat_core                   none
% 6.57/1.54  --bmc1_unsat_core_children              false
% 6.57/1.54  --bmc1_unsat_core_extrapolate_axioms    false
% 6.57/1.54  --bmc1_out_stat                         full
% 6.57/1.54  --bmc1_ground_init                      false
% 6.57/1.54  --bmc1_pre_inst_next_state              false
% 6.57/1.54  --bmc1_pre_inst_state                   false
% 6.57/1.54  --bmc1_pre_inst_reach_state             false
% 6.57/1.54  --bmc1_out_unsat_core                   false
% 6.57/1.54  --bmc1_aig_witness_out                  false
% 6.57/1.54  --bmc1_verbose                          false
% 6.57/1.54  --bmc1_dump_clauses_tptp                false
% 6.57/1.54  --bmc1_dump_unsat_core_tptp             false
% 6.57/1.54  --bmc1_dump_file                        -
% 6.57/1.54  --bmc1_ucm_expand_uc_limit              128
% 6.57/1.54  --bmc1_ucm_n_expand_iterations          6
% 6.57/1.54  --bmc1_ucm_extend_mode                  1
% 6.57/1.54  --bmc1_ucm_init_mode                    2
% 6.57/1.54  --bmc1_ucm_cone_mode                    none
% 6.57/1.54  --bmc1_ucm_reduced_relation_type        0
% 6.57/1.54  --bmc1_ucm_relax_model                  4
% 6.57/1.54  --bmc1_ucm_full_tr_after_sat            true
% 6.57/1.54  --bmc1_ucm_expand_neg_assumptions       false
% 6.57/1.54  --bmc1_ucm_layered_model                none
% 6.57/1.54  --bmc1_ucm_max_lemma_size               10
% 6.57/1.54  
% 6.57/1.54  ------ AIG Options
% 6.57/1.54  
% 6.57/1.54  --aig_mode                              false
% 6.57/1.54  
% 6.57/1.54  ------ Instantiation Options
% 6.57/1.54  
% 6.57/1.54  --instantiation_flag                    true
% 6.57/1.54  --inst_sos_flag                         false
% 6.57/1.54  --inst_sos_phase                        true
% 6.57/1.54  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.57/1.54  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.57/1.54  --inst_lit_sel_side                     none
% 6.57/1.54  --inst_solver_per_active                1400
% 6.57/1.54  --inst_solver_calls_frac                1.
% 6.57/1.54  --inst_passive_queue_type               priority_queues
% 6.57/1.54  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.57/1.54  --inst_passive_queues_freq              [25;2]
% 6.57/1.54  --inst_dismatching                      true
% 6.57/1.54  --inst_eager_unprocessed_to_passive     true
% 6.57/1.54  --inst_prop_sim_given                   true
% 6.57/1.54  --inst_prop_sim_new                     false
% 6.57/1.54  --inst_subs_new                         false
% 6.57/1.54  --inst_eq_res_simp                      false
% 6.57/1.54  --inst_subs_given                       false
% 6.57/1.54  --inst_orphan_elimination               true
% 6.57/1.54  --inst_learning_loop_flag               true
% 6.57/1.54  --inst_learning_start                   3000
% 6.57/1.54  --inst_learning_factor                  2
% 6.57/1.54  --inst_start_prop_sim_after_learn       3
% 6.57/1.54  --inst_sel_renew                        solver
% 6.57/1.54  --inst_lit_activity_flag                true
% 6.57/1.54  --inst_restr_to_given                   false
% 6.57/1.54  --inst_activity_threshold               500
% 6.57/1.54  --inst_out_proof                        true
% 6.57/1.54  
% 6.57/1.54  ------ Resolution Options
% 6.57/1.54  
% 6.57/1.54  --resolution_flag                       false
% 6.57/1.54  --res_lit_sel                           adaptive
% 6.57/1.54  --res_lit_sel_side                      none
% 6.57/1.54  --res_ordering                          kbo
% 6.57/1.54  --res_to_prop_solver                    active
% 6.57/1.54  --res_prop_simpl_new                    false
% 6.57/1.54  --res_prop_simpl_given                  true
% 6.57/1.54  --res_passive_queue_type                priority_queues
% 6.57/1.54  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.57/1.54  --res_passive_queues_freq               [15;5]
% 6.57/1.54  --res_forward_subs                      full
% 6.57/1.54  --res_backward_subs                     full
% 6.57/1.54  --res_forward_subs_resolution           true
% 6.57/1.54  --res_backward_subs_resolution          true
% 6.57/1.54  --res_orphan_elimination                true
% 6.57/1.54  --res_time_limit                        2.
% 6.57/1.54  --res_out_proof                         true
% 6.57/1.54  
% 6.57/1.54  ------ Superposition Options
% 6.57/1.54  
% 6.57/1.54  --superposition_flag                    true
% 6.57/1.54  --sup_passive_queue_type                priority_queues
% 6.57/1.54  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.57/1.54  --sup_passive_queues_freq               [8;1;4]
% 6.57/1.54  --demod_completeness_check              fast
% 6.57/1.54  --demod_use_ground                      true
% 6.57/1.54  --sup_to_prop_solver                    passive
% 6.57/1.54  --sup_prop_simpl_new                    true
% 6.57/1.54  --sup_prop_simpl_given                  true
% 6.57/1.54  --sup_fun_splitting                     false
% 6.57/1.54  --sup_smt_interval                      50000
% 6.57/1.54  
% 6.57/1.54  ------ Superposition Simplification Setup
% 6.57/1.54  
% 6.57/1.54  --sup_indices_passive                   []
% 6.57/1.54  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.57/1.54  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.57/1.54  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.57/1.54  --sup_full_triv                         [TrivRules;PropSubs]
% 6.57/1.54  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.57/1.54  --sup_full_bw                           [BwDemod]
% 6.57/1.54  --sup_immed_triv                        [TrivRules]
% 6.57/1.54  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.57/1.54  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.57/1.54  --sup_immed_bw_main                     []
% 6.57/1.54  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.57/1.54  --sup_input_triv                        [Unflattening;TrivRules]
% 6.57/1.54  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.57/1.54  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.57/1.54  
% 6.57/1.54  ------ Combination Options
% 6.57/1.54  
% 6.57/1.54  --comb_res_mult                         3
% 6.57/1.54  --comb_sup_mult                         2
% 6.57/1.54  --comb_inst_mult                        10
% 6.57/1.54  
% 6.57/1.54  ------ Debug Options
% 6.57/1.54  
% 6.57/1.54  --dbg_backtrace                         false
% 6.57/1.54  --dbg_dump_prop_clauses                 false
% 6.57/1.54  --dbg_dump_prop_clauses_file            -
% 6.57/1.54  --dbg_out_stat                          false
% 6.57/1.54  
% 6.57/1.54  
% 6.57/1.54  
% 6.57/1.54  
% 6.57/1.54  ------ Proving...
% 6.57/1.54  
% 6.57/1.54  
% 6.57/1.54  % SZS status Theorem for theBenchmark.p
% 6.57/1.54  
% 6.57/1.54   Resolution empty clause
% 6.57/1.54  
% 6.57/1.54  % SZS output start CNFRefutation for theBenchmark.p
% 6.57/1.54  
% 6.57/1.54  fof(f23,conjecture,(
% 6.57/1.54    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 6.57/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.57/1.54  
% 6.57/1.54  fof(f24,negated_conjecture,(
% 6.57/1.54    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 6.57/1.54    inference(negated_conjecture,[],[f23])).
% 6.57/1.54  
% 6.57/1.54  fof(f49,plain,(
% 6.57/1.54    ? [X0,X1,X2,X3] : ((((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 6.57/1.54    inference(ennf_transformation,[],[f24])).
% 6.57/1.54  
% 6.57/1.54  fof(f50,plain,(
% 6.57/1.54    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 6.57/1.54    inference(flattening,[],[f49])).
% 6.57/1.54  
% 6.57/1.54  fof(f56,plain,(
% 6.57/1.54    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 6.57/1.54    introduced(choice_axiom,[])).
% 6.57/1.54  
% 6.57/1.54  fof(f57,plain,(
% 6.57/1.54    (~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 6.57/1.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f50,f56])).
% 6.57/1.54  
% 6.57/1.54  fof(f95,plain,(
% 6.57/1.54    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 6.57/1.54    inference(cnf_transformation,[],[f57])).
% 6.57/1.54  
% 6.57/1.54  fof(f16,axiom,(
% 6.57/1.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 6.57/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.57/1.54  
% 6.57/1.54  fof(f37,plain,(
% 6.57/1.54    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.57/1.54    inference(ennf_transformation,[],[f16])).
% 6.57/1.54  
% 6.57/1.54  fof(f77,plain,(
% 6.57/1.54    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.57/1.54    inference(cnf_transformation,[],[f37])).
% 6.57/1.54  
% 6.57/1.54  fof(f11,axiom,(
% 6.57/1.54    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 6.57/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.57/1.54  
% 6.57/1.54  fof(f31,plain,(
% 6.57/1.54    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 6.57/1.54    inference(ennf_transformation,[],[f11])).
% 6.57/1.54  
% 6.57/1.54  fof(f32,plain,(
% 6.57/1.54    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 6.57/1.54    inference(flattening,[],[f31])).
% 6.57/1.54  
% 6.57/1.54  fof(f71,plain,(
% 6.57/1.54    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 6.57/1.54    inference(cnf_transformation,[],[f32])).
% 6.57/1.54  
% 6.57/1.54  fof(f6,axiom,(
% 6.57/1.54    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 6.57/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.57/1.54  
% 6.57/1.54  fof(f53,plain,(
% 6.57/1.54    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 6.57/1.54    inference(nnf_transformation,[],[f6])).
% 6.57/1.54  
% 6.57/1.54  fof(f65,plain,(
% 6.57/1.54    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 6.57/1.54    inference(cnf_transformation,[],[f53])).
% 6.57/1.54  
% 6.57/1.54  fof(f8,axiom,(
% 6.57/1.54    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 6.57/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.57/1.54  
% 6.57/1.54  fof(f29,plain,(
% 6.57/1.54    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 6.57/1.54    inference(ennf_transformation,[],[f8])).
% 6.57/1.54  
% 6.57/1.54  fof(f67,plain,(
% 6.57/1.54    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 6.57/1.54    inference(cnf_transformation,[],[f29])).
% 6.57/1.54  
% 6.57/1.54  fof(f66,plain,(
% 6.57/1.54    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 6.57/1.54    inference(cnf_transformation,[],[f53])).
% 6.57/1.54  
% 6.57/1.54  fof(f10,axiom,(
% 6.57/1.54    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 6.57/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.57/1.54  
% 6.57/1.54  fof(f70,plain,(
% 6.57/1.54    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 6.57/1.54    inference(cnf_transformation,[],[f10])).
% 6.57/1.54  
% 6.57/1.54  fof(f13,axiom,(
% 6.57/1.54    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 6.57/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.57/1.54  
% 6.57/1.54  fof(f33,plain,(
% 6.57/1.54    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 6.57/1.54    inference(ennf_transformation,[],[f13])).
% 6.57/1.54  
% 6.57/1.54  fof(f74,plain,(
% 6.57/1.54    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 6.57/1.54    inference(cnf_transformation,[],[f33])).
% 6.57/1.54  
% 6.57/1.54  fof(f19,axiom,(
% 6.57/1.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 6.57/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.57/1.54  
% 6.57/1.54  fof(f41,plain,(
% 6.57/1.54    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.57/1.54    inference(ennf_transformation,[],[f19])).
% 6.57/1.54  
% 6.57/1.54  fof(f42,plain,(
% 6.57/1.54    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.57/1.54    inference(flattening,[],[f41])).
% 6.57/1.54  
% 6.57/1.54  fof(f55,plain,(
% 6.57/1.54    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.57/1.54    inference(nnf_transformation,[],[f42])).
% 6.57/1.54  
% 6.57/1.54  fof(f81,plain,(
% 6.57/1.54    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.57/1.54    inference(cnf_transformation,[],[f55])).
% 6.57/1.54  
% 6.57/1.54  fof(f94,plain,(
% 6.57/1.54    v1_funct_2(sK3,sK0,sK1)),
% 6.57/1.54    inference(cnf_transformation,[],[f57])).
% 6.57/1.54  
% 6.57/1.54  fof(f17,axiom,(
% 6.57/1.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 6.57/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.57/1.54  
% 6.57/1.54  fof(f38,plain,(
% 6.57/1.54    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.57/1.54    inference(ennf_transformation,[],[f17])).
% 6.57/1.54  
% 6.57/1.54  fof(f79,plain,(
% 6.57/1.54    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.57/1.54    inference(cnf_transformation,[],[f38])).
% 6.57/1.54  
% 6.57/1.54  fof(f14,axiom,(
% 6.57/1.54    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 6.57/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.57/1.54  
% 6.57/1.54  fof(f34,plain,(
% 6.57/1.54    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 6.57/1.54    inference(ennf_transformation,[],[f14])).
% 6.57/1.54  
% 6.57/1.54  fof(f35,plain,(
% 6.57/1.54    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 6.57/1.54    inference(flattening,[],[f34])).
% 6.57/1.54  
% 6.57/1.54  fof(f75,plain,(
% 6.57/1.54    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 6.57/1.54    inference(cnf_transformation,[],[f35])).
% 6.57/1.54  
% 6.57/1.54  fof(f93,plain,(
% 6.57/1.54    v1_funct_1(sK3)),
% 6.57/1.54    inference(cnf_transformation,[],[f57])).
% 6.57/1.54  
% 6.57/1.54  fof(f21,axiom,(
% 6.57/1.54    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 6.57/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.57/1.54  
% 6.57/1.54  fof(f45,plain,(
% 6.57/1.54    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 6.57/1.54    inference(ennf_transformation,[],[f21])).
% 6.57/1.54  
% 6.57/1.54  fof(f46,plain,(
% 6.57/1.54    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 6.57/1.54    inference(flattening,[],[f45])).
% 6.57/1.54  
% 6.57/1.54  fof(f89,plain,(
% 6.57/1.54    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 6.57/1.54    inference(cnf_transformation,[],[f46])).
% 6.57/1.54  
% 6.57/1.54  fof(f20,axiom,(
% 6.57/1.54    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 6.57/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.57/1.54  
% 6.57/1.54  fof(f43,plain,(
% 6.57/1.54    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 6.57/1.54    inference(ennf_transformation,[],[f20])).
% 6.57/1.54  
% 6.57/1.54  fof(f44,plain,(
% 6.57/1.54    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 6.57/1.54    inference(flattening,[],[f43])).
% 6.57/1.54  
% 6.57/1.54  fof(f88,plain,(
% 6.57/1.54    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 6.57/1.54    inference(cnf_transformation,[],[f44])).
% 6.57/1.54  
% 6.57/1.54  fof(f96,plain,(
% 6.57/1.54    r1_tarski(sK2,sK0)),
% 6.57/1.54    inference(cnf_transformation,[],[f57])).
% 6.57/1.54  
% 6.57/1.54  fof(f22,axiom,(
% 6.57/1.54    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 6.57/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.57/1.54  
% 6.57/1.54  fof(f47,plain,(
% 6.57/1.54    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 6.57/1.54    inference(ennf_transformation,[],[f22])).
% 6.57/1.54  
% 6.57/1.54  fof(f48,plain,(
% 6.57/1.54    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 6.57/1.54    inference(flattening,[],[f47])).
% 6.57/1.54  
% 6.57/1.54  fof(f92,plain,(
% 6.57/1.54    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 6.57/1.54    inference(cnf_transformation,[],[f48])).
% 6.57/1.54  
% 6.57/1.54  fof(f87,plain,(
% 6.57/1.54    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_partfun1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 6.57/1.54    inference(cnf_transformation,[],[f44])).
% 6.57/1.54  
% 6.57/1.54  fof(f91,plain,(
% 6.57/1.54    ( ! [X0,X1] : (v1_funct_2(X1,k1_relat_1(X1),X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 6.57/1.54    inference(cnf_transformation,[],[f48])).
% 6.57/1.54  
% 6.57/1.54  fof(f98,plain,(
% 6.57/1.54    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 6.57/1.54    inference(cnf_transformation,[],[f57])).
% 6.57/1.54  
% 6.57/1.54  fof(f78,plain,(
% 6.57/1.54    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.57/1.54    inference(cnf_transformation,[],[f37])).
% 6.57/1.54  
% 6.57/1.54  fof(f9,axiom,(
% 6.57/1.54    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 6.57/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.57/1.54  
% 6.57/1.54  fof(f30,plain,(
% 6.57/1.54    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 6.57/1.54    inference(ennf_transformation,[],[f9])).
% 6.57/1.54  
% 6.57/1.54  fof(f54,plain,(
% 6.57/1.54    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 6.57/1.54    inference(nnf_transformation,[],[f30])).
% 6.57/1.54  
% 6.57/1.54  fof(f68,plain,(
% 6.57/1.54    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 6.57/1.54    inference(cnf_transformation,[],[f54])).
% 6.57/1.54  
% 6.57/1.54  fof(f15,axiom,(
% 6.57/1.54    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)))),
% 6.57/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.57/1.54  
% 6.57/1.54  fof(f36,plain,(
% 6.57/1.54    ! [X0,X1] : (r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 6.57/1.54    inference(ennf_transformation,[],[f15])).
% 6.57/1.54  
% 6.57/1.54  fof(f76,plain,(
% 6.57/1.54    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 6.57/1.54    inference(cnf_transformation,[],[f36])).
% 6.57/1.54  
% 6.57/1.54  fof(f2,axiom,(
% 6.57/1.54    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 6.57/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.57/1.54  
% 6.57/1.54  fof(f26,plain,(
% 6.57/1.54    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 6.57/1.54    inference(ennf_transformation,[],[f2])).
% 6.57/1.54  
% 6.57/1.54  fof(f27,plain,(
% 6.57/1.54    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 6.57/1.54    inference(flattening,[],[f26])).
% 6.57/1.54  
% 6.57/1.54  fof(f59,plain,(
% 6.57/1.54    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 6.57/1.54    inference(cnf_transformation,[],[f27])).
% 6.57/1.54  
% 6.57/1.54  fof(f97,plain,(
% 6.57/1.54    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 6.57/1.54    inference(cnf_transformation,[],[f57])).
% 6.57/1.54  
% 6.57/1.54  fof(f4,axiom,(
% 6.57/1.54    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 6.57/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.57/1.54  
% 6.57/1.54  fof(f51,plain,(
% 6.57/1.54    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 6.57/1.54    inference(nnf_transformation,[],[f4])).
% 6.57/1.54  
% 6.57/1.54  fof(f52,plain,(
% 6.57/1.54    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 6.57/1.54    inference(flattening,[],[f51])).
% 6.57/1.54  
% 6.57/1.54  fof(f63,plain,(
% 6.57/1.54    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 6.57/1.54    inference(cnf_transformation,[],[f52])).
% 6.57/1.54  
% 6.57/1.54  fof(f99,plain,(
% 6.57/1.54    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 6.57/1.54    inference(equality_resolution,[],[f63])).
% 6.57/1.54  
% 6.57/1.54  fof(f5,axiom,(
% 6.57/1.54    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 6.57/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.57/1.54  
% 6.57/1.54  fof(f64,plain,(
% 6.57/1.54    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 6.57/1.54    inference(cnf_transformation,[],[f5])).
% 6.57/1.54  
% 6.57/1.54  fof(f12,axiom,(
% 6.57/1.54    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 6.57/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.57/1.54  
% 6.57/1.54  fof(f72,plain,(
% 6.57/1.54    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 6.57/1.54    inference(cnf_transformation,[],[f12])).
% 6.57/1.54  
% 6.57/1.54  fof(f62,plain,(
% 6.57/1.54    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 6.57/1.54    inference(cnf_transformation,[],[f52])).
% 6.57/1.54  
% 6.57/1.54  fof(f100,plain,(
% 6.57/1.54    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 6.57/1.54    inference(equality_resolution,[],[f62])).
% 6.57/1.54  
% 6.57/1.54  fof(f18,axiom,(
% 6.57/1.54    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => (r1_tarski(k1_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))),
% 6.57/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.57/1.54  
% 6.57/1.54  fof(f39,plain,(
% 6.57/1.54    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 6.57/1.54    inference(ennf_transformation,[],[f18])).
% 6.57/1.54  
% 6.57/1.54  fof(f40,plain,(
% 6.57/1.54    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 6.57/1.54    inference(flattening,[],[f39])).
% 6.57/1.54  
% 6.57/1.54  fof(f80,plain,(
% 6.57/1.54    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) )),
% 6.57/1.54    inference(cnf_transformation,[],[f40])).
% 6.57/1.54  
% 6.57/1.54  cnf(c_38,negated_conjecture,
% 6.57/1.54      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 6.57/1.54      inference(cnf_transformation,[],[f95]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_1833,plain,
% 6.57/1.54      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 6.57/1.54      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_20,plain,
% 6.57/1.54      ( v4_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 6.57/1.54      inference(cnf_transformation,[],[f77]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_13,plain,
% 6.57/1.54      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 6.57/1.54      inference(cnf_transformation,[],[f71]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_464,plain,
% 6.57/1.54      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.57/1.54      | ~ v1_relat_1(X0)
% 6.57/1.54      | k7_relat_1(X0,X1) = X0 ),
% 6.57/1.54      inference(resolution,[status(thm)],[c_20,c_13]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_1830,plain,
% 6.57/1.54      ( k7_relat_1(X0,X1) = X0
% 6.57/1.54      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 6.57/1.54      | v1_relat_1(X0) != iProver_top ),
% 6.57/1.54      inference(predicate_to_equality,[status(thm)],[c_464]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_5214,plain,
% 6.57/1.54      ( k7_relat_1(sK3,sK0) = sK3 | v1_relat_1(sK3) != iProver_top ),
% 6.57/1.54      inference(superposition,[status(thm)],[c_1833,c_1830]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_8,plain,
% 6.57/1.54      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 6.57/1.54      inference(cnf_transformation,[],[f65]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_1845,plain,
% 6.57/1.54      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 6.57/1.54      | r1_tarski(X0,X1) = iProver_top ),
% 6.57/1.54      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_2656,plain,
% 6.57/1.54      ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 6.57/1.54      inference(superposition,[status(thm)],[c_1833,c_1845]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_9,plain,
% 6.57/1.54      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 6.57/1.54      inference(cnf_transformation,[],[f67]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_7,plain,
% 6.57/1.54      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 6.57/1.54      inference(cnf_transformation,[],[f66]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_275,plain,
% 6.57/1.54      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 6.57/1.54      inference(prop_impl,[status(thm)],[c_7]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_276,plain,
% 6.57/1.54      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 6.57/1.54      inference(renaming,[status(thm)],[c_275]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_346,plain,
% 6.57/1.54      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 6.57/1.54      inference(bin_hyper_res,[status(thm)],[c_9,c_276]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_1831,plain,
% 6.57/1.54      ( r1_tarski(X0,X1) != iProver_top
% 6.57/1.54      | v1_relat_1(X1) != iProver_top
% 6.57/1.54      | v1_relat_1(X0) = iProver_top ),
% 6.57/1.54      inference(predicate_to_equality,[status(thm)],[c_346]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_3979,plain,
% 6.57/1.54      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 6.57/1.54      | v1_relat_1(sK3) = iProver_top ),
% 6.57/1.54      inference(superposition,[status(thm)],[c_2656,c_1831]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_12,plain,
% 6.57/1.54      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 6.57/1.54      inference(cnf_transformation,[],[f70]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_1844,plain,
% 6.57/1.54      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 6.57/1.54      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_4772,plain,
% 6.57/1.54      ( v1_relat_1(sK3) = iProver_top ),
% 6.57/1.54      inference(forward_subsumption_resolution,[status(thm)],[c_3979,c_1844]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_4773,plain,
% 6.57/1.54      ( v1_relat_1(sK3) ),
% 6.57/1.54      inference(predicate_to_equality_rev,[status(thm)],[c_4772]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_2733,plain,
% 6.57/1.54      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 6.57/1.54      | ~ v1_relat_1(sK3)
% 6.57/1.54      | k7_relat_1(sK3,X0) = sK3 ),
% 6.57/1.54      inference(instantiation,[status(thm)],[c_464]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_5098,plain,
% 6.57/1.54      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 6.57/1.54      | ~ v1_relat_1(sK3)
% 6.57/1.54      | k7_relat_1(sK3,sK0) = sK3 ),
% 6.57/1.54      inference(instantiation,[status(thm)],[c_2733]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_5477,plain,
% 6.57/1.54      ( k7_relat_1(sK3,sK0) = sK3 ),
% 6.57/1.54      inference(global_propositional_subsumption,
% 6.57/1.54                [status(thm)],
% 6.57/1.54                [c_5214,c_38,c_4773,c_5098]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_16,plain,
% 6.57/1.54      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) | ~ v1_relat_1(X0) ),
% 6.57/1.54      inference(cnf_transformation,[],[f74]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_1843,plain,
% 6.57/1.54      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) = iProver_top
% 6.57/1.54      | v1_relat_1(X0) != iProver_top ),
% 6.57/1.54      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_5481,plain,
% 6.57/1.54      ( r1_tarski(k1_relat_1(sK3),sK0) = iProver_top
% 6.57/1.54      | v1_relat_1(sK3) != iProver_top ),
% 6.57/1.54      inference(superposition,[status(thm)],[c_5477,c_1843]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_5672,plain,
% 6.57/1.54      ( r1_tarski(k1_relat_1(sK3),sK0) = iProver_top ),
% 6.57/1.54      inference(global_propositional_subsumption,[status(thm)],[c_5481,c_4772]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_28,plain,
% 6.57/1.54      ( ~ v1_funct_2(X0,X1,X2)
% 6.57/1.54      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.57/1.54      | k1_relset_1(X1,X2,X0) = X1
% 6.57/1.54      | k1_xboole_0 = X2 ),
% 6.57/1.54      inference(cnf_transformation,[],[f81]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_39,negated_conjecture,
% 6.57/1.54      ( v1_funct_2(sK3,sK0,sK1) ),
% 6.57/1.54      inference(cnf_transformation,[],[f94]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_682,plain,
% 6.57/1.54      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.57/1.54      | k1_relset_1(X1,X2,X0) = X1
% 6.57/1.54      | sK3 != X0
% 6.57/1.54      | sK1 != X2
% 6.57/1.54      | sK0 != X1
% 6.57/1.54      | k1_xboole_0 = X2 ),
% 6.57/1.54      inference(resolution_lifted,[status(thm)],[c_28,c_39]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_683,plain,
% 6.57/1.54      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 6.57/1.54      | k1_relset_1(sK0,sK1,sK3) = sK0
% 6.57/1.54      | k1_xboole_0 = sK1 ),
% 6.57/1.54      inference(unflattening,[status(thm)],[c_682]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_685,plain,
% 6.57/1.54      ( k1_relset_1(sK0,sK1,sK3) = sK0 | k1_xboole_0 = sK1 ),
% 6.57/1.54      inference(global_propositional_subsumption,[status(thm)],[c_683,c_38]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_21,plain,
% 6.57/1.54      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.57/1.54      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 6.57/1.54      inference(cnf_transformation,[],[f79]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_1840,plain,
% 6.57/1.54      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 6.57/1.54      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 6.57/1.54      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_3377,plain,
% 6.57/1.54      ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
% 6.57/1.54      inference(superposition,[status(thm)],[c_1833,c_1840]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_3636,plain,
% 6.57/1.54      ( k1_relat_1(sK3) = sK0 | sK1 = k1_xboole_0 ),
% 6.57/1.54      inference(superposition,[status(thm)],[c_685,c_3377]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_17,plain,
% 6.57/1.54      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 6.57/1.54      | ~ v1_relat_1(X1)
% 6.57/1.54      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
% 6.57/1.54      inference(cnf_transformation,[],[f75]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_1842,plain,
% 6.57/1.54      ( k1_relat_1(k7_relat_1(X0,X1)) = X1
% 6.57/1.54      | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
% 6.57/1.54      | v1_relat_1(X0) != iProver_top ),
% 6.57/1.54      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_4413,plain,
% 6.57/1.54      ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
% 6.57/1.54      | sK1 = k1_xboole_0
% 6.57/1.54      | r1_tarski(X0,sK0) != iProver_top
% 6.57/1.54      | v1_relat_1(sK3) != iProver_top ),
% 6.57/1.54      inference(superposition,[status(thm)],[c_3636,c_1842]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_5841,plain,
% 6.57/1.54      ( r1_tarski(X0,sK0) != iProver_top
% 6.57/1.54      | sK1 = k1_xboole_0
% 6.57/1.54      | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ),
% 6.57/1.54      inference(global_propositional_subsumption,[status(thm)],[c_4413,c_4772]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_5842,plain,
% 6.57/1.54      ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
% 6.57/1.54      | sK1 = k1_xboole_0
% 6.57/1.54      | r1_tarski(X0,sK0) != iProver_top ),
% 6.57/1.54      inference(renaming,[status(thm)],[c_5841]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_5854,plain,
% 6.57/1.54      ( k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK3))) = k1_relat_1(sK3)
% 6.57/1.54      | sK1 = k1_xboole_0 ),
% 6.57/1.54      inference(superposition,[status(thm)],[c_5672,c_5842]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_40,negated_conjecture,
% 6.57/1.54      ( v1_funct_1(sK3) ),
% 6.57/1.54      inference(cnf_transformation,[],[f93]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_31,plain,
% 6.57/1.54      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.57/1.54      | ~ v1_funct_1(X0)
% 6.57/1.54      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 6.57/1.54      inference(cnf_transformation,[],[f89]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_2273,plain,
% 6.57/1.54      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 6.57/1.54      | ~ v1_funct_1(sK3)
% 6.57/1.54      | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) ),
% 6.57/1.54      inference(instantiation,[status(thm)],[c_31]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_2309,plain,
% 6.57/1.54      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 6.57/1.54      | ~ v1_funct_1(sK3)
% 6.57/1.54      | k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
% 6.57/1.54      inference(instantiation,[status(thm)],[c_2273]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_3354,plain,
% 6.57/1.54      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 6.57/1.54      | ~ v1_funct_1(sK3)
% 6.57/1.54      | k2_partfun1(sK0,sK1,sK3,sK2) = k7_relat_1(sK3,sK2) ),
% 6.57/1.54      inference(instantiation,[status(thm)],[c_2309]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_2368,plain,
% 6.57/1.54      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.57/1.54      | r1_tarski(X0,k2_zfmisc_1(X1,X2)) ),
% 6.57/1.54      inference(instantiation,[status(thm)],[c_8]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_3428,plain,
% 6.57/1.54      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 6.57/1.54      | r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),k2_zfmisc_1(X0,X1)) ),
% 6.57/1.54      inference(instantiation,[status(thm)],[c_2368]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_7161,plain,
% 6.57/1.54      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 6.57/1.54      | r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),k2_zfmisc_1(sK0,sK1)) ),
% 6.57/1.54      inference(instantiation,[status(thm)],[c_3428]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_29,plain,
% 6.57/1.54      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.57/1.54      | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.57/1.54      | ~ v1_funct_1(X0) ),
% 6.57/1.54      inference(cnf_transformation,[],[f88]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_2268,plain,
% 6.57/1.54      ( m1_subset_1(k2_partfun1(X0,X1,sK3,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 6.57/1.54      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 6.57/1.54      | ~ v1_funct_1(sK3) ),
% 6.57/1.54      inference(instantiation,[status(thm)],[c_29]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_2315,plain,
% 6.57/1.54      ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 6.57/1.54      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 6.57/1.54      | ~ v1_funct_1(sK3) ),
% 6.57/1.54      inference(instantiation,[status(thm)],[c_2268]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_7162,plain,
% 6.57/1.54      ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 6.57/1.54      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 6.57/1.54      | ~ v1_funct_1(sK3) ),
% 6.57/1.54      inference(instantiation,[status(thm)],[c_2315]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_2166,plain,
% 6.57/1.54      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
% 6.57/1.54      | v1_relat_1(X0)
% 6.57/1.54      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 6.57/1.54      inference(instantiation,[status(thm)],[c_346]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_2869,plain,
% 6.57/1.54      ( ~ r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),k2_zfmisc_1(X0,X1))
% 6.57/1.54      | v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 6.57/1.54      | ~ v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 6.57/1.54      inference(instantiation,[status(thm)],[c_2166]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_9562,plain,
% 6.57/1.54      ( ~ r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),k2_zfmisc_1(sK0,sK1))
% 6.57/1.54      | v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 6.57/1.54      | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
% 6.57/1.54      inference(instantiation,[status(thm)],[c_2869]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_1076,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_2976,plain,
% 6.57/1.54      ( X0 != X1
% 6.57/1.54      | X0 = k2_partfun1(sK0,sK1,sK3,X2)
% 6.57/1.54      | k2_partfun1(sK0,sK1,sK3,X2) != X1 ),
% 6.57/1.54      inference(instantiation,[status(thm)],[c_1076]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_3597,plain,
% 6.57/1.54      ( X0 = k2_partfun1(sK0,sK1,sK3,X1)
% 6.57/1.54      | X0 != k7_relat_1(sK3,X1)
% 6.57/1.54      | k2_partfun1(sK0,sK1,sK3,X1) != k7_relat_1(sK3,X1) ),
% 6.57/1.54      inference(instantiation,[status(thm)],[c_2976]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_5167,plain,
% 6.57/1.54      ( k2_partfun1(sK0,sK1,sK3,X0) != k7_relat_1(sK3,X0)
% 6.57/1.54      | k7_relat_1(sK3,X0) = k2_partfun1(sK0,sK1,sK3,X0)
% 6.57/1.54      | k7_relat_1(sK3,X0) != k7_relat_1(sK3,X0) ),
% 6.57/1.54      inference(instantiation,[status(thm)],[c_3597]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_11130,plain,
% 6.57/1.54      ( k2_partfun1(sK0,sK1,sK3,sK2) != k7_relat_1(sK3,sK2)
% 6.57/1.54      | k7_relat_1(sK3,sK2) = k2_partfun1(sK0,sK1,sK3,sK2)
% 6.57/1.54      | k7_relat_1(sK3,sK2) != k7_relat_1(sK3,sK2) ),
% 6.57/1.54      inference(instantiation,[status(thm)],[c_5167]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_1082,plain,
% 6.57/1.54      ( ~ v1_relat_1(X0) | v1_relat_1(X1) | X1 != X0 ),
% 6.57/1.54      theory(equality) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_4676,plain,
% 6.57/1.54      ( ~ v1_relat_1(X0)
% 6.57/1.54      | v1_relat_1(k7_relat_1(sK3,sK2))
% 6.57/1.54      | k7_relat_1(sK3,sK2) != X0 ),
% 6.57/1.54      inference(instantiation,[status(thm)],[c_1082]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_11131,plain,
% 6.57/1.54      ( ~ v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 6.57/1.54      | v1_relat_1(k7_relat_1(sK3,sK2))
% 6.57/1.54      | k7_relat_1(sK3,sK2) != k2_partfun1(sK0,sK1,sK3,sK2) ),
% 6.57/1.54      inference(instantiation,[status(thm)],[c_4676]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_1075,plain,( X0 = X0 ),theory(equality) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_5168,plain,
% 6.57/1.54      ( k7_relat_1(sK3,X0) = k7_relat_1(sK3,X0) ),
% 6.57/1.54      inference(instantiation,[status(thm)],[c_1075]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_13785,plain,
% 6.57/1.54      ( k7_relat_1(sK3,sK2) = k7_relat_1(sK3,sK2) ),
% 6.57/1.54      inference(instantiation,[status(thm)],[c_5168]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_37,negated_conjecture,
% 6.57/1.54      ( r1_tarski(sK2,sK0) ),
% 6.57/1.54      inference(cnf_transformation,[],[f96]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_1834,plain,
% 6.57/1.54      ( r1_tarski(sK2,sK0) = iProver_top ),
% 6.57/1.54      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_5851,plain,
% 6.57/1.54      ( k1_relat_1(k7_relat_1(sK3,sK2)) = sK2 | sK1 = k1_xboole_0 ),
% 6.57/1.54      inference(superposition,[status(thm)],[c_1834,c_5842]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_32,plain,
% 6.57/1.54      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 6.57/1.54      | ~ r1_tarski(k2_relat_1(X0),X1)
% 6.57/1.54      | ~ v1_funct_1(X0)
% 6.57/1.54      | ~ v1_relat_1(X0) ),
% 6.57/1.54      inference(cnf_transformation,[],[f92]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_1835,plain,
% 6.57/1.54      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
% 6.57/1.54      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 6.57/1.54      | v1_funct_1(X0) != iProver_top
% 6.57/1.54      | v1_relat_1(X0) != iProver_top ),
% 6.57/1.54      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_6237,plain,
% 6.57/1.54      ( sK1 = k1_xboole_0
% 6.57/1.54      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
% 6.57/1.54      | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) != iProver_top
% 6.57/1.54      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top
% 6.57/1.54      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 6.57/1.54      inference(superposition,[status(thm)],[c_5851,c_1835]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_1836,plain,
% 6.57/1.54      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
% 6.57/1.54      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 6.57/1.54      | v1_funct_1(X2) != iProver_top ),
% 6.57/1.54      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_6334,plain,
% 6.57/1.54      ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0)
% 6.57/1.54      | v1_funct_1(sK3) != iProver_top ),
% 6.57/1.54      inference(superposition,[status(thm)],[c_1833,c_1836]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_6656,plain,
% 6.57/1.54      ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
% 6.57/1.54      inference(global_propositional_subsumption,
% 6.57/1.54                [status(thm)],
% 6.57/1.54                [c_6334,c_40,c_38,c_2309]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_30,plain,
% 6.57/1.54      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.57/1.54      | ~ v1_funct_1(X0)
% 6.57/1.54      | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) ),
% 6.57/1.54      inference(cnf_transformation,[],[f87]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_1837,plain,
% 6.57/1.54      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 6.57/1.54      | v1_funct_1(X0) != iProver_top
% 6.57/1.54      | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) = iProver_top ),
% 6.57/1.54      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_5294,plain,
% 6.57/1.54      ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
% 6.57/1.54      | v1_funct_1(sK3) != iProver_top ),
% 6.57/1.54      inference(superposition,[status(thm)],[c_1833,c_1837]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_41,plain,
% 6.57/1.54      ( v1_funct_1(sK3) = iProver_top ),
% 6.57/1.54      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_43,plain,
% 6.57/1.54      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 6.57/1.54      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_2249,plain,
% 6.57/1.54      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 6.57/1.54      | v1_funct_1(k2_partfun1(X0,X1,sK3,X2))
% 6.57/1.54      | ~ v1_funct_1(sK3) ),
% 6.57/1.54      inference(instantiation,[status(thm)],[c_30]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_2301,plain,
% 6.57/1.54      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 6.57/1.54      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0))
% 6.57/1.54      | ~ v1_funct_1(sK3) ),
% 6.57/1.54      inference(instantiation,[status(thm)],[c_2249]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_2302,plain,
% 6.57/1.54      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 6.57/1.54      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
% 6.57/1.54      | v1_funct_1(sK3) != iProver_top ),
% 6.57/1.54      inference(predicate_to_equality,[status(thm)],[c_2301]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_5493,plain,
% 6.57/1.54      ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top ),
% 6.57/1.54      inference(global_propositional_subsumption,
% 6.57/1.54                [status(thm)],
% 6.57/1.54                [c_5294,c_41,c_43,c_2302]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_6665,plain,
% 6.57/1.54      ( v1_funct_1(k7_relat_1(sK3,X0)) = iProver_top ),
% 6.57/1.54      inference(demodulation,[status(thm)],[c_6656,c_5493]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_10054,plain,
% 6.57/1.54      ( sK1 = k1_xboole_0
% 6.57/1.54      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
% 6.57/1.54      | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) != iProver_top
% 6.57/1.54      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 6.57/1.54      inference(forward_subsumption_resolution,[status(thm)],[c_6237,c_6665]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_33,plain,
% 6.57/1.54      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 6.57/1.54      | ~ r1_tarski(k2_relat_1(X0),X1)
% 6.57/1.54      | ~ v1_funct_1(X0)
% 6.57/1.54      | ~ v1_relat_1(X0) ),
% 6.57/1.54      inference(cnf_transformation,[],[f91]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_35,negated_conjecture,
% 6.57/1.54      ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
% 6.57/1.54      | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 6.57/1.54      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
% 6.57/1.54      inference(cnf_transformation,[],[f98]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_693,plain,
% 6.57/1.54      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 6.57/1.54      | ~ r1_tarski(k2_relat_1(X0),X1)
% 6.57/1.54      | ~ v1_funct_1(X0)
% 6.57/1.54      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 6.57/1.54      | ~ v1_relat_1(X0)
% 6.57/1.54      | k2_partfun1(sK0,sK1,sK3,sK2) != X0
% 6.57/1.54      | k1_relat_1(X0) != sK2
% 6.57/1.54      | sK1 != X1 ),
% 6.57/1.54      inference(resolution_lifted,[status(thm)],[c_33,c_35]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_694,plain,
% 6.57/1.54      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 6.57/1.54      | ~ r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK1)
% 6.57/1.54      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 6.57/1.54      | ~ v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 6.57/1.54      | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2 ),
% 6.57/1.54      inference(unflattening,[status(thm)],[c_693]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_19,plain,
% 6.57/1.54      ( v5_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 6.57/1.54      inference(cnf_transformation,[],[f78]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_11,plain,
% 6.57/1.54      ( ~ v5_relat_1(X0,X1) | r1_tarski(k2_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 6.57/1.54      inference(cnf_transformation,[],[f68]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_482,plain,
% 6.57/1.54      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.57/1.54      | r1_tarski(k2_relat_1(X0),X2)
% 6.57/1.54      | ~ v1_relat_1(X0) ),
% 6.57/1.54      inference(resolution,[status(thm)],[c_19,c_11]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_706,plain,
% 6.57/1.54      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 6.57/1.54      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 6.57/1.54      | ~ v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 6.57/1.54      | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2 ),
% 6.57/1.54      inference(forward_subsumption_resolution,[status(thm)],[c_694,c_482]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_1820,plain,
% 6.57/1.54      ( k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
% 6.57/1.54      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 6.57/1.54      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top
% 6.57/1.54      | v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 6.57/1.54      inference(predicate_to_equality,[status(thm)],[c_706]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_6662,plain,
% 6.57/1.54      ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
% 6.57/1.54      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 6.57/1.54      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top
% 6.57/1.54      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 6.57/1.54      inference(demodulation,[status(thm)],[c_6656,c_1820]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_6688,plain,
% 6.57/1.54      ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
% 6.57/1.54      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 6.57/1.54      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 6.57/1.54      inference(forward_subsumption_resolution,[status(thm)],[c_6662,c_6665]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_18928,plain,
% 6.57/1.54      ( sK1 = k1_xboole_0
% 6.57/1.54      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 6.57/1.54      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 6.57/1.54      inference(superposition,[status(thm)],[c_5851,c_6688]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_18936,plain,
% 6.57/1.54      ( sK1 = k1_xboole_0
% 6.57/1.54      | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) != iProver_top
% 6.57/1.54      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 6.57/1.54      inference(superposition,[status(thm)],[c_10054,c_18928]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_18,plain,
% 6.57/1.54      ( r1_tarski(k2_relat_1(k7_relat_1(X0,X1)),k2_relat_1(X0))
% 6.57/1.54      | ~ v1_relat_1(X0) ),
% 6.57/1.54      inference(cnf_transformation,[],[f76]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_1841,plain,
% 6.57/1.54      ( r1_tarski(k2_relat_1(k7_relat_1(X0,X1)),k2_relat_1(X0)) = iProver_top
% 6.57/1.54      | v1_relat_1(X0) != iProver_top ),
% 6.57/1.54      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_1829,plain,
% 6.57/1.54      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 6.57/1.54      | r1_tarski(k2_relat_1(X0),X2) = iProver_top
% 6.57/1.54      | v1_relat_1(X0) != iProver_top ),
% 6.57/1.54      inference(predicate_to_equality,[status(thm)],[c_482]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_4184,plain,
% 6.57/1.54      ( r1_tarski(k2_relat_1(sK3),sK1) = iProver_top
% 6.57/1.54      | v1_relat_1(sK3) != iProver_top ),
% 6.57/1.54      inference(superposition,[status(thm)],[c_1833,c_1829]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_1,plain,
% 6.57/1.54      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X2,X0) | r1_tarski(X2,X1) ),
% 6.57/1.54      inference(cnf_transformation,[],[f59]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_1849,plain,
% 6.57/1.54      ( r1_tarski(X0,X1) != iProver_top
% 6.57/1.54      | r1_tarski(X2,X0) != iProver_top
% 6.57/1.54      | r1_tarski(X2,X1) = iProver_top ),
% 6.57/1.54      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_4620,plain,
% 6.57/1.54      ( r1_tarski(X0,k2_relat_1(sK3)) != iProver_top
% 6.57/1.54      | r1_tarski(X0,sK1) = iProver_top
% 6.57/1.54      | v1_relat_1(sK3) != iProver_top ),
% 6.57/1.54      inference(superposition,[status(thm)],[c_4184,c_1849]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_5182,plain,
% 6.57/1.54      ( r1_tarski(X0,sK1) = iProver_top
% 6.57/1.54      | r1_tarski(X0,k2_relat_1(sK3)) != iProver_top ),
% 6.57/1.54      inference(global_propositional_subsumption,[status(thm)],[c_4620,c_4772]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_5183,plain,
% 6.57/1.54      ( r1_tarski(X0,k2_relat_1(sK3)) != iProver_top
% 6.57/1.54      | r1_tarski(X0,sK1) = iProver_top ),
% 6.57/1.54      inference(renaming,[status(thm)],[c_5182]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_5191,plain,
% 6.57/1.54      ( r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1) = iProver_top
% 6.57/1.54      | v1_relat_1(sK3) != iProver_top ),
% 6.57/1.54      inference(superposition,[status(thm)],[c_1841,c_5183]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_10812,plain,
% 6.57/1.54      ( r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1) = iProver_top ),
% 6.57/1.54      inference(global_propositional_subsumption,[status(thm)],[c_5191,c_4772]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_20246,plain,
% 6.57/1.54      ( sK1 = k1_xboole_0 | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 6.57/1.54      inference(forward_subsumption_resolution,[status(thm)],[c_18936,c_10812]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_20247,plain,
% 6.57/1.54      ( ~ v1_relat_1(k7_relat_1(sK3,sK2)) | sK1 = k1_xboole_0 ),
% 6.57/1.54      inference(predicate_to_equality_rev,[status(thm)],[c_20246]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_21936,plain,
% 6.57/1.54      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
% 6.57/1.54      inference(instantiation,[status(thm)],[c_12]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_22406,plain,
% 6.57/1.54      ( sK1 = k1_xboole_0 ),
% 6.57/1.54      inference(global_propositional_subsumption,
% 6.57/1.54                [status(thm)],
% 6.57/1.54                [c_5854,c_40,c_38,c_3354,c_7161,c_7162,c_9562,c_11130,c_11131,
% 6.57/1.54                 c_13785,c_20247,c_21936]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_712,plain,
% 6.57/1.54      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 6.57/1.54      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 6.57/1.54      | k2_partfun1(sK0,sK1,sK3,sK2) != sK3
% 6.57/1.54      | sK2 != sK0
% 6.57/1.54      | sK1 != sK1 ),
% 6.57/1.54      inference(resolution_lifted,[status(thm)],[c_35,c_39]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_819,plain,
% 6.57/1.54      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 6.57/1.54      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 6.57/1.54      | k2_partfun1(sK0,sK1,sK3,sK2) != sK3
% 6.57/1.54      | sK2 != sK0 ),
% 6.57/1.54      inference(equality_resolution_simp,[status(thm)],[c_712]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_1819,plain,
% 6.57/1.54      ( k2_partfun1(sK0,sK1,sK3,sK2) != sK3
% 6.57/1.54      | sK2 != sK0
% 6.57/1.54      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 6.57/1.54      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 6.57/1.54      inference(predicate_to_equality,[status(thm)],[c_819]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_6663,plain,
% 6.57/1.54      ( k7_relat_1(sK3,sK2) != sK3
% 6.57/1.54      | sK2 != sK0
% 6.57/1.54      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 6.57/1.54      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 6.57/1.54      inference(demodulation,[status(thm)],[c_6656,c_1819]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_6680,plain,
% 6.57/1.54      ( k7_relat_1(sK3,sK2) != sK3
% 6.57/1.54      | sK2 != sK0
% 6.57/1.54      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 6.57/1.54      inference(forward_subsumption_resolution,[status(thm)],[c_6663,c_6665]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_22442,plain,
% 6.57/1.54      ( k7_relat_1(sK3,sK2) != sK3
% 6.57/1.54      | sK2 != sK0
% 6.57/1.54      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
% 6.57/1.54      inference(demodulation,[status(thm)],[c_22406,c_6680]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_36,negated_conjecture,
% 6.57/1.54      ( k1_xboole_0 != sK1 | k1_xboole_0 = sK0 ),
% 6.57/1.54      inference(cnf_transformation,[],[f97]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_22492,plain,
% 6.57/1.54      ( sK0 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 6.57/1.54      inference(demodulation,[status(thm)],[c_22406,c_36]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_22493,plain,
% 6.57/1.54      ( sK0 = k1_xboole_0 ),
% 6.57/1.54      inference(equality_resolution_simp,[status(thm)],[c_22492]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_22672,plain,
% 6.57/1.54      ( k7_relat_1(sK3,sK2) != sK3
% 6.57/1.54      | sK2 != k1_xboole_0
% 6.57/1.54      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
% 6.57/1.54      inference(light_normalisation,[status(thm)],[c_22442,c_22493]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_3,plain,
% 6.57/1.54      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 6.57/1.54      inference(cnf_transformation,[],[f99]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_22676,plain,
% 6.57/1.54      ( k7_relat_1(sK3,sK2) != sK3
% 6.57/1.54      | sK2 != k1_xboole_0
% 6.57/1.54      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 6.57/1.54      inference(demodulation,[status(thm)],[c_22672,c_3]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_22926,plain,
% 6.57/1.54      ( r1_tarski(sK2,k1_xboole_0) = iProver_top ),
% 6.57/1.54      inference(demodulation,[status(thm)],[c_22493,c_1834]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_6,plain,
% 6.57/1.54      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 6.57/1.54      inference(cnf_transformation,[],[f64]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_1847,plain,
% 6.57/1.54      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 6.57/1.54      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_5212,plain,
% 6.57/1.54      ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0
% 6.57/1.54      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 6.57/1.54      inference(superposition,[status(thm)],[c_1847,c_1830]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_102,plain,
% 6.57/1.54      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 6.57/1.54      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_104,plain,
% 6.57/1.54      ( v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
% 6.57/1.54      inference(instantiation,[status(thm)],[c_102]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_2167,plain,
% 6.57/1.54      ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 6.57/1.54      | v1_relat_1(X0) = iProver_top
% 6.57/1.54      | v1_relat_1(k2_zfmisc_1(X1,X2)) != iProver_top ),
% 6.57/1.54      inference(predicate_to_equality,[status(thm)],[c_2166]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_2169,plain,
% 6.57/1.54      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top
% 6.57/1.54      | v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top
% 6.57/1.54      | v1_relat_1(k1_xboole_0) = iProver_top ),
% 6.57/1.54      inference(instantiation,[status(thm)],[c_2167]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_2204,plain,
% 6.57/1.54      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 6.57/1.54      inference(instantiation,[status(thm)],[c_6]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_2207,plain,
% 6.57/1.54      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top ),
% 6.57/1.54      inference(predicate_to_equality,[status(thm)],[c_2204]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_2209,plain,
% 6.57/1.54      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 6.57/1.54      inference(instantiation,[status(thm)],[c_2207]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_2369,plain,
% 6.57/1.54      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 6.57/1.54      | r1_tarski(X0,k2_zfmisc_1(X1,X2)) = iProver_top ),
% 6.57/1.54      inference(predicate_to_equality,[status(thm)],[c_2368]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_2371,plain,
% 6.57/1.54      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 6.57/1.54      | r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
% 6.57/1.54      inference(instantiation,[status(thm)],[c_2369]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_9499,plain,
% 6.57/1.54      ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 6.57/1.54      inference(global_propositional_subsumption,
% 6.57/1.54                [status(thm)],
% 6.57/1.54                [c_5212,c_104,c_2169,c_2209,c_2371]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_15,plain,
% 6.57/1.54      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 6.57/1.54      inference(cnf_transformation,[],[f72]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_4412,plain,
% 6.57/1.54      ( k1_relat_1(k7_relat_1(k1_xboole_0,X0)) = X0
% 6.57/1.54      | r1_tarski(X0,k1_xboole_0) != iProver_top
% 6.57/1.54      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 6.57/1.54      inference(superposition,[status(thm)],[c_15,c_1842]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_4449,plain,
% 6.57/1.54      ( r1_tarski(X0,k1_xboole_0) != iProver_top
% 6.57/1.54      | k1_relat_1(k7_relat_1(k1_xboole_0,X0)) = X0 ),
% 6.57/1.54      inference(global_propositional_subsumption,
% 6.57/1.54                [status(thm)],
% 6.57/1.54                [c_4412,c_104,c_2169,c_2209,c_2371]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_4450,plain,
% 6.57/1.54      ( k1_relat_1(k7_relat_1(k1_xboole_0,X0)) = X0
% 6.57/1.54      | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 6.57/1.54      inference(renaming,[status(thm)],[c_4449]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_9503,plain,
% 6.57/1.54      ( k1_relat_1(k1_xboole_0) = X0
% 6.57/1.54      | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 6.57/1.54      inference(demodulation,[status(thm)],[c_9499,c_4450]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_9515,plain,
% 6.57/1.54      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 6.57/1.54      inference(demodulation,[status(thm)],[c_9503,c_15]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_23491,plain,
% 6.57/1.54      ( sK2 = k1_xboole_0 ),
% 6.57/1.54      inference(superposition,[status(thm)],[c_22926,c_9515]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_25731,plain,
% 6.57/1.54      ( k7_relat_1(sK3,sK2) != sK3
% 6.57/1.54      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 6.57/1.54      inference(global_propositional_subsumption,
% 6.57/1.54                [status(thm)],
% 6.57/1.54                [c_22676,c_23491]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_22921,plain,
% 6.57/1.54      ( k7_relat_1(sK3,k1_xboole_0) = sK3 ),
% 6.57/1.54      inference(demodulation,[status(thm)],[c_22493,c_5477]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_4,plain,
% 6.57/1.54      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 6.57/1.54      inference(cnf_transformation,[],[f100]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_1838,plain,
% 6.57/1.54      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 6.57/1.54      | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 6.57/1.54      | v1_funct_1(X0) != iProver_top ),
% 6.57/1.54      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_7318,plain,
% 6.57/1.54      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
% 6.57/1.54      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 6.57/1.54      | v1_funct_1(sK3) != iProver_top ),
% 6.57/1.54      inference(superposition,[status(thm)],[c_6656,c_1838]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_8033,plain,
% 6.57/1.54      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 6.57/1.54      inference(global_propositional_subsumption,
% 6.57/1.54                [status(thm)],
% 6.57/1.54                [c_7318,c_41,c_43]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_22,plain,
% 6.57/1.54      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.57/1.54      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
% 6.57/1.54      | ~ r1_tarski(k1_relat_1(X0),X3) ),
% 6.57/1.54      inference(cnf_transformation,[],[f80]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_1839,plain,
% 6.57/1.54      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 6.57/1.54      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) = iProver_top
% 6.57/1.54      | r1_tarski(k1_relat_1(X0),X3) != iProver_top ),
% 6.57/1.54      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_8042,plain,
% 6.57/1.54      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) = iProver_top
% 6.57/1.54      | r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),X1) != iProver_top ),
% 6.57/1.54      inference(superposition,[status(thm)],[c_8033,c_1839]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_12457,plain,
% 6.57/1.54      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 6.57/1.54      | r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),k1_xboole_0) != iProver_top ),
% 6.57/1.54      inference(superposition,[status(thm)],[c_4,c_8042]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_13043,plain,
% 6.57/1.54      ( m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 6.57/1.54      | v1_relat_1(sK3) != iProver_top ),
% 6.57/1.54      inference(superposition,[status(thm)],[c_1843,c_12457]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_13138,plain,
% 6.57/1.54      ( m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 6.57/1.54      inference(global_propositional_subsumption,
% 6.57/1.54                [status(thm)],
% 6.57/1.54                [c_13043,c_4772]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_13143,plain,
% 6.57/1.54      ( r1_tarski(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0) = iProver_top ),
% 6.57/1.54      inference(superposition,[status(thm)],[c_13138,c_1845]) ).
% 6.57/1.54  
% 6.57/1.54  cnf(c_13448,plain,
% 6.57/1.54      ( k7_relat_1(sK3,k1_xboole_0) = k1_xboole_0 ),
% 6.57/1.54      inference(superposition,[status(thm)],[c_13143,c_9515]) ).
% 6.57/1.55  
% 6.57/1.55  cnf(c_22942,plain,
% 6.57/1.55      ( sK3 = k1_xboole_0 ),
% 6.57/1.55      inference(light_normalisation,[status(thm)],[c_22921,c_13448]) ).
% 6.57/1.55  
% 6.57/1.55  cnf(c_25735,plain,
% 6.57/1.55      ( k7_relat_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 6.57/1.55      | m1_subset_1(k7_relat_1(k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 6.57/1.55      inference(light_normalisation,[status(thm)],[c_25731,c_22942,c_23491]) ).
% 6.57/1.55  
% 6.57/1.55  cnf(c_25736,plain,
% 6.57/1.55      ( k1_xboole_0 != k1_xboole_0
% 6.57/1.55      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 6.57/1.55      inference(demodulation,[status(thm)],[c_25735,c_9499]) ).
% 6.57/1.55  
% 6.57/1.55  cnf(c_25737,plain,
% 6.57/1.55      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 6.57/1.55      inference(equality_resolution_simp,[status(thm)],[c_25736]) ).
% 6.57/1.55  
% 6.57/1.55  cnf(c_25739,plain,
% 6.57/1.55      ( $false ),
% 6.57/1.55      inference(forward_subsumption_resolution,[status(thm)],[c_25737,c_1847]) ).
% 6.57/1.55  
% 6.57/1.55  
% 6.57/1.55  % SZS output end CNFRefutation for theBenchmark.p
% 6.57/1.55  
% 6.57/1.55  ------                               Statistics
% 6.57/1.55  
% 6.57/1.55  ------ General
% 6.57/1.55  
% 6.57/1.55  abstr_ref_over_cycles:                  0
% 6.57/1.55  abstr_ref_under_cycles:                 0
% 6.57/1.55  gc_basic_clause_elim:                   0
% 6.57/1.55  forced_gc_time:                         0
% 6.57/1.55  parsing_time:                           0.01
% 6.57/1.55  unif_index_cands_time:                  0.
% 6.57/1.55  unif_index_add_time:                    0.
% 6.57/1.55  orderings_time:                         0.
% 6.57/1.55  out_proof_time:                         0.025
% 6.57/1.55  total_time:                             0.851
% 6.57/1.55  num_of_symbols:                         51
% 6.57/1.55  num_of_terms:                           16750
% 6.57/1.55  
% 6.57/1.55  ------ Preprocessing
% 6.57/1.55  
% 6.57/1.55  num_of_splits:                          0
% 6.57/1.55  num_of_split_atoms:                     0
% 6.57/1.55  num_of_reused_defs:                     0
% 6.57/1.55  num_eq_ax_congr_red:                    12
% 6.57/1.55  num_of_sem_filtered_clauses:            1
% 6.57/1.55  num_of_subtypes:                        0
% 6.57/1.55  monotx_restored_types:                  0
% 6.57/1.55  sat_num_of_epr_types:                   0
% 6.57/1.55  sat_num_of_non_cyclic_types:            0
% 6.57/1.55  sat_guarded_non_collapsed_types:        0
% 6.57/1.55  num_pure_diseq_elim:                    0
% 6.57/1.55  simp_replaced_by:                       0
% 6.57/1.55  res_preprocessed:                       184
% 6.57/1.55  prep_upred:                             0
% 6.57/1.55  prep_unflattend:                        43
% 6.57/1.55  smt_new_axioms:                         0
% 6.57/1.55  pred_elim_cands:                        5
% 6.57/1.55  pred_elim:                              3
% 6.57/1.55  pred_elim_cl:                           1
% 6.57/1.55  pred_elim_cycles:                       5
% 6.57/1.55  merged_defs:                            8
% 6.57/1.55  merged_defs_ncl:                        0
% 6.57/1.55  bin_hyper_res:                          9
% 6.57/1.55  prep_cycles:                            4
% 6.57/1.55  pred_elim_time:                         0.01
% 6.57/1.55  splitting_time:                         0.
% 6.57/1.55  sem_filter_time:                        0.
% 6.57/1.55  monotx_time:                            0.
% 6.57/1.55  subtype_inf_time:                       0.
% 6.57/1.55  
% 6.57/1.55  ------ Problem properties
% 6.57/1.55  
% 6.57/1.55  clauses:                                39
% 6.57/1.55  conjectures:                            4
% 6.57/1.55  epr:                                    7
% 6.57/1.55  horn:                                   34
% 6.57/1.55  ground:                                 15
% 6.57/1.55  unary:                                  10
% 6.57/1.55  binary:                                 7
% 6.57/1.55  lits:                                   105
% 6.57/1.55  lits_eq:                                37
% 6.57/1.55  fd_pure:                                0
% 6.57/1.55  fd_pseudo:                              0
% 6.57/1.55  fd_cond:                                3
% 6.57/1.55  fd_pseudo_cond:                         1
% 6.57/1.55  ac_symbols:                             0
% 6.57/1.55  
% 6.57/1.55  ------ Propositional Solver
% 6.57/1.55  
% 6.57/1.55  prop_solver_calls:                      30
% 6.57/1.55  prop_fast_solver_calls:                 1888
% 6.57/1.55  smt_solver_calls:                       0
% 6.57/1.55  smt_fast_solver_calls:                  0
% 6.57/1.55  prop_num_of_clauses:                    8985
% 6.57/1.55  prop_preprocess_simplified:             18594
% 6.57/1.55  prop_fo_subsumed:                       87
% 6.57/1.55  prop_solver_time:                       0.
% 6.57/1.55  smt_solver_time:                        0.
% 6.57/1.55  smt_fast_solver_time:                   0.
% 6.57/1.55  prop_fast_solver_time:                  0.
% 6.57/1.55  prop_unsat_core_time:                   0.
% 6.57/1.55  
% 6.57/1.55  ------ QBF
% 6.57/1.55  
% 6.57/1.55  qbf_q_res:                              0
% 6.57/1.55  qbf_num_tautologies:                    0
% 6.57/1.55  qbf_prep_cycles:                        0
% 6.57/1.55  
% 6.57/1.55  ------ BMC1
% 6.57/1.55  
% 6.57/1.55  bmc1_current_bound:                     -1
% 6.57/1.55  bmc1_last_solved_bound:                 -1
% 6.57/1.55  bmc1_unsat_core_size:                   -1
% 6.57/1.55  bmc1_unsat_core_parents_size:           -1
% 6.57/1.55  bmc1_merge_next_fun:                    0
% 6.57/1.55  bmc1_unsat_core_clauses_time:           0.
% 6.57/1.55  
% 6.57/1.55  ------ Instantiation
% 6.57/1.55  
% 6.57/1.55  inst_num_of_clauses:                    2447
% 6.57/1.55  inst_num_in_passive:                    860
% 6.57/1.55  inst_num_in_active:                     972
% 6.57/1.55  inst_num_in_unprocessed:                615
% 6.57/1.55  inst_num_of_loops:                      1190
% 6.57/1.55  inst_num_of_learning_restarts:          0
% 6.57/1.55  inst_num_moves_active_passive:          215
% 6.57/1.55  inst_lit_activity:                      0
% 6.57/1.55  inst_lit_activity_moves:                0
% 6.57/1.55  inst_num_tautologies:                   0
% 6.57/1.55  inst_num_prop_implied:                  0
% 6.57/1.55  inst_num_existing_simplified:           0
% 6.57/1.55  inst_num_eq_res_simplified:             0
% 6.57/1.55  inst_num_child_elim:                    0
% 6.57/1.55  inst_num_of_dismatching_blockings:      1263
% 6.57/1.55  inst_num_of_non_proper_insts:           3319
% 6.57/1.55  inst_num_of_duplicates:                 0
% 6.57/1.55  inst_inst_num_from_inst_to_res:         0
% 6.57/1.55  inst_dismatching_checking_time:         0.
% 6.57/1.55  
% 6.57/1.55  ------ Resolution
% 6.57/1.55  
% 6.57/1.55  res_num_of_clauses:                     0
% 6.57/1.55  res_num_in_passive:                     0
% 6.57/1.55  res_num_in_active:                      0
% 6.57/1.55  res_num_of_loops:                       188
% 6.57/1.55  res_forward_subset_subsumed:            47
% 6.57/1.55  res_backward_subset_subsumed:           4
% 6.57/1.55  res_forward_subsumed:                   0
% 6.57/1.55  res_backward_subsumed:                  0
% 6.57/1.55  res_forward_subsumption_resolution:     4
% 6.57/1.55  res_backward_subsumption_resolution:    0
% 6.57/1.55  res_clause_to_clause_subsumption:       2148
% 6.57/1.55  res_orphan_elimination:                 0
% 6.57/1.55  res_tautology_del:                      167
% 6.57/1.55  res_num_eq_res_simplified:              1
% 6.57/1.55  res_num_sel_changes:                    0
% 6.57/1.55  res_moves_from_active_to_pass:          0
% 6.57/1.55  
% 6.57/1.55  ------ Superposition
% 6.57/1.55  
% 6.57/1.55  sup_time_total:                         0.
% 6.57/1.55  sup_time_generating:                    0.
% 6.57/1.55  sup_time_sim_full:                      0.
% 6.57/1.55  sup_time_sim_immed:                     0.
% 6.57/1.55  
% 6.57/1.55  sup_num_of_clauses:                     363
% 6.57/1.55  sup_num_in_active:                      69
% 6.57/1.55  sup_num_in_passive:                     294
% 6.57/1.55  sup_num_of_loops:                       236
% 6.57/1.55  sup_fw_superposition:                   441
% 6.57/1.55  sup_bw_superposition:                   432
% 6.57/1.55  sup_immediate_simplified:               396
% 6.57/1.55  sup_given_eliminated:                   8
% 6.57/1.55  comparisons_done:                       0
% 6.57/1.55  comparisons_avoided:                    46
% 6.57/1.55  
% 6.57/1.55  ------ Simplifications
% 6.57/1.55  
% 6.57/1.55  
% 6.57/1.55  sim_fw_subset_subsumed:                 72
% 6.57/1.55  sim_bw_subset_subsumed:                 45
% 6.57/1.55  sim_fw_subsumed:                        153
% 6.57/1.55  sim_bw_subsumed:                        12
% 6.57/1.55  sim_fw_subsumption_res:                 17
% 6.57/1.55  sim_bw_subsumption_res:                 0
% 6.57/1.55  sim_tautology_del:                      43
% 6.57/1.55  sim_eq_tautology_del:                   41
% 6.57/1.55  sim_eq_res_simp:                        4
% 6.57/1.55  sim_fw_demodulated:                     74
% 6.57/1.55  sim_bw_demodulated:                     146
% 6.57/1.55  sim_light_normalised:                   192
% 6.57/1.55  sim_joinable_taut:                      0
% 6.57/1.55  sim_joinable_simp:                      0
% 6.57/1.55  sim_ac_normalised:                      0
% 6.57/1.55  sim_smt_subsumption:                    0
% 6.57/1.55  
%------------------------------------------------------------------------------
